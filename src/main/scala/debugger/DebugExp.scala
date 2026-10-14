// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.debugger.AnyDebugNode
import viper.silicon.decider.PathConditions
import viper.silicon.state.terms.{Quantifier, Term, Trigger, Var}
import viper.silver.ast
import viper.silver.ast.{Exp, Position}
import viper.silver.ast.utility.Simplifier

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object DebugCounter {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def next(): Int = idCounter.getAndIncrement()
}


/* -------------------------------------------------------------------------------------------- *
 * Traits                                                                                       *
 * -------------------------------------------------------------------------------------------- */

/** A node is either a single assumption of a particular type, or a DebugGroupNode with children.
  * Group nodes should not have terms or expressions themselves, but only with respect to their children.
  */
sealed trait DebugNode[Self <: DebugNode[Self]] {
  val id: Int
  def description: Option[String]
  def isInternal: Boolean
  def isGlobal: Boolean

  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[AnyDebugNode]): Option[AnyDebugNode]

  // Remove the node and any children containing 'term'.
  def filterTerm(t: Term): Option[DebugNode[Self]]

  // toString is used by the debugger, includes indents, newlines and ids
  def toString(currDepth: Int, maxDepth: Int, config: DebugPrintConfiguration): String
  def toString(config: DebugPrintConfiguration): String =
    toString(0, config.printHierarchyLevel, config)
  override def toString: String = {
    toString(0, 6, new DebugPrintConfiguration)
  }
}

/** DebugAssumptions need to be passed into 'decider.assume' before the final term is known.
  * So all extensions should implement 'awaitTerm' to delay construction.
  */
sealed trait DebugAssumption[Self <: DebugAssumption[Self]] extends DebugNode[Self] {
  def term: Term
  def finalExp: Option[Exp] = None
  def originalExp: Option[Exp] = None

  lazy val isGlobal: Boolean = PathConditions.isGlobal(term)

  override def getNodeWithId(soughtId: Int, visited: mutable.HashSet[AnyDebugNode]): Option[DebugAssumption[Self]] =
    Option.when(this.id == soughtId)(this)

  override def filterTerm(t: Term): Option[DebugAssumption[Self]] =
    Option.when(this.term.contains(t))(this)

  def toString(currDepth: Int, maxDepth: Int, config: DebugPrintConfiguration): String =
    ("\t" * currDepth) + s"\t[$id] ${display(config)}"

  override def toString(config: DebugPrintConfiguration): String =
    s"\t[$id] ${display(config)}"

  // display is only the content of the node
  def display(config: DebugPrintConfiguration): String
}

/** A category that groups the assumptions made underneath it, rather than standing alone. */
sealed trait DebugGroupNode[Self <: DebugGroupNode[Self]] extends DebugNode[Self] {
  def children: InsertionOrderedSet[AnyDebugNode]

  /** The terms that were actually assumed for this group, which might not directly match the children.
    * See Decider.assume and PathConditions. Use actualTerms for verification, but children for display.
    */
  def actualTerms: InsertionOrderedSet[Term]

  lazy val isGlobal: Boolean = children.forall(_.isGlobal)

  // Return a copy of the group with any children matching 'ids' removed.
  // The terms of removed children are removed from this group's terms. A removed child whose terms
  // only occur as part of a larger term of this group (e.g. inside an implication) cannot be removed
  // from that term; see SiliconDebugger.removeAssumptions, which reports such children.
  def removeChildrenById(ids: Seq[Int]): DebugGroupNode[Self] = {
    val newChildren = children.flatMap[AnyDebugNode] {
      case ass: DebugAssumption[_] => if (ids.contains(ass.id)) None else Some(ass)
      case group: DebugGroupNode[_] => if (ids.contains(group.id)) None else Some(group.removeChildrenById(ids))
    }
    withRemainingChildren(newChildren)
  }

  // A copy with the given children, which replace the current ones, and without the terms that
  // only the replaced children contributed.
  protected def withRemainingChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): DebugGroupNode[Self] = {
    val removedTerms = DebugGroupNode.termsOf(children) -- DebugGroupNode.termsOf(newChildren)
    this.withChildren(newChildren).withTerms(actualTerms -- removedTerms)
  }

  def withChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): Self
  def withTerms(newTerms: InsertionOrderedSet[Term]): DebugGroupNode[Self]

  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[AnyDebugNode] = mutable.HashSet.empty): Option[AnyDebugNode] = {
    if (visited.contains(this))
      return None

    visited.add(this)
    if (id == soughtId)
      return Some(this)

    val toSearch = children.toSeq
    var found: Option[AnyDebugNode] = None
    var i = 0
    while (found.isEmpty && i < toSearch.size) {
      found = toSearch(i).getNodeWithId(soughtId, visited)
      i += 1
    }
    found
  }

  private def childrenToString(currDepth: Int, maxDepth: Int, config: DebugPrintConfiguration): String = {
    val printableChildren = children.filter(de => config.isPrintInternalEnabled || !de.isInternal)
    if (printableChildren.isEmpty) ""
    else if (maxDepth <= currDepth) "\n" + ("\t" * (currDepth + 2)) + "[...]"
    else {
      val resBuilder = new mutable.StringBuilder()
      val childrenToPrint = if (config.nChildrenToShow > 0) printableChildren.take(config.nChildrenToShow) else printableChildren
      childrenToPrint.foreach(de => resBuilder.addAll("\n" + de.toString(currDepth + 1, maxDepth, config)))
      if (childrenToPrint.size < printableChildren.size) resBuilder.addAll("\n\t" + ("\t" * (currDepth + 1)) + "[...]")
      resBuilder.toString()
    }
  }

  // Description or implication, etc
  def headerString(config: DebugPrintConfiguration): String

  def toString(currDepth: Int, maxDepth: Int, config: DebugPrintConfiguration): String = {
    if (isInternal && !config.isPrintInternalEnabled) ""
    else "\t" + ("\t" * currDepth) + s"[$id] ${headerString(config)}" +
      childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
  }
}

object DebugGroupNode {
  // The terms recorded by the given nodes (for groups, their recorded terms, not those of their children).
  def termsOf(nodes: Iterable[AnyDebugNode]): InsertionOrderedSet[Term] =
    InsertionOrderedSet(nodes.flatMap {
      case group: DebugGroupNode[_] => group.actualTerms
      case assum: DebugAssumption[_] => Iterable(assum.term)
    })

  def termsOf(node: AnyDebugNode): InsertionOrderedSet[Term] =
    termsOf(Iterable(node))
}


/* -------------------------------------------------------------------------------------------- *
 * Assumptions                                                                                  *
 * -------------------------------------------------------------------------------------------- */

// Generic assumption type
class DebugExp(val id: Int,
               val description: Option[String],
               override val isInternal: Boolean,
               val term: Term,
               override val originalExp: Option[Exp],
               override val finalExp: Option[Exp]) extends DebugAssumption[DebugExp] {
  override def display(config: DebugPrintConfiguration): String = {
    val descriptionStr = description.map(_ + ": ").getOrElse("")
    val assumptionStr = if (config.printInternalTermRepresentation) term.toString
      else if (finalExp.isDefined) finalExp.get.toString
      else description.getOrElse("Internal assumption")
    descriptionStr + assumptionStr
  }
}

object DebugExp {
  def apply(description: Option[String],
            isInternal: Boolean,
            term: Term,
            originalExp: Option[Exp],
            finalExp: Option[Exp])
            : DebugExp = {
    val originalExpSimplified = originalExp.map(Simplifier.simplify(_, assumeWelldefinedness = true))
    val finalExpSimplified = finalExp.map(Simplifier.simplify(_, assumeWelldefinedness = true))
    new DebugExp(DebugCounter.next(), description, isInternal, term, originalExpSimplified, finalExpSimplified)
  }

  def apply(term: Term, originalExp: Option[Exp], finalExp: Option[Exp], isInternal: Boolean): DebugExp =
    new DebugExp(DebugCounter.next(), None, isInternal, term, originalExp, finalExp)

  def awaitTerm(description: String, isInternal: Boolean): Term => DebugExp =
    term => DebugExp(Some(description), isInternal, term, None, None)

  def awaitTerm(originalExp: Exp, finalExp: Exp): Term => DebugExp =
    term => DebugExp(None, isInternal = false, term, Some(originalExp), Some(finalExp))

  def awaitTerm(originalExp: Option[Exp], finalExp: Option[Exp]): Term => DebugExp =
    term => DebugExp(None, isInternal = false, term, originalExp, finalExp)

  def awaitTerm(description: String, originalExp: ast.Exp, finalExp: ast.Exp, isInternal: Boolean): Term => DebugExp =
    term => DebugExp(Some(description), isInternal, term, Some(originalExp), Some(finalExp))
}

class DebugPrecondition(val id: Int,
                        val term: Term,
                        val funExp: ast.FuncApp,
                        val finalArgs: Option[Seq[Exp]],
                        val heapLabel: String) extends DebugAssumption[DebugPrecondition] {
  override def description: Option[String] = Some(s"Precondition of ${funExp.funcname}(${funExp.args.mkString(", ")}) holds")

  override def isInternal: Boolean = true

  override def originalExp: Option[Exp] = Some(funExp)

  override def display(config: DebugPrintConfiguration): String = {
    if (config.printInternalTermRepresentation) s"${description.get}: ${term.toString}"
    else description.get
  }
}

object DebugPrecondition {
  def apply(term: Term, funExp: ast.FuncApp, finalArgs: Option[Seq[Exp]], heapLabel: String): DebugPrecondition =
    new DebugPrecondition(DebugCounter.next(), term, funExp, finalArgs, heapLabel)

  def awaitTerm(fun: ast.FuncApp, finalArgs: Option[Seq[Exp]], heapLabel: String): Term => DebugPrecondition =
    term => DebugPrecondition(term, fun, finalArgs, heapLabel)
}


/* -------------------------------------------------------------------------------------------- *
 * Groups                                                                                       *
 * -------------------------------------------------------------------------------------------- */

// Generic group of assumptions
class DebugGroup(val id: Int,
                 val groupDescription: String,
                 val children: InsertionOrderedSet[AnyDebugNode],
                 val actualTerms: InsertionOrderedSet[Term]) extends DebugGroupNode[DebugGroup] {
  override def description: Option[String] = Some(groupDescription)

  override val isInternal: Boolean = children.forall(_.isInternal)

  override def filterTerm(t: Term): Option[DebugNode[DebugGroup]] = {
    val newChildren = children.flatMap(_.filterTerm(t))
    Option.when(newChildren.nonEmpty)(withRemainingChildren(newChildren))
  }

  override def withChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): DebugGroup =
    new DebugGroup(id, groupDescription, newChildren, actualTerms)

  override def withTerms(newTerms: InsertionOrderedSet[Term]): DebugGroup =
    new DebugGroup(id, groupDescription, children, newTerms)

  override def headerString(config: DebugPrintConfiguration): String = description.getOrElse("Group") + ":"
}

object DebugGroup {
  /* The group's terms default to the terms recorded by its children, which is correct for a group that
   * only collects separately assumed nodes. A group passed to Decider.assume is given the assumed terms. */
  def apply(description: String, children: InsertionOrderedSet[AnyDebugNode]): DebugGroup =
    new DebugGroup(DebugCounter.next(), description, children, DebugGroupNode.termsOf(children))

  def apply(description: String, children: Iterable[AnyDebugNode]): DebugGroup =
    DebugGroup(description, InsertionOrderedSet(children))

  def awaitChildren(description: String): InsertionOrderedSet[AnyDebugNode] => DebugGroup =
    children => DebugGroup(description, children)
}

class DebugImplication(val id: Int,
                       val description: Option[String],
                       val isInternal: Boolean,
                       val term : Term, // Antecedent of the implication
                       val originalExp: Option[Exp],
                       val finalExp: Option[Exp],
                       val children: InsertionOrderedSet[AnyDebugNode],
                       val actualTerms: InsertionOrderedSet[Term]) // The assumed implication(s)
                       extends DebugGroupNode[DebugImplication] {
  override def filterTerm(t: Term): Option[DebugNode[DebugImplication]] = {
    if (term.contains(t)) None
    else {
      val newChildren = children.flatMap(_.filterTerm(t))
      Option.when(newChildren.nonEmpty)(withRemainingChildren(newChildren))
    }
  }

  override def withChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): DebugImplication =
    new DebugImplication(id, description, isInternal, term, originalExp, finalExp, newChildren, actualTerms)

  override def withTerms(newTerms: InsertionOrderedSet[Term]): DebugImplication =
    new DebugImplication(id, description, isInternal, term, originalExp, finalExp, children, newTerms)

  override def headerString(config: DebugPrintConfiguration): String = {
    if (config.printInternalTermRepresentation) s"$term ==>"
    else (finalExp, originalExp) match {
      case (Some(exp), _) => exp.toString + " ==>"
      case (None, Some(exp)) => exp.toString + " ==>"
      case _ => "No antecedent exp"
    }
  }
}

object DebugImplication {
  def apply(description: Option[String], isInternal: Boolean, term: Term,
            originalExp: Option[Exp], finalExp: Option[Exp],
            children: InsertionOrderedSet[AnyDebugNode],
            terms: InsertionOrderedSet[Term]
           ): DebugImplication = {
    val originalExpSimp = originalExp.map(Simplifier.simplify(_, assumeWelldefinedness = true))
    val finalExpSimp = finalExp.map(Simplifier.simplify(_, assumeWelldefinedness = true))
    new DebugImplication(DebugCounter.next(), description, isInternal, term, originalExpSimp, finalExpSimp, children, terms)
  }
}

class DebugQuantifier(val id: Int,
                      val description: Option[String],
                      val isInternal: Boolean,
                      val quantifier: Quantifier,
                      val qvars : Seq[Exp],
                      val tQvars: Seq[Var],
                      val triggers: Seq[ast.Trigger],
                      val tTriggers: Seq[Trigger],
                      val children : InsertionOrderedSet[AnyDebugNode],
                      val actualTerms: InsertionOrderedSet[Term]) // The assumed quantification(s)
                      extends DebugGroupNode[DebugQuantifier] {
  override def filterTerm(t: Term): Option[DebugNode[DebugQuantifier]] = {
    if (tQvars.exists(_.contains(t))) None
    else {
      val newChildren = children.flatMap(_.filterTerm(t))
      Option.when(newChildren.nonEmpty)(withRemainingChildren(newChildren))
    }
  }

  override def withChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): DebugQuantifier =
    new DebugQuantifier(id, description, isInternal, quantifier, qvars, tQvars, triggers, tTriggers, newChildren, actualTerms)

  override def withTerms(newTerms: InsertionOrderedSet[Term]): DebugQuantifier =
    new DebugQuantifier(id, description, isInternal, quantifier, qvars, tQvars, triggers, tTriggers, children, newTerms)

  override def headerString(config: DebugPrintConfiguration): String =
    if (config.printInternalTermRepresentation) s"$quantifier ${tQvars.mkString(", ")} ::"
    else s"${quantifier.fullName} ${qvars.mkString(", ")} ::"
}

object DebugQuantifier {
  def apply(description: Option[String],
            isInternal: Boolean,
            quantifier: Quantifier,
            qvars : Seq[Exp],
            tQvars: Seq[Var],
            triggers: Seq[ast.Trigger],
            tTriggers: Seq[Trigger],
            children : InsertionOrderedSet[AnyDebugNode],
            terms: InsertionOrderedSet[Term]): DebugQuantifier =
    new DebugQuantifier(DebugCounter.next(), description, isInternal, quantifier, qvars, tQvars, triggers, tTriggers, children, terms)
}

class DebugInvariant(val id: Int,
                     val loopPos: Position,
                     val children: InsertionOrderedSet[AnyDebugNode],
                     val actualTerms: InsertionOrderedSet[Term])
                     extends DebugGroupNode[DebugInvariant] {
  override def description: Option[String] = Some("Loop invariants")

  override def isInternal: Boolean = false

  override def withChildren(newChildren: InsertionOrderedSet[AnyDebugNode]): DebugInvariant =
    new DebugInvariant(id, loopPos, newChildren, actualTerms)

  override def withTerms(newTerms: InsertionOrderedSet[Term]): DebugInvariant =
    new DebugInvariant(id, loopPos, children, newTerms)

  override def filterTerm(t: Term): Option[DebugNode[DebugInvariant]] = {
    val newChildren = children.flatMap(_.filterTerm(t))
    Option.when(newChildren.nonEmpty)(withRemainingChildren(newChildren))
  }

  override def headerString(config: DebugPrintConfiguration): String = s"Loop invariants (at $loopPos):"
}

object DebugInvariant {
  // As for DebugGroup, the terms default to those of the children until the invariant group is assumed.
  def apply(loopPos: Position, children: InsertionOrderedSet[AnyDebugNode]): DebugInvariant =
    new DebugInvariant(DebugCounter.next(), loopPos, children, DebugGroupNode.termsOf(children))
}


/* -------------------------------------------------------------------------------------------- *
 * Configuration                                                                                *
 * -------------------------------------------------------------------------------------------- */

class DebugPrintConfiguration {
  var isPrintInternalEnabled: Boolean = false
  var nChildrenToShow: Int = 5
  var printHierarchyLevel: Int = 2
  var nodeToHierarchyLevelMap: Map[Int, Int] = Map.empty
  var isPrintAxiomsEnabled: Boolean = false
  var printInternalTermRepresentation: Boolean = false
  var printOldHeaps: Boolean = false

  def setPrintHierarchyLevel(level: String): Unit ={
    printHierarchyLevel = level match {
      case "full" => 100
      case "top" => 0
      case _ => level.toIntOption match {
        case Some(v) => v
        case None    => printHierarchyLevel
      }
    }
  }

  def addHierarchyLevelForId(str: String): Unit ={
    val strSplit = str.split("->")
    if (strSplit.size < 2){
      println("invalid input")
      return
    }
    val level = strSplit(1).trim.toIntOption
    if (level.isEmpty){
      println("invalid input")
      return
    }
    strSplit(0).split(",").foreach(s_id => s_id.trim.toIntOption match {
      case Some(value) => nodeToHierarchyLevelMap += value -> level.get
      case None =>
    })
  }

  override def toString: String = {
    s"  isPrintInternalEnabled = $isPrintInternalEnabled\n" +
      s"  printInternalTermReps  = $printInternalTermRepresentation\n" +
      s"  nChildrenToShow        = $nChildrenToShow\n" +
      s"  printHierarchyLevel    = $printHierarchyLevel\n" +
      s"  hierarchy per id       = $nodeToHierarchyLevelMap\n" +
      s"  printOldHeaps          = $printOldHeaps\n" +
      s"  isPrintAxiomsEnabled   = $isPrintAxiomsEnabled\n"
  }
}

class DebugAxiom(val description: String, val terms: InsertionOrderedSet[Term]){
  override def toString: String = {
    s"$description:\n\t\t${terms.mkString("\n\t\t")}\n"
  }
}