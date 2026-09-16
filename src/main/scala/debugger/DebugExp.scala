// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.debugger.debugger.AnyDebugNode
import viper.silicon.decider.PathConditions
import viper.silicon.state.terms.{Exists, Forall, Quantifier, Term, Trigger, Var}
import viper.silver.ast
import viper.silver.ast.Exp
import viper.silver.ast.utility.Simplifier

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable


object DebugCounter {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def next(): Int = idCounter.getAndIncrement()
}

/** A node is either a single assumption of a particular type, or a DebugGroupNode with children.
  * Group nodes should not have terms or expressions themselves, but only with respect to their children.
  */
sealed trait DebugNode[Self <: DebugNode[Self]] {
  val id: Int
  def description: Option[String]
  def isInternal: Boolean
  def isGlobal: Boolean

  // TODO: Why do these take visited? Could we just remove?
  def getAllTerms(visited: mutable.HashSet[DebugNode[_]]): Seq[Term]
  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode[_]]): Option[DebugNode[_]]

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

  override def getAllTerms(visited: mutable.HashSet[DebugNode[_]]): Seq[Term] =
    if (visited.contains(this)) Seq() else Seq(term)

  override def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode[_]]): Option[DebugAssumption[Self]] =
    Option.when(this.id == soughtId)(this)

  override def filterTerm(t: Term): Option[DebugAssumption[Self]] =
    Option.when(this.term.contains(t))(this)

  def toString(currDepth: Int, maxDepth: Int, config: DebugPrintConfiguration): String =
    if (!config.printInternalTermRepresentation && isInternal) "" else ("\t" * currDepth) + s"\t[$id] ${display(config)}"

  // display is only the content of the node
  def display(config: DebugPrintConfiguration): String
}

/** A category that groups the assumptions made underneath it, rather than standing alone. */
sealed trait DebugGroupNode[Self <: DebugGroupNode[Self]] extends DebugNode[Self] {
  def children: InsertionOrderedSet[DebugNode[_]]

  lazy val isGlobal: Boolean = children.forall(_.isGlobal)

  def getAllTerms(visited: mutable.HashSet[DebugNode[_]]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    children.toSeq.flatMap(_.getAllTerms(visited))
  }

  // Return a copy of the group with any children matching 'ids' removed.
  def removeChildrenById(ids: Seq[Int]): DebugGroupNode[Self]

  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode[_]] = mutable.HashSet.empty): Option[DebugNode[_]] = {
    /*    if (visited.contains(this))
          return None
        visited.add(this)
        if (id == soughtId) {
          return Some(this)
        }
        val toSearch = children.toSeq
        var found: Option[DebugNode] = None
        var i = 0
        while (found.isEmpty && i < toSearch.size) {
          found = toSearch(i).getNodeWithId(soughtId, visited)
          i += 1
        }
        found*/
    // TODO: do we need visited? Can't we just filter?
    None
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


/* -------------------------------------------------------------------------------------------- *
 * Assumptions                                                                                  *
 * -------------------------------------------------------------------------------------------- */

// Generic assumption type
class DebugExp(val id: Int,
               val description : Option[String],
               override val isInternal : Boolean,
               val term : Term,
               override val originalExp : Option[Exp],
               override val finalExp : Option[Exp]) extends DebugAssumption[DebugExp] {
  override lazy val isGlobal: Boolean = PathConditions.isGlobal(term)

  override def display(config: DebugPrintConfiguration): String = {
    if (config.printInternalTermRepresentation) term.toString
    else if (finalExp.isDefined) finalExp.get.toString
    else description.getOrElse("Internal assumption")
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


/* -------------------------------------------------------------------------------------------- *
 * Groups                                                                                       *
 * -------------------------------------------------------------------------------------------- */

// Generic group of assumptions
class DebugGroup(val id: Int,
                 val description: Option[String],
                 val children: InsertionOrderedSet[DebugNode[_]]) extends DebugGroupNode[DebugGroup] {
  override val isInternal: Boolean = children.forall(_.isInternal)

  lazy val terms: Option[InsertionOrderedSet[Term]] =
    Some(children.flatMap(c => c.getAllTerms(mutable.HashSet.empty)))

  override def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode[_]]): Option[DebugNode[_]] =
    ???

  override def filterTerm(t: Term): Option[DebugNode[DebugGroup]] = ???

  override def headerString(config: DebugPrintConfiguration): String = description.getOrElse("Group") + ":"

  override def removeChildrenById(ids: Seq[Int]): DebugGroupNode[DebugGroup] = ???
}

object DebugGroup {
  def apply(description: String, children: InsertionOrderedSet[DebugNode[_]]): DebugGroup =
    new DebugGroup(DebugCounter.next(), Some(description), children)

  def apply(description: String, children: Iterable[AnyDebugNode]): DebugGroup =
    new DebugGroup(DebugCounter.next(), Some(description), InsertionOrderedSet(children))

  def awaitChildren(description: String): InsertionOrderedSet[DebugNode[_]] => DebugGroup =
    children => DebugGroup(description, children)
}

class DebugImplication(val id: Int,
                       val description: Option[String],
                       val isInternal: Boolean,
                       term : Term, // Antecedent of the implication
                       originalExp: Option[Exp],
                       finalExp: Option[Exp],
                       val children: InsertionOrderedSet[DebugNode[_]]) extends DebugGroupNode[DebugImplication] {

  override def removeChildrenById(ids: Seq[Int]): DebugGroupNode[DebugImplication] = ???

  override def filterTerm(t: Term): Option[DebugNode[DebugImplication]] = ???

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
  def apply(description: Option[String], isInternal: Boolean, term: Term, originalExp: Option[Exp], finalExp: Option[Exp],
            children: InsertionOrderedSet[DebugNode[_]]): DebugImplication =
    new DebugImplication(DebugCounter.next(), description, isInternal, term, originalExp, finalExp, children)
}

class DebugQuantifier(val id: Int,
                      val description: Option[String],
                      val isInternal: Boolean,
                      val quantifier: Quantifier,
                      val qvars : Seq[Exp],
                      val tQvars: Seq[Var],
                      val triggers: Seq[ast.Trigger],
                      val tTriggers: Seq[Trigger],
                      val children : InsertionOrderedSet[DebugNode[_]]) extends DebugGroupNode[DebugQuantifier] {
  val terms = None

  override def removeChildrenById(ids: Seq[Int]): DebugGroupNode[DebugQuantifier] = ???

  override def filterTerm(t: Term): Option[DebugNode[DebugQuantifier]] = ???

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
            children : InsertionOrderedSet[DebugNode[_]]): DebugQuantifier =
    new DebugQuantifier(DebugCounter.next(), description, isInternal, quantifier, qvars, tQvars, triggers, tTriggers, children)
}

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
      s"  nChildrenToShow        = $nChildrenToShow\n" +
      s"  printHierarchyLevel    = $printHierarchyLevel\n" +
      s"  hierarchy per id       = $nodeToHierarchyLevelMap\n" +
      s"  isPrintAxiomsEnabled   = $isPrintAxiomsEnabled\n" +
      s"  printInternalTermReps  = $printInternalTermRepresentation\n" +
      s"  printOldHeaps          = $printOldHeaps\n"
  }
}

class DebugAxiom(val description: String, val terms: InsertionOrderedSet[Term]){
  override def toString: String = {
    s"$description:\n\t\t${terms.mkString("\n\t\t")}\n"
  }
}