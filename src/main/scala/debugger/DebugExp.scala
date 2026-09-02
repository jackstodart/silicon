// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.debugger

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditions
import viper.silicon.state.terms.{And, Exists, Forall, Implies, Quantification, Term, Trigger, Var}
import viper.silver.ast
import viper.silver.ast.utility.Simplifier

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

object DebugCounter {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def next(): Int = idCounter.getAndIncrement()
}

/**
 * A node in the tree of debug information recorded while `debugMode` is enabled. Every assumption
 * made during symbolic execution is recorded as one of the categories below.
 *
 * The category, rather than a free-text description, determines how an assumption is presented to
 * the user and how its terms are reconstructed by the debugger. Categories that group other
 * assumptions carry them in [[children]]; the remaining ones are leaves.
 *
 * Nodes are created before the term they stand for has been assumed, so the decider attaches that
 * term afterwards with [[withTerm]]. Nodes are immutable: [[withTerm]] returns a copy.
 */
sealed trait DebugNode {
  val id: Int
  def term: Option[Term]
  def finalExp: Option[ast.Exp] = None
  def originalExp: Option[ast.Exp] = None
  def children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty
  def isInternal: Boolean
  def description: Option[String]

  /** Returns a copy of this node recording the term that was assumed for it. The decider attaches
    * the term after the fact because it is the one it actually assumed, which is not the one the
    * call site passed: assumptions already known to hold are filtered out first.
    */
  def withTerm(newTerm: Term): DebugNode

  lazy val isGlobal: Boolean = {
    val thisGlobal = term match {
      case Some(t) => PathConditions.isGlobal(t)
      case None => true
    }
    thisGlobal && children.forall(_.isGlobal)
  }

  def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    term.toSeq ++ children.toSeq.flatMap(_.getAllTerms(visited))
  }

  def removeChildrenById(ids: Seq[Int]): DebugNode = this match {
    case group: DebugGroup if group.children.nonEmpty =>
      group.withChildren(group.children.filter(c => !ids.contains(c.id)).map(_.removeChildrenById(ids)))
    case _ => this
  }

  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode]): Option[DebugNode] = {
    if (visited.contains(this))
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
    found
  }

  def childrenToString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    val nonInternalChildren = children.filter(de => config.isPrintInternalEnabled || !de.isInternal)
    if (nonInternalChildren.isEmpty) ""
    else if (maxDepth <= currDepth) "[...]"
    else {
      val resBuilder = new mutable.StringBuilder()
      val childrenToShow = if (config.nChildrenToShow > 0) nonInternalChildren.take(config.nChildrenToShow) else nonInternalChildren
      childrenToShow.foreach(de => resBuilder.addAll(de.toString(currDepth + 1, maxDepth, config)))
      if (childrenToShow.size < nonInternalChildren.size) resBuilder.addAll("\n\t" + ("\t" * (currDepth + 1)) + "[...]")
      resBuilder.toString()
    }
  }

  def getTopLevelString(currDepth: Int, config: DebugExpPrintConfiguration): String = {
    val toDisplay = if (config.printInternalTermRepresentation) Some(term) else finalExp
    val delimiter = if (toDisplay.isDefined && description.isDefined) ": " else ""
    "\n\t" + ("\t" * currDepth) + "[" + id + "] " + description.getOrElse("") + delimiter + toDisplay.getOrElse("")
  }

  def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal && !config.isPrintInternalEnabled) {
      return ""
    }
    getTopLevelString(currDepth, config) +
      childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
  }

  def toString(config: DebugExpPrintConfiguration): String = {
    toString(0, config.printHierarchyLevel, config)
  }

  override def toString: String = {
    toString(0, 6, new DebugExpPrintConfiguration)
  }
}

/** A category that groups the assumptions made underneath it, rather than standing alone. */
sealed trait DebugGroup extends DebugNode {
  def children: InsertionOrderedSet[DebugNode]

  /** Returns a copy of this node with different children. */
  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugGroup
}

/* -------------------------------------------------------------------------------------------- *
 * Plain assumptions                                                                              *
 * -------------------------------------------------------------------------------------------- */

/**
 * An assumption that stands directly for a source-level expression, with no further structure.
 * This is the category for assumptions the user wrote themselves, as opposed to the ones Silicon
 * derives while reasoning about them.
 */
class DebugExp(val id: Int,
               override val originalExp: Option[ast.Exp],
               override val finalExp: Option[ast.Exp],
               override val term: Option[Term],
               override val isInternal: Boolean) extends DebugNode {

  def description: Option[String] = None

  def withTerm(newTerm: Term): DebugExp =
    new DebugExp(id, originalExp, finalExp, Some(newTerm), isInternal)
}

object DebugExp {
  def apply(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp], isInternal: Boolean): DebugExp =
    new DebugExp(DebugCounter.next(),
                 originalExp.map(Simplifier.simplify(_, true)),
                 finalExp.map(Simplifier.simplify(_, true)),
                 None,
                 isInternal)

  def apply(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugExp =
    apply(originalExp, finalExp, isInternal = false)

  def apply(originalExp: ast.Exp, finalExp: ast.Exp): DebugExp =
    apply(Some(originalExp), Some(finalExp), isInternal = false)
}

/** An assumption that a permission amount is positive, made while evaluating a `perm` expression. */
class DebugPermissionPositive(val id: Int,
                              val permExp: ast.Exp,
                              override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(s"$permExp > none")

  def withTerm(newTerm: Term): DebugPermissionPositive =
    new DebugPermissionPositive(id, permExp, Some(newTerm))
}

object DebugPermissionPositive {
  def apply(permExp: ast.Exp): DebugPermissionPositive =
    new DebugPermissionPositive(DebugCounter.next(), permExp)
}

/* -------------------------------------------------------------------------------------------- *
 * Structure: implications, quantifiers, loops, branches, bindings                                 *
 * -------------------------------------------------------------------------------------------- */

/** A group of assumptions that only hold under some antecedent, typically a branch condition. */
class DebugImplication(val id: Int,
                       val antecedentTerm: Option[Term],
                       val antecedentExp: Option[ast.Exp],
                       val antecedentFinalExp: Option[ast.Exp],
                       override val children: InsertionOrderedSet[DebugNode],
                       override val isInternal: Boolean = false) extends DebugGroup {

  def description: Option[String] = None

  override def originalExp: Option[ast.Exp] = antecedentExp
  override def finalExp: Option[ast.Exp] = antecedentFinalExp
  override def term: Option[Term] = antecedentTerm

  /* The antecedent is the term this node stands for, so it is never overwritten. */
  def withTerm(newTerm: Term): DebugImplication = this

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugImplication =
    new DebugImplication(id, antecedentTerm, antecedentExp, antecedentFinalExp, newChildren, isInternal)

  override def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    assert(antecedentTerm.isDefined)
    Seq(Implies(antecedentTerm.get, And(children.toSeq.flatMap(_.getAllTerms(visited)))))
  }

  override def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal && !config.isPrintInternalEnabled) {
      return ""
    }
    if (children.nonEmpty) {
      getTopLevelString(currDepth, config) + " ==> " +
        childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
    } else {
      "true"
    }
  }
}

object DebugImplication {
  def apply(antecedentTerm: Option[Term],
            antecedentExp: Option[ast.Exp],
            antecedentFinalExp: Option[ast.Exp],
            children: InsertionOrderedSet[DebugNode],
            isInternal: Boolean = false): DebugImplication =
    new DebugImplication(DebugCounter.next(),
                         antecedentTerm,
                         antecedentExp.map(Simplifier.simplify(_, assumeWelldefinedness = true)),
                         antecedentFinalExp.map(Simplifier.simplify(_, assumeWelldefinedness = true)),
                         children,
                         isInternal)
}

/** A group of assumptions that hold for all (or some) instantiations of the quantified variables. */
class DebugQuantifier(val id: Int,
                      override val isInternal: Boolean,
                      val quantifier: String,
                      val qvarsExp: Seq[ast.Exp],
                      val qvarsTerm: Seq[Var],
                      val triggersExp: Seq[ast.Trigger],
                      val triggersTerm: Seq[Trigger],
                      override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = None
  override val term: Option[Term] = None

  def isUniversal: Boolean = quantifier == "QA"

  /* The term is the quantification built from the children, so it is never overwritten. */
  def withTerm(newTerm: Term): DebugQuantifier = this

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugQuantifier =
    new DebugQuantifier(id, isInternal, quantifier, qvarsExp, qvarsTerm, triggersExp, triggersTerm, newChildren)

  override def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    val q = if (isUniversal) Forall else Exists
    Seq(Quantification(q, qvarsTerm, And(children.toSeq.flatMap(_.getAllTerms(visited))), triggersTerm))
  }

  override def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal && !config.isPrintInternalEnabled) {
      return ""
    }
    if (qvarsExp.nonEmpty) {
      "\n\t" + ("\t" * currDepth) + "[" + id + "] " + (if (isUniversal) "forall" else "exists") + " " +
        qvarsExp.mkString(", ") + " :: " +
        childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
    } else {
      getTopLevelString(currDepth, config)
    }
  }
}

object DebugQuantifier {
  def apply(isInternal: Boolean,
            quantifier: String,
            qvarsExp: Seq[ast.Exp],
            qvarsTerm: Seq[Var],
            triggersExp: Seq[ast.Trigger],
            triggersTerm: Seq[Trigger],
            children: InsertionOrderedSet[DebugNode]): DebugQuantifier =
    new DebugQuantifier(DebugCounter.next(), isInternal, quantifier, qvarsExp, qvarsTerm, triggersExp, triggersTerm, children)
}

/** The assumptions carried over from a loop invariant once the loop has been left. */
class DebugInvariant(val id: Int,
                     val pos: ast.Position,
                     override val children: InsertionOrderedSet[DebugNode],
                     override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some(s"Loop invariant ($posString)")
  override val isInternal: Boolean = false

  private def posString: String = pos match {
    case lc: ast.HasLineColumn => s"${lc.line}.${lc.column}"
    case _ => "position unknown"
  }

  def withTerm(newTerm: Term): DebugInvariant =
    new DebugInvariant(id, pos, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugInvariant =
    new DebugInvariant(id, pos, newChildren, term)
}

object DebugInvariant {
  def apply(pos: ast.Position, children: InsertionOrderedSet[DebugNode]): DebugInvariant =
    new DebugInvariant(DebugCounter.next(), pos, children)
}

/** The path conditions of one branch, assumed again once the branches have been joined. */
class DebugBranchJoin(val id: Int,
                      override val children: InsertionOrderedSet[DebugNode],
                      override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some("Joined path conditions")
  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugBranchJoin =
    new DebugBranchJoin(id, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugBranchJoin =
    new DebugBranchJoin(id, newChildren, term)
}

object DebugBranchJoin {
  def apply(children: InsertionOrderedSet[DebugNode]): DebugBranchJoin =
    new DebugBranchJoin(DebugCounter.next(), children)
}

/** The assumption that execution continues along one of the branches that turned out feasible. */
class DebugFeasibleBranches(val id: Int,
                            override val originalExp: Option[ast.Exp],
                            override val finalExp: Option[ast.Exp],
                            override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = Some("Feasible branches")
  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugFeasibleBranches =
    new DebugFeasibleBranches(id, originalExp, finalExp, Some(newTerm))
}

object DebugFeasibleBranches {
  def apply(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugFeasibleBranches =
    new DebugFeasibleBranches(DebugCounter.next(), originalExp, finalExp)
}

/** The assumption binding a `let` variable to the expression it stands for. */
class DebugLetBinding(val id: Int,
                      val boundVar: ast.AbstractLocalVar,
                      override val children: InsertionOrderedSet[DebugNode],
                      override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some(s"Binding of let variable ${boundVar.name}")
  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugLetBinding =
    new DebugLetBinding(id, boundVar, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugLetBinding =
    new DebugLetBinding(id, boundVar, newChildren, term)
}

object DebugLetBinding {
  def apply(boundVar: ast.AbstractLocalVar, children: InsertionOrderedSet[DebugNode]): DebugLetBinding =
    new DebugLetBinding(DebugCounter.next(), boundVar, children)
}

/** Assumptions added by the path conditions of a sub-evaluation, replayed into the current state. */
class DebugPathConditionDelta(val id: Int,
                              override val children: InsertionOrderedSet[DebugNode],
                              override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some("Path conditions of evaluation")
  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugPathConditionDelta =
    new DebugPathConditionDelta(id, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugPathConditionDelta =
    new DebugPathConditionDelta(id, newChildren, term)
}

object DebugPathConditionDelta {
  def apply(children: InsertionOrderedSet[DebugNode]): DebugPathConditionDelta =
    new DebugPathConditionDelta(DebugCounter.next(), children)
}

/** The assumption that a function's precondition holds at one of its applications. */
class DebugFnPrecondition(val id: Int,
                          val fnName: String,
                          val argsExp: Seq[ast.Exp],
                          val argsTerm: Seq[Term],
                          val heapLabel: Option[String],
                          override val children: InsertionOrderedSet[DebugNode],
                          override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = {
    val where = heapLabel.map(l => s" in heap $l").getOrElse("")
    val args = if (argsExp.isEmpty) "" else s"(${argsExp.mkString(", ")})"
    Some(s"Precondition of $fnName$args holds$where")
  }

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugFnPrecondition =
    new DebugFnPrecondition(id, fnName, argsExp, argsTerm, heapLabel, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugFnPrecondition =
    new DebugFnPrecondition(id, fnName, argsExp, argsTerm, heapLabel, newChildren, term)
}

object DebugFnPrecondition {
  def apply(fnName: String,
            argsExp: Seq[ast.Exp],
            argsTerm: Seq[Term] = Seq.empty,
            heapLabel: Option[String] = None,
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugFnPrecondition =
    new DebugFnPrecondition(DebugCounter.next(), fnName, argsExp, argsTerm, heapLabel, children)
}

/*/** The assumption that the preconditions of the functions inside a quantifier hold. */
class DebugQuantifiedFnPreconditions(val id: Int,
                                     val quantifiedExp: ast.Exp,
                                     override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(s"Function preconditions hold in quantifier $quantifiedExp")

  def withTerm(newTerm: Option[Term]): DebugQuantifiedFnPreconditions =
    new DebugQuantifiedFnPreconditions(id, quantifiedExp, newTerm)
}

object DebugQuantifiedFnPreconditions {
  def apply(quantifiedExp: ast.Exp): DebugQuantifiedFnPreconditions =
    new DebugQuantifiedFnPreconditions(DebugCounter.next(), quantifiedExp)
}*/

/** Assumptions made while folding a predicate. */
class DebugFold(val id: Int,
                val predicateExp: ast.PredicateAccess,
                override val children: InsertionOrderedSet[DebugNode],
                override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some(s"Folded $predicateExp")

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugFold =
    new DebugFold(id, predicateExp, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugFold =
    new DebugFold(id, predicateExp, newChildren, term)
}

object DebugFold {
  def apply(predicateExp: ast.PredicateAccess,
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugFold =
    new DebugFold(DebugCounter.next(), predicateExp, children)
}

/** Assumptions made while unfolding a predicate in a statement. */
class DebugUnfold(val id: Int,
                  val predicateExp: ast.PredicateAccess,
                  override val children: InsertionOrderedSet[DebugNode],
                  override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some(s"Unfolded $predicateExp")

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugUnfold =
    new DebugUnfold(id, predicateExp, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugUnfold =
    new DebugUnfold(id, predicateExp, newChildren, term)
}

object DebugUnfold {
  def apply(predicateExp: ast.PredicateAccess,
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugUnfold =
    new DebugUnfold(DebugCounter.next(), predicateExp, children)
}

/** Assumptions made while evaluating an `unfolding ... in ...` expression. */
class DebugUnfolding(val id: Int,
                     val predicateName: String,
                     val argsExp: Seq[ast.Exp],
                     val heapLabel: Option[String],
                     override val children: InsertionOrderedSet[DebugNode],
                     override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = {
    val where = heapLabel.map(l => s" in heap $l").getOrElse("")
    Some(s"Unfolding of $predicateName(${argsExp.mkString(", ")})$where")
  }

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugUnfolding =
    new DebugUnfolding(id, predicateName, argsExp, heapLabel, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugUnfolding =
    new DebugUnfolding(id, predicateName, argsExp, heapLabel, newChildren, term)
}

object DebugUnfolding {
  def apply(predicateName: String,
            argsExp: Seq[ast.Exp],
            heapLabel: Option[String],
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugUnfolding =
    new DebugUnfolding(DebugCounter.next(), predicateName, argsExp, heapLabel, children)
}

/** Assumptions taken from the body of a predicate that has just been unfolded. */
/*class DebugUnfoldedPredicateBody(val id: Int,
                                 override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = Some("Assumption from unfolded predicate body")

  def withTerm(newTerm: Option[Term]): DebugUnfoldedPredicateBody =
    new DebugUnfoldedPredicateBody(id, newTerm)
}

object DebugUnfoldedPredicateBody {
  def apply(): DebugUnfoldedPredicateBody =
    new DebugUnfoldedPredicateBody(DebugCounter.next())
}*/

/** Assumptions made while taking permissions to a resource out of the heap. */
class DebugConsumePermissions(val id: Int,
                              val resource: String,
                              override val children: InsertionOrderedSet[DebugNode],
                              override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = Some(s"Consume permissions for $resource")

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugConsumePermissions =
    new DebugConsumePermissions(id, resource, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugConsumePermissions =
    new DebugConsumePermissions(id, resource, newChildren, term)
}

object DebugConsumePermissions {
  def apply(resource: String,
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugConsumePermissions =
    new DebugConsumePermissions(DebugCounter.next(), resource, children)
}

/* -------------------------------------------------------------------------------------------- *
 * Snapshots                                                                                      *
 * -------------------------------------------------------------------------------------------- */

sealed trait SnapshotKind {
  def description: String
}

object SnapshotKind {
  /** The snapshot of a resource, equated with the snapshots of its parts. */
  case object Definition extends SnapshotKind {
    val description = "Snapshot definition"
  }
  /** Snapshot equalities introduced when merging heaps during state consolidation. */
  case object Equation extends SnapshotKind {
    val description = "Snapshot equations"
  }
  /** The snapshot of an assertion that carries no value, such as one without permissions. */
  case object Empty extends SnapshotKind {
    val description = "Empty snapshot"
  }
  /** The snapshot of a magic wand. */
  case object MagicWand extends SnapshotKind {
    val description = "Magic wand snapshot definition"
  }
  /** The path conditions defining a magic wand snapshot function. */
  case object MagicWandFunction extends SnapshotKind {
    val description = "MWSF definition path conditions"
  }
}

/** An assumption defining or relating the snapshots that record the values held by a resource. */
class DebugSnapshot(val id: Int,
                    val kind: SnapshotKind,
                    override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = Some(kind.description)

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugSnapshot =
    new DebugSnapshot(id, kind, Some(newTerm))
}

object DebugSnapshot {
  def apply(kind: SnapshotKind): DebugSnapshot =
    new DebugSnapshot(DebugCounter.next(), kind)
}

/* -------------------------------------------------------------------------------------------- *
 * Snapshot maps                                                                                  *
 * -------------------------------------------------------------------------------------------- */

sealed trait SnapshotMapKind {
  def description: String
}

object SnapshotMapKind {
  /** Which locations a snapshot map is defined on. */
  case object Domain extends SnapshotMapKind {
    val description = "Definitional axioms for snapshot map domain"
  }
  case object DomainInstantiated extends SnapshotMapKind {
    val description = "Definitional axioms for snapshot map domain (instantiated)"
  }
  /** Which value a snapshot map maps each location to. */
  case object Values extends SnapshotMapKind {
    val description = "Definitional axioms for snapshot map values"
  }
  case object ValuesInstantiated extends SnapshotMapKind {
    val description = "Definitional axioms for snapshot map values (instantiated)"
  }
  /** The value of a snapshot map built for a single location. */
  case object SingletonValue extends SnapshotMapKind {
    val description = "Definitional axioms for singleton-SM's value"
  }
  /** The value of a field value function built for a single location. */
  case object SingletonFvfValue extends SnapshotMapKind {
    val description = "Definitional axioms for singleton-FVF's value"
  }
  /** The values held by a permission map. */
  case object PermissionValues extends SnapshotMapKind {
    val description = "Value definitions"
  }
}

/** An assumption defining the domain or the values of a snapshot map. */
class DebugSnapshotMapDefinition(val id: Int,
                                 val kind: SnapshotMapKind,
                                 override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(kind.description)

  def withTerm(newTerm: Term): DebugSnapshotMapDefinition =
    new DebugSnapshotMapDefinition(id, kind, Some(newTerm))
}

object DebugSnapshotMapDefinition {
  def apply(kind: SnapshotMapKind): DebugSnapshotMapDefinition =
    new DebugSnapshotMapDefinition(DebugCounter.next(), kind)
}

/* -------------------------------------------------------------------------------------------- *
 * Triggers                                                                                       *
 * -------------------------------------------------------------------------------------------- */

sealed trait TriggerKind {
  def description: String
}

object TriggerKind {
  case object Field extends TriggerKind {
    val description = "FieldTrigger"
  }
  case object Predicate extends TriggerKind {
    val description = "PredicateTrigger"
  }
  case object Resource extends TriggerKind {
    val description = "Resource trigger"
  }
  /** Triggers assumed for the resources reachable in the current heap. */
  case object Heap extends TriggerKind {
    val description = "Heap triggers"
  }
  /** Triggers assumed for the inverse functions of a quantified permission. */
  case object InverseFunction extends TriggerKind {
    val description = "Inverse trigger"
  }
}

/** An assumption that exists only to give the prover a term to trigger quantifiers on. */
class DebugResourceTrigger(val id: Int,
                           val kind: TriggerKind,
                           val resourceName: Option[String],
                           val argsExp: Seq[ast.Exp],
                           val argsTerm: Seq[Term],
                           override val originalExp: Option[ast.Exp] = None,
                           override val finalExp: Option[ast.Exp] = None,
                           override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = {
    val target = resourceName match {
      case Some(name) if argsExp.nonEmpty => s"($name(${argsExp.mkString(", ")}))"
      case Some(name) => s"($name)"
      case None if argsExp.nonEmpty => s"(${argsExp.mkString(", ")})"
      case None => ""
    }
    Some(s"${kind.description}$target")
  }

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugResourceTrigger =
    new DebugResourceTrigger(id, kind, resourceName, argsExp, argsTerm, originalExp, finalExp, Some(newTerm))
}

object DebugResourceTrigger {
  def apply(kind: TriggerKind,
            resourceName: Option[String] = None,
            argsExp: Seq[ast.Exp] = Seq.empty,
            argsTerm: Seq[Term] = Seq.empty,
            resourceExp: Option[ast.Exp] = None): DebugResourceTrigger =
    new DebugResourceTrigger(DebugCounter.next(), kind, resourceName, argsExp, argsTerm, resourceExp, resourceExp)

  /** A field trigger, whose target is written as `receiver.field` rather than as an application. */
  def field(receiver: ast.Exp, fieldName: String): DebugResourceTrigger =
    apply(TriggerKind.Field, Some(s"$receiver.$fieldName"))
}

/* -------------------------------------------------------------------------------------------- *
 * Quantified permissions                                                                         *
 * -------------------------------------------------------------------------------------------- */

sealed trait InverseFunctionKind {
  def description: String
}

object InverseFunctionKind {
  /** The axioms that define the inverse functions of a quantified permission. */
  case object Definitional extends InverseFunctionKind {
    val description = "Definitional axioms for inverse functions"
  }
  /** The same, for the inverse functions introduced by a `havocall`. */
  case object HavocallDefinitional extends InverseFunctionKind {
    val description = "Definitional axioms for havocall inverse functions"
  }
  /** The axioms stating that the inverse functions really are inverses. */
  case object Axioms extends InverseFunctionKind {
    val description = "Inverse function axioms"
  }
  /** The inverse functions introduced for a quantified permission. */
  case object QuantifiedPermission extends InverseFunctionKind {
    val description = "Inverse functions for quantified permission"
  }
}

/** An assumption about the inverse functions used to reason about quantified permissions. */
class DebugInverseFunctions(val id: Int,
                            val kind: InverseFunctionKind,
                            override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(kind.description)

  def withTerm(newTerm: Term): DebugInverseFunctions =
    new DebugInverseFunctions(id, kind, Some(newTerm))
}

object DebugInverseFunctions {
  def apply(kind: InverseFunctionKind): DebugInverseFunctions =
    new DebugInverseFunctions(DebugCounter.next(), kind)
}

/**
 * The well-definedness conditions of the check that the receivers of a quantified permission are
 * pairwise distinct, assumed before the check itself is made.
 */
class DebugInjectivityCheck(val id: Int,
                            override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("QP receiver injectivity check is well-defined")

  def withTerm(newTerm: Term): DebugInjectivityCheck =
    new DebugInjectivityCheck(id, Some(newTerm))
}

object DebugInjectivityCheck {
  def apply(): DebugInjectivityCheck =
    new DebugInjectivityCheck(DebugCounter.next())
}

/** The assumption that two quantified chunks describe the same locations. */
class DebugChunkAlias(val id: Int,
                      override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("Chunks alias")

  def withTerm(newTerm: Term): DebugChunkAlias =
    new DebugChunkAlias(id, Some(newTerm))
}

object DebugChunkAlias {
  def apply(): DebugChunkAlias =
    new DebugChunkAlias(DebugCounter.next())
}

/** Well-definedness conditions collected while evaluating the body of a quantifier. They are split
  * into those that hold globally and those that only hold under the current branch conditions.
  */
class DebugAuxiliaryTerms(val id: Int,
                          val areGlobal: Boolean,
                          val fromEvaluation: Boolean,
                          override val children: InsertionOrderedSet[DebugNode],
                          override val term: Option[Term] = None) extends DebugGroup {

  def description: Option[String] = {
    val scope = if (areGlobal) "globals" else "non-globals"
    val origin = if (fromEvaluation) " (aux)" else ""
    Some(s"Nested auxiliary terms: $scope$origin")
  }

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugAuxiliaryTerms =
    new DebugAuxiliaryTerms(id, areGlobal, fromEvaluation, children, Some(newTerm))

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugAuxiliaryTerms =
    new DebugAuxiliaryTerms(id, areGlobal, fromEvaluation, newChildren, term)
}

object DebugAuxiliaryTerms {
  def apply(areGlobal: Boolean,
            fromEvaluation: Boolean,
            children: InsertionOrderedSet[DebugNode]): DebugAuxiliaryTerms =
    new DebugAuxiliaryTerms(DebugCounter.next(), areGlobal, fromEvaluation, children)
}

/* -------------------------------------------------------------------------------------------- *
 * Heap manipulation                                                                              *
 * -------------------------------------------------------------------------------------------- */

/** The assumption that newly allocated references differ from the ones already in the heap. */
class DebugReferenceDisjointness(val id: Int,
                                 override val originalExp: Option[ast.Exp],
                                 override val finalExp: Option[ast.Exp],
                                 override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = Some("Reference disjointness")

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugReferenceDisjointness =
    new DebugReferenceDisjointness(id, originalExp, finalExp, Some(newTerm))
}

object DebugReferenceDisjointness {
  def apply(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugReferenceDisjointness =
    new DebugReferenceDisjointness(DebugCounter.next(), originalExp, finalExp)
}

/** The axiom relating a heap before and after a `havoc`, for the locations it does not affect. */
class DebugHavoc(val id: Int,
                 override val term: Option[Term] = None) extends DebugNode {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("Havoc axiom")

  def withTerm(newTerm: Term): DebugHavoc =
    new DebugHavoc(id, Some(newTerm))
}

object DebugHavoc {
  def apply(): DebugHavoc =
    new DebugHavoc(DebugCounter.next())
}

/* -------------------------------------------------------------------------------------------- *
 * Failed assertions                                                                              *
 * -------------------------------------------------------------------------------------------- */

/**
 * The assertion that failed, recorded alongside the assumptions so the debugger can present the
 * two together. Unlike the categories above, this is not itself an assumption.
 */
class DebugFailedAssertion(val id: Int,
                           val assertionDescription: Option[String],
                           override val originalExp: Option[ast.Exp],
                           override val finalExp: Option[ast.Exp],
                           override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] = assertionDescription

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugFailedAssertion =
    new DebugFailedAssertion(id, assertionDescription, originalExp, finalExp, Some(newTerm))
}

object DebugFailedAssertion {
  def apply(assertionDescription: String): DebugFailedAssertion =
    new DebugFailedAssertion(DebugCounter.next(), Some(assertionDescription), None, None)

  def apply(originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugFailedAssertion =
    new DebugFailedAssertion(DebugCounter.next(), None, originalExp, finalExp)
}

/** Stands in for an assertion whose term Silicon could not build, and which therefore cannot hold. */
class DebugMissingTerm(val id: Int,
                       val missingTermDescription: String,
                       override val term: Option[Term] = None) extends DebugNode {

  def description: Option[String] =
    Some(s"Asserted term for '$missingTermDescription' not available, substituting false.")

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugMissingTerm =
    new DebugMissingTerm(id, missingTermDescription, Some(newTerm))
}

object DebugMissingTerm {
  def apply(missingTermDescription: String): DebugMissingTerm =
    new DebugMissingTerm(DebugCounter.next(), missingTermDescription)
}

/* -------------------------------------------------------------------------------------------- *
 * Printing                                                                                       *
 * -------------------------------------------------------------------------------------------- */

class DebugExpPrintConfiguration {
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
