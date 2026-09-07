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
import viper.silver.ast.Exp
import viper.silver.ast.utility.Simplifier

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

object DebugCounter {
  private val idCounter: AtomicInteger = new AtomicInteger(0)

  def next(): Int = idCounter.getAndIncrement()
}

/** A node is either a single assumption of a particular type, or a DebugGroup with children.
  */
sealed trait DebugNode {
  val id: Int
  def isInternal: Boolean
  def isGlobal: Boolean
  def description: Option[String]

  def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term]
  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode]): Option[DebugNode]

  def getTopLevelString(currDepth: Int, config: DebugExpPrintConfiguration): String
  def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String
  def toString(config: DebugExpPrintConfiguration): String = {
    toString(0, config.printHierarchyLevel, config)
  }
  override def toString: String = {
    toString(0, 6, new DebugExpPrintConfiguration)
  }
}

sealed trait DebugAssumption extends DebugNode {
  def term: Term
  def finalExp: Option[Exp] = None
  def originalExp: Option[Exp] = None

  lazy val isGlobal: Boolean = PathConditions.isGlobal(term)

  /** Returns a copy of this node with a new term. Used when some original terms already known to hold
   * are filtered out.
   */
  def withTerm(newTerm: Term): DebugNode

  override def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = Seq(term)
  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode]): Option[DebugNode] =
    Option.when(this.id == soughtId)(this)

  def getTopLevelString(currDepth: Int, config: DebugExpPrintConfiguration): String = {
    ""
  }

  def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = ""
}

/** A category that groups the assumptions made underneath it, rather than standing alone. */
sealed trait DebugGroup extends DebugNode {
  def children: InsertionOrderedSet[DebugNode]

  /** Returns a copy of this node with different children. */
  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugGroup

  lazy val isGlobal: Boolean = children.forall(_.isGlobal)

  def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    children.toSeq.flatMap(_.getAllTerms(visited))
  }

  def removeChildrenById(ids: Seq[Int]): DebugNode = {
    if (this.children.nonEmpty) {
      val filtered = children.filter(c => !ids.contains(c.id))
      val newChildren = filtered.map {
        case g: DebugGroup => g.removeChildrenById(ids)
        case c => c
      }
      this.withChildren(newChildren)
    } else this
  }

  def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode]): Option[DebugNode] = {
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
    // val toDisplay = if (config.printInternalTermRepresentation) Some(term) else finalExp
    // val delimiter = if (toDisplay.isDefined && description.isDefined) ": " else ""
    // "\n\t" + ("\t" * currDepth) + "[" + id + "] " + description.getOrElse("") + delimiter + toDisplay.getOrElse("")
    ""
  }

  def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = {
    if (isInternal && !config.isPrintInternalEnabled) {
      return ""
    }
    getTopLevelString(currDepth, config) +
      childrenToString(currDepth, math.max(maxDepth, config.nodeToHierarchyLevelMap.getOrElse(id, 0)), config)
  }
}

/* -------------------------------------------------------------------------------------------- *
 * Assumptions                                                                                  *
 * -------------------------------------------------------------------------------------------- */

/** An assumption directly from the source program.
  */
class DebugExp(val id: Int,
               val term: Term,
               val ogExp: Exp,
               val fnExp: Exp,
               override val isInternal: Boolean) extends DebugAssumption {

  def description: Option[String] = None

  override def originalExp: Option[Exp] = Some(ogExp)

  def withTerm(newTerm: Term): DebugExp =
    new DebugExp(id, newTerm, ogExp, fnExp, isInternal)
}

object DebugExp {
  def apply(term: Term, originalExp: Exp, finalExp: Exp, isInternal: Boolean): DebugExp =
    new DebugExp(DebugCounter.next(),
                 term,
                 Simplifier.simplify(originalExp, assumeWelldefinedness = true),
                 Simplifier.simplify(finalExp, assumeWelldefinedness = true),
                 isInternal)
}

/** An assumption that a permission amount is positive, made while evaluating a `perm` expression. */
class DebugPermissionPositive(val id: Int,
                              val term: Term,
                              val permExp: Exp) extends DebugAssumption {

  override def isInternal: Boolean = true // TODO: Check if this is correct

  def description: Option[String] = Some(s"$permExp > none")

  def withTerm(newTerm: Term): DebugPermissionPositive =
    new DebugPermissionPositive(id, newTerm, permExp)
}

object DebugPermissionPositive {
  def apply(term: Term, permExp: Exp): DebugPermissionPositive =
    new DebugPermissionPositive(DebugCounter.next(), term, permExp)
}

/** The assumption that a function's precondition holds at one of its applications. */
class DebugFnPrecondition(val id: Int,
                          val term: Term,
                          val fnName: String,
                          val argsExp: Seq[Exp],
                          val heapLabel: Option[String]) extends DebugAssumption {

  def description: Option[String] = {
    val where = heapLabel.map(l => s" in heap $l").getOrElse("")
    val args = if (argsExp.isEmpty) "" else s"(${argsExp.mkString(", ")})"
    Some(s"Precondition of $fnName$args holds$where")
  }

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugFnPrecondition = this
}

object DebugFnPrecondition {
  def apply(term: Term,
            fnName: String,
            argsExp: Seq[Exp],
            heapLabel: Option[String]): DebugFnPrecondition =
    new DebugFnPrecondition(DebugCounter.next(), term, fnName, argsExp, heapLabel)
}

/** The assumption that execution continues along one of the branches that turned out feasible. */
class DebugFeasibleBranches(val id: Int,
                            val term: Term,
                            override val originalExp: Option[ast.Exp],
                            override val finalExp: Option[ast.Exp]) extends DebugAssumption {

  def description: Option[String] = Some("Feasible branches")
  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugFeasibleBranches =
    new DebugFeasibleBranches(id, newTerm, originalExp, finalExp)
}

object DebugFeasibleBranches {
  def apply(term: Term, originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugFeasibleBranches =
    new DebugFeasibleBranches(DebugCounter.next(), term, originalExp, finalExp)
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
/*class DebugConsumePermissions(val id: Int,
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
}*/


/* -------------------------------------------------------------------------------------------- *
 * Snapshots                                                                                      *
 * -------------------------------------------------------------------------------------------- */

sealed trait DebugSnapshotKind {
  def description: String
}

object DebugSnapshotKind {
  /** The snapshot of a resource, equated with the snapshots of its parts. */
  case object Definition extends DebugSnapshotKind {
    val description = "Snapshot definition"
  }
  /** Snapshot equalities introduced when merging heaps during state consolidation. */
  case object Equation extends DebugSnapshotKind {
    val description = "Snapshot equations"
  }
  /** The snapshot of an assertion that carries no value, such as one without permissions. */
  case object Empty extends DebugSnapshotKind {
    val description = "Empty snapshot"
  }
  /** The snapshot of a magic wand. */
  case object MagicWand extends DebugSnapshotKind {
    val description = "Magic wand snapshot definition"
  }
  /** The path conditions defining a magic wand snapshot function. */
  case object MagicWandFunction extends DebugSnapshotKind {
    val description = "MWSF definition path conditions"
  }
}

/** An assumption defining or relating snapshots, typically an equality. */
class DebugSnapshot(val id: Int,
                    val term: Term,
                    val kind: DebugSnapshotKind) extends DebugAssumption {

  def description: Option[String] = Some(kind.description)

  override def isInternal: Boolean = true

  def withTerm(newTerm: Term): DebugSnapshot =
    new DebugSnapshot(id, newTerm, kind)
}

object DebugSnapshot {
  def apply(term: Term, kind: DebugSnapshotKind): DebugSnapshot =
    new DebugSnapshot(DebugCounter.next(), term, kind)
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
                                 val term: Term,
                                 val kind: SnapshotMapKind) extends DebugAssumption {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(kind.description)

  def withTerm(newTerm: Term): DebugSnapshotMapDefinition =
    new DebugSnapshotMapDefinition(id, newTerm, kind)
}

object DebugSnapshotMapDefinition {
  def apply(term: Term, kind: SnapshotMapKind): DebugSnapshotMapDefinition =
    new DebugSnapshotMapDefinition(DebugCounter.next(), term, kind)
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
                           val term: Term,
                           val kind: TriggerKind,
                           val resourceName: Option[String],
                           val argsExp: Seq[ast.Exp],
                           val argsTerm: Seq[Term],
                           override val originalExp: Option[ast.Exp] = None,
                           override val finalExp: Option[ast.Exp] = None) extends DebugAssumption {

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
    new DebugResourceTrigger(id, newTerm, kind, resourceName, argsExp, argsTerm, originalExp, finalExp)
}

object DebugResourceTrigger {
  def apply(term: Term,
            kind: TriggerKind,
            resourceName: Option[String] = None,
            argsExp: Seq[ast.Exp] = Seq.empty,
            argsTerm: Seq[Term] = Seq.empty,
            resourceExp: Option[ast.Exp] = None): DebugResourceTrigger =
    new DebugResourceTrigger(DebugCounter.next(), term, kind, resourceName, argsExp, argsTerm, resourceExp, resourceExp)

  /** A field trigger, whose target is written as `receiver.field` rather than as an application. */
  // def field(receiver: ast.Exp, fieldName: String): DebugResourceTrigger =
  //   apply(TriggerKind.Field, Some(s"$receiver.$fieldName"))
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
                            val term: Term,
                            val kind: InverseFunctionKind) extends DebugAssumption {

  override def isInternal: Boolean = true

  def description: Option[String] = Some(kind.description)

  def withTerm(newTerm: Term): DebugInverseFunctions =
    new DebugInverseFunctions(id, newTerm, kind)
}

object DebugInverseFunctions {
  def apply(term: Term, kind: InverseFunctionKind): DebugInverseFunctions =
    new DebugInverseFunctions(DebugCounter.next(), term, kind)
}

/**
 * The well-definedness conditions of the check that the receivers of a quantified permission are
 * pairwise distinct, assumed before the check itself is made.
 */
class DebugInjectivityCheck(val id: Int,
                            val term: Term) extends DebugAssumption {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("QP receiver injectivity check is well-defined")

  def withTerm(newTerm: Term): DebugInjectivityCheck =
    new DebugInjectivityCheck(id, newTerm)
}

object DebugInjectivityCheck {
  def apply(term: Term): DebugInjectivityCheck =
    new DebugInjectivityCheck(DebugCounter.next(), term)
}

/** The assumption that two quantified chunks describe the same locations. */
class DebugChunkAlias(val id: Int,
                      val term: Term) extends DebugAssumption {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("Chunks alias")

  def withTerm(newTerm: Term): DebugChunkAlias =
    new DebugChunkAlias(id, newTerm)
}

object DebugChunkAlias {
  def apply(term: Term): DebugChunkAlias =
    new DebugChunkAlias(DebugCounter.next(), term)
}

class DebugRefDisjoint(val id: Int,
                       val term: Term,
                       override val originalExp: Option[Exp],
                       override val finalExp: Option[Exp]) extends DebugAssumption {

  def description: Option[String] = Some("Reference disjointness")

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugRefDisjoint =
    new DebugRefDisjoint(id, newTerm, originalExp, finalExp)
}

object DebugRefDisjoint {
  def apply(term: Term, originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugRefDisjoint =
    new DebugRefDisjoint(DebugCounter.next(), term, originalExp, finalExp)
}

/** The axiom relating a heap before and after a `havoc`, for the locations it does not affect. */
class DebugHavoc(val id: Int,
                 val term: Term) extends DebugAssumption {

  override def isInternal: Boolean = true

  def description: Option[String] = Some("Havoc axiom")

  def withTerm(newTerm: Term): DebugHavoc =
    new DebugHavoc(id, newTerm)
}

object DebugHavoc {
  def apply(term: Term): DebugHavoc =
    new DebugHavoc(DebugCounter.next(), term)
}

/** The assertion that failed, recorded alongside the assumptions so the debugger can present the
  * two together. Unlike the categories above, this is not itself an assumption.
  * // TODO: Why is this a DebugExp? Can we just remove it?
  */
class DebugFailedAssertion(val id: Int,
                           val term: Term,
                           val assertionDescription: Option[String],
                           val originalExp: Option[Exp],
                           val finalExp: Option[Exp]) extends DebugNode {

  def description: Option[String] = assertionDescription

  override def isInternal: Boolean = false

  override def isGlobal: Boolean = true

  def withTerm(newTerm: Term): DebugFailedAssertion =
    new DebugFailedAssertion(id, newTerm, assertionDescription, originalExp, finalExp)

  override def getTopLevelString(currDepth: Int, config: DebugExpPrintConfiguration): String = ???

  override def toString(currDepth: Int, maxDepth: Int, config: DebugExpPrintConfiguration): String = ???

  override def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = ???

  override def getNodeWithId(soughtId: Int, visited: mutable.HashSet[DebugNode]): Option[DebugNode] =
    Option.when(id == soughtId)(this)
}

object DebugFailedAssertion {
  def apply(term: Term, assertionDescription: String): DebugFailedAssertion =
    new DebugFailedAssertion(DebugCounter.next(), term, Some(assertionDescription), None, None)

  def apply(term: Term, originalExp: Option[ast.Exp], finalExp: Option[ast.Exp]): DebugFailedAssertion =
    new DebugFailedAssertion(DebugCounter.next(), term, None, originalExp, finalExp)
}

/** Stands in for an assertion whose term Silicon could not build, and which therefore cannot hold. */
// TODO: no idea what this should be
/*class DebugMissingTerm(val id: Int,
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
}*/

/* -------------------------------------------------------------------------------------------- *
 * Groups                                                                                       *
 * -------------------------------------------------------------------------------------------- */

/** A group of assumptions that only hold under some antecedent, typically a branch condition. */
class DebugImplication(val id: Int,
                       val antecedentTerm: Term,
                       val antecedentExp: Option[Exp],
                       val antecedentFinalExp: Option[Exp],
                       override val children: InsertionOrderedSet[DebugNode],
                       override val isInternal: Boolean = false) extends DebugGroup {

  def description: Option[String] = None

  /* The antecedent is the term this node stands for, so it is never overwritten. */
  def withTerm(newTerm: Term): DebugImplication = this

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugImplication =
    new DebugImplication(id, antecedentTerm, antecedentExp, antecedentFinalExp, newChildren, isInternal)

  override def getAllTerms(visited: mutable.HashSet[DebugNode]): Seq[Term] = {
    if (visited.contains(this))
      return Seq.empty
    visited.add(this)
    Seq(Implies(antecedentTerm, And(children.toSeq.flatMap(_.getAllTerms(visited)))))
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
  def apply(antecedentTerm: Term,
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

/** A group of assumptions that hold under a quantifier. */
class DebugQuantifier(val id: Int,
                      val isUniversal: Boolean,
                      val qvarsTerm: Seq[Var],
                      val qvarsExp: Seq[Exp],
                      val triggersTerm: Seq[Trigger],
                      val triggersExp: Seq[ast.Trigger],
                      override val isInternal: Boolean,
                      override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = None

  /* The term is the quantification built from the children, so it is never overwritten. */
  def withTerm(newTerm: Term): DebugQuantifier = this

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugQuantifier =
    new DebugQuantifier(id, isUniversal, qvarsTerm, qvarsExp, triggersTerm, triggersExp, isInternal, newChildren)

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
  def apply(isUniversal: Boolean,
            qvarsTerm: Seq[Var],
            qvarsExp: Seq[Exp],
            triggersTerm: Seq[Trigger],
            triggersExp: Seq[ast.Trigger],
            isInternal: Boolean,
            children: InsertionOrderedSet[DebugNode]): DebugQuantifier =
    new DebugQuantifier(DebugCounter.next(), isUniversal, qvarsTerm, qvarsExp, triggersTerm, triggersExp, isInternal, children)
}

/** All loop invariants grouped together, either inside or after the loop. */
class DebugInvariant(val id: Int,
                     val pos: ast.Position,
                     override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = Some(s"Loop invariant ($posString)")
  override val isInternal: Boolean = false

  private def posString: String = pos match {
    case lc: ast.HasLineColumn => s"${lc.line}.${lc.column}"
    case _ => "position unknown"
  }

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugInvariant =
    new DebugInvariant(id, pos, newChildren)
}

object DebugInvariant {
  def apply(pos: ast.Position, children: InsertionOrderedSet[DebugNode]): DebugInvariant =
    new DebugInvariant(DebugCounter.next(), pos, children)
}

/** The path conditions of one branch, assumed again once the branches have been joined. */
class DebugBranchJoin(val id: Int,
                      override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = Some("Joined path conditions")
  override def isInternal: Boolean = false

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugBranchJoin =
    new DebugBranchJoin(id, newChildren)
}

object DebugBranchJoin {
  def apply(children: InsertionOrderedSet[DebugNode]): DebugBranchJoin =
    new DebugBranchJoin(DebugCounter.next(), children)
}

/** The assumption binding a `let` variable to the expression it stands for. */
class DebugLetBinding(val id: Int,
                      val boundVar: ast.AbstractLocalVar,
                      override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = Some(s"Binding of let variable ${boundVar.name}")
  override def isInternal: Boolean = false

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugLetBinding =
    new DebugLetBinding(id, boundVar, newChildren)
}

object DebugLetBinding {
  def apply(boundVar: ast.AbstractLocalVar, children: InsertionOrderedSet[DebugNode]): DebugLetBinding =
    new DebugLetBinding(DebugCounter.next(), boundVar, children)
}

/** Assumptions added by the path conditions of a sub-evaluation, replayed into the current state. */
class DebugPathConditionDelta(val id: Int,
                              override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = Some("Path conditions of evaluation")
  override def isInternal: Boolean = true

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugPathConditionDelta =
    new DebugPathConditionDelta(id, newChildren)
}

object DebugPathConditionDelta {
  def apply(children: InsertionOrderedSet[DebugNode]): DebugPathConditionDelta =
    new DebugPathConditionDelta(DebugCounter.next(), children)
}

/** Assumptions made while folding a predicate. */
class DebugFold(val id: Int,
                val term: Term,
                val predicateExp: ast.PredicateAccess,
                override val children: InsertionOrderedSet[DebugNode]) extends DebugGroup {

  def description: Option[String] = Some(s"Folded $predicateExp")

  override def isInternal: Boolean = false

  def withTerm(newTerm: Term): DebugFold =
    new DebugFold(id, newTerm, predicateExp, children)

  def withChildren(newChildren: InsertionOrderedSet[DebugNode]): DebugFold =
    new DebugFold(id, term, predicateExp, newChildren)
}

object DebugFold {
  def apply(term: Term,
            predicateExp: ast.PredicateAccess,
            children: InsertionOrderedSet[DebugNode] = InsertionOrderedSet.empty): DebugFold =
    new DebugFold(DebugCounter.next(), term, predicateExp, children)
}

/** Assumptions made while unfolding a predicate in a statement. */
class DebugUnfold(val id: Int,
                  val predicateExp: ast.PredicateAccess,
                  override val children: InsertionOrderedSet[DebugNode],
                  val term: Option[Term] = None) extends DebugGroup {

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
                     val term: Option[Term] = None) extends DebugGroup {

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

/** Well-definedness conditions collected while evaluating the body of a quantifier. They are split
 * into those that hold globally and those that only hold under the current branch conditions.
 */
class DebugAuxiliaryTerms(val id: Int,
                          val areGlobal: Boolean,
                          val fromEvaluation: Boolean,
                          override val children: InsertionOrderedSet[DebugNode],
                          val term: Option[Term] = None) extends DebugGroup {

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
