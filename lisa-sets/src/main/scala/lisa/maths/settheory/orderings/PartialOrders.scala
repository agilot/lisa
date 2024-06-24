package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Relations.*
import lisa.maths.settheory.Functions.*
import lisa.prooflib.SimpleDeducedSteps.InstantiateForall
import lisa.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 * Linear and Partial Ordering
 */
object PartialOrders extends lisa.Main {

  // var defs
  private val w = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val h = formulaVariable
  private val t = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable

  // relation and function symbols
  private val r = variable
  private val r1 = variable
  private val r2 = variable
  private val p = variable
  private val q = variable
  private val f = variable
  private val g = variable
  private val F = function[1]
  private val G = function[2]

  private val P = predicate[1]
  private val Q = predicate[1]
  private val schemPred = predicate[1]

  /**
   * Definition --- Strict Partial Order
   *
   * A strict partial order is a relation that is irreflexive and transitive.
   */
  val strictPartialOrder = DEF(r, x) --> irreflexive(r, x) /\ transitive(r, x)

  /**
   * Theorem --- Strict partial order introduction rule
   *
   *   `r ⊆ x × x, irreflexive(r, x), transitive(r, x) ⊢ strictPartialOrder(r, x)`
   */
  val strictPartialOrderIntro = Lemma((irreflexive(r, x), transitive(r, x)) |- strictPartialOrder(r, x)) {
    have(thesis) by Weakening(strictPartialOrder.definition)
  }

  /**
   * Theorem --- A strict partial order is irreflexive
   *
   *   `strictPartialOrder(r, x) ⊢ irreflexive(r, x)`
   */
  val strictPartialOrderIrreflexive = Lemma(
    strictPartialOrder(r, x) |- irreflexive(r, x)
  ) {
    have(thesis) by Weakening(strictPartialOrder.definition)
  }

  /**
   * Theorem --- A strict partial order is transitive
   *
   *   `strictPartialOrder(r, x) ⊢ transitive(r, x)`
   */
  val strictPartialOrderTransitive = Lemma(
    strictPartialOrder(r, x) |- transitive(r, x)
  ) {
    have(thesis) by Weakening(strictPartialOrder.definition)
  }

  /**
   * Theorem --- A strict partial order is a relation
   *
   *   `strictPartialOrder(r, x) ⊢ relationBetween(r, x, x)`
   */
  val strictPartialOrderIsRelation = Lemma(
    strictPartialOrder(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Cut(strictPartialOrderIrreflexive, antiReflexiveRelationIsRelation)
  }

  /**
   * Theorem --- The empty relation is a strict partial order on any set
   *
   *   `strictPartialOrder(∅, x)`
   */
  val emptyStrictPartialOrder = Lemma(
    strictPartialOrder(emptySet, x)
  ) {
    have((transitive(emptySet, x)) |- strictPartialOrder(emptySet, x)) by Cut(emptyRelationIrreflexive of (a := x), strictPartialOrderIntro of (r -> emptySet))
    have(thesis) by Cut(emptyRelationTransitive of (a := x), lastStep)
  }

  /**
   * Theorem --- The empty relation is a strict partial order on the empty set
   *
   *   `strictPartialOrder(∅, ∅)`
   */
  val emptySetStrictPartialOrder = Lemma(
    strictPartialOrder(emptySet, emptySet)
  ) {
    have(thesis) by Restate.from(emptyStrictPartialOrder of (x := emptySet))
  }

  /**
   * Theorem --- The restriction of a strict partial order remains a strict partial order
   *
   *   `strictPartialOrder(r, x), y ⊆ x |- strictPartialOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictPartialOrder = Lemma(
    (strictPartialOrder(r, x), subset(y, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)
  ) {
    have((irreflexive(r, x), transitive(relationRestriction(r, y, y), y), subset(y, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionIrreflexive, strictPartialOrderIntro of (r := relationRestriction(r, y, y), x := y))
    have((irreflexive(r, x), transitive(r, x), subset(y, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionTransitive, lastStep)
    have((strictPartialOrder(r, x), transitive(r, x), subset(y, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
      Cut(strictPartialOrderIrreflexive, lastStep)
    have(thesis) by Cut(strictPartialOrderTransitive, lastStep)
  }

  /**
   * Definition --- Least Element of a Set in a Strict Partial Order
   *
   * An element is a least element of a subset of a strict partial order if it is in the subset and is below all other elements
   * that belong to the subset.
   *
   *   `strictPartialOrder(r, x) ∧ y ⊆ x ∧ a ∈ y ∧ (∀ b ∈ y. (a, b) ∈ r ∨ a = b)`
   */
  val isLeastElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ ∀(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))

  /**
   * Theorem --- Least element introduction rule
   *
   *   `strictPartialOrder(r, x), y ⊆ x, a ∈ y, ∀ b ∈ y. (a, b) ∈ r ∨ a = b ⊢ isLeastElement(a, y, r, x)`
   */
  val isLeastElementIntro = Lemma((strictPartialOrder(r, x), subset(y, x), in(a, y), forall(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))) |- isLeastElement(a, y, r, x)) {
    have(thesis) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- Least element elimination rule
   *
   *   `isLeastElement(a, y, r, x), b ∈ y ⊢ (a, b) ∈ r ∨ a = b`
   */
  val isLeastElementElim = Lemma((isLeastElement(a, y, r, x), in(b, y)) |- in(pair(a, b), r) \/ (a === b)) {
    have(isLeastElement(a, y, r, x) |- forall(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))) by Weakening(isLeastElement.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Theorem --- The least element of a subset is in the subset
   *
   *   `isLeastElement(a, y, r, x) ⊢ a ∈ y`
   */
  val isLeastElementInSubset = Lemma(isLeastElement(a, y, r, x) |- in(a, y)) {
    have(isLeastElement(a, y, r, x) |- in(a, y)) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- The least element of a subset is in a subset of the domain
   *
   *   `isLeastElement(a, y, r, x) ⊢ y ⊆ x`
   */
  val isLeastElementInducesSubset = Lemma(isLeastElement(a, y, r, x) |- subset(y, x)) {
    have(isLeastElement(a, y, r, x) |- subset(y, x)) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- The least element of a subset is in the domain of the relation
   *
   *   `isLeastElement(a, y, r, x) ⊢ a ∈ x`
   */
  val isLeastElementInDomain = Lemma(isLeastElement(a, y, r, x) |- in(a, x)) {
    have((isLeastElement(a, y, r, x), subset(y, x)) |- in(a, x)) by Cut(isLeastElementInSubset, subsetElim of (z := a, x := y, y := x))
    have(thesis) by Cut(isLeastElementInducesSubset, lastStep)
  }

  /**
   * Theorem --- The least element of a subset in a strict partial order makes sense in a strict partial order only
   *
   *  `isLeastElement(a, y, r, x) ⊢ strictPartialOrder(r, x)`
   */
  val isLeastElementInStrictPartialOrder = Lemma(isLeastElement(a, y, r, x) |- strictPartialOrder(r, x)) {
    have(isLeastElement(a, y, r, x) |- strictPartialOrder(r, x)) by Weakening(isLeastElement.definition)
  }

  /**
    * Theorem --- An element that is below the least element of a subset is not in the subset
    * 
    *   `isLeastElement(a, y, r, x), (a, b) ∈ r ⊢ b ∉ y`
    */
  val belowLeastElement = Lemma((isLeastElement(a, y, r, x), in(pair(b, a), r)) |- !in(b, y)) {
    sorry
  }

  /**
   * Theorem --- Least elements are preserved under relation restriction
   *
   *   `isLeastElement(a, z, r, x), z ⊆ y ⊆ x |- isLeastElement(a, z, relationRestriction(r, y, y), y)`
   */
  val relationRestrictionLeastElement = Lemma(
    (isLeastElement(a, z, r, x), subset(z, y), subset(y, x)) |- isLeastElement(a, z, relationRestriction(r, y, y), y)
  ) {
    have((in(pair(a, b), r) \/ (a === b), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)) by Tautology.from(relationRestrictionIntro of (x := y))
    have((isLeastElement(a, z, r, x), in(b, z), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)) by Cut(isLeastElementElim of (y := z), lastStep)
    have((isLeastElement(a, z, r, x), subset(z, y), in(a, y), in(b, z)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)) by Cut(subsetElim of (z := b, x := z), lastStep)
    have((isLeastElement(a, z, r, x), subset(z, y), in(a, z), in(b, z)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)) by Cut(subsetElim of (z := a, x := z), lastStep)
    have((isLeastElement(a, z, r, x), subset(z, y), in(b, z)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)) by Cut(isLeastElementInSubset of (y := z), lastStep)
    thenHave((isLeastElement(a, z, r, x), subset(z, y)) |- in(b, z) ==> (in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b))) by RightImplies
    thenHave((isLeastElement(a, z, r, x), subset(z, y)) |- forall(b, in(b, z) ==> (in(pair(a, b), relationRestriction(r, y, y)) \/ (a === b)))) by RightForall
    have((isLeastElement(a, z, r, x), strictPartialOrder(relationRestriction(r, y, y), y), subset(z, y), in(a, z)) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      isLeastElementIntro of (r := relationRestriction(r, y, y), x := y, y := z)
    )
    have((isLeastElement(a, z, r, x), strictPartialOrder(relationRestriction(r, y, y), y), subset(z, y)) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
      isLeastElementInSubset of (y := z),
      lastStep
    )
    have((isLeastElement(a, z, r, x), strictPartialOrder(r, x), subset(y, x), subset(z, y)) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
      relationRestrictionStrictPartialOrder,
      lastStep
    )
    have(thesis) by Cut(isLeastElementInStrictPartialOrder of (y := z), lastStep)
  }

  /**
   * Definition --- Strict Total Order
   *
   * A strict total order is a strict partial order that is connected.
   */
  val strictTotalOrder = DEF(r, x) --> strictPartialOrder(r, x) /\ connected(r, x)

  /**
   * Theorem --- Strict total order introduction rule
   *
   *   `strictPartialOrder(r, x), connected(r, x) ⊢ strictTotalOrder(r, x)`
   */
  val strictTotalOrderIntro = Lemma((strictPartialOrder(r, x), connected(r, x)) |- strictTotalOrder(r, x)) {
    have(thesis) by Weakening(strictTotalOrder.definition)
  }

  /**
   * Theorem --- A strict total order is a strict partial order
   *
   *   `strictTotalOrder(r, x) ⊢ strictPartialOrder(r, x)`
   */
  val strictTotalOrderIsPartial = Lemma(
    strictTotalOrder(r, x) |- strictPartialOrder(r, x)
  ) {
    have(thesis) by Weakening(strictTotalOrder.definition)
  }

  /**
   * Theorem --- A strict total order is irreflexive
   *
   *   `strictTotalOrder(r, x) ⊢ irreflexive(r, x)`
   */
  val strictTotalOrderIrreflexive = Lemma(
    strictTotalOrder(r, x) |- irreflexive(r, x)
  ) {
    have(thesis) by Cut(strictTotalOrderIsPartial, strictPartialOrderIrreflexive)
  }

  /**
   * Theorem --- A strict total order is transitive
   *
   *   `strictTotalOrder(r, x) ⊢ transitive(r, x)`
   */
  val strictTotalOrderTransitive = Lemma(
    strictTotalOrder(r, x) |- transitive(r, x)
  ) {
    have(thesis) by Cut(strictTotalOrderIsPartial, strictPartialOrderTransitive)
  }

  /**
   * Theorem --- A strict total order is connected
   *
   *   `strictTotalOrder(r, x) ⊢ connected(r, x)`
   */
  val strictTotalOrderConnected = Lemma(
    strictTotalOrder(r, x) |- connected(r, x)
  ) {
    have(thesis) by Weakening(strictTotalOrder.definition)
  }

  /**
   * Theorem --- A strict total order is a relation
   *
   *   `strictTotalOrder(r, x) ⊢ relationBetween(r, x, x)`
   */
  val strictTotalOrderIsRelation = Lemma(
    strictTotalOrder(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Cut(strictTotalOrderIsPartial, strictPartialOrderIsRelation)
  }

  /**
   * Theorem --- The empty relation is a strict total order on the empty set
   *
   *   `strictTotalOrder(∅, ∅)`
   */
  val emptySetStrictTotalOrder = Lemma(
    strictTotalOrder(emptySet, emptySet)
  ) {
    have(total(emptySet, emptySet) |- strictTotalOrder(emptySet, emptySet)) by Cut(emptySetStrictPartialOrder, strictTotalOrderIntro of (r -> emptySet, x -> emptySet))
    have(thesis) by Cut(emptyRelationTotalOnItself, lastStep)
  }

  /**
   * Theorem --- The restriction of a strict total order remains a strict total order
   *
   *   `strictTotalOrder(r, x), y ⊆ x |- strictTotalOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictTotalOrder = Lemma(
    (strictTotalOrder(r, x), subset(y, x)) |- strictTotalOrder(relationRestriction(r, y, y), y)
  ) {
    have((strictPartialOrder(r, x), connected(relationRestriction(r, y, y), y), subset(y, x)) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionStrictPartialOrder, strictTotalOrderIntro of (r := relationRestriction(r, y, y), x := y))
    have((strictPartialOrder(r, x), connected(r, x), subset(y, x)) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionConnected, lastStep)
    have((strictTotalOrder(r, x), connected(r, x), subset(y, x)) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
      Cut(strictTotalOrderIsPartial, lastStep)
    have(thesis) by Cut(strictTotalOrderConnected, lastStep)
  }

  /**
   * Definition --- Predecessor
   *
   * An element is predecessor of another element in a strict partial order if the former is below the latter
   * and if there is no element between them.
   *
   *   `strictTotalOrder(r, x) ∧ (a, b) ∈ r ∧ (∀ c. (a, c) ∉ r ∨ (c, b) ∉ r)`
   */
  val isPredecessor = DEF(a, b, r, x) --> strictTotalOrder(r, x) /\ in(pair(a, b), r) /\ forall(c, !in(pair(a, c), r) \/ !in(pair(c, b), r))

  /**
   * Theorem --- Predecessor introduction rule
   *
   *   `strictTotalOrder(r, x), (a, b) ∈ r, (∀ c. (a, c) ∉ r ∨ (c, b) ∉ r) ⊢ isPredecessor(a, b, r, x)`
   */
  val isPredecessorIntro = Lemma((strictTotalOrder(r, x), in(pair(a, b), r), forall(c, !in(pair(a, c), r) \/ !in(pair(c, b), r))) |- isPredecessor(a, b, r, x)) {
    have(thesis) by Weakening(isPredecessor.definition)
  }

  /**
   * Theorem --- Predecessor is below its successor
   *
   *   `isPredecessor(a, b, r, x) ⊢ in(pair(a, b), r)`
   */
  val isPredecessorBelow = Lemma(
    isPredecessor(a, b, r, x) |- in(pair(a, b), r)
  ) {
    have(thesis) by Weakening(isPredecessor.definition)
  }

  /**
   * Theorem --- Predecessor is in a strict total order
   *
   *   `isPredecessor(a, b, r, x) ⊢ strictTotalOrder(r, x)`
   */
  val isPredecessorInStrictTotalOrder = Lemma(
    isPredecessor(a, b, r, x) |- strictTotalOrder(r, x)
  ) {
    have(thesis) by Weakening(isPredecessor.definition)
  }

  /**
   * Definition --- Limit Element
   *
   * An element is a limit element in a strict total order if it is has no predecessor.
   *
   *    `strictTotalOrder(r, x) ∧ a ∈ x ∧ ¬∃ b. isPredecessor(b, a, r, x)`
   */
  val isLimitElement = DEF(a, r, x) --> strictTotalOrder(r, x) /\ in(a, x) /\ !exists(b, isPredecessor(b, a, r, x))

  /**
   * Definition --- Successor Element
   *
   * An element is a successor element in a strict total order if it has a predecessor.
   *
   *   `∃ b. isPredecessor(b, a, r, x)`
   */
  val isSuccessorElement = DEF(a, r, x) --> exists(b, isPredecessor(b, a, r, x))

  /**
   * Theorem --- Limit element introduction rule
   *
   *   `strictTotalOrder(r, x), a ∈ x, ∀ b. ¬isPredecessor(b, a, r, x) ⊢ isLimitElement(a, r, x)`
   */
  val isLimitElementIntro = Lemma((strictTotalOrder(r, x), in(a, x), forall(b, !isPredecessor(b, a, r, x))) |- isLimitElement(a, r, x)) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Limit element elimination rule
   *
   *   `isLimitElement(a, r, x) ⊢ ¬isPredecessor(b, a, r, x)`
   */
  val isLimitElementElim = Lemma(isLimitElement(a, r, x) |- !isPredecessor(b, a, r, x)) {
    have(isLimitElement(a, r, x) |- forall(b, !isPredecessor(b, a, r, x))) by Weakening(isLimitElement.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Theorem --- Limit elements belong to strict total orders
   *
   *   `isLimitElement(a, r, x) ⊢ strictTotalOrder(r, x)`
   */
  val isLimitElementStrictTotalOrder = Lemma(isLimitElement(a, r, x) |- strictTotalOrder(r, x)) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Limit elements are defined within strict total orders
   *
   *   `isLimitElement(a, r, x) ⊢ strictTotalOrder(r, x) `
   */
  val isLimitElementImpliesStrictTotalOrder = Lemma(isLimitElement(a, r, x) |- strictTotalOrder(r, x)) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Limit elements are in the domain of strict total orders
   *
   *   `isLimitElement(a, r, x) ⊢ a ∈ x`
   */
  val isLimitElementImpliesInDomain = Lemma(isLimitElement(a, r, x) |- in(a, x)) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Successor element introduction rule
   *
   *   `isPredecessor(b, a, r, x) ⊢ isSuccessorElement(a, r, x)`
   */
  val isSuccessorElementIntro = Lemma(isPredecessor(b, a, r, x) |- isSuccessorElement(a, r, x)) {
    have(isPredecessor(b, a, r, x) |- isPredecessor(b, a, r, x)) by Hypothesis
    thenHave(isPredecessor(b, a, r, x) |- exists(b, isPredecessor(b, a, r, x))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(isSuccessorElement.definition)
  }

  val isSuccessorElementElim = Lemma(isLimitElement(a, r, x) |- !isPredecessor(b, a, r, x)) {
    have(isLimitElement(a, r, x) |- forall(b, !isPredecessor(b, a, r, x))) by Weakening(isLimitElement.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Theorem --- Elements of strict total orders are either limit or successors
   *
   *   `strictTotalOrder(r, x), a ∈ x ⊢ isLimitElement(a, r, x) ∨ isSuccessorElement(a, r, x)`
   */
  val everyElemInStrictTotalOrderLimitOrSuccessor = Lemma(
    (strictTotalOrder(r, x), in(a, x)) |- isLimitElement(a, r, x) \/ isSuccessorElement(a, r, x)
  ) {
    have((strictTotalOrder(r, x), in(a, x)) |- (strictTotalOrder(r, x) /\ in(a, x) /\ !exists(b, isPredecessor(b, a, r, x))) \/ exists(b, isPredecessor(b, a, r, x))) by Restate
    thenHave((strictTotalOrder(r, x), in(a, x)) |- isLimitElement(a, r, x) \/ exists(b, isPredecessor(b, a, r, x))) by Substitution.ApplyRules(isLimitElement.definition)
    thenHave(thesis) by Substitution.ApplyRules(isSuccessorElement.definition)
  }

  /**
   * Theorem --- There is always an element between a limit element and any other element
   *
   *   `isLimitElement(a, r, x), (c, a) ∈ r ⊢ ∃ b. (c, b) ∈ r ∧ (b, a) ∈ r`
   */
  val belowLimitElement = Lemma(
    (isLimitElement(a, r, x), in(pair(c, a), r)) |- exists(b, in(pair(c, b), r) /\ in(pair(b, a), r))
  ) {
    have((isLimitElement(a, r, x), in(pair(c, a), r), forall(b, !in(pair(c, b), r) \/ !in(pair(b, a), r))) |- isPredecessor(c, a, r, x)) by Cut(
      isLimitElementStrictTotalOrder,
      isPredecessorIntro of (a -> c, b -> a)
    )
    have((isLimitElement(a, r, x), in(pair(c, a), r), forall(b, !in(pair(c, b), r) \/ !in(pair(b, a), r))) |- isPredecessor(c, a, r, x) /\ !isPredecessor(c, a, r, x)) by RightAnd(
      lastStep,
      isLimitElementElim of (b -> c)
    )
  }

  /**
   * Definition --- Strict Well-Order
   *
   * A strict well-order is a strict total order where every non-empty subset has a least element.
   *
   *   `strictTotalOrder(r, x) ∧ ∀ ∅ ≠ y ⊆ x. ∃ a. isLeastElement(a, y, r, x)`
   */
  val strictWellOrder = DEF(r, x) -->
    strictTotalOrder(r, x) /\ forall(y, (subset(y, x) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, r, x)))

  /**
   * Theorem --- Strict well-order introduction rule
   *
   *  `strictTotalOrder(r, x), ∀ ∅ ≠ y ⊆ x. ∃ a. isLeastElement(a, y, r, x) ⊢ strictWellOrder(r, x)`
   */
  val strictWellOrderIntro = Lemma(
    (strictTotalOrder(r, x), forall(y, (subset(y, x) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, r, x)))) |- strictWellOrder(r, x)
  ) {
    have(thesis) by Weakening(strictWellOrder.definition)
  }

  /**
   * Theorem --- Strict well-order elimination rule
   *
   *   `strictWellOrder(r, x), y ⊆ x, y ≠ ∅ ⊢ ∃ a. isLeastElement(a, y, r, x)`
   */
  val strictWellOrderElim = Lemma(
    (strictWellOrder(r, x), subset(y, x), !(y === emptySet)) |- exists(a, isLeastElement(a, y, r, x))
  ) {
    have(strictWellOrder(r, x) |- forall(y, (subset(y, x) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, r, x)))) by Weakening(strictWellOrder.definition)
    thenHave(thesis) by InstantiateForall(y)
  }

  /**
   * Theorem --- A strict well-order is a strict total order
   *
   *   `strictWellOrder(r, x) ⊢ strictTotalOrder(r, x)`
   */
  val strictWellOrderTotal = Lemma(
    strictWellOrder(r, x) |- strictTotalOrder(r, x)
  ) {
    have(thesis) by Weakening(strictWellOrder.definition)
  }

  /**
   * Theorem --- A strict well-order is irreflexive
   *
   *   `strictWellOrder(r, x) ⊢ irreflexive(r, x)`
   */

  val strictWellOrderIrreflexive = Lemma(
    strictWellOrder(r, x) |- irreflexive(r, x)
  ) {
    have(thesis) by Cut(strictWellOrderTotal, strictTotalOrderIrreflexive)
  }

  /**
   * Theorem --- A strict well-order is transitive
   *
   *  `strictWellOrder(r, x) ⊢ transitive(r, x)`
   */
  val strictWellOrderTransitive = Lemma(
    strictWellOrder(r, x) |- transitive(r, x)
  ) {
    have(thesis) by Cut(strictWellOrderTotal, strictTotalOrderTransitive)
  }

  /**
   * Theorem --- A strict well-order is connected
   *
   *   `strictWellOrder(r, x) ⊢ connected(r, x)`
   */
  val strictWellOrderConnected = Lemma(
    strictWellOrder(r, x) |- connected(r, x)
  ) {
    have(thesis) by Cut(strictWellOrderTotal, strictTotalOrderConnected)
  }

  /**
   * Theorem --- A strict well-order is a relation
   *
   *   `strictWellOrder(r, x) ⊢ relationBetween(r, x, x)`
   */
  val strictWellOrderIsRelation = Lemma(
    strictWellOrder(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Cut(strictWellOrderTotal, strictTotalOrderIsRelation)
  }

  /**
   * Theorem --- the empty set is well ordered by the empty relation.
   */
  val emptyStrictWellOrder = Lemma(
    strictWellOrder(emptySet, emptySet)
  ) {
    have((subset(y, emptySet) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, emptySet, emptySet))) by Weakening(emptySetIsItsOwnOnlySubset of (x := y))
    thenHave(forall(y, (subset(y, emptySet) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, emptySet, emptySet)))) by RightForall
    have(strictTotalOrder(emptySet, emptySet) |- strictWellOrder(emptySet, emptySet)) by Cut(lastStep, strictWellOrderIntro of (r -> emptySet, x -> emptySet))
    have(thesis) by Cut(emptySetStrictTotalOrder, lastStep)
  }

  /**
   * Theorem --- Strict well orders are preserved under relation restriction
   *
   *   `strictWellOrder(r, x), y ⊆ x |- strictWellOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictWellOrder = Lemma(
    (strictWellOrder(r, x), subset(y, x)) |- strictWellOrder(relationRestriction(r, y, y), y)
  ) {
    have((isLeastElement(a, z, r, x), subset(z, y), subset(y, x)) |- exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by RightExists(relationRestrictionLeastElement)
    thenHave((exists(a, isLeastElement(a, z, r, x)), subset(z, y), subset(y, x)) |- exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by LeftExists
    have((strictWellOrder(r, x), subset(z, x), !(z === emptySet), subset(z, y), subset(y, x)) |- exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by Cut(
      strictWellOrderElim of (y := z),
      lastStep
    )
    have((strictWellOrder(r, x), !(z === emptySet), subset(z, y), subset(y, x)) |- exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by Cut(
      subsetTransitivity of (x := z, z := x),
      lastStep
    )
    thenHave((strictWellOrder(r, x), subset(z, y) /\ !(z === emptySet), subset(y, x)) |- exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by LeftAnd
    thenHave((strictWellOrder(r, x), subset(y, x)) |- (subset(z, y) /\ !(z === emptySet)) ==> exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by RightImplies
    thenHave((strictWellOrder(r, x), subset(y, x)) |- forall(z, (subset(z, y) /\ !(z === emptySet)) ==> exists(a, isLeastElement(a, z, relationRestriction(r, y, y), y)))) by RightForall
    have((strictWellOrder(r, x), subset(y, x), strictTotalOrder(relationRestriction(r, y, y), y)) |- strictWellOrder(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      strictWellOrderIntro of (r := relationRestriction(r, y, y), x := y)
    )
    have((strictWellOrder(r, x), subset(y, x), strictTotalOrder(r, x)) |- strictWellOrder(relationRestriction(r, y, y), y)) by Cut(relationRestrictionStrictTotalOrder, lastStep)
    have(thesis) by Cut(strictWellOrderTotal, lastStep)
  }

  // /**
  //  * Properties of functions under partial orders
  //  */

  val relationIsomorphism = DEF(f, r1, x, r2, y) --> bijective(f, x, y) /\ relationBetween(r1, x, x) /\ relationBetween(r2, y, y) /\
    forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2))))

  val relationIsomorphismIntro = Lemma(
    (
      bijective(f, x, y),
      relationBetween(r1, x, x),
      relationBetween(r2, y, y),
      forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2))))
    ) |- relationIsomorphism(f, r1, x, r2, y)
  ) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsomorphismBijective = Lemma(relationIsomorphism(f, r1, x, r2, y) |- bijective(f, x, y)) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsmorphismDomainIsRelation = Lemma(relationIsomorphism(f, r1, x, r2, y) |- relationBetween(r1, x, x)) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsomorphismElim = Lemma((relationIsomorphism(f, r1, x, r2, y), in(a, x), in(b, x)) |- in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2)) {
    have(relationIsomorphism(f, r1, x, r2, y) |- forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2))))) by Weakening(
      relationIsomorphism.definition
    )
    thenHave(relationIsomorphism(f, r1, x, r2, y) |- forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2)))) by InstantiateForall(a)
    thenHave(thesis) by InstantiateForall(b)
  }

  val relationIsomorphismElimForward = Lemma((relationIsomorphism(f, r1, x, r2, y), in(pair(a, b), r1)) |- in(pair(app(f, a), app(f, b)), r2)) {
    have((relationIsomorphism(f, r1, x, r2, y), in(a, x), in(b, x), in(pair(a, b), r1)) |- in(pair(app(f, a), app(f, b)), r2)) by Weakening(relationIsomorphismElim)
    thenHave((relationIsomorphism(f, r1, x, r2, y), in(a, x) /\ in(b, x), in(pair(a, b), r1)) |- in(pair(app(f, a), app(f, b)), r2)) by LeftAnd
    have((relationIsomorphism(f, r1, x, r2, y), relationBetween(r1, x, x), in(pair(a, b), r1)) |- in(pair(app(f, a), app(f, b)), r2)) by Cut(
      relationBetweenElimPair of (r := r1, x := a, y := b, a := x, b := x),
      lastStep
    )
    have(thesis) by Cut(relationIsmorphismDomainIsRelation, lastStep)
  }

  val relationIsomorphismElimBackward = Lemma((relationIsomorphism(f, r1, x, r2, y), in(a, x), in(b, x), in(pair(app(f, a), app(f, b)), r2)) |- in(pair(a, b), r1)) {
    have(thesis) by Weakening(relationIsomorphismElim)
  }

  val strictWellOrderIsomorphismIntro = Lemma(
    (
      bijective(f, x, y),
      strictWellOrder(r1, x),
      strictWellOrder(r2, y),
      forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2))))
    ) |- relationIsomorphism(f, r1, x, r2, y)
  ) {
    have(
      (
        bijective(f, x, y),
        strictWellOrder(r1, x),
        relationBetween(r2, y, y),
        forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), r1) <=> in(pair(app(f, a), app(f, b)), r2))))
      ) |- relationIsomorphism(f, r1, x, r2, y)
    ) by Cut(strictWellOrderIsRelation of (r := r1), relationIsomorphismIntro)
    have(thesis) by Cut(strictWellOrderIsRelation of (r := r2, x := y), lastStep)
  }

  val relationIsomorphismAppInCodomain = Lemma(
    (relationIsomorphism(f, r1, x, r2, y), in(a, x)) |- in(app(f, a), y)
  ) {
    have(relationIsomorphism(f, r1, x, r2, y) |- functionFrom(f, x, y)) by Cut(relationIsomorphismBijective, bijectiveIsFunction)
    have(thesis) by Cut(lastStep, functionFromAppInCodomain)
  }

  // val inverseRelationIsomorphismIsIsomorphism = Lemma(
    
  // ) {
  //   have((in(a, y), in(b, y)) |- (in(pair(a, b), r2) <=> in(pair(app(inverseRelation(f), a), app(inverseRelation(f), b)), r1)))
  // }
}
