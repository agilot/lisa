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
  private val r3 = variable
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
   * Theorem --- A strict partial order is asymmetric
   * 
   *  `strictPartialOrder(r, x) ⊢ asymmetric(r, x)`
   */
  val strictPartialOrderAsymmetric = Lemma(
    strictPartialOrder(r, x) |- asymmetric(r, x)
  ) {
    have((strictPartialOrder(r, x), transitive(r, x)) |- asymmetric(r, x)) by Cut(strictPartialOrderIrreflexive, antiReflexiveTransitiveIsAsymmetric)
    have(thesis) by Cut(strictPartialOrderTransitive, lastStep)
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
    strictPartialOrder(∅, x)
  ) {
    have((transitive(∅, x)) |- strictPartialOrder(∅, x)) by Cut(emptyRelationIrreflexive of (a := x), strictPartialOrderIntro of (r := ∅))
    have(thesis) by Cut(emptyRelationTransitive of (a := x), lastStep)
  }

  /**
   * Theorem --- The empty relation is a strict partial order on the empty set
   *
   *   `strictPartialOrder(∅, ∅)`
   */
  val emptySetStrictPartialOrder = Lemma(
    strictPartialOrder(∅, ∅)
  ) {
    have(thesis) by Restate.from(emptyStrictPartialOrder of (x := ∅))
  }

  /**
   * Theorem --- The restriction of a strict partial order remains a strict partial order
   *
   *   `strictPartialOrder(r, x) |- strictPartialOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictPartialOrder = Lemma(
    strictPartialOrder(r, x) |- strictPartialOrder(relationRestriction(r, y, y), y)
  ) {
    have((irreflexive(r, x), transitive(relationRestriction(r, y, y), y)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionIrreflexive, strictPartialOrderIntro of (r := relationRestriction(r, y, y), x := y))
    have((irreflexive(r, x), transitive(r, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionTransitive, lastStep)
    have((strictPartialOrder(r, x), transitive(r, x)) |- strictPartialOrder(relationRestriction(r, y, y), y)) by
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
  val isLeastElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ y ⊆ x /\ a ∈ y /\ ∀(b, b ∈ y ==> (pair(a, b) ∈ r \/ (a === b)))

  /**
   * Theorem --- Least element introduction rule
   *
   *   `strictPartialOrder(r, x), y ⊆ x, a ∈ y, ∀ b ∈ y. (a, b) ∈ r ∨ a = b ⊢ isLeastElement(a, y, r, x)`
   */
  val isLeastElementIntro = Lemma((strictPartialOrder(r, x), y ⊆ x, a ∈ y, ∀(b, b ∈ y ==> (pair(a, b) ∈ r \/ (a === b)))) |- isLeastElement(a, y, r, x)) {
    have(thesis) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- Least element elimination rule
   *
   *   `isLeastElement(a, y, r, x), b ∈ y ⊢ (a, b) ∈ r ∨ a = b`
   */
  val isLeastElementElim = Lemma((isLeastElement(a, y, r, x), b ∈ y) |- pair(a, b) ∈ r \/ (a === b)) {
    have(isLeastElement(a, y, r, x) |- ∀(b, b ∈ y ==> (pair(a, b) ∈ r \/ (a === b)))) by Weakening(isLeastElement.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Theorem --- The least element of a subset is in the subset
   *
   *   `isLeastElement(a, y, r, x) ⊢ a ∈ y`
   */
  val isLeastElementInSubset = Lemma(isLeastElement(a, y, r, x) |- a ∈ y) {
    have(isLeastElement(a, y, r, x) |- a ∈ y) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- The least element of a subset is in a subset of the domain
   *
   *   `isLeastElement(a, y, r, x) ⊢ y ⊆ x`
   */
  val isLeastElementInducesSubset = Lemma(isLeastElement(a, y, r, x) |- y ⊆ x) {
    have(isLeastElement(a, y, r, x) |- y ⊆ x) by Weakening(isLeastElement.definition)
  }

  /**
   * Theorem --- The least element of a subset is in the domain of the relation
   *
   *   `isLeastElement(a, y, r, x) ⊢ a ∈ x`
   */
  val isLeastElementInDomain = Lemma(isLeastElement(a, y, r, x) |- a ∈ x) {
    have((isLeastElement(a, y, r, x), y ⊆ x) |- a ∈ x) by Cut(isLeastElementInSubset, subsetElim of (z := a, x := y, y := x))
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
  val belowLeastElement = Lemma((isLeastElement(a, y, r, x), pair(b, a) ∈ r) |- b ∉ y) {
    val left = have((strictPartialOrder(r, x), pair(b, a) ∈ r) |- a =/= b) by Cut(strictPartialOrderIrreflexive, pairInAntiReflexiveRelation of (a := b, b := a))
    val right = have((strictPartialOrder(r, x), pair(b, a) ∈ r) |- pair(a, b) ∉ r) by Cut(strictPartialOrderAsymmetric, asymmetricElim of (y := b, z := a))

    have((strictPartialOrder(r, x), pair(b, a) ∈ r) |- !(pair(a, b) ∈ r \/ (a === b))) by RightAnd(left, right)
    have((isLeastElement(a, y, r, x), strictPartialOrder(r, x), pair(b, a) ∈ r, b ∈ y) |- ()) by RightAnd(lastStep, isLeastElementElim)
    have((isLeastElement(a, y, r, x), pair(b, a) ∈ r, b ∈ y) |- ()) by Cut(isLeastElementInStrictPartialOrder, lastStep)
  }

  /**
   * Theorem --- Least elements are preserved under relation restriction
   *
   *   `isLeastElement(a, z, r, x), z ⊆ y |- isLeastElement(a, z, relationRestriction(r, y, y), y)`
   */
  val relationRestrictionLeastElement = Lemma(
    (isLeastElement(a, z, r, x), z ⊆ y) |- isLeastElement(a, z, relationRestriction(r, y, y), y)
  ) {
    have((pair(a, b) ∈ r \/ (a === b), a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)) by Tautology.from(relationRestrictionIntroPair of (x := y))
    have((isLeastElement(a, z, r, x), b ∈ z, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)) by Cut(isLeastElementElim of (y := z), lastStep)
    have((isLeastElement(a, z, r, x), z ⊆ y, a ∈ y, b ∈ z) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)) by Cut(subsetElim of (z := b, x := z), lastStep)
    have((isLeastElement(a, z, r, x), z ⊆ y, a ∈ z, b ∈ z) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)) by Cut(subsetElim of (z := a, x := z), lastStep)
    have((isLeastElement(a, z, r, x), z ⊆ y, b ∈ z) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)) by Cut(isLeastElementInSubset of (y := z), lastStep)
    thenHave((isLeastElement(a, z, r, x), z ⊆ y) |- b ∈ z ==> (pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b))) by RightImplies
    thenHave((isLeastElement(a, z, r, x), z ⊆ y) |- ∀(b, b ∈ z ==> (pair(a, b) ∈ relationRestriction(r, y, y) \/ (a === b)))) by RightForall
    have((isLeastElement(a, z, r, x), strictPartialOrder(relationRestriction(r, y, y), y), z ⊆ y, a ∈ z) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      isLeastElementIntro of (r := relationRestriction(r, y, y), x := y, y := z)
    )
    have((isLeastElement(a, z, r, x), strictPartialOrder(relationRestriction(r, y, y), y), z ⊆ y) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
      isLeastElementInSubset of (y := z),
      lastStep
    )
    have((isLeastElement(a, z, r, x), strictPartialOrder(r, x), z ⊆ y) |- isLeastElement(a, z, relationRestriction(r, y, y), y)) by Cut(
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
    strictTotalOrder(∅, ∅)
  ) {
    have(total(∅, ∅) |- strictTotalOrder(∅, ∅)) by Cut(emptySetStrictPartialOrder, strictTotalOrderIntro of (r := ∅, x := ∅))
    have(thesis) by Cut(emptyRelationTotalOnItself, lastStep)
  }

  /**
   * Theorem --- The restriction of a strict total order remains a strict total order
   *
   *   `strictTotalOrder(r, x), y ⊆ x |- strictTotalOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictTotalOrder = Lemma(
    (strictTotalOrder(r, x), y ⊆ x) |- strictTotalOrder(relationRestriction(r, y, y), y)
  ) {
    have((strictPartialOrder(r, x), connected(relationRestriction(r, y, y), y)) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionStrictPartialOrder, strictTotalOrderIntro of (r := relationRestriction(r, y, y), x := y))
    have((strictPartialOrder(r, x), connected(r, x), y ⊆ x) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
      Cut(relationRestrictionConnected, lastStep)
    have((strictTotalOrder(r, x), connected(r, x), y ⊆ x) |- strictTotalOrder(relationRestriction(r, y, y), y)) by
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
  val isPredecessor = DEF(a, b, r, x) --> strictTotalOrder(r, x) /\ pair(a, b) ∈ r /\ ∀(c, pair(a, c) ∉ r \/ (pair(c, b) ∉ r))

  /**
   * Theorem --- Predecessor introduction rule
   *
   *   `strictTotalOrder(r, x), (a, b) ∈ r, (∀ c. (a, c) ∉ r ∨ (c, b) ∉ r) ⊢ isPredecessor(a, b, r, x)`
   */
  val isPredecessorIntro = Lemma((strictTotalOrder(r, x), pair(a, b) ∈ r, ∀(c, pair(a, c) ∉ r \/ (pair(c, b) ∉ r))) |- isPredecessor(a, b, r, x)) {
    have(thesis) by Weakening(isPredecessor.definition)
  }

  /**
   * Theorem --- Predecessor is below its successor
   *
   *   `isPredecessor(a, b, r, x) ⊢ pair(a, b) ∈ r`
   */
  val isPredecessorBelow = Lemma(
    isPredecessor(a, b, r, x) |- pair(a, b) ∈ r
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
  val isLimitElement = DEF(a, r, x) --> strictTotalOrder(r, x) /\ a ∈ x /\ !(∃(b, isPredecessor(b, a, r, x)))

  /**
   * Definition --- Successor Element
   *
   * An element is a successor element in a strict total order if it has a predecessor.
   *
   *   `∃ b. isPredecessor(b, a, r, x)`
   */
  val isSuccessorElement = DEF(a, r, x) --> ∃(b, isPredecessor(b, a, r, x))

  /**
   * Theorem --- Limit element introduction rule
   *
   *   `strictTotalOrder(r, x), a ∈ x, ∀ b. ¬isPredecessor(b, a, r, x) ⊢ isLimitElement(a, r, x)`
   */
  val isLimitElementIntro = Lemma((strictTotalOrder(r, x), a ∈ x, ∀(b, !isPredecessor(b, a, r, x))) |- isLimitElement(a, r, x)) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Limit element elimination rule
   *
   *   `isLimitElement(a, r, x) ⊢ ¬isPredecessor(b, a, r, x)`
   */
  val isLimitElementElim = Lemma(isLimitElement(a, r, x) |- !isPredecessor(b, a, r, x)) {
    have(isLimitElement(a, r, x) |- ∀(b, !isPredecessor(b, a, r, x))) by Weakening(isLimitElement.definition)
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
  val isLimitElementImpliesInDomain = Lemma(isLimitElement(a, r, x) |- a ∈ x) {
    have(thesis) by Weakening(isLimitElement.definition)
  }

  /**
   * Theorem --- Successor element introduction rule
   *
   *   `isPredecessor(b, a, r, x) ⊢ isSuccessorElement(a, r, x)`
   */
  val isSuccessorElementIntro = Lemma(isPredecessor(b, a, r, x) |- isSuccessorElement(a, r, x)) {
    have(isPredecessor(b, a, r, x) |- isPredecessor(b, a, r, x)) by Hypothesis
    thenHave(isPredecessor(b, a, r, x) |- ∃(b, isPredecessor(b, a, r, x))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(isSuccessorElement.definition)
  }

  val isSuccessorElementElim = Lemma(isLimitElement(a, r, x) |- !isPredecessor(b, a, r, x)) {
    have(isLimitElement(a, r, x) |- ∀(b, !isPredecessor(b, a, r, x))) by Weakening(isLimitElement.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Theorem --- Elements of strict total orders are either limit or successors
   *
   *   `strictTotalOrder(r, x), a ∈ x ⊢ isLimitElement(a, r, x) ∨ isSuccessorElement(a, r, x)`
   */
  val everyElemInStrictTotalOrderLimitOrSuccessor = Lemma(
    (strictTotalOrder(r, x), a ∈ x) |- isLimitElement(a, r, x) \/ isSuccessorElement(a, r, x)
  ) {
    have((strictTotalOrder(r, x), a ∈ x) |- (strictTotalOrder(r, x) /\ a ∈ x /\ !(∃(b, isPredecessor(b, a, r, x)))) \/ ∃(b, isPredecessor(b, a, r, x))) by Restate
    thenHave((strictTotalOrder(r, x), a ∈ x) |- isLimitElement(a, r, x) \/ ∃(b, isPredecessor(b, a, r, x))) by Substitution.ApplyRules(isLimitElement.definition)
    thenHave(thesis) by Substitution.ApplyRules(isSuccessorElement.definition)
  }

  /**
   * Theorem --- There is always an element between a limit element and any other element
   *
   *   `isLimitElement(a, r, x), (c, a) ∈ r ⊢ ∃ b. (c, b) ∈ r ∧ (b, a) ∈ r`
   */
  val belowLimitElement = Lemma(
    (isLimitElement(a, r, x), pair(c, a) ∈ r) |- ∃(b, pair(c, b) ∈ r /\ pair(b, a) ∈ r)
  ) {
    have((isLimitElement(a, r, x), pair(c, a) ∈ r, ∀(b, pair(c, b) ∉ r \/ (pair(b, a) ∉ r))) |- isPredecessor(c, a, r, x)) by Cut(
      isLimitElementStrictTotalOrder,
      isPredecessorIntro of (a := c, b := a)
    )
    have((isLimitElement(a, r, x), pair(c, a) ∈ r, ∀(b, pair(c, b) ∉ r \/ (pair(b, a) ∉ r))) |- ()) by RightAnd(
      lastStep,
      isLimitElementElim of (b := c)
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
    strictTotalOrder(r, x) /\ ∀(y, (y ⊆ x /\ (y =/= ∅)) ==> ∃(a, isLeastElement(a, y, r, x)))

  /**
   * Theorem --- Strict well-order introduction rule
   *
   *  `strictTotalOrder(r, x), ∀ ∅ ≠ y ⊆ x. ∃ a. isLeastElement(a, y, r, x) ⊢ strictWellOrder(r, x)`
   */
  val strictWellOrderIntro = Lemma(
    (strictTotalOrder(r, x), ∀(y, (y ⊆ x /\ (y =/= ∅)) ==> ∃(a, isLeastElement(a, y, r, x)))) |- strictWellOrder(r, x)
  ) {
    have(thesis) by Weakening(strictWellOrder.definition)
  }

  /**
   * Theorem --- Strict well-order elimination rule
   *
   *   `strictWellOrder(r, x), y ⊆ x, y ≠ ∅ ⊢ ∃ a. isLeastElement(a, y, r, x)`
   */
  val strictWellOrderElim = Lemma(
    (strictWellOrder(r, x), y ⊆ x, y =/= ∅) |- ∃(a, isLeastElement(a, y, r, x))
  ) {
    have(strictWellOrder(r, x) |- ∀(y, (y ⊆ x /\ (y =/= ∅)) ==> ∃(a, isLeastElement(a, y, r, x)))) by Weakening(strictWellOrder.definition)
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
  val strictWellOrderIsRelationBetween = Lemma(
    strictWellOrder(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Cut(strictWellOrderTotal, strictTotalOrderIsRelation)
  }

  val strictWellOrderIsRelation = Lemma(
    strictWellOrder(r, x) |- relation(r)
  ) {
    have(thesis) by Cut(strictWellOrderIsRelationBetween, relationBetweenIsRelation of (a := x, b := x))
  }

  /**
   * Theorem --- the empty set is well ordered by the empty relation.
   */
  val emptyStrictWellOrder = Lemma(
    strictWellOrder(∅, ∅)
  ) {
    have((y ⊆ ∅ /\ (y =/= ∅)) ==> ∃(a, isLeastElement(a, y, ∅, ∅))) by Weakening(subsetEmptySet of (x := y))
    thenHave(∀(y, (y ⊆ ∅ /\ (y =/= ∅)) ==> ∃(a, isLeastElement(a, y, ∅, ∅)))) by RightForall
    have(strictTotalOrder(∅, ∅) |- strictWellOrder(∅, ∅)) by Cut(lastStep, strictWellOrderIntro of (r := ∅, x := ∅))
    have(thesis) by Cut(emptySetStrictTotalOrder, lastStep)
  }

  /**
   * Theorem --- Strict well orders are preserved under relation restriction
   *
   *   `strictWellOrder(r, x), y ⊆ x |- strictWellOrder(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionStrictWellOrder = Lemma(
    (strictWellOrder(r, x), y ⊆ x) |- strictWellOrder(relationRestriction(r, y, y), y)
  ) {
    have((isLeastElement(a, z, r, x), z ⊆ y) |- ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by RightExists(relationRestrictionLeastElement)
    thenHave((∃(a, isLeastElement(a, z, r, x)), z ⊆ y) |- ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by LeftExists
    have((strictWellOrder(r, x), z ⊆ x, z =/= ∅, z ⊆ y) |- ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by Cut(
      strictWellOrderElim of (y := z),
      lastStep
    )
    have((strictWellOrder(r, x), z =/= ∅, z ⊆ y, y ⊆ x) |- ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by Cut(
      subsetTransitivity of (x := z, z := x),
      lastStep
    )
    thenHave((strictWellOrder(r, x), z ⊆ y /\ (z =/= ∅), y ⊆ x) |- ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by LeftAnd
    thenHave((strictWellOrder(r, x), y ⊆ x) |- (z ⊆ y /\ (z =/= ∅)) ==> ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y))) by RightImplies
    thenHave((strictWellOrder(r, x), y ⊆ x) |- ∀(z, (z ⊆ y /\ (z =/= ∅)) ==> ∃(a, isLeastElement(a, z, relationRestriction(r, y, y), y)))) by RightForall
    have((strictWellOrder(r, x), y ⊆ x, strictTotalOrder(relationRestriction(r, y, y), y)) |- strictWellOrder(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      strictWellOrderIntro of (r := relationRestriction(r, y, y), x := y)
    )
    have((strictWellOrder(r, x), y ⊆ x, strictTotalOrder(r, x)) |- strictWellOrder(relationRestriction(r, y, y), y)) by Cut(relationRestrictionStrictTotalOrder, lastStep)
    have(thesis) by Cut(strictWellOrderTotal, lastStep)
  }


  val relationIsomorphism = DEF(f, r1, x, r2, y) --> bijective(f, x, y) /\ relationBetween(r1, x, x) /\ relationBetween(r2, y, y) /\
    ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2)))

  val relationIsomorphismIntro = Lemma(
    (
      bijective(f, x, y),
      relationBetween(r1, x, x),
      relationBetween(r2, y, y),
      ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2)))
    ) |- relationIsomorphism(f, r1, x, r2, y)
  ) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsomorphismBijective = Lemma(relationIsomorphism(f, r1, x, r2, y) |- bijective(f, x, y)) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsomorphismFunctionFrom = Lemma(relationIsomorphism(f, r1, x, r2, y) |- functionFrom(f, x, y)) {
    have(thesis) by Cut(relationIsomorphismBijective, bijectiveIsFunctionFrom)
  }

  val relationIsomorphismDomainIsRelation = Lemma(relationIsomorphism(f, r1, x, r2, y) |- relationBetween(r1, x, x)) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

    val relationIsomorphismRangeIsRelation = Lemma(relationIsomorphism(f, r1, x, r2, y) |- relationBetween(r2, y, y)) {
    have(thesis) by Weakening(relationIsomorphism.definition)
  }

  val relationIsomorphismElim = Lemma((relationIsomorphism(f, r1, x, r2, y), a ∈ x, b ∈ x) |- pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2) {
    have(relationIsomorphism(f, r1, x, r2, y) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2)))) by Weakening(
      relationIsomorphism.definition
    )
    thenHave(relationIsomorphism(f, r1, x, r2, y) |- ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2))) by InstantiateForall(a)
    thenHave(thesis) by InstantiateForall(b)
  }

  val relationIsomorphismElimForward = Lemma((relationIsomorphism(f, r1, x, r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) {
    have((relationIsomorphism(f, r1, x, r2, y), a ∈ x, b ∈ x, pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by Weakening(relationIsomorphismElim)
    thenHave((relationIsomorphism(f, r1, x, r2, y), a ∈ x /\ b ∈ x, pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by LeftAnd
    have((relationIsomorphism(f, r1, x, r2, y), relationBetween(r1, x, x), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by Cut(
      relationBetweenElimPair of (r := r1, x := a, y := b, a := x, b := x),
      lastStep
    )
    have(thesis) by Cut(relationIsomorphismDomainIsRelation, lastStep)
  }

  val relationIsomorphismElimBackward = Lemma((relationIsomorphism(f, r1, x, r2, y), a ∈ x, b ∈ x, pair(app(f, a), app(f, b)) ∈ r2) |- pair(a, b) ∈ r1) {
    have(thesis) by Weakening(relationIsomorphismElim)
  }

  val strictWellOrderIsomorphismIntro = Lemma(
    (
      bijective(f, x, y),
      strictWellOrder(r1, x),
      strictWellOrder(r2, y),
      ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2)))
    ) |- relationIsomorphism(f, r1, x, r2, y)
  ) {
    have(
      (
        bijective(f, x, y),
        strictWellOrder(r1, x),
        relationBetween(r2, y, y),
        ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ r1 <=> pair(app(f, a), app(f, b)) ∈ r2)))
      ) |- relationIsomorphism(f, r1, x, r2, y)
    ) by Cut(strictWellOrderIsRelationBetween of (r := r1), relationIsomorphismIntro)
    have(thesis) by Cut(strictWellOrderIsRelationBetween of (r := r2, x := y), lastStep)
  }

  val relationIsomorphismAppInCodomain = Lemma(
    (relationIsomorphism(f, r1, x, r2, y), a ∈ x) |- app(f, a) ∈ y
  ) {
    have(thesis) by Cut(relationIsomorphismFunctionFrom, functionFromAppInCodomain)
  }

  val inverseRelationIsomorphism = Lemma(
    relationIsomorphism(f, r1, x, r2, y) |- relationIsomorphism(inverseRelation(f), r2, y, r1, x)
  ) {
    have((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y), a ∈ y, b ∈ y, app(inverseRelation(f), a) ∈ x, app(inverseRelation(f), b) ∈ x) |- pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1 <=> pair(a, b) ∈ r2) by 
      Substitution.ApplyRules(inverseRelationRightCancel)(relationIsomorphismElim of (a := app(inverseRelation(f), a), b := app(inverseRelation(f), b)))
    have((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y), a ∈ y, b ∈ y, app(inverseRelation(f), b) ∈ x) |- pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1 <=> pair(a, b) ∈ r2) by Cut(inverseFunctionImageInDomain of (b := a), lastStep)
    have(((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y), a ∈ y, b ∈ y) |- pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1 <=> pair(a, b) ∈ r2)) by Cut(inverseFunctionImageInDomain, lastStep)
    thenHave((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y)) |- (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ r2 <=> pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1)) by Restate
    thenHave((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y)) |- ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ r2 <=> pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1))) by RightForall
    thenHave((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y)) |- ∀(a, ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ r2 <=> pair(app(inverseRelation(f), a), app(inverseRelation(f), b)) ∈ r1)))) by RightForall
    have((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y), bijective(inverseRelation(f), y, x), relationBetween(r1, x, x), relationBetween(r2, y, y)) |- relationIsomorphism(inverseRelation(f), r2, y, r1, x)) by Cut(lastStep, relationIsomorphismIntro of (f := inverseRelation(f), r1 := r2, x := y, r2 := r1, y := x))
    thenHave((relationIsomorphism(f, r1, x, r2, y), bijective(f, x, y), relationBetween(r1, x, x), relationBetween(r2, y, y)) |- relationIsomorphism(inverseRelation(f), r2, y, r1, x)) by Substitution.ApplyRules(inverseFunctionBijective)
    have((relationIsomorphism(f, r1, x, r2, y), relationBetween(r1, x, x), relationBetween(r2, y, y)) |- relationIsomorphism(inverseRelation(f), r2, y, r1, x)) by Cut(relationIsomorphismBijective, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationBetween(r2, y, y)) |- relationIsomorphism(inverseRelation(f), r2, y, r1, x)) by Cut(relationIsomorphismDomainIsRelation, lastStep)
    have(thesis) by Cut(relationIsomorphismRangeIsRelation, lastStep)      
  }

  val relationIsomorphismComposition = Lemma(
    (relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)
  ) {
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), a ∈ x, b ∈ x, app(f, a) ∈ y, app(f, b) ∈ y) |- pair(a, b) ∈ r1 <=> pair(app(g, app(f, a)), app(g, app(f, b))) ∈ r3) by 
      Substitution.ApplyRules(relationIsomorphismElim of (f := g, r1 := r2, r2 := r3, x := y, y := z, a := app(f, a), b := app(f, b)))(relationIsomorphismElim)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), a ∈ x, b ∈ x, app(f, b) ∈ y) |- pair(a, b) ∈ r1 <=> pair(app(g, app(f, a)), app(g, app(f, b))) ∈ r3) by Cut(relationIsomorphismAppInCodomain, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), a ∈ x, b ∈ x) |- pair(a, b) ∈ r1 <=> pair(app(g, app(f, a)), app(g, app(f, b))) ∈ r3) by Cut(relationIsomorphismAppInCodomain of (a := b), lastStep)
    thenHave((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, b ∈ x) |- pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3) by Substitution.ApplyRules(functionCompositionApp)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), functionFrom(g, y, z), a ∈ x, b ∈ x) |- pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3) by Cut(relationIsomorphismFunctionFrom, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), a ∈ x, b ∈ x) |- pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3) by Cut(relationIsomorphismFunctionFrom of (f := g, x := y, y := z, r1 := r2, r2 := r3), lastStep)
    thenHave((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z)) |- (a ∈ x /\ b ∈ x) ==> pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3) by Restate
    thenHave((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z)) |- ∀(b, (a ∈ x /\ b ∈ x) ==> pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3)) by RightForall
    thenHave((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z)) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> pair(a, b) ∈ r1 <=> pair(app(g ∘ f, a), app(g ∘ f, b)) ∈ r3))) by RightForall
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), relationBetween(r1, x, x), relationBetween(r3, z, z), bijective(g ∘ f, x, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)) by Cut(lastStep, relationIsomorphismIntro of (f := g ∘ f, r2 := r3, y := z))
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), relationBetween(r3, z, z), bijective(g ∘ f, x, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)) by Cut(relationIsomorphismDomainIsRelation, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), bijective(g ∘ f, x, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)) by Cut(relationIsomorphismRangeIsRelation of (r1 := r2, r2 := r3, f := g, x := y, y := z), lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), bijective(f, x, y), bijective(g, y, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)) by Cut(functionCompositionBijective, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z), bijective(g, y, z)) |- relationIsomorphism(g ∘ f, r1, x, r3, z)) by Cut(relationIsomorphismBijective, lastStep)
    have(thesis) by Cut(relationIsomorphismBijective of (f := g, r1 := r2, r2 := r3, x := y, y := z), lastStep)
  }

  val strictWellOrderIsomorphismUnique = Lemma(
    (strictWellOrder(r1, x), strictWellOrder(r2, y), relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r1, x, r2, y)) |- f === g
  ) {
    sorry
  }

  val isomorphic = DEF(r1, x, r2, y) --> ∃(f, relationIsomorphism(f, r1, x, r2, y))

  extension (p1: (Term, Term)) 
    def ≅ (p2: (Term, Term)): Formula = isomorphic(p1._1, p1._2, p2._1, p2._2)
    def ≃ (p2: (Term, Term)): Formula = isomorphic(p1._1, p1._2, p2._1, p2._2)

  val isomorphicIntro = Lemma(
    relationIsomorphism(f, r1, x, r2, y) |- (r1, x) ≃ (r2, y)
  ) {
    have(relationIsomorphism(f, r1, x, r2, y) |- relationIsomorphism(f, r1, x, r2, y)) by Hypothesis
    thenHave(relationIsomorphism(f, r1, x, r2, y) |- ∃(f, relationIsomorphism(f, r1, x, r2, y))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(isomorphic.definition)
  }

  val isomorphicElim = Lemma(
    (r1, x) ≃ (r2, y) |- ∃(f, relationIsomorphism(f, r1, x, r2, y))
  ) {
    have(thesis) by Weakening(isomorphic.definition)
  }

  val isomorphicTransitivity = Lemma(
    ((r1, x) ≃ (r2, y), (r2, y) ≃ (r3, z)) |- (r1, x) ≃ (r3, z)
  ) {
    have((relationIsomorphism(f, r1, x, r2, y), relationIsomorphism(g, r2, y, r3, z)) |- (r1, x) ≃ (r3, z)) by Cut(relationIsomorphismComposition, isomorphicIntro of (f := g ∘ f, r2 := r3, y := z))
    thenHave((∃(f, relationIsomorphism(f, r1, x, r2, y)), relationIsomorphism(g, r2, y, r3, z)) |- (r1, x) ≃ (r3, z)) by LeftExists
    thenHave((∃(f, relationIsomorphism(f, r1, x, r2, y)), ∃(g, relationIsomorphism(g, r2, y, r3, z))) |- (r1, x) ≃ (r3, z)) by LeftExists
    have(((r1, x) ≃ (r2, y), ∃(g, relationIsomorphism(g, r2, y, r3, z))) |- (r1, x) ≃ (r3, z)) by Cut(isomorphicElim, lastStep)
    have(thesis) by Cut(isomorphicElim of (r1 := r2, x := y, r2 := r3, y := z), lastStep)
  }

  val isomorphicSymmetry = Lemma(
    (r1, x) ≃ (r2, y) |- (r2, y) ≃ (r1, x)
  ) {
    have((relationIsomorphism(f, r1, x, r2, y)) |- (r2, y) ≃ (r1, x)) by Cut(inverseRelationIsomorphism, isomorphicIntro of (f := inverseRelation(f), r1 := r2, x := y, r2 := r1, y := x))
    thenHave((∃(f, relationIsomorphism(f, r1, x, r2, y))) |- (r2, y) ≃ (r1, x)) by LeftExists
    have(thesis) by Cut(isomorphicElim, lastStep)
  }
  
}
