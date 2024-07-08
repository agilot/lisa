package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import scala.collection.immutable.{Map => ScalaMap}

/**
 * Set Theory Library
 *
 * Develops Zermelo-Fraenkel Set Theory.
 * Uses the following book as the main reference:
 *
 * Jech, Thomas. Set theory: The third millennium edition, revised and expanded.
 * Springer Berlin Heidelberg, 2003.
 * [[https://link.springer.com/book/10.1007/3-540-44761-X]]
 */
object SetTheory extends lisa.Main {

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
  private val A = variable
  private val B = variable
  private val C = variable

  // relation and function symbols
  private val r = variable
  private val r1 = variable
  private val r2 = variable
  private val p = variable
  private val f = variable
  private val g = variable

  private val q = formulaVariable
  private val P = predicate[1]
  private val Q = predicate[1]
  private val R = predicate[2]
  private val F = function[1]
  private val schemPred = predicate[1]

  /**
   * Chapter 1
   */

  /**
   * Axioms of Set Theory
   *
   * See [[SetTheoryZAxioms]] and [[SetTheoryZFAxioms]]
   */

  /**
   * Theorems about basic sets
   */

  /**
   * Lemma --- Russel's Paradox
   *
   * Consider a set `x`, that contains every set that is not a member of itself.
   * The existence of `x` leads to a contradiction. This paradox forces the
   * current form of the comprehension schema, i.e. `{x ∈ X | Ψ(x, X)}`
   * instead of the full comprehension schema `{x | Ψ(x)}`.
   */
  val russelsParadox = Lemma(
    ∃(x, ∀(y, !in(y, y) <=> in(y, x))) |- ()
  ) {
    val contra = !in(x, x) <=> in(x, x)

    have(contra |- ()) by Restate
    thenHave(∀(y, !in(y, y) <=> in(y, x)) |- ()) by LeftForall
    thenHave(∃(x, ∀(y, !in(y, y) <=> in(y, x))) |- ()) by LeftExists
  }

  /**
   * Lemma --- Uniqueness by Definition
   *
   * If a set is defined by its elements, existence implies uniqueness.
   *
   *    `∃ z. ∀ t. t ∈ z ⇔ P(t) ⊢ ∃! z. ∀ t. t ∈ z ⇔ P(t)`
   *
   * where `P(t)` does not contain `z` as a free variable.
   *
   * Instantiation will fail if `myProperty(t)` contains `z` as a free variable.
   */
  val uniqueByExtension = Lemma(
    ∃(z, ∀(t, in(t, z) <=> schemPred(t))) |- ∃!(z, ∀(t, in(t, z) <=> schemPred(t)))
  ) {
    def prop(z: Term) = in(t, z) <=> schemPred(t)
    def fprop(z: Term) = ∀(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    thenHave((fprop(z), (z === a)) |- fprop(a)) by RightSubstEq.withParametersSimple(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = thenHave(fprop(z) |- (z === a) ==> fprop(a)) by RightImplies

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val hyp = thenHave(fprop(z) |- prop(z)) by InstantiateForall(t)
    have((fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(lastStep, lastStep of (z := a))
    thenHave((fprop(z), fprop(a)) |- in(t, a) <=> in(t, z)) by Tautology
    thenHave((fprop(z), fprop(a)) |- ∀(t, in(t, a) <=> in(t, z))) by RightForall

    have((fprop(z), fprop(a)) |- (∀(t, in(t, a) <=> in(t, z)) <=> (a === z)) /\ ∀(t, in(t, a) <=> in(t, z))) by RightAnd(lastStep, extensionalityAxiom of (x := a, y := z))
    thenHave((fprop(z), fprop(a)) |- (a === z)) by Tautology
    val backward = thenHave(fprop(z) |- fprop(a) ==> (a === z)) by RightImplies

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    thenHave(fprop(z) |- ∀(a, fprop(a) <=> (a === z))) by RightForall
    thenHave(fprop(z) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by RightExists
    thenHave(∃(z, fprop(z)) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by LeftExists
    thenHave(∃(z, fprop(z)) |- ∃!(z, fprop(z))) by RightExistsOne
  }

  val equalityIntro = Lemma(
    forall(z, in(z, x) <=> in(z, y)) |- x === y
  ) {
    have(thesis) by Weakening(extensionalityAxiom)
  }

  /**
   * Replacement schema
   */

  def classFunction(R: Term ** 2 |-> Formula, P: Term ** 1 |-> Formula): Formula = forall(x, P(x) ==> existsOne(y, R(x, y)))
  def classFunction(R: Term ** 2 |-> Formula): Formula = classFunction(R, lambda(x, True))
  def classFunction(R: Term ** 2 |-> Formula, A: Term): Formula = classFunction(R, lambda(x, in(x, A)))

  val classFunctionElim = Lemma(
    (classFunction(R, P), P(x)) |- existsOne(y, R(x, y))
  ) {
    have(classFunction(R, P) |- classFunction(R, P)) by Hypothesis
    thenHave(thesis) by InstantiateForall(x)
  }

  val totalClassFunctionElim = Lemma(
    classFunction(R) |- existsOne(y, R(x, y))
  ) {
    have(thesis) by Restate.from(classFunctionElim of (P := lambda(x, True)))
  }

  val classFunctionUniqueness = Lemma(
    (classFunction(R, P), P(x), R(x, y), R(x, z)) |- y === z
  ) {
    have(thesis) by Cut(classFunctionElim, existsOneImpliesUniqueness of (P := lambda(z, R(x, z)), x := y, y := z))
  }

  val totalClassFunctionUniqueness = Lemma(
    (classFunction(R), R(x, y), R(x, z)) |- y === z
  ) {
    have(thesis) by Restate.from(classFunctionUniqueness of (P := lambda(x, True)))
  }

  val functionIsClassFunction = Lemma(
    classFunction(lambda((x, y), F(x) === y), P)
  ) {
    have(((F(x) === y) /\ (F(x) === z)) ==> (y === z)) by Restate.from(equalityTransitivity of (x := y, y := F(x)))
    thenHave(forall(z, ((F(x) === y) /\ (F(x) === z)) ==> (y === z))) by RightForall
    val uniqueness = thenHave(forall(y, forall(z, ((F(x) === y) /\ (F(x) === z)) ==> (y === z)))) by RightForall

    have(F(x) === F(x)) by RightRefl
    val existence = thenHave(exists(y, F(x) === y)) by RightExists

    have(exists(y, F(x) === y) |- existsOne(y, F(x) === y)) by Cut(uniqueness of (P := lambda(y, F(x) === y)), existenceAndUniqueness of (P := lambda(y, F(x) === y)))
    have(existsOne(y, F(x) === y)) by Cut(existence, lastStep)
    thenHave(P(x) ==> existsOne(y, F(x) === y)) by Weakening
    thenHave(thesis) by RightForall
  }

  val replacementExistence = Lemma(
    classFunction(R, A) |- exists(B, forall(y, in(y, B) <=> exists(x, in(x, A) /\ R(x, y))))
  ) {
    have(∃!(y, R(x, y)) |- (R(x, y) /\ R(x, z)) ==> (y === z)) by Restate.from(existsOneImpliesUniqueness of (P := lambda(y, R(x, y)), x := y, y := z))
    thenHave(∃!(y, R(x, y)) |- forall(z, (R(x, y) /\ R(x, z)) ==> (y === z))) by RightForall
    thenHave(∃!(y, R(x, y)) |- forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by RightForall
    thenHave(in(x, A) ==> ∃!(y, R(x, y)) |- in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by Tautology
    thenHave(classFunction(R, A) |- in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by LeftForall
    val uniqueness = thenHave(classFunction(R, A) |- forall(x, in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z))))) by RightForall

    have(forall(x, in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) |- exists(B, forall(b, in(b, B) <=> exists(x, in(x, A) /\ R(x, b))))) by
      Restate.from({ val P = predicate[2]; replacementSchema of (P := R) })
    have(thesis) by Cut(uniqueness, lastStep)
  }

  val replacementUniqueness = Lemma(
    classFunction(R, A) |- existsOne(B, forall(y, in(y, B) <=> exists(x, in(x, A) /\ R(x, y))))
  ) {
    have(thesis) by Cut(replacementExistence, uniqueByExtension of (z := B, schemPred := lambda(b, exists(x, in(x, A) /\ R(x, b)))))
  }

  val replacementClassFunction = Lemma(
    existsOne(B, forall(y, in(y, B) <=> exists(x, in(x, A) /\ (F(x) === y))))
  ) {
    have(thesis) by Cut(functionIsClassFunction of (P := lambda(x, in(x, A))), replacementUniqueness of (R := lambda((x, y), F(x) === y)))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Empty Set
   */

  /**
   * Lemma --- If a set has an element, then it is not the empty set.
   *
   *    `y ∈ x ⊢ x ≠ ∅`
   */
  val setWithElementNonEmpty = Lemma(
    in(y, x) |- !(x === ∅)
  ) {
    have((x === ∅) |- !in(y, x)) by Substitution.ApplyRules(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
   * Lemma --- If a set is empty, then it has no elements.
   *
   *    `x = ∅ ⊢ y ∉ x`
   */
  val setEmptyHasNoElements = Lemma(
    (x === ∅) |- !in(y, x)
  ) {
    have(thesis) by Restate.from(setWithElementNonEmpty)
  }

  /**
   * Lemma --- A set containing no elements is empty.
   *
   *    `∀ y. y ∉ x ⊢ x = ∅`
   */
  val setWithNoElementsIsEmpty = Lemma(
    ∀(y, !in(y, x)) |- (x === ∅)
  ) {
    val lhs = have(in(y, ∅) ==> in(y, x)) by Weakening(emptySetAxiom of (x := y))

    have(!in(y, x) |- !in(y, x)) by Hypothesis
    thenHave(!in(y, x) |- (!in(y, x), in(y, ∅))) by Weakening
    val rhs = thenHave(!in(y, x) |- in(y, x) ==> in(y, ∅)) by Restate

    have(!in(y, x) |- in(y, x) <=> in(y, ∅)) by RightIff(lhs, rhs)
    thenHave(∀(y, !in(y, x)) |- in(y, x) <=> in(y, ∅)) by LeftForall
    thenHave(∀(y, !in(y, x)) |- ∀(y, in(y, x) <=> in(y, ∅))) by RightForall
    have(∀(y, !in(y, x)) |- (x === ∅)) by Cut(lastStep, equalityIntro of (y := ∅))
  }

  /**
   * Lemma --- Any non-empty set has an element.
   * 
   *   `x ≠ ∅ ⊢ ∃ y. y ∈ x`
   */
  val nonEmptySetHasAnElement = Lemma(
    !(x === ∅) |- exists(y, in(y, x))
  ) {
    have(thesis) by Restate.from(setWithNoElementsIsEmpty)
  }

  /**
   * Subset properties
   */

  /**
   * Lemma --- Subset introduction rule
   * 
   *  `∀ z. z ∈ x ⇒ z ∈ y ⊢ x ⊆ y`
   */
  val subsetIntro = Lemma(forall(z, in(z, x) ==> in(z, y)) |- subset(x, y)) {
    have(thesis) by Weakening(subsetAxiom)
  }

  /**
   * Lemma --- Subset elimination rule
   *
   *  `x ⊆ y, z ∈ x ⊢ z ∈ y`
   */
  val subsetElim = Lemma((subset(x, y), in(z, x)) |- in(z, y)) {
    have(subset(x, y) |- forall(z, in(z, x) ==> in(z, y))) by Weakening(subsetAxiom)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma ---  Subset reflexivity
   *
   *   `x ⊆ x`
   */
  val subsetReflexivity = Lemma(
    subset(x, x)
  ) {
    have(in(z, x) ==> in(z, x)) by Restate
    thenHave(∀(z, in(z, x) ==> in(z, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := x))
  }

  /**
   * Lemma --- Subset antisymmetry
   *
   *   `x ⊆ y, y ⊆ x |- x = y`
   */
  val subsetAntisymmetry = Lemma(
    (subset(x, y), subset(y, x)) |- (x === y)
  ) {
    val forward = have(subset(x, y) |- in(z, x) ==> in(z, y)) by RightImplies(subsetElim)
    val backward = have(subset(y, x) |- in(z, y) ==> in(z, x)) by RightImplies(subsetElim of (x := y, y := x))
    have((subset(x, y), subset(y, x)) |- in(z, x) <=> in(z, y)) by RightIff(forward, backward)
    thenHave((subset(x, y), subset(y, x)) |- forall(z, in(z, x) <=> in(z, y))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro)
  }

  /**
   * Lemma --- Subset transitivity
   *
   *    `x ⊆ y, y ⊆ z ⊢ x ⊆ z`
   */
  val subsetTransitivity = Lemma(
    (subset(x, y), subset(y, z)) |- subset(x, z)
  ) {
    have((subset(x, y), subset(y, z), in(a, x)) |- in(a, z)) by Cut(subsetElim of (z := a), subsetElim of (x := y, y := z, z := a))
    thenHave((subset(x, y), subset(y, z)) |- in(a, x) ==> in(a, z)) by RightImplies
    thenHave((subset(x, y), subset(y, z)) |- forall(a, in(a, x) ==> in(a, z))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := z))
  }

  /**
   * Lemma --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val emptySetSubset = Lemma(
    subset(∅, x)
  ) {
    have(in(y, ∅) ==> in(y, x)) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, in(y, ∅) ==> in(y, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := ∅, y := x))
  }

  /**
   * Lemma --- Any subset of the empty set is empty.
   *
   *    `x ⊆ ∅ <=> x = ∅`
   */
  val subsetEmptySet = Lemma(
    subset(x, emptySet) <=> (x === emptySet)
  ) {
    val forward = have(subset(x, emptySet) ==> (x === emptySet)) subproof {
      have((subset(x, emptySet), in(z, x)) |- ()) by RightAnd(subsetElim of (y := emptySet), emptySetAxiom of (x := z))
      thenHave((subset(x, emptySet), exists(z, in(z, x))) |- ()) by LeftExists
      have((subset(x, emptySet), !(x === emptySet)) |- ()) by Cut(nonEmptySetHasAnElement, lastStep)
    }

    val backward = have((x === emptySet) ==> subset(x, emptySet)) subproof {
      have((x === emptySet) |- subset(x, emptySet)) by RightSubstEq.withParametersSimple(List((x, emptySet)), lambda(x, subset(x, emptySet)))(emptySetSubset of (x := emptySet))
    }

    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Lemma --- A superset of a non empty set is non empty.
   *
   *     `x ⊆ y, x ≠ ∅ ⊢ y ≠ ∅`
   */
  val subsetNotEmpty = Lemma(
    (subset(x, y), !(x === ∅)) |- !(y === ∅)
  ) {
    have(subset(x, emptySet) |- x === emptySet) by Weakening(subsetEmptySet)
    thenHave((subset(x, y), y === emptySet) |- x === emptySet) by LeftSubstEq.withParametersSimple(List((y, emptySet)), lambda(y, subset(x, y)))
  }

  /**
   * Power set properties
   */

  /**
   * Lemma --- Power set introduction rule
   * 
   *  `x ⊆ y ⊢ x ∈ 𝓟(y)`
   */
  val powerSetIntro = Lemma(
    subset(x, y) |- in(x, powerSet(y))
  ) {
    have(thesis) by Weakening(powerAxiom)
  }

  /**
   * Lemma --- Power set elimination rule
   *
   *  `x ∈ 𝓟(y) ⊢ x ⊆ y`
   */
  val powerSetElim = Lemma(
    in(x, powerSet(y)) |- subset(x, y)
  ) {
    have(thesis) by Weakening(powerAxiom)
  }

  /**
   * Lemma --- Any set is in its power set.
   * 
   *  `x ∈ 𝓟(x)`
   */
  val powerSetContainsSet = Lemma(
    in(x, powerSet(x))
  ) {
    have(thesis) by Cut(subsetReflexivity, powerSetIntro of (y := x))
  }

  /**
   * Lemma --- The empty set is in every power set.
   *
   *    `∅ ∈ 𝓟(x)`
   */
  val powerSetContainsEmptySet = Lemma(
    in(∅, powerSet(x))
  ) {
    have(thesis) by Cut(emptySetSubset, powerSetIntro of (x := emptySet, y := x))
  }

  /**
   * Lemma --- The power set is never empty.
   *
   *    `𝓟(x) ≠ ∅`
   */
  val powerSetNonEmpty = Lemma(
    !(powerSet(x) === ∅)
  ) {
    have(thesis) by Cut(powerSetContainsEmptySet, setWithElementNonEmpty of (y := ∅, x := powerSet(x)))
  }

  /**
   * Properties about pairs
   */

  /**
   * Lemma --- Unordered pair left introduction rule
   *
   *    `x ∈ {x, y}`
   *
   */
  val unorderedPairLeftIntro = Lemma(
    in(x, unorderedPair(x, y))
  ) {
    have(thesis) by Weakening(pairAxiom of (z := x))
  }

  /**
   * Lemma --- Unordered pair right introduction rule
   *
   *    `y ∈ {x, y}`
   *
   */
  val unorderedPairRightIntro = Lemma(
    in(y, unorderedPair(x, y))
  ) {
    have(thesis) by Weakening(pairAxiom of (z := y))
  }

  /**
   * Lemma --- Unordered pair elimination rule
   * 
   *   `z ∈ {x, y} |- z = x ∨ z = y`
   */
  val unorderedPairElim = Lemma(
    in(z, unorderedPair(x, y)) |- (z === x, z === y)
  ) {
    have(thesis) by Weakening(pairAxiom)
  }

  /**
   * Lemma --- An unordered pair is never empty.
   * 
   *   `{x, y} ≠ ∅`
   */
  val unorderedPairNonEmpty = Lemma(
    !(unorderedPair(x, y) === ∅)
  ) {
    have(thesis) by Cut(unorderedPairRightIntro, setWithElementNonEmpty of (x := unorderedPair(x, y)))
  }

  val unorderedPairSubset = Lemma(
    subset(unorderedPair(x, y), z) <=> (in(x, z) /\ in(y, z)) 
  ) {
    val forward = have(subset(unorderedPair(x, y), z) ==> (in(x, z) /\ in(y, z))) subproof {
      val left = have(subset(unorderedPair(x, y), z) |- in(x, z)) by Cut(unorderedPairLeftIntro, subsetElim of (x := unorderedPair(x, y), y := z, z := x))
      val right = have(subset(unorderedPair(x, y), z) |- in(y, z)) by Cut(unorderedPairRightIntro, subsetElim of (x := unorderedPair(x, y), y := z, z := y))
      have(subset(unorderedPair(x, y), z) |- in(x, z) /\ in(y, z)) by RightAnd(left, right)
    } 

    val backward = have((in(x, z) /\ in(y, z)) ==> subset(unorderedPair(x, y), z)) subproof {
      have(in(x, z) |- in(x, z)) by Hypothesis
      val seq = thenHave((in(x, z), w === x) |- in(w, z)) by RightSubstEq.withParametersSimple(List((w, x)), lambda(x, in(x, z)))
      have((in(w, unorderedPair(x, y)), in(x, z)) |- (in(w, z), w === y)) by Cut(unorderedPairElim of (z := w), seq)
      have((in(w, unorderedPair(x, y)), in(x, z), in(y, z)) |- in(w, z)) by Cut(lastStep, seq of (x := y))
      thenHave((in(x, z), in(y, z)) |- in(w, unorderedPair(x, y)) ==> in(w, z)) by RightImplies
      thenHave((in(x, z), in(y, z)) |- forall(w, in(w, unorderedPair(x, y)) ==> in(w, z))) by RightForall
      have((in(x, z), in(y, z)) |- subset(unorderedPair(x, y), z)) by Cut(lastStep, subsetIntro of (x := unorderedPair(x, y), y := z))
    }
    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Lemma --- Unordered pair symmetry
   *
   *    `{x, y} = {y, x}`
   */
  val unorderedPairSymmetry = Lemma(
    unorderedPair(x, y) === unorderedPair(y, x)
  ) {
    have(in(z, unorderedPair(y, x)) <=> in(z, unorderedPair(x, y))) by Substitution.ApplyRules(pairAxiom)(pairAxiom of (x := y, y := x))
    thenHave(∀(z, in(z, unorderedPair(x, y)) <=> in(z, unorderedPair(y, x)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := unorderedPair(x, y), y := unorderedPair(y, x)))
  }

  // TODO
  val unorderedPairDeconstruction = Lemma(
    (unorderedPair(a, b) === unorderedPair(c, d)) |- (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    val s1 = have(Substitution.applySubst(unorderedPair(a, b) === unorderedPair(c, d))(pairAxiom of (x := a, y := b)))
    val base = have(Substitution.applySubst(s1)(pairAxiom of (x := c, y := d)))

    have(thesis) by Tautology.from(base of (z := a), base of (z := b), base of (z := c), base of (z := d))
  }

  /**
   * Lemma --- Two [[unorderedPair]]s are equal iff their elements are equal pairwise.
   *
   *    `{a, b} = {c, d} <=> (a = c ∧ b = d) ∨ (a = d ∧ b = c)`
   */
  val unorderedPairExtensionality = Lemma(
    (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    val forward = have((unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightImplies(unorderedPairDeconstruction)

    val backward = have((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) ==> (unorderedPair(a, b) === unorderedPair(c, d))) subproof {
      have(unorderedPair(a, b) === unorderedPair(a, b)) by RightRefl
      thenHave((a === c, b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by RightSubstEq.withParametersSimple(
        List((a, c), (b, d)),
        lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(x, y))
      )
      val lhs = thenHave((a === c) /\ (b === d) |- unorderedPair(a, b) === unorderedPair(c, d)) by LeftAnd

      have((a === d, b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by RightSubstEq.withParametersSimple(
        List((a, d), (b, c)),
        lambda(Seq(x, y), unorderedPair(a, b) === unorderedPair(y, x))
      )(unorderedPairSymmetry of (x := a, y := b))
      val rhs = thenHave((a === d) /\ (b === c) |- (unorderedPair(a, b) === unorderedPair(c, d))) by LeftAnd

      have((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) |- (unorderedPair(a, b) === unorderedPair(c, d))) by LeftOr(lhs, rhs)
    }

    have((unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightIff(forward, backward)
  }

  /**
   * Lemma --- Unordered pairs of elements of a set are in its power set.
   *
   *    `a ∈ x ∧ b ∈ x <=> {a, b} ∈ 𝓟(x)` 
   */
  val unorderedPairInPowerSet = Lemma(
    (in(x, z) /\ in(y, z)) <=> in(unorderedPair(x, y), powerSet(z))
  ) {
    have(subset(unorderedPair(x, y), z) <=> (in(x, z) /\ in(y, z)) |- (in(x, z) /\ in(y, z)) <=> in(unorderedPair(x, y), powerSet(z))) by RightSubstIff.withParametersSimple(
      List((subset(unorderedPair(x, y), z), in(x, z) /\ in(y, z))), lambda(h, h <=> in(unorderedPair(x, y), powerSet(z))) 
    )(powerAxiom of (x := unorderedPair(x, y), y := z))
    have(thesis) by Cut(unorderedPairSubset, lastStep)
  }

  /**
   * Definition --- Singleton Set
   *
   *   `{x} = {x, x}`
   */
  val singleton = DEF(x) --> unorderedPair(x, x)

  /**
   * Lemma --- Singleton membership rule
   *
   *    `y ∈ {x} <=> y = x`
   */
  val singletonMembership = Lemma(
    in(y, singleton(x)) <=> (x === y)
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(pairAxiom of (z := y, y := x))
  }

  /**
   * Lemma --- Singleton introduction rule
   *
   *   `x ∈ {x}`
   */
  val singletonIntro = Lemma(in(x, singleton(x))) {
    have(thesis) by Restate.from(singletonMembership of (y := x))
  }

  /**
   * Lemma --- Singleton elimination rule
   *
   *   `y ∈ {x} |- x = y`
   */
  val singletonElim = Lemma(in(y, singleton(x)) |- x === y) {
    have(thesis) by Weakening(singletonMembership)
  }

  /**
   * Lemma --- A singleton set is never empty.
   *
   *    `! {x} = ∅`
   */
  val singletonNonEmpty = Lemma(
    !(singleton(x) === ∅)
  ) {
    have(thesis) by Cut(singletonIntro, setWithElementNonEmpty of (y := x, x := singleton(x)))
  }

  val singletonSubset = Lemma(
    subset(singleton(x), y) <=> in(x, y) 
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(unorderedPairSubset of (y := x, z := y))
  }

  /**
   * Lemma --- Two singletons are equal iff their elements are equal
   *
   *    `{x} = {y} <=> x = y`
   */
  val singletonExtensionality = Lemma(
    (singleton(x) === singleton(y)) <=> (x === y)
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition, singleton.shortDefinition of (x := y))(unorderedPairExtensionality of (a := x, b := x, c := y, d := y))
  }

  val singletonEqualsUnorderedPair = Lemma(
    (singleton(x) === unorderedPair(y, z)) <=> ((x === y) /\ (x === z))
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(unorderedPairExtensionality of (a := x, b := x, c := y, d := z))
  }

  /**
   * Lemma --- The singleton of an element of a set is in its power set.
   * 
   *   `x ∈ y <=> {x} ∈ 𝓟(y)`
   */
  val singletonInPowerSet = Lemma(
    in(x, y) <=> in(singleton(x), powerSet(y))
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(unorderedPairInPowerSet of (y := x, z := y))
  }

  /**
   * Union properties
   */

  /**
   * Lemma --- Union introduction rule
   *
   *   `z ∈ y, y ∈ x ⊢ z ∈ ∪ x`
   */
  val unionIntro = Lemma((in(z, y), in(y, x)) |- in(z, union(x))) {
    have((in(z, y), in(y, x)) |- in(y, x) /\ in(z, y)) by Restate
    thenHave((in(z, y), in(y, x)) |- exists(y, in(y, x) /\ in(z, y))) by RightExists
    thenHave((in(z, y), in(y, x)) |- in(z, union(x))) by Substitution.ApplyRules(unionAxiom)
  }

  /**
   * Lemma --- Union elimination rule
   *
   *   `z ∈ ∪ x |- ∃ y ∈ x. z ∈ y`
   */
  val unionElim = Lemma(in(z, union(x)) |- exists(y, in(y, x) /\ in(z, y))) {
    have(thesis) by Weakening(unionAxiom)
  }

  /**
   * Lemma --- Any element of a set is a subset of its union.
   * 
   *   `z ∈ x |- z ⊆ ∪ x`
   */
  val subsetUnion = Lemma(in(x, y) |- subset(x, union(y))) {
    have(in(x, y) |- in(z, x) ==> in(z, union(y))) by RightImplies(unionIntro of (x := y, y := x))
    thenHave(in(x, y) |- forall(z, in(z, x) ==> in(z, union(y)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := union(y)))
  }

  /**
   * Lemma --- The union of the empty set is the empty set.
   *
   *    `∪ ∅ = ∅`
   */
  val unionEmpty = Lemma(union(emptySet) === emptySet) {
    have(in(y, emptySet) /\ in(x, y) |- ()) by Weakening(emptySetAxiom of (x := y))
    thenHave(exists(y, in(y, emptySet) /\ in(x, y)) |- ()) by LeftExists
    have(in(x, union(emptySet)) |- ()) by Cut(unionElim of (z := x, x := emptySet), lastStep)
    thenHave(exists(x, in(x, union(emptySet))) |- ()) by LeftExists
    have(!(union(emptySet) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := union(emptySet)), lastStep)
  }

  /**
   * Lemma --- Union is monotonic
   *
   *    `x ⊆ y |- ∪ x ⊆ ∪ y`
   */
  val unionMonotonicity = Lemma(subset(x, y) |- subset(union(x), union(y))) {
    have((in(z, w), in(w, x), subset(x, y)) |- in(z, union(y))) by Cut(subsetElim of (z := w), unionIntro of (y := w, x := y))
    thenHave((in(z, w) /\ in(w, x), subset(x, y)) |- in(z, union(y))) by LeftAnd
    thenHave((exists(w, in(z, w) /\ in(w, x)), subset(x, y)) |- in(z, union(y))) by LeftExists
    have((in(z, union(x)), subset(x, y)) |- in(z, union(y))) by Cut(unionElim, lastStep)
    thenHave(subset(x, y) |- in(z, union(x)) ==> in(z, union(y))) by RightImplies
    thenHave(subset(x, y) |- forall(z, in(z, union(x)) ==> in(z, union(y)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := union(x), y := union(y)))
  }

  /**
   * Lemma --- The union of a Singleton is the original set
   * 
   *      `∪ {x} = x`
   */
  val unionSingleton = Lemma((union(singleton(x)) === x)) {
    have((in(y, singleton(x)) /\ in(z, y)) <=> (in(y, singleton(x)) /\ in(z, y))) by Restate
    thenHave((in(y, singleton(x)) /\ in(z, y)) <=> ((x === y) /\ in(z, y))) by Substitution.ApplyRules(singletonMembership)
    thenHave(forall(y, (in(y, singleton(x)) /\ in(z, y)) <=> ((x === y) /\ in(z, y)))) by RightForall
    have(exists(y, in(y, singleton(x)) /\ in(z, y)) <=> exists(y, (x === y) /\ in(z, y))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(y, in(y, singleton(x)) /\ in(z, y)), Q := lambda(y, (x === y) /\ in(z, y)))
    )
    thenHave(in(z, union(singleton(x))) <=> in(z, x)) by Substitution.ApplyRules(unionAxiom, onePointRule of (y := x, Q := lambda(y, in(z, y))))
    thenHave(∀(z, in(z, union(singleton(x))) <=> in(z, x))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(singleton(x)), y := x))
  }

  val unorderedPairElementsInUnion = Lemma(
    in(unorderedPair(x, y), r) |- in(x, union(r)) /\ in(y, union(r))
  ) {
    val left = have(in(unorderedPair(x, y), r) |- in(x, union(r))) by Cut(unorderedPairLeftIntro, unionIntro of (z := x, y := unorderedPair(x, y), x := r))
    val right = have(in(unorderedPair(x, y), r) |- in(y, union(r))) by Cut(unorderedPairRightIntro, unionIntro of (z := y, y := unorderedPair(x, y), x := r))
    have(thesis) by RightAnd(left, right)
  }

  val singletonElementInUnion = Lemma(
    in(singleton(x), r) |- in(x, union(r))
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(unorderedPairElementsInUnion of (y := x))
  }

  /**
   * Binary union properties
   */

  /**
   * Definition --- Binary Set Union
   *
   *   `x ∪ y = ∪ {x, y}`
   */
  val setUnion: ConstantFunctionLabel[2] = DEF(x, y) --> union(unorderedPair(x, y))

  /**
   * Lemma --- Binary Union Membership
   *
   *   `z ∈ x ∪ y ⇔ z ∈ x ∨ z ∈ y`
   */
  val setUnionMembership = Lemma(
    in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))
  ) {
    have((in(z, a) /\ ((a === x) \/ (a === y))) <=> (((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a)))) by Tautology
    thenHave((in(z, a) /\ in(a, unorderedPair(x, y))) <=> (((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a)))) by Substitution.ApplyRules(pairAxiom of (z := a))
    thenHave(forall(a, (in(z, a) /\ in(a, unorderedPair(x, y))) <=> (((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a))))) by RightForall
    have(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> exists(a, ((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a)))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, (in(z, a) /\ in(a, unorderedPair(x, y)))), Q := lambda(a, ((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a))))
    )
    thenHave(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (exists(a, (a === x) /\ in(z, a)) \/ exists(a, in(z, a) /\ (a === y)))) by Substitution.ApplyRules(
      existentialDisjunctionCommutation of (P := lambda(a, (a === x) /\ in(z, a)), Q := lambda(a, in(z, a) /\ (a === y)))
    )
    thenHave(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (in(z, x) \/ exists(a, in(z, a) /\ (a === y)))) by Substitution.ApplyRules(onePointRule of (y := x, Q := lambda(a, in(z, a))))
    thenHave(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (in(z, x) \/ in(z, y))) by Substitution.ApplyRules(onePointRule of (Q := lambda(a, in(z, a))))
    thenHave(in(z, union(unorderedPair(x, y))) <=> (in(z, x) \/ in(z, y))) by Substitution.ApplyRules(unionAxiom of (x := unorderedPair(x, y)))
    thenHave(thesis) by Substitution.ApplyRules(setUnion.shortDefinition)
  }

  /**
   * Lemma --- Binary union left introduction rule
   *
   *   `z ∈ x ⊢ z ∈ x ∪ y`
   */
  val setUnionLeftIntro = Lemma(in(z, x) |- in(z, setUnion(x, y))) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- Binary union right introduction rule
   *
   *   `z ∈ y ⊢ z ∈ x ∪ y`
   */
  val setUnionRightIntro = Lemma(in(z, y) |- in(z, setUnion(x, y))) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- Binary union elimination rule
   *
   *   `z ∈ x ∪ y ⊢ z ∈ x ∨ z ∈ y`
   */
  val setUnionElim = Lemma(in(z, setUnion(x, y)) |- (in(z, x), in(z, y))) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- the binary set union operation is commutative.
   *
   *    `a ∪ b = b ∪ a`
   */
  val setUnionCommutativity = Lemma(
    setUnion(a, b) === setUnion(b, a)
  ) {
    have(in(z, setUnion(a, b)) <=> in(z, setUnion(b, a))) by Substitution.ApplyRules(setUnionMembership of (x := b, y := a))(setUnionMembership of (x := a, y := b))
    thenHave(forall(z, in(z, setUnion(a, b)) <=> in(z, setUnion(b, a)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := setUnion(a, b), y := setUnion(b, a)))
  }

  /**
   * Lemma --- the first element of a union is a subset of it.
   *
   *    `a ⊆ a ∪ b`
   */
  val setUnionLeftSubset = Lemma(
    subset(a, setUnion(a, b))
  ) {
    have(in(z, a) ==> in(z, setUnion(a, b))) by RightImplies(setUnionLeftIntro of (x := a, y := b))
    thenHave(forall(z, in(z, a) ==> in(z, setUnion(a, b)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := a, y := setUnion(a, b)))
  }

  /**
   * Lemma --- the second element of a union is a subset of it.
   *
   *    `b ⊆ a ∪ b`
   */
  val setUnionRightSubset = Lemma(
    subset(b, setUnion(a, b))
  ) {
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity)(setUnionLeftSubset of (a := b, b := a))
  }

  /**
   * Lemma --- the union of two subsets of a set is still a subset of it.
   *
   *    `a ⊆ c ∧ b ⊆ c ⊢ a ∪ b ⊆ c`
   */
  val unionOfTwoSubsets = Lemma(
    (subset(a, c), subset(b, c)) |- subset(setUnion(a, b), c)
  ) {
    have((in(z, setUnion(a, b)), subset(a, c)) |- (in(z, c), in(z, b))) by Cut(setUnionElim of (x := a, y := b), subsetElim of (x := a, y := c))
    have((in(z, setUnion(a, b)), subset(a, c), subset(b, c)) |- in(z, c)) by Cut(lastStep, subsetElim of (x := b, y := c))
    thenHave((subset(a, c), subset(b, c)) |- in(z, setUnion(a, b)) ==> in(z, c)) by RightImplies
    thenHave((subset(a, c), subset(b, c)) |- forall(z, in(z, setUnion(a, b)) ==> in(z, c))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setUnion(a, b), y := c))
  }

  /**
   * Lemma --- the union of subsets of two sets is a subset of their union.
   *
   *    `a ⊆ c ∧ b ⊆ d ⊢ a ∪ b ⊆ c ∪ d`
   */
  val unionOfSubsetsOfDifferentSets = Lemma(
    (subset(a, c), subset(b, d)) |- subset(setUnion(a, b), setUnion(c, d))
  ) {
    have((in(z, setUnion(a, b)), subset(a, c)) |- (in(z, c), in(z, b))) by Cut(setUnionElim of (x := a, y := b), subsetElim of (x := a, y := c))
    have((in(z, setUnion(a, b)), subset(a, c), subset(b, d)) |- (in(z, c), in(z, d))) by Cut(lastStep, subsetElim of (x := b, y := d))
    have((in(z, setUnion(a, b)), subset(a, c), subset(b, d)) |- (in(z, setUnion(c, d)), in(z, d))) by Cut(lastStep, setUnionLeftIntro of (x := c, y := d))
    have((in(z, setUnion(a, b)), subset(a, c), subset(b, d)) |- in(z, setUnion(c, d))) by Cut(lastStep, setUnionRightIntro of (x := c, y := d))
    thenHave((subset(a, c), subset(b, d)) |- in(z, setUnion(a, b)) ==> in(z, setUnion(c, d))) by RightImplies
    thenHave((subset(a, c), subset(b, d)) |- forall(z, in(z, setUnion(a, b)) ==> in(z, setUnion(c, d)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setUnion(a, b), y := setUnion(c, d)))
  }

  /**
   * Lemma --- Binary union with the emptySet
   *
   *   `x ∪ ∅ = x`
   */
  val setUnionRightEmpty = Lemma(
    setUnion(a, emptySet) === a
  ) {
    have(in(z, emptySet) <=> False) by Restate.from(emptySetAxiom of (x := z))
    have(in(z, setUnion(a, emptySet)) <=> (in(z, a) \/ False)) by Substitution.ApplyRules(lastStep)(setUnionMembership of (x := a, y := emptySet))
    thenHave(forall(z, in(z, setUnion(a, emptySet)) <=> in(z, a))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := setUnion(a, emptySet), y := a))
  }

  /**
   * Lemma --- Binary union with the emptySet
   *
   *   `∅ ∪ x = x`
   */
  val setUnionLeftEmpty = Lemma(
    setUnion(emptySet, a) === a
  ) {
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity)(setUnionRightEmpty)
  }

  /**
   * Unary Intersection
   */

  val intersectionUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))
  ) {
    have(thesis) by UniqueComprehension(union(x), lambda(t, ∀(b, in(b, x) ==> in(t, b))))
  }

  /**
   * Unary Set Intersection --- Intersection of all elements of a given set.
   *
   *     `∩ x = {z ∈ ∪ x | ∀ y ∈ x. z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   */
  val intersection = DEF(x) --> The(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(y, in(y, x) ==> in(t, y)))))(intersectionUniqueness)

  /**
   * Lemma --- Intersection membership rule
   *
   *    `x ≠ ∅ ⊢ z ∈ ∩ x ⇔ ∀ y ∈ x. z ∈ y`
   */
  val intersectionMembership = Lemma(
    !(x === emptySet) |- in(z, intersection(x)) <=> ∀(y, in(y, x) ==> in(z, y))
  ) {

    have(∀(y, in(y, x) ==> in(z, y)) |- ∀(y, in(y, x) ==> in(z, y))) by Hypothesis
    thenHave((∀(y, in(y, x) ==> in(z, y)), in(y, x)) |- in(z, y)) by InstantiateForall(y)
    have((∀(y, in(y, x) ==> in(z, y)), in(y, x)) |- in(z, union(x))) by Cut(lastStep, unionIntro)
    thenHave((∀(y, in(y, x) ==> in(z, y)), exists(y, in(y, x))) |- in(z, union(x))) by LeftExists
    have((∀(y, in(y, x) ==> in(z, y)), !(x === emptySet)) |- in(z, union(x))) by Cut(nonEmptySetHasAnElement, lastStep)
    val assumption = thenHave(!(x === emptySet) |- ∀(y, in(y, x) ==> in(z, y)) ==> in(z, union(x))) by RightImplies
    
    have(∀(z, in(z, intersection(x)) <=> (in(z, union(x)) /\ ∀(y, in(y, x) ==> in(z, y))))) by InstantiateForall(intersection(x))(intersection.definition)
    thenHave(in(z, intersection(x)) <=> (in(z, union(x)) /\ ∀(y, in(y, x) ==> in(z, y)))) by InstantiateForall(z)
    thenHave(∀(y, in(y, x) ==> in(z, y)) ==> in(z, union(x)) |- in(z, intersection(x)) <=> ∀(y, in(y, x) ==> in(z, y))) by Tautology
    have(thesis) by Cut(assumption, lastStep)
  }

  /**
   * Lemma --- Intersection introduction rule
   *
   *    `x ≠ ∅, ∀ y ∈ x. z ∈ y ⊢ z ∈ ∩ x`
   */
  val intersectionIntro = Lemma(
    (!(x === emptySet), ∀(y, in(y, x) ==> in(z, y))) |- in(z, intersection(x))
  ) {
    have(thesis) by Weakening(intersectionMembership)
  }

  /**
   * Lemma --- Intersection elimination rule
   *
   *    `x ≠ ∅, z ∈ ∩ x, y ∈ x ⊢ z ∈ y`
   */
  val intersectionElim = Lemma(
    (!(x === emptySet), in(z, intersection(x)), in(y, x)) |- in(z, y)
  ) {
    have((!(x === emptySet), in(z, intersection(x))) |- ∀(y, in(y, x) ==> in(z, y))) by Weakening(intersectionMembership) 
    thenHave(thesis) by InstantiateForall(y)
  }


  /**
   * Lemma --- Intersection of a non-empty Class is a Set
   *
   * There exists a set that is the intersection of all sets satisfying a given
   * formula. With classes, this means that the unary intersection of a class
   * defined by a predicate is a set.
   *
   *    `∃ x. P(x) ⊢ ∃ z. t ∈ z ⇔ ∀ x. P(x) ⇒ t ∈ x`
   */
  val intersectionOfPredicateClassExists = Lemma(
    ∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, P(y) ==> in(t, y))))
  ) {

    val hyp = have(∀(y, P(y) ==> in(t, y)) |- ∀(y, P(y) ==> in(t, y))) by Hypothesis
    thenHave((∀(y, P(y) ==> in(t, y)), P(x)) |- in(t, x)) by InstantiateForall(x)
    have((∀(y, P(y) ==> in(t, y)), P(x)) |- in(t, x) /\ ∀(y, P(y) ==> in(t, y))) by RightAnd(lastStep, hyp)
    val forward = thenHave(P(x) |- ∀(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightImplies

    val backward = thenHave((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) ==> (∀(y, P(y) ==> in(t, y)))) by Weakening

    val lhs = have(P(x) |- ∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightIff(forward, backward)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = thenHave(
      Set((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))), (∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (∀(y, P(y) ==> in(t, y))))
    ) by RightSubstIff.withParametersSimple(List((∀(y, P(y) ==> in(t, y)), (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have((P(x), (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by LeftForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y))))) by RightForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by RightExists
    val cutRhs = thenHave((P(x), ∃(z, ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by Cut(comprehensionSchema of (z := x, φ := lambda(t, ∀(y, P(y) ==> in(t, y)))), cutRhs)
    thenHave(∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

  }


  /**
   * Binary intersection
   */

  /**
   * Definition --- Binary Set Intersection
   *
   *     `x ∩ y = ∩ {x, y}`
   */
  val setIntersection = DEF(x, y) --> intersection(unorderedPair(x, y))

  extension (x: Term) {
    infix def ∩(y: Term) = setIntersection(x, y)
  }

  /**
   * Lemma --- Binary Intersection Membership
   *
   *    `z ∈ x ∩ y <=> z ∈ x ∧ z ∈ y`
   */
  val setIntersectionMembership = Lemma(
    in(z, setIntersection(x, y)) <=> (in(z, x) /\ in(z, y))
  ) {
    val forward = have(∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)) ==> (in(z, x) /\ in(z, y))) subproof {
      have(∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)) |- ∀(w, in(w, unorderedPair(x, y)) ==> in(z, w))) by Hypothesis
      val seq = thenHave((∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)), in(w, unorderedPair(x, y))) |- in(z, w)) by InstantiateForall(w)

      have((∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)), in(x, unorderedPair(x, y)), in(y, unorderedPair(x, y))) |- in(z, x) /\ in(z, y)) by RightAnd(seq of (w := x), seq of (w := y))
      have((∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)), in(x, unorderedPair(x, y))) |- in(z, x) /\ in(z, y)) by Cut(unorderedPairRightIntro, lastStep)
      have(∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)) |- in(z, x) /\ in(z, y)) by Cut(unorderedPairLeftIntro, lastStep)
    }

    val backward = have((in(z, x) /\ in(z, y)) ==> ∀(w, in(w, unorderedPair(x, y)) ==> in(z, w))) subproof {
      have(in(z, x) |- in(z, x)) by Hypothesis
      val seq = thenHave((in(z, x), x === w) |- in(z, w)) by RightSubstEq.withParametersSimple(List((x, w)), lambda(w, in(z, w)))

      have((in(z, x), in(w, unorderedPair(x, y))) |- (in(z, w), w === y)) by Cut(unorderedPairElim of (z := w), seq)
      have((in(z, x), in(z, y), in(w, unorderedPair(x, y))) |- in(z, w)) by Cut(lastStep, seq of (x := y))
      thenHave((in(z, x), in(z, y)) |- in(w, unorderedPair(x, y)) ==> in(z, w)) by RightImplies
      thenHave((in(z, x), in(z, y)) |- ∀(w, in(w, unorderedPair(x, y)) ==> in(z, w))) by RightForall
    }

    have(∀(w, in(w, unorderedPair(x, y)) ==> in(z, w)) <=> (in(z, x) /\ in(z, y))) by RightIff(forward, backward)
    thenHave(!(unorderedPair(x, y) === emptySet) |- in(z, intersection(unorderedPair(x, y))) <=> (in(z, x) /\ in(z, y))) by Substitution.ApplyRules(intersectionMembership)
    have(in(z, intersection(unorderedPair(x, y))) <=> (in(z, x) /\ in(z, y))) by Cut(unorderedPairNonEmpty, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(setIntersection.shortDefinition)
  }

  /**
   * Lemma --- Binary Intersection Introduction Rule
   *
   *    `z ∈ x, z ∈ y ⊢ z ∈ x ∩ y`
   */
  val setIntersectionIntro = Lemma(
    (in(z, x), in(z, y)) |- in(z, setIntersection(x, y))
  ) {
    have(thesis) by Weakening(setIntersectionMembership)
  }

  /**
   * Lemma --- Binary Intersection Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ x /\ z ∈ y`
   */
  val setIntersectionElim = Lemma(
    in(z, setIntersection(x, y)) |- in(z, x) /\ in(z, y)
  ) {
    have(thesis) by Weakening(setIntersectionMembership)
  }

  /**
   * Lemma --- Binary Intersection Left Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ x`
   */
  val setIntersectionLeftElim = Lemma(
    in(z, setIntersection(x, y)) |- in(z, x)
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  /**
   * Lemma --- Binary Intersection Right Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ y`
   */
  val setIntersectionRightElim = Lemma(
    in(z, setIntersection(x, y)) |- in(z, y)
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  /**
   * Lemma --- Binary Intersection Commutativity
   *
   *    `x ∩ y = y ∩ x`
   */
  val setIntersectionCommutativity = Lemma(
    setIntersection(x, y) === setIntersection(y, x)
  ) {
    have(in(z, setIntersection(x, y)) <=> in(z, setIntersection(y, x))) by Substitution.ApplyRules(setIntersectionMembership)(setIntersectionMembership)
    thenHave(forall(z, in(z, setIntersection(x, y)) <=> in(z, setIntersection(y, x)))) by RightForall
    have(setIntersection(x, y) === setIntersection(y, x)) by Cut(lastStep, equalityIntro of (x := setIntersection(x, y), y := setIntersection(y, x)))
  }

  /**
   * Lemma --- Binary Intersection Left Subset
   * 
   *   `x ∩ y ⊆ x`
   */
  val setIntersectionLeftSubset = Lemma(
    subset(setIntersection(x, y), x)
  ) {
    have(in(z, setIntersection(x, y)) ==> in(z, x)) by RightImplies(setIntersectionLeftElim)
    thenHave(forall(z, in(z, setIntersection(x, y)) ==> in(z, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(x, y), y := x))
  }

  /**
   * Lemma --- Binary Intersection Right Subset
   * 
   *   `x ∩ y ⊆ y`
   */
  val setIntersectionRightSubset = Lemma(
    subset(setIntersection(x, y), y)
  ) {
    have(in(z, setIntersection(x, y)) ==> in(z, y)) by RightImplies(setIntersectionRightElim)
    thenHave(forall(z, in(z, setIntersection(x, y)) ==> in(z, y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(x, y), y := y))
  }

  /**
   * Lemma --- Intersection with a subset
   * 
   *   `x ⊆ y ⊢ x ∩ y = x`
   */
  val setIntersectionOfSubsetForward = Lemma(
    subset(x, y) |- setIntersection(x, y) === x
  ) {
    have((in(z, x), subset(x, y)) |- in(z, setIntersection(x, y))) by Cut(subsetElim, setIntersectionIntro)
    thenHave(subset(x, y) |- in(z, x) ==> in(z, setIntersection(x, y))) by RightImplies
    thenHave(subset(x, y) |- forall(z, in(z, x) ==> in(z, setIntersection(x, y)))) by RightForall
    have(subset(x, y) |- subset(x, setIntersection(x, y))) by Cut(lastStep, subsetIntro of (y := setIntersection(x, y)))
    have((subset(x, y), subset(setIntersection(x, y), x)) |- x === setIntersection(x, y)) by Cut(lastStep, subsetAntisymmetry of (y := setIntersection(x, y)))
    have(thesis) by Cut(setIntersectionLeftSubset, lastStep)
  }

  /**
   * Lemma --- Intersection with a subset
   * 
   *   `y ⊆ x ⊢ x ∩ y = y`
   */
  val setIntersectionOfSubsetBackward = Lemma(
    subset(y, x) |- setIntersection(x, y) === y
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionCommutativity)(setIntersectionOfSubsetForward of (x := y, y := x))
  }

  /**
   * Definition --- Disjoint Sets
   * 
   *   `disjoint(x, y) <=> x ∩ y = ∅`
   */
  val disjoint = DEF(x, y) --> (setIntersection(x, y) === emptySet)

  /**
   * Lemma --- Disjoint definition unfolding
   * 
   *  `disjoint(x, y) ⊢ x ∩ y = ∅`
   */
  val disjointUnfold = Lemma(
    disjoint(x, y) |- setIntersection(x, y) === emptySet
  ) {
    have(thesis) by Weakening(disjoint.definition)
  }

  /**
   * Lemma --- Disjoint definition folding
   * 
   *  `x ∩ y = ∅ ⊢ disjoint(x, y)`
   */
  val disjointFold = Lemma(
    setIntersection(x, y) === emptySet |- disjoint(x, y)
  ) {
    have(thesis) by Weakening(disjoint.definition)
  }

  /**
   * Lemma --- Disjoint Elimination Rule
   * 
   *  `disjoint(x, y), z ∈ x, z ∈ y ⊢ ⊥`
   */
  val disjointElim = Lemma(
    (disjoint(x, y), in(z, x), in(z, y)) |- ()
  ) {
    have((setIntersection(x, y) === emptySet, in(z, setIntersection(x, y))) |- ()) by Restate.from(setEmptyHasNoElements of (x := setIntersection(x, y), y := z))
    have((setIntersection(x, y) === emptySet, in(z, x), in(z, y)) |- ()) by Cut(setIntersectionIntro of (x := x, y := y), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(disjoint.definition)
  }

  /**
   * Lemma --- Non Disjointn Elimination Rule
   * 
   * `¬disjoint(x, y) ⊢ ∃ z. z ∈ x ∧ z ∈ y`
   */
  val nonDisjointElim = Lemma(
    !disjoint(x, y) |- exists(z, in(z, x) /\ in(z, y))
  ) {
    have(in(z, setIntersection(x, y)) |- exists(z, in(z, x) /\ in(z, y))) by RightExists(setIntersectionElim) 
    thenHave(exists(z, in(z, setIntersection(x, y))) |- exists(z, in(z, x) /\ in(z, y))) by LeftExists
    have(!(setIntersection(x, y) === emptySet) |- exists(z, in(z, x) /\ in(z, y))) by Cut(nonEmptySetHasAnElement of (x := setIntersection(x, y)), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(disjoint.definition)
  }

  /**
   * Lemma --- Disjoint Symmetry
   * 
   *    `disjoint(x, y) <=> disjoint(y, x)`
   */
  val disjointSymmetry = Lemma(
    disjoint(x, y) <=> disjoint(y, x)
  ) {
    have((setIntersection(x, y) === emptySet) <=> (setIntersection(x, y) === emptySet)) by Restate
    thenHave((setIntersection(x, y) === emptySet) <=> (setIntersection(y, x) === emptySet)) by Substitution.ApplyRules(setIntersectionCommutativity)
    thenHave(thesis) by Substitution.ApplyRules(disjoint.definition, disjoint.definition of (x := y, y := x))
  }

  val nonDisjointSingleton = Lemma(
    !disjoint(y, singleton(x)) |- in(x, y)
  ) {
    have(in(z, y) |- in(z, y)) by Hypothesis
    thenHave((in(z, singleton(x)), in(z, y)) |- in(x, y)) by Substitution.ApplyRules(singletonElim of (y := z))
    thenHave(in(z, singleton(x)) /\ in(z, y) |- in(x, y)) by LeftAnd
    thenHave(exists(z, in(z, singleton(x)) /\ in(z, y)) |- in(x, y)) by LeftExists
    have(thesis) by Cut(nonDisjointElim of (x := y, y := singleton(x)), lastStep)
  }


  /**
   * Lemma --- Set Difference Uniqueness
   * 
   *   `∃! z. ∀ t. t ∈ z <=> (t ∈ x ∧ ! t ∈ y)`
   */
  val setDifferenceUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))) by UniqueComprehension(x, lambda(t, !in(t, y)))
  }

  /**
   * Binary Set Difference --- Given two sets, produces the set that contains
   * elements in the first but not in the second.
   *
   *    `x - y = {z ∈ x | ! z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setDifference = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ !in(t, y))))(setDifferenceUniqueness)


  /**
   * Ordered Pair --- `(x, y)`. Shorthand for `{{x}, {x, y}}`.
   *
   * @param x set
   * @param y set
   */
  val pair: ConstantFunctionLabel[2] = DEF(x, y) --> unorderedPair(unorderedPair(x, y), singleton(x))

  /**
   * Lemma --- Pair Extensionality
   *
   * Two ordered pairs are equal iff their elements are equal when taken in order.
   *
   *  `pair(a, b) = pair(c, d) <=> a = c ∧ b = d`
   */
  val pairExtensionality = Lemma(
    (pair(a, b) === pair(c, d)) <=> ((a === c) /\ (b === d))
  ) {
    have(
      (pair(a, b) === pair(c, d)) <=>
        (((((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))) /\ (a === c)) \/ (((a === c) /\ (b === c)) /\ ((a === c) /\ (a === d))))
    ) by
      Substitution.ApplyRules(
        singletonExtensionality of (x := a, y := c),
        singletonEqualsUnorderedPair of (x := c, y := a, z := b),
        singletonEqualsUnorderedPair of (x := a, y := c, z := d),
        unorderedPairExtensionality,
        pair.shortDefinition of (x := a, y := b),
        pair.shortDefinition of (x := c, y := d)
      )(unorderedPairExtensionality of (a := unorderedPair(a, b), b := singleton(a), c := unorderedPair(c, d), d := singleton(c)))

    val equiv = thenHave((pair(a, b) === pair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === c) /\ (b === c) /\ (a === d)))) by Tautology

    val right = have((b === c, c === a, a === d) |- b === d) by Cut(equalityTransitivity of (x := b, y := c, z := a), equalityTransitivity of (x := b, y := a, z := d))
    val left = have(a === c |- a === c) by Hypothesis
    have((a === c, b === c, a === d) |- (a === c) /\ (b === d)) by RightAnd(left, right)
    val right2 = thenHave((a === c) /\ (b === c) /\ (a === d) |- (a === c) /\ (b === d)) by Restate
    val left2 = have((a === c) /\ (b === d) |- (a === c) /\ (b === d)) by Hypothesis
    have(((a === c) /\ (b === d)) \/ ((a === c) /\ (b === c) /\ (a === d)) |- (a === c) /\ (b === d)) by LeftOr(left2, right2)
    thenHave(pair(a, b) === pair(c, d) |- (a === c) /\ (b === d)) by Substitution.ApplyRules(equiv)

    val forward = thenHave((pair(a, b) === pair(c, d)) ==> ((a === c) /\ (b === d))) by RightImplies
    val backward = have(((a === c) /\ (b === d)) ==> (pair(a, b) === pair(c, d))) by Weakening(equiv)
    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Lemma --- The union of an ordered pair is the corresponding unordered pair.
   *
   *    `∪ (x, y) = ∪ {{x}, {x, y}} = {x, y}`
   */
  val unionOfOrderedPair = Lemma(
    union(pair(x, y)) === unorderedPair(x, y)
  ) {
    val forward = have(in(z, union(pair(x, y))) ==> in(z, unorderedPair(x, y))) subproof {

      val left = have(in(z, unorderedPair(x, y)) |- in(z, unorderedPair(x, y))) by Hypothesis
      val right = have(in(z, singleton(x)) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(singletonElim)(unorderedPairLeftIntro)
      have(in(z, setUnion(unorderedPair(x, y), singleton(x))) |- (in(z, unorderedPair(x, y)), in(z, singleton(x)))) by Cut(setUnionElim of (x := unorderedPair(x, y), y := singleton(x)), left)
      have(in(z, setUnion(unorderedPair(x, y), singleton(x))) |- in(z, unorderedPair(x, y))) by Cut(lastStep, right)
      thenHave(in(z, union(unorderedPair(unorderedPair(x, y), singleton(x)))) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(setUnion.shortDefinition)
      thenHave(in(z, union(pair(x, y))) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(pair.shortDefinition)
    }

    val backward = have(in(z, unorderedPair(x, y)) ==> in(z, union(pair(x, y)))) subproof {
      have(in(z, unorderedPair(x, y)) |- in(z, union(unorderedPair(unorderedPair(x, y), singleton(x))))) by Substitution.ApplyRules(setUnion.shortDefinition)(setUnionLeftIntro of (x := unorderedPair(x, y), y := singleton(x)))
      thenHave(in(z, unorderedPair(x, y)) |- in(z, union(pair(x, y))) ) by Substitution.ApplyRules(pair.shortDefinition)
    }

    have(in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y))) by RightIff(forward, backward)
    thenHave(forall(z, in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(pair(x, y)), y := unorderedPair(x, y)))
  }

  val pairComponentsInUnionUnion = Lemma(
    in(pair(x, y), r) |- in(x, union(union(r))) /\ in(y, union(union(r)))
  ) {
    have(in(unorderedPair(unorderedPair(x, y), singleton(x)), r) |- in(unorderedPair(x, y), union(r))) by Weakening(unorderedPairElementsInUnion of (x := unorderedPair(x, y), y := singleton(x)))
    have(in(unorderedPair(unorderedPair(x, y), singleton(x)), r) |- in(x, union(union(r))) /\ in(y, union(union(r))) ) by Cut(lastStep, unorderedPairElementsInUnion of (r := union(r)))
    thenHave(thesis) by Substitution.ApplyRules(pair.shortDefinition)
  }

  /**
   * Lemma --- The unary intersection of an ordered pair is the singleton
   * containing the first element.
   *
   *    `∩ (x, y) = ∩ {{x}, {x, y}} = {x}`
   */
  val pairIntersection = Lemma(
    intersection(pair(x, y)) === singleton(x)
  ) {
    have(subset(singleton(x), unorderedPair(x, y))) by Substitution.ApplyRules(singletonSubset)(unorderedPairLeftIntro)
    have(setIntersection(unorderedPair(x, y), singleton(x)) === singleton(x)) by Cut(lastStep, setIntersectionOfSubsetBackward of (x := unorderedPair(x, y), y := singleton(x)))
    thenHave(intersection(unorderedPair(unorderedPair(x, y), singleton(x))) === singleton(x)) by Substitution.ApplyRules(setIntersection.shortDefinition)
    thenHave(intersection(pair(x, y)) === singleton(x)) by Substitution.ApplyRules(pair.shortDefinition) 
  }

  val foundation = Lemma(
    !(x === emptySet) |- ∃(y, in(y, x) /\ ∀(z, in(z, x) ==> !in(z, y)))
  ) {
    have(thesis) by Restate.from(foundationAxiom)
  }

  /**
   * Lemma --- No set is an element of itself.
   *
   *    `x ∉ x`
   *
   * This is imposed by the Foundation Axiom ([[foundationAxiom]]).
   */
  val selfNonMembership = Lemma(
    !in(x, x)
  ) {
    val foundation = have(!(singleton(x) === ∅) |- ∃(y, in(y, singleton(x)) /\ ∀(z, in(z, singleton(x)) ==> !in(z, y)))) by Restate.from(foundationAxiom of (x := singleton(x)))
    have((in(x, singleton(x)) ==> !in(x, y), in(x, singleton(x)), in(x, y)) |- ()) by Restate
    have((in(x, singleton(x)) ==> !in(x, y), in(x, y)) |- ()) by Cut(singletonIntro, lastStep)
    thenHave((x === y, in(x, singleton(x)) ==> !in(x, y), in(x, x)) |- ()) by LeftSubstEq.withParametersSimple(List((x, y)), lambda(y, in(x, y)))
    have((in(y, singleton(x)), in(x, singleton(x)) ==> !in(x, y), in(x, x)) |- ()) by Cut(singletonElim, lastStep)
    thenHave((in(y, singleton(x)), forall(z, in(z, singleton(x)) ==> !in(z, y)), in(x, x)) |- ()) by LeftForall
    thenHave((in(y, singleton(x)), forall(z, in(z, singleton(x)) ==> !in(z, y))) |- !in(x, x)) by RightNot
    thenHave(in(y, singleton(x)) /\ forall(z, in(z, singleton(x)) ==> !in(z, y)) |- !in(x, x)) by LeftAnd
    thenHave(∃(y, in(y, singleton(x)) /\ forall(z, in(z, singleton(x)) ==> !in(z, y))) |- !in(x, x)) by LeftExists
    have(!(singleton(x) === ∅) |- !in(x, x)) by Cut(foundation, lastStep)
    have(thesis) by Cut(singletonNonEmpty, lastStep)
  }

  /**
   * Lemma --- No Universal Set
   *
   *    `∀ z. z ∈ x ⊢ ⊥`
   *
   * There does not exist a set of all sets. Alternatively, its existence, with
   * the [[comprehensionSchema]] and Russel's paradox ([[russelsParadox]]), produces
   * a contradiction.
   */
  val noUniversalSet = Lemma(
    ∀(z, in(z, x)) |- ()
  ) {
    have(exists(z, !in(z, x))) by RightExists(selfNonMembership)
  }

  /**
    * Lemma --- The membership relation is asymmetric.
    * 
    *   `x ∈ y, y ∈ x ⊢ ⊥`
    */
  val membershipAsymmetry = Lemma(
    (in(x, y), in(y, x)) |- ()
  ) {
    val u = unorderedPair(x, y)

    val minimal = have(exists(w, in(w, u) /\ forall(z, in(z, u) ==> !in(z, w)))) by Cut(unorderedPairNonEmpty, foundation of (x := u))

    have(in(y, x) |- in(y, x)) by Hypothesis
    have(in(y, x) |- in(y, u) /\ in(y, x)) by RightAnd(lastStep, unorderedPairRightIntro) 
    thenHave((in(y, x), z === x) |- in(y, u) /\ in(y, z)) by RightSubstEq.withParametersSimple(List((z, x)), lambda(z, in(y, u) /\ in(y, z)))
    val left = thenHave((in(y, x), z === x) |- exists(w, in(w, u) /\ in(w, z))) by RightExists

    have(in(x, y) |- in(x, y)) by Hypothesis
    have(in(x, y) |- in(x, u) /\ in(x, y)) by RightAnd(lastStep, unorderedPairLeftIntro) 
    thenHave((in(x, y), z === y) |- in(x, u) /\ in(x, z)) by RightSubstEq.withParametersSimple(List((z, y)), lambda(z, in(x, u) /\ in(x, z)))
    val right = thenHave((in(x, y), z === y) |- exists(w, in(w, u) /\ in(w, z))) by RightExists

    have((in(y, x), in(z, u)) |- (exists(w, in(w, u) /\ in(w, z)), z === y)) by Cut(unorderedPairElim, left)
    have((in(x, y), in(y, x), in(z, u)) |- exists(w, in(w, u) /\ in(w, z))) by Cut(lastStep, right) 
    thenHave((in(x, y), in(y, x)) |- in(z, u) ==> exists(w, in(w, u) /\ in(w, z))) by RightImplies
    thenHave((in(x, y), in(y, x)) |- forall(z, in(z, u) ==> exists(w, in(w, u) /\ in(w, z))) ) by RightForall
    have(thesis) by RightAnd(lastStep, minimal)
  }

  val pairInPowerPowerSet = Lemma(
    in(pair(x, y), powerSet(powerSet(z))) <=> (in(x, z) /\ in(y, z)) 
  ) {
    have((in(x, z) /\ in(x, z) /\ in(y, z)) <=> (in(x, z) /\ in(y, z))) by Restate
    thenHave((in(x, z) <=> in(singleton(x), powerSet(z)), (in(x, z) /\ in(y, z)) <=> in(unorderedPair(x, y), powerSet(z))) |- (in(singleton(x), powerSet(z)) /\ in(unorderedPair(x, y), powerSet(z))) <=> (in(x, z) /\ in(y, z))) by RightSubstIff.withParametersSimple(
      List((in(x, z), in(singleton(x), powerSet(z))), (in(x, z) /\ in(y, z), in(unorderedPair(x, y), powerSet(z)))), lambda((h, q), (h /\ q) <=> (in(x, z) /\ in(y, z)))
    )
    have(in(x, z) <=> in(singleton(x), powerSet(z)) |- (in(singleton(x), powerSet(z)) /\ in(unorderedPair(x, y), powerSet(z))) <=> (in(x, z) /\ in(y, z))) by Cut(unorderedPairInPowerSet, lastStep)
    have((in(singleton(x), powerSet(z)) /\ in(unorderedPair(x, y), powerSet(z))) <=> (in(x, z) /\ in(y, z))) by Cut(singletonInPowerSet of (y := z), lastStep)
    thenHave(in(unorderedPair(unorderedPair(x, y), singleton(x)), powerSet(powerSet(z))) <=> (in(x, z) /\ in(y, z))) by Substitution.ApplyRules(unorderedPairInPowerSet of (x := unorderedPair(x, y), y := singleton(x), z := powerSet(z)))
    thenHave(thesis) by Substitution.ApplyRules(pair.shortDefinition)
  }

  /**
   * Lemma --- Any set is disjoint with its singleton
   * 
   *  `disjoint(x,  {x})`
   */
  val singletonDisjointSelf = Lemma(
    disjoint(x, singleton(x))
  ) {
    have(!disjoint(x, singleton(x)) |- ()) by RightAnd(nonDisjointSingleton of (y := x), selfNonMembership)
  }

  /**
   * The first element of an ordered [[pair]] --- `first p = ∪ ∩ p`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `∩ p = {a}`, and `∪ ∩ p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[firstInPairReduction]].
   */
  val firstInPair = DEF(p) --> union(intersection(p))

  /**
   * Lemma --- The [[firstInPair]] operation when applied to an ordered pair
   * produces the first element of the pair.
   *
   *    `first((x, y)) = x`
   */
  val firstInPairReduction = Lemma(
    (firstInPair(pair(x, y)) === x)
  ) {
    have(union(intersection(pair(x, y))) === x) by Substitution.ApplyRules(pairIntersection)(unionSingleton)
    thenHave(thesis) by Substitution.ApplyRules(firstInPair.shortDefinition)
  }

  val secondInPairSingletonUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === intersection(p))) ==> (!in(t, intersection(p)))))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(t, ((!(union(p) === intersection(p))) ==> (!in(t, intersection(p))))))
  }

  /**
   * See [[secondInPair]].
   */
  val secondInPairSingleton =
    DEF(p) --> The(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ (in(t, intersection(p)) ==> (union(p) === intersection(p))))))(secondInPairSingletonUniqueness)

  /**
   * The second element of an ordered [[pair]] ---
   *
   *    `second p = ∪ {x ∈ ∪ p | ∪ p != ∩ p ⟹ !x ∈ ∩ p} = ∪ (secondSingleton p)`
   *
   * There is a more naive definition: `second p = ∪ (∪ p - (first p))`.
   * If `p = (a, b) = {{a}, {a, b}}`, `∪ p = {a, b}`, and `∪ p - (first p)
   * = {a, b} - {a} = {b}`, the `∪` at the top level reduces this to `b`.
   * However, this fails when `a = b`, and returns the [[emptySet]].
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[secondInPairReduction]].
   *
   * @see https://en.wikipedia.org/wiki/Ordered_pair#Kuratowski's_definition
   */
  val secondInPair = DEF(p) --> union(secondInPairSingleton(p))


  /**
   * Lemma --- The [[secondInPairSingleton]] operation when applied to an
   * ordered pair produces the singleton containing the second element of the pair.
   *
   *    `secondSingleton((x, y)) = {y}`
   *
   * Used for [[secondInPair]] reduction.
   */
  val secondInPairSingletonReduction = Lemma(
    secondInPairSingleton(pair(x, y)) === singleton(y)
  ) {
    have(
      forall(
        t,
        in(t, secondInPairSingleton(pair(x, y))) <=> (in(t, union(pair(x, y))) /\ (in(t, intersection(pair(x, y))) ==> (union(pair(x, y)) === intersection(pair(x, y)))))
      )
    ) by InstantiateForall(secondInPairSingleton(pair(x, y)))(secondInPairSingleton.definition of (p := pair(x, y)))
    thenHave(
      in(z, secondInPairSingleton(pair(x, y))) <=> (in(z, union(pair(x, y))) /\ (in(z, intersection(pair(x, y))) ==> (union(pair(x, y)) === intersection(pair(x, y)))))
    ) by InstantiateForall(z)
    thenHave(
      in(z, secondInPairSingleton(pair(x, y))) <=> (in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (unorderedPair(x, y) === singleton(x))))
    ) by Substitution.ApplyRules(unionOfOrderedPair, pairIntersection)
    val iff = thenHave(
      in(z, secondInPairSingleton(pair(x, y))) <=> (in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (x === y)))
    ) by Substitution.ApplyRules(singletonEqualsUnorderedPair of (y := x, z := y))

    val forward = have((in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (x === y))) ==> in(z, singleton(y))) subproof {
      have((in(z, singleton(x)) ==> (x === y), in(z, singleton(x))) |- x === y) by Restate
      thenHave((in(z, singleton(x)) ==> (x === y), z === x, in(x, singleton(x))) |- x === y) by LeftSubstEq.withParametersSimple(List((z, x)), lambda(z, in(z, singleton(x))))
      have((in(z, singleton(x)) ==> (x === y), z === x) |- x === y) by Cut(singletonIntro, lastStep)
      have((in(z, singleton(x)) ==> (x === y), z === x) |- z === y) by Cut(lastStep, equalityTransitivity of (x := z, y := x, z := y))
      have((in(z, singleton(x)) ==> (x === y), in(z, unorderedPair(x, y))) |- z === y) by Cut(unorderedPairElim, lastStep)
      thenHave((in(z, singleton(x)) ==> (x === y), in(z, unorderedPair(x, y))) |- in(z, singleton(y))) by Substitution.ApplyRules(singletonMembership of (y := z, x := y))
    }
    val backward = have(in(z, singleton(y)) ==> (in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (x === y)))) subproof {
      val left = have(in(z, singleton(y)) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(singletonElim)(unorderedPairRightIntro)

      have((in(z, singleton(x)), in(z, singleton(y))) |- x === y) by Substitution.ApplyRules(singletonElim of (y := z, x := y))(singletonElim of (y := z))
      val right = thenHave(in(z, singleton(y)) |- in(z, singleton(x)) ==> (x === y)) by RightImplies

      have(in(z, singleton(y)) |- in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (x === y))) by RightAnd(left, right)
    }

    have((in(z, unorderedPair(x, y)) /\ (in(z, singleton(x)) ==> (x === y))) <=> in(z, singleton(y))) by RightIff(forward, backward)
    thenHave(in(z, secondInPairSingleton(pair(x, y))) <=> in(z, singleton(y))) by Substitution.ApplyRules(iff)
    thenHave(forall(z, in(z, secondInPairSingleton(pair(x, y))) <=> in(z, singleton(y)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := secondInPairSingleton(pair(x, y)), y := singleton(y)))
  }

  /**
   * Lemma --- The [[secondInPair]] operation when applied to an ordered pair
   * produces the second element of the pair.
   *
   *    `second((x, y)) = y`
   */
  val secondInPairReduction = Lemma(
    secondInPair(pair(x, y)) === y
  ) {
    have(union(secondInPairSingleton(pair(x, y))) === y) by Substitution.ApplyRules(secondInPairSingletonReduction)(unionSingleton of (x := y))
    thenHave(thesis) by Substitution.ApplyRules(secondInPair.shortDefinition)
  }

  /**
   * Lemma --- Pair Reconstruction
   *
   * If `x` is a pair (i.e. `= (c, d)` for some `c` and `d`), then pair element
   * projection on it is invertible, so `x = (fst x, snd x)`.
   */
  val pairReconstruction = Lemma(
    exists(y, exists(z, pair(y, z) === x)) |- x === pair(firstInPair(x), secondInPair(x))
  ) {
    val left = have(pair(y, z) === x |- firstInPair(x) === y) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(x, firstInPair(x) === y))(firstInPairReduction of (x := y, y := z))
    val right = have(pair(y, z) === x |- secondInPair(x) === z) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(x, secondInPair(x) === z))(secondInPairReduction of (x := y, y := z))
    have(pair(y, z) === x |- (firstInPair(x) === y) /\ (secondInPair(x) === z)) by RightAnd(left, right)
    thenHave(pair(y, z) === x |- pair(y, z) === pair(firstInPair(x), secondInPair(x))) by Substitution.ApplyRules(pairExtensionality of (a := y, b := z, c := firstInPair(x), d := secondInPair(x)))
    thenHave(pair(y, z) === x |- x === pair(firstInPair(x), secondInPair(x))) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(z, z === pair(firstInPair(x), secondInPair(x))))
    thenHave(exists(z, pair(y, z) === x) |- x === pair(firstInPair(x), secondInPair(x))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Cartesian Product
   */

  val cartesianProductUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))) by UniqueComprehension(
      powerSet(powerSet(setUnion(x, y))),
      lambda(t, ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
    )
  }

  /**
   * Cartesian Product --- Given two sets `x` and `y`, their cartesian product
   * is the set containing pairs with the first element in `x` and the second
   * in `y`. The cartesian product can be seen as a comprehension on the set
   * `PP(x ∪ y)`.
   *
   *     `x * y = {z ∈ PP(x ∪ y) | ∃ a ∈ x, b ∈ y. z = (a, b)}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val cartesianProduct =
    DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))))(cartesianProductUniqueness)


  val elemOfPowerPowerUnion = Lemma(
    ∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y))) |- in(p, powerSet(powerSet(setUnion(x, y))))
  ) {
    have((in(a, setUnion(x, y)), in(b, setUnion(x, y))) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y))))) by Weakening(pairInPowerPowerSet of (x := a, y := b, z := setUnion(x, y)))
    have((in(a, x), in(b, setUnion(x, y))) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y))))) by Cut(setUnionLeftIntro of (z := a), lastStep)
    have((in(a, x), in(b, y)) |- in(pair(a, b), powerSet(powerSet(setUnion(x, y))))) by Cut(setUnionRightIntro of (z := b), lastStep)
    thenHave((p === pair(a, b), in(a, x), in(b, y)) |- in(p, powerSet(powerSet(setUnion(x, y))))) by RightSubstEq.withParametersSimple(List((p, pair(a, b))), lambda(p, in(p, powerSet(powerSet(setUnion(x, y))))))
    thenHave((p === pair(a, b)) /\ in(a, x) /\ in(b, y) |- in(p, powerSet(powerSet(setUnion(x, y))))) by Restate
    thenHave(∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- in(p, powerSet(powerSet(setUnion(x, y))))) by LeftExists
    thenHave(thesis) by LeftExists
  }


  /**
   * Lemma --- a set is an element of a Cartesian product iff it is a pair containing
   * elements from the constituents of the product.
   *
   *    `p ∈ x * y <=> ∃ a, b. p = (a, b) ∧ a ∈ x ∧ b ∈ y`
   *
   * Asserts a stronger definition of the [[cartesianProduct]]. See
   * [[elemOfPowerPowerUnion]] for the redundancy proof.
   */
  val elemOfCartesianProduct = Lemma(
    in(p, cartesianProduct(x, y)) <=> ∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)))
  ) {
    val powerPowerSet = have(∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y))) ==> in(p, powerSet(powerSet(setUnion(x, y))))) by RightImplies(elemOfPowerPowerUnion)

    have(forall(p, in(p, cartesianProduct(x, y)) <=> (in(p, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)))))) by InstantiateForall(
      cartesianProduct(x, y)
    )(cartesianProduct.definition)
    thenHave(in(p, cartesianProduct(x, y)) <=> (in(p, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y))))) by InstantiateForall(p)
    thenHave(∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y))) ==> in(p, powerSet(powerSet(setUnion(x, y)))) |- in(p, cartesianProduct(x, y)) <=> ∃(a, ∃(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)))) by Tautology
    have(thesis) by Cut(powerPowerSet, lastStep)
  }

  val pairReconstructionInCartesianProduct = Lemma(
    in(p, cartesianProduct(x, y)) |- p === pair(firstInPair(p), secondInPair(p))
  ) {
    have((p === pair(a, b)) /\ in(a, x) /\ in(b, y) |- p === pair(a, b)) by Restate
    thenHave((p === pair(a, b)) /\ in(a, x) /\ in(b, y) |- exists(b, p === pair(a, b))) by RightExists
    thenHave(exists(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- exists(b, p === pair(a, b))) by LeftExists
    thenHave(exists(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- exists(a, exists(b, p === pair(a, b)))) by RightExists
    thenHave(exists(a, exists(b, (p === pair(a, b)) /\ in(a, x) /\ in(b, y))) |- exists(a, exists(b, p === pair(a, b)))) by LeftExists
    thenHave(in(p, cartesianProduct(x, y)) |- exists(a, exists(b, p === pair(a, b)))) by Substitution.ApplyRules(elemOfCartesianProduct)
    have(thesis) by Cut(lastStep, pairReconstruction of (x := p))
  }

  val cartesianProductIntro = Lemma(
    (in(a, x), in(b, y)) |- in(pair(a, b), cartesianProduct(x, y))
  ) {
    have((in(a, x), in(b, y)) |- (pair(a, b) === pair(a, b)) /\ in(a, x) /\ in(b, y)) by Restate
    thenHave((in(a, x), in(b, y)) |- exists(d, (pair(a, b) === pair(a, d)) /\ in(a, x) /\ in(d, y))) by RightExists
    thenHave((in(a, x), in(b, y)) |- exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct)
  }

  val cartesianProductElimPair = Lemma(
    in(pair(a, b), cartesianProduct(x, y)) |- in(a, x) /\ in(b, y)
  ) {
    have(in(c, x) /\ in(d, y) |- in(c, x) /\ in(d, y)) by Hypothesis
    thenHave((a === c, b === d, in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by RightSubstEq.withParametersSimple(List((a, c), (b, d)), lambda(Seq(a, b), in(a, x) /\ in(b, y)))
    thenHave((a === c) /\ (b === d) /\ in(c, x) /\ in(d, y) |- in(a, x) /\ in(b, y)) by Restate
    thenHave((pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y) |- in(a, x) /\ in(b, y)) by Substitution.ApplyRules(pairExtensionality)
    thenHave(exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(a, x) /\ in(b, y)) by LeftExists
    thenHave(exists(c, exists(d, (pair(a, b) === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(a, x) /\ in(b, y)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct)
  }

  /**
   * Lemma --- Cartesian Product Elimination Rule
   *
   *   `p ∈ x * y ⇒ fst p ∈ x ∧ snd p ∈ y`
   */
  val cartesianProductElim = Lemma(
    in(p, cartesianProduct(x, y)) |- in(firstInPair(p), x) /\ in(secondInPair(p), y)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInCartesianProduct)(cartesianProductElimPair of (a := firstInPair(p), b := secondInPair(p)))
  }

  val cartesianProductMembershipPair = Lemma(
    in(pair(a, b), cartesianProduct(x, y)) <=> (in(a, x) /\ in(b, y))
  ) {
    val forward = have(in(pair(a, b), cartesianProduct(x, y)) ==> (in(a, x) /\ in(b, y))) by Restate.from(cartesianProductElimPair)
    val backward = have((in(a, x) /\ in(b, y)) ==> in(pair(a, b), cartesianProduct(x, y))) by Restate.from(cartesianProductIntro)
    have(thesis) by RightIff(forward, backward)
  }

  val cartesianProductLeftEmpty = Lemma(
    cartesianProduct(emptySet, y) === emptySet
  ) {
    have(in(firstInPair(p), emptySet) /\ in(secondInPair(p), y) |- ()) by Weakening(emptySetAxiom of (x := firstInPair(p)))
    have(in(p, cartesianProduct(emptySet, y)) |- ()) by Cut(cartesianProductElim of (x := emptySet), lastStep)
    thenHave(exists(p, in(p, cartesianProduct(emptySet, y))) |- ()) by LeftExists
    have(!(cartesianProduct(emptySet, y) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := cartesianProduct(emptySet, y)), lastStep)
  }

  val cartesianProductRightEmpty = Lemma(
    cartesianProduct(x, emptySet) === emptySet
  ) {
    have(in(firstInPair(p), x) /\ in(secondInPair(p), emptySet) |- ()) by Weakening(emptySetAxiom of (x := secondInPair(p)))
    have(in(p, cartesianProduct(x, emptySet)) |- ()) by Cut(cartesianProductElim of (y := emptySet), lastStep)
    thenHave(exists(p, in(p, cartesianProduct(x, emptySet))) |- ()) by LeftExists
    have(!(cartesianProduct(x, emptySet) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := cartesianProduct(x, emptySet)), lastStep)
  }

  val cartesianProductSubset = Lemma(
    (subset(w, y), subset(x, z)) |- subset(cartesianProduct(w, x), cartesianProduct(y, z))
  ) {
    have((in(firstInPair(p), w), in(secondInPair(p), z), subset(w, y)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(y, z))) by
      Cut(subsetElim of (z := firstInPair(p), x := w), cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := y, y := z))
    have((in(firstInPair(p), w), in(secondInPair(p), x), subset(w, y), subset(x, z)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(y, z))) by
      Cut(subsetElim of (z := secondInPair(p), y := z), lastStep)
    thenHave((in(firstInPair(p), w) /\ in(secondInPair(p), x), subset(w, y), subset(x, z)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(y, z))) by
      LeftAnd
    have((in(p, cartesianProduct(w, x)), subset(w, y), subset(x, z)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(y, z))) by Cut(cartesianProductElim of (x := w, y := x), lastStep)
    thenHave((in(p, cartesianProduct(w, x)), subset(w, y), subset(x, z)) |- in(p, cartesianProduct(y, z))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := w, y := x))
    thenHave((subset(w, y), subset(x, z)) |- in(p, cartesianProduct(w, x)) ==> in(p, cartesianProduct(y, z))) by RightImplies
    thenHave((subset(w, y), subset(x, z)) |- forall(p, in(p, cartesianProduct(w, x)) ==> in(p, cartesianProduct(y, z)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := cartesianProduct(w, x), y := cartesianProduct(y, z)))
  }

  val singletonCartesianProduct = Lemma(
    singleton(pair(x, y)) === cartesianProduct(singleton(x), singleton(y))
  ) {
    val forward = have(in(p, singleton(pair(x, y))) ==> in(p, cartesianProduct(singleton(x), singleton(y))))subproof {
      have(in(y, singleton(y)) |- in(pair(x, y), cartesianProduct(singleton(x), singleton(y)))) by
        Cut(singletonIntro, cartesianProductIntro of (a := x, b := y, x := singleton(x), y := singleton(y)))
      have(in(pair(x, y), cartesianProduct(singleton(x), singleton(y)))) by Cut(singletonIntro of (x := y), lastStep) 
      thenHave(in(p, singleton(pair(x, y))) |- in(p, cartesianProduct(singleton(x), singleton(y)))) by
        Substitution.ApplyRules(singletonElim) 
    }

    val backward = have(in(p, cartesianProduct(singleton(x), singleton(y))) ==> in(p, singleton(pair(x, y)))) subproof {
      have((firstInPair(p) === x, secondInPair(p) === y) |- in(pair(firstInPair(p), secondInPair(p)), singleton(pair(x, y)))) by
        Substitution.ApplyRules(firstInPair(p) === x, secondInPair(p) === y)(singletonIntro of (x := pair(x, y)))
      have((in(firstInPair(p), singleton(x)), secondInPair(p) === y) |- in(pair(firstInPair(p), secondInPair(p)), singleton(pair(x, y))) )by
        Cut(singletonElim of (y := firstInPair(p)), lastStep)
      have((in(firstInPair(p), singleton(x)), in(secondInPair(p), singleton(y))) |- in(pair(firstInPair(p), secondInPair(p)), singleton(pair(x, y)))) by 
        Cut(singletonElim of (x := y, y := secondInPair(p)), lastStep)
      thenHave(in(firstInPair(p), singleton(x)) /\ in(secondInPair(p), singleton(y)) |- in(pair(firstInPair(p), secondInPair(p)), singleton(pair(x, y)))) by LeftAnd
      have(in(p, cartesianProduct(singleton(x), singleton(y))) |- in(pair(firstInPair(p), secondInPair(p)), singleton(pair(x, y)))) by
        Cut(cartesianProductElim of (x := singleton(x), y := singleton(y)), lastStep)
      thenHave(in(p, cartesianProduct(singleton(x), singleton(y))) |- in(p, singleton(pair(x, y)))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := singleton(x), y := singleton(y)))
    }

    have(in(p, singleton(pair(x, y))) <=> in(p, cartesianProduct(singleton(x), singleton(y)))) by RightIff(forward, backward)
    thenHave(forall(p, in(p, singleton(pair(x, y))) <=> in(p, cartesianProduct(singleton(x), singleton(y))))) by RightForall
    have(singleton(pair(x, y)) === cartesianProduct(singleton(x), singleton(y))) by Cut(lastStep, equalityIntro of (x := singleton(pair(x, y)), y := cartesianProduct(singleton(x), singleton(y))))
  }

  val cartesianProductLeftUnion = Lemma(
    cartesianProduct(setUnion(a, b), c) === setUnion(cartesianProduct(a, c), cartesianProduct(b, c))
  ) {
    val forward = have(in(p, cartesianProduct(setUnion(a, b), c)) ==> in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c)))) subproof {
      val hyp = have(in(secondInPair(p), c) |- in(secondInPair(p), c)) by Hypothesis
      val cartProdIntro = have(in(firstInPair(p), a) /\ in(secondInPair(p), c) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(a, c))) by LeftAnd(
        cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := a, y := c)
      )

      have((in(firstInPair(p), setUnion(a, b)), in(secondInPair(p), c)) |- (in(firstInPair(p), a), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by RightAnd(
        setUnionElim of (z := firstInPair(p), x := a, y := b),
        hyp
      )
      have((in(firstInPair(p), setUnion(a, b)), in(secondInPair(p), c)) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by RightAnd(
        lastStep,
        hyp
      )
      thenHave((in(firstInPair(p), setUnion(a, b)) /\ in(secondInPair(p), c)) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by LeftAnd
      have(in(p, cartesianProduct(setUnion(a, b), c)) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by
        Cut(cartesianProductElim of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, b), y := c), lastStep)
      have(in(p, cartesianProduct(setUnion(a, b), c)) |- (in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(a, c)), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by
        Cut(lastStep, cartProdIntro)
      have(in(p, cartesianProduct(setUnion(a, b), c)) |- (in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(a, c)), in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(b, c)))) by
        Cut(lastStep, cartProdIntro of (a := b))
      thenHave(in(p, cartesianProduct(setUnion(a, b), c)) |- (in(p, cartesianProduct(a, c)), in(p, cartesianProduct(b, c)))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := setUnion(a, b), y := c))
      have(in(p, cartesianProduct(setUnion(a, b), c)) |- (in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(b, c)))) by
        Cut(lastStep, setUnionLeftIntro of (x := cartesianProduct(a, c), y := cartesianProduct(b, c), z := p))
      have(in(p, cartesianProduct(setUnion(a, b), c)) |- in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c)))) by
        Cut(lastStep, setUnionRightIntro of (x := cartesianProduct(a, c), y := cartesianProduct(b, c), z := p))
    }
    val backward = have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) ==> in(p, cartesianProduct(setUnion(a, b), c))) subproof {

      val cartesianProdIntro = have(in(firstInPair(p), setUnion(a, b)) /\ in(secondInPair(p), c) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, b), c))) by
        LeftAnd(cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, b), y := c))

      val unElim = have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(p, cartesianProduct(a, c)) \/ in(p, cartesianProduct(b, c))) by
        RightOr(setUnionElim of (z := p, x := cartesianProduct(a, c), y := cartesianProduct(b, c)))

      have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(p, cartesianProduct(b, c)))) by
        Cut(setUnionElim of (z := p, x := cartesianProduct(a, c), y := cartesianProduct(b, c)), cartesianProductElim of (x := a, y := c))
      have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by
        Cut(lastStep, cartesianProductElim of (x := b, y := c))
      thenHave(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- (in(firstInPair(p), a) \/ in(firstInPair(p), b)) /\ in(secondInPair(p), c)) by Tautology
      thenHave(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(firstInPair(p), setUnion(a, b)) /\ in(secondInPair(p), c)) by Substitution.ApplyRules(setUnionMembership)
      val beforeSubst =
        have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, b), c))) by Cut(lastStep, cartesianProdIntro)

      val left = thenHave((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(a, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a, y := c))

      val right = have((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(b, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := b, y := c))(beforeSubst)

      have((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(a, c)) \/ in(p, cartesianProduct(b, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by LeftOr(
        left,
        right
      )
      have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by Cut(unElim, lastStep)
    }

    have(in(p, cartesianProduct(setUnion(a, b), c)) <=> in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c)))) by RightIff(forward, backward)
    thenHave(forall(p, in(p, cartesianProduct(setUnion(a, b), c)) <=> in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := cartesianProduct(setUnion(a, b), c), y := setUnion(cartesianProduct(a, c), cartesianProduct(b, c))))
  }

  /**
   * Lemma --- the union of two Cartesian products is a subset of the product of unions.
   *
   *    `a * b ∪ c * d ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfCartesianProducts = Lemma(
    subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))
  ) {
    val left = have(subset(cartesianProduct(a, b), cartesianProduct(setUnion(a, c), setUnion(b, d)))) subproof {
      have((in(firstInPair(p), a), in(secondInPair(p), setUnion(b, d))) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionLeftIntro of (z := firstInPair(p), x := a, y := c),
        cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, c), y := setUnion(b, d))
      )
      have((in(firstInPair(p), a), in(secondInPair(p), b)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionLeftIntro of (z := secondInPair(p), x := b, y := d),
        lastStep
      )
      thenHave(in(firstInPair(p), a) /\ in(secondInPair(p), b) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by LeftAnd
      have(in(p, cartesianProduct(a, b)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(cartesianProductElim of (x := a, y := b), lastStep)
      thenHave(in(p, cartesianProduct(a, b)) |- in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a, y := b))
      thenHave(in(p, cartesianProduct(a, b)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by RightImplies
      thenHave(forall(p, in(p, cartesianProduct(a, b)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d))))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := cartesianProduct(a, b), y := cartesianProduct(setUnion(a, c), setUnion(b, d))))
    }

    val right = have(subset(cartesianProduct(c, d), cartesianProduct(setUnion(a, c), setUnion(b, d)))) subproof {
      have((in(firstInPair(p), c), in(secondInPair(p), setUnion(b, d))) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionRightIntro of (z := firstInPair(p), x := a, y := c),
        cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, c), y := setUnion(b, d))
      )
      have((in(firstInPair(p), c), in(secondInPair(p), d)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionRightIntro of (z := secondInPair(p), x := b, y := d),
        lastStep
      )
      thenHave(in(firstInPair(p), c) /\ in(secondInPair(p), d) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by LeftAnd
      have(in(p, cartesianProduct(c, d)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(cartesianProductElim of (x := c, y := d), lastStep)
      thenHave(in(p, cartesianProduct(c, d)) |- in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := c, y := d))
      thenHave(in(p, cartesianProduct(c, d)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by RightImplies
      thenHave(forall(p, in(p, cartesianProduct(c, d)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d))))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := cartesianProduct(c, d), y := cartesianProduct(setUnion(a, c), setUnion(b, d))))
    }

    have(
      subset(cartesianProduct(c, d), cartesianProduct(setUnion(a, c), setUnion(b, d))) |- subset(
        setUnion(cartesianProduct(a, b), cartesianProduct(c, d)),
        cartesianProduct(setUnion(a, c), setUnion(b, d))
      )
    ) by Cut(left, unionOfTwoSubsets of (a := cartesianProduct(a, b), b := cartesianProduct(c, d), c := cartesianProduct(setUnion(a, c), setUnion(b, d))))
    have(thesis) by Cut(right, lastStep)
  }

}
