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
  private val S = predicate[3]
  private val F = function[1]
  private val G = function[2]
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
    ∃(x, ∀(y, y ∉ y <=> y ∈ x)) |- ()
  ) {
    val contra = x ∉ x <=> x ∈ x

    have(contra |- ()) by Restate
    thenHave(∀(y, y ∉ y <=> y ∈ x) |- ()) by LeftForall
    thenHave(∃(x, ∀(y, y ∉ y <=> y ∈ x)) |- ()) by LeftExists
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
    ∃(z, ∀(t, t ∈ z <=> schemPred(t))) |- ∃!(z, ∀(t, t ∈ z <=> schemPred(t)))
  ) {
    def prop(z: Term) = t ∈ z <=> schemPred(t)
    def fprop(z: Term) = ∀(t, prop(z))

    // forward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    thenHave((fprop(z), (z === a)) |- fprop(a)) by RightSubstEq.withParametersSimple(List((z, a)), lambda(Seq(z), fprop(z)))
    val forward = thenHave(fprop(z) |- (z === a) ==> fprop(a)) by RightImplies

    // backward direction
    have(fprop(z) |- fprop(z)) by Hypothesis
    val hyp = thenHave(fprop(z) |- prop(z)) by InstantiateForall(t)
    have((fprop(z), fprop(a)) |- prop(z) /\ prop(a)) by RightAnd(lastStep, lastStep of (z := a))
    thenHave((fprop(z), fprop(a)) |- t ∈ a <=> t ∈ z) by Tautology
    thenHave((fprop(z), fprop(a)) |- ∀(t, t ∈ a <=> t ∈ z)) by RightForall

    have((fprop(z), fprop(a)) |- (∀(t, t ∈ a <=> t ∈ z) <=> (a === z)) /\ ∀(t, t ∈ a <=> t ∈ z)) by RightAnd(lastStep, extensionalityAxiom of (x := a, y := z))
    thenHave((fprop(z), fprop(a)) |- (a === z)) by Tautology
    val backward = thenHave(fprop(z) |- fprop(a) ==> (a === z)) by RightImplies

    have(fprop(z) |- fprop(a) <=> (a === z)) by RightIff(forward, backward)
    thenHave(fprop(z) |- ∀(a, fprop(a) <=> (a === z))) by RightForall
    thenHave(fprop(z) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by RightExists
    thenHave(∃(z, fprop(z)) |- ∃(z, ∀(a, fprop(a) <=> (a === z)))) by LeftExists
    thenHave(∃(z, fprop(z)) |- ∃!(z, fprop(z))) by RightExistsOne
  }

  val equalityIntro = Lemma(
    ∀(z, z ∈ x <=> z ∈ y) |- x === y
  ) {
    have(thesis) by Weakening(extensionalityAxiom)
  }

  /**
   * Replacement schema
   */

  def classFunction(R: Term ** 2 |-> Formula, P: Term ** 1 |-> Formula): Formula = ∀(x, P(x) ==> ∃!(y, R(x, y)))
  def classFunction(R: Term ** 2 |-> Formula): Formula = classFunction(R, lambda(x, True))
  def classFunction(R: Term ** 2 |-> Formula, A: Term): Formula = classFunction(R, lambda(x, x ∈ A))

  def classFunctionTwoArgs(S: Term ** 3 |-> Formula, R: Term ** 2 |-> Formula): Formula = ∀(x, ∀(y, R(x, y) ==> ∃!(z, S(x, y, z))))
  def classFunctionTwoArgs(S: Term ** 3 |-> Formula): Formula = classFunctionTwoArgs(S, lambda((x, y), True))

  val classFunctionElim = Lemma(
    (classFunction(R, P), P(x)) |- ∃!(y, R(x, y))
  ) {
    have(classFunction(R, P) |- classFunction(R, P)) by Hypothesis
    thenHave(thesis) by InstantiateForall(x)
  }

  val totalClassFunctionElim = Lemma(
    classFunction(R) |- ∃!(y, R(x, y))
  ) {
    have(thesis) by Restate.from(classFunctionElim of (P := lambda(x, True)))
  }

  val classFunctionTwoArgsElim = Lemma(
    (classFunctionTwoArgs(S, R), R(x, y)) |- ∃!(z, S(x, y, z))
  ) {
    have(classFunctionTwoArgs(S, R) |- classFunctionTwoArgs(S, R)) by Hypothesis
    thenHave(thesis) by InstantiateForall(x, y)
  }

  val totalClassFunctionTwoArgsElim = Lemma(
    classFunctionTwoArgs(S) |- ∃!(z, S(x, y, z))
  ) {
    have(thesis) by Restate.from(classFunctionTwoArgsElim of (R := lambda((x, y), True)))
  }

  val classFunctionHasImage = Lemma(
    (classFunction(R, P), P(x)) |- ∃(y, R(x, y))
  ) {
    have(thesis) by Cut(classFunctionElim, existsOneImpliesExists of (P := lambda(y, R(x, y))))
  }

  val totalClassFunctionHasImage = Lemma(
    classFunction(R) |- ∃(y, R(x, y))
  ) {
    have(thesis) by Restate.from(classFunctionHasImage of (P := lambda(x, True)))
  }

  val classFunctionTwoArgsHasImage = Lemma(
    (classFunctionTwoArgs(S, R), R(x, y)) |- ∃(z, S(x, y, z))
  ) {
    have(thesis) by Cut(classFunctionTwoArgsElim, existsOneImpliesExists of (P := lambda(z, S(x, y, z))))
  }

  val totalClassFunctionTwoArgsHasImage = Lemma(
    classFunctionTwoArgs(S) |- ∃(z, S(x, y, z))
  ) {
    have(thesis) by Restate.from(classFunctionTwoArgsHasImage of (R := lambda((x, y), True)))
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
    thenHave(∀(z, ((F(x) === y) /\ (F(x) === z)) ==> (y === z))) by RightForall
    val uniqueness = thenHave(∀(y, ∀(z, ((F(x) === y) /\ (F(x) === z)) ==> (y === z)))) by RightForall

    have(F(x) === F(x)) by RightRefl
    val existence = thenHave(∃(y, F(x) === y)) by RightExists

    have(∃(y, F(x) === y) |- ∃!(y, F(x) === y)) by Cut(uniqueness of (P := lambda(y, F(x) === y)), existenceAndUniqueness of (P := lambda(y, F(x) === y)))
    have(∃!(y, F(x) === y)) by Cut(existence, lastStep)
    thenHave(P(x) ==> ∃!(y, F(x) === y)) by Weakening
    thenHave(thesis) by RightForall
  }

    val classFunctionTwoArgsUniqueness = Lemma(
    (classFunctionTwoArgs(S, R), R(x, y), S(x, y, z), S(x, y, w)) |- z === w
  ) {
    have(thesis) by Cut(classFunctionTwoArgsElim, existsOneImpliesUniqueness of (P := lambda(z, S(x, y, z)), x := z, y := w))
  }

  val totalClassFunctionTwoArgsUniqueness = Lemma(
    (classFunctionTwoArgs(S), S(x, y, z), S(x, y, w)) |- z === w
  ) {
    have(thesis) by Restate.from(classFunctionTwoArgsUniqueness of (R := lambda((x, y), True)))
  }

  val functionIsClassFunctionTwoArgs = Lemma(
    classFunctionTwoArgs(lambda((x, y, z), G(x, y) === z), R)
  ) {
    have(((G(x, y) === z) /\ (G(x, y) === w)) ==> (z === w)) by Restate.from(equalityTransitivity of (x := z, y := G(x, y), z := w))
    thenHave(∀(z, ((G(x, y) === z) /\ (G(x, y) === w)) ==> (z === w))) by RightForall
    val uniqueness = thenHave(∀(w, ∀(z, ((G(x, y) === z) /\ (G(x, y) === w)) ==> (z === w)))) by RightForall

    have(G(x, y) === G(x, y)) by RightRefl
    val existence = thenHave(∃(z, G(x, y) === z)) by RightExists

    have(∃(z, G(x, y) === z) |- ∃!(z, G(x, y) === z)) by Cut(uniqueness, existenceAndUniqueness of (P := lambda(z, G(x, y) === z)))
    have(∃!(z, G(x, y) === z)) by Cut(existence, lastStep)
    thenHave(R(x, y) ==> ∃!(z, G(x, y) === z)) by Weakening
    thenHave(∀(y, R(x, y) ==> ∃!(z, G(x, y) === z))) by RightForall
    thenHave(thesis) by RightForall
  }

  val replacementExistence = Lemma(
    classFunction(R, A) |- ∃(B, ∀(y, y ∈ B <=> ∃(x, x ∈ A /\ R(x, y))))
  ) {
    have(∃!(y, R(x, y)) |- (R(x, y) /\ R(x, z)) ==> (y === z)) by Restate.from(existsOneImpliesUniqueness of (P := lambda(y, R(x, y)), x := y, y := z))
    thenHave(∃!(y, R(x, y)) |- ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z))) by RightForall
    thenHave(∃!(y, R(x, y)) |- ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by RightForall
    thenHave(x ∈ A ==> ∃!(y, R(x, y)) |- x ∈ A ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by Tautology
    thenHave(classFunction(R, A) |- x ∈ A ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by LeftForall
    val uniqueness = thenHave(classFunction(R, A) |- ∀(x, x ∈ A ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z))))) by RightForall

    have(∀(x, x ∈ A ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) |- ∃(B, ∀(b, b ∈ B <=> ∃(x, x ∈ A /\ R(x, b))))) by
      Restate.from({ val P = predicate[2]; replacementSchema of (P := R) })
    have(thesis) by Cut(uniqueness, lastStep)
  }

  val replacementUniqueness = Lemma(
    classFunction(R, A) |- ∃!(B, ∀(y, y ∈ B <=> ∃(x, x ∈ A /\ R(x, y))))
  ) {
    have(thesis) by Cut(replacementExistence, uniqueByExtension of (z := B, schemPred := lambda(b, ∃(x, x ∈ A /\ R(x, b)))))
  }

  val replacementClassFunction = Lemma(
    ∃!(B, ∀(y, y ∈ B <=> ∃(x, x ∈ A /\ (F(x) === y))))
  ) {
    have(thesis) by Cut(functionIsClassFunction of (P := lambda(x, x ∈ A)), replacementUniqueness of (R := lambda((x, y), F(x) === y)))
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
    y ∈ x |- x =/= ∅
  ) {
    have((x === ∅) |- y ∉ x) by Substitution.ApplyRules(x === ∅)(emptySetAxiom of (x := y))
  }

  /**
   * Lemma --- If a set is empty, then it has no elements.
   *
   *    `x = ∅ ⊢ y ∉ x`
   */
  val emptySetHasNoElements = Lemma(
    x === ∅ |- y ∉ x
  ) {
    have(thesis) by Restate.from(setWithElementNonEmpty)
  }

  /**
   * Lemma --- A set containing no elements is empty.
   *
   *    `∀ y. y ∉ x ⊢ x = ∅`
   */
  val setWithNoElementsIsEmpty = Lemma(
    ∀(y, y ∉ x) |- (x === ∅)
  ) {
    val lhs = have(y ∈ ∅ ==> y ∈ x) by Weakening(emptySetAxiom of (x := y))

    have(y ∉ x |- y ∉ x) by Hypothesis
    thenHave(y ∉ x |- (y ∉ x, y ∈ ∅)) by Weakening
    val rhs = thenHave(y ∉ x |- y ∈ x ==> y ∈ ∅) by Restate

    have(y ∉ x |- y ∈ x <=> y ∈ ∅) by RightIff(lhs, rhs)
    thenHave(∀(y, y ∉ x) |- y ∈ x <=> y ∈ ∅) by LeftForall
    thenHave(∀(y, y ∉ x) |- ∀(y, y ∈ x <=> y ∈ ∅)) by RightForall
    have(∀(y, y ∉ x) |- (x === ∅)) by Cut(lastStep, equalityIntro of (y := ∅))
  }

  /**
   * Lemma --- Any non-empty set has an element.
   * 
   *   `x ≠ ∅ ⊢ ∃ y. y ∈ x`
   */
  val nonEmptySetHasAnElement = Lemma(
    x =/= ∅ |- ∃(y, y ∈ x)
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
  val subsetIntro = Lemma(
    ∀(z, z ∈ x ==> z ∈ y) |- x ⊆ y
  ) {
    have(thesis) by Weakening(subsetAxiom)
  }

  /**
   * Lemma --- Subset elimination rule
   *
   *  `x ⊆ y, z ∈ x ⊢ z ∈ y`
   */
  val subsetElim = Lemma(
    (x ⊆ y, z ∈ x) |- z ∈ y
  ) {
    have(x ⊆ y |- ∀(z, z ∈ x ==> z ∈ y)) by Weakening(subsetAxiom)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma ---  Subset reflexivity
   *
   *   `x ⊆ x`
   */
  val subsetReflexivity = Lemma(
    x ⊆ x
  ) {
    have(z ∈ x ==> z ∈ x) by Restate
    thenHave(∀(z, z ∈ x ==> z ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := x))
  }

  /**
   * Lemma --- Subset antisymmetry
   *
   *   `x ⊆ y, y ⊆ x |- x = y`
   */
  val subsetAntisymmetry = Lemma(
    (x ⊆ y, y ⊆ x) |- (x === y)
  ) {
    val forward = have(x ⊆ y |- z ∈ x ==> z ∈ y) by RightImplies(subsetElim)
    val backward = have(y ⊆ x |- z ∈ y ==> z ∈ x) by RightImplies(subsetElim of (x := y, y := x))
    have((x ⊆ y, y ⊆ x) |- z ∈ x <=> z ∈ y) by RightIff(forward, backward)
    thenHave((x ⊆ y, y ⊆ x) |- ∀(z, z ∈ x <=> z ∈ y)) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro)
  }

  /**
   * Lemma --- Subset transitivity
   *
   *    `x ⊆ y, y ⊆ z ⊢ x ⊆ z`
   */
  val subsetTransitivity = Lemma(
    (x ⊆ y, y ⊆ z) |- x ⊆ z
  ) {
    have((x ⊆ y, y ⊆ z, a ∈ x) |- a ∈ z) by Cut(subsetElim of (z := a), subsetElim of (x := y, y := z, z := a))
    thenHave((x ⊆ y, y ⊆ z) |- a ∈ x ==> a ∈ z) by RightImplies
    thenHave((x ⊆ y, y ⊆ z) |- ∀(a, a ∈ x ==> a ∈ z)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := z))
  }

  /**
   * Lemma --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val emptySetSubset = Lemma(
    ∅ ⊆ x
  ) {
    have(y ∈ ∅ ==> y ∈ x) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, y ∈ ∅ ==> y ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := ∅, y := x))
  }

  /**
   * Lemma --- Any subset of the empty set is empty.
   *
   *    `x ⊆ ∅ <=> x = ∅`
   */
  val subsetEmptySet = Lemma(
    x ⊆ ∅ <=> (x === ∅)
  ) {
    val forward = have(x ⊆ ∅ ==> (x === ∅)) subproof {
      have((x ⊆ ∅, z ∈ x) |- ()) by RightAnd(subsetElim of (y := ∅), emptySetAxiom of (x := z))
      thenHave((x ⊆ ∅, ∃(z, z ∈ x)) |- ()) by LeftExists
      have((x ⊆ ∅, x =/= ∅) |- ()) by Cut(nonEmptySetHasAnElement, lastStep)
    }

    val backward = have((x === ∅) ==> x ⊆ ∅) subproof {
      have((x === ∅) |- x ⊆ ∅) by RightSubstEq.withParametersSimple(List((x, ∅)), lambda(x, x ⊆ ∅))(emptySetSubset of (x := ∅))
    }

    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Lemma --- A superset of a non empty set is non empty.
   *
   *     `x ⊆ y, x ≠ ∅ ⊢ y ≠ ∅`
   */
  val subsetNotEmpty = Lemma(
    (x ⊆ y, x =/= ∅) |- y =/= ∅
  ) {
    have(x ⊆ ∅ |- x === ∅) by Weakening(subsetEmptySet)
    thenHave((x ⊆ y, y === ∅) |- x === ∅) by LeftSubstEq.withParametersSimple(List((y, ∅)), lambda(y, x ⊆ y))
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
    x ⊆ y |- x ∈ 𝓟(y)
  ) {
    have(thesis) by Weakening(powerAxiom)
  }

  /**
   * Lemma --- Power set elimination rule
   *
   *  `x ∈ 𝓟(y) ⊢ x ⊆ y`
   */
  val powerSetElim = Lemma(
    x ∈ 𝓟(y) |- x ⊆ y
  ) {
    have(thesis) by Weakening(powerAxiom)
  }

  /**
   * Lemma --- Any set is in its power set.
   * 
   *  `x ∈ 𝓟(x)`
   */
  val powerSetContainsSet = Lemma(
    x ∈ 𝓟(x)
  ) {
    have(thesis) by Cut(subsetReflexivity, powerSetIntro of (y := x))
  }

  /**
   * Lemma --- The empty set is an element of every power set.
   *
   *    `∅ ∈ 𝓟(x)`
   */
  val powerSetContainsEmptySet = Lemma(
    ∅ ∈ 𝓟(x)
  ) {
    have(thesis) by Cut(emptySetSubset, powerSetIntro of (x := ∅, y := x))
  }

  /**
   * Lemma --- The power set is never empty.
   *
   *    `𝓟(x) ≠ ∅`
   */
  val powerSetNonEmpty = Lemma(
    𝓟(x) =/= ∅
  ) {
    have(thesis) by Cut(powerSetContainsEmptySet, setWithElementNonEmpty of (y := ∅, x := 𝓟(x)))
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
    x ∈ unorderedPair(x, y)
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
    y ∈ unorderedPair(x, y)
  ) {
    have(thesis) by Weakening(pairAxiom of (z := y))
  }

  /**
   * Lemma --- Unordered pair elimination rule
   * 
   *   `z ∈ {x, y} |- z = x ∨ z = y`
   */
  val unorderedPairElim = Lemma(
    z ∈ unorderedPair(x, y) |- (z === x, z === y)
  ) {
    have(thesis) by Weakening(pairAxiom)
  }

  /**
   * Lemma --- An unordered pair is never empty.
   * 
   *   `{x, y} ≠ ∅`
   */
  val unorderedPairNonEmpty = Lemma(
    unorderedPair(x, y) =/= ∅
  ) {
    have(thesis) by Cut(unorderedPairRightIntro, setWithElementNonEmpty of (x := unorderedPair(x, y)))
  }

  /**
   * Lemma --- Unordered pair subset
   *
   *    `{x, y} ⊆ z <=> x ∈ z ∧ y ∈ z`
   */
  val unorderedPairSubset = Lemma(
    unorderedPair(x, y) ⊆ z <=> (x ∈ z /\ y ∈ z) 
  ) {
    val forward = have(unorderedPair(x, y) ⊆ z ==> (x ∈ z /\ y ∈ z)) subproof {
      val left = have(unorderedPair(x, y) ⊆ z |- x ∈ z) by Cut(unorderedPairLeftIntro, subsetElim of (x := unorderedPair(x, y), y := z, z := x))
      val right = have(unorderedPair(x, y) ⊆ z |- y ∈ z) by Cut(unorderedPairRightIntro, subsetElim of (x := unorderedPair(x, y), y := z, z := y))
      have(unorderedPair(x, y) ⊆ z |- x ∈ z /\ y ∈ z) by RightAnd(left, right)
    } 

    val backward = have((x ∈ z /\ y ∈ z) ==> unorderedPair(x, y) ⊆ z) subproof {
      have(x ∈ z |- x ∈ z) by Hypothesis
      val seq = thenHave((x ∈ z, w === x) |- w ∈ z) by RightSubstEq.withParametersSimple(List((w, x)), lambda(x, x ∈ z))
      have((w ∈ unorderedPair(x, y), x ∈ z) |- (w ∈ z, w === y)) by Cut(unorderedPairElim of (z := w), seq)
      have((w ∈ unorderedPair(x, y), x ∈ z, y ∈ z) |- w ∈ z) by Cut(lastStep, seq of (x := y))
      thenHave((x ∈ z, y ∈ z) |- w ∈ unorderedPair(x, y) ==> w ∈ z) by RightImplies
      thenHave((x ∈ z, y ∈ z) |- ∀(w, w ∈ unorderedPair(x, y) ==> w ∈ z)) by RightForall
      have((x ∈ z, y ∈ z) |- unorderedPair(x, y) ⊆ z) by Cut(lastStep, subsetIntro of (x := unorderedPair(x, y), y := z))
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
    have(z ∈ unorderedPair(y, x) <=> z ∈ unorderedPair(x, y)) by Substitution.ApplyRules(pairAxiom)(pairAxiom of (x := y, y := x))
    thenHave(∀(z, z ∈ unorderedPair(x, y) <=> z ∈ unorderedPair(y, x))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := unorderedPair(x, y), y := unorderedPair(y, x)))
  }

  /**
   * Lemma --- Unordered pair equality 
   *
   *   `{a, b} = {c, d} |- (a = c ∧ b = d) ∨ (a = d ∧ b = c)`
   */
  val unorderedPairDeconstruction = Lemma(
    (unorderedPair(a, b) === unorderedPair(c, d)) |- (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    val s1 = have(Substitution.applySubst(unorderedPair(a, b) === unorderedPair(c, d))(pairAxiom of (x := a, y := b)))
    val base = have(Substitution.applySubst(s1)(pairAxiom of (x := c, y := d)))

    have(thesis) by Tautology.from(base of (z := a), base of (z := b), base of (z := c), base of (z := d))
  }

  /**
   * Lemma --- Unordered pair equality equivalence
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
    (x ∈ z /\ y ∈ z) <=> unorderedPair(x, y) ∈ 𝓟(z)
  ) {
    have(unorderedPair(x, y) ⊆ z <=> (x ∈ z /\ y ∈ z) |- (x ∈ z /\ y ∈ z) <=> unorderedPair(x, y) ∈ 𝓟(z)) by RightSubstIff.withParametersSimple(
      List((unorderedPair(x, y) ⊆ z, x ∈ z /\ y ∈ z)), lambda(h, h <=> unorderedPair(x, y) ∈ 𝓟(z))
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
    y ∈ singleton(x) <=> (x === y)
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(pairAxiom of (z := y, y := x))
  }

  /**
   * Lemma --- Singleton introduction rule
   *
   *   `x ∈ {x}`
   */
  val singletonIntro = Lemma(
    x ∈ singleton(x)
  ) {
    have(thesis) by Restate.from(singletonMembership of (y := x))
  }

  /**
   * Lemma --- Singleton elimination rule
   *
   *   `y ∈ {x} |- x = y`
   */
  val singletonElim = Lemma(
    y ∈ singleton(x) |- x === y
  ) {
    have(thesis) by Weakening(singletonMembership)
  }

  /**
   * Lemma --- A singleton set is never empty.
   *
   *    `{x} ≠ ∅`
   */
  val singletonNonEmpty = Lemma(
    singleton(x) =/= ∅
  ) {
    have(thesis) by Cut(singletonIntro, setWithElementNonEmpty of (y := x, x := singleton(x)))
  }

  /**
   * Lemma --- Singleton subset
   *
   *    `{x} ⊆ y <=> x ∈ y`
   */
  val singletonSubset = Lemma(
    singleton(x) ⊆ y <=> x ∈ y 
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

  /**
   * Lemma --- Singleton-Unordered pair equality
   *
    *    `{x} = {y, z} <=> x = y ∧ x = z`
    */
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
    x ∈ y <=> singleton(x) ∈ 𝓟(y)
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
  val unionIntro = Lemma(
    (z ∈ y, y ∈ x) |- z ∈ union(x)
  ) {
    have((z ∈ y, y ∈ x) |- y ∈ x /\ z ∈ y) by Restate
    thenHave((z ∈ y, y ∈ x) |- ∃(y, y ∈ x /\ z ∈ y)) by RightExists
    thenHave((z ∈ y, y ∈ x) |- z ∈ union(x)) by Substitution.ApplyRules(unionAxiom)
  }

  /**
   * Lemma --- Union elimination rule
   *
   *   `z ∈ ∪ x |- ∃ y ∈ x. z ∈ y`
   */
  val unionElim = Lemma(
    z ∈ union(x) |- ∃(y, y ∈ x /\ z ∈ y)
  ) {
    have(thesis) by Weakening(unionAxiom)
  }

  /**
   * Lemma --- Any element of a set is a subset of its union.
   * 
   *   `x ∈ y |- x ⊆ ∪ y`
   */
  val subsetUnion = Lemma(x ∈ y |- x ⊆ union(y)) {
    have(x ∈ y |- z ∈ x ==> z ∈ union(y)) by RightImplies(unionIntro of (x := y, y := x))
    thenHave(x ∈ y |- ∀(z, z ∈ x ==> z ∈ union(y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (y := union(y)))
  }

  /**
   * Lemma --- The union of the empty set is the empty set.
   *
   *    `∪ ∅ = ∅`
   */
  val unionEmpty = Lemma(union(∅) === ∅) {
    have(y ∈ ∅ /\ x ∈ y |- ()) by Weakening(emptySetAxiom of (x := y))
    thenHave(∃(y, y ∈ ∅ /\ x ∈ y) |- ()) by LeftExists
    have(x ∈ union(∅) |- ()) by Cut(unionElim of (z := x, x := ∅), lastStep)
    thenHave(∃(x, x ∈ union(∅)) |- ()) by LeftExists
    have(union(∅) =/= ∅ |- ()) by Cut(nonEmptySetHasAnElement of (x := union(∅)), lastStep)
  }

  /**
   * Lemma --- Union is monotonic
   *
   *    `x ⊆ y |- ∪ x ⊆ ∪ y`
   */
  val unionMonotonicity = Lemma(x ⊆ y |- union(x) ⊆ union(y)) {
    have((z ∈ w, w ∈ x, x ⊆ y) |- z ∈ union(y)) by Cut(subsetElim of (z := w), unionIntro of (y := w, x := y))
    thenHave((z ∈ w /\ w ∈ x, x ⊆ y) |- z ∈ union(y)) by LeftAnd
    thenHave((∃(w, z ∈ w /\ w ∈ x), x ⊆ y) |- z ∈ union(y)) by LeftExists
    have((z ∈ union(x), x ⊆ y) |- z ∈ union(y)) by Cut(unionElim, lastStep)
    thenHave(x ⊆ y |- z ∈ union(x) ==> z ∈ union(y)) by RightImplies
    thenHave(x ⊆ y |- ∀(z, z ∈ union(x) ==> z ∈ union(y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := union(x), y := union(y)))
  }

  /**
   * Lemma --- The union of a Singleton is the original set
   * 
   *      `∪ {x} = x`
   */
  val unionSingleton = Lemma((union(singleton(x)) === x)) {
    have((y ∈ singleton(x) /\ z ∈ y) <=> (y ∈ singleton(x) /\ z ∈ y)) by Restate
    thenHave((y ∈ singleton(x) /\ z ∈ y) <=> ((x === y) /\ z ∈ y)) by Substitution.ApplyRules(singletonMembership)
    thenHave(∀(y, (y ∈ singleton(x) /\ z ∈ y) <=> ((x === y) /\ z ∈ y))) by RightForall
    have(∃(y, y ∈ singleton(x) /\ z ∈ y) <=> ∃(y, (x === y) /\ z ∈ y)) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(y, y ∈ singleton(x) /\ z ∈ y), Q := lambda(y, (x === y) /\ z ∈ y))
    )
    thenHave(z ∈ union(singleton(x)) <=> z ∈ x) by Substitution.ApplyRules(unionAxiom, onePointRule of (y := x, Q := lambda(y, z ∈ y)))
    thenHave(∀(z, z ∈ union(singleton(x)) <=> z ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(singleton(x)), y := x))
  }

  val unorderedPairElementsInUnion = Lemma(
    unorderedPair(x, y) ∈ z |- x ∈ union(z) /\ y ∈ union(z)
  ) {
    val left = have(unorderedPair(x, y) ∈ z |- x ∈ union(z)) by Cut(unorderedPairLeftIntro, unionIntro of (z := x, y := unorderedPair(x, y), x := z))
    val right = have(unorderedPair(x, y) ∈ z |- y ∈ union(z)) by Cut(unorderedPairRightIntro, unionIntro of (z := y, y := unorderedPair(x, y), x := z))
    have(thesis) by RightAnd(left, right)
  }

  /**
   * Lemma --- IF a singleton belongs to the set then its element belongs to the union of the set.
   *
   *    `{x} ∈ y |- x ∈ ∪ y`
   */
  val singletonElementInUnion = Lemma(
    singleton(x) ∈ y |- x ∈ union(y)
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition)(unorderedPairElementsInUnion of (y := x, z := y))
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

  extension (x: Term) {
    infix def ∪(y: Term) = setUnion(x, y)
  }

  /**
   * Lemma --- Binary Union Membership
   *
   *   `z ∈ x ∪ y ⇔ z ∈ x ∨ z ∈ y`
   */
  val setUnionMembership = Lemma(
    z ∈ (x ∪ y) <=> (z ∈ x \/ (z ∈ y))
  ) {
    have((z ∈ a /\ ((a === x) \/ (a === y))) <=> (((a === x) /\ z ∈ a) \/ ((a === y) /\ z ∈ a))) by Tautology
    thenHave((z ∈ a /\ a ∈ unorderedPair(x, y)) <=> (((a === x) /\ z ∈ a) \/ ((a === y) /\ z ∈ a))) by Substitution.ApplyRules(pairAxiom of (z := a))
    thenHave(∀(a, (z ∈ a /\ a ∈ unorderedPair(x, y)) <=> (((a === x) /\ z ∈ a) \/ ((a === y) /\ z ∈ a)))) by RightForall
    have(∃(a, z ∈ a /\ a ∈ unorderedPair(x, y)) <=> ∃(a, ((a === x) /\ z ∈ a) \/ ((a === y) /\ z ∈ a))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, (z ∈ a /\ a ∈ unorderedPair(x, y))), Q := lambda(a, ((a === x) /\ z ∈ a) \/ ((a === y) /\ z ∈ a)))
    )
    thenHave(∃(a, z ∈ a /\ a ∈ unorderedPair(x, y)) <=> (∃(a, (a === x) /\ z ∈ a) \/ ∃(a, z ∈ a /\ (a === y)))) by Substitution.ApplyRules(
      existentialDisjunctionCommutation of (P := lambda(a, (a === x) /\ z ∈ a), Q := lambda(a, z ∈ a /\ (a === y)))
    )
    thenHave(∃(a, z ∈ a /\ a ∈ unorderedPair(x, y)) <=> (z ∈ x \/ ∃(a, z ∈ a /\ (a === y)))) by Substitution.ApplyRules(onePointRule of (y := x, Q := lambda(a, z ∈ a)))
    thenHave(∃(a, z ∈ a /\ a ∈ unorderedPair(x, y)) <=> (z ∈ x \/ (z ∈ y))) by Substitution.ApplyRules(onePointRule of (Q := lambda(a, z ∈ a)))
    thenHave(z ∈ union(unorderedPair(x, y)) <=> (z ∈ x \/ (z ∈ y))) by Substitution.ApplyRules(unionAxiom of (x := unorderedPair(x, y)))
    thenHave(thesis) by Substitution.ApplyRules(setUnion.shortDefinition)
  }

  /**
   * Lemma --- Binary union left introduction rule
   *
   *   `z ∈ x ⊢ z ∈ x ∪ y`
   */
  val setUnionLeftIntro = Lemma(
    z ∈ x |- z ∈ (x ∪ y)
  ) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- Binary union right introduction rule
   *
   *   `z ∈ y ⊢ z ∈ x ∪ y`
   */
  val setUnionRightIntro = Lemma(
    z ∈ y |- z ∈ (x ∪ y)
  ) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- Binary union elimination rule
   *
   *   `z ∈ x ∪ y ⊢ z ∈ x ∨ z ∈ y`
   */
  val setUnionElim = Lemma(
    z ∈ (x ∪ y) |- (z ∈ x, z ∈ y)
  ) {
    have(thesis) by Weakening(setUnionMembership)
  }

  /**
   * Lemma --- the binary set union operation is commutative.
   *
   *    `a ∪ b = b ∪ a`
   */
  val setUnionCommutativity = Lemma(
    a ∪ b === b ∪ a
  ) {
    have(z ∈ (a ∪ b) <=> z ∈ (b ∪ a)) by Substitution.ApplyRules(setUnionMembership of (x := b, y := a))(setUnionMembership of (x := a, y := b))
    thenHave(∀(z, z ∈ (a ∪ b) <=> z ∈ (b ∪ a))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := a ∪ b, y := b ∪ a))
  }

  /**
   * Lemma --- the first element of a union is a subset of it.
   *
   *    `a ⊆ a ∪ b`
   */
  val setUnionLeftSubset = Lemma(
    a ⊆ (a ∪ b)
  ) {
    have(z ∈ a ==> z ∈ (a ∪ b)) by RightImplies(setUnionLeftIntro of (x := a, y := b))
    thenHave(∀(z, z ∈ a ==> z ∈ (a ∪ b))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := a, y := a ∪ b))
  }

  /**
   * Lemma --- the second element of a union is a subset of it.
   *
   *    `b ⊆ a ∪ b`
   */
  val setUnionRightSubset = Lemma(
    b ⊆ (a ∪ b)
  ) {
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity)(setUnionLeftSubset of (a := b, b := a))
  }

  /**
   * Lemma --- the union of two subsets of a set is still a subset of it.
   *
   *    `a ⊆ c ∧ b ⊆ c ⊢ a ∪ b ⊆ c`
   */
  val unionOfTwoSubsets = Lemma(
    (a ∪ b) ⊆ c <=> (a ⊆ c /\ b ⊆ c)
  ) {
    val forward = have((a ⊆ c /\ b ⊆ c) ==> (a ∪ b) ⊆ c) subproof {
      have((z ∈ (a ∪ b), a ⊆ c) |- (z ∈ c, z ∈ b)) by Cut(setUnionElim of (x := a, y := b), subsetElim of (x := a, y := c))
      have((z ∈ (a ∪ b), a ⊆ c, b ⊆ c) |- z ∈ c) by Cut(lastStep, subsetElim of (x := b, y := c))
      thenHave((a ⊆ c, b ⊆ c) |- z ∈ (a ∪ b) ==> z ∈ c) by RightImplies
      thenHave((a ⊆ c, b ⊆ c) |- ∀(z, z ∈ (a ∪ b) ==> z ∈ c)) by RightForall
      have((a ⊆ c, b ⊆ c) |- (a ∪ b) ⊆ c) by Cut(lastStep, subsetIntro of (x := a ∪ b, y := c))
    }

    val backward = have((a ∪ b) ⊆ c ==> (a ⊆ c /\ b ⊆ c)) subproof {
      val left = have((a ∪ b) ⊆ c |- a ⊆ c) by Cut(setUnionLeftSubset, subsetTransitivity of (x := a, y := a ∪ b, z := c))
      val right = have((a ∪ b) ⊆ c |- b ⊆ c) by Cut(setUnionRightSubset, subsetTransitivity of (x := b, y := a ∪ b, z := c))
      have((a ∪ b) ⊆ c |- a ⊆ c /\ b ⊆ c) by RightAnd(left, right)
    }

    have(thesis) by RightIff(forward, backward)

  }

  /**
   * Lemma --- the union of subsets of two sets is a subset of their union.
   *
   *    `a ⊆ c ∧ b ⊆ d ⊢ a ∪ b ⊆ c ∪ d`
   */
  val unionOfSubsetsOfDifferentSets = Lemma(
    (a ⊆ c, b ⊆ d) |- (a ∪ b) ⊆ (c ∪ d)
  ) {
    have((z ∈ (a ∪ b), a ⊆ c) |- (z ∈ c, z ∈ b)) by Cut(setUnionElim of (x := a, y := b), subsetElim of (x := a, y := c))
    have((z ∈ (a ∪ b), a ⊆ c, b ⊆ d) |- (z ∈ c, z ∈ d)) by Cut(lastStep, subsetElim of (x := b, y := d))
    have((z ∈ (a ∪ b), a ⊆ c, b ⊆ d) |- (z ∈ (c ∪ d), z ∈ d)) by Cut(lastStep, setUnionLeftIntro of (x := c, y := d))
    have((z ∈ (a ∪ b), a ⊆ c, b ⊆ d) |- z ∈ (c ∪ d)) by Cut(lastStep, setUnionRightIntro of (x := c, y := d))
    thenHave((a ⊆ c, b ⊆ d) |- z ∈ (a ∪ b) ==> z ∈ (c ∪ d)) by RightImplies
    thenHave((a ⊆ c, b ⊆ d) |- ∀(z, z ∈ (a ∪ b) ==> z ∈ (c ∪ d))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := a ∪ b, y := c ∪ d))
  }

  /**
   * Lemma --- Binary union with the ∅
   *
   *   `x ∪ ∅ = x`
   */
  val setUnionRightEmpty = Lemma(
    a ∪ ∅ === a
  ) {
    have(z ∈ ∅ <=> False) by Restate.from(emptySetAxiom of (x := z))
    have(z ∈ (a ∪ ∅) <=> (z ∈ a \/ False)) by Substitution.ApplyRules(lastStep)(setUnionMembership of (x := a, y := ∅))
    thenHave(∀(z, z ∈ (a ∪ ∅) <=> z ∈ a)) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := a ∪ ∅, y := a))
  }

  /**
   * Lemma --- Binary union with the ∅
   *
   *   `∅ ∪ x = x`
   */
  val setUnionLeftEmpty = Lemma(
    ∅ ∪ a === a
  ) {
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity)(setUnionRightEmpty)
  }

  val unionDistributesOverSetUnion = Lemma(
    union(a ∪ b) === union(a) ∪ union(b)
  ) {
    val forward = have(z ∈ union(a ∪ b) ==> z ∈ (union(a) ∪ union(b))) subproof {
      val left = have((z ∈ y, y ∈ a) |- z ∈ (union(a) ∪ union(b))) by Cut(unionIntro of (x := a), setUnionLeftIntro of (x := union(a), y := union(b)))
      val right = have((z ∈ y, y ∈ b) |- z ∈ (union(a) ∪ union(b))) by Cut(unionIntro of (x := b), setUnionRightIntro of (x := union(a), y := union(b)))
      have((z ∈ y, y ∈ a \/ (y ∈ b)) |- z ∈ (union(a) ∪ union(b))) by LeftOr(left, right)
      thenHave((z ∈ y, y ∈ (a ∪ b)) |- z ∈ (union(a) ∪ union(b))) by Substitution.ApplyRules(setUnionMembership)
      thenHave((z ∈ y /\ y ∈ (a ∪ b)) |- z ∈ (union(a) ∪ union(b))) by LeftAnd
      thenHave((∃(y, z ∈ y /\ y ∈ (a ∪ b))) |- z ∈ (union(a) ∪ union(b))) by LeftExists
      have(z ∈ union(a ∪ b) |- z ∈ (union(a) ∪ union(b))) by Cut(unionElim of (z := z, x := a ∪ b), lastStep) 
    }

    val backward = have(z ∈ (union(a) ∪ union(b)) ==> z ∈ union(a ∪ b)) subproof {
      have((z ∈ y, y ∈ a) |- z ∈ union(a ∪ b)) by Cut(setUnionLeftIntro of (z := y, x := a, y := b), unionIntro of (x := a ∪ b))
      thenHave(z ∈ y /\ y ∈ a |- z ∈ union(a ∪ b)) by LeftAnd
      thenHave((∃(y, z ∈ y /\ y ∈ a) |- z ∈ union(a ∪ b))) by LeftExists
      val left = have(z ∈ union(a) |- z ∈ union(a ∪ b)) by Cut(unionElim of (x := a), lastStep)

      have((z ∈ y, y ∈ b) |- z ∈ union(a ∪ b)) by Cut(setUnionRightIntro of (z := y, x := a, y := b), unionIntro of (x := a ∪ b))
      thenHave(z ∈ y /\ y ∈ b |- z ∈ union(a ∪ b)) by LeftAnd
      thenHave((∃(y, z ∈ y /\ y ∈ b) |- z ∈ union(a ∪ b))) by LeftExists
      val right = have(z ∈ union(b) |- z ∈ union(a ∪ b)) by Cut(unionElim of (x := b), lastStep)

      have(z ∈ (union(a) ∪ union(b)) |- (z ∈ union(a ∪ b), z ∈ union(b))) by Cut(setUnionElim of (x := union(a), y := union(b)), left)
      have(z ∈ (union(a) ∪ union(b)) |- z ∈ union(a ∪ b)) by Cut(lastStep, right)
    }

    have(z ∈ union(a ∪ b) <=> z ∈ (union(a) ∪ union(b))) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ union(a ∪ b) <=> z ∈ (union(a) ∪ union(b)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(a ∪ b), y := union(a) ∪ union(b)))
  }

    /**
   * Lemma --- Union with a subset
   * 
   *   `x ⊆ y ⊢ x ∪ y = y`
   */
  val setUnionOfSubsetForward = Lemma(
    x ⊆ y |- x ∪ y === y
  ) {
    have((z ∈ (x ∪ y), x ⊆ y) |- z ∈ y) by Cut(setUnionElim, subsetElim)
    thenHave(x ⊆ y |- z ∈ (x ∪ y) ==> z ∈ y) by RightImplies
    thenHave(x ⊆ y |- ∀(z, z ∈ (x ∪ y) ==> z ∈ y)) by RightForall
    have(x ⊆ y |- (x ∪ y) ⊆ y) by Cut(lastStep, subsetIntro of (x := x ∪ y))
    have((x ⊆ y, y ⊆ (x ∪ y)) |- x ∪ y === y) by Cut(lastStep, subsetAntisymmetry of (x := y, y := x ∪ y))
    have(thesis) by Cut(setUnionRightSubset of (a := x, b := y), lastStep)
  }

  /**
   * Lemma --- Union with a subset
   * 
   *   `y ⊆ x ⊢ x ∪ y = x`
   */
  val setUnionOfSubsetBackward = Lemma(
    y ⊆ x |- x ∪ y === x
  ) {
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity)(setUnionOfSubsetForward of (x := y, y := x))
  }

  /**
   * Unary Intersection
   */

  val intersectionUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> (t ∈ union(x) /\ ∀(b, b ∈ x ==> t ∈ b))))
  ) {
    have(thesis) by UniqueComprehension(union(x), lambda(t, ∀(b, b ∈ x ==> t ∈ b)))
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
  val intersection = DEF(x) --> The(z, ∀(t, t ∈ z <=> (t ∈ union(x) /\ ∀(y, y ∈ x ==> t ∈ y))))(intersectionUniqueness)

  /**
   * Lemma --- Intersection membership rule
   *
   *    `x ≠ ∅ ⊢ z ∈ ∩ x ⇔ ∀ y ∈ x. z ∈ y`
   */
  val intersectionMembership = Lemma(
    x =/= ∅ |- z ∈ intersection(x) <=> ∀(y, y ∈ x ==> z ∈ y)
  ) {

    have(∀(y, y ∈ x ==> z ∈ y) |- ∀(y, y ∈ x ==> z ∈ y)) by Hypothesis
    thenHave((∀(y, y ∈ x ==> z ∈ y), y ∈ x) |- z ∈ y) by InstantiateForall(y)
    have((∀(y, y ∈ x ==> z ∈ y), y ∈ x) |- z ∈ union(x)) by Cut(lastStep, unionIntro)
    thenHave((∀(y, y ∈ x ==> z ∈ y), ∃(y, y ∈ x)) |- z ∈ union(x)) by LeftExists
    have((∀(y, y ∈ x ==> z ∈ y), x =/= ∅) |- z ∈ union(x)) by Cut(nonEmptySetHasAnElement, lastStep)
    val assumption = thenHave(x =/= ∅ |- ∀(y, y ∈ x ==> z ∈ y) ==> z ∈ union(x)) by RightImplies
    
    have(∀(z, z ∈ intersection(x) <=> (z ∈ union(x) /\ ∀(y, y ∈ x ==> z ∈ y)))) by InstantiateForall(intersection(x))(intersection.definition)
    thenHave(z ∈ intersection(x) <=> (z ∈ union(x) /\ ∀(y, y ∈ x ==> z ∈ y))) by InstantiateForall(z)
    thenHave(∀(y, y ∈ x ==> z ∈ y) ==> z ∈ union(x) |- z ∈ intersection(x) <=> ∀(y, y ∈ x ==> z ∈ y)) by Tautology
    have(thesis) by Cut(assumption, lastStep)
  }

  /**
   * Lemma --- Intersection introduction rule
   *
   *    `x ≠ ∅, ∀ y ∈ x. z ∈ y ⊢ z ∈ ∩ x`
   */
  val intersectionIntro = Lemma(
    (x =/= ∅, ∀(y, y ∈ x ==> z ∈ y)) |- z ∈ intersection(x)
  ) {
    have(thesis) by Weakening(intersectionMembership)
  }

  /**
   * Lemma --- Intersection elimination rule
   *
   *    `x ≠ ∅, z ∈ ∩ x, y ∈ x ⊢ z ∈ y`
   */
  val intersectionElim = Lemma(
    (x =/= ∅, z ∈ intersection(x), y ∈ x) |- z ∈ y
  ) {
    have((x =/= ∅, z ∈ intersection(x)) |- ∀(y, y ∈ x ==> z ∈ y)) by Weakening(intersectionMembership) 
    thenHave(thesis) by InstantiateForall(y)
  }


  /**
   * Lemma --- Intersection of a non-empty Class is a Set
   *
   * There ∃ a set that is the intersection of all sets satisfying a given
   * formula. With classes, this means that the unary intersection of a class
   * defined by a predicate is a set.
   *
   *    `∃ x. P(x) ⊢ ∃ z. t ∈ z ⇔ ∀ x. P(x) ⇒ t ∈ x`
   */
  val intersectionOfPredicateClassExists = Lemma(
    ∃(x, P(x)) |- ∃(z, ∀(t, t ∈ z <=> ∀(y, P(y) ==> t ∈ y)))
  ) {

    val hyp = have(∀(y, P(y) ==> t ∈ y) |- ∀(y, P(y) ==> t ∈ y)) by Hypothesis
    thenHave((∀(y, P(y) ==> t ∈ y), P(x)) |- t ∈ x) by InstantiateForall(x)
    have((∀(y, P(y) ==> t ∈ y), P(x)) |- t ∈ x /\ ∀(y, P(y) ==> t ∈ y)) by RightAnd(lastStep, hyp)
    val forward = thenHave(P(x) |- ∀(y, P(y) ==> t ∈ y) ==> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))) by RightImplies

    val backward = thenHave((t ∈ x /\ ∀(y, P(y) ==> t ∈ y)) ==> (∀(y, P(y) ==> t ∈ y))) by Weakening

    val lhs = have(P(x) |- ∀(y, P(y) ==> t ∈ y) <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))) by RightIff(forward, backward)

    val form = formulaVariable
    have((t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))) |- t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))) by Hypothesis
    val rhs = thenHave(
      Set((t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))), (∀(y, P(y) ==> t ∈ y) <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y)))) |- (t ∈ z <=> (∀(y, P(y) ==> t ∈ y)))
    ) by RightSubstIff.withParametersSimple(List((∀(y, P(y) ==> t ∈ y), (t ∈ x /\ ∀(y, P(y) ==> t ∈ y)))), lambda(form, t ∈ z <=> (form)))

    have((P(x), (t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y)))) |- t ∈ z <=> (∀(y, P(y) ==> t ∈ y))) by Cut(lhs, rhs)
    thenHave((P(x), ∀(t, (t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))))) |- t ∈ z <=> (∀(y, P(y) ==> t ∈ y))) by LeftForall
    thenHave((P(x), ∀(t, (t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))))) |- ∀(t, t ∈ z <=> (∀(y, P(y) ==> t ∈ y)))) by RightForall
    thenHave((P(x), ∀(t, (t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y))))) |- ∃(z, ∀(t, t ∈ z <=> (∀(y, P(y) ==> t ∈ y))))) by RightExists
    val cutRhs = thenHave((P(x), ∃(z, ∀(t, (t ∈ z <=> (t ∈ x /\ ∀(y, P(y) ==> t ∈ y)))))) |- ∃(z, ∀(t, t ∈ z <=> (∀(y, P(y) ==> t ∈ y))))) by LeftExists

    have(P(x) |- ∃(z, ∀(t, t ∈ z <=> (∀(y, P(y) ==> t ∈ y))))) by Cut(comprehensionSchema of (z := x, φ := lambda(t, ∀(y, P(y) ==> t ∈ y))), cutRhs)
    thenHave(∃(x, P(x)) |- ∃(z, ∀(t, t ∈ z <=> (∀(y, P(y) ==> t ∈ y))))) by LeftExists

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
    z ∈ (x ∩ y) <=> (z ∈ x /\ z ∈ y)
  ) {
    val forward = have(∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w) ==> (z ∈ x /\ z ∈ y)) subproof {
      have(∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w) |- ∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w)) by Hypothesis
      val seq = thenHave((∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w), w ∈ unorderedPair(x, y)) |- z ∈ w) by InstantiateForall(w)

      have((∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w), x ∈ unorderedPair(x, y), y ∈ unorderedPair(x, y)) |- z ∈ x /\ z ∈ y) by RightAnd(seq of (w := x), seq of (w := y))
      have((∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w), x ∈ unorderedPair(x, y)) |- z ∈ x /\ z ∈ y) by Cut(unorderedPairRightIntro, lastStep)
      have(∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w) |- z ∈ x /\ z ∈ y) by Cut(unorderedPairLeftIntro, lastStep)
    }

    val backward = have((z ∈ x /\ z ∈ y) ==> ∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w)) subproof {
      have(z ∈ x |- z ∈ x) by Hypothesis
      val seq = thenHave((z ∈ x, x === w) |- z ∈ w) by RightSubstEq.withParametersSimple(List((x, w)), lambda(w, z ∈ w))

      have((z ∈ x, w ∈ unorderedPair(x, y)) |- (z ∈ w, w === y)) by Cut(unorderedPairElim of (z := w), seq)
      have((z ∈ x, z ∈ y, w ∈ unorderedPair(x, y)) |- z ∈ w) by Cut(lastStep, seq of (x := y))
      thenHave((z ∈ x, z ∈ y) |- w ∈ unorderedPair(x, y) ==> z ∈ w) by RightImplies
      thenHave((z ∈ x, z ∈ y) |- ∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w)) by RightForall
    }

    have(∀(w, w ∈ unorderedPair(x, y) ==> z ∈ w) <=> (z ∈ x /\ z ∈ y)) by RightIff(forward, backward)
    thenHave(unorderedPair(x, y) =/= ∅ |- z ∈ intersection(unorderedPair(x, y)) <=> (z ∈ x /\ z ∈ y)) by Substitution.ApplyRules(intersectionMembership)
    have(z ∈ intersection(unorderedPair(x, y)) <=> (z ∈ x /\ z ∈ y)) by Cut(unorderedPairNonEmpty, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(setIntersection.shortDefinition)
  }

  /**
   * Lemma --- Binary Intersection Introduction Rule
   *
   *    `z ∈ x, z ∈ y ⊢ z ∈ x ∩ y`
   */
  val setIntersectionIntro = Lemma(
    (z ∈ x, z ∈ y) |- z ∈ (x ∩ y)
  ) {
    have(thesis) by Weakening(setIntersectionMembership)
  }

  /**
   * Lemma --- Binary Intersection Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ x /\ z ∈ y`
   */
  val setIntersectionElim = Lemma(
    z ∈ (x ∩ y) |- z ∈ x /\ z ∈ y
  ) {
    have(thesis) by Weakening(setIntersectionMembership)
  }

  /**
   * Lemma --- Binary Intersection Left Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ x`
   */
  val setIntersectionLeftElim = Lemma(
    z ∈ (x ∩ y) |- z ∈ x
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  /**
   * Lemma --- Binary Intersection Right Elimination Rule
   *
   *    `z ∈ x ∩ y ⊢ z ∈ y`
   */
  val setIntersectionRightElim = Lemma(
    z ∈ (x ∩ y) |- z ∈ y
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  /**
   * Lemma --- Binary Intersection Commutativity
   *
   *    `x ∩ y = y ∩ x`
   */
  val setIntersectionCommutativity = Lemma(
    x ∩ y === y ∩ x
  ) {
    have(z ∈ (x ∩ y) <=> z ∈ (y ∩ x)) by Substitution.ApplyRules(setIntersectionMembership)(setIntersectionMembership)
    thenHave(∀(z, z ∈ (x ∩ y) <=> z ∈ (y ∩ x))) by RightForall
    have(x ∩ y === y ∩ x) by Cut(lastStep, equalityIntro of (x := x ∩ y, y := y ∩ x))
  }

  /**
   * Lemma --- Binary Intersection Left Subset
   * 
   *   `x ∩ y ⊆ x`
   */
  val setIntersectionLeftSubset = Lemma(
    x ∩ y ⊆ x
  ) {
    have(z ∈ (x ∩ y) ==> z ∈ x) by RightImplies(setIntersectionLeftElim)
    thenHave(∀(z, z ∈ (x ∩ y) ==> z ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := x ∩ y, y := x))
  }

  /**
   * Lemma --- Binary Intersection Right Subset
   * 
   *   `x ∩ y ⊆ y`
   */
  val setIntersectionRightSubset = Lemma(
    (x ∩ y) ⊆ y
  ) {
    have(z ∈ (x ∩ y) ==> z ∈ y) by RightImplies(setIntersectionRightElim)
    thenHave(∀(z, z ∈ (x ∩ y) ==> z ∈ y)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := x ∩ y, y := y))
  }

  /**
   * Lemma --- Intersection with a subset
   * 
   *   `x ⊆ y ⊢ x ∩ y = x`
   */
  val setIntersectionOfSubsetForward = Lemma(
    x ⊆ y |- x ∩ y === x
  ) {
    have((z ∈ x, x ⊆ y) |- z ∈ (x ∩ y)) by Cut(subsetElim, setIntersectionIntro)
    thenHave(x ⊆ y |- z ∈ x ==> z ∈ (x ∩ y)) by RightImplies
    thenHave(x ⊆ y |- ∀(z, z ∈ x ==> z ∈ (x ∩ y))) by RightForall
    have(x ⊆ y |- x ⊆ (x ∩ y)) by Cut(lastStep, subsetIntro of (y := x ∩ y))
    have((x ⊆ y, (x ∩ y) ⊆ x) |- x === x ∩ y) by Cut(lastStep, subsetAntisymmetry of (y := x ∩ y))
    have(thesis) by Cut(setIntersectionLeftSubset, lastStep)
  }

  /**
   * Lemma --- Intersection with a subset
   * 
   *   `y ⊆ x ⊢ x ∩ y = y`
   */
  val setIntersectionOfSubsetBackward = Lemma(
    y ⊆ x |- x ∩ y === y
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionCommutativity)(setIntersectionOfSubsetForward of (x := y, y := x))
  }

  val setIntersectionIdempotence = Lemma(
    x ∩ x === x
  ) {
    have(thesis) by Cut(subsetReflexivity, setIntersectionOfSubsetForward of (y := x))
  }

  val setIntersectionLeftMonotonicity = Lemma(
    x ⊆ y |- (x ∩ z) ⊆ (y ∩ z)
  ) {
    have((x ⊆ y, w ∈ x, w ∈ z) |- w ∈ (y ∩ z)) by Cut(subsetElim of (z := w), setIntersectionIntro of (x := y, y := z, z := w))
    thenHave((x ⊆ y, w ∈ x /\ w ∈ z) |- w ∈ (y ∩ z)) by LeftAnd
    have((x ⊆ y, w ∈ (x ∩ z)) |- w ∈ (y ∩ z)) by Cut(setIntersectionElim of (z := w, y := z), lastStep)
    thenHave(x ⊆ y |- w ∈ (x ∩ z) ==> w ∈ (y ∩ z)) by RightImplies
    thenHave(x ⊆ y |- ∀(w, w ∈ (x ∩ z) ==> w ∈ (y ∩ z))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := x ∩ z, y := y ∩ z))
  }

  /**
   * Definition --- Disjoint Sets
   * 
   *   `disjoint(x, y) <=> x ∩ y = ∅`
   */
  val disjoint = DEF(x, y) --> (x ∩ y === ∅)

  /**
   * Lemma --- Disjoint definition unfolding
   * 
   *  `disjoint(x, y) ⊢ x ∩ y = ∅`
   */
  val disjointUnfold = Lemma(
    disjoint(x, y) |- x ∩ y === ∅
  ) {
    have(thesis) by Weakening(disjoint.definition)
  }

  /**
   * Lemma --- Disjoint definition folding
   * 
   *  `x ∩ y = ∅ ⊢ disjoint(x, y)`
   */
  val disjointFold = Lemma(
    x ∩ y === ∅ |- disjoint(x, y)
  ) {
    have(thesis) by Weakening(disjoint.definition)
  }

  /**
   * Lemma --- Disjoint Elimination Rule
   * 
   *  `disjoint(x, y), z ∈ x, z ∈ y ⊢ ⊥`
   */
  val disjointElim = Lemma(
    (disjoint(x, y), z ∈ x, z ∈ y) |- ()
  ) {
    have((x ∩ y === ∅, z ∈ (x ∩ y)) |- ()) by Restate.from(emptySetHasNoElements of (x := x ∩ y, y := z))
    have((x ∩ y === ∅, z ∈ x, z ∈ y) |- ()) by Cut(setIntersectionIntro of (x := x, y := y), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(disjoint.definition)
  }

  /**
   * Lemma --- Non Disjointn Elimination Rule
   * 
   * `¬disjoint(x, y) ⊢ ∃ z. z ∈ x ∧ z ∈ y`
   */
  val nonDisjointElim = Lemma(
    !disjoint(x, y) |- ∃(z, z ∈ x /\ z ∈ y)
  ) {
    have(z ∈ (x ∩ y) |- ∃(z, z ∈ x /\ z ∈ y)) by RightExists(setIntersectionElim) 
    thenHave(∃(z, z ∈ (x ∩ y)) |- ∃(z, z ∈ x /\ z ∈ y)) by LeftExists
    have(x ∩ y =/= ∅ |- ∃(z, z ∈ x /\ z ∈ y)) by Cut(nonEmptySetHasAnElement of (x := x ∩ y), lastStep)
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
    have((x ∩ y === ∅) <=> (x ∩ y === ∅)) by Restate
    thenHave((x ∩ y === ∅) <=> (y ∩ x === ∅)) by Substitution.ApplyRules(setIntersectionCommutativity)
    thenHave(thesis) by Substitution.ApplyRules(disjoint.definition, disjoint.definition of (x := y, y := x))
  }

  val nonDisjointSingleton = Lemma(
    !disjoint(y, singleton(x)) |- x ∈ y
  ) {
    have(z ∈ y |- z ∈ y) by Hypothesis
    thenHave((z ∈ singleton(x), z ∈ y) |- x ∈ y) by Substitution.ApplyRules(singletonElim of (y := z))
    thenHave(z ∈ singleton(x) /\ z ∈ y |- x ∈ y) by LeftAnd
    thenHave(∃(z, z ∈ singleton(x) /\ z ∈ y) |- x ∈ y) by LeftExists
    have(thesis) by Cut(nonDisjointElim of (x := y, y := singleton(x)), lastStep)
  }


  /**
   * Lemma --- Set Difference Uniqueness
   * 
   *   `∃! z. ∀ t. t ∈ z <=> (t ∈ x ∧ ! t ∈ y)`
   */
  val setDifferenceUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> (t ∈ x /\ t ∉ y)))
  ) {
    have(∃!(z, ∀(t, t ∈ z <=> (t ∈ x /\ t ∉ y)))) by UniqueComprehension(x, lambda(t, t ∉ y))
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
  val setDifference = DEF(x, y) --> The(z, ∀(t, t ∈ z <=> (t ∈ x /\ t ∉ y)))(setDifferenceUniqueness)


  extension (x: Term) {
    infix def \ (y: Term) = setDifference(x, y)
  }

  /**
   * Lemma --- Set Difference Membership
   *
   *    `z ∈ x \ y <=> z ∈ x ∧ ! z ∈ y`
   */
  val setDifferenceMembership = Lemma(
    z ∈ (x \ y) <=> (z ∈ x /\ z ∉ y)
  ) {
    have(∀(z, z ∈ (x \ y) <=> (z ∈ x /\ z ∉ y))) by InstantiateForall(x \ y)(setDifference.definition)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- Set Difference Introduction Rule
   *
   *    `z ∈ x, z ∉ y ⊢ z ∈ x \ y`
   */
  val setDifferenceIntro = Lemma(
    (z ∈ x, z ∉ y) |- z ∈ (x \ y)
  ) {
    have(thesis) by Weakening(setDifferenceMembership)
  }

  /**
   * Lemma --- Set Difference Elimination Rule
   *
   *    `z ∈ x \ y ⊢ z ∈ x ∧ z ∉ y`
   */
  val setDifferenceElim = Lemma(
    z ∈ (x \ y) |- z ∈ x /\ z ∉ y
  ) {
    have(thesis) by Weakening(setDifferenceMembership)
  }

  val setDifferenceSubsetDomain = Lemma(
    (x \ y) ⊆ x
  ) {
    have(z ∈ (x \ y) ==> z ∈ x) by Weakening(setDifferenceElim)
    thenHave(∀(z, z ∈ (x \ y) ==> z ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := x \ y, y := x))
  }

  val setDifferenceEmpty = Lemma(
    ((x \ y) === ∅) <=> x ⊆ y
  ) {
    val forward = have(x ⊆ y ==> ((x \ y) === ∅)) subproof {
      have(z ∈ (x \ y) |- !(z ∈ x ==> z ∈ y)) by Weakening(setDifferenceElim)
      thenHave(z ∈ (x \ y) |- ∃(z, !(z ∈ x ==> z ∈ y))) by RightExists
      thenHave(∃(z, z ∈ (x \ y)) |- !(∀(z, z ∈ x ==> z ∈ y))) by LeftExists
      thenHave(∃(z, z ∈ (x \ y)) |- !(x ⊆ y)) by Substitution.ApplyRules(subsetAxiom)
      have((x \ y) =/= ∅ |- !(x ⊆ y)) by Cut(nonEmptySetHasAnElement of (x := x \ y), lastStep)
    }
    
    val backward = have(((x \ y) === ∅) ==> x ⊆ y) subproof {
      have(z ∉ (x \ y) |- z ∈ x ==> z ∈ y) by Restate.from(setDifferenceIntro)
      have((x \ y) === ∅ |- z ∈ x ==> z ∈ y) by Cut(emptySetHasNoElements of (x := x \ y, y := z), lastStep)
      thenHave((x \ y) === ∅ |- ∀(z, z ∈ x ==> z ∈ y)) by RightForall
      have((x \ y) === ∅ |- x ⊆ y) by Cut(lastStep, subsetIntro)
    }

    have(thesis) by RightIff(forward, backward)
  }
  

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
    val forward = have(z ∈ union(pair(x, y)) ==> z ∈ unorderedPair(x, y)) subproof {

      val left = have(z ∈ unorderedPair(x, y) |- z ∈ unorderedPair(x, y)) by Hypothesis
      val right = have(z ∈ singleton(x) |- z ∈ unorderedPair(x, y)) by Substitution.ApplyRules(singletonElim)(unorderedPairLeftIntro)
      have(z ∈ (unorderedPair(x, y) ∪ singleton(x)) |- (z ∈ unorderedPair(x, y), z ∈ singleton(x))) by Cut(setUnionElim of (x := unorderedPair(x, y), y := singleton(x)), left)
      have(z ∈ (unorderedPair(x, y) ∪ singleton(x)) |- z ∈ unorderedPair(x, y)) by Cut(lastStep, right)
      thenHave(z ∈ union(unorderedPair(unorderedPair(x, y), singleton(x))) |- z ∈ unorderedPair(x, y)) by Substitution.ApplyRules(setUnion.shortDefinition)
      thenHave(z ∈ union(pair(x, y)) |- z ∈ unorderedPair(x, y)) by Substitution.ApplyRules(pair.shortDefinition)
    }

    val backward = have(z ∈ unorderedPair(x, y) ==> z ∈ union(pair(x, y))) subproof {
      have(z ∈ unorderedPair(x, y) |- z ∈ union(unorderedPair(unorderedPair(x, y), singleton(x)))) by Substitution.ApplyRules(setUnion.shortDefinition)(setUnionLeftIntro of (x := unorderedPair(x, y), y := singleton(x)))
      thenHave(z ∈ unorderedPair(x, y) |- z ∈ union(pair(x, y)) ) by Substitution.ApplyRules(pair.shortDefinition)
    }

    have(z ∈ union(pair(x, y)) <=> z ∈ unorderedPair(x, y)) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ union(pair(x, y)) <=> z ∈ unorderedPair(x, y))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(pair(x, y)), y := unorderedPair(x, y)))
  }

  /**
   * Lemma --- If pair belongs to a set ifThe elements of an ordered pair are in the union of the union of the pair.
   *
   *    `(x, y) ∈ z |- x ∈ ∪ ∪ z /\ y ∈ ∪ ∪ z`
   */
  val pairComponentsInUnionUnion = Lemma(
    pair(x, y) ∈ z |- x ∈ union(union(z)) /\ y ∈ union(union(z))
  ) {
    have(unorderedPair(unorderedPair(x, y), singleton(x)) ∈ z |- unorderedPair(x, y) ∈ union(z)) by Weakening(unorderedPairElementsInUnion of (x := unorderedPair(x, y), y := singleton(x)))
    have(unorderedPair(unorderedPair(x, y), singleton(x)) ∈ z |- x ∈ union(union(z)) /\ y ∈ union(union(z))) by Cut(lastStep, unorderedPairElementsInUnion of (z := union(z)))
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
    have(singleton(x) ⊆ unorderedPair(x, y)) by Substitution.ApplyRules(singletonSubset)(unorderedPairLeftIntro)
    have(unorderedPair(x, y) ∩ singleton(x) === singleton(x)) by Cut(lastStep, setIntersectionOfSubsetBackward of (x := unorderedPair(x, y), y := singleton(x)))
    thenHave(intersection(unorderedPair(unorderedPair(x, y), singleton(x))) === singleton(x)) by Substitution.ApplyRules(setIntersection.shortDefinition)
    thenHave(intersection(pair(x, y)) === singleton(x)) by Substitution.ApplyRules(pair.shortDefinition) 
  }

  val foundation = Lemma(
    x =/= ∅ |- ∃(y, y ∈ x /\ ∀(z, z ∈ x ==> z ∉ y))
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
    x ∉ x
  ) {
    val foundation = have(singleton(x) =/= ∅ |- ∃(y, y ∈ singleton(x) /\ ∀(z, z ∈ singleton(x) ==> z ∉ y))) by Restate.from(foundationAxiom of (x := singleton(x)))
    have((x ∈ singleton(x) ==> x ∉ y, x ∈ singleton(x), x ∈ y) |- ()) by Restate
    have((x ∈ singleton(x) ==> x ∉ y, x ∈ y) |- ()) by Cut(singletonIntro, lastStep)
    thenHave((x === y, x ∈ singleton(x) ==> x ∉ y, x ∈ x) |- ()) by LeftSubstEq.withParametersSimple(List((x, y)), lambda(y, x ∈ y))
    have((y ∈ singleton(x), x ∈ singleton(x) ==> x ∉ y, x ∈ x) |- ()) by Cut(singletonElim, lastStep)
    thenHave((y ∈ singleton(x), ∀(z, z ∈ singleton(x) ==> z ∉ y), x ∈ x) |- ()) by LeftForall
    thenHave((y ∈ singleton(x), ∀(z, z ∈ singleton(x) ==> z ∉ y)) |- x ∉ x) by RightNot
    thenHave(y ∈ singleton(x) /\ ∀(z, z ∈ singleton(x) ==> z ∉ y) |- x ∉ x) by LeftAnd
    thenHave(∃(y, y ∈ singleton(x) /\ ∀(z, z ∈ singleton(x) ==> z ∉ y)) |- x ∉ x) by LeftExists
    have(singleton(x) =/= ∅ |- x ∉ x) by Cut(foundation, lastStep)
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
    ∀(z, z ∈ x) |- ()
  ) {
    have(∃(z, z ∉ x)) by RightExists(selfNonMembership)
  }

  /**
    * Lemma --- The membership relation is asymmetric.
    * 
    *   `x ∈ y, y ∈ x ⊢ ⊥`
    */
  val membershipAsymmetry = Lemma(
    (x ∈ y, y ∈ x) |- ()
  ) {
    val u = unorderedPair(x, y)

    val minimal = have(∃(w, w ∈ u /\ ∀(z, z ∈ u ==> z ∉ w))) by Cut(unorderedPairNonEmpty, foundation of (x := u))

    have(y ∈ x |- y ∈ x) by Hypothesis
    have(y ∈ x |- y ∈ u /\ y ∈ x) by RightAnd(lastStep, unorderedPairRightIntro) 
    thenHave((y ∈ x, z === x) |- y ∈ u /\ y ∈ z) by RightSubstEq.withParametersSimple(List((z, x)), lambda(z, y ∈ u /\ y ∈ z))
    val left = thenHave((y ∈ x, z === x) |- ∃(w, w ∈ u /\ w ∈ z)) by RightExists

    have(x ∈ y |- x ∈ y) by Hypothesis
    have(x ∈ y |- x ∈ u /\ x ∈ y) by RightAnd(lastStep, unorderedPairLeftIntro) 
    thenHave((x ∈ y, z === y) |- x ∈ u /\ x ∈ z) by RightSubstEq.withParametersSimple(List((z, y)), lambda(z, x ∈ u /\ x ∈ z))
    val right = thenHave((x ∈ y, z === y) |- ∃(w, w ∈ u /\ w ∈ z)) by RightExists

    have((y ∈ x, z ∈ u) |- (∃(w, w ∈ u /\ w ∈ z), z === y)) by Cut(unorderedPairElim, left)
    have((x ∈ y, y ∈ x, z ∈ u) |- ∃(w, w ∈ u /\ w ∈ z)) by Cut(lastStep, right) 
    thenHave((x ∈ y, y ∈ x) |- z ∈ u ==> ∃(w, w ∈ u /\ w ∈ z)) by RightImplies
    thenHave((x ∈ y, y ∈ x) |- ∀(z, z ∈ u ==> ∃(w, w ∈ u /\ w ∈ z)) ) by RightForall
    have(thesis) by RightAnd(lastStep, minimal)
  }

  val pairInPowerPowerSet = Lemma(
    pair(x, y) ∈ 𝓟(𝓟(z)) <=> (x ∈ z /\ y ∈ z) 
  ) {
    have((x ∈ z /\ x ∈ z /\ y ∈ z) <=> (x ∈ z /\ y ∈ z)) by Restate
    thenHave((x ∈ z <=> singleton(x) ∈ 𝓟(z), (x ∈ z /\ y ∈ z) <=> unorderedPair(x, y) ∈ 𝓟(z)) |- (singleton(x) ∈ 𝓟(z) /\ unorderedPair(x, y) ∈ 𝓟(z)) <=> (x ∈ z /\ y ∈ z)) by RightSubstIff.withParametersSimple(
      List((x ∈ z, singleton(x) ∈ 𝓟(z)), (x ∈ z /\ y ∈ z, unorderedPair(x, y) ∈ 𝓟(z))), lambda((h, q), (h /\ q) <=> (x ∈ z /\ y ∈ z))
    )
    have(x ∈ z <=> singleton(x) ∈ 𝓟(z) |- (singleton(x) ∈ 𝓟(z) /\ unorderedPair(x, y) ∈ 𝓟(z)) <=> (x ∈ z /\ y ∈ z)) by Cut(unorderedPairInPowerSet, lastStep)
    have((singleton(x) ∈ 𝓟(z) /\ unorderedPair(x, y) ∈ 𝓟(z)) <=> (x ∈ z /\ y ∈ z)) by Cut(singletonInPowerSet of (y := z), lastStep)
    thenHave(unorderedPair(unorderedPair(x, y), singleton(x)) ∈ 𝓟(𝓟(z)) <=> (x ∈ z /\ y ∈ z)) by Substitution.ApplyRules(unorderedPairInPowerSet of (x := unorderedPair(x, y), y := singleton(x), z := 𝓟(z)))
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

  val fst = firstInPair

  /**
   * Lemma --- The [[firstInPair]] operation when applied to an ordered pair
   * produces the first element of the pair.
   *
   *    `first((x, y)) = x`
   */
  val firstInPairReduction = Lemma(
    (fst(pair(x, y)) === x)
  ) {
    have(union(intersection(pair(x, y))) === x) by Substitution.ApplyRules(pairIntersection)(unionSingleton)
    thenHave(thesis) by Substitution.ApplyRules(fst.shortDefinition)
  }

  val secondInPairSingletonUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> (t ∈ union(p) /\ ((union(p) =/= intersection(p)) ==> t ∉ intersection(p)))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(t, ((union(p) =/= intersection(p)) ==> t ∉ intersection(p))))
  }

  /**
   * See [[secondInPair]].
   */
  val secondInPairSingleton =
    DEF(p) --> The(z, ∀(t, t ∈ z <=> (t ∈ union(p) /\ (t ∈ intersection(p) ==> (union(p) === intersection(p))))))(secondInPairSingletonUniqueness)

  /**
   * The second element of an ordered [[pair]] ---
   *
   *    `second p = ∪ {x ∈ ∪ p | ∪ p != ∩ p ⟹ !x ∈ ∩ p} = ∪ (secondSingleton p)`
   *
   * There is a more naive definition: `second p = ∪ (∪ p - (first p))`.
   * If `p = (a, b) = {{a}, {a, b}}`, `∪ p = {a, b}`, and `∪ p - (first p)
   * = {a, b} - {a} = {b}`, the `∪` at the top level reduces this to `b`.
   * However, this fails when `a = b`, and returns the [[∅]].
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[secondInPairReduction]].
   *
   * @see https://en.wikipedia.org/wiki/Ordered_pair#Kuratowski's_definition
   */
  val secondInPair = DEF(p) --> union(secondInPairSingleton(p))

  val snd = secondInPair

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
      ∀(
        t,
        t ∈ secondInPairSingleton(pair(x, y)) <=> (t ∈ union(pair(x, y)) /\ (t ∈ intersection(pair(x, y)) ==> (union(pair(x, y)) === intersection(pair(x, y)))))
      )
    ) by InstantiateForall(secondInPairSingleton(pair(x, y)))(secondInPairSingleton.definition of (p := pair(x, y)))
    thenHave(
      z ∈ secondInPairSingleton(pair(x, y)) <=> (z ∈ union(pair(x, y)) /\ (z ∈ intersection(pair(x, y)) ==> (union(pair(x, y)) === intersection(pair(x, y)))))
    ) by InstantiateForall(z)
    thenHave(
      z ∈ secondInPairSingleton(pair(x, y)) <=> (z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (unorderedPair(x, y) === singleton(x))))
    ) by Substitution.ApplyRules(unionOfOrderedPair, pairIntersection)
    val iff = thenHave(
      z ∈ secondInPairSingleton(pair(x, y)) <=> (z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (x === y)))
    ) by Substitution.ApplyRules(singletonEqualsUnorderedPair of (y := x, z := y))

    val forward = have((z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (x === y))) ==> z ∈ singleton(y)) subproof {
      have((z ∈ singleton(x) ==> (x === y), z ∈ singleton(x)) |- x === y) by Restate
      thenHave((z ∈ singleton(x) ==> (x === y), z === x, x ∈ singleton(x)) |- x === y) by LeftSubstEq.withParametersSimple(List((z, x)), lambda(z, z ∈ singleton(x)))
      have((z ∈ singleton(x) ==> (x === y), z === x) |- x === y) by Cut(singletonIntro, lastStep)
      have((z ∈ singleton(x) ==> (x === y), z === x) |- z === y) by Cut(lastStep, equalityTransitivity of (x := z, y := x, z := y))
      have((z ∈ singleton(x) ==> (x === y), z ∈ unorderedPair(x, y)) |- z === y) by Cut(unorderedPairElim, lastStep)
      thenHave((z ∈ singleton(x) ==> (x === y), z ∈ unorderedPair(x, y)) |- z ∈ singleton(y)) by Substitution.ApplyRules(singletonMembership of (y := z, x := y))
    }
    val backward = have(z ∈ singleton(y) ==> (z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (x === y)))) subproof {
      val left = have(z ∈ singleton(y) |- z ∈ unorderedPair(x, y)) by Substitution.ApplyRules(singletonElim)(unorderedPairRightIntro)

      have((z ∈ singleton(x), z ∈ singleton(y)) |- x === y) by Substitution.ApplyRules(singletonElim of (y := z, x := y))(singletonElim of (y := z))
      val right = thenHave(z ∈ singleton(y) |- z ∈ singleton(x) ==> (x === y)) by RightImplies

      have(z ∈ singleton(y) |- z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (x === y))) by RightAnd(left, right)
    }

    have((z ∈ unorderedPair(x, y) /\ (z ∈ singleton(x) ==> (x === y))) <=> z ∈ singleton(y)) by RightIff(forward, backward)
    thenHave(z ∈ secondInPairSingleton(pair(x, y)) <=> z ∈ singleton(y)) by Substitution.ApplyRules(iff)
    thenHave(∀(z, z ∈ secondInPairSingleton(pair(x, y)) <=> z ∈ singleton(y))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := secondInPairSingleton(pair(x, y)), y := singleton(y)))
  }

  /**
   * Lemma --- The [[snd]] operation when applied to an ordered pair
   * produces the second element of the pair.
   *
   *    `second((x, y)) = y`
   */
  val secondInPairReduction = Lemma(
    snd(pair(x, y)) === y
  ) {
    have(union(secondInPairSingleton(pair(x, y))) === y) by Substitution.ApplyRules(secondInPairSingletonReduction)(unionSingleton of (x := y))
    thenHave(thesis) by Substitution.ApplyRules(snd.shortDefinition)
  }

  /**
   * Lemma --- Pair Reconstruction
   *
   * If `x` is a pair (i.e. `= (c, d)` for some `c` and `d`), then pair element
   * projection on it is invertible, so `x = (fst x, snd x)`.
   */
  val pairReconstruction = Lemma(
    ∃(y, ∃(z, pair(y, z) === x)) |- x === pair(fst(x), snd(x))
  ) {
    val left = have(pair(y, z) === x |- fst(x) === y) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(x, fst(x) === y))(firstInPairReduction of (x := y, y := z))
    val right = have(pair(y, z) === x |- snd(x) === z) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(x, snd(x) === z))(secondInPairReduction of (x := y, y := z))
    have(pair(y, z) === x |- (fst(x) === y) /\ (snd(x) === z)) by RightAnd(left, right)
    thenHave(pair(y, z) === x |- pair(y, z) === pair(fst(x), snd(x))) by Substitution.ApplyRules(pairExtensionality of (a := y, b := z, c := fst(x), d := snd(x)))
    thenHave(pair(y, z) === x |- x === pair(fst(x), snd(x))) by RightSubstEq.withParametersSimple(List((pair(y, z), x)), lambda(z, z === pair(fst(x), snd(x))))
    thenHave(∃(z, pair(y, z) === x) |- x === pair(fst(x), snd(x))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Cartesian Product
   */

  val cartesianProductUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> (t ∈  𝓟(𝓟(x ∪ y)) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ a ∈ x /\ b ∈ y)))))
  ) {
    have(∃!(z, ∀(t, t ∈ z <=> (t ∈ 𝓟(𝓟(x ∪ y)) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ a ∈ x /\ b ∈ y)))))) by UniqueComprehension(
      𝓟(𝓟(x ∪ y)),
      lambda(t, ∃(a, ∃(b, (t === pair(a, b)) /\ a ∈ x /\ b ∈ y)))
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
    DEF(x, y) --> The(z, ∀(t, t ∈ z <=> (t ∈ 𝓟(𝓟(x ∪ y)) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ a ∈ x /\ b ∈ y)))))(cartesianProductUniqueness)

  extension (x: Term)
    def × (y: Term): Term = cartesianProduct(x, y)


  val elemOfPowerPowerUnion = Lemma(
    ∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y)) |- p ∈ 𝓟(𝓟(x ∪ y))
  ) {
    have((a ∈ (x ∪ y), b ∈ (x ∪ y)) |- pair(a, b) ∈ 𝓟(𝓟(x ∪ y))) by Weakening(pairInPowerPowerSet of (x := a, y := b, z := x ∪ y))
    have((a ∈ x, b ∈ (x ∪ y)) |- pair(a, b) ∈ 𝓟(𝓟(x ∪ y))) by Cut(setUnionLeftIntro of (z := a), lastStep)
    have((a ∈ x, b ∈ y) |- pair(a, b) ∈  𝓟(𝓟(x ∪ y))) by Cut(setUnionRightIntro of (z := b), lastStep)
    thenHave((p === pair(a, b), a ∈ x, b ∈ y) |- p ∈ 𝓟(𝓟(x ∪ y))) by RightSubstEq.withParametersSimple(List((p, pair(a, b))), lambda(p, p ∈ 𝓟(𝓟(x ∪ y))))
    thenHave((p === pair(a, b)) /\ a ∈ x /\ b ∈ y |- p ∈ 𝓟(𝓟(x ∪ y))) by Restate
    thenHave(∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y) |- p ∈ 𝓟(𝓟(x ∪ y))) by LeftExists
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
    p ∈ (x × y) <=> ∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y))
  ) {
    val powerPowerSet = have(∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y)) ==> p ∈ 𝓟(𝓟(x ∪ y))) by RightImplies(elemOfPowerPowerUnion)

    have(∀(p, p ∈ (x × y) <=> (p ∈ 𝓟(𝓟(x ∪ y)) /\ ∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y))))) by InstantiateForall(
      x × y
    )(cartesianProduct.definition)
    thenHave(p ∈ (x × y) <=> (p ∈ 𝓟(𝓟(x ∪ y)) /\ ∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y)))) by InstantiateForall(p)
    thenHave(∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y)) ==> p ∈ 𝓟(𝓟(x ∪ y)) |- p ∈ (x × y) <=> ∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y))) by Tautology
    have(thesis) by Cut(powerPowerSet, lastStep)
  }

  val pairReconstructionInCartesianProduct = Lemma(
    p ∈ (x × y) |- p === pair(fst(p), snd(p))
  ) {
    have((p === pair(a, b)) /\ a ∈ x /\ b ∈ y |- p === pair(a, b)) by Restate
    thenHave((p === pair(a, b)) /\ a ∈ x /\ b ∈ y |- ∃(b, p === pair(a, b))) by RightExists
    thenHave(∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y) |- ∃(b, p === pair(a, b))) by LeftExists
    thenHave(∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y) |- ∃(a, ∃(b, p === pair(a, b)))) by RightExists
    thenHave(∃(a, ∃(b, (p === pair(a, b)) /\ a ∈ x /\ b ∈ y)) |- ∃(a, ∃(b, p === pair(a, b)))) by LeftExists
    thenHave(p ∈ (x × y) |- ∃(a, ∃(b, p === pair(a, b)))) by Substitution.ApplyRules(elemOfCartesianProduct)
    have(thesis) by Cut(lastStep, pairReconstruction of (x := p))
  }

  val cartesianProductIntro = Lemma(
    (a ∈ x, b ∈ y) |- pair(a, b) ∈ (x × y)
  ) {
    have((a ∈ x, b ∈ y) |- (pair(a, b) === pair(a, b)) /\ a ∈ x /\ b ∈ y) by Restate
    thenHave((a ∈ x, b ∈ y) |- ∃(d, (pair(a, b) === pair(a, d)) /\ a ∈ x /\ d ∈ y)) by RightExists
    thenHave((a ∈ x, b ∈ y) |- ∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ c ∈ x /\ d ∈ y))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct)
  }

  val cartesianProductElimPair = Lemma(
    pair(a, b) ∈ (x × y) |- a ∈ x /\ b ∈ y
  ) {
    have(c ∈ x /\ d ∈ y |- c ∈ x /\ d ∈ y) by Hypothesis
    thenHave((a === c, b === d, c ∈ x /\ d ∈ y) |- a ∈ x /\ b ∈ y) by RightSubstEq.withParametersSimple(List((a, c), (b, d)), lambda(Seq(a, b), a ∈ x /\ b ∈ y))
    thenHave((a === c) /\ (b === d) /\ c ∈ x /\ d ∈ y |- a ∈ x /\ b ∈ y) by Restate
    thenHave((pair(a, b) === pair(c, d)) /\ c ∈ x /\ d ∈ y |- a ∈ x /\ b ∈ y) by Substitution.ApplyRules(pairExtensionality)
    thenHave(∃(d, (pair(a, b) === pair(c, d)) /\ c ∈ x /\ d ∈ y) |- a ∈ x /\ b ∈ y) by LeftExists
    thenHave(∃(c, ∃(d, (pair(a, b) === pair(c, d)) /\ c ∈ x /\ d ∈ y)) |- a ∈ x /\ b ∈ y) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct)
  }

  /**
   * Lemma --- Cartesian Product Elimination Rule
   *
   *   `p ∈ x * y ⇒ fst p ∈ x ∧ snd p ∈ y`
   */
  val cartesianProductElim = Lemma(
    p ∈ (x × y) |- fst(p) ∈ x /\ snd(p) ∈ y
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInCartesianProduct)(cartesianProductElimPair of (a := fst(p), b := snd(p)))
  }

  val cartesianProductMembershipPair = Lemma(
    pair(a, b) ∈ (x × y) <=> (a ∈ x /\ b ∈ y)
  ) {
    val forward = have(pair(a, b) ∈ (x × y) ==> (a ∈ x /\ b ∈ y)) by Restate.from(cartesianProductElimPair)
    val backward = have((a ∈ x /\ b ∈ y) ==> pair(a, b) ∈ (x × y)) by Restate.from(cartesianProductIntro)
    have(thesis) by RightIff(forward, backward)
  }

  val cartesianProductLeftEmpty = Lemma(
    ∅ × y === ∅
  ) {
    have(fst(p) ∈ ∅ /\ snd(p) ∈ y |- ()) by Weakening(emptySetAxiom of (x := fst(p)))
    have(p ∈ (∅ × y) |- ()) by Cut(cartesianProductElim of (x := ∅), lastStep)
    thenHave(∃(p, p ∈ (∅ × y)) |- ()) by LeftExists
    have(∅ × y =/= ∅ |- ()) by Cut(nonEmptySetHasAnElement of (x := ∅ × y), lastStep)
  }

  val cartesianProductRightEmpty = Lemma(
    x × ∅ === ∅
  ) {
    have(fst(p) ∈ x /\ snd(p) ∈ ∅ |- ()) by Weakening(emptySetAxiom of (x := snd(p)))
    have(p ∈ (x × ∅) |- ()) by Cut(cartesianProductElim of (y := ∅), lastStep)
    thenHave(∃(p, p ∈ (x × ∅)) |- ()) by LeftExists
    have(x × ∅ =/= ∅ |- ()) by Cut(nonEmptySetHasAnElement of (x := x × ∅), lastStep)
  }

  val cartesianProductSubset = Lemma(
    (w ⊆ y, x ⊆ z) |- (w × x) ⊆ (y × z)
  ) {
    have((fst(p) ∈ w, snd(p) ∈ z, w ⊆ y) |- pair(fst(p), snd(p)) ∈ (y × z)) by
      Cut(subsetElim of (z := fst(p), x := w), cartesianProductIntro of (a := fst(p), b := snd(p), x := y, y := z))
    have((fst(p) ∈ w, snd(p) ∈ x, w ⊆ y, x ⊆ z) |- pair(fst(p), snd(p)) ∈ (y × z)) by
      Cut(subsetElim of (z := snd(p), y := z), lastStep)
    thenHave((fst(p) ∈ w /\ snd(p) ∈ x, w ⊆ y, x ⊆ z) |- pair(fst(p), snd(p)) ∈ (y × z)) by
      LeftAnd
    have((p ∈ (w × x), w ⊆ y, x ⊆ z) |- pair(fst(p), snd(p)) ∈ (y × z)) by Cut(cartesianProductElim of (x := w, y := x), lastStep)
    thenHave((p ∈ (w × x), w ⊆ y, x ⊆ z) |- p ∈ (y × z)) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := w, y := x))
    thenHave((w ⊆ y, x ⊆ z) |- p ∈ (w × x) ==> p ∈ (y × z)) by RightImplies
    thenHave((w ⊆ y, x ⊆ z) |- ∀(p, p ∈ (w × x) ==> p ∈ (y × z))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := w × x, y := y × z))
  }

  val singletonCartesianProduct = Lemma(
    singleton(pair(x, y)) === singleton(x) × singleton(y)
  ) {
    val forward = have(p ∈ singleton(pair(x, y)) ==> p ∈ (singleton(x) × singleton(y)))subproof {
      have(y ∈ singleton(y) |- pair(x, y) ∈ (singleton(x) × singleton(y))) by
        Cut(singletonIntro, cartesianProductIntro of (a := x, b := y, x := singleton(x), y := singleton(y)))
      have(pair(x, y) ∈ (singleton(x) × singleton(y))) by Cut(singletonIntro of (x := y), lastStep) 
      thenHave(p ∈ singleton(pair(x, y)) |- p ∈ (singleton(x) × singleton(y))) by
        Substitution.ApplyRules(singletonElim) 
    }

    val backward = have(p ∈ (singleton(x) × singleton(y)) ==> p ∈ singleton(pair(x, y))) subproof {
      have((fst(p) === x, snd(p) === y) |- pair(fst(p), snd(p)) ∈ singleton(pair(x, y))) by
        Substitution.ApplyRules(fst(p) === x, snd(p) === y)(singletonIntro of (x := pair(x, y)))
      have((fst(p) ∈ singleton(x), snd(p) === y) |- pair(fst(p), snd(p)) ∈ singleton(pair(x, y)) )by
        Cut(singletonElim of (y := fst(p)), lastStep)
      have((fst(p) ∈ singleton(x), snd(p) ∈ singleton(y)) |- pair(fst(p), snd(p)) ∈ singleton(pair(x, y))) by 
        Cut(singletonElim of (x := y, y := snd(p)), lastStep)
      thenHave(fst(p) ∈ singleton(x) /\ snd(p) ∈ singleton(y) |- pair(fst(p), snd(p)) ∈ singleton(pair(x, y))) by LeftAnd
      have(p ∈ (singleton(x) × singleton(y)) |- pair(fst(p), snd(p)) ∈ singleton(pair(x, y))) by
        Cut(cartesianProductElim of (x := singleton(x), y := singleton(y)), lastStep)
      thenHave(p ∈ (singleton(x) × singleton(y)) |- p ∈ singleton(pair(x, y))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := singleton(x), y := singleton(y)))
    }

    have(p ∈ singleton(pair(x, y)) <=> p ∈ (singleton(x) × singleton(y))) by RightIff(forward, backward)
    thenHave(∀(p, p ∈ singleton(pair(x, y)) <=> p ∈ (singleton(x) × singleton(y)))) by RightForall
    have(singleton(pair(x, y)) === singleton(x) × singleton(y)) by Cut(lastStep, equalityIntro of (x := singleton(pair(x, y)), y := singleton(x) × singleton(y)))
  }

  val pairInSingletonCartesianProduct = Lemma(
    pair(x, y) ∈ (singleton(x) × singleton(y))
  ){
    have(thesis) by Substitution.ApplyRules(singletonCartesianProduct)(singletonIntro of (x := pair(x, y)))
  }

  val cartesianProductLeftUnion = Lemma(
    (a ∪ b) × c === ((a × c) ∪ (b × c))
  ) {
    val forward = have(p ∈ ((a ∪ b) × c) ==> p ∈ ((a × c) ∪ (b × c))) subproof {
      val hyp = have(snd(p) ∈ c |- snd(p) ∈ c) by Hypothesis
      val cartProdIntro = have(fst(p) ∈ a /\ snd(p) ∈ c |- pair(fst(p), snd(p)) ∈ (a × c)) by LeftAnd(
        cartesianProductIntro of (a := fst(p), b := snd(p), x := a, y := c)
      )

      have((fst(p) ∈ (a ∪ b), snd(p) ∈ c) |- (fst(p) ∈ a, fst(p) ∈ b /\ snd(p) ∈ c)) by RightAnd(
        setUnionElim of (z := fst(p), x := a, y := b),
        hyp
      )
      have((fst(p) ∈ (a ∪ b), snd(p) ∈ c) |- (fst(p) ∈ a /\ snd(p) ∈ c, fst(p) ∈ b /\ snd(p) ∈ c)) by RightAnd(
        lastStep,
        hyp
      )
      thenHave((fst(p) ∈ (a ∪ b) /\ snd(p) ∈ c) |- (fst(p) ∈ a /\ snd(p) ∈ c, fst(p) ∈ b /\ snd(p) ∈ c)) by LeftAnd
      have(p ∈ ((a ∪ b) × c) |- (fst(p) ∈ a /\ snd(p) ∈ c, fst(p) ∈ b /\ snd(p) ∈ c)) by
        Cut(cartesianProductElim of (a := fst(p), b := snd(p), x := a ∪ b, y := c), lastStep)
      have(p ∈ ((a ∪ b) × c) |- (pair(fst(p), snd(p)) ∈ (a × c), fst(p) ∈ b /\ snd(p) ∈ c)) by
        Cut(lastStep, cartProdIntro)
      have(p ∈ ((a ∪ b) × c) |- (pair(fst(p), snd(p)) ∈ (a × c), pair(fst(p), snd(p)) ∈ (b × c))) by
        Cut(lastStep, cartProdIntro of (a := b))
      thenHave(p ∈ ((a ∪ b) × c) |- (p ∈ (a × c), p ∈ (b × c))) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a ∪ b, y := c))
      have(p ∈ ((a ∪ b) × c) |- (p ∈ ((a × c) ∪ (b × c)), p ∈ (b × c))) by
        Cut(lastStep, setUnionLeftIntro of (x := a × c, y := b × c, z := p))
      have(p ∈ ((a ∪ b) × c) |- p ∈ ((a × c) ∪ (b × c))) by
        Cut(lastStep, setUnionRightIntro of (x := a × c, y := b × c, z := p))
    }
    val backward = have(p ∈ ((a × c) ∪ (b × c)) ==> p ∈ ((a ∪ b) × c)) subproof {

      val cartesianProdIntro = have(fst(p) ∈ (a ∪ b) /\ snd(p) ∈ c |- pair(fst(p), snd(p)) ∈ ((a ∪ b) × c)) by
        LeftAnd(cartesianProductIntro of (a := fst(p), b := snd(p), x := a ∪ b, y := c))

      val unElim = have(p ∈ ((a × c) ∪ (b × c)) |- p ∈ (a × c) \/ (p ∈ (b × c))) by
        RightOr(setUnionElim of (z := p, x := a × c, y := (b × c)))

      have(p ∈ ((a × c) ∪ (b × c)) |- (fst(p) ∈ a /\ snd(p) ∈ c, p ∈ (b × c))) by
        Cut(setUnionElim of (z := p, x := a × c, y := b × c), cartesianProductElim of (x := a, y := c))
      have(p ∈ ((a × c) ∪ (b × c)) |- (fst(p) ∈ a /\ snd(p) ∈ c, fst(p) ∈ b /\ snd(p) ∈ c)) by
        Cut(lastStep, cartesianProductElim of (x := b, y := c))
      thenHave(p ∈ ((a × c) ∪ (b × c)) |- (fst(p) ∈ a \/ (fst(p) ∈ b)) /\ snd(p) ∈ c) by Tautology
      thenHave(p ∈ ((a × c) ∪ (b × c)) |- fst(p) ∈ (a ∪ b) /\ snd(p) ∈ c) by Substitution.ApplyRules(setUnionMembership)
      val beforeSubst =
        have(p ∈ ((a × c) ∪ (b × c)) |- pair(fst(p), snd(p)) ∈ ((a ∪ b) × c)) by Cut(lastStep, cartesianProdIntro)

      val left = thenHave((p ∈ ((a × c) ∪ (b × c)), p ∈ (a × c)) |- p ∈ ((a ∪ b) × c)) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a, y := c))

      val right = have((p ∈ ((a × c) ∪ (b × c)), p ∈ (b × c)) |- p ∈ ((a ∪ b) × c)) by
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := b, y := c))(beforeSubst)

      have((p ∈ ((a × c) ∪ (b × c)), p ∈ (a × c) \/ (p ∈ (b × c))) |- p ∈ ((a ∪ b) × c)) by LeftOr(
        left,
        right
      )
      have(p ∈ ((a × c) ∪ (b × c)) |- p ∈ ((a ∪ b) × c)) by Cut(unElim, lastStep)
    }

    have(p ∈ ((a ∪ b) × c) <=> p ∈ ((a × c) ∪ (b × c))) by RightIff(forward, backward)
    thenHave(∀(p, p ∈ ((a ∪ b) × c) <=> p ∈ ((a × c) ∪ (b × c)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := (a ∪ b) × c, y := (a × c) ∪ (b × c)))
  }

  /**
   * Lemma --- the union of two Cartesian products is a subset of the product of unions.
   *
   *    `a * b ∪ c * d ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfCartesianProducts = Lemma(
    ((a × b) ∪ (c × d)) ⊆ ((a ∪ c) × (b ∪ d))
  ) {
    val left = have((a × b) ⊆ ((a ∪ c) × (b ∪ d))) subproof {
      have((fst(p) ∈ a, snd(p) ∈ (b ∪ d)) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(
        setUnionLeftIntro of (z := fst(p), x := a, y := c),
        cartesianProductIntro of (a := fst(p), b := snd(p), x := (a ∪ c), y := (b ∪ d))
      )
      have((fst(p) ∈ a, snd(p) ∈ b) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(
        setUnionLeftIntro of (z := snd(p), x := b, y := d),
        lastStep
      )
      thenHave(fst(p) ∈ a /\ snd(p) ∈ b |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by LeftAnd
      have(p ∈ (a × b) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(cartesianProductElim of (x := a, y := b), lastStep)
      thenHave(p ∈ (a × b) |- p ∈ ((a ∪ c) × (b ∪ d))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a, y := b))
      thenHave(p ∈ (a × b) ==> p ∈ ((a ∪ c) × (b ∪ d))) by RightImplies
      thenHave(∀(p, p ∈ (a × b) ==> p ∈ ((a ∪ c) × (b ∪ d)))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := a × b, y := (a ∪ c) × (b ∪ d)))
    }

    val right = have((c × d) ⊆ ((a ∪ c) × (b ∪ d))) subproof {
      have((fst(p) ∈ c, snd(p) ∈ (b ∪ d)) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(
        setUnionRightIntro of (z := fst(p), x := a, y := c),
        cartesianProductIntro of (a := fst(p), b := snd(p), x := (a ∪ c), y := (b ∪ d))
      )
      have((fst(p) ∈ c, snd(p) ∈ d) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(
        setUnionRightIntro of (z := snd(p), x := b, y := d),
        lastStep
      )
      thenHave(fst(p) ∈ c /\ snd(p) ∈ d |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by LeftAnd
      have(p ∈ (c × d) |- pair(fst(p), snd(p)) ∈ ((a ∪ c) × (b ∪ d))) by Cut(cartesianProductElim of (x := c, y := d), lastStep)
      thenHave(p ∈ (c × d) |- p ∈ ((a ∪ c) × (b ∪ d))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := c, y := d))
      thenHave(p ∈ (c × d) ==> p ∈ ((a ∪ c) × (b ∪ d))) by RightImplies
      thenHave(∀(p, p ∈ (c × d) ==> p ∈ ((a ∪ c) × (b ∪ d)))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := c × d, y := (a ∪ c) × (b ∪ d)))
    }

    have((a × b) ⊆ ((a ∪ c) × (b ∪ d)) /\ (c × d) ⊆ ((a ∪ c) × (b ∪ d))) by RightAnd(left, right)
    thenHave(thesis) by Substitution.ApplyRules(unionOfTwoSubsets of (a := a × b, b := c × d, c := (a ∪ c) × (b ∪ d)))
  }

  val swapUniqueness = Lemma(
    ∃!(z, (∃(x, ∃(y, p === pair(x, y))) ==> (z === pair(snd(p), fst(p)))) /\ (!(∃(x, ∃(y, p === pair(x, y)))) ==> (z === p)))
  ) {
    val left = have(∃(x, ∃(y, p === pair(x, y))) ==> ∃!(z, z === pair(snd(p), fst(p)))) by Weakening(existsOneEquality of (y := pair(snd(p), fst(p))))
    val right = have(!(∃(x, ∃(y, p === pair(x, y)))) ==> ∃!(z, z === p)) by Weakening(existsOneEquality of (y := p))

    have(!(∃(x, ∃(y, p === pair(x, y)))) ==> ∃!(z, z === p) |- ∃!(z, (∃(x, ∃(y, p === pair(x, y))) ==> (z === pair(snd(p), fst(p)))) /\ (!(∃(x, ∃(y, p === pair(x, y)))) ==> (z === p)))) by Cut(left, existsOneCases of (q := ∃(x, ∃(y, p === pair(x, y))), P := lambda(z, z === pair(snd(p), fst(p))), Q := lambda(z, z === p)))
    have(thesis) by Cut(right, lastStep)
  }

  val swap = DEF(p) --> The(z, (∃(x, ∃(y, p === pair(x, y))) ==> (z === pair(snd(p), fst(p)))) /\ (!(∃(x, ∃(y, p === pair(x, y)))) ==> (z === p)))(swapUniqueness)

  val swapPair = Lemma(
    swap(pair(x, y)) === pair(y, x)
  ) {
    have((∃(a, ∃(b, pair(x, y) === pair(a, b))) ==> (swap(pair(x, y)) === pair(snd(pair(x, y)), fst(pair(x, y))))) /\ (!(∃(a, ∃(b, pair(x, y) === pair(a, b)))) ==> (swap(pair(x, y)) === pair(x, y)))) by InstantiateForall(swap(pair(x, y)))(swap.definition of (p := pair(x, y)))
    thenHave(∃(a, ∃(b, pair(x, y) === pair(a, b))) |- swap(pair(x, y)) === pair(snd(pair(x, y)), fst(pair(x, y)))) by Weakening
    val withExists = thenHave(∃(a, ∃(b, pair(x, y) === pair(a, b))) |- swap(pair(x, y)) === pair(y, x)) by Substitution.ApplyRules(secondInPairReduction, firstInPairReduction)

    have(pair(x, y) === pair(x, y)) by RightRefl
    thenHave(∃(b, pair(x, y) === pair(x, b))) by RightExists
    thenHave(∃(a, ∃(b, pair(x, y) === pair(a, b)))) by RightExists
    have(thesis) by Cut(lastStep, withExists)
  }

  val swapNotPair = Lemma(
    ∀(x, ∀(y, p =/= pair(x, y))) |- swap(p) === p
  ) {
    have((∃(x, ∃(y, p === pair(x, y))) ==> (swap(p) === pair(snd(p), fst(p)))) /\ (!(∃(x, ∃(y, p === pair(x, y)))) ==> (swap(p) === p))) by InstantiateForall(swap(p))(swap.definition)
    thenHave(thesis) by Weakening
  }

  val swapInvolutive = Lemma(
    swap(swap(p)) === p
  ) {
    have(swap(swap(pair(x, y))) === pair(x, y)) by Substitution.ApplyRules(swapPair)(swapPair of (x := y, y := x))
    thenHave(p === pair(x, y) |- swap(swap(p)) === p) by RightSubstEq.withParametersSimple(List((p, pair(x, y))), lambda(p, swap(swap(p)) === p))
    thenHave(∃(y, p === pair(x, y)) |- swap(swap(p)) === p) by LeftExists
    val left = thenHave(∃(x, ∃(y, p === pair(x, y))) |- swap(swap(p)) === p) by LeftExists
    val right = have(∀(x, ∀(y, p =/= pair(x, y))) |- swap(swap(p)) === p) by Substitution.ApplyRules(swapNotPair)(swapNotPair of (p := swap(p)))
    have(thesis) by LeftOr(left, right)
  }

  val swapIsPair = Lemma(
    ∃(x, ∃(y, p === pair(x, y))) <=> ∃(x, ∃(y, swap(p) === pair(x, y)))
  ) {
    have(p === pair(a, b) |- swap(p) === pair(b, a)) by Substitution.ApplyRules(p === pair(a, b))(swapPair of (x := a, y := b))
    val forward = thenHave((p === pair(a, b)) ==> (swap(p) === pair(b, a))) by RightImplies
    val backward = have((swap(p) === pair(b, a)) ==> (p === pair(a, b))) by Substitution.ApplyRules(swapInvolutive)(forward of (p := swap(p), b := a, a := b))
    have((p === pair(a, b)) <=> (swap(p) === pair(b, a))) by RightIff(forward, backward)
    thenHave(∀(b, (p === pair(a, b)) <=> (swap(p) === pair(b, a)))) by RightForall
    have(∃(b, (p === pair(a, b))) <=> ∃(b, (swap(p) === pair(b, a)))) by Cut(lastStep, existentialEquivalenceDistribution of (P := lambda(b, p === pair(a, b)), Q := lambda(b, swap(p) === pair(b, a))))
    thenHave(∀(a, ∃(b, (p === pair(a, b))) <=> ∃(b, (swap(p) === pair(b, a))))) by RightForall
    have(∃(a, ∃(b, (p === pair(a, b)))) <=> ∃(a, ∃(b, (swap(p) === pair(b, a))))) by Cut(lastStep, existentialEquivalenceDistribution of (P := lambda(a, ∃(b, p === pair(a, b))), Q := lambda(a, ∃(b, swap(p) === pair(b, a)))))
    thenHave(∃(a, ∃(b, (p === pair(a, b)))) <=> ∃(b, ∃(a, (swap(p) === pair(b, a))))) by Substitution.ApplyRules(existentialSwap of (R := lambda((a, b), swap(p) === pair(b, a))))
  }

  val swapInjectivity = Lemma(
    swap(x) === swap(y) |- x === y
  ) {
    have((swap(pair(a, b)) === swap(pair(c, d))) <=> (pair(a, b) === pair(c, d))) by Substitution.ApplyRules(pairExtensionality, swapPair)(pairExtensionality of (b := a, a := b, c := d, d := c))
    thenHave(swap(pair(a, b)) === swap(pair(c, d)) |- pair(a, b) === pair(c, d)) by Weakening
    thenHave((x === pair(a, b), y === pair(c, d), swap(x) === swap(y)) |- x === y) by Substitution.ApplyRules(x === pair(a, b), y === pair(c, d))
    thenHave((x === pair(a, b), ∃(d, y === pair(c, d)), swap(x) === swap(y)) |- x === y) by LeftExists
    val case1 = thenHave((x === pair(a, b), ∃(c, ∃(d, y === pair(c, d))), swap(x) === swap(y)) |- x === y) by LeftExists

    have((pair(b, a) === y, y =/= pair(b, a)) |- x === y) by Restate
    thenHave((pair(b, a) === y, ∀(a, y =/= pair(b, a))) |- x === y) by LeftForall
    thenHave((pair(b, a) === y, ∀(b, ∀(a, y =/= pair(b, a)))) |- x === y) by LeftForall
    thenHave((swap(pair(a, b)) === swap(y), ∀(b, ∀(a, y =/= pair(b, a)))) |- x === y) by Substitution.ApplyRules(swapPair, swapNotPair)
    val case2 = thenHave((x === pair(a, b), ∀(b, ∀(a, y =/= pair(b, a))), swap(x) === swap(y)) |- x === y) by LeftSubstEq.withParametersSimple(List((x, pair(a, b))), lambda(x, swap(x) === swap(y)))

    have((x === pair(a, b), swap(x) === swap(y)) |- x === y) by LeftOr(case1, case2)
    thenHave((∃(b, x === pair(a, b)), swap(x) === swap(y)) |- x === y) by LeftExists
    val case12 = thenHave((∃(a, ∃(b, x === pair(a, b))), swap(x) === swap(y)) |- x === y) by LeftExists

    have((∀(a, ∀(b, x =/= pair(a, b))), y === pair(a, b), swap(x) === swap(y)) |- x === y) by Restate.from(case2 of (x := y, y := x))
    thenHave((∀(a, ∀(b, x =/= pair(a, b))), ∃(b, y === pair(a, b)), swap(x) === swap(y)) |- x === y) by LeftExists
    val case3 = thenHave((∀(a, ∀(b, x =/= pair(a, b))), ∃(a, ∃(b, y === pair(a, b))), swap(x) === swap(y)) |- x === y) by LeftExists
    
    have(x === y |- x === y) by Hypothesis
    val case4 = thenHave((∀(a, ∀(b, x =/= pair(a, b))), ∀(a, ∀(b, y =/= pair(a, b))), swap(x) === swap(y)) |- x === y) by Substitution.ApplyRules(swapNotPair)

    have((∀(a, ∀(b, x =/= pair(a, b))), swap(x) === swap(y)) |- x === y) by LeftOr(case3, case4)
    have(thesis) by LeftOr(case12, lastStep)
  }

  val swapEqualsPair = Lemma(
    swap(p) === pair(x, y) |- p === pair(y, x)
  ) {
   have(thesis) by Substitution.ApplyRules(swapPair)(swapInjectivity of (x := p, y := pair(y, x)))
  }

  val swapCartesianProduct = Lemma(
    p ∈ (x × y) <=> swap(p) ∈ (y × x)
  ) {
    val forward = have(p ∈ (x × y) ==> swap(p) ∈ (y  × x)) subproof {
      have(b ∈ y /\ a ∈ x |- pair(b, a) ∈ (y  × x)) by LeftAnd(cartesianProductIntro of (a := b, b := a, x := y, y := x))
      have(pair(a, b) ∈ (x × y) |- pair(b, a) ∈ (y  × x)) by Cut(cartesianProductElimPair, lastStep)
      thenHave(pair(a, b) ∈ (x × y) |- swap(pair(a, b)) ∈ (y  × x)) by Substitution.ApplyRules(swapPair)
      thenHave((p === pair(a, b), p ∈ (x × y)) |- swap(p) ∈ (y  × x)) by Substitution.ApplyRules(p === pair(a, b))
      have(p ∈ (x × y) |- swap(p) ∈ (y  × x)) by Cut(pairReconstructionInCartesianProduct, lastStep of (a := fst(p), b := snd(p)))
    }
    val backward = have(swap(p) ∈ (y  × x) ==> p ∈ (x × y)) by Substitution.ApplyRules(swapInvolutive)(forward of (p := swap(p), x := y, y := x))
    have(thesis) by RightIff(forward, backward)
  }

}
