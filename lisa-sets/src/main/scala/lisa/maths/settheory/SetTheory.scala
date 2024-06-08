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
  def classFunction(R: Term ** 2 |-> Formula, A: Term): Formula = classFunction(R, lambda(x, in(x, A)))

  val classFunctionElim = Lemma(
    (classFunction(R, P), P(x)) |- existsOne(y, R(x, y))
  ) {
    have(classFunction(R, P) |- classFunction(R, P)) by Hypothesis
    thenHave(thesis) by InstantiateForall(x)
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

  val replacementUniqueness = Lemma(
    classFunction(R, A) |- existsOne(B, forall(y, in(y, B) <=> exists(x, in(x, A) /\ R(x, y))))
  ) {
    have(∃!(y, R(x, y)) |- (R(x, y) /\ R(x, z)) ==> (y === z)) by Restate.from(existsOneImpliesUniqueness of (P := lambda(y, R(x, y)), x := y, y := z))
    thenHave(∃!(y, R(x, y)) |- forall(z, (R(x, y) /\ R(x, z)) ==> (y === z))) by RightForall
    thenHave(∃!(y, R(x, y)) |- forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by RightForall
    thenHave(in(x, A) ==> ∃!(y, R(x, y)) |- in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by Tautology
    thenHave(classFunction(R, A) |- in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by LeftForall
    val uniqueness = thenHave(classFunction(R, A) |- forall(x, in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z))))) by RightForall

    have(forall(x, in(x, A) ==> forall(y, forall(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) |- exists(B, forall(b, in(b, B) <=> exists(x, in(x, A) /\ R(x, b))))) by 
      Restate.from({val P = predicate[2]; replacementSchema of (P := R)})
    have(classFunction(R, A) |- exists(B, forall(b, in(b, B) <=> exists(x, in(x, A) /\ R(x, b))))) by Cut(uniqueness, lastStep)
    have(thesis) by Cut(lastStep, uniqueByExtension of (z := B, schemPred := lambda(b, exists(x, in(x, A) /\ R(x, b)))))
  }
  
  val replacementClassFunction = Lemma(
    existsOne(B, forall(y, in(y, B) <=> exists(x, in(x, A) /\ (F(x) === y))))
  ) {
    have(thesis) by Cut(functionIsClassFunction of (P := lambda(x, in(x, A))), replacementUniqueness of (R := lambda((x, y), F(x) === y)))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Properties about the empty set and power sets
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
   * Lemma --- A set containing no elements is equal to the empty set.
   *
   *    `∀ y. y ∉ x ⊢ x = ∅`
   *
   * Converse of the empty set axiom ([[emptySetAxiom]]).
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

  val nonEmptySetHasAnElement = Lemma(
    !(x === ∅) |- exists(y, in(y, x))
  ) {
    have(thesis) by Restate.from(setWithNoElementsIsEmpty)
  }

  /**
   * Subset properties
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
    (subset(x, y) /\ subset(y, x)) <=> (x === y)
  ) {
    have(subset(x, y) /\ subset(y, x) <=> subset(x, y) /\ subset(y, x)) by Restate
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ subset(y, x)) by Substitution.ApplyRules(subsetAxiom)
    thenHave(subset(x, y) /\ subset(y, x) <=> forall(t, in(t, x) ==> in(t, y)) /\ forall(t, in(t, y) ==> in(t, x))) by Substitution.ApplyRules(subsetAxiom)
    andThen(Substitution.applySubst(universalConjunctionCommutation of (P := lambda(t, in(t, x) ==> in(t, y)), Q := lambda(t, in(t, y) ==> in(t, x)))))
    andThen(Substitution.applySubst(extensionalityAxiom))
    thenHave(thesis) by Restate
  }

  /**
   * Lemma --- Subset relationship is transitive
   *
   *    `a ⊆ b, b ⊆ c ⊢ a ⊆ c`
   */
  val subsetTransitivity = Lemma(
    (subset(a, b), subset(b, c)) |- subset(a, c)
  ) {
    have((subset(a, b), subset(b, c), in(z, a)) |- in(z, c)) by Cut(subsetElim of (x := a, y := b), subsetElim of (x := b, y := c))
    thenHave((subset(a, b), subset(b, c)) |- in(z, a) ==> in(z, c)) by RightImplies
    thenHave((subset(a, b), subset(b, c)) |- forall(z, in(z, a) ==> in(z, c))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := a, y := c))
  }

  /**
   * Lemma --- The empty set is a subset of every set.
   *
   *    `∅ ⊆ x`
   */
  val emptySetIsASubset = Lemma(
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
  val emptySetIsItsOwnOnlySubset = Lemma(
    subset(x, emptySet) <=> (x === emptySet)
  ) {
    val forward = have(subset(x, emptySet) ==> (x === emptySet)) subproof {
      have((subset(x, emptySet), in(z, x)) |- ()) by RightAnd(subsetElim of (y := emptySet), emptySetAxiom of (x := z))
      thenHave((subset(x, emptySet), exists(z, in(z, x))) |- ()) by LeftExists
      have((subset(x, emptySet), !(x === emptySet)) |- ()) by Cut(nonEmptySetHasAnElement, lastStep)
    }

    val backward = have((x === emptySet) ==> subset(x, emptySet)) subproof {
      have((x === emptySet) |- subset(x, emptySet)) by RightSubstEq.withParametersSimple(List((x, emptySet)), lambda(x, subset(x, emptySet)))(emptySetIsASubset of (x := emptySet))
    }

    have(thesis) by RightIff(forward, backward)
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

  val inSetSubsetUnion = Lemma(in(x, y) |- subset(x, union(y))) {
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
    thenHave(exists(x , in(x, union(emptySet))) |- ()) by LeftExists
    have(!(union(emptySet) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := union(emptySet)), lastStep)
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
    thenHave(forall(a, (in(z, a) /\ in(a, unorderedPair(x, y))) <=>  (((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a))))) by RightForall
    have(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> exists(a, ((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a)))) by Cut(lastStep, existentialEquivalenceDistribution of (P := lambda(a, (in(z, a) /\ in(a, unorderedPair(x, y)))), Q := lambda(a, ((a === x) /\ in(z, a)) \/ ((a === y) /\ in(z, a)))))
    thenHave(exists(a, in(z, a) /\ in(a, unorderedPair(x, y))) <=> (exists(a, (a === x) /\ in(z, a)) \/ exists(a, in(z, a) /\ (a === y)))) by Substitution.ApplyRules(existentialDisjunctionCommutation of (P := lambda(a, (a === x) /\ in(z, a)), Q := lambda(a, in(z, a) /\ (a === y))))
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
    have(in(z, setUnion(a, b)) <=> in(z, setUnion(b, a))) by Substitution.ApplyRules(setUnionMembership of (x := b, y := a))( setUnionMembership of (x := a, y := b))
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
    have(thesis) by Substitution.ApplyRules(setUnionCommutativity of (b := emptySet))(setUnionRightEmpty)
  }

  /**
   * Shorthand definitions
   */

  /**
   * Proper Subset --- `x ⊂ y`. Shorthand for `x ⊆ y ∧ x != y`.
   *
   * @param x set
   * @param y set
   */
  def properSubset(x: Term, y: Term) = subset(x, y) /\ !(x === y)



  

  //////////////////////////////////////////////////////////////////////////////



  

  /**
   * Lemma --- A power set is never empty.
   *
   *    `! P(x) = ∅`
   */
  val powerSetNonEmpty = Lemma(
    !(powerSet(x) === ∅)
  ) {
    have(thesis) by Tautology.from(emptySetIsASubset, powerAxiom of (x := ∅, y := x), setWithElementNonEmpty of (y := ∅, x := powerSet(x)))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Properties about pairs
   */

  

  /**
   * Lemma --- First Element in Pair
   *
   *    `x ∈ {x, y}`
   *
   * Unfolds the definition of [[unorderedPair]]. Easier to use in theorems than
   * the complete definition.
   */
  val firstElemInPair = Lemma(
    in(x, unorderedPair(x, y))
  ) {
    have(thesis) by Weakening(pairAxiom of (z := x))
  }

  /**
   * Lemma --- Second Element in Pair
   *
   *    `y ∈ {x, y}`
   *
   * Unfolds the definition of [[unorderedPair]]. Easier to use in theorems than
   * the complete definition.
   */
  val secondElemInPair = Lemma(
    in(y, unorderedPair(x, y))
  ) {
    have(thesis) by Weakening(pairAxiom of (z := y))
  }

  /**
   * Lemma --- The [[unorderedPair]] is, in fact, unordered.
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

  val unorderedPairDeconstruction = Lemma(
    (unorderedPair(a, b) === unorderedPair(c, d)) ⊢ (((a === c) ∧ (b === d)) ∨ ((a === d) ∧ (b === c)))
  ) {
    val s1 = have(Substitution.applySubst(unorderedPair(a, b) === unorderedPair(c, d))(pairAxiom of (x := a, y := b)))
    val base = have(Substitution.applySubst(s1)(pairAxiom of (x := c, y := d)))

    have(thesis) by Tautology.from(base of (z := a), base of (z := b), base of (z := c), base of (z := d))
  }

    /**
   * Lemma --- Two [[unorderedPair]]s are equal iff their elements are equal pairwise.
   *
   *    `{a, b} = {c, d} <=> ( (a = c ∧ b = d) ∨ (a = d ∧ b = c) )`
   */
  val unorderedPairExtensionality = Lemma(
    (unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))
  ) {
    // forward direction
    //      up ab = up cd |- a = c and b = d OR a = d and b = c
    val fwd = have((unorderedPair(a, b) === unorderedPair(c, d)) ==> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightImplies(unorderedPairDeconstruction)

    // backward direction
    //      a = c and b = d => up ab = up cd (and the other case)
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
    val bwd = thenHave((((a === d) /\ (b === c)) \/ ((a === c) /\ (b === d))) ==> (unorderedPair(a, b) === unorderedPair(c, d))) by RightImplies

    have((unorderedPair(a, b) === unorderedPair(c, d)) <=> (((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c)))) by RightIff(fwd, bwd)
  }

  /**
   * Definition --- Singleton Set
   *
   *   `{x} = {x, x}`
   */
  val singleton = DEF(x) --> unorderedPair(x, x)


  /**
   * Lemma --- If a set belongs to a [[singleton]], it must be the single element.
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
   * Lemma --- Union of a Singleton is the Original Set
   *
   * The unary [[union]] operation unfolds a [[singleton]] into the single
   * element
   *
   *      `∀ x. ∪ {x} === x`
   */
  val unionOfSingletonIsTheOriginalSet = Lemma((union(singleton(x)) === x)) {
    have((in(y, singleton(x)) /\ in(z, y)) <=> ((x === y) /\ in(z, y))) by Tautology.from(singletonMembership)
    thenHave(forall(y, (in(y, singleton(x)) /\ in(z, y)) <=> ((x === y) /\ in(z, y)))) by RightForall
    have(exists(y, in(y, singleton(x)) /\ in(z, y)) <=> exists(y, (x === y) /\ in(z, y))) by Cut(lastStep, existentialEquivalenceDistribution of (P := lambda(y, in(y, singleton(x)) /\ in(z, y)), Q := lambda(y, (x === y) /\ in(z, y))))
    thenHave( in(z, union(singleton(x))) <=> in(z, x)) by Substitution.ApplyRules(unionAxiom of (x := singleton(x)), onePointRule of (y := x, Q := lambda(y, in(z, y))))
    thenHave(∀(z, in(z, union(singleton(x))) <=> in(z, x))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(singleton(x)), y := x))
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
   * Lemma --- Unordered pairs of elements of a set `x` are in its power set `P(x)`.
   *
   *    `a ∈ x ∧ b ∈ x <=> {a, b} ∈ P(x)`
   */
  val unorderedPairInPowerSet = Lemma(
    (in(a, x) /\ in(b, x)) <=> in(unorderedPair(a, b), powerSet(x))
  ) {

    // forward
    val fwd = have((in(a, x) /\ in(b, x)) ==> in(unorderedPair(a, b), powerSet(x))) subproof {
      val axExpansion = have(in(unorderedPair(a, b), powerSet(x)) <=> ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(
        powerAxiom of (x := unorderedPair(a, b), y := x),
        subsetAxiom of (x := unorderedPair(a, b), y := x)
      )

      val abToz = have(in(a, x) /\ in(b, x) |- ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) subproof {
        val pairAxab = have(in(z, unorderedPair(a, b)) |- (z === a) \/ (z === b)) by Tautology.from(pairAxiom of (x := a, y := b))

        have(in(a, x) /\ in(b, x) |- in(a, x)) by Restate
        val za = thenHave((in(a, x) /\ in(b, x), (z === a)) |- in(z, x)) by RightSubstEq.withParametersSimple(List((z, a)), lambda(a, in(a, x)))
        have(in(a, x) /\ in(b, x) |- in(b, x)) by Restate
        val zb = thenHave((in(a, x) /\ in(b, x), (z === b)) |- in(z, x)) by RightSubstEq.withParametersSimple(List((z, b)), lambda(a, in(a, x)))

        val zab = have((in(a, x) /\ in(b, x), (z === a) \/ (z === b)) |- in(z, x)) by LeftOr(za, zb)

        have((in(z, unorderedPair(a, b)), in(a, x) /\ in(b, x)) |- in(z, x)) by Cut(pairAxab, zab)
        thenHave(in(a, x) /\ in(b, x) |- in(z, unorderedPair(a, b)) ==> in(z, x)) by Restate
        thenHave(thesis) by RightForall
      }

      have(thesis) by Tautology.from(abToz, axExpansion)
    }

    val bwd = have(in(unorderedPair(a, b), powerSet(x)) ==> (in(a, x) /\ in(b, x))) subproof {
      have(in(unorderedPair(a, b), powerSet(x)) |- ∀(z, in(z, unorderedPair(a, b)) ==> in(z, x))) by Tautology.from(
        powerAxiom of (x := unorderedPair(a, b), y := x),
        subsetAxiom of (x := unorderedPair(a, b), y := x)
      )
      val upz = thenHave(in(unorderedPair(a, b), powerSet(x)) |- in(z, unorderedPair(a, b)) ==> in(z, x)) by InstantiateForall(z)

      val xa = have(in(unorderedPair(a, b), powerSet(x)) |- in(a, x)) by Tautology.from(upz of (z := a), firstElemInPair of (x := a, y := b))
      val xb = have(in(unorderedPair(a, b), powerSet(x)) |- in(b, x)) by Tautology.from(upz of (z := b), secondElemInPair of (x := a, y := b))
      have(in(unorderedPair(a, b), powerSet(x)) |- in(b, x) /\ in(a, x)) by RightAnd(xa, xb)
    }

    have(thesis) by RightIff(fwd, bwd)
  }

  val singletonInPowerSet = Lemma(
    in(a, x) <=> in(singleton(a), powerSet(x))
  ) {
    have(thesis) by Substitution.ApplyRules(singleton.shortDefinition of (x := a))(unorderedPairInPowerSet of (b := a))
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
      (((((a === c) /\ (b === d)) \/ ((a === d) /\ (b === c))) /\ (a === c)) \/ (((a === c) /\ (b === c)) /\ ((a === c) /\ (a === d))))) by 
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
   * Lemma --- No set is an element of itself.
   *
   *    `! x ∈ x`
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
   * Lemma --- The power set of any set is not a proper subset of it.
   *
   *    `∃ x. P(x) ⊂ x ⊢ ⊥`
   */
  val powerSetNonInclusion = Lemma(
    exists(x, properSubset(powerSet(x), x)) |- ()
  ) {
    have(subset(powerSet(x), x) |- subset(powerSet(x), x)) by Hypothesis
    have(subset(powerSet(x), x) |- subset(powerSet(x), x) /\ (in(powerSet(x), powerSet(x)) <=> subset(powerSet(x), x))) by RightAnd(lastStep, powerAxiom of (x := powerSet(x), y := x))
    val contraLhs = thenHave(subset(powerSet(x), x) |- in(powerSet(x), powerSet(x))) by Tautology
    have(subset(powerSet(x), x) |- !in(powerSet(x), powerSet(x)) /\ in(powerSet(x), powerSet(x))) by RightAnd(contraLhs, selfNonMembership of (x := powerSet(x)))
    thenHave(subset(powerSet(x), x) |- (x === powerSet(x))) by Weakening
    thenHave(properSubset(powerSet(x), x) |- ()) by Restate
    thenHave(∃(x, properSubset(powerSet(x), x)) |- ()) by LeftExists
  }

    /**
   * Lemma --- If `t` is a pair containing elements from `x` and `y`, then
   * it is in `PP(x ∪ y)`.
   *
   *    `∃ c, d. t = (c, d) ∧ c ∈ x ∧ d ∈ y ⊢ t ∈ PP(x ∪ y)`
   *
   * Asserts that the first part of the [[cartesianProduct]] definition is redundant.
   */
  val elemOfPowerPowerUnion = Lemma(
    ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))
  ) {
    val upCD = have((in(c, x), in(d, y)) |- in(unorderedPair(c, d), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x), in(d, y)) |- subset(unorderedPair(c, d), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, d)) <=> ((z === c) \/ (z === d))) by Restate.from(pairAxiom of (x := c, y := d))

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(setUnionMembership)
        val zd = have((z === d) |- in(z, setUnion(x, y)) <=> (in(d, x) \/ in(d, y))) by Substitution.ApplyRules(z === d)(setUnionMembership)

        have((in(c, x), in(d, y)) |- in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc, zd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Cut(lastStep, subsetIntro of (x := unorderedPair(c, d), y := setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y := setUnion(x, y), x := unorderedPair(c, d)))
    }

    val upCC = have((in(c, x)) |- in(singleton(c), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x)) |- subset(singleton(c), setUnion(x, y))) subproof {
        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(setUnionMembership)

        have(in(c, x) |- in(z, singleton(c)) ==> in(z, setUnion(x, y))) by Tautology.from(singletonMembership of (y := z, x := c), zc)
        thenHave(in(c, x) |- forall(z, in(z, singleton(c)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Cut(lastStep, subsetIntro of (x := singleton(c), y := setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y := setUnion(x, y), x := singleton(c)))

    }

    have((in(c, x), in(d, y)) |- in(pair(c, d), powerSet(powerSet(setUnion(x, y))))) subproof {

      have((in(c, x), in(d, y)) |- subset(pair(c, d), powerSet(setUnion(x, y)))) subproof {

        val zp = have(in(z, pair(c, d)) <=> ((z === unorderedPair(c, d)) \/ (z === singleton(c)))) by Substitution.ApplyRules(pair.shortDefinition of (x := c, y := d))(
          pairAxiom of (x := unorderedPair(c, d), y := singleton(c))
        )

        val zcc = have((z === singleton(c), in(c, x)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === singleton(c))(upCC)
        val zcd = have((z === unorderedPair(c, d), in(c, x), in(d, y)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === unorderedPair(c, d))(upCD)

        have((in(c, x), in(d, y)) |- in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y)))) by Tautology.from(zp, zcc, zcd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Cut(lastStep, subsetIntro of (x := pair(c, d), y := powerSet(setUnion(x, y))))
      }

      have(thesis) by Tautology.from(lastStep, powerAxiom of (y := powerSet(setUnion(x, y)), x := pair(c, d)))

    }

    thenHave((t === pair(c, d), in(c, x), in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Substitution.ApplyRules(t === pair(c, d))
    thenHave(((t === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Restate
    thenHave(exists(d, ((t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  val inclusionAntiSymmetric = Lemma(
    !(in(x, y) /\ in(y, x))
  ) {
    assume(in(x, y))
    assume(in(y, x))

    // consider the set u = {x, y}
    val u = unorderedPair(x, y)

    // u is not the empty set
    have(in(x, u)) by Weakening(firstElemInPair)
    have(!(u === emptySet)) by Tautology.from(lastStep, setWithElementNonEmpty of (y := x, x := u))

    // by Foundation, there must be an inclusion minimal element in u
    val minimal = have(exists(z, in(z, u) /\ forall(t, in(t, u) ==> !in(t, z)))) by Tautology.from(lastStep, foundationAxiom of (x := u))
    // negation = forall(z, in(z, u) ==> exists(t, in(t, u) /\ in(t, z)))

    // it can only be x or y
    val zxy = have(in(z, u) <=> ((z === x) \/ (z === y))) by Weakening(pairAxiom)

    // but x \cap u contains y, and y \cap u contains x
    have(in(x, u) /\ in(x, y)) by Tautology.from(firstElemInPair)
    thenHave((z === y) |- in(x, u) /\ in(x, z)) by Substitution.ApplyRules(z === y)
    val zy = thenHave((z === y) |- exists(t, in(t, u) /\ in(t, z))) by RightExists

    have(in(y, u) /\ in(y, x)) by Tautology.from(secondElemInPair)
    thenHave((z === x) |- in(y, u) /\ in(y, z)) by Substitution.ApplyRules(z === x)
    val zx = thenHave((z === x) |- exists(t, in(t, u) /\ in(t, z))) by RightExists

    // this is a contradiction
    have(in(z, u) ==> exists(t, in(t, u) /\ in(t, z))) by Tautology.from(zxy, zx, zy)
    thenHave(forall(z, in(z, u) ==> exists(t, in(t, u) /\ in(t, z)))) by RightForall

    have(thesis) by Tautology.from(lastStep, minimal)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Set intersection
   */

  val setIntersectionUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))
  ) {
    have(∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))) by UniqueComprehension(x, lambda(t, in(t, y)))
  }

  /**
   * Binary Set Intersection --- Intersection of two sets.
   *
   *     `x ∩ y = {z ∈ x | z ∈ y}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * @param x set
   * @param y set
   */
  val setIntersection = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ in(t, y))))(setIntersectionUniqueness)

  extension (x: Term) {
    infix def ∩(y: Term) = setIntersection(x, y)
  }

  val setIntersectionMembership = Lemma(
    in(t, setIntersection(x, y)) <=> (in(t, x) /\ in(t, y))
  ) {
    have(forall(t, in(t, setIntersection(x, y)) <=> (in(t, x) /\ in(t, y)))) by InstantiateForall(setIntersection(x, y))(setIntersection.definition)
    thenHave(thesis) by InstantiateForall(t)
  }

  /**
   * Set Intersection Introduction Rule
   *
   *    `t ∈ x, t ∈ y ⊢ t ∈ x ∩ y`
   */
  val setIntersectionIntro = Lemma(
    (in(t, x), in(t, y)) |- in(t, setIntersection(x, y))
  ) {
    have(thesis) by Weakening(setIntersectionMembership)
  }

  val setIntersectionElim = Lemma(
    in(t, setIntersection(x, y)) |- in(t, x) /\ in(t, y)
  ) {
    have(thesis) by Tautology.from(setIntersectionMembership)
  }

  val setIntersectionLeftElim = Lemma(
    in(t, setIntersection(x, y)) |- in(t, x)
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  val setIntersectionRightElim = Lemma(
    in(t, setIntersection(x, y)) |- in(t, y)
  ) {
    have(thesis) by Weakening(setIntersectionElim)
  }

  val setIntersectionCommutativity = Lemma(
    setIntersection(x, y) === setIntersection(y, x)
  ) {
    have(in(t, setIntersection(x, y)) <=> in(t, setIntersection(y, x))) by Substitution.ApplyRules(setIntersectionMembership of (x := y, y := x))(setIntersectionMembership)
    thenHave(forall(t, in(t, setIntersection(x, y)) <=> in(t, setIntersection(y, x)))) by RightForall
    have(setIntersection(x, y) === setIntersection(y, x)) by Cut(lastStep, equalityIntro of (x := setIntersection(x, y), y := setIntersection(y, x)))
  }

  val setIntersectionLeftSubset = Lemma(
    subset(setIntersection(x, y), x)
  ) {
    have(in(t, setIntersection(x, y)) ==> in(t, x)) by RightImplies(setIntersectionLeftElim)
    thenHave(forall(t, in(t, setIntersection(x, y)) ==> in(t, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(x, y), y := x))
  }

  val setIntersectionRightSubset = Lemma(
    subset(setIntersection(x, y), y)
  ) {
    have(in(t, setIntersection(x, y)) ==> in(t, y)) by RightImplies(setIntersectionRightElim)
    thenHave(forall(t, in(t, setIntersection(x, y)) ==> in(t, y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(x, y), y := y))
  }

  val setIntersectionOfSubsetForward = Lemma(
    subset(x, y) |- setIntersection(x, y) === x
  ) {
    have(subset(x, y) |- in(t, setIntersection(x, y)) <=> in(t, x)) by Tautology.from(subsetElim of (z := t), setIntersectionMembership)
    thenHave(subset(x, y) |- forall(t, in(t, setIntersection(x, y)) <=> in(t, x))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := setIntersection(x, y), y := x))
  }

  val setIntersectionOfSubsetBackward = Lemma(
    subset(y, x) |- setIntersection(x, y) === y
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionCommutativity)(setIntersectionOfSubsetForward of (x := y, y := x))
  }

  val singletonDisjointSelf = Lemma(
    setIntersection(x, singleton(x)) === emptySet
  ) {
    have(in(z, x) |- in(z, x)) by Hypothesis
    thenHave((in(z, x), in(z, singleton(x))) |- in(z, z)) by Substitution.ApplyRules(singletonElim of (y := z))
    thenHave((in(z, x) /\ in(z, singleton(x)), !in(z, z)) |- ()) by Restate
    have(in(z, x) /\ in(z, singleton(x)) |- ()) by Cut(selfNonMembership of (x := z), lastStep)
    have(in(z, setIntersection(x, singleton(x))) |- ()) by Cut(setIntersectionElim of (t := z, y := singleton(x)), lastStep)
    thenHave(exists(z, in(z, setIntersection(x, singleton(x)))) |- ()) by LeftExists
    have(!(setIntersection(x, singleton(x)) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := setIntersection(x, singleton(x))), lastStep)
  }

  val unaryIntersectionUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by UniqueComprehension(union(x), lambda(t, ∀(b, in(b, x) ==> in(t, b))))

    val lhs = have((in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))) |- ∀(b, in(b, x) ==> in(t, b)) /\ exists(b, in(b, x))) subproof {
      val unionAx = have(in(t, union(x)) |- exists(b, in(b, x) /\ in(t, b))) by Weakening(unionAxiom of (z := t))

      have(in(b, x) /\ in(t, b) |- in(b, x)) by Restate
      thenHave(in(b, x) /\ in(t, b) |- exists(b, in(b, x))) by RightExists
      val exRed = thenHave(exists(b, in(b, x) /\ in(t, b)) |- exists(b, in(b, x))) by LeftExists

      have(in(t, union(x)) |- exists(b, in(b, x))) by Cut(unionAx, exRed)
      thenHave(thesis) by Tautology
    }

    val rhs = have(∀(b, in(b, x) ==> in(t, b)) /\ exists(b, in(b, x)) |- (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))) subproof {
      val unionAx = have(in(t, union(x)) <=> exists(z, in(z, x) /\ in(t, z))) by Restate.from(unionAxiom of (z := t))

      have((in(b, x), in(b, x) ==> in(t, b)) |- in(b, x) /\ (in(t, b))) by Tautology
      thenHave((in(b, x), forall(b, in(b, x) ==> in(t, b))) |- in(b, x) /\ in(t, b)) by LeftForall
      thenHave((in(b, x), forall(b, in(b, x) ==> in(t, b))) |- exists(b, in(b, x) /\ in(t, b))) by RightExists
      val exRed = thenHave((exists(b, (in(b, x))), forall(b, in(b, x) ==> in(t, b))) |- exists(b, in(b, x) /\ in(t, b))) by LeftExists

      have(thesis) by Tautology.from(unionAx, exRed)
    }

    have(() |- (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))) <=> (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))) by Tautology.from(lhs, rhs)
    thenHave(() |- forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))) <=> (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by RightForall

    have(() |- forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))) <=> forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) by Cut(
      lastStep,
      universalEquivalenceDistribution of (P := lambda(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))), Q := lambda(
        t,
        (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))
      ))
    )
    thenHave(
      () |- forall(z, forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))) <=> forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))))
    ) by RightForall

    have(
      () |- existsOne(z, forall(t, (in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))) <=> existsOne(z, forall(t, (in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))))
    ) by Cut(
      lastStep,
      uniqueExistentialEquivalenceDistribution of (P := lambda(z, forall(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b))))), Q := lambda(
        z,
        forall(t, in(t, z) <=> (in(t, union(x)) /\ ∀(b, in(b, x) ==> in(t, b))))
      ))
    )
    have(thesis) by Tautology.from(lastStep, uniq)
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
  val unaryIntersection = DEF(x) --> The(z, ∀(t, in(t, z) <=> (exists(b, in(b, x)) /\ ∀(b, in(b, x) ==> in(t, b)))))(unaryIntersectionUniqueness)

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
    val fwd = thenHave(P(x) |- ∀(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightImplies

    val bwd = thenHave((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) ==> (∀(y, P(y) ==> in(t, y)))) by Weakening

    val lhs = have(P(x) |- ∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

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
   * The first element of an ordered [[pair]] --- `first p = ∪ ∩ p`
   *
   * If `p = (a, b) = {{a}, {a, b}}`, `∩ p = {a}`, and `∪ ∩ p = a`.
   *
   * While the function is defined on all sets, the result on non-pairs may be
   * uninteresting or garbage. Generally expected to be used via
   * [[firstInPairReduction]].
   */
  val firstInPair = DEF(p) --> union(unaryIntersection(p))

  val secondInPairSingletonUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))
  ) {
    have(thesis) by UniqueComprehension(union(p), lambda(t, ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p))))))
  }

  /**
   * See [[secondInPair]].
   */
  val secondInPairSingleton =
    DEF(p) --> The(z, ∀(t, in(t, z) <=> (in(t, union(p)) /\ ((!(union(p) === unaryIntersection(p))) ==> (!in(t, unaryIntersection(p)))))))(secondInPairSingletonUniqueness)

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
   * Lemma --- The union of an ordered pair is the corresponding unordered pair.
   *
   *    `∪ (x, y) = ∪ {{x}, {x, y}} = {x, y}`
   */
  val unionOfOrderedPair = Lemma(
    () |- (union(pair(x, y)) === unorderedPair(x, y))
  ) {
    val upElem = have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Restate.from(pairAxiom)

    val unionElem = have(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) subproof {
      // expand being in \cup (x, y)
      val unionax = have(in(z, union(pair(x, y))) <=> exists(b, in(b, pair(x, y)) /\ in(z, b))) by Restate.from(unionAxiom of (x := pair(x, y)))

      // what does it mean for b to be in (x, y)?
      // b \in (x, y) /\ z \in b <=> z = x \/ z = y
      val fwd = have(exists(b, in(b, pair(x, y)) /\ in(z, b)) |- ((z === x) \/ (z === y))) subproof {

        have(in(b, unorderedPair(unorderedPair(x, y), singleton(x))) /\ in(z, b) |- ((b === unorderedPair(x, y)) \/ (b === singleton(x)))) by Weakening(
          pairAxiom of (x := unorderedPair(x, y), y := singleton(x), z := b)
        )
        val bxy = thenHave(in(b, pair(x, y)) /\ in(z, b) |- ((b === unorderedPair(x, y)) \/ (b === singleton(x)))) by Substitution.ApplyRules(pair.shortDefinition)
        val zxy = have((b === unorderedPair(x, y)) |- in(z, b) <=> ((z === x) \/ (z === y))) by Substitution.ApplyRules(b === unorderedPair(x, y))(pairAxiom)
        have((b === unorderedPair(x, x)) |- in(z, b) <=> ((z === x) \/ (z === x))) by Substitution.ApplyRules(b === unorderedPair(x, x))(pairAxiom of (y := x))
        val zxx = thenHave((b === singleton(x)) |- in(z, b) <=> ((z === x) \/ (z === x))) by Substitution.ApplyRules(singleton.shortDefinition)

        have(in(b, pair(x, y)) /\ in(z, b) |- ((z === x) \/ (z === y))) by Tautology.from(bxy, zxy, zxx)
        thenHave(thesis) by LeftExists
      }

      val bwd = have(((z === x) \/ (z === y)) |- exists(b, in(b, pair(x, y)) /\ in(z, b))) subproof {
        have(in(unorderedPair(x, y), unorderedPair(unorderedPair(x, y), singleton(x)))) by Restate.from(firstElemInPair of (x := unorderedPair(x, y), y := singleton(x)))
        val xyp = thenHave(in(unorderedPair(x, y), pair(x, y))) by Substitution.ApplyRules(pair.shortDefinition)
        val zx = have((z === x) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(z === x)(firstElemInPair)
        val zy = have((z === y) |- in(z, unorderedPair(x, y))) by Substitution.ApplyRules(z === y)(secondElemInPair)

        have(((z === x) \/ (z === y)) |- in(unorderedPair(x, y), pair(x, y)) /\ in(z, unorderedPair(x, y))) by Tautology.from(xyp, zx, zy)
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(fwd, bwd, unionax)
    }

    have(in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y))) by Tautology.from(upElem, unionElem)
    thenHave(forall(z, in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := union(pair(x, y)), y := unorderedPair(x, y)))
  }

  /**
   * Lemma --- The unary intersection of an ordered pair is the singleton
   * containing the first element.
   *
   *    `∩ (x, y) = ∩ {{x}, {x, y}} = {x}`
   */
  val pairUnaryIntersection = Lemma(
    () |- in(z, unaryIntersection(pair(x, y))) <=> (z === x)
  ) {
    have(forall(t, in(t, unaryIntersection(pair(x, y))) <=> (exists(b, in(b, pair(x, y))) /\ ∀(b, in(b, pair(x, y)) ==> in(t, b))))) by InstantiateForall(unaryIntersection(pair(x, y)))(
      unaryIntersection.definition of (x := pair(x, y))
    )
    val defexp = thenHave(in(z, unaryIntersection(pair(x, y))) <=> (exists(b, in(b, pair(x, y))) /\ ∀(b, in(b, pair(x, y)) ==> in(z, b)))) by InstantiateForall(z)

    val lhs = have(in(z, unaryIntersection(pair(x, y))) |- (z === x)) subproof {
      have(in(z, unaryIntersection(pair(x, y))) |- forall(b, in(b, pair(x, y)) ==> in(z, b))) by Weakening(defexp)
      thenHave((in(z, unaryIntersection(pair(x, y))), in(singleton(x), pair(x, y))) |- in(z, singleton(x))) by InstantiateForall(singleton(x))
      thenHave((in(z, unaryIntersection(pair(x, y))), in(singleton(x), unorderedPair(unorderedPair(x, y), singleton(x)))) |- in(z, singleton(x))) by Substitution.ApplyRules(
        pair.shortDefinition
      )
      have(in(z, unaryIntersection(pair(x, y))) |- in(z, singleton(x))) by Cut(secondElemInPair of (x := unorderedPair(x, y), y := singleton(x)), lastStep)
      thenHave(thesis) by Substitution.ApplyRules(singletonMembership of (y := z))
    }

    val rhs = have((z === x) |- in(z, unaryIntersection(pair(x, y)))) subproof {
      val xinxy = have(in(x, unaryIntersection(pair(x, y)))) subproof {
        have(in(singleton(x), pair(x, y))) by Substitution.ApplyRules(pair.shortDefinition)(secondElemInPair of (x := unorderedPair(x, y), y := singleton(x)))
        val exClause = thenHave(exists(b, in(b, pair(x, y)))) by RightExists

        have(in(b, pair(x, y)) |- in(b, pair(x, y))) by Hypothesis
        thenHave(in(b, pair(x, y)) |- in(b, unorderedPair(unorderedPair(x, y), singleton(x)))) by Substitution.ApplyRules(pair.shortDefinition)
        val bp = thenHave(in(b, pair(x, y)) |- (b === singleton(x)) \/ (b === unorderedPair(x, y))) by Substitution.ApplyRules(pairAxiom of (z := b, x := unorderedPair(x, y), y := singleton(x)))

        have(in(x, singleton(x))) by Restate.from(singletonMembership of (y := x))
        val bxx = thenHave((b === singleton(x)) |- in(x, b)) by Substitution.ApplyRules((b === singleton(x)))

        have(in(x, unorderedPair(x, y))) by Restate.from(firstElemInPair)
        val bxy = thenHave((b === unorderedPair(x, y)) |- in(x, b)) by Substitution.ApplyRules((b === unorderedPair(x, y)))

        have(in(b, pair(x, y)) ==> in(x, b)) by Tautology.from(bp, bxx, bxy)
        val frClause = thenHave(forall(b, in(b, pair(x, y)) ==> in(x, b))) by RightForall

        have(thesis) by Tautology.from(defexp of (z := x), exClause, frClause)
      }
      thenHave(thesis) by Substitution.ApplyRules((z === x))
    }

    have(thesis) by Tautology.from(lhs, rhs)
  }

  /**
   * Lemma --- The unary intersection and union of an ordered pair are equal
   * iff the two elements are equal.
   *
   *    `∪ (x, y) = {x} = {x, y} = ∩ (x, y) <=> x = y`
   *
   * See [[pairUnaryIntersection]] and [[unionOfOrderedPair]].
   */
  val pairUnionIntersectionEqual = Lemma(
    () |- (union(pair(x, y)) === unaryIntersection(pair(x, y))) <=> (x === y)
  ) {
    have(in(z, unorderedPair(x, y)) <=> ((z === x) \/ (z === y))) by Restate.from(pairAxiom)
    val unionPair = thenHave(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) by Substitution.ApplyRules(unionOfOrderedPair)

    val fwd = have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (x === y)) subproof {
      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- forall(z, in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y))))) by Weakening(
        extensionalityAxiom of (x := union(pair(x, y)), y := unaryIntersection(pair(x, y)))
      )
      thenHave((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y)))) by InstantiateForall(z)

      have((union(pair(x, y)) === unaryIntersection(pair(x, y))) |- (((z === x) \/ (z === y)) <=> (z === x))) by Tautology.from(lastStep, unionPair, pairUnaryIntersection)
      have(thesis) by Restate.from(lastStep of (z := y))
    }

    val bwd = have((x === y) |- (union(pair(x, y)) === unaryIntersection(pair(x, y)))) subproof {
      have((x === y) |- in(z, union(pair(x, y))) <=> ((z === x) \/ (z === x))) by Substitution.ApplyRules(x === y)(unionPair)
      have((x === y) |- in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y)))) by Tautology.from(lastStep, pairUnaryIntersection)
      thenHave((x === y) |- forall(z, in(z, union(pair(x, y))) <=> in(z, unaryIntersection(pair(x, y))))) by RightForall

      have(thesis) by Cut(lastStep, equalityIntro of (x := union(pair(x, y)), y := unaryIntersection(pair(x, y))))
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

  /**
   * Lemma --- The [[firstInPair]] operation when applied to an ordered pair
   * produces the first element of the pair.
   *
   *    `first((x, y)) = x`
   */
  val firstInPairReduction = Lemma(
    () |- (firstInPair(pair(x, y)) === x)
  ) {
    // z \in \cap (x, y) <=> z = x
    val elemInter = have(in(z, unaryIntersection(pair(x, y))) <=> (z === x)) by Restate.from(pairUnaryIntersection)

    // z in \cup \cap p <=> z \in x
    val elemUnion = have(in(z, union(unaryIntersection(pair(x, y)))) <=> in(z, x)) subproof {
      val unionax =
        have(in(z, union(unaryIntersection(pair(x, y)))) <=> exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t))) by Restate.from(unionAxiom of (x := unaryIntersection(pair(x, y))))

      val lhs = have(exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t)) |- in(z, x)) subproof {
        have(in(z, t) |- in(z, t)) by Hypothesis
        thenHave((in(z, t), (t === x)) |- in(z, x)) by Substitution.ApplyRules(t === x)
        have(in(t, unaryIntersection(pair(x, y))) /\ in(z, t) |- in(z, x)) by Tautology.from(lastStep, elemInter of (z := t))
        thenHave(thesis) by LeftExists
      }

      val rhs = have(in(z, x) |- exists(t, in(t, unaryIntersection(pair(x, y))) /\ in(z, t))) subproof {
        have(in(x, unaryIntersection(pair(x, y)))) by Restate.from(elemInter of (z := x))
        thenHave(in(z, x) |- in(x, unaryIntersection(pair(x, y))) /\ in(z, x)) by Tautology
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(lhs, rhs, unionax)
    }

    thenHave(forall(z, in(z, union(unaryIntersection(pair(x, y)))) <=> in(z, x))) by RightForall

    // \cup \cap (x, y) = x
    val unioneq = have(union(unaryIntersection(pair(x, y))) === x) by Cut(lastStep, equalityIntro of (x := union(unaryIntersection(pair(x, y))), y := x))
    have((firstInPair(pair(x, y)) === union(unaryIntersection(pair(x, y))))) by InstantiateForall(firstInPair(pair(x, y)))(firstInPair.definition of (p := pair(x, y)))
    have(thesis) by Substitution.ApplyRules(lastStep)(unioneq)
  }

  /**
   * Lemma --- The [[secondInPairSingletone]] operation when applied to an
   * ordered pair produces the singleton containing the second element of the pair.
   *
   *    `secondSingleton((x, y)) = {y}`
   *
   * Used for [[secondInPair]] reduction.
   */
  val secondInPairSingletonReduction = Lemma(
    () |- in(z, secondInPairSingleton(pair(x, y))) <=> (z === y)
  ) {
    have(
      forall(
        t,
        in(t, secondInPairSingleton(pair(x, y))) <=> (in(t, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(t, unaryIntersection(pair(x, y))))))
      )
    ) by InstantiateForall(secondInPairSingleton(pair(x, y)))(secondInPairSingleton.definition of (p := pair(x, y)))
    val sipsDef = thenHave(
      in(z, secondInPairSingleton(pair(x, y))) <=> (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y))))))
    ) by InstantiateForall(z)

    val predElem = have((in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y)))))) <=> (z === y)) subproof {

      // breakdown for each of the clauses in the statement
      have(forall(z, in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y)))) by Tautology.from(unionOfOrderedPair, extensionalityAxiom of (x := union(pair(x, y)), y := unorderedPair(x, y)))
      thenHave(in(z, union(pair(x, y))) <=> in(z, unorderedPair(x, y))) by InstantiateForall(z)
      val zUnion = have(in(z, union(pair(x, y))) <=> ((z === x) \/ (z === y))) by Tautology.from(lastStep, pairAxiom)
      val unEqInt = have((union(pair(x, y)) === unaryIntersection(pair(x, y))) <=> (x === y)) by Restate.from(pairUnionIntersectionEqual)
      val zInter = have(in(z, unaryIntersection(pair(x, y))) <=> (z === x)) by Restate.from(pairUnaryIntersection)

      have(
        (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y)))))) <=> (in(z, union(pair(x, y))) /\ ((!(union(
          pair(x, y)
        ) === unaryIntersection(pair(x, y)))) ==> (!in(z, unaryIntersection(pair(x, y))))))
      ) by Restate
      val propDest = thenHave(
        (in(z, union(pair(x, y))) /\ ((!(union(pair(x, y)) === unaryIntersection(pair(x, y)))) ==> (!in(
          z,
          unaryIntersection(pair(x, y))
        )))) <=> (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))
      ) by Substitution.ApplyRules(zUnion, zInter, unEqInt)

      have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) <=> (z === y)) subproof {
        val hypo = have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x)))) |- (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))) by Hypothesis
        thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), (x === y)) |- (((z === y) \/ (z === y)) /\ ((!(y === y)) ==> (!(z === x))))) by Substitution.ApplyRules(x === y)
        val xeqy = thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), (x === y)) |- (z === y)) by Tautology

        have((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), !(x === y)) |- (((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))))) by Weakening(hypo)
        val xneqy = thenHave((((z === x) \/ (z === y)) /\ ((!(x === y)) ==> (!(z === x))), !(x === y)) |- (z === y)) by Tautology

        have(thesis) by Tautology.from(xeqy, xneqy, equalityTransitivity of (z := y, y := z))
      }

      have(thesis) by Tautology.from(lastStep, propDest)
    }

    have(thesis) by Tautology.from(sipsDef, predElem)
  }

  /**
   * Lemma --- The [[secondInPair]] operation when applied to an ordered pair
   * produces the second element of the pair.
   *
   *    `second((x, y)) = y`
   */
  val secondInPairReduction = Lemma(
    () |- secondInPair(pair(x, y)) === y
  ) {
    have(secondInPair(pair(x, y)) === union(secondInPairSingleton(pair(x, y)))) by InstantiateForall(secondInPair(pair(x, y)))(secondInPair.definition of (p := pair(x, y)))
    have(forall(z, in(z, secondInPair(pair(x, y))) <=> in(z, union(secondInPairSingleton(pair(x, y)))))) by Tautology.from(
      lastStep,
      extensionalityAxiom of (x := secondInPair(pair(x, y)), y := union(secondInPairSingleton(pair(x, y))))
    )
    thenHave(in(z, secondInPair(pair(x, y))) <=> in(z, union(secondInPairSingleton(pair(x, y))))) by InstantiateForall(z)
    val secondElem =
      have(in(z, secondInPair(pair(x, y))) <=> (exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b)))) by Tautology.from(lastStep, unionAxiom of (x := secondInPairSingleton(pair(x, y))))

    val elemIsY = have((exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) <=> in(z, y)) subproof {
      val lhs = have((exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) |- in(z, y)) subproof {
        have(in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b) |- in(z, b)) by Restate
        thenHave((in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b), (b === y)) |- in(z, y)) by Substitution.ApplyRules(b === y)
        have((in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b)) |- in(z, y)) by Tautology.from(lastStep, secondInPairSingletonReduction of (z := b))

        thenHave(thesis) by LeftExists
      }

      val rhs = have(in(z, y) |- exists(b, in(b, secondInPairSingleton(pair(x, y))) /\ in(z, b))) subproof {
        have(in(z, y) |- in(z, y)) by Hypothesis
        have(in(z, y) |- in(y, secondInPairSingleton(pair(x, y))) /\ in(z, y)) by Tautology.from(lastStep, secondInPairSingletonReduction of (z := y))
        thenHave(thesis) by RightExists
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    have(in(z, secondInPair(pair(x, y))) <=> in(z, y)) by Tautology.from(secondElem, elemIsY)
    thenHave(forall(z, in(z, secondInPair(pair(x, y))) <=> in(z, y))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x := secondInPair(pair(x, y))))
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

  /**
   * Lemma --- a set is an element of a Cartesian product iff it is a pair containing
   * elements from the constituents of the product.
   *
   *    `t ∈ x * y <=> ∃ a, b. t = (a, b) ∧ a ∈ x ∧ b ∈ y`
   *
   * Asserts a stronger definition of the [[cartesianProduct]]. See
   * [[elemOfPowerPowerUnion]] for the redundancy proof.
   */
  val elemOfCartesianProduct = Lemma(
    in(t, cartesianProduct(x, y)) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))
  ) {
    have(forall(t, in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))))) by InstantiateForall(
      cartesianProduct(x, y)
    )(cartesianProduct.definition)
    val defUnfold = thenHave(in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))) by InstantiateForall(t)

    have(∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) <=> (in(t, powerSet(powerSet(setUnion(x, y)))) /\ ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))))) by Tautology.from(
      elemOfPowerPowerUnion
    )

    have(thesis) by Tautology.from(lastStep, defUnfold)
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
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct of (t := pair(a, b)))
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
    thenHave(thesis) by Substitution.ApplyRules(elemOfCartesianProduct of (t := pair(a, b)))
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
    sorry
  }

  val cartesianProductLeftUnion = Lemma(
    cartesianProduct(setUnion(a, b), c) === setUnion(cartesianProduct(a, c), cartesianProduct(b, c))
  ) {
    val forward = have(in(p, cartesianProduct(setUnion(a, b), c)) ==> in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c)))) subproof {
      val hyp = have(in(secondInPair(p), c) |- in(secondInPair(p), c)) by Hypothesis
      val cartProdIntro = have(in(firstInPair(p), a) /\ in(secondInPair(p), c) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(a, c))) by LeftAnd(cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := a, y := c))

      have((in(firstInPair(p), setUnion(a, b)), in(secondInPair(p), c)) |- (in(firstInPair(p), a), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by RightAnd(setUnionElim of (z := firstInPair(p), x := a, y := b), hyp)
      have((in(firstInPair(p), setUnion(a, b)), in(secondInPair(p), c)) |- (in(firstInPair(p), a) /\ in(secondInPair(p), c), in(firstInPair(p), b) /\ in(secondInPair(p), c))) by RightAnd(lastStep, hyp)
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
      thenHave(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(firstInPair(p), setUnion(a, b)) /\ in(secondInPair(p), c)) by Substitution.ApplyRules(setUnionMembership of (z := firstInPair(p), x := a, y := b))
      val beforeSubst = have(in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, b), c))) by Cut(lastStep, cartesianProdIntro)

      val left = thenHave((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(a, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by 
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := a, y := c))
      
      val right = have((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(b, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by 
        Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := b, y := c))(beforeSubst)

      have((in(p, setUnion(cartesianProduct(a, c), cartesianProduct(b, c))), in(p, cartesianProduct(a, c)) \/ in(p, cartesianProduct(b, c))) |- in(p, cartesianProduct(setUnion(a, b), c))) by LeftOr(left, right)
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
        setUnionLeftIntro of (z := firstInPair(p), x := a, y := c), cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, c), y := setUnion(b, d))
      )
      have((in(firstInPair(p), a), in(secondInPair(p), b)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionLeftIntro of (z := secondInPair(p), x := b, y := d), lastStep
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
        setUnionRightIntro of (z := firstInPair(p), x := a, y := c), cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := setUnion(a, c), y := setUnion(b, d))
      )
      have((in(firstInPair(p), c), in(secondInPair(p), d)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
        setUnionRightIntro of (z := secondInPair(p), x := b, y := d), lastStep
      )
      thenHave(in(firstInPair(p), c) /\ in(secondInPair(p), d) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by LeftAnd
      have(in(p, cartesianProduct(c, d)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(cartesianProductElim of (x := c, y := d), lastStep)
      thenHave(in(p, cartesianProduct(c, d)) |- in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.ApplyRules(pairReconstructionInCartesianProduct of (x := c, y := d))
      thenHave(in(p, cartesianProduct(c, d)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by RightImplies
      thenHave(forall(p, in(p, cartesianProduct(c, d)) ==> in(p, cartesianProduct(setUnion(a, c), setUnion(b, d))))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := cartesianProduct(c, d), y := cartesianProduct(setUnion(a, c), setUnion(b, d))))
    }

    have(subset(cartesianProduct(c, d), cartesianProduct(setUnion(a, c), setUnion(b, d))) |- subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(left, unionOfTwoSubsets of (a := cartesianProduct(a, b), b := cartesianProduct(c, d), c := cartesianProduct(setUnion(a, c), setUnion(b, d))))
    have(thesis) by Cut(right, lastStep)
  }


  /**
   * Lemma --- if a pair is in a set `r`, then elements of the pair are in `∪ ∪ r`.
   *
   *    `(a, b) ∈ r ⊢ a, b ∈ ∪ ∪ r`
   *
   * Used to prove stronger definitions for [[relationDomain]] and [[relationRange]]
   */
  val pairInSetImpliesPairInUnion = Lemma(
    in(pair(a, b), r) |- in(a, union(union(r))) /\ in(b, union(union(r)))
  ) {
    // a, b in {a, b} and union union r
    // {a, b} in union r
    // pair a b in r
    val unionUP = have(in(pair(a, b), r) |- in(unorderedPair(a, b), union(r))) subproof {
      val hypo = have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
      have(in(pair(a, b), r) |- in(unorderedPair(a, b), unorderedPair(unorderedPair(a, b), singleton(a))) /\ in(pair(a, b), r)) by RightAnd(
        hypo,
        firstElemInPair of (x := unorderedPair(a, b), y := singleton(a))
      )
      thenHave(in(pair(a, b), r) |- in(unorderedPair(a, b), pair(a, b)) /\ in(pair(a, b), r)) by Substitution.ApplyRules(pair.shortDefinition of (x := a, y := b))
      thenHave(in(pair(a, b), r) |- ∃(y, in(unorderedPair(a, b), y) /\ in(y, r))) by RightExists
      andThen(Substitution.applySubst(unionAxiom of (z := unorderedPair(a, b), x := r)))
    }
    val unionA = have(in(unorderedPair(a, b), union(r)) |- in(a, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(a, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, firstElemInPair of (x := a, y := b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(a, y) /\ in(y, union(r)))) by RightExists
      andThen(Substitution.applySubst(unionAxiom of (z := a, x := union(r))))
    }
    val unionB = have(in(unorderedPair(a, b), union(r)) |- in(b, union(union(r)))) subproof {
      val hypo = have(in(unorderedPair(a, b), union(r)) |- in(unorderedPair(a, b), union(r))) by Hypothesis
      have(in(unorderedPair(a, b), union(r)) |- in(b, unorderedPair(a, b)) /\ in(unorderedPair(a, b), union(r))) by RightAnd(hypo, secondElemInPair of (x := a, y := b))
      thenHave(in(unorderedPair(a, b), union(r)) |- ∃(y, in(b, y) /\ in(y, union(r)))) by RightExists
      andThen(Substitution.applySubst(unionAxiom of (z := b, x := union(r))))
    }

    have(thesis) by Tautology.from(unionUP, unionA, unionB)
  }

}
