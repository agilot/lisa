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

  /**
   * Binary Relation --- A binary relation `r` from `a` to `b` is a subset of
   * the [[cartesianProduct]] of `a` and `b`, `a * b`. We say `x r y`, `r(x,
   * y)`, or `r relates x to y` for `(x, y) ∈ r`.
   */
  val relationBetween = DEF(r, a, b) --> subset(r, cartesianProduct(a, b))

  val pairReconstructionInRelationBetween = Lemma(
    (relationBetween(r, a, b), in(p, r)) |- p === pair(firstInPair(p), secondInPair(p))
  ) {
    have(relationBetween(r, a, b) |- subset(r, cartesianProduct(a, b))) by Weakening(relationBetween.definition)
    have((relationBetween(r, a, b), in(p, r)) |- in(p, cartesianProduct(a, b))) by Cut(lastStep, subsetElim of (z := p, x := r, y := cartesianProduct(a, b)))
    have(thesis) by Cut(lastStep, pairReconstructionInCartesianProduct of (t := p, x := a, y := b))
  }

  /**
   * Lemma --- Pair in Relation
   *
   * If a pair `(x, y)` exists in a relation `r` from `a` to `b`,
   * then `x` and `y` are elements of `a` and `b` respectively.
   */
  val relationBetweenElimPair = Lemma(
    (relationBetween(r, a, b), in(pair(x, y), r)) |- in(x, a) /\ in(y, b)
  ) {
    have((relationBetween(r, a, b), in(pair(x, y), r)) |- in(pair(x, y), cartesianProduct(a, b))) by Substitution.ApplyRules(relationBetween.definition)(subsetElim of (z := pair(x, y), x := r, y := cartesianProduct(a, b)))
    have(thesis) by Cut(lastStep, cartesianProductElimPair of (x := a, y := b, a := x, b := y))
  }

  val relationBetweenElim = Lemma(
    (relationBetween(r, a, b), in(p, r)) |- in(firstInPair(p), a) /\ in(secondInPair(p), b)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelationBetween)(relationBetweenElimPair of (x := firstInPair(p), y := secondInPair(p)))
  }

  val relationBetweenIntro = Lemma(
    subset(r, cartesianProduct(a, b)) |- relationBetween(r, a, b)
  ) {
    have(thesis) by Weakening(relationBetween.definition)
  }

  val relationBetweenSubset = Lemma(
    (subset(r1, r2), relationBetween(r2, a, b)) |- relationBetween(r1, a, b)
  ) {
    have((subset(r1, r2), relationBetween(r2, a, b)) |- subset(r1, cartesianProduct(a, b))) by 
      Substitution.ApplyRules(relationBetween.definition of (r := r2))(subsetTransitivity of (a := r1, b := r2, c := cartesianProduct(a, b)))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := r1))
  }

  /**
   * Lemma --- the empty set is a relation, the empty relation, between any two sets.
   */
  val emptySetRelation = Lemma(
    relationBetween(emptySet, a, b)
  ) {
    have(thesis) by Cut(emptySetIsASubset of (x := cartesianProduct(a, b)), relationBetweenIntro of (r := emptySet))
  }

  val relationBetweenLeftEmptyIsEmpty = Lemma(
    relationBetween(r, emptySet, b) |- r === emptySet
  ) {
    have(subset(r, emptySet) |- r === emptySet) by Weakening(emptySetIsItsOwnOnlySubset of (x := r))
    thenHave(subset(r, cartesianProduct(emptySet, b)) |- r === emptySet) by Substitution.ApplyRules(cartesianProductLeftEmpty of (y := b))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (a := emptySet))
  }

  val relationBetweenRightEmptyIsEmpty = Lemma(
    relationBetween(r, a, emptySet) |- r === emptySet
  ) {
    have(subset(r, emptySet) |- r === emptySet) by Weakening(emptySetIsItsOwnOnlySubset of (x := r))
    thenHave(subset(r, cartesianProduct(a, emptySet)) |- r === emptySet) by Substitution.ApplyRules(cartesianProductRightEmpty of (x := a))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (b := emptySet))
  }

  /**
   * Lemma --- the empty relation is a relation on the empty set.
   */
  val emptySetRelationOnItself = Lemma(
    relationBetween(emptySet, emptySet, emptySet)
  ) {
    have(thesis) by Restate.from(emptySetRelation of (a := emptySet, b := emptySet))
  }

  /**
   * Lemma --- The union of two relations is a relation
   *
   *    `r1 ⊆ a × b, r2 ⊆ c × d ⊢ r1 ∪ r2 ⊆ (a ∪ c) × (b ∪ d)`
   */
  val unionOfTwoRelationsWithField = Lemma(
    (relationBetween(r1, a, b), relationBetween(r2, c, d)) |- relationBetween(setUnion(r1, r2), setUnion(a, c), setUnion(b, d))
  ) {
    have((subset(r1, cartesianProduct(a, b)), subset(r2, cartesianProduct(c, d)), 
          subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) |- 
         subset(setUnion(r1, r2), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
      unionOfSubsetsOfDifferentSets of (a := r1, b := r2, c := cartesianProduct(a, b), d := cartesianProduct(c, d)),
      subsetTransitivity of (a := setUnion(r1, r2), b := setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), c := cartesianProduct(setUnion(a, c), setUnion(b, d)))
    )
    have((subset(r1, cartesianProduct(a, b)), subset(r2, cartesianProduct(c, d))) |- subset(setUnion(r1, r2), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(unionOfCartesianProducts, lastStep)
    thenHave((relationBetween(r1, a, b), subset(r2, cartesianProduct(c, d))) |- relationBetween(setUnion(r1, r2), setUnion(a, c), setUnion(b, d))) by Substitution.ApplyRules(
      relationBetween.definition of (r := setUnion(r1, r2), a := setUnion(a, c), b := setUnion(b, d)), relationBetween.definition of (r := r1)
    )
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := r2, a := c, b := d))
  }

  val relationBetweenSingleton = Lemma(
    relationBetween(singleton(pair(x, y)), singleton(x), singleton(y))
  ) {
    have(relationBetween(cartesianProduct(singleton(x), singleton(y)), singleton(x), singleton(y))) by Cut(subsetReflexivity of (x :=  cartesianProduct(singleton(x), singleton(y))), relationBetweenIntro of (r := cartesianProduct(singleton(x), singleton(y)), a := singleton(x), b := singleton(y)))
    thenHave(thesis) by Substitution.ApplyRules(singletonCartesianProduct)
  }

  val relationBetweenSubsetDomains = Lemma(
    (relationBetween(r, a, b), subset(a, c), subset(b, d)) |- relationBetween(r, c, d)
  ) {
    have((subset(r, cartesianProduct(a, b)), subset(a, c), subset(b, d)) |- subset(r, cartesianProduct(c, d))) by Cut(cartesianProductSubset of (w := a, x := b, y := c, z := d), subsetTransitivity of (a := r, b := cartesianProduct(a, b), c := cartesianProduct(c, d)))
    thenHave((subset(r, cartesianProduct(a, b)), subset(a, c), subset(b, d)) |- relationBetween(r, c, d)) by Substitution.ApplyRules(relationBetween.definition of (a := c, b := d))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }
  

  val relationDomainUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> ∃(a, in(pair(t, a), r))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))) by UniqueComprehension(
      union(union(r)),
      lambda(t, ∃(a, in(pair(t, a), r)))
    )

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) subproof {
      val hypo = have(in(pair(t, a), r) |- in(pair(t, a), r)) by Hypothesis
      have(in(pair(t, a), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a := t, b := a))
      thenHave(in(pair(t, a), r) |- in(t, union(union(r)))) by Weakening
      thenHave(∃(a, in(pair(t, a), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(∃(a, in(pair(t, a), r)) ==> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by Tautology
      val rhs = have((∃(a, in(pair(t, a), r)) /\ in(t, union(union(r)))) ==> ∃(a, in(pair(t, a), r))) by Restate

      val subst = have(∃(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by RightIff(lhs, rhs)

      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) by Hypothesis
      val cutRhs = thenHave(
        (in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))), ∃(a, in(pair(t, a), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(
          a,
          in(pair(t, a), r)
        ))
      ) by RightSubstIff.withParametersSimple(List((∃(a, in(pair(t, a), r)), in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))), lambda(h, in(t, z) <=> h))
      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(a, in(pair(t, a), r)))) by Cut(subst, cutRhs)
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- in(t, z) <=> (∃(a, in(pair(t, a), r)))) by LeftForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r))))) by RightForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by RightExists
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(
      ∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))
    ) by Restate.from(existsOneImpliesExists of (P := lambda(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r)))))))
    val cutR = have(∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Restate.from(
      uniqueByExtension of (schemPred := lambda(t, (∃(a, in(pair(t, a), r)))))
    )

    val trL =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Cut(cutL, transform)
    val trR =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(t, a), r)))))) by Cut(trL, cutR)

    have(thesis) by Cut.withParameters(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(t, a), r))))))(uniq, trR)
  }

  /**
   * (Binary) Relation Domain --- The set containing the first elements of every
   * pair in a relation `r`. Alternatively, the set of elements which are
   * related to another element by `r`.
   *
   *      `dom(r) = {z ∈ ∪ ∪ r | ∃ t. (z, t) ∈ r}`
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * The first part is proved redundant by [[pairInSetImpliesPairInUnion]].
   * We have,
   *
   *      `dom(r) = {z | ∃ t. (z, t) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationDomain = DEF(r) --> The(z, ∀(t, in(t, z) <=> ∃(a, in(pair(t, a), r))))(relationDomainUniqueness)

  val relationDomainMembership = Lemma(
    in(a, relationDomain(r)) <=> ∃(b, in(pair(a, b), r))
  ) {
    have(∀(t, in(t, relationDomain(r)) <=> ∃(b, in(pair(t, b), r)))) by InstantiateForall(relationDomain(r))(relationDomain.definition)
    thenHave(thesis) by InstantiateForall(a)
  }

  /**
    * Lemma --- Relation Domain Introduction Rule
    * 
    *   `(a, b) ∈ r ⊢ a ∈ dom(r)`
    */
  val relationDomainIntro = Lemma(
    in(pair(a, b), r) |- in(a, relationDomain(r))
  ) {
    have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
    thenHave(in(pair(a, b), r) |- exists(b, in(pair(a, b), r))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationDomainMembership)
  }

  val relationDomainElim = Lemma(
    in(a, relationDomain(r)) |- ∃(b, in(pair(a, b), r))
  ) {
    have(thesis) by Weakening(relationDomainMembership)
  }

  val relationDomainSingleton = Lemma(
    relationDomain(singleton(pair(a, b))) === singleton(a)
  ) {
    val backward = have(in(x, singleton(a)) ==> in(x, relationDomain(singleton(pair(a, b))))) subproof {
      have(in(a, relationDomain(singleton(pair(a, b))))) by Cut(singletonIntro of (x := pair(a, b)), relationDomainIntro of (r := singleton(pair(a, b))))
      thenHave(in(x, singleton(a)) |- in(x, relationDomain(singleton(pair(a, b))))) by Substitution.ApplyRules(singletonElim of (y := x, x := a))
    }

    val forward = have(in(x, relationDomain(singleton(pair(a, b)))) ==> in(x, singleton(a))) subproof {
      have(pair(x, c) === pair(a, b) |- x === a) by Weakening(pairExtensionality of (a := x, b := c, c := a, d := b))
      have(in(pair(x, c), singleton(pair(a, b))) |- x === a) by Cut(singletonElim of (y := pair(x, c), x := pair(a, b)), lastStep)
      thenHave(exists(c, in(pair(x, c), singleton(pair(a, b)))) |- x === a) by LeftExists
      val xEqA = have(in(x, relationDomain(singleton(pair(a, b)))) |- x === a) by Cut(relationDomainElim of (a := x, r := singleton(pair(a, b))), lastStep)
      have(x === a |- in(x, singleton(a))) by RightSubstEq.withParametersSimple(List((x, a)), lambda(x, in(x, singleton(a))))(singletonIntro of (x := a))
      have(in(x, relationDomain(singleton(pair(a, b)))) |- in(x, singleton(a))) by Cut(xEqA, lastStep)

    }

    have(in(x, relationDomain(singleton(pair(a, b)))) <=> in(x, singleton(a))) by RightIff(forward, backward)
    thenHave(forall(x, in(x, relationDomain(singleton(pair(a, b)))) <=> in(x, singleton(a)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationDomain(singleton(pair(a, b))), y := singleton(a)))
  }

  val relationDomainSetUnion = Lemma(
    relationDomain(setUnion(r1, r2)) === setUnion(relationDomain(r1), relationDomain(r2))
  ) {
    val forward = have(in(a, relationDomain(setUnion(r1, r2))) ==> in(a, setUnion(relationDomain(r1), relationDomain(r2)))) subproof {
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r1)), in(pair(a, b), r2))) by Cut(setUnionElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntro of (r := r1))
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r1)), in(a, relationDomain(r2)))) by Cut(lastStep, relationDomainIntro of (r := r2))
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r2)), in(a, setUnion(relationDomain(r1), relationDomain(r2))))) by Cut(lastStep, setUnionLeftIntro of (z := a, x := relationDomain(r1), y := relationDomain(r2)))
      have(in(pair(a, b), setUnion(r1, r2)) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by Cut(lastStep, setUnionRightIntro of (z := a, x := relationDomain(r1), y := relationDomain(r2)))
      thenHave(exists(b, in(pair(a, b), setUnion(r1, r2))) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by LeftExists
      have(in(a, relationDomain(setUnion(r1, r2))) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by Cut(relationDomainElim of (r := setUnion(r1, r2)), lastStep)
    }

    val backward = have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) ==> in(a, relationDomain(setUnion(r1, r2)))) subproof {

      have(in(pair(a, b), r1) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by RightExists(setUnionLeftIntro of (z := pair(a, b), x := r1, y := r2))
      val left = thenHave(exists(b, in(pair(a, b), r1)) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by LeftExists

      have(in(pair(a, b), r2) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by RightExists(setUnionRightIntro of (z := pair(a, b), x := r1, y := r2))
      val right = thenHave(exists(b, in(pair(a, b), r2)) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by LeftExists

      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), r1)), in(a, relationDomain(r2)))) by Cut(setUnionElim of (z := a, x := relationDomain(r1), y := relationDomain(r2)), relationDomainElim of (r := r1))
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), r1)), exists(b, in(pair(a, b), r2)))) by Cut(lastStep, relationDomainElim of (r := r2))
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), setUnion(r1, r2))), exists(b, in(pair(a, b), r2)))) by Cut(lastStep, left)
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by Cut(lastStep, right)
      thenHave(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- in(a, relationDomain(setUnion(r1, r2)))) by Substitution.ApplyRules(relationDomainMembership of (r := setUnion(r1, r2)))
    }

    have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) <=> in(a, relationDomain(setUnion(r1, r2)))) by RightIff(forward, backward)
    thenHave(forall(a, in(a, setUnion(relationDomain(r1), relationDomain(r2))) <=> in(a, relationDomain(setUnion(r1, r2))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationDomain(setUnion(r1, r2)), y := setUnion(relationDomain(r1), relationDomain(r2))))
  }

  val relationDomainSubset = Lemma(
    subset(r1, r2) |- subset(relationDomain(r1), relationDomain(r2))
  ) {
    have((subset(r1, r2), in(pair(a, b), r1)) |- in(a, relationDomain(r2))) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntro of (r := r2))
    thenHave((subset(r1, r2), exists(b, in(pair(a, b), r1))) |- in(a, relationDomain(r2))) by LeftExists
    have((subset(r1, r2), in(a, relationDomain(r1))) |- in(a, relationDomain(r2))) by Cut(relationDomainElim of (r := r1), lastStep)
    thenHave(subset(r1, r2) |- in(a, relationDomain(r1)) ==> in(a, relationDomain(r2))) by RightImplies
    thenHave(subset(r1, r2) |- forall(a, in(a, relationDomain(r1)) ==> in(a, relationDomain(r2)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationDomain(r1), y := relationDomain(r2)))
  }

  val relationRangeUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> ∃(a, in(pair(a, t), r))))
  ) {
    val uniq = have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))) by UniqueComprehension(
      union(union(r)),
      lambda(t, ∃(a, in(pair(a, t), r)))
    )

    // eliminating t \in UU r
    // since it is implied by the second condition
    val transform = have(∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) subproof {
      val hypo = have(in(pair(a, t), r) |- in(pair(a, t), r)) by Hypothesis
      have(in(pair(a, t), r) |- in(t, union(union(r))) /\ in(a, union(union(r)))) by Cut(hypo, pairInSetImpliesPairInUnion of (a := a, b := t))
      thenHave(in(pair(a, t), r) |- in(t, union(union(r)))) by Weakening
      thenHave(∃(a, in(pair(a, t), r)) |- in(t, union(union(r)))) by LeftExists
      val lhs = thenHave(∃(a, in(pair(a, t), r)) ==> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by Tautology
      val rhs = have((∃(a, in(pair(a, t), r)) /\ in(t, union(union(r)))) ==> ∃(a, in(pair(a, t), r))) by Restate

      val subst = have(∃(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by RightIff(lhs, rhs)

      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) by Hypothesis
      val cutRhs = thenHave(
        (in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))), ∃(a, in(pair(a, t), r)) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(
          a,
          in(pair(a, t), r)
        ))
      ) by RightSubstIff.withParametersSimple(List((∃(a, in(pair(a, t), r)), in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))), lambda(h, in(t, z) <=> h))
      have((in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(a, in(pair(a, t), r)))) by Cut(subst, cutRhs)
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- in(t, z) <=> (∃(a, in(pair(a, t), r)))) by LeftForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r))))) by RightForall
      thenHave(∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by RightExists
      thenHave(thesis) by LeftExists
    }

    // converting the exists to existsOne
    val cutL = have(
      ∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))
    ) by Restate.from(existsOneImpliesExists of (P := lambda(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r)))))))
    val cutR = have(∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Restate.from(
      uniqueByExtension of (schemPred := lambda(t, (∃(a, in(pair(a, t), r)))))
    )

    val trL =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Cut(cutL, transform)
    val trR =
      have(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))) |- ∃!(z, ∀(t, in(t, z) <=> (∃(a, in(pair(a, t), r)))))) by Cut(trL, cutR)

    have(thesis) by Cut.withParameters(∃!(z, ∀(t, in(t, z) <=> (in(t, union(union(r))) /\ ∃(a, in(pair(a, t), r))))))(uniq, trR)
  }

  /**
   * (Binary) Relation Range --- The set containing the second elements of every
   * pair in a relation `r`. Alternatively, the set of elements which another
   * element relates to by `r`.
   *
   *      `range(r) = {z ∈ ∪ ∪ r | ∃ t. (t, z) ∈ r}
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * The first part is proved redundant by [[pairInSetImpliesPairInUnion]].
   * We have,
   *
   *      `range(r) = {z | ∃ t. (t, z) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationRange = DEF(r) --> The(z, ∀(t, in(t, z) <=> ∃(a, in(pair(a, t), r))))(relationRangeUniqueness)

  val relationRangeMembership = Lemma(
    in(b, relationRange(r)) <=> ∃(a, in(pair(a, b), r))
  ) {
    have(∀(t, in(t, relationRange(r)) <=> ∃(a, in(pair(a, t), r)))) by InstantiateForall(relationRange(r))(relationRange.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  val relationRangeIntro = Lemma(
    in(pair(a, b), r) |- in(b, relationRange(r))
  ) {
    have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
    thenHave(in(pair(a, b), r) |- exists(a, in(pair(a, b), r))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationRangeMembership)
  }

  val relationRangeElim = Lemma(
    in(b, relationRange(r)) |- ∃(a, in(pair(a, b), r))
  ) {
    have(thesis) by Weakening(relationRangeMembership)
  }

  /**
   * Lemma --- The range of the empty function is empty.
   *
   *     `Ran(∅) = ∅`
   */
  val rangeEmpty = Lemma(relationRange(emptySet) === emptySet) {
    have(forall(a, !in(pair(a, b), emptySet))) by RightForall(emptySetAxiom of (x := pair(a, b)))
    thenHave(exists(a, in(pair(a, b), emptySet)) |- ()) by Restate
    have(in(b, relationRange(emptySet)) |- ()) by Cut(relationRangeElim of (r := emptySet), lastStep)
    thenHave(exists(b, in(b, relationRange(emptySet))) |- ()) by LeftExists
    have(!(relationRange(emptySet) === emptySet) |- ()) by Cut(nonEmptySetHasAnElement of (x := relationRange(emptySet)), lastStep)
  }

  val relationRangeSubset = Lemma(
    subset(r1, r2) |- subset(relationRange(r1), relationRange(r2))
  ) {
    have((subset(r1, r2), in(pair(a, b), r1)) |- in(b, relationRange(r2))) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationRangeIntro of (r := r2))
    thenHave((subset(r1, r2), exists(a, in(pair(a, b), r1))) |- in(b, relationRange(r2))) by LeftExists
    have((subset(r1, r2), in(b, relationRange(r1))) |- in(b, relationRange(r2))) by Cut(relationRangeElim of (r := r1), lastStep)
    thenHave(subset(r1, r2) |- in(b, relationRange(r1)) ==> in(b, relationRange(r2))) by RightImplies
    thenHave(subset(r1, r2) |- forall(b, in(b, relationRange(r1)) ==> in(b, relationRange(r2)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(r1), y := relationRange(r2)))
  }

  val pairInRelation = Lemma(
    in(pair(a, b), r) |- in(a, relationDomain(r)) /\ in(b, relationRange(r))
  ) {
    have(thesis) by RightAnd(relationDomainIntro, relationRangeIntro)
  }

  val relationBetweenBetweenDomainAndRange = Lemma(
    relationBetween(r, a, b) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), relationRange(r)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(relationDomain(r), relationRange(r)))) by LeftAnd(cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := relationDomain(r), y := relationRange(r)))
    have(in(pair(firstInPair(p), secondInPair(p)), r) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(relationDomain(r), relationRange(r)))) by Cut(pairInRelation of (a := firstInPair(p), b := secondInPair(p)), lastStep)
    thenHave((relationBetween(r, a, b), in(p, r)) |- in(p, cartesianProduct(relationDomain(r), relationRange(r)))) by Substitution.ApplyRules(pairReconstructionInRelationBetween)
    thenHave(relationBetween(r, a, b) |- in(p, r) ==> in(p, cartesianProduct(relationDomain(r), relationRange(r)))) by RightImplies
    thenHave(relationBetween(r, a, b) |- forall(p, in(p, r) ==> in(p, cartesianProduct(relationDomain(r), relationRange(r))))) by RightForall
    have(relationBetween(r, a, b) |- subset(r, cartesianProduct(relationDomain(r), relationRange(r)))) by Cut(lastStep, subsetIntro of (x := r, y := cartesianProduct(relationDomain(r), relationRange(r))))
    have(thesis) by Cut(lastStep, relationBetweenIntro of (a := relationDomain(r), b := relationRange(r)))
  }



  /**
   * `r` is a relation *from* `a` if there exists a set `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relationFrom = DEF(r, a) --> ∃(b, relationBetween(r, a, b))

  val relationBetweenIsRelationFrom = Lemma(relationBetween(r, a, b) |- relationFrom(r, a)) {
    have(relationBetween(r, a, b) |- relationBetween(r, a, b)) by Hypothesis
    thenHave(relationBetween(r, a, b) |- exists(b, relationBetween(r, a, b))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val pairReconstructionInRelationFrom = Lemma(
    (relationFrom(r, a), in(p, r)) |- p === pair(firstInPair(p), secondInPair(p))
  ) {
    have((exists(b, relationBetween(r, a, b)), in(p, r)) |- p === pair(firstInPair(p), secondInPair(p))) by LeftExists(pairReconstructionInRelationBetween)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  /**
   * Lemma --- Pair in Relation
   *
   * If a pair `(x, y)` exists in a relation `r` from `a` to `b`,
   * then `x` and `y` are elements of `a` and `b` respectively.
   */
  val relationFromElimPair = Lemma(
    (relationFrom(r, a), in(pair(x, y), r)) |- in(x, a)
  ) {
    have((relationBetween(r, a, b), in(pair(x, y), r)) |- in(x, a)) by Weakening(relationBetweenElimPair)
    thenHave((exists(b, relationBetween(r, a, b)), in(pair(x, y), r)) |- in(x, a)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val relationFromElim = Lemma(
    (relationFrom(r, a), in(p, r)) |- in(firstInPair(p), a)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelationFrom)(relationFromElimPair of (x := firstInPair(p), y := secondInPair(p)))
  }

  val relationFromSubset = Lemma(
    (subset(r1, r2), relationFrom(r2, a)) |- relationFrom(r1, a)
  ) {
    have((subset(r1, r2), relationBetween(r2, a, b)) |- relationFrom(r1, a)) by Cut(relationBetweenSubset, relationBetweenIsRelationFrom of (r := r1))
    thenHave((subset(r1, r2), exists(b, relationBetween(r2, a, b))) |- relationFrom(r1, a)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition of (r := r2))
  }

  val relationFromSetUnion = Lemma(
    (relationFrom(r1, a), relationFrom(r2, b)) |- relationFrom(setUnion(r1, r2), setUnion(a, b))
  ) {
    have((relationBetween(r1, a, x), relationBetween(r2, b, y)) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by RightExists(unionOfTwoRelationsWithField of (c := b, b := x, d := y))
    thenHave((exists(x, relationBetween(r1, a, x)), relationBetween(r2, b, y)) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by LeftExists
    thenHave((exists(x, relationBetween(r1, a, x)), exists(y, relationBetween(r2, b, y))) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(
      relationFrom.definition of (r := setUnion(r1, r2), a := setUnion(a, b)), relationFrom.definition of (r := r1), relationFrom.definition of (r := r2, a := b)
    )
  }

  val relationFromBetweenDomainAndRange = Lemma(
    relationFrom(r, a) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(exists(b, relationBetween(r, a, b)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists(relationBetweenBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }




  /**
   * `r` is a relation if there exist sets `a` and `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relation = DEF(r) --> ∃(a, relationFrom(r, a))

  val pairReconstructionInRelation = Lemma(
    (relation(r), in(p, r)) |- p === pair(firstInPair(p), secondInPair(p))
  ) {
    have((exists(a, relationFrom(r, a)), in(p, r)) |- p === pair(firstInPair(p), secondInPair(p))) by LeftExists(pairReconstructionInRelationFrom)
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationElim = Lemma(
    (relation(r), in(p, r)) |- in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), relationRange(r))
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(pairInRelation of (a := firstInPair(p), b := secondInPair(p)))
  }

  val relationFromIsRelation = Lemma(relationFrom(r, a) |- relation(r)) {
    have(relationFrom(r, a) |- relationFrom(r, a)) by Hypothesis
    thenHave(relationFrom(r, a) |- exists(a, relationFrom(r, a))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationBetweenIsRelation = Lemma(relationBetween(r, a, b) |- relation(r)) {
    have(thesis) by Cut(relationBetweenIsRelationFrom, relationFromIsRelation)
  }

  val relationSubset = Lemma(
    (subset(r1, r2), relation(r2)) |- relation(r1)
  ) {
    have((subset(r1, r2), relationFrom(r2, a)) |- relation(r1)) by Cut(relationFromSubset, relationFromIsRelation of (r := r1))
    thenHave((subset(r1, r2), exists(a, relationFrom(r2, a))) |- relation(r1)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition of (r := r2))
  }

  /**
   * Lemma --- the union of two relations is a relation. (weaker form)
   *
   * Weakening of [[unionOfTwoRelationsWithField]] to unknown fields.
   */
  val relationSetUnion = Lemma(
    (relation(r1), relation(r2)) |- relation(setUnion(r1, r2))
  ) {
    have((relationFrom(r1, a), relationFrom(r2, b)) |- exists(y, relationFrom(setUnion(r1, r2), y))) by RightExists(relationFromSetUnion)
    thenHave((exists(a, relationFrom(r1, a)), relationFrom(r2, b)) |- exists(y, relationFrom(setUnion(r1, r2), y))) by LeftExists
    thenHave((exists(a, relationFrom(r1, a)), exists(b, relationFrom(r2, b))) |- exists(y, relationFrom(setUnion(r1, r2), y))) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition of (r := setUnion(r1, r2)), relation.definition of (r := r1), relation.definition of (r := r2))
  }

  /**
   * Lemma --- the union of a set of relations is a relation itself.
   *
   *    `\forall t \in z. relation(t) |- relation(union(z))`
   *
   * This implication also holds in the other direction, but that is
   * not as useful.
   */
  val unionOfRelationSet = Lemma(
    forall(r, in(r, z) ==> relation(r)) |- relation(union(z))
  ) {
    val doms = variable
    val rans = variable
    val domsDef = forall(x, in(x, doms) <=> exists(r, in(r, z) /\ (x === relationDomain(r))))
    val ransDef = forall(x, in(x, rans) <=> exists(r, in(r, z) /\ (x === relationRange(r))))
    
    val inDoms = have((domsDef, in(r, z), in(firstInPair(p), relationDomain(r))) |- in(firstInPair(p), union(doms))) subproof {
      have(in(r, z) |- in(r, z) /\ (relationDomain(r) === relationDomain(r))) by Restate
      val exDoms = thenHave(in(r, z) |- exists(r2, in(r2, z) /\ (relationDomain(r) === relationDomain(r2)))) by RightExists
      have(domsDef |- domsDef) by Hypothesis
      thenHave(domsDef |- in(relationDomain(r), doms) <=> exists(r2, in(r2, z) /\ (relationDomain(r) === relationDomain(r2)))) by InstantiateForall(relationDomain(r))
      thenHave((domsDef, exists(r2, in(r2, z) /\ (relationDomain(r) === relationDomain(r2)))) |- in(relationDomain(r), doms)) by Weakening
      have((domsDef, in(r, z)) |- in(relationDomain(r), doms)) by Cut(exDoms, lastStep)
      have((domsDef, in(r, z)) |- subset(relationDomain(r), union(doms))) by Cut(lastStep, inSetSubsetUnion of (x := relationDomain(r), y := doms))
      have(thesis) by Cut(lastStep, subsetElim of (z := firstInPair(p), x := relationDomain(r), y := union(doms)))
    } 

    val inRans = have((ransDef, in(r, z), in(secondInPair(p), relationRange(r))) |- in(secondInPair(p), union(rans))) subproof {
      have(in(r, z) |- in(r, z) /\ (relationRange(r) === relationRange(r))) by Restate
      val exDoms = thenHave(in(r, z) |- exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) by RightExists
      have(ransDef |- ransDef) by Hypothesis
      thenHave(ransDef |- in(relationRange(r), rans) <=> exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) by InstantiateForall(relationRange(r))
      thenHave((ransDef, exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) |- in(relationRange(r), rans)) by Weakening
      have((ransDef, in(r, z)) |- in(relationRange(r), rans)) by Cut(exDoms, lastStep)
      have((ransDef, in(r, z)) |- subset(relationRange(r), union(rans))) by Cut(lastStep, inSetSubsetUnion of (x := relationRange(r), y := rans))
      have(thesis) by Cut(lastStep, subsetElim of (z := secondInPair(p), x := relationRange(r), y := union(rans)))
    } 

    val relSet = forall(r, in(r, z) ==> relation(r))
    have(relSet |- relSet) by Hypothesis
    val relSetMembership = thenHave((relSet, in(r, z)) |- relation(r)) by InstantiateForall(r)

    val inCartProduct = have(in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(union(doms), union(rans)))) by LeftAnd(cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := union(doms), y := union(rans)))

    have((domsDef, ransDef, in(r, z), in(firstInPair(p), relationDomain(r)), in(secondInPair(p), relationRange(r))) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))) by RightAnd(inDoms, inRans)
    thenHave((domsDef, ransDef, in(r, z), in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), relationRange(r))) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))) by LeftAnd
    have((domsDef, ransDef, in(p, r), relation(r), in(r, z)) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))) by Cut(relationElim, lastStep)
    have((domsDef, ransDef, in(p, r), relation(r), in(r, z)) |-in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(union(doms), union(rans)))) by Cut(lastStep, inCartProduct)
    thenHave((domsDef, ransDef, in(p, r), relation(r), in(r, z)) |- in(p, cartesianProduct(union(doms), union(rans)))) by Substitution.ApplyRules(pairReconstructionInRelation)
    have((domsDef, ransDef, relSet, in(p, r), in(r, z)) |- in(p, cartesianProduct(union(doms), union(rans)))) by Cut(relSetMembership, lastStep)
    thenHave((domsDef, ransDef, relSet, in(p, r) /\ in(r, z)) |- in(p, cartesianProduct(union(doms), union(rans)))) by LeftAnd
    thenHave((domsDef, ransDef, relSet, exists(r, in(p, r) /\ in(r, z))) |- in(p, cartesianProduct(union(doms), union(rans)))) by LeftExists
    have((domsDef, ransDef, relSet, in(p, union(z))) |- in(p, cartesianProduct(union(doms), union(rans)))) by Cut(unionElim of (x := z, z := p), lastStep)
    thenHave((domsDef, ransDef, relSet) |- in(p, union(z)) ==> in(p, cartesianProduct(union(doms), union(rans)))) by RightImplies
    thenHave((domsDef, ransDef, relSet) |- forall(p, in(p, union(z)) ==> in(p, cartesianProduct(union(doms), union(rans))))) by RightForall
    have((domsDef, ransDef, relSet) |- subset(union(z), cartesianProduct(union(doms), union(rans)))) by Cut(lastStep, subsetIntro of (x := union(z), y := cartesianProduct(union(doms), union(rans))))
    have((domsDef, ransDef, relSet) |- relationBetween(union(z), union(doms), union(rans))) by Cut(lastStep, relationBetweenIntro of (r := union(z), a := union(doms), b := union(rans)))
    have((domsDef, ransDef, relSet) |- relation(union(z))) by Cut(lastStep, relationBetweenIsRelation of (r := union(z), a := union(doms), b := union(rans)))
    thenHave((exists(doms, domsDef), ransDef, relSet) |- relation(union(z))) by LeftExists
    thenHave((exists(doms, domsDef), exists(rans, ransDef), relSet) |- relation(union(z))) by LeftExists
    have((existsOne(doms, domsDef), exists(rans, ransDef), relSet) |- relation(union(z))) by Cut(existsOneImpliesExists of (P := lambda(doms, domsDef)), lastStep)
    have((existsOne(doms, domsDef), existsOne(rans, ransDef), relSet) |- relation(union(z))) by Cut(existsOneImpliesExists of (P := lambda(rans, ransDef)), lastStep)
    have((existsOne(rans, ransDef), relSet) |- relation(union(z))) by Cut(replacementClassFunction of (A := z, F := lambda(r, relationDomain(r))), lastStep)
    have(thesis) by Cut(replacementClassFunction of (A := z, F := lambda(r, relationRange(r))), lastStep)

  }



  val relationBetweenDomainAndRange = Lemma(
    relation(r) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(exists(a, relationFrom(r, a)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists(relationFromBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationFromDomain = Lemma(
    relation(r) |- relationFrom(r, relationDomain(r))
  ) {
    have(thesis) by Cut(relationBetweenDomainAndRange, relationBetweenIsRelationFrom of (a := relationDomain(r), b := relationRange(r)))
  }

  val relationDomainEmpty = Lemma(
    (relation(r), relationDomain(r) === emptySet) |- r === emptySet
  ) {
    have((relation(r), relationDomain(r) === emptySet) |- relationBetween(r, emptySet, relationRange(r))) by 
      RightSubstEq.withParametersSimple(List((relationDomain(r), emptySet)), lambda(x, relationBetween(r, x, relationRange(r))))(relationBetweenDomainAndRange)
    have(thesis) by Cut(lastStep, relationBetweenLeftEmptyIsEmpty of (b := relationRange(r)))
  }

  val relationRangeEmpty = Lemma(
    (relation(r), relationRange(r) === emptySet) |- r === emptySet
  ) {
    have((relation(r), relationRange(r) === emptySet) |- relationBetween(r, relationDomain(r), emptySet)) by 
      RightSubstEq.withParametersSimple(List((relationRange(r), emptySet)), lambda(x, relationBetween(r, relationDomain(r), x)))(relationBetweenDomainAndRange)
    have(thesis) by Cut(lastStep, relationBetweenRightEmptyIsEmpty of (a := relationDomain(r)))
  }


  /**
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) ∧ ∀ x. (∃ y. (x, y) ∈ f) ⟹ (∃! y. (x, y) ∈ f)`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> relation(f) /\ ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))

  val functionalIsRelation = Lemma(
    functional(f) |- relation(f)
  ) {
    have(thesis) by Weakening(functional.definition)
  }

  /**
   * Lemma --- Function Introduction Rule
   * 
   *    `relation(f), ∀ x. ∀ y. ∀ z. (x, y) ∈ f ∧ (x, z) ∈ f ⟹ y = z |- functional(f)`
   */
  val functionalIntro = Lemma(
    (relation(f), ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) |- functional(f)
  ) {
    have(thesis) by Weakening(functional.definition)
  }

  /**
   * Lemma --- a function cannot have two pairs representing different values
   * for a given element.
   *
   *    `functional(f) /\ (x, y) \in f /\ (x, z) \in f /\ !(y = z) |- \bot`
   */
  val functionalElim = Lemma(
    (functional(f), in(pair(x, y), f), in(pair(x, z), f)) |- y === z
  ) {
    have(functional(f) |- ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) by Weakening(functional.definition)
    thenHave(functional(f) |- ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z)))) by InstantiateForall(x)
    thenHave(functional(f) |- ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- Subset of functions are functions
   * 
   *   `functional(g), f ⊆ g |- functional(f)`
   */
  val functionalSubset = Lemma(
    (functional(g), subset(f, g)) |- functional(f)
  ) {
    have((functional(g), subset(f, g), in(pair(x, y), f), in(pair(x, z), g)) |- y === z) by Cut(subsetElim of (z := pair(x, y), x := f, y := g), functionalElim of (f := g))
    have((functional(g), subset(f, g), in(pair(x, y), f), in(pair(x, z), f)) |- y === z) by Cut(subsetElim of (z := pair(x, z), x := f, y := g), lastStep)
    thenHave((functional(g), subset(f, g)) |- in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z)) by Restate
    thenHave((functional(g), subset(f, g)) |- forall(z, (in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z)))) by RightForall
    thenHave((functional(g), subset(f, g)) |- forall(y, forall(z, (in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z))))) by RightForall
    thenHave((functional(g), subset(f, g)) |- ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) by RightForall
    have((functional(g), subset(f, g), relation(f)) |- functional(f)) by Cut(lastStep, functionalIntro of (f := f))
    have((functional(g), subset(f, g), relation(g)) |- functional(f)) by Cut(relationSubset of (r1 := f, r2 := g), lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }



  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[relationDomain]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (relationDomain(f) === x)




  /**
   * Lemma --- A function with domain x has domain x
   *
   *   `functionalOver(f, x) |- dom(f) = x`
   */
  val functionalOverDomain = Lemma(
    functionalOver(f, x) |- relationDomain(f) === x
  ) {
    have(thesis) by Weakening(functionalOver.definition)
  }

  /**
   * Lemma --- A total function is partial
   *
   *  `functionalOver(f, x) |- functional(f)`
   */
  val functionalOverIsFunctional = Lemma(
    functionalOver(f, x) |- functional(f)
  ) {
    have(thesis) by Weakening(functionalOver.definition)
  }

  val functionalOverIntro = Lemma(
    functional(f) |- functionalOver(f, relationDomain(f))
  ) {
    have(thesis) by Weakening(functionalOver.definition of (x := relationDomain(f)))
  }

  val functionalOverSingleton = Lemma(
    functionalOver(singleton(pair(x, y)), singleton(x))
  ) {
    val pairExtensionality1 = have(pair(z, a) === pair(x, y) |- a === y) by Weakening(pairExtensionality of (a := z, b := a, c := x, d := y))
    val pairExtensionality2 = have(pair(z, b) === pair(x, y) |- b === y) by Weakening(pairExtensionality of (a := z, c := x, d := y))

    have(in(pair(z, a), singleton(pair(x, y))) |- a === y) by Cut(singletonElim of (y := pair(z, a), x := pair(x, y)), pairExtensionality1)
    have((in(pair(z, a), singleton(pair(x, y))), b === y) |- a === b) by Cut(lastStep, equalityTransitivity of (x := a, z := b))
    have((in(pair(z, a), singleton(pair(x, y))), pair(z, b) === pair(x, y)) |- a === b) by Cut(pairExtensionality2, lastStep)
    have((in(pair(z, a), singleton(pair(x, y))), in(pair(z, b), singleton(pair(x, y)))) |- a === b) by Cut(singletonElim of (y := pair(z, b), x := pair(x, y)), lastStep)
    thenHave((in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b)) by Restate
    thenHave(forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b))) by RightForall
    thenHave(forall(a, forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b)))) by RightForall
    thenHave(forall(z, forall(a, forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b))))) by RightForall
    have(relation(singleton(pair(x, y))) |- functional(singleton(pair(x, y)))) by Cut(lastStep, functionalIntro of (f := singleton(pair(x, y))))
    have(relationBetween(singleton(pair(x, y)), singleton(x), singleton(y)) |- functional(singleton(pair(x, y)))) by Cut(relationBetweenIsRelation of (r := singleton(pair(x, y)), a := singleton(x), b := singleton(y)), lastStep)
    have(functional(singleton(pair(x, y)))) by Cut(relationBetweenSingleton, lastStep)
    have(functionalOver(singleton(pair(x, y)), relationDomain(singleton(pair(x, y))))) by Cut(lastStep, functionalOverIntro of (f := singleton(pair(x, y))))
    thenHave(thesis) by Substitution.ApplyRules(relationDomainSingleton)
  }



  val setOfFunctionsUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))
  ) {
    have(thesis) by UniqueComprehension(powerSet(cartesianProduct(x, y)), lambda(t, functionalOver(t, x)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x → y` or
   * `→(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a ∈
   * x, b ∈ y`, it is a filtering on the power set of their product, i.e. `x
   * → y ⊆ PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f ∈ x → y` or `f: x → y`.
   */
  val functionFrom = DEF(f, x, y) --> in(f, setOfFunctions(x, y))

  /**
   * Lemma --- A function between two sets is [[functional]]
   */
  val functionFromIsFunctionalOver = Lemma(
    functionFrom(f, x, y) |- functionalOver(f, x)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)
    thenHave(in(f, setOfFunctions(x, y)) |- functionalOver(f, x)) by Weakening
    thenHave(thesis) by Substitution.ApplyRules(functionFrom.definition)
  }

  /**
   * Lemma --- A function between two sets is [[functional]]
   */
  val functionFromIsFunctional = Lemma(
    functionFrom(f, x, y) |- functional(f)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverIsFunctional)
  }

  /**
   * Lemma --- The domain of a function from `x` to `y` is `x`.
   *
   *   `f ∈ x → y ⊢ dom(f) = x`
   */
  val functionFromImpliesDomainEq = Lemma(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverDomain)
  }

  /**
   * Lemma --- The range of a function is a subset of its codomain.
   *
   *   `f ∈ x → y ⊢ ran(f) ⊆ y`
   */
  val functionFromRangeSubsetCodomain = Lemma(
    functionFrom(f, x, y) |- subset(relationRange(f), y)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(functionFrom(f, x, y) |- ∀(z, in(z, f) ==> in(z, cartesianProduct(x, y)))) by Tautology.from(
      functionFrom.definition,
      funSetDef,
      powerAxiom of (x := f, y := cartesianProduct(x, y)),
      subsetAxiom of (x := f, y := cartesianProduct(x, y))
    )
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(pair(a, t), cartesianProduct(x, y))) by InstantiateForall(pair(a, t))
    have((functionFrom(f, x, y), in(pair(a, t), f)) |- in(a, x) /\ in(t, y)) by Cut(lastStep, cartesianProductElimPair of (b := t))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(t, y)) by Weakening
    thenHave((functionFrom(f, x, y), ∃(a, in(pair(a, t), f))) |- in(t, y)) by LeftExists
    have((functionFrom(f, x, y), in(t, relationRange(f))) |- in(t, y)) by Cut(relationRangeElim of (b := t, r := f), lastStep)
    thenHave((functionFrom(f, x, y)) |- in(t, relationRange(f)) ==> in(t, y)) by Restate
    thenHave((functionFrom(f, x, y)) |- ∀(t, in(t, relationRange(f)) ==> in(t, y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(f)))
  }

  val functionApplicationUniqueness = Lemma(
    ∃!(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))
  ) {
    val prem = functional(f) /\ in(x, relationDomain(f))

    // we prove thesis by two cases, first by assuming prem, and then by assuming !prem

    have((relationDomain(f) === relationDomain(f)) <=> ∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r := f)
    )
    thenHave(∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by Restate
    thenHave(in(x, relationDomain(f)) <=> (∃(y, in(pair(x, y), f)))) by InstantiateForall(x)
    val domDef = thenHave(in(x, relationDomain(f)) |- ∃(y, in(pair(x, y), f))) by Weakening

    val uniqPrem = have(functional(f) /\ in(x, relationDomain(f)) |- ∃!(z, in(pair(x, z), f))) by Sorry

    val positive = have(prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ ⊤))) subproof {
        val iff = have(prem |- (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) by Restate
        have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> in(pair(x, y), f))) by Restate
        val subst = thenHave((prem /\ ((z === y) <=> in(pair(x, y), f)), (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by RightSubstIff
          .withParametersSimple(
            List(((in(pair(x, y), f)), (prem ==> in(pair(x, y), f)))),
            lambda(h, ((z === y) <=> h))
          )

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(prem |- (!prem ==> (y === ∅)) <=> ⊤) by Restate
        val topSubst = have(
          (prem /\ ((z === y) <=> in(pair(x, y), f)), ((!prem ==> (y === ∅)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((!prem ==> (y === ∅)), ⊤)), lambda(h, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ h))))(lhs)

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification = have((prem, ∃!(z, in(pair(x, z), f))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
        have((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) by RightForall
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
        thenHave(
          (prem, ∃(z, ∀(y, ((z === y) <=> in(pair(x, y), f))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
        ) by LeftExists
        thenHave(thesis) by Restate
      }

      have(thesis) by Cut(uniqPrem, quantification)
    }

    // negative
    have((∅ === y) <=> (∅ === y)) by Restate
    thenHave(∀(y, (∅ === y) <=> (∅ === y))) by RightForall
    thenHave(∃(z, ∀(y, (z === y) <=> (∅ === y)))) by RightExists
    val emptyPrem = thenHave(∃!(z, (z === ∅))) by Restate

    val negative = have(!prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> ((!prem ==> (y === ∅)) /\ ⊤))) subproof {
        val iff = have(!prem |- ((y === ∅)) <=> (!prem ==> (y === ∅))) by Restate
        have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> (y === ∅))) by Restate
        val subst = thenHave(
          (!prem /\ ((z === y) <=> (y === ∅)), ((y === ∅)) <=> (!prem ==> (y === ∅))) |- ((z === y) <=> (!prem ==> (y === ∅)))
        ) by RightSubstIff.withParametersSimple(List((((y === ∅)), (!prem ==> (y === ∅)))), lambda(h, ((z === y) <=> h)))

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> (!prem ==> (y === ∅)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(!prem |- (prem ==> in(pair(x, y), f)) <=> ⊤) by Restate
        val topSubst = have(
          (!prem /\ ((z === y) <=> (y === ∅)), ((prem ==> in(pair(x, y), f)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((prem ==> in(pair(x, y), f)), ⊤)), lambda(h, ((z === y) <=> ((!prem ==> (y === ∅)) /\ h))))(lhs)

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification =
        have((!prem, ∃!(z, (z === ∅))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
          have((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∀(y, (z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by RightForall
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
          thenHave(
            (!prem, ∃(z, ∀(y, ((z === y) <=> (y === ∅))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
          ) by LeftExists
          thenHave(thesis) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- (prem, ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅)))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) ∈ f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  val functionalApp = Lemma(
    functional(f) |- in(pair(a, b), f) <=> (in(a, relationDomain(f)) /\ (app(f, a) === b))
  ) {
    val appDef = have(
      (app(f, a) === b) <=> (((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (b === ∅)))
    ) by InstantiateForall(b)(app.definition of (x := a))
    have((functional(f), in(a, relationDomain(f)), in(pair(a, b), f)) |- app(f, a) === b) by Weakening(appDef)
    have((functional(f), in(a, relationDomain(f)), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))) by RightAnd(
      lastStep,
      pairInRelation of (r := f, x := a, y := b)
    )
    thenHave(
      (functional(f), in(a, relationDomain(f)) /\ in(b, relationRange(f)), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))
    ) by LeftAnd
    have((functional(f), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))) by Cut(pairInRelation of (r := f, x := a, y := b), lastStep)
    val forward = thenHave(functional(f) |- in(pair(a, b), f) ==> ((app(f, a) === b) /\ in(a, relationDomain(f)))) by Weakening
    val backward = have(functional(f) |- ((app(f, a) === b) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) by Weakening(appDef)
    have(thesis) by RightIff(forward, backward)
  }

  val appIntroFunctional = Lemma(
    (functional(f), in(a, relationDomain(f))) |- in(pair(a, app(f, a)), f)
  ) {
    have(thesis) by Weakening(functionalApp of (b := app(f, a)))
  }

  val pairIsAppFunctional = Lemma(
    (functional(f), in(pair(a, b), f)) |- app(f, a) === b
  ) {
    have(thesis) by Weakening(functionalApp)
  }

  val functionalOverApp = Lemma(
    functionalOver(f, x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))
  ) {
    have((functional(f), relationDomain(f) === x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((relationDomain(f), x)),
      lambda(x, in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b)))
    )(functionalApp)
    have((functionalOver(f, x), relationDomain(f) === x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val appIntroFunctionalOver = Lemma(
    (functionalOver(f, x), in(a, x)) |- in(pair(a, app(f, a)), f)
  ) {
    have((functionalOver(f, x), in(a, relationDomain(f))) |- in(pair(a, app(f, a)), f)) by Cut(functionalOverIsFunctional, appIntroFunctional)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain)
  }

  val pairIsAppFunctionalOver = Lemma(
    (functionalOver(f, x), in(pair(a, b), f)) |- app(f, a) === b
  ) {
    have(thesis) by Cut(functionalOverIsFunctional, pairIsAppFunctional)
  }

  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functional(f) |- b ∈ ran(f) <=> ∃ a ∈ dom(f). f(a) = b`
   */
  val functionalRangeMembership = Lemma(
    functional(f) |- in(b, relationRange(f)) <=> exists(a, in(a, relationDomain(f)) /\ (app(f, a) === b))
  ) {
    have(functional(f) |- forall(a, in(pair(a, b), f) <=> (in(a, relationDomain(f)) /\ (app(f, a) === b)))) by RightForall(functionalApp)
    have(functional(f) |- exists(a, in(pair(a, b), f)) <=> exists(a, in(a, relationDomain(f)) /\ (app(f, a) === b))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, in(pair(a, b), f)), Q := lambda(a, in(a, relationDomain(f)) /\ (app(f, a) === b)))
    )
    thenHave(thesis) by Substitution.ApplyRules(relationRangeMembership of (r := f))
  }


  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functionalOver(f, x) |- b ∈ ran(f) <=> ∃ a ∈ x. f(a) = b`
   */
  val functionalOverRangeMembership = Lemma(
    functionalOver(f, x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))
  ) {
    have((functional(f), relationDomain(f) === x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((relationDomain(f), x)),
      lambda(x, in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b)))
    )(functionalRangeMembership)
    have((functionalOver(f, x), relationDomain(f) === x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val functionalAppInRange = Lemma(
    (functional(f), in(a, relationDomain(f))) |- in(app(f, a), relationRange(f))
  ) {
    have(in(a, relationDomain(f)) |- in(a, relationDomain(f)) /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(in(a, relationDomain(f)) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === app(f, a)))) by RightExists
    have((functional(f), exists(z, in(z, relationDomain(f)) /\ (app(f, z) === app(f, a)))) |- in(app(f, a), relationRange(f))) by Weakening(functionalRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionalOverAppInRange = Lemma(
    (functionalOver(f, x), in(a, x)) |- in(app(f, a), relationRange(f))
  ) {
    have(in(a, x) |- in(a, x) /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(in(a, x) |- exists(z, in(z, x) /\ (app(f, z) === app(f, a)))) by RightExists
    have((functionalOver(f, x), exists(z, in(z, x) /\ (app(f, z) === app(f, a)))) |- in(app(f, a), relationRange(f))) by Weakening(functionalOverRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionFromAppInCodomain = Lemma(
    (functionFrom(f, x, y), in(a, x)) |- in(app(f, a), y)
  ) {
    have((functionFrom(f, x, y), in(a, x)) |- in(app(f, a), relationRange(f))) by Cut(functionFromIsFunctionalOver, functionalOverAppInRange)
    have((functionFrom(f, x, y), in(a, x), subset(relationRange(f), y)) |- in(app(f, a), y)) by Cut(lastStep, subsetElim of (z := app(f, a), x := relationRange(f), y := y))
    have(thesis) by Cut(functionFromRangeSubsetCodomain, lastStep)
  }

  
  /**
   * Surjective (function) --- a function `f: x → y` is surjective iff it
   * maps to every `b ∈ y` from atleast one `a ∈ x`.
   *
   * `surjective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Lemma --- A surjective function is a function.
   *
   *   `surjective(f, x, y) |- functionFrom(f, x, y)`
   */
  val surjectiveIsFunction = Lemma(
    surjective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  /**
   * Lemma --- Surjective function introduction rule.
   *
   *  `functionFrom(f, x, y), ∀ b ∈ y. (∃ a ∈ x. f(a) = b) |- surjective(f, x, y)`
   */
  val surjectiveIntro = Lemma(
    (functionFrom(f, x, y), ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))) |- surjective(f, x, y)
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  /**
   * Lemma --- Surjective function elimination rule.
   *
   *  `surjective(f, x, y), b ∈ y |- ∃ a ∈ x. f(a) = b`
   */
  val surjectiveElim = Lemma(
    (surjective(f, x, y), in(b, y)) |- ∃(a, in(a, x) /\ (app(f, a) === b))
  ) {
    have(surjective(f, x, y) |- ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))) by Weakening(surjective.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Injective (function) --- a function `f: x → y` is injective iff it maps
   * to every `b ∈ y` from atmost one `a ∈ x`.
   *
   * `injective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b) ⟹ (∃! a ∈ x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> (∃(a, in(a, x) /\ in(pair(a, b), f)) ==> ∃!(a, in(a, x) /\ in(pair(a, b), f))))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  val injectiveIsFunction = Lemma(
    injective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Tautology.from(injective.definition)
  }

  /**
   * Bijective function --- a function `f: x → y` is bijective iff it is
   * [[injective]] and [[surjective]].
   */
  val bijective = DEF(f, x, y) --> injective(f, x, y) /\ surjective(f, x, y)

  /**
   * Invertible Function --- a function from `x` to `y` is invertible iff it is
   * [[bijective]]. See also, [[inverseFunction]]
   */
  val invertibleFunction = bijective

  val bijectiveInjective = Lemma(
    bijective(f, x, y) |- injective(f, x, y)
  ) {
    have(thesis) by Weakening(bijective.definition)
  }

  val bijectiveSurjective = Lemma(
    bijective(f, x, y) |- surjective(f, x, y)
  ) {
    have(thesis) by Weakening(bijective.definition)
  }

  val bijectiveIsFunction = Lemma(
    bijective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Cut(bijectiveInjective, injectiveIsFunction)
  }

  val inverseRelationUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> exists(p, in(p, r) /\ (t === pair(secondInPair(p), firstInPair(p))))))
  ) {
    have(thesis) by Restate.from(replacementClassFunction of (A := r, F := lambda(p, pair(secondInPair(p), firstInPair(p)))))
  }

  val inverseRelation = DEF(r) --> The(z, ∀(t, in(t, z) <=> exists(p, in(p, r) /\ (t === pair(secondInPair(p), firstInPair(p))))))(inverseRelationUniqueness)


  val inverseRelationLeftCancel = Lemma((bijective(f, x, y), in(a, x)) |- app(inverseRelation(f), app(f, a)) === a) {
    sorry
  }

  val inverseRelationRightCancel = Lemma((bijective(f, x, y), in(b, y)) |- app(f, app(inverseRelation(f), b)) === b) {
    sorry
  }

  val inverseFunctionImageInDomain = Lemma(
    (bijective(f, x, y), in(b, y)) |- in(app(inverseRelation(f), b), x)
  ) {
    sorry
  }

  /**
   * Relation Restriction
   */

  val relationRestrictionUniqueness = Lemma(existsOne(z, forall(p, in(p, z) <=> (in(p, r) /\ in(p, cartesianProduct(x, y)))))) {
    have(thesis) by UniqueComprehension(r, lambda(p, in(p, r) /\ in(p, cartesianProduct(x, y))))
  }

  val relationRestriction = DEF(r, x, y) --> The(z, forall(p, in(p, z) <=> (in(p, r) /\ in(p, cartesianProduct(x, y)))))(relationRestrictionUniqueness)

 
  val relationRestrictionElem = Lemma(
    in(p, relationRestriction(r, x, y)) <=> (in(p, r) /\ in(p, cartesianProduct(x, y)))
  ) {
    have(forall(p, in(p, relationRestriction(r, x, y)) <=> (in(p, r) /\ in(p, cartesianProduct(x, y))))) by InstantiateForall(relationRestriction(r, x, y))(relationRestriction.definition)
    thenHave(thesis) by InstantiateForall(p)
  }

  val relationRestrictionElemPair = Lemma(
    in(pair(a, b), relationRestriction(r, x, y)) <=> (in(pair(a, b), r) /\ in(a, x) /\ in(b, y))
  ) {
    have(in(pair(a, b), cartesianProduct(x, y)) <=> in(a, x) /\ in(b, y) |- in(pair(a, b), relationRestriction(r, x, y)) <=> (in(pair(a, b), r) /\ in(a, x) /\ in(b, y))) by RightSubstIff
      .withParametersSimple(List((in(pair(a, b), cartesianProduct(x, y)), in(a, x) /\ in(b, y))), lambda(h, in(pair(a, b), relationRestriction(r, x, y)) <=> (in(pair(a, b), r) /\ h)))
       (relationRestrictionElem of (p := pair(a, b)))
    have(thesis) by Cut(cartesianProductMembershipPair, lastStep)
  }

  val relationRestrictionIntro = Lemma(
    (in(pair(a, b), r), in(a, x), in(b, y)) |- in(pair(a, b), relationRestriction(r, x, y))
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionPairInRestrictedDomains = Lemma(
    (in(pair(a, b), relationRestriction(r, x, y))) |- in(a, x) /\ in(b, y)
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionPairInRelation = Lemma(
    (in(pair(a, b), relationRestriction(r, x, y))) |- in(pair(a, b), r)
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionSubset = Lemma(
    subset(relationRestriction(r, x, y), r)
  ) {
    have(forall(p, in(p, relationRestriction(r, x, y)) <=> (in(p, r) /\ in(p, cartesianProduct(x, y))))) by InstantiateForall(relationRestriction(r, x, y))(relationRestriction.definition)
    thenHave(in(p, relationRestriction(r, x, y)) <=> (in(p, r) /\ in(p, cartesianProduct(x, y)))) by InstantiateForall(p)
    thenHave(in(p, relationRestriction(r, x, y)) ==> in(p, r)) by Weakening
    thenHave(forall(p, in(p, relationRestriction(r, x, y)) ==> in(p, r))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRestriction(r, x, y), y := r))
  }

  val relationRestrictionDomain = Lemma(
    subset(relationDomain(relationRestriction(r, x, y)), setIntersection(relationDomain(r), x))
  ) {
    have(in(pair(a, b), relationRestriction(r, x, y)) |- in(a, x)) by Weakening(relationRestrictionPairInRestrictedDomains)
    have((in(pair(a, b), relationRestriction(r, x, y)), in(a, relationDomain(r))) |- in(a, setIntersection(relationDomain(r), x))) by Cut(lastStep, setIntersectionIntro of (t := a, x := relationDomain(r), y := x))
    have((in(pair(a, b), relationRestriction(r, x, y)), in(pair(a, b), r)) |- in(a, setIntersection(relationDomain(r), x))) by Cut(relationDomainIntro, lastStep)
    have(in(pair(a, b), relationRestriction(r, x, y)) |- in(a, setIntersection(relationDomain(r), x))) by Cut(relationRestrictionPairInRelation, lastStep)
    thenHave(exists(b, in(pair(a, b), relationRestriction(r, x, y))) |- in(a, setIntersection(relationDomain(r), x))) by LeftExists
    have(in(a, relationDomain(relationRestriction(r, x, y))) |- in(a, setIntersection(relationDomain(r), x))) by Cut(relationDomainElim of (r := relationRestriction(r, x, y)), lastStep)
    thenHave(in(a, relationDomain(relationRestriction(r, x, y))) ==> in(a, setIntersection(relationDomain(r), x))) by RightImplies
    thenHave(forall(a, in(a, relationDomain(relationRestriction(r, x, y))) ==> in(a, setIntersection(relationDomain(r), x)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationDomain(relationRestriction(r, x, y)), y := setIntersection(relationDomain(r), x)))
  }

  val relationRestrictionRange = Lemma(
    subset(relationRange(relationRestriction(r, x, y)), setIntersection(relationRange(r), y))
  ) {
    have(in(pair(a, b), relationRestriction(r, x, y)) |- in(b, y)) by Weakening(relationRestrictionPairInRestrictedDomains)
    have((in(pair(a, b), relationRestriction(r, x, y)), in(b, relationRange(r))) |- in(b, setIntersection(relationRange(r), y))) by Cut(lastStep, setIntersectionIntro of (t := b, x := relationRange(r)))
    have((in(pair(a, b), relationRestriction(r, x, y)), in(pair(a, b), r)) |- in(b, setIntersection(relationRange(r), y))) by Cut(relationRangeIntro, lastStep)
    have(in(pair(a, b), relationRestriction(r, x, y)) |- in(b, setIntersection(relationRange(r), y))) by Cut(relationRestrictionPairInRelation, lastStep)
    thenHave(exists(a, in(pair(a, b), relationRestriction(r, x, y))) |- in(b, setIntersection(relationRange(r), y))) by LeftExists
    have(in(b, relationRange(relationRestriction(r, x, y))) |- in(b, setIntersection(relationRange(r), y))) by Cut(relationRangeElim of (r := relationRestriction(r, x, y)), lastStep)
    thenHave(in(b, relationRange(relationRestriction(r, x, y))) ==> in(b, setIntersection(relationRange(r), y))) by RightImplies
    thenHave(forall(b, in(b, relationRange(relationRestriction(r, x, y))) ==> in(b, setIntersection(relationRange(r), y)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(relationRestriction(r, x, y)), y := setIntersection(relationRange(r), y)))
  }

  val relationRestrictionOnDomainRange = Lemma(
    relation(r) |- relationRestriction(r, relationDomain(r), relationRange(r)) === r
  ) {
    have((in(pair(firstInPair(p), secondInPair(p)), r), in(secondInPair(p), relationRange(r))) |- 
          in(pair(firstInPair(p), secondInPair(p)), relationRestriction(r, relationDomain(r), relationRange(r)))) by 
          Cut(relationDomainIntro of (a := firstInPair(p), b := secondInPair(p)),
              relationRestrictionIntro of (a := firstInPair(p), b := secondInPair(p), x := relationDomain(r), y := relationRange(r)))
    have(in(pair(firstInPair(p), secondInPair(p)), r) |- in(pair(firstInPair(p), secondInPair(p)), relationRestriction(r, relationDomain(r), relationRange(r)))) by
      Cut(relationRangeIntro of (a := firstInPair(p), b := secondInPair(p)), lastStep)
    thenHave((relation(r), in(p, r)) |- in(p, relationRestriction(r, relationDomain(r), relationRange(r)))) by Substitution.ApplyRules(pairReconstructionInRelation)
    thenHave(relation(r) |- in(p, r) ==> in(p, relationRestriction(r, relationDomain(r), relationRange(r)))) by RightImplies
    thenHave(relation(r) |- forall(p, in(p, r) ==> in(p, relationRestriction(r, relationDomain(r), relationRange(r))))) by RightForall
    have(relation(r) |- subset(r, relationRestriction(r, relationDomain(r), relationRange(r)))) by 
      Cut(lastStep, subsetIntro of (x := r, y := relationRestriction(r, relationDomain(r), relationRange(r))))
    have(relation(r) |- subset(r, relationRestriction(r, relationDomain(r), relationRange(r))) /\ subset(relationRestriction(r, relationDomain(r), relationRange(r)), r)) by 
      RightAnd(lastStep, relationRestrictionSubset of (r := r, x := relationDomain(r), y := relationRange(r)))
    thenHave(thesis) by Substitution.ApplyRules(subsetAntisymmetry of (x := relationRestriction(r, relationDomain(r), relationRange(r)), y := r))
  }

  val relationRestrictionSupersetRange = Lemma(
    (relation(r), subset(relationRange(r), y)) |- relationRestriction(r, x, y) === relationRestriction(r, x, relationRange(r))
  ) {
    sorry
  }

  val relationRestrictionIsRelationBetweenRestrictedDomains = Lemma(
    relationBetween(relationRestriction(r, x, y), x, y)
  ) {
    have(in(p, relationRestriction(r, x, y)) |- in(p, cartesianProduct(x, y))) by Weakening(relationRestrictionElem)
    thenHave(in(p, relationRestriction(r, x, y)) ==> in(p, cartesianProduct(x, y))) by RightImplies
    thenHave(forall(p, in(p, relationRestriction(r, x, y)) ==> in(p, cartesianProduct(x, y)))) by RightForall
    have(subset(relationRestriction(r, x, y), cartesianProduct(x, y))) by Cut(lastStep, subsetIntro of (x := relationRestriction(r, x, y), y := cartesianProduct(x, y)))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := relationRestriction(r, x, y))) 
  }

  val relationRestrictionIsRelationFromRestrictedDomain = Lemma(
    relationFrom(relationRestriction(r, x, y), x)
  ) {
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains, relationBetweenIsRelationFrom of (r := relationRestriction(r, x, y), a := x, b := y))
  }

  val relationRestrictionIsRelation = Lemma(
    relation(relationRestriction(r, x, y))
  ) {
    have(thesis) by Cut(relationRestrictionIsRelationFromRestrictedDomain, relationFromIsRelation of (r := relationRestriction(r, x, y), a := x))
  }

  val relationRestrictionFunctional = Lemma(
    functional(f) |- functional(relationRestriction(f, x, y))
  ) {
    have(thesis) by Cut(relationRestrictionSubset of (r := f), functionalSubset of (f := relationRestriction(f, x, y), g := f))
  }

  val relationRestrictionSetUnion = Lemma(
    relationRestriction(setUnion(r1, r2), x, y) === setUnion(relationRestriction(r1, x, y), relationRestriction(r2, x, y))
  ) {
    have(in(p, relationRestriction(setUnion(r1, r2), x, y)) <=> ((in(p, r1) \/ in(p, r2)) /\ in(p, cartesianProduct(x, y)))) by 
      Substitution.ApplyRules(setUnionMembership of (z := p, x := r1, y := r2))(relationRestrictionElem of (r := setUnion(r1, r2)))
    thenHave(in(p, relationRestriction(setUnion(r1, r2), x, y)) <=> ((in(p, r1) /\ in(p, cartesianProduct(x, y))) \/ (in(p, r2) /\ in(p, cartesianProduct(x, y))))) by Tautology
    thenHave(in(p, relationRestriction(setUnion(r1, r2), x, y)) <=> (in(p, relationRestriction(r1, x, y)) \/ in(p, relationRestriction(r2, x, y)))) by
      Substitution.ApplyRules(relationRestrictionElem of (r := r1), relationRestrictionElem of (r := r2))
    thenHave(in(p, relationRestriction(setUnion(r1, r2), x, y)) <=> in(p, setUnion(relationRestriction(r1, x, y), relationRestriction(r2, x, y)))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := relationRestriction(r1, x, y), y := relationRestriction(r2, x, y)))
    thenHave(forall(p, in(p, relationRestriction(setUnion(r1, r2), x, y)) <=> in(p, setUnion(relationRestriction(r1, x, y), relationRestriction(r2, x, y))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(setUnion(r1, r2), x, y), y := setUnion(relationRestriction(r1, x, y), relationRestriction(r2, x, y))))
  }

  val relationRestrictionSetUnionDomain = Lemma(
    relationRestriction(r, setUnion(x, y), z) === setUnion(relationRestriction(r, x, z), relationRestriction(r, y, z))
  ) {
    have(in(p, relationRestriction(r, setUnion(x, y), z)) <=> (in(p, r) /\ in(p, setUnion(cartesianProduct(x, z), cartesianProduct(y, z))))) by 
      Substitution.ApplyRules(cartesianProductLeftUnion)(relationRestrictionElem of (x := setUnion(x, y), y := z))
    thenHave(in(p, relationRestriction(r, setUnion(x, y), z)) <=> (in(p, r) /\ (in(p, cartesianProduct(x, z)) \/ in(p, cartesianProduct(y, z))))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := cartesianProduct(x, z), y := cartesianProduct(y, z)))
    thenHave(in(p, relationRestriction(r, setUnion(x, y), z)) <=> (in(p, r) /\ in(p, cartesianProduct(x, z))) \/ (in(p, r) /\ in(p, cartesianProduct(y, z)))) by Tautology
    thenHave(in(p, relationRestriction(r, setUnion(x, y), z)) <=> (in(p, relationRestriction(r, x, z)) \/ in(p, relationRestriction(r, y, z)))) by
      Substitution.ApplyRules(relationRestrictionElem of (y := z), relationRestrictionElem of (x := y, y := z))
    thenHave(in(p, relationRestriction(r, setUnion(x, y), z)) <=> in(p, setUnion(relationRestriction(r, x, z), relationRestriction(r, y, z)))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := relationRestriction(r, x, z), y := relationRestriction(r, y, z)))
    thenHave(forall(p, in(p, relationRestriction(r, setUnion(x, y), z)) <=> in(p, setUnion(relationRestriction(r, x, z), relationRestriction(r, y, z))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, setUnion(x, y), z), y := setUnion(relationRestriction(r, x, z), relationRestriction(r, y, z))))
  }

  val domainRestriction = DEF(f, x) --> relationRestriction(f, x, relationRange(f))

  val domainRestrictionIntro = Lemma(
    (in(pair(a, b), f), in(a, x)) |- in(pair(a, b), domainRestriction(f, x))
  ) {
    have((in(pair(a, b), f), in(a, x), in(b, relationRange(f))) |- in(pair(a, b), domainRestriction(f, x))) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionIntro of (r := f, y := relationRange(f)))
    have(thesis) by Cut(relationRangeIntro of (r := f), lastStep)
  }

  val domainRestrictionPairInRelation = Lemma(
    (in(pair(a, b), domainRestriction(f, x))) |- in(pair(a, b), f)
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionPairInRelation of (r := f, y := relationRange(f)))
  }

  val domainRestrictionSubset = Lemma(
    subset(domainRestriction(f, x), f)
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionSubset of (r := f, y := relationRange(f)))
  }

  val domainRestrictionDomain = Lemma(
    relationDomain(domainRestriction(f, x)) === setIntersection(relationDomain(f), x)
  ) {
    val forward = have(subset(relationDomain(domainRestriction(f, x)), setIntersection(relationDomain(f), x))) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionDomain of (r := f, y := relationRange(f)))
    val backward = have(subset(setIntersection(relationDomain(f), x), relationDomain(domainRestriction(f, x)))) subproof {
      have((in(pair(a, b), f), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(domainRestrictionIntro, relationDomainIntro of (r := domainRestriction(f, x)))
      thenHave((exists(b, in(pair(a, b), f)), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by LeftExists
      have((in(a, relationDomain(f)), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(relationDomainElim of (r := f), lastStep)
      thenHave(in(a, relationDomain(f)) /\ in(a, x) |- in(a, relationDomain(domainRestriction(f, x)))) by LeftAnd
      have(in(a, setIntersection(relationDomain(f), x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(setIntersectionElim of (t := a, x := relationDomain(f), y := x), lastStep)
      thenHave(in(a, setIntersection(relationDomain(f), x)) ==> in(a, relationDomain(domainRestriction(f, x)))) by RightImplies
      thenHave(forall(a, in(a, setIntersection(relationDomain(f), x)) ==> in(a, relationDomain(domainRestriction(f, x))))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(relationDomain(f), x), y := relationDomain(domainRestriction(f, x))))
    }
    have(subset(relationDomain(domainRestriction(f, x)), setIntersection(relationDomain(f), x)) /\ subset(setIntersection(relationDomain(f), x), relationDomain(domainRestriction(f, x)))) by RightAnd(forward, backward)
    thenHave(thesis) by Substitution.ApplyRules(subsetAntisymmetry of (x := relationDomain(domainRestriction(f, x)), y := setIntersection(relationDomain(f), x)))
  }

  val domainRestrictionOnDomain = Lemma(
    relation(f) |- domainRestriction(f, relationDomain(f)) ===  f
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionOnDomainRange of (r := f))
  }

  val functionRestrictionOnDomain = Lemma(
    functional(f) |- domainRestriction(f, relationDomain(f)) === f
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionOnDomain)
  }

  val domainRestrictionFunctional = Lemma(
    functional(f) |- functional(domainRestriction(f, x))
  ) {
    have(thesis) by Cut(domainRestrictionSubset, functionalSubset of (f := domainRestriction(f, x), g := f))
  }

  val domainRestrictionSetUnion = Lemma(
    (relation(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))
  ) {
    have(domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(setUnion(f, g))), relationRestriction(g, x, relationRange(setUnion(f, g))))) by 
      Substitution.ApplyRules(domainRestriction.shortDefinition of (f := setUnion(f, g)))(relationRestrictionSetUnion of (r1 := f, r2 := g, y := relationRange(setUnion(f, g))))
    thenHave((relation(f), subset(relationRange(f), relationRange(setUnion(f, g)))) |- 
          domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(setUnion(f, g))))) by 
          Substitution.ApplyRules(relationRestrictionSupersetRange of (r := f, y := relationRange(setUnion(f, g))))
    have((relation(f), subset(f, setUnion(f, g))) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(setUnion(f, g))))) by 
      Cut(relationRangeSubset of (r1 := f, r2 := setUnion(f, g)), lastStep)
    have(relation(f) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(setUnion(f, g))))) by 
      Cut(setUnionLeftSubset of (a := f, b := g), lastStep)
    thenHave((relation(f), relation(g), subset(relationRange(g), relationRange(setUnion(f, g)))) |- 
        domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(g)))) by 
        Substitution.ApplyRules(relationRestrictionSupersetRange of (r := g, y := relationRange(setUnion(f, g))))
    have((relation(f), relation(g), subset(g, setUnion(f, g))) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(g)))) by 
      Cut(relationRangeSubset of (r1 := g, r2 := setUnion(f, g)), lastStep)
    have((relation(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(g)))) by 
      Cut(setUnionRightSubset of (a := f, b := g), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition, domainRestriction.shortDefinition of (x := g))
  }

  val functionRestrictionSetUnion = Lemma(
    (functional(f), functional(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))
  ) {
    have((functional(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))) by Cut(functionalIsRelation, domainRestrictionSetUnion)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  val domainRestrictionSetUnionDomain = Lemma(
    domainRestriction(f, setUnion(x, y)) === setUnion(domainRestriction(f, x), domainRestriction(f, y))
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition, domainRestriction.shortDefinition of (x := y), domainRestriction.shortDefinition of (x := setUnion(x, y)))(relationRestrictionSetUnionDomain of (r := f, z := relationRange(f)))
  }

  val restrictedFunctionApplication = Lemma(
    in(y, x) |- app(f, y) === app(domainRestriction(f, x), y)
  ) {
    sorry
  }

  val restrictedFunctionAbsorption = Lemma(
    domainRestriction(domainRestriction(f, x), y) === domainRestriction(f, setIntersection(x, y))
  ) {
    sorry
  }

  // TODO: any subset of a functional is functional
  // TODO: a functional over something restricted to x is still functional

  /**
   * Sigma Pi Lambda
   */

  /**
   * Dependent Sum (Sigma)
   *
   * TODO: explain
   */
  val Sigma = DEF(x, f) --> union(domainRestriction(f, x))

  val piUniqueness = Lemma(
    ∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    have(∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(z, (subset(x, relationDomain(z)) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))(piUniqueness)

  /**
   * Properties of relations
   */

  /**
   * Reflexive Relation --- `∀ x. x R x`
   */
  val reflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, in(y, x) ==> in(pair(y, y), r))

  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r)))

  /**
   * Transitive Relation --- `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(w, ∀(y, ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))

  /**
   * Lemma --- Transitive relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ w. ∀ y. ∀ z. (w, y) ∈ r ∧ (y, z) ∈ r ⇒ (w, z) ∈ r |- transitive(r, x)`
   */
  val transitiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(w, ∀(y, ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))) |- transitive(r, x)
  ) {
    have(thesis) by Weakening(transitive.definition)
  }

  /**
   * Lemma --- Transitive relation elimination rule
   *
   *   `transitive(r, x), (w, y) ∈ r, (y, z) ∈ r |- (w, z) ∈ r`
   */
  val transitiveElim = Lemma(
    (transitive(r, x), in(pair(w, y), r), in(pair(y, z), r)) |- in(pair(w, z), r)
  ) {
    have(transitive(r, x) |- ∀(w, ∀(y, ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))))) by Weakening(transitive.definition)
    thenHave(transitive(r, x) |- ∀(y, ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r)))) by InstantiateForall(w)
    thenHave(transitive(r, x) |- ∀(z, (in(pair(w, y), r) /\ in(pair(y, z), r)) ==> in(pair(w, z), r))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- A transitive relation is a relation
   *
   *   `transitive(r, x) |- relationBetween(r, x, x)`
   */
  val transitiveRelationIsRelation = Lemma(
    transitive(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(transitive.definition)
  }

  /**
   * Lemma --- The restriction of a transitive relation remains transitive
   *
   *   `transitive(r, x), y ⊆ x |- transitive(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionTransitive = Lemma(
    transitive(r, x) |- transitive(relationRestriction(r, y, y), y)
  ) {
    have((transitive(r, x), in(pair(a, b), r), in(pair(b, c), r), in(a, y), in(c, y)) |- in(pair(a, c), relationRestriction(r, y, y))) by
      Cut(transitiveElim of (w := a, y := b, z := c), relationRestrictionIntro of (b := c, x := y))
    have((transitive(r, x), in(pair(a, b), relationRestriction(r, y, y)), in(pair(b, c), r), in(a, y), in(c, y)) |- in(pair(a, c), relationRestriction(r, y, y))) by
      Cut(relationRestrictionPairInRelation of (x := y), lastStep)
    have((transitive(r, x), in(pair(a, b), relationRestriction(r, y, y)), in(pair(b, c), relationRestriction(r, y, y)), in(a, y), in(c, y)) |- in(pair(a, c), relationRestriction(r, y, y))) by
      Cut(relationRestrictionPairInRelation of (x := y, a := b, b := c), lastStep)
    thenHave(
      (transitive(r, x), in(pair(a, b), relationRestriction(r, y, y)), in(pair(b, c), relationRestriction(r, y, y)), in(a, y) /\ in(b, y), in(b, y) /\ in(c, y)) |- in(
        pair(a, c),
        relationRestriction(r, y, y)
      )
    ) by Weakening
    have((transitive(r, x), in(pair(a, b), relationRestriction(r, y, y)), in(pair(b, c), relationRestriction(r, y, y)), in(b, y) /\ in(c, y)) |- in(pair(a, c), relationRestriction(r, y, y))) by
      Cut(relationRestrictionPairInRestrictedDomains of (x := y), lastStep)
    have((transitive(r, x), in(pair(a, b), relationRestriction(r, y, y)), in(pair(b, c), relationRestriction(r, y, y))) |- in(pair(a, c), relationRestriction(r, y, y))) by
      Cut(relationRestrictionPairInRestrictedDomains of (x := y, a := b, b := c), lastStep)
    thenHave(transitive(r, x) |- (in(pair(a, b), relationRestriction(r, y, y)) /\ in(pair(b, c), relationRestriction(r, y, y))) ==> in(pair(a, c), relationRestriction(r, y, y))) by Restate
    thenHave(
      transitive(r, x) |- forall(c, in(pair(a, b), relationRestriction(r, y, y)) /\ in(pair(b, c), relationRestriction(r, y, y)) ==> in(pair(a, c), relationRestriction(r, y, y)))
    ) by RightForall
    thenHave(
      transitive(r, x) |- forall(b, forall(c, in(pair(a, b), relationRestriction(r, y, y)) /\ in(pair(b, c), relationRestriction(r, y, y)) ==> in(pair(a, c), relationRestriction(r, y, y))))
    ) by RightForall
    thenHave(
      transitive(r, x) |- forall(a, forall(b, forall(c, in(pair(a, b), relationRestriction(r, y, y)) /\ in(pair(b, c), relationRestriction(r, y, y)) ==> in(pair(a, c), relationRestriction(r, y, y)))))
    ) by RightForall
    have((transitive(r, x), relationBetween(relationRestriction(r, y, y), y, y)) |- transitive(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      transitiveIntro of (x := y, r := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Equivalence Relation --- A relation is an equivalence relation if it is
   * [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

  /**
   * Anti-reflexive Relation --- `∀ x. ! x R x`
   */
  val antiReflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, in(y, x) ==> !in(pair(y, y), r))

  /**
   * Irreflexive Relation --- Alias for [[antiReflexive]].
   */
  val irreflexive = antiReflexive

  /**
   * Lemma --- Anti-reflexive relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ y. in(y, x) ==> !in(pair(y, y), r) |- antiReflexive(r, x)`
   */
  val antiReflexiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, in(y, x) ==> !in(pair(y, y), r))) |- antiReflexive(r, x)
  ) {
    have(thesis) by Weakening(antiReflexive.definition)
  }

  /**
   * Lemma --- Anti-reflexive relation elimination rule
   *
   *   `antiReflexive(r, x), y ∈ x |- (y, y) ∉ r`
   */
  val antiReflexiveElim = Lemma(
    (antiReflexive(r, x), in(y, x)) |- !in(pair(y, y), r)
  ) {
    have(antiReflexive(r, x) |- ∀(y, in(y, x) ==> !in(pair(y, y), r))) by Weakening(antiReflexive.definition)
    thenHave(thesis) by InstantiateForall(y)
  }

  /**
   * Lemma --- An anti-reflexive relation is a relation
   *
   *   `antiReflexive(r, x) |- relationBetween(r, x, x)`
   */
  val antiReflexiveRelationIsRelation = Lemma(
    antiReflexive(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(antiReflexive.definition)
  }

  val pairInAntiReflexiveRelation = Lemma(
    (antiReflexive(r, x), in(pair(a, b), r)) |- !(a === b)
  ) {
    have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
    thenHave((a === b, in(pair(a, b), r)) |- in(pair(a, a), r)) by RightSubstEq.withParametersSimple(
      List((a, b)),
      lambda(b, in(pair(a, b), r))
    )
    have((antiReflexive(r, x), in(a, x), in(pair(a, b), r), a === b) |- in(pair(a, a), r) /\ !in(pair(a, a), r)) by RightAnd(lastStep, antiReflexiveElim of (y := a))
    thenHave((antiReflexive(r, x), in(a, x) /\ in(b, x), in(pair(a, b), r), a === b) |- ()) by Weakening
    have((antiReflexive(r, x), relationBetween(r, x, x), in(pair(a, b), r), a === b) |- ()) by Cut(relationBetweenElimPair of (a := x, b := x, x := a, y := b), lastStep)
    have((antiReflexive(r, x), in(pair(a, b), r), a === b) |- ()) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }

  /**
   * Lemma --- A subset of an irreflexive relation is also irreflexive
   *
   *   `irreflexive(r, x), t ⊆ r, y ⊆ x |- irreflexive(t, y)`
   */
  val relationSubsetIrreflexive = Lemma(
    (irreflexive(r, x), subset(t, r), subset(y, x), relationBetween(t, y, y)) |- irreflexive(t, y)
  ) {
    have((!in(pair(a, a), r), subset(t, r)) |- !in(pair(a, a), t)) by Restate.from(subsetElim of (z := pair(a, a), x := t, y := r))
    have((irreflexive(r, x), in(a, x), subset(t, r)) |- !in(pair(a, a), t)) by Cut(antiReflexiveElim of (y := a), lastStep)
    have((irreflexive(r, x), in(a, y), subset(t, r), subset(y, x)) |- !in(pair(a, a), t)) by Cut(subsetElim of (z := a, y := x, x := y), lastStep)
    thenHave((irreflexive(r, x), subset(t, r), subset(y, x)) |- in(a, y) ==> !in(pair(a, a), t)) by RightImplies
    thenHave((irreflexive(r, x), subset(t, r), subset(y, x)) |- forall(a, in(a, y) ==> !in(pair(a, a), t))) by RightForall
    have(thesis) by Cut(lastStep, antiReflexiveIntro of (x := y, r := t))
  }

  /**
   * Lemma --- The restriction of an irreflexive relation remains irreflexive
   *
   *   `irreflexive(r, x), y ⊆ x |- irreflexive(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionIrreflexive = Lemma(
    (irreflexive(r, x), subset(y, x)) |- irreflexive(relationRestriction(r, y, y), y)
  ) {
    have((irreflexive(r, x), subset(y, x), relationBetween(relationRestriction(r, y, y), y, y)) |- irreflexive(relationRestriction(r, y, y), y)) by Cut(
      relationRestrictionSubset of (x := y),
      relationSubsetIrreflexive of (t := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

  /**
   * Connected Relation --- `∀ x y. (x R y) ∨ (y R x) ∨ (y = x)`
   */
  val connected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Lemma --- Connected relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ y. ∀ z. in(y, x) /\ in(z, x) ==> (in(pair(y, z), r) ∨ in(pair(z, y), r) ∨ (y = z)) |- connected(r, x)`
   */
  val connectedIntro = Lemma((relationBetween(r, x, x), ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))) |- connected(r, x)) {
    have(thesis) by Weakening(connected.definition)
  }

  /**
   * Lemma --- Connected relation elimination rule
   *
   *   `connected(r, x), y ∈ x, z ∈ x |- (y, z) ∈ r ∨ (z, y) ∈ r ∨ y = z`
   */
  val connectedElim = Lemma((connected(r, x), in(y, x), in(z, x)) |- in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z)) {
    have(connected(r, x) |- ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z))))) by Weakening(connected.definition)
    thenHave(connected(r, x) |- ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r) \/ (y === z)))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- A connected relation is a relation
   *
   *   `connected(r, x) |- relationBetween(r, x, x)`
   */
  val connectedRelationIsRelation = Lemma(connected(r, x) |- relationBetween(r, x, x)) {
    have(thesis) by Weakening(connected.definition)
  }

  /**
   * Lemma --- The restriction of a connected relation remains connected
   *
   *   `connected(r, x), y ⊆ x |- connected(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionConnected = Lemma(
    (connected(r, x), subset(y, x)) |- connected(relationRestriction(r, y, y), y)
  ) {
    val left = have((in(pair(a, b), r), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Weakening(
      relationRestrictionIntro of (x := y)
    )
    val right = have((in(pair(b, a), r), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Weakening(
      relationRestrictionIntro of (x := y, a := b, b := a)
    )
    have(a === b |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Restate
    have((in(pair(b, a), r) \/ (a === b), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by LeftOr(lastStep, right)
    have(
      (in(pair(a, b), r) \/ in(pair(b, a), r) \/ (a === b), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)
    ) by LeftOr(lastStep, left)
    have((connected(r, x), in(a, x), in(b, x), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      connectedElim of (y := a, z := b),
      lastStep
    )
    have((connected(r, x), subset(y, x), in(b, x), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      subsetElim of (z := a, y := x, x := y),
      lastStep
    )
    have((connected(r, x), subset(y, x), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      subsetElim of (z := b, y := x, x := y),
      lastStep
    )
    thenHave((connected(r, x), subset(y, x)) |- (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b))) by Restate
    thenHave(
      (connected(r, x), subset(y, x)) |- forall(b, (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)))
    ) by RightForall
    thenHave(
      (connected(r, x), subset(y, x)) |- forall(a, forall(b, (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b))))
    ) by RightForall
    have((connected(r, x), relationBetween(relationRestriction(r, y, y), y, y), subset(y, x)) |- connected(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      connectedIntro of (x := y, r := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Strongly Connected Relation ---
   *     `∀ x y z. y R x ∧ z R x ⇒ y R z ∨ z R y`
   */
  val stronglyConnected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(y, x) /\ in(z, x)) ==> (in(pair(y, z), r) \/ in(pair(z, y), r))))



  /**
   * Lemma --- empty relation on the empty set is reflexive.
   */
  val emptyRelationReflexiveOnItself = Lemma(
    () |- reflexive(emptySet, emptySet)
  ) {
    have(() |- in(y, emptySet) ==> in(pair(y, y), emptySet)) by Tautology.from(emptySetAxiom of (x := y))
    val refCond = thenHave(() |- forall(y, in(y, emptySet) ==> in(pair(y, y), emptySet))) by RightForall

    have(thesis) by Tautology.from(reflexive.definition of (r := emptySet, x := emptySet), emptySetRelationOnItself, refCond)
  }

  /**
   * Lemma --- the empty relation is symmetric.
   */
  val emptyRelationSymmetric = Lemma(
    () |- symmetric(emptySet, a)
  ) {
    have(() |- in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)) by Tautology.from(emptySetAxiom of (x := pair(y, z)), emptySetAxiom of (x := pair(z, y)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet))) by RightForall
    val symCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)))) by RightForall

    have(thesis) by Tautology.from(symmetric.definition of (r := emptySet, x := a), emptySetRelation of (b := a), symCond)
  }

  /**
   * Lemma --- the empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Lemma(
    () |- irreflexive(emptySet, a)
  ) {
    have(() |- in(y, a) ==> !in(pair(y, y), emptySet)) by Tautology.from(emptySetAxiom of (x := pair(y, y)))
    val irrefCond = thenHave(() |- forall(y, in(y, a) ==> !in(pair(y, y), emptySet))) by RightForall

    have(thesis) by Tautology.from(irreflexive.definition of (r := emptySet, x := a), emptySetRelation of (b := a), irrefCond)
  }

  /**
   * Lemma --- the empty relation is transitive.
   */
  val emptyRelationTransitive = Lemma(
    () |- transitive(emptySet, a)
  ) {
    have(() |- (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)) by Tautology.from(emptySetAxiom of (x := pair(w, y)))
    thenHave(() |- forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))) by RightForall
    thenHave(() |- forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)))) by RightForall
    val trsCond = thenHave(() |- forall(w, forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))))) by RightForall

    have(thesis) by Tautology.from(transitive.definition of (r := emptySet, x := a), emptySetRelation of (b := a), trsCond)
  }

  /**
   * Lemma --- the empty relation is an equivalence relation on the empty set.
   */
  val emptyRelationEquivalence = Lemma(
    () |- equivalence(emptySet, emptySet)
  ) {
    have(thesis) by Tautology.from(
      equivalence.definition of (r := emptySet, x := emptySet),
      emptyRelationReflexiveOnItself,
      emptyRelationSymmetric of (a := emptySet),
      emptyRelationTransitive of (a := emptySet)
    )
  }

  /**
   * Lemma --- the empty relation is anti-symmetric.
   */
  val emptyRelationAntiSymmetric = Lemma(
    () |- antiSymmetric(emptySet, a)
  ) {
    have(() |- (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)) by Tautology.from(emptySetAxiom of (x := pair(y, z)))
    thenHave(() |- forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z))) by RightForall
    val ansymCond = thenHave(() |- forall(y, forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)))) by RightForall

    have(thesis) by Tautology.from(antiSymmetric.definition of (r := emptySet, x := a), emptySetRelation of (b := a), ansymCond)
  }

  /**
   * Lemma --- the empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Lemma(
    () |- asymmetric(emptySet, a)
  ) {
    have(() |- in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)) by Tautology.from(emptySetAxiom of (x := pair(y, z)))
    thenHave(() |- forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet))) by RightForall
    val asymCond = thenHave(() |- forall(y, forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)))) by RightForall

    have(thesis) by Tautology.from(asymmetric.definition of (r := emptySet, x := a), emptySetRelation of (b := a), asymCond)
  }

  /**
   * Lemma --- the empty relation is total on the empty set.
   */
  val emptyRelationTotalOnItself = Lemma(
    () |- total(emptySet, emptySet)
  ) {
    have((in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))) by Tautology.from(emptySetAxiom of (x := y))
    thenHave(forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z)))) by RightForall
    thenHave(forall(y, forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))))) by RightForall

    have(thesis) by Tautology.from(lastStep, total.definition of (r := emptySet, x := emptySet), emptySetRelationOnItself)
  }

  /**
   * Cantor theorem
   */

  // smaller needed lemmas
  // f from x to y => range f <= y
  // f from x to y => dom f = x
  // x <= y, y <= x |- x = y

  /**
   * Lemma --- The range of a surjective function is equal to its codomain.
   *
   *   `surjective(f, x, y) |- y = ran(f)`
   */
  val surjectiveImpliesRangeIsCodomain = Lemma(
    surjective(f, x, y) |- y === relationRange(f)
  ) {
    have((surjective(f, x, y), functionalOver(f, x), in(b, y)) |- in(b, relationRange(f))) by Substitution.ApplyRules(functionalOverRangeMembership)(surjectiveElim)
    have((surjective(f, x, y), functionFrom(f, x, y), in(b, y)) |- in(b, relationRange(f))) by Cut(functionFromIsFunctionalOver, lastStep)
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- in(b, y) ==> in(b, relationRange(f))) by RightImplies
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- ∀(b, in(b, y) ==> in(b, relationRange(f)))) by RightForall
    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f))) by Cut(lastStep, subsetIntro of (x := y, y := relationRange(f)))
    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f)) /\ subset(relationRange(f), y)) by RightAnd(lastStep, functionFromRangeSubsetCodomain)
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- y === relationRange(f)) by Substitution.ApplyRules(subsetAntisymmetry of (x := y, y := relationRange(f)))
    have(thesis) by Cut(surjectiveIsFunction, lastStep)
  }

  /**
   * Lemma --- Cantor's Lemma
   *
   * There is no [[surjective]] mapping ([[functionFrom]]) a set to its [[powerSet]].
   *
   * In terms of cardinality, it asserts that a set is strictly smaller than
   * its power set.
   */
  val cantorTheorem = Lemma(
    surjective(f, x, powerSet(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = ∀(t, in(t, y) <=> (in(t, x) /\ !in(t, app(f, t))))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(t, y) <=> (in(t, x) /\ !in(t, app(f, t)))) by InstantiateForall(t)
    thenHave(ydef |- in(t, y) ==> in(t, x)) by Weakening
    thenHave(ydef |- ∀(t, in(t, y) ==> in(t, x))) by RightForall
    andThen(Substitution.applySubst(subsetAxiom of (x := y, y := x)))
    andThen(Substitution.applySubst(powerAxiom of (x := y, y := x)))
    thenHave(ydef |- in(y, powerSet(x))) by Restate
    val existsZ = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by Cut(lastStep, surjectiveElim of (y := powerSet(x), b := y))

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by InstantiateForall(z)
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by Weakening
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, app(f, z)) <=> (in(z, x) /\ !in(z, app(f, z)))) by RightSubstEq.withParametersSimple(
      List((y, app(f, z))),
      lambda(y, in(z, y) <=> (in(z, x) /\ !in(z, app(f, z))))
    )
    thenHave((ydef, in(z, x) /\ (app(f, z) === y)) |- ()) by Tautology
    thenHave((ydef, ∃(z, in(z, x) /\ (app(f, z) === y))) |- ()) by LeftExists
    have((ydef, surjective(f, x, powerSet(x))) |- ()) by Cut(existsZ, lastStep)
    val yToContra = thenHave((∃(y, ydef), surjective(f, x, powerSet(x))) |- ()) by LeftExists
    val yexists = have(∃(y, ydef)) by Restate.from(comprehensionSchema of (z := x, φ := lambda(t, !in(t, app(f, t)))))

    have(thesis) by Cut(yexists, yToContra)
  }

  /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalSetUnion = Lemma(
    (functional(f), functional(g), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))
  ) {
    val commonDomains = forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))
    have(commonDomains |- commonDomains) by Hypothesis
    thenHave((commonDomains, in(x, relationDomain(f)), in(x, relationDomain(g))) |- app(f, x) === app(g, x)) by InstantiateForall(x)
    have((commonDomains, in(pair(x, y), f),  in(x, relationDomain(g))) |- app(f, x) === app(g, x)) by Cut(relationDomainIntro of (a := x, b := y, r := f), lastStep)
    have((commonDomains, in(pair(x, y), f),  in(pair(x, z), g)) |- app(f, x) === app(g, x)) by Cut(relationDomainIntro of (a := x, b := z, r := g), lastStep)
    thenHave((commonDomains, functional(f), in(pair(x, y), f),  in(pair(x, z), g)) |- y === app(g, x)) by Substitution.ApplyRules(pairIsAppFunctional)
    thenHave((commonDomains, functional(f), functional(g), in(pair(x, y), f),  in(pair(x, z), g)) |- y === z) by Substitution.ApplyRules(pairIsAppFunctional)
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), g)) |- (in(pair(x, y), g), y === z)) by Cut(setUnionElim of (x := f, y := g, z := pair(x, y)), lastStep)
    val right = have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), g)) |- y === z) by Cut(lastStep, functionalElim of (f := g))
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), f)) |- y === z) by Substitution.ApplyRules(setUnionCommutativity)(lastStep of (f := g, g := f))
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)), in(pair(x, z), setUnion(f, g))) |- (in(pair(x, z), g), y === z)) by Cut(setUnionElim of (x := f, y := g, z := pair(x, z)), lastStep)
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)), in(pair(x, z), setUnion(f, g))) |- y === z) by Cut(lastStep, right)
    thenHave((commonDomains, functional(f), functional(g)) |- (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g)) ==> (y === z))) by Restate
    thenHave((commonDomains, functional(f), functional(g)) |- forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- forall(y, forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z)))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- forall(x, forall(y, forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z))))) by RightForall
    have((commonDomains, functional(f), functional(g), relation(setUnion(f, g))) |- functional(setUnion(f, g))) by Cut(lastStep, functionalIntro of (f := setUnion(f, g)))
    have((commonDomains, functional(f), functional(g), relation(f), relation(g)) |- functional(setUnion(f, g))) by Cut(relationSetUnion of (r1 := f, r2 := g), lastStep)
    have((commonDomains, functional(f), functional(g), relation(g)) |- functional(setUnion(f, g))) by Cut(functionalIsRelation, lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

    /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalOverSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, b))
  ) {
    have((functionalOver(f, a), functional(g), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))) by Cut(functionalOverIsFunctional of (x := a), functionalSetUnion)
    have((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))) by Cut(functionalOverIsFunctional of (f := g, x := b), lastStep)
    have((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), relationDomain(setUnion(f, g)))) by Cut(lastStep, functionalOverIntro of (f := setUnion(f, g), x := setUnion(a, b)))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(relationDomain(f), relationDomain(g)))) by Substitution.ApplyRules(relationDomainSetUnion of (r1 := f, r2 := g))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, relationDomain(g)))) by Substitution.ApplyRules(functionalOverDomain of (x := a))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, b))) by Substitution.ApplyRules(functionalOverDomain of (f :=g, x := b))
  }

  val functionalOverDisjointSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), setIntersection(a, b) === emptySet) |- functionalOver(setUnion(f, g), setUnion(a, b))
  ) {
    have((setIntersection(a, b) === emptySet, in(x, setIntersection(a, b))) |- ()) by Restate.from(setEmptyHasNoElements of (y := x, x := setIntersection(a, b)))
    have((setIntersection(a, b) === emptySet, in(x, a), in(x, b)) |- ()) by Cut(setIntersectionIntro of (t := x, x := a, y := b), lastStep)
    thenHave((setIntersection(a, b) === emptySet, in(x, a), in(x, b)) |- app(f, x) === app(g, x)) by Weakening
    thenHave(setIntersection(a, b) === emptySet |- (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x))) by Restate
    thenHave(setIntersection(a, b) === emptySet |- forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) by RightForall
    have(thesis) by Cut(lastStep, functionalOverSetUnion)
  }



  /**
   * Lemma --- Union of a Set of Functions is a Function
   *
   * Given a set `z` of functions (weakly or [[reflexive]]ly) totally ordered by
   * the [[subset]] relation on the elements' domains ([[relationDomain]]), `∪
   * z` is [[functional]] (in particular, with domain as the union of the
   * elements' domains).
   */
  val unionOfFunctionSet = Lemma(
    (forall(t, in(t, z) ==> functional(t)), forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))))|- functional(union(z))
  ) {
    // add assumptions
    assume(forall(t, in(t, z) ==> functional(t)), forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))))

    // assume, towards a contradiction
    assume(!functional(union(z)))

    val u = union(z)

    // begin proof ----------------

    // u is a relation

    have(in(t, z) ==> functional(t)) by InstantiateForall
    have(in(t, z) ==> relation(t)) by Tautology.from(lastStep, functional.definition of (f := t))
    thenHave(forall(t, in(t, z) ==> relation(t))) by RightForall
    val relU = have(relation(u)) by Tautology.from(lastStep, unionOfRelationSet)

    // if u is not functional, there exists a violating pair in it
    val notFun = have(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)))) by Sorry

    have((exists(f, in(f, z) /\ in(pair(x, y), f)), exists(g, in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) subproof {
      have(forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x))))) by Restate
      val subfg = thenHave((in(f, z) /\ in(g, z)) ==> (subset(f, g) \/ subset(g, f))) by InstantiateForall(f, g)

      have(forall(t, in(t, z) ==> functional(t))) by Restate
      val funF = thenHave(in(f, z) ==> functional(f)) by InstantiateForall(f)

      val fg = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(f, g)) |- ()) by Tautology.from(subsetElim of (z := pair(x, y), x := f, y := g), funF of (f := g), functionalElim of (f := g, z := w))
      val gf = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(g, f)) |- ()) by Tautology.from(subsetElim of (z := pair(x, w), x := g, y := f), funF, functionalElim of (f := f, z := w))

      have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w)) |- ()) by Tautology.from(subfg, fg, gf)
      thenHave((exists(f, in(f, z) /\ in(pair(x, y), f)), (in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) by LeftExists
      thenHave(thesis) by LeftExists
    }
    have((in(pair(x, y), u), exists(g, in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) by Cut(unionElim of (x := z, z := pair(x, y)), lastStep)
    have((in(pair(x, y), u), in(pair(x, w), u), !(y === w)) |- ()) by Cut(unionElim of (x := z, z := pair(x, w)), lastStep)
    thenHave(in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w) |- ()) by Restate
    thenHave(exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w)) |- ()) by LeftExists
    thenHave(exists(y, exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w))) |- ()) by LeftExists

    have(exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)) |- ()) by Tautology.from(lastStep, atleastTwoExist of (P := lambda(y, in(pair(x, y), u))))
    thenHave(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u))) |- ()) by LeftExists

    // contradiction
    have(thesis) by Tautology.from(lastStep, notFun)
  }

  /**
   * Lemma --- Domain of Relational Union
   *
   * If the unary union of a set is relational, then its domain is defined
   * precisely by the union of the domains of its elements.
   *
   *    relation(\cup z) |- \forall t. t \in dom(U z) <=> \exists y \in z. t \in
   *    dom(y)
   *
   * This holds, particularly, as the elements of z must be relations
   * themselves, which follows from the assumption.
   */
  val domainOfRelationalUnion = Lemma(
    forall(t, in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y))))
  ) {
    val uz = union(z)

    have(forall(t, in(t, relationDomain(uz)) <=> exists(a, in(pair(t, a), uz)))) by InstantiateForall(relationDomain(uz))(relationDomain.definition of (r := uz))
    val inDom = thenHave(in(t, relationDomain(uz)) <=> exists(a, in(pair(t, a), uz))) by InstantiateForall(t)

    have(exists(a, in(pair(t, a), uz)) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
      // we prove the directions separately
      val fwd = have(exists(a, in(pair(t, a), uz)) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
        have(in(pair(t, a), uz) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
          assume(in(pair(t, a), uz))
          // since \cup z is a union
          // \exists y such that (t, a) \in y
          // and so t \in dom y
          val exy = have(exists(y, in(pair(t, a), y) /\ in(y, z))) by Tautology.from(unionAxiom of (z := pair(t, a), x := z))

          have(exists(y, in(pair(t, a), y) /\ in(y, z)) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) subproof {
            have(forall(z, (z === relationDomain(y)) <=> forall(t, in(t, z) <=> exists(a, in(pair(t, a), y))))) by Weakening(relationDomain.definition of (r := y))
            thenHave(forall(t, in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y)))) by InstantiateForall(relationDomain(y))
            val inDomY = thenHave(in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y))) by InstantiateForall(t)
            have(in(pair(t, a), y) |- in(pair(t, a), y)) by Hypothesis
            thenHave(in(pair(t, a), y) |- exists(a, in(pair(t, a), y))) by RightExists
            have(in(pair(t, a), y) /\ in(y, z) |- in(t, relationDomain(y)) /\ in(y, z)) by Tautology.from(lastStep, inDomY)
            thenHave(in(pair(t, a), y) /\ in(y, z) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) by RightExists
            thenHave(thesis) by LeftExists
          }

          have(thesis) by Cut(exy, lastStep)
        }

        thenHave(thesis) by LeftExists
      }
      val bwd = have(exists(y, in(y, z) /\ in(t, relationDomain(y))) |- exists(a, in(pair(t, a), uz))) subproof {
        have(forall(z, (z === relationDomain(y)) <=> forall(t, in(t, z) <=> exists(a, in(pair(t, a), y))))) by Weakening(relationDomain.definition of (r := y))
        thenHave(forall(t, in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y)))) by InstantiateForall(relationDomain(y))
        thenHave(in(t, relationDomain(y)) <=> exists(a, in(pair(t, a), y))) by InstantiateForall(t)
        val exA = thenHave(in(t, relationDomain(y)) |- exists(a, in(pair(t, a), y))) by Tautology

        have((in(pair(t, a), y), in(y, z)) |- exists(a, in(pair(t, a), uz))) by RightExists(unionIntro of (z := pair(t, a), x := z))
        thenHave((exists(a, in(pair(t, a), y)), in(y, z)) |- exists(a, in(pair(t, a), uz))) by LeftExists
        have((in(y, z), in(t, relationDomain(y))) |- exists(a, in(pair(t, a), uz))) by Cut(exA, lastStep)
        thenHave((in(y, z) /\ in(t, relationDomain(y))) |- exists(a, in(pair(t, a), uz))) by LeftAnd
        thenHave(thesis) by LeftExists
      }

      have(thesis) by Tautology.from(fwd, bwd)
    }

    have(in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))) by Tautology.from(inDom, lastStep)
    thenHave(thesis) by RightForall
  }

  /**
   * Lemma --- Domain of Functional Union
   *
   * If the unary union of a set is functional, then its domain is defined
   * precisely by the union of the domains of its elements.
   *
   *    functional(\cup z) |- \forall t. t \in dom(U z) <=> \exists y \in z. t
   *    \in dom(y)
   *
   * This holds, particularly, as the elements of z must be functions
   * themselves, which follows from the assumption.
   */
  val domainOfFunctionalUnion = Lemma(
    functional(union(z)) |- forall(t, in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y))))
  ) {
    assume(functional(union(z)))
    have(relation(union(z))) by Tautology.from(functional.definition of (f := union(z)))
    have(thesis) by Tautology.from(lastStep, domainOfRelationalUnion)
  }

}
