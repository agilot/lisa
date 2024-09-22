package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import SetTheory.*

object Relations extends lisa.Main {

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
   * Binary Relation --- A binary relation `r` from `a` to `b` is a subset of
   * the [[cartesianProduct]] of `a` and `b`, `a * b`. We say `x r y`, `r(x,
   * y)`, or `r relates x to y` for `(x, y) ∈ r`.
   */
  val relationBetween = DEF(r, a, b) --> r ⊆ (a × b)

  val pairReconstructionInRelationBetween = Lemma(
    (relationBetween(r, a, b), p ∈ r) |- p === pair(fst(p), snd(p))
  ) {
    have(relationBetween(r, a, b) |- r ⊆ (a × b)) by Weakening(relationBetween.definition)
    have((relationBetween(r, a, b), p ∈ r) |- p ∈ (a × b)) by Cut(lastStep, subsetElim of (z := p, x := r, y := a × b))
    have(thesis) by Cut(lastStep, pairReconstructionInCartesianProduct of (t := p, x := a, y := b))
  }

  /**
   * Lemma --- Pair in Relation
   *
   * If a pair `(x, y)` ∃ in a relation `r` from `a` to `b`,
   * then `x` and `y` are elements of `a` and `b` respectively.
   */
  val relationBetweenElimPair = Lemma(
    (relationBetween(r, a, b), pair(x, y) ∈ r) |- x ∈ a /\ y ∈ b
  ) {
    have((relationBetween(r, a, b), pair(x, y) ∈ r) |- pair(x, y) ∈ (a × b)) by Substitution.ApplyRules(relationBetween.definition)(
      subsetElim of (z := pair(x, y), x := r, y := a × b)
    )
    have(thesis) by Cut(lastStep, cartesianProductElimPair of (x := a, y := b, a := x, b := y))
  }

  val relationBetweenElim = Lemma(
    (relationBetween(r, a, b), p ∈ r) |- fst(p) ∈ a /\ snd(p) ∈ b
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelationBetween)(relationBetweenElimPair of (x := fst(p), y := snd(p)))
  }

  val relationBetweenIntro = Lemma(
    r ⊆ (a × b) |- relationBetween(r, a, b)
  ) {
    have(thesis) by Weakening(relationBetween.definition)
  }

  val relationBetweenSubset = Lemma(
    (r1 ⊆ r2, relationBetween(r2, a, b)) |- relationBetween(r1, a, b)
  ) {
    have((r1 ⊆ r2, relationBetween(r2, a, b)) |- r1 ⊆ (a × b)) by
      Substitution.ApplyRules(relationBetween.definition)(subsetTransitivity of (x := r1, y := r2, z := a × b))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }

  /**
   * Lemma --- the empty set is a relation, the empty relation, between any two sets.
   */
  val emptySetRelation = Lemma(
    relationBetween(∅, a, b)
  ) {
    have(thesis) by Cut(emptySetSubset of (x := a × b), relationBetweenIntro of (r := ∅))
  }

  val relationBetweenLeftEmptyIsEmpty = Lemma(
    relationBetween(r, ∅, b) |- r === ∅
  ) {
    have(r ⊆ ∅ |- r === ∅) by Weakening(subsetEmptySet of (x := r))
    thenHave(r ⊆ (∅ × b) |- r === ∅) by Substitution.ApplyRules(cartesianProductLeftEmpty of (y := b))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }

  val relationBetweenRightEmptyIsEmpty = Lemma(
    relationBetween(r, a, ∅) |- r === ∅
  ) {
    have(r ⊆ ∅ |- r === ∅) by Weakening(subsetEmptySet of (x := r))
    thenHave(r ⊆ (a × ∅) |- r === ∅) by Substitution.ApplyRules(cartesianProductRightEmpty of (x := a))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }

  /**
   * Lemma --- the empty relation is a relation on the empty set.
   */
  val emptySetRelationOnItself = Lemma(
    relationBetween(∅, ∅, ∅)
  ) {
    have(thesis) by Restate.from(emptySetRelation of (a := ∅, b := ∅))
  }

  /**
   * Lemma --- The union of two relations is a relation
   *
   *    `r1 ⊆ a × b, r2 ⊆ c × d ⊢ r1 ∪ r2 ⊆ (a ∪ c) × (b ∪ d)`
   */
  val unionOfTwoRelationsWithField = Lemma(
    (relationBetween(r1, a, b), relationBetween(r2, c, d)) |- relationBetween(r1 ∪ r2, a ∪ c, b ∪ d)
  ) {
    have(
      (r1 ⊆ (a × b), r2 ⊆ (c × d), ((a × b) ∪ (c × d)) ⊆ ((a ∪ c) × (b ∪ d))) |-
        (r1 ∪ r2) ⊆ ((a ∪ c) × (b ∪ d))
    ) by Cut(
      unionOfSubsetsOfDifferentSets of (a := r1, b := r2, c := a × b, d := c × d),
      subsetTransitivity of (x := r1 ∪ r2, y := (a × b) ∪ (c × d), z := (a ∪ c) × (b ∪ d))
    )
    have((r1 ⊆ (a × b), r2 ⊆ (c × d)) |- (r1 ∪ r2) ⊆ ((a ∪ c) × (b ∪ d))) by Cut(unionOfCartesianProducts, lastStep)
    thenHave((relationBetween(r1, a, b), r2 ⊆ (c × d)) |- relationBetween(r1 ∪ r2, a ∪ c, b ∪ d)) by Substitution.ApplyRules(relationBetween.definition)
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := r2, a := c, b := d))
  }

  val relationBetweenSingleton = Lemma(
    relationBetween(singleton(pair(x, y)), singleton(x), singleton(y))
  ) {
    have(relationBetween(singleton(x) × singleton(y), singleton(x), singleton(y))) by Cut(
      subsetReflexivity of (x := singleton(x) × singleton(y)),
      relationBetweenIntro of (r := singleton(x) × singleton(y), a := singleton(x), b := singleton(y))
    )
    thenHave(thesis) by Substitution.ApplyRules(singletonCartesianProduct)
  }

  val relationBetweenSubsetDomains = Lemma(
    (relationBetween(r, a, b), a ⊆ c, b ⊆ d) |- relationBetween(r, c, d)
  ) {
    have((r ⊆ (a × b), a ⊆ c, b ⊆ d) |- r ⊆ (c × d)) by Cut(
      cartesianProductSubset of (w := a, x := b, y := c, z := d),
      subsetTransitivity of (x := r, y := a × b, z := c × d)
    )
    thenHave((r ⊆ (a × b), a ⊆ c, b ⊆ d) |- relationBetween(r, c, d)) by Substitution.ApplyRules(relationBetween.definition of (a := c, b := d))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }

  val relationBetweenSubsetLeftDomain = Lemma(
    (relationBetween(r, a, b), a ⊆ c) |- relationBetween(r, c, b)
  ) {
    have(thesis) by Cut(subsetReflexivity of (x := b), relationBetweenSubsetDomains of (d := b))
  }

  val relationBetweenSubsetRightDomain = Lemma(
    (relationBetween(r, a, b), b ⊆ d) |- relationBetween(r, a, d)
  ) {
    have(thesis) by Cut(subsetReflexivity of (x := a), relationBetweenSubsetDomains of (c := a))
  }

  val relationDomainUniqueness = Lemma(
    ∃!(z, ∀(a, a ∈ z <=> (a ∈ union(union(r)) /\ ∃(b, pair(a, b) ∈ r))))
  ) {
    have(thesis) by UniqueComprehension(union(union(r)), lambda(a, ∃(b, pair(a, b) ∈ r)))
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
   * The first part is proved redundant by [[pairComponentsInUnionUnion]].
   * We have,
   *
   *      `dom(r) = {z | ∃ t. (z, t) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationDomain = DEF(r) --> The(z, ∀(a, a ∈ z <=> (a ∈ union(union(r)) /\ ∃(b, pair(a, b) ∈ r))))(relationDomainUniqueness)

  val dom = relationDomain

  val relationDomainMembership = Lemma(
    a ∈ dom(r) <=> ∃(b, pair(a, b) ∈ r)
  ) {
    have(pair(a, b) ∈ r |- a ∈ union(union(r))) by Weakening(pairComponentsInUnionUnion of (x := a, y := b, z := r))
    thenHave(∃(b, pair(a, b) ∈ r) |- a ∈ union(union(r))) by LeftExists
    val redundancy = thenHave(∃(b, pair(a, b) ∈ r) ==> a ∈ union(union(r))) by RightImplies

    have(∀(a, a ∈ dom(r) <=> (a ∈ union(union(r)) /\ ∃(b, pair(a, b) ∈ r)))) by InstantiateForall(dom(r))(dom.definition)
    thenHave(a ∈ dom(r) <=> (a ∈ union(union(r)) /\ ∃(b, pair(a, b) ∈ r))) by InstantiateForall(a)
    thenHave(∃(b, pair(a, b) ∈ r) ==> a ∈ union(union(r)) |- a ∈ dom(r) <=> ∃(b, pair(a, b) ∈ r)) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  /**
   * Lemma --- Relation Domain Introduction Rule
   *
   *   `(a, b) ∈ r ⊢ a ∈ dom(r)`
   */
  val relationDomainIntroPair = Lemma(
    pair(a, b) ∈ r |- a ∈ dom(r)
  ) {
    have(pair(a, b) ∈ r |- pair(a, b) ∈ r) by Hypothesis
    thenHave(pair(a, b) ∈ r |- ∃(b, pair(a, b) ∈ r)) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationDomainMembership)
  }

  /**
   * Lemma --- Relation Domain Elimination Rule
   *
   *   `a ∈ dom(r) ⊢ ∃ b. (a, b) ∈ r`
   */
  val relationDomainElim = Lemma(
    a ∈ dom(r) |- ∃(b, pair(a, b) ∈ r)
  ) {
    have(thesis) by Weakening(relationDomainMembership)
  }

  /**
    * Lemma --- Domain of the singleton pair relation
    * 
    *  `dom({(a, b)}) = {a}`
    */
  val relationDomainSingleton = Lemma(
    dom(singleton(pair(a, b))) === singleton(a)
  ) {
    val backward = have(x ∈ singleton(a) ==> x ∈ dom(singleton(pair(a, b)))) subproof {
      have(a ∈ dom(singleton(pair(a, b)))) by Cut(singletonIntro of (x := pair(a, b)), relationDomainIntroPair of (r := singleton(pair(a, b))))
      thenHave(x ∈ singleton(a) |- x ∈ dom(singleton(pair(a, b)))) by Substitution.ApplyRules(singletonElim of (y := x, x := a))
    }

    val forward = have(x ∈ dom(singleton(pair(a, b))) ==> x ∈ singleton(a)) subproof {
      have(pair(x, c) === pair(a, b) |- x === a) by Weakening(pairExtensionality of (a := x, b := c, c := a, d := b))
      have(pair(x, c) ∈ singleton(pair(a, b)) |- x === a) by Cut(singletonElim of (y := pair(x, c), x := pair(a, b)), lastStep)
      thenHave(∃(c, pair(x, c) ∈ singleton(pair(a, b))) |- x === a) by LeftExists
      val xEqA = have(x ∈ dom(singleton(pair(a, b))) |- x === a) by Cut(relationDomainElim of (a := x, r := singleton(pair(a, b))), lastStep)
      have(x === a |- x ∈ singleton(a)) by RightSubstEq.withParametersSimple(List((x, a)), lambda(x, x ∈ singleton(a)))(singletonIntro of (x := a))
      have(x ∈ dom(singleton(pair(a, b))) |- x ∈ singleton(a)) by Cut(xEqA, lastStep)

    }

    have(x ∈ dom(singleton(pair(a, b))) <=> x ∈ singleton(a)) by RightIff(forward, backward)
    thenHave(∀(x, x ∈ dom(singleton(pair(a, b))) <=> x ∈ singleton(a))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := dom(singleton(pair(a, b))), y := singleton(a)))
  }

  val relationDomainSetUnion = Lemma(
    dom((r1 ∪ r2)) === dom(r1) ∪ dom(r2)
  ) {
    val forward = have(a ∈ dom((r1 ∪ r2)) ==> a ∈ (dom(r1) ∪ dom(r2))) subproof {
      have(pair(a, b) ∈ (r1 ∪ r2) |- (a ∈ dom(r1), pair(a, b) ∈ r2)) by Cut(setUnionElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntroPair of (r := r1))
      have(pair(a, b) ∈ (r1 ∪ r2) |- (a ∈ dom(r1), a ∈ dom(r2))) by Cut(lastStep, relationDomainIntroPair of (r := r2))
      have(pair(a, b) ∈ (r1 ∪ r2) |- (a ∈ dom(r2), a ∈ (dom(r1) ∪ dom(r2)))) by Cut(
        lastStep,
        setUnionLeftIntro of (z := a, x := dom(r1), y := dom(r2))
      )
      have(pair(a, b) ∈ (r1 ∪ r2) |- a ∈ (dom(r1) ∪ dom(r2))) by Cut(
        lastStep,
        setUnionRightIntro of (z := a, x := dom(r1), y := dom(r2))
      )
      thenHave(∃(b, pair(a, b) ∈ (r1 ∪ r2)) |- a ∈ (dom(r1) ∪ dom(r2))) by LeftExists
      have(a ∈ dom((r1 ∪ r2)) |- a ∈ (dom(r1) ∪ dom(r2))) by Cut(relationDomainElim of (r := r1 ∪ r2), lastStep)
    }

    val backward = have(a ∈ (dom(r1) ∪ dom(r2)) ==> a ∈ dom((r1 ∪ r2))) subproof {

      have(pair(a, b) ∈ r1 |- ∃(b, pair(a, b) ∈ (r1 ∪ r2))) by RightExists(setUnionLeftIntro of (z := pair(a, b), x := r1, y := r2))
      val left = thenHave(∃(b, pair(a, b) ∈ r1) |- ∃(b, pair(a, b) ∈ (r1 ∪ r2))) by LeftExists

      have(pair(a, b) ∈ r2 |- ∃(b, pair(a, b) ∈ (r1 ∪ r2))) by RightExists(setUnionRightIntro of (z := pair(a, b), x := r1, y := r2))
      val right = thenHave(∃(b, pair(a, b) ∈ r2) |- ∃(b, pair(a, b) ∈ (r1 ∪ r2))) by LeftExists

      have(a ∈ (dom(r1) ∪ dom(r2)) |- (∃(b, pair(a, b) ∈ r1), a ∈ dom(r2))) by Cut(
        setUnionElim of (z := a, x := dom(r1), y := dom(r2)),
        relationDomainElim of (r := r1)
      )
      have(a ∈ (dom(r1) ∪ dom(r2)) |- (∃(b, pair(a, b) ∈ r1), ∃(b, pair(a, b) ∈ r2))) by Cut(lastStep, relationDomainElim of (r := r2))
      have(a ∈ (dom(r1) ∪ dom(r2)) |- (∃(b, pair(a, b) ∈ (r1 ∪ r2)), ∃(b, pair(a, b) ∈ r2))) by Cut(lastStep, left)
      have(a ∈ (dom(r1) ∪ dom(r2)) |- ∃(b, pair(a, b) ∈ (r1 ∪ r2))) by Cut(lastStep, right)
      thenHave(a ∈ (dom(r1) ∪ dom(r2)) |- a ∈ dom((r1 ∪ r2))) by Substitution.ApplyRules(relationDomainMembership of (r := (r1 ∪ r2)))
    }

    have(a ∈ (dom(r1) ∪ dom(r2)) <=> a ∈ dom((r1 ∪ r2))) by RightIff(forward, backward)
    thenHave(∀(a, a ∈ (dom(r1) ∪ dom(r2)) <=> a ∈ dom((r1 ∪ r2)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := dom((r1 ∪ r2)), y := dom(r1) ∪ dom(r2)))
  }

  val relationDomainUnion = Lemma(
    t ∈ dom(union(z)) <=> ∃(y, y ∈ z /\ t ∈ dom(y))
  ) {
    val forward = have(∃(a, pair(t, a) ∈ union(z)) ==> ∃(y, y ∈ z /\ t ∈ dom(y))) subproof {
      have(y ∈ z |- y ∈ z) by Hypothesis
      have((pair(t, a) ∈ y, y ∈ z) |- t ∈ dom(y) /\ y ∈ z) by RightAnd(relationDomainIntroPair of (a := t, b := a, r := y), lastStep)
      thenHave((pair(t, a) ∈ y, y ∈ z) |- ∃(y, t ∈ dom(y) /\ y ∈ z)) by RightExists
      thenHave((pair(t, a) ∈ y /\ y ∈ z) |- ∃(y, t ∈ dom(y) /\ y ∈ z)) by LeftAnd
      thenHave(∃(y, pair(t, a) ∈ y /\ y ∈ z) |- ∃(y, t ∈ dom(y) /\ y ∈ z)) by LeftExists
      have(pair(t, a) ∈ union(z) |- ∃(y, y ∈ z /\ t ∈ dom(y))) by Cut(unionElim of (z := pair(t, a), x := z), lastStep)
      thenHave(∃(a, pair(t, a) ∈ union(z)) |- ∃(y, y ∈ z /\ t ∈ dom(y))) by LeftExists
    }
    val backward = have(∃(y, y ∈ z /\ t ∈ dom(y)) ==> ∃(a, pair(t, a) ∈ union(z))) subproof {
      have((pair(t, a) ∈ y, y ∈ z) |- ∃(a, pair(t, a) ∈ union(z))) by RightExists(unionIntro of (z := pair(t, a), x := z))
      thenHave((∃(a, pair(t, a) ∈ y), y ∈ z) |- ∃(a, pair(t, a) ∈ union(z))) by LeftExists
      have((y ∈ z, t ∈ dom(y)) |- ∃(a, pair(t, a) ∈ union(z))) by Cut(relationDomainElim of (a := t, r := y), lastStep)
      thenHave((y ∈ z /\ t ∈ dom(y)) |- ∃(a, pair(t, a) ∈ union(z))) by LeftAnd
      thenHave(∃(y, y ∈ z /\ t ∈ dom(y)) |- ∃(a, pair(t, a) ∈ union(z))) by LeftExists
    }

    have(∃(a, pair(t, a) ∈ union(z)) <=> ∃(y, y ∈ z /\ t ∈ dom(y))) by RightIff(forward, backward)
    thenHave(thesis) by Substitution.ApplyRules(relationDomainMembership)
  }

  val relationDomainSubset = Lemma(
    r1 ⊆ r2 |- dom(r1) ⊆ dom(r2)
  ) {
    have((r1 ⊆ r2, pair(a, b) ∈ r1) |- a ∈ dom(r2)) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntroPair of (r := r2))
    thenHave((r1 ⊆ r2, ∃(b, pair(a, b) ∈ r1)) |- a ∈ dom(r2)) by LeftExists
    have((r1 ⊆ r2, a ∈ dom(r1)) |- a ∈ dom(r2)) by Cut(relationDomainElim of (r := r1), lastStep)
    thenHave(r1 ⊆ r2 |- a ∈ dom(r1) ==> a ∈ dom(r2)) by RightImplies
    thenHave(r1 ⊆ r2 |- ∀(a, a ∈ dom(r1) ==> a ∈ dom(r2))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := dom(r1), y := dom(r2)))
  }

  val relationRangeUniqueness = Lemma(
    ∃!(z, ∀(b, b ∈ z <=> (b ∈ union(union(r)) /\ ∃(a, pair(a, b) ∈ r))))
  ) {
    have(thesis) by UniqueComprehension(union(union(r)), lambda(b, ∃(a, pair(a, b) ∈ r)))
  }

  /**
   * (Binary) Relation Range --- The set containing the second elements of every
   * pair in a relation `r`. Alternatively, the set of elements which another
   * element relates to by `r`.
   *
   *      `range(r) = {b ∈ ∪ ∪ r | ∃ a. (a, b) ∈ r}
   *
   * The proofs are guaranteed and generated by [[UniqueComprehension]].
   *
   * The first part is proved redundant by [[pairComponentsInUnionUnion]].
   * We have,
   *
   *      `ran(r) = {b | ∃ a. (a, b) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationRange = DEF(r) --> The(z, ∀(b, b ∈ z <=> (b ∈ union(union(r)) /\ ∃(a, pair(a, b) ∈ r))))(relationRangeUniqueness)

  val ran = relationRange

  val relationRangeMembership = Lemma(
    b ∈ ran(r) <=> ∃(a, pair(a, b) ∈ r)
  ) {
    have(pair(a, b) ∈ r |- b ∈ union(union(r))) by Weakening(pairComponentsInUnionUnion of (x := a, y := b, z := r))
    thenHave(∃(a, pair(a, b) ∈ r) |- b ∈ union(union(r))) by LeftExists
    val redundancy = thenHave(∃(a, pair(a, b) ∈ r) ==> b ∈ union(union(r))) by RightImplies

    have(∀(b, b ∈ ran(r) <=> (b ∈ union(union(r)) /\ ∃(a, pair(a, b) ∈ r)))) by InstantiateForall(ran(r))(ran.definition)
    thenHave(b ∈ ran(r) <=> (b ∈ union(union(r)) /\ ∃(a, pair(a, b) ∈ r))) by InstantiateForall(b)
    thenHave(∃(a, pair(a, b) ∈ r) ==> b ∈ union(union(r)) |- b ∈ ran(r) <=> ∃(a, pair(a, b) ∈ r)) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  val relationRangeIntroPair = Lemma(
    pair(a, b) ∈ r |- b ∈ ran(r)
  ) {
    have(pair(a, b) ∈ r |- pair(a, b) ∈ r) by Hypothesis
    thenHave(pair(a, b) ∈ r |- ∃(a, pair(a, b) ∈ r)) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationRangeMembership)
  }

  val relationRangeElim = Lemma(
    b ∈ ran(r) |- ∃(a, pair(a, b) ∈ r)
  ) {
    have(thesis) by Weakening(relationRangeMembership)
  }

  /**
   * Lemma --- The range of the empty function is empty.
   *
   *     `Ran(∅) = ∅`
   */
  val rangeEmpty = Lemma(ran(∅) === ∅) {
    have(∀(a, pair(a, b) ∉ ∅)) by RightForall(emptySetAxiom of (x := pair(a, b)))
    thenHave(∃(a, pair(a, b) ∈ ∅) |- ()) by Restate
    have(b ∈ ran(∅) |- ()) by Cut(relationRangeElim of (r := ∅), lastStep)
    thenHave(∃(b, b ∈ ran(∅)) |- ()) by LeftExists
    have(ran(∅) =/= ∅ |- ()) by Cut(nonEmptySetHasAnElement of (x := ran(∅)), lastStep)
  }

  val relationRangeSubset = Lemma(
    r1 ⊆ r2 |- ran(r1) ⊆ ran(r2)
  ) {
    have((r1 ⊆ r2, pair(a, b) ∈ r1) |- b ∈ ran(r2)) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationRangeIntroPair of (r := r2))
    thenHave((r1 ⊆ r2, ∃(a, pair(a, b) ∈ r1)) |- b ∈ ran(r2)) by LeftExists
    have((r1 ⊆ r2, b ∈ ran(r1)) |- b ∈ ran(r2)) by Cut(relationRangeElim of (r := r1), lastStep)
    thenHave(r1 ⊆ r2 |- b ∈ ran(r1) ==> b ∈ ran(r2)) by RightImplies
    thenHave(r1 ⊆ r2 |- ∀(b, b ∈ ran(r1) ==> b ∈ ran(r2))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := ran(r1), y := ran(r2)))
  }

  val pairInRelation = Lemma(
    pair(a, b) ∈ r |- a ∈ dom(r) /\ b ∈ ran(r)
  ) {
    have(thesis) by RightAnd(relationDomainIntroPair, relationRangeIntroPair)
  }

  val relationBetweenDomain = Lemma(
    relationBetween(r, a, b) |- dom(r) ⊆ a
  ) {
    have((relationBetween(r, a, b), pair(x, y) ∈ r) |- x ∈ a) by Weakening(relationBetweenElimPair)
    thenHave((relationBetween(r, a, b), ∃(y, pair(x, y) ∈ r)) |- x ∈ a) by LeftExists
    have((relationBetween(r, a, b), x ∈ dom(r)) |- x ∈ a) by Cut(relationDomainElim of (a := x), lastStep)
    thenHave(relationBetween(r, a, b) |- x ∈ dom(r) ==> x ∈ a) by RightImplies
    thenHave(relationBetween(r, a, b) |- ∀(x, x ∈ dom(r) ==> x ∈ a)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := dom(r), y := a))
  }

  val relationBetweenRange = Lemma(
    relationBetween(r, a, b) |- ran(r) ⊆ b
  ) {
    have((relationBetween(r, a, b), pair(x, y) ∈ r) |- y ∈ b) by Weakening(relationBetweenElimPair)
    thenHave((relationBetween(r, a, b), ∃(x, pair(x, y) ∈ r)) |- y ∈ b) by LeftExists
    have((relationBetween(r, a, b), y ∈ ran(r)) |- y ∈ b) by Cut(relationRangeElim of (b := y), lastStep)
    thenHave(relationBetween(r, a, b) |- y ∈ ran(r) ==> y ∈ b) by RightImplies
    thenHave(relationBetween(r, a, b) |- ∀(y, y ∈ ran(r) ==> y ∈ b)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := ran(r), y := b))
  }

  val relationBetweenBetweenDomainAndRange = Lemma(
    relationBetween(r, a, b) |- relationBetween(r, dom(r), ran(r))
  ) {
    have(fst(p) ∈ dom(r) /\ snd(p) ∈ ran(r) |- pair(fst(p), snd(p)) ∈ (dom(r) × ran(r))) by LeftAnd(
      cartesianProductIntro of (a := fst(p), b := snd(p), x := dom(r), y := ran(r))
    )
    have(pair(fst(p), snd(p)) ∈ r |- pair(fst(p), snd(p)) ∈ (dom(r) × ran(r))) by Cut(
      pairInRelation of (a := fst(p), b := snd(p)),
      lastStep
    )
    thenHave((relationBetween(r, a, b), p ∈ r) |- p ∈ (dom(r) × ran(r))) by Substitution.ApplyRules(pairReconstructionInRelationBetween)
    thenHave(relationBetween(r, a, b) |- p ∈ r ==> p ∈ (dom(r) × ran(r))) by RightImplies
    thenHave(relationBetween(r, a, b) |- ∀(p, p ∈ r ==> p ∈ (dom(r) × ran(r)))) by RightForall
    have(relationBetween(r, a, b) |- r ⊆ (dom(r) × ran(r))) by Cut(
      lastStep,
      subsetIntro of (x := r, y := dom(r) × ran(r))
    )
    have(thesis) by Cut(lastStep, relationBetweenIntro of (a := dom(r), b := ran(r)))
  }

  /**
   * `r` is a relation *from* `a` if there ∃ a set `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relationFrom = DEF(r, a) --> ∃(b, relationBetween(r, a, b))

  val relationBetweenIsRelationFrom = Lemma(relationBetween(r, a, b) |- relationFrom(r, a)) {
    have(relationBetween(r, a, b) |- relationBetween(r, a, b)) by Hypothesis
    thenHave(relationBetween(r, a, b) |- ∃(b, relationBetween(r, a, b))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val pairReconstructionInRelationFrom = Lemma(
    (relationFrom(r, a), p ∈ r) |- p === pair(fst(p), snd(p))
  ) {
    have((∃(b, relationBetween(r, a, b)), p ∈ r) |- p === pair(fst(p), snd(p))) by LeftExists(pairReconstructionInRelationBetween)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  /**
   * Lemma --- Pair in Relation
   *
   * If a pair `(x, y)` ∃ in a relation `r` from `a` to `b`,
   * then `x` and `y` are elements of `a` and `b` respectively.
   */
  val relationFromElimPair = Lemma(
    (relationFrom(r, a), pair(x, y) ∈ r) |- x ∈ a
  ) {
    have((relationBetween(r, a, b), pair(x, y) ∈ r) |- x ∈ a) by Weakening(relationBetweenElimPair)
    thenHave((∃(b, relationBetween(r, a, b)), pair(x, y) ∈ r) |- x ∈ a) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val relationFromElim = Lemma(
    (relationFrom(r, a), p ∈ r) |- fst(p) ∈ a
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelationFrom)(relationFromElimPair of (x := fst(p), y := snd(p)))
  }

  val relationFromSubset = Lemma(
    (r1 ⊆ r2, relationFrom(r2, a)) |- relationFrom(r1, a)
  ) {
    have((r1 ⊆ r2, relationBetween(r2, a, b)) |- relationFrom(r1, a)) by Cut(relationBetweenSubset, relationBetweenIsRelationFrom of (r := r1))
    thenHave((r1 ⊆ r2, ∃(b, relationBetween(r2, a, b))) |- relationFrom(r1, a)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition of (r := r2))
  }

  val relationFromSetUnion = Lemma(
    (relationFrom(r1, a), relationFrom(r2, b)) |- relationFrom((r1 ∪ r2), a ∪ b)
  ) {
    have((relationBetween(r1, a, x), relationBetween(r2, b, y)) |- ∃(y, relationBetween((r1 ∪ r2), a ∪ b, y))) by RightExists(
      unionOfTwoRelationsWithField of (c := b, b := x, d := y)
    )
    thenHave((∃(x, relationBetween(r1, a, x)), relationBetween(r2, b, y)) |- ∃(y, relationBetween((r1 ∪ r2), a ∪ b, y))) by LeftExists
    thenHave((∃(x, relationBetween(r1, a, x)), ∃(y, relationBetween(r2, b, y))) |- ∃(y, relationBetween((r1 ∪ r2), a ∪ b, y))) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(
      relationFrom.definition of (r := r1 ∪ r2, a := a ∪ b),
      relationFrom.definition of (r := r1),
      relationFrom.definition of (r := r2, a := b)
    )
  }

  val relationFromBetweenDomainAndRange = Lemma(
    relationFrom(r, a) |- relationBetween(r, dom(r), ran(r))
  ) {
    have(∃(b, relationBetween(r, a, b)) |- relationBetween(r, dom(r), ran(r))) by LeftExists(relationBetweenBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

    val relationFromDomain = Lemma(
    relationFrom(r, a) |- dom(r) ⊆ a
  ) {
    have(∃(b, relationBetween(r, a, b)) |- dom(r) ⊆ a) by LeftExists(relationBetweenDomain)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val relationFromToRange = Lemma(
    relationFrom(r, a) |- relationBetween(r, a, ran(r))
  ) {
    have((relationFrom(r, a), dom(r) ⊆ a) |- relationBetween(r, a, ran(r))) by 
      Cut(relationFromBetweenDomainAndRange, relationBetweenSubsetLeftDomain of (b := ran(r), a := dom(r), c := a))
    have(thesis) by Cut(relationFromDomain, lastStep)
  }

  /**
   * `r` is a relation if there exist sets `a` and `b` such that `r` is a
   * relation from `a` to `b`.
   */
  val relation = DEF(r) --> ∃(a, relationFrom(r, a))

  val pairReconstructionInRelation = Lemma(
    (relation(r), p ∈ r) |- p === pair(fst(p), snd(p))
  ) {
    have((∃(a, relationFrom(r, a)), p ∈ r) |- p === pair(fst(p), snd(p))) by LeftExists(pairReconstructionInRelationFrom)
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationElim = Lemma(
    (relation(r), p ∈ r) |- fst(p) ∈ dom(r) /\ snd(p) ∈ ran(r)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(pairInRelation of (a := fst(p), b := snd(p)))
  }

  val relationFromIsRelation = Lemma(relationFrom(r, a) |- relation(r)) {
    have(relationFrom(r, a) |- relationFrom(r, a)) by Hypothesis
    thenHave(relationFrom(r, a) |- ∃(a, relationFrom(r, a))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationBetweenIsRelation = Lemma(relationBetween(r, a, b) |- relation(r)) {
    have(thesis) by Cut(relationBetweenIsRelationFrom, relationFromIsRelation)
  }

  val relationDomainIntro = Lemma(
    (relation(r), p ∈ r) |- fst(p) ∈ dom(r)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationDomainIntroPair of (a := fst(p), b := snd(p)))
  }

  val relationRangeIntro = Lemma(
    (relation(r), p ∈ r) |- snd(p) ∈ ran(r)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationRangeIntroPair of (a := fst(p), b := snd(p)))
  }

  val relationSubset = Lemma(
    (r1 ⊆ r2, relation(r2)) |- relation(r1)
  ) {
    have((r1 ⊆ r2, relationFrom(r2, a)) |- relation(r1)) by Cut(relationFromSubset, relationFromIsRelation of (r := r1))
    thenHave((r1 ⊆ r2, ∃(a, relationFrom(r2, a))) |- relation(r1)) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition of (r := r2))
  }

  /**
   * Lemma --- the union of two relations is a relation. (weaker form)
   *
   * Weakening of [[unionOfTwoRelationsWithField]] to unknown fields.
   */
  val relationSetUnion = Lemma(
    (relation(r1), relation(r2)) |- relation((r1 ∪ r2))
  ) {
    have((relationFrom(r1, a), relationFrom(r2, b)) |- ∃(y, relationFrom((r1 ∪ r2), y))) by RightExists(relationFromSetUnion)
    thenHave((∃(a, relationFrom(r1, a)), relationFrom(r2, b)) |- ∃(y, relationFrom((r1 ∪ r2), y))) by LeftExists
    thenHave((∃(a, relationFrom(r1, a)), ∃(b, relationFrom(r2, b))) |- ∃(y, relationFrom((r1 ∪ r2), y))) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(relation.definition of (r := (r1 ∪ r2)), relation.definition of (r := r1), relation.definition of (r := r2))
  }

  /**
   * Lemma --- the union of a set of relations is a relation itself.
   *
   *    `\∀ t \in z. relation(t) |- relation(union(z))`
   *
   * This implication also holds in the other direction, but that is
   * not as useful.
   */
  val unionOfRelationSet = Lemma(
    ∀(r, r ∈ z ==> relation(r)) |- relation(union(z))
  ) {
    val doms = variable
    val rans = variable
    val domsDef = ∀(x, x ∈ doms <=> ∃(r, r ∈ z /\ (x === dom(r))))
    val ransDef = ∀(x, x ∈ rans <=> ∃(r, r ∈ z /\ (x === ran(r))))

    val inDoms = have((domsDef, r ∈ z, fst(p) ∈ dom(r)) |- fst(p) ∈ union(doms)) subproof {
      have(r ∈ z |- r ∈ z /\ (dom(r) === dom(r))) by Restate
      val exDoms = thenHave(r ∈ z |- ∃(r2, r2 ∈ z /\ (dom(r) === dom(r2)))) by RightExists
      have(domsDef |- domsDef) by Hypothesis
      thenHave(domsDef |- dom(r) ∈ doms <=> ∃(r2, r2 ∈ z /\ (dom(r) === dom(r2)))) by InstantiateForall(dom(r))
      thenHave((domsDef, ∃(r2, r2 ∈ z /\ (dom(r) === dom(r2)))) |- dom(r) ∈ doms) by Weakening
      have((domsDef, r ∈ z) |- dom(r) ∈ doms) by Cut(exDoms, lastStep)
      have((domsDef, r ∈ z) |- dom(r) ⊆ union(doms)) by Cut(lastStep, subsetUnion of (x := dom(r), y := doms))
      have(thesis) by Cut(lastStep, subsetElim of (z := fst(p), x := dom(r), y := union(doms)))
    }

    val inRans = have((ransDef, r ∈ z, snd(p) ∈ ran(r)) |- snd(p) ∈ union(rans)) subproof {
      have(r ∈ z |- r ∈ z /\ (ran(r) === ran(r))) by Restate
      val exDoms = thenHave(r ∈ z |- ∃(r2, r2 ∈ z /\ (ran(r) === ran(r2)))) by RightExists
      have(ransDef |- ransDef) by Hypothesis
      thenHave(ransDef |- ran(r) ∈ rans <=> ∃(r2, r2 ∈ z /\ (ran(r) === ran(r2)))) by InstantiateForall(ran(r))
      thenHave((ransDef, ∃(r2, r2 ∈ z /\ (ran(r) === ran(r2)))) |- ran(r) ∈ rans) by Weakening
      have((ransDef, r ∈ z) |- ran(r) ∈ rans) by Cut(exDoms, lastStep)
      have((ransDef, r ∈ z) |- ran(r) ⊆ union(rans)) by Cut(lastStep, subsetUnion of (x := ran(r), y := rans))
      have(thesis) by Cut(lastStep, subsetElim of (z := snd(p), x := ran(r), y := union(rans)))
    }

    val relSet = ∀(r, r ∈ z ==> relation(r))
    have(relSet |- relSet) by Hypothesis
    val relSetMembership = thenHave((relSet, r ∈ z) |- relation(r)) by InstantiateForall(r)

    val inCartProduct = have(fst(p) ∈ union(doms) /\ snd(p) ∈ union(rans) |- pair(fst(p), snd(p)) ∈ (union(doms) × union(rans))) by LeftAnd(
      cartesianProductIntro of (a := fst(p), b := snd(p), x := union(doms), y := union(rans))
    )

    have((domsDef, ransDef, r ∈ z, fst(p) ∈ dom(r), snd(p) ∈ ran(r)) |- fst(p) ∈ union(doms) /\ snd(p) ∈ union(rans)) by RightAnd(
      inDoms,
      inRans
    )
    thenHave(
      (domsDef, ransDef, r ∈ z, fst(p) ∈ dom(r) /\ snd(p) ∈ ran(r)) |- fst(p) ∈ union(doms) /\ snd(p) ∈ union(rans)
    ) by LeftAnd
    have((domsDef, ransDef, p ∈ r, relation(r), r ∈ z) |- fst(p) ∈ union(doms) /\ snd(p) ∈ union(rans)) by Cut(relationElim, lastStep)
    have((domsDef, ransDef, p ∈ r, relation(r), r ∈ z) |- pair(fst(p), snd(p)) ∈ (union(doms) × union(rans))) by Cut(lastStep, inCartProduct)
    thenHave((domsDef, ransDef, p ∈ r, relation(r), r ∈ z) |- p ∈ (union(doms) × union(rans))) by Substitution.ApplyRules(pairReconstructionInRelation)
    have((domsDef, ransDef, relSet, p ∈ r, r ∈ z) |- p ∈ (union(doms) × union(rans))) by Cut(relSetMembership, lastStep)
    thenHave((domsDef, ransDef, relSet, p ∈ r /\ r ∈ z) |- p ∈ (union(doms) × union(rans))) by LeftAnd
    thenHave((domsDef, ransDef, relSet, ∃(r, p ∈ r /\ r ∈ z)) |- p ∈ (union(doms) × union(rans))) by LeftExists
    have((domsDef, ransDef, relSet, p ∈ union(z)) |- p ∈ (union(doms) × union(rans))) by Cut(unionElim of (x := z, z := p), lastStep)
    thenHave((domsDef, ransDef, relSet) |- p ∈ union(z) ==> p ∈ (union(doms) × union(rans))) by RightImplies
    thenHave((domsDef, ransDef, relSet) |- ∀(p, p ∈ union(z) ==> p ∈ (union(doms) × union(rans)))) by RightForall
    have((domsDef, ransDef, relSet) |- union(z) ⊆ (union(doms) × union(rans))) by Cut(lastStep, subsetIntro of (x := union(z), y := union(doms) × union(rans)))
    have((domsDef, ransDef, relSet) |- relationBetween(union(z), union(doms), union(rans))) by Cut(lastStep, relationBetweenIntro of (r := union(z), a := union(doms), b := union(rans)))
    have((domsDef, ransDef, relSet) |- relation(union(z))) by Cut(lastStep, relationBetweenIsRelation of (r := union(z), a := union(doms), b := union(rans)))
    thenHave((∃(doms, domsDef), ransDef, relSet) |- relation(union(z))) by LeftExists
    thenHave((∃(doms, domsDef), ∃(rans, ransDef), relSet) |- relation(union(z))) by LeftExists
    have((∃!(doms, domsDef), ∃(rans, ransDef), relSet) |- relation(union(z))) by Cut(existsOneImpliesExists of (P := lambda(doms, domsDef)), lastStep)
    have((∃!(doms, domsDef), ∃!(rans, ransDef), relSet) |- relation(union(z))) by Cut(existsOneImpliesExists of (P := lambda(rans, ransDef)), lastStep)
    have((∃!(rans, ransDef), relSet) |- relation(union(z))) by Cut(replacementClassFunction of (A := z, F := lambda(r, dom(r))), lastStep)
    have(thesis) by Cut(replacementClassFunction of (A := z, F := lambda(r, ran(r))), lastStep)

  }

  val relationIsRelationBetween = Lemma(
    relation(r) |- relationBetween(r, dom(r), ran(r))
  ) {
    have(∃(a, relationFrom(r, a)) |- relationBetween(r, dom(r), ran(r))) by LeftExists(relationFromBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationIsRelationFrom = Lemma(
    relation(r) |- relationFrom(r, dom(r))
  ) {
    have(thesis) by Cut(relationIsRelationBetween, relationBetweenIsRelationFrom of (a := dom(r), b := ran(r)))
  }

  /**
   * Lemma --- The only relation with an empty domain is the empty relation.
   *
   *     `relation(r), Dom(r) = ∅ |- r = ∅`
   */
  val relationDomainEmpty = Lemma(
    (relation(r), dom(r) === ∅) |- r === ∅
  ) {
    have((relation(r), dom(r) === ∅) |- relationBetween(r, ∅, ran(r))) by
      RightSubstEq.withParametersSimple(List((dom(r), ∅)), lambda(x, relationBetween(r, x, ran(r))))(relationIsRelationBetween)
    have(thesis) by Cut(lastStep, relationBetweenLeftEmptyIsEmpty of (b := ran(r)))
  }

  /**
   * Lemma --- The only relation with an empty range is the empty relation.
   *
   *     `relation(r), Ran(r) = ∅ |- r = ∅`
   */
  val relationRangeEmpty = Lemma(
    (relation(r), ran(r) === ∅) |- r === ∅
  ) {
    have((relation(r), ran(r) === ∅) |- relationBetween(r, dom(r), ∅)) by
      RightSubstEq.withParametersSimple(List((ran(r), ∅)), lambda(x, relationBetween(r, dom(r), x)))(relationIsRelationBetween)
    have(thesis) by Cut(lastStep, relationBetweenRightEmptyIsEmpty of (a := dom(r)))
  }

  val inverseRelationUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> ∃(p, p ∈ r /\ (t === swap(p)))))
  ) {
    have(thesis) by Restate.from(replacementClassFunction of (A := r, F := lambda(p, swap(p))))
  }

  val inverseRelation = DEF(r) --> The(z, ∀(t, t ∈ z <=> ∃(p, p ∈ r /\ (t === swap(p)))))(inverseRelationUniqueness)

  def inv = inverseRelation

  val inverseRelationMembership = Lemma(
    p ∈ r <=> swap(p) ∈ inverseRelation(r)
  ) {
    have(∀(t, t ∈ inverseRelation(r) <=> ∃(p, p ∈ r /\ (t === swap(p))))) by InstantiateForall(inverseRelation(r))(inverseRelation.definition)
    val definition = thenHave(swap(p) ∈ inverseRelation(r) <=> ∃(b, b ∈ r /\ (swap(p) === swap(b)))) by InstantiateForall(swap(p))

    val forward = have(p ∈ r ==> swap(p) ∈ inverseRelation(r)) subproof {
      have(p ∈ r |- p ∈ r /\ (swap(p) === swap(p))) by Restate
      thenHave(p ∈ r |- ∃(b, b ∈ r /\ (swap(p) === swap(b)))) by RightExists
      thenHave(p ∈ r |- swap(p) ∈ inverseRelation(r)) by Substitution.ApplyRules(definition)
    }

    val backward = have(swap(p) ∈ inverseRelation(r) ==> p ∈ r) subproof {
      have(b ∈ r |- b ∈ r) by Hypothesis
      thenHave((b ∈ r, b === p) |- p ∈ r) by RightSubstEq.withParametersSimple(List((b, p)), lambda(x, x ∈ r))
      have((b ∈ r, swap(b) === swap(p)) |- p ∈ r) by Cut(swapInjectivity of (x := b, y := p), lastStep)
      thenHave(b ∈ r /\ (swap(b) === swap(p)) |- p ∈ r) by LeftAnd
      thenHave(∃(b, b ∈ r /\ (swap(b) === swap(p))) |- p ∈ r) by LeftExists
      thenHave(swap(p) ∈ inverseRelation(r) |- p ∈ r) by Substitution.ApplyRules(definition)
    }
    
    have(thesis) by RightIff(forward, backward)
  }

  val inverseRelationReverseMembership = Lemma(
    swap(p) ∈ r <=> p ∈ inverseRelation(r)
  ) {
    have(thesis) by Substitution.ApplyRules(swapInvolutive)(inverseRelationMembership of (p := swap(p)))
  }

  val inverseRelationMembershipPair = Lemma(
    pair(x, y) ∈ r <=> pair(y, x) ∈ inverseRelation(r)
  ) {
    have(thesis) by Substitution.ApplyRules(swapPair)(inverseRelationMembership of (p := pair(x, y)))
  }

  val inverseInverseRelation = Lemma(
    inverseRelation(inverseRelation(r)) === r
  ) {
    have(p ∈ r <=> p ∈ inverseRelation(inverseRelation(r))) by Substitution.ApplyRules(swapInvolutive, inverseRelationMembership)(inverseRelationMembership of (p := swap(p), r := inverseRelation(r)))
    thenHave(∀(p, p ∈ r <=> p ∈ inverseRelation(inverseRelation(r)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := r, y := inverseRelation(inverseRelation(r))))
  }

  val inverseRelationDomain = Lemma(
    dom(inverseRelation(r)) === ran(r)
  ) {
    val forward = have(b ∈ dom(inverseRelation(r)) ==> b ∈ ran(r)) subproof {
      have(pair(b, a) ∈ inverseRelation(r) |- b ∈ ran(r)) by Substitution.ApplyRules(inverseRelationMembershipPair)(relationRangeIntroPair)
      thenHave(∃(a, pair(b, a) ∈ inverseRelation(r)) |- b ∈ ran(r)) by LeftExists
      have(b ∈ dom(inverseRelation(r)) |- b ∈ ran(r)) by Cut(relationDomainElim of (a := b, r := inverseRelation(r)), lastStep)
    }
    val backward = have(b ∈ ran(r) ==> b ∈ dom(inverseRelation(r))) subproof {
      have(pair(a, b) ∈ r |- b ∈ dom(inverseRelation(r))) by Substitution.ApplyRules(inverseRelationMembershipPair)(relationDomainIntroPair of (r := inverseRelation(r), a := b, b := a))
      thenHave(∃(a, pair(a, b) ∈ r) |- b ∈ dom(inverseRelation(r))) by LeftExists
      have(b ∈ ran(r) |- b ∈ dom(inverseRelation(r)) ) by Cut(relationRangeElim, lastStep)
    }
    have(b ∈ dom(inverseRelation(r)) <=> b ∈ ran(r)) by RightIff(forward, backward)
    thenHave(∀(b, b ∈ dom(inverseRelation(r)) <=> b ∈ ran(r)) ) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := dom(inverseRelation(r)), y := ran(r)))
  }

  val inverseRelationRange = Lemma(
    ran(inverseRelation(r)) === dom(r)
  ) {
    have(dom(r) === ran(inverseRelation(r))) by Substitution.ApplyRules(inverseInverseRelation)(inverseRelationDomain of (r := inverseRelation(r)))
  }

  val inverseRelationIsRelationBetween = Lemma(
    relationBetween(r, a, b) <=> relationBetween(inverseRelation(r), b, a)
  ) {
    val forward = have(relationBetween(r, a, b) ==> relationBetween(inverseRelation(r), b, a)) subproof {
      have(p ∈ inverseRelation(r) |- swap(p) ∈ r) by Weakening(inverseRelationReverseMembership)
      have((p ∈ inverseRelation(r), r ⊆ (a × b)) |- swap(p) ∈ (a × b)) by Cut(lastStep, subsetElim of (z := swap(p), x := r, y := a × b))
      thenHave((p ∈ inverseRelation(r), relationBetween(r, a, b)) |- p ∈ (b × a)) by Substitution.ApplyRules(relationBetween.definition, swapCartesianProduct)
      thenHave(relationBetween(r, a, b) |- p ∈ inverseRelation(r) ==> p ∈ (b × a)) by RightImplies
      thenHave(relationBetween(r, a, b) |- ∀(p, p ∈ inverseRelation(r) ==> p ∈ (b × a)) ) by RightForall
      have(relationBetween(r, a, b) |- inverseRelation(r) ⊆ (b × a)) by Cut(lastStep, subsetIntro of (x := inverseRelation(r), y := b × a))
      have(relationBetween(r, a, b) |- relationBetween(inverseRelation(r), b, a)) by Cut(lastStep, relationBetweenIntro of (r := inverseRelation(r), a := b, b := a))
    }

    val backward = have(relationBetween(inverseRelation(r), b, a) ==> relationBetween(r, a, b)) by Substitution.ApplyRules(inverseInverseRelation)(forward of (r := inverseRelation(r), a := b, b := a))

    have(thesis) by RightIff(forward, backward)
  }

  val inverseRelationBetweenRangeAndDomain = Lemma(
    relation(r) |- relationBetween(inverseRelation(r), ran(r), dom(r))
  ) {
    have(relationBetween(r, dom(r), ran(r)) |- relationBetween(inverseRelation(r), ran(r), dom(r))) by Weakening(inverseRelationIsRelationBetween of (a := dom(r), b := ran(r)))
    have(thesis) by Cut(relationIsRelationBetween, lastStep)
  }

  val inverseRelationIsRelation = Lemma(
    relation(r) <=> relation(inverseRelation(r))
  ) {
    have(relation(r) |- relation(inverseRelation(r))) by Cut(inverseRelationBetweenRangeAndDomain, relationBetweenIsRelation of (r := inverseRelation(r), a := ran(r), b := dom(r)))
    val forward = thenHave(relation(r) ==> relation(inverseRelation(r))) by RightImplies
    val backward = have(relation(inverseRelation(r)) ==> relation(r)) by Substitution.ApplyRules(inverseInverseRelation)(forward of (r := inverseRelation(r)))
    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Relation Restriction
   */

  val relationRestrictionUniqueness = Lemma(∃!(z, ∀(p, p ∈ z <=> (p ∈ r /\ p ∈ (x × y))))) {
    have(thesis) by UniqueComprehension(r, lambda(p, p ∈ r /\ p ∈ (x × y)))
  }

  val relationRestriction = DEF(r, x, y) --> The(z, ∀(p, p ∈ z <=> (p ∈ r /\ p ∈ (x × y))))(relationRestrictionUniqueness)

  val relationRestrictionElem = Lemma(
    p ∈ relationRestriction(r, x, y) <=> (p ∈ r /\ p ∈ (x × y))
  ) {
    have(∀(p, p ∈ relationRestriction(r, x, y) <=> (p ∈ r /\ p ∈ (x × y)))) by InstantiateForall(relationRestriction(r, x, y))(relationRestriction.definition)
    thenHave(thesis) by InstantiateForall(p)
  }

  val relationRestrictionElemPair = Lemma(
    pair(a, b) ∈ relationRestriction(r, x, y) <=> (pair(a, b) ∈ r /\ a ∈ x /\ b ∈ y)
  ) {
    have(pair(a, b) ∈ (x × y) <=> a ∈ x /\ b ∈ y |- pair(a, b) ∈ relationRestriction(r, x, y) <=> (pair(a, b) ∈ r /\ a ∈ x /\ b ∈ y)) by RightSubstIff
      .withParametersSimple(List((pair(a, b) ∈ (x × y), a ∈ x /\ b ∈ y)), lambda(h, pair(a, b) ∈ relationRestriction(r, x, y) <=> (pair(a, b) ∈ r /\ h)))(
        relationRestrictionElem of (p := pair(a, b))
      )
    have(thesis) by Cut(cartesianProductMembershipPair, lastStep)
  }

  val relationRestrictionIntroPair = Lemma(
    (pair(a, b) ∈ r, a ∈ x, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, x, y)
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionIntro = Lemma(
    (relation(r), p ∈ r, fst(p) ∈ x, snd(p) ∈ y) |- p ∈ relationRestriction(r, x, y)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationRestrictionIntroPair of (a := fst(p), b := snd(p)))
  }

  val relationRestrictionPairInRestrictedDomains = Lemma(
    pair(a, b) ∈ relationRestriction(r, x, y) |- a ∈ x /\ b ∈ y
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionInRestrictedDomains = Lemma(
    p ∈ relationRestriction(r, x, y) |- fst(p) ∈ x /\ snd(p) ∈ y
  ) {
    have(p ∈ relationRestriction(r, x, y) |- p ∈ (x × y)) by Weakening(relationRestrictionElem)
    have(thesis) by Cut(lastStep, cartesianProductElim)
  }

  val relationRestrictionPairInRelation = Lemma(
    p ∈ relationRestriction(r, x, y) |- p ∈ r
  ) {
    have(thesis) by Weakening(relationRestrictionElem)
  }

  val relationRestrictionLeftEmpty = Lemma(
    relationRestriction(r, ∅, y) === ∅
  ) {
    have(fst(p) ∉ ∅ |- p ∉ relationRestriction(r, ∅, y)) by Weakening(relationRestrictionInRestrictedDomains of (x := ∅))
    have(p ∉ relationRestriction(r, ∅, y)) by Cut(emptySetAxiom of (x := fst(p)), lastStep)
    thenHave(∀(p, p ∉ relationRestriction(r, ∅, y))) by RightForall
    have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty of (x := relationRestriction(r, ∅, y)))
  }

  val relationRestrictionRightEmpty = Lemma(
    relationRestriction(r, x, ∅) === ∅
  ) {
    have(snd(p) ∉ ∅ |- p ∉ relationRestriction(r, x, ∅)) by Weakening(relationRestrictionInRestrictedDomains of (y := ∅))
    have(p ∉ relationRestriction(r, x, ∅)) by Cut(emptySetAxiom of (x := snd(p)), lastStep)
    thenHave(∀(p, p ∉ relationRestriction(r, x, ∅))) by RightForall
    have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty of (x := relationRestriction(r, x, ∅)))
  }

  val relationRestrictionEmptyDomains = Lemma(
    relationRestriction(r, ∅, ∅) === ∅
  ) {
    have(thesis) by Restate.from(relationRestrictionRightEmpty of (x := ∅))
  }

  val relationRestrictionEmpty = Lemma(
    relationRestriction(∅, x, y) === ∅
  ) {
    have(p ∉ ∅ |- p ∉ relationRestriction(∅, x, y)) by Weakening(relationRestrictionPairInRelation of (r := ∅))
    have(p ∉ relationRestriction(∅, x, y)) by Cut(emptySetAxiom of (x := p), lastStep)
    thenHave(∀(p, p ∉ relationRestriction(∅, x, y))) by RightForall
    have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty of (x := relationRestriction(∅, x, y)))
  }

  val relationRestrictionSubset = Lemma(
    relationRestriction(r, x, y) ⊆ r
  ) {
    have(∀(p, p ∈ relationRestriction(r, x, y) <=> (p ∈ r /\ p ∈ (x × y)))) by InstantiateForall(relationRestriction(r, x, y))(relationRestriction.definition)
    thenHave(p ∈ relationRestriction(r, x, y) <=> (p ∈ r /\ p ∈ (x × y))) by InstantiateForall(p)
    thenHave(p ∈ relationRestriction(r, x, y) ==> p ∈ r) by Weakening
    thenHave(∀(p, p ∈ relationRestriction(r, x, y) ==> p ∈ r)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRestriction(r, x, y), y := r))
  }

  val relationRestrictionInRelation = Lemma(
    p ∈ relationRestriction(r, x, y) |- p ∈ r
  ) {
    have(thesis) by Cut(relationRestrictionSubset, subsetElim of (z := p, x := relationRestriction(r, x, y), y := r))
  }

  val relationRestrictionDomain = Lemma(
    dom(relationRestriction(r, x, y)) ⊆ (dom(r) ∩ x)
  ) {
    have(pair(a, b) ∈ relationRestriction(r, x, y) |- a ∈ x) by Weakening(relationRestrictionPairInRestrictedDomains)
    have((pair(a, b) ∈ relationRestriction(r, x, y), a ∈ dom(r)) |- a ∈ (dom(r) ∩ x)) by Cut(
      lastStep,
      setIntersectionIntro of (z := a, x := dom(r), y := x)
    )
    have((pair(a, b) ∈ relationRestriction(r, x, y), pair(a, b) ∈ r) |- a ∈ (dom(r) ∩ x)) by Cut(relationDomainIntroPair, lastStep)
    have(pair(a, b) ∈ relationRestriction(r, x, y) |- a ∈ (dom(r) ∩ x)) by Cut(relationRestrictionPairInRelation of (p := pair(a, b)), lastStep)
    thenHave(∃(b, pair(a, b) ∈ relationRestriction(r, x, y)) |- a ∈ (dom(r) ∩ x)) by LeftExists
    have(a ∈ dom(relationRestriction(r, x, y)) |- a ∈ (dom(r) ∩ x)) by Cut(relationDomainElim of (r := relationRestriction(r, x, y)), lastStep)
    thenHave(a ∈ dom(relationRestriction(r, x, y)) ==> a ∈ (dom(r) ∩ x)) by RightImplies
    thenHave(∀(a, a ∈ dom(relationRestriction(r, x, y)) ==> a ∈ (dom(r) ∩ x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := dom(relationRestriction(r, x, y)), y := dom(r) ∩ x))
  }

  val relationRestrictionRange = Lemma(
    ran(relationRestriction(r, x, y)) ⊆ (ran(r) ∩ y)
  ) {
    have(pair(a, b) ∈ relationRestriction(r, x, y) |- b ∈ y) by Weakening(relationRestrictionPairInRestrictedDomains)
    have((pair(a, b) ∈ relationRestriction(r, x, y), b ∈ ran(r)) |- b ∈ (ran(r) ∩ y)) by Cut(
      lastStep,
      setIntersectionIntro of (z := b, x := ran(r))
    )
    have((pair(a, b) ∈ relationRestriction(r, x, y), pair(a, b) ∈ r) |- b ∈ (ran(r) ∩ y)) by Cut(relationRangeIntroPair, lastStep)
    have(pair(a, b) ∈ relationRestriction(r, x, y) |- b ∈ (ran(r) ∩ y)) by Cut(relationRestrictionPairInRelation of (p := pair(a, b)), lastStep)
    thenHave(∃(a, pair(a, b) ∈ relationRestriction(r, x, y)) |- b ∈ (ran(r) ∩ y)) by LeftExists
    have(b ∈ ran(relationRestriction(r, x, y)) |- b ∈ (ran(r) ∩ y)) by Cut(relationRangeElim of (r := relationRestriction(r, x, y)), lastStep)
    thenHave(b ∈ ran(relationRestriction(r, x, y)) ==> b ∈ (ran(r) ∩ y)) by RightImplies
    thenHave(∀(b, b ∈ ran(relationRestriction(r, x, y)) ==> b ∈ (ran(r) ∩ y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := ran(relationRestriction(r, x, y)), y := ran(r) ∩ y))
  }

  val relationRestrictionOnItself = Lemma(
    relationBetween(r, x, y) |- relationRestriction(r, x, y) === r
  ) {
    (relationBetween(r, a, b), p ∈ r) |- fst(p) ∈ a /\ snd(p) ∈ b
    have((relation(r), p ∈ r, fst(p) ∈ x /\ snd(p) ∈ y) |- p ∈ relationRestriction(r, x, y)) by LeftAnd(relationRestrictionIntro)
    have((relation(r), p ∈ r, relationBetween(r, x, y)) |- p ∈ relationRestriction(r, x, y)) by Cut(relationBetweenElim of (a := x, b := y), lastStep)
    have((relationBetween(r, x, y), p ∈ r) |- p ∈ relationRestriction(r, x, y)) by Cut(relationBetweenIsRelation of (a := x, b := y), lastStep)
    thenHave(relationBetween(r, x, y) |- p ∈ r ==> p ∈ relationRestriction(r, x, y)) by RightImplies
    thenHave(relationBetween(r, x, y) |- ∀(p, p ∈ r ==> p ∈ relationRestriction(r, x, y))) by RightForall
    have(relationBetween(r, x, y) |- r ⊆ relationRestriction(r, x, y)) by
      Cut(lastStep, subsetIntro of (x := r, y := relationRestriction(r, x, y)))
    have((relationBetween(r, x, y), relationRestriction(r, x, y) ⊆ r) |- relationRestriction(r, x, y) === r) by
      Cut(lastStep, subsetAntisymmetry of (x := relationRestriction(r, x, y), y := r))
    have(thesis) by
      Cut(relationRestrictionSubset, lastStep)
  }

  val relationRestrictionOnDomainRange = Lemma(
    relation(r) |- relationRestriction(r, dom(r), ran(r)) === r
  ) {
    have(thesis) by Cut(relationIsRelationBetween, relationRestrictionOnItself of (x := dom(r), y := ran(r)))
  }

  val relationRestrictionIsRelationBetweenRestrictedDomains = Lemma(
    relationBetween(relationRestriction(r, x, y), x, y)
  ) {
    have(p ∈ relationRestriction(r, x, y) |- p ∈ (x × y)) by Weakening(relationRestrictionElem)
    thenHave(p ∈ relationRestriction(r, x, y) ==> p ∈ (x × y)) by RightImplies
    thenHave(∀(p, p ∈ relationRestriction(r, x, y) ==> p ∈ (x × y))) by RightForall
    have(relationRestriction(r, x, y) ⊆ (x × y)) by Cut(lastStep, subsetIntro of (x := relationRestriction(r, x, y), y := x × y))
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

  val relationRestrictionSupersetRange = Lemma(
    (relation(r), ran(r) ⊆ y) |- relationRestriction(r, x, y) === relationRestriction(r, x, ran(r))
  ) {
    val forward = have(relation(r) |- p ∈ relationRestriction(r, x, y) ==> p ∈ relationRestriction(r, x, ran(r))) subproof {
      have((relation(r), p ∈ r, fst(p) ∈ x) |- p ∈ relationRestriction(r, x, ran(r))) by Cut(relationRangeIntro, relationRestrictionIntro of (y := ran(r)))
      have((relation(r), p ∈ relationRestriction(r, x, y), fst(p) ∈ x) |- p ∈ relationRestriction(r, x, ran(r))) by Cut(relationRestrictionInRelation, lastStep)
      thenHave((relation(r), p ∈ relationRestriction(r, x, y), fst(p) ∈ x /\ snd(p) ∈ y) |- p ∈ relationRestriction(r, x, ran(r))) by LeftAnd
      have((relation(r), p ∈ relationRestriction(r, x, y)) |- p ∈ relationRestriction(r, x, ran(r))) by Cut(relationRestrictionInRestrictedDomains, lastStep)
    }
    val backward = have((relation(r), ran(r) ⊆ y) |- p ∈ relationRestriction(r, x, ran(r)) ==> p ∈ relationRestriction(r, x, y)) subproof {
      have((relation(r), ran(r) ⊆ y, p ∈ r, fst(p) ∈ x, snd(p) ∈ ran(r)) |- p ∈ relationRestriction(r, x, y)) by Cut(subsetElim of (z := snd(p), x := ran(r)), relationRestrictionIntro)
      have((relation(r), ran(r) ⊆ y, p ∈ relationRestriction(r, x, ran(r)), fst(p) ∈ x, snd(p) ∈ ran(r)) |- p ∈ relationRestriction(r, x, y)) by Cut(relationRestrictionInRelation of (y := ran(r)), lastStep)
      thenHave((relation(r), ran(r) ⊆ y, p ∈ relationRestriction(r, x, ran(r)), fst(p) ∈ x /\ snd(p) ∈ ran(r)) |- p ∈ relationRestriction(r, x, y)) by LeftAnd
      have((relation(r), ran(r) ⊆ y, p ∈ relationRestriction(r, x, ran(r))) |- p ∈ relationRestriction(r, x, y)) by Cut(relationRestrictionInRestrictedDomains of (y := ran(r)), lastStep)
    }
    have((relation(r), ran(r) ⊆ y) |- p ∈ relationRestriction(r, x, y) <=> p ∈ relationRestriction(r, x, ran(r))) by
      RightIff(forward, backward)
    thenHave((relation(r), ran(r) ⊆ y) |- ∀(p, p ∈ relationRestriction(r, x, y) <=> p ∈ relationRestriction(r, x, ran(r)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, x, y), y := relationRestriction(r, x, ran(r))))
  }

  val relationRestrictionSupersetDomain = Lemma(
    (relation(r), dom(r) ⊆ x) |- relationRestriction(r, x, y) === relationRestriction(r, dom(r), y)
  ) {
    val forward = have(relation(r) |- p ∈ relationRestriction(r, x, y) ==> p ∈ relationRestriction(r, dom(r), y)) subproof {
      have((relation(r), p ∈ r, snd(p) ∈ y) |- p ∈ relationRestriction(r, dom(r), y)) by Cut(relationDomainIntro, relationRestrictionIntro of (x := dom(r)))
      have((relation(r), p ∈ relationRestriction(r, x, y), snd(p) ∈ y) |- p ∈ relationRestriction(r, dom(r), y)) by Cut(relationRestrictionInRelation, lastStep)
      thenHave((relation(r), p ∈ relationRestriction(r, x, y), fst(p) ∈ x /\ snd(p) ∈ y) |- p ∈ relationRestriction(r, dom(r), y)) by LeftAnd
      have((relation(r), p ∈ relationRestriction(r, x, y)) |- p ∈ relationRestriction(r, dom(r), y)) by Cut(relationRestrictionInRestrictedDomains, lastStep)
    }
    val backward = have((relation(r), dom(r) ⊆ x) |- p ∈ relationRestriction(r, dom(r), y) ==> p ∈ relationRestriction(r, x, y)) subproof {
      have((relation(r), dom(r) ⊆ x, p ∈ r, fst(p) ∈ dom(r), snd(p) ∈ y) |- p ∈ relationRestriction(r, x, y)) by Cut(subsetElim of (z := fst(p), x := dom(r), y := x), relationRestrictionIntro)
      have((relation(r), dom(r) ⊆ x, p ∈ relationRestriction(r, dom(r), y), fst(p) ∈ dom(r), snd(p) ∈ y) |- p ∈ relationRestriction(r, x, y)) by Cut(relationRestrictionInRelation of (x := dom(r)), lastStep)
      thenHave((relation(r), dom(r) ⊆ x, p ∈ relationRestriction(r, dom(r), y), fst(p) ∈ dom(r) /\ snd(p) ∈ y) |- p ∈ relationRestriction(r, x, y)) by LeftAnd
      have((relation(r), dom(r) ⊆ x, p ∈ relationRestriction(r, dom(r), y)) |- p ∈ relationRestriction(r, x, y)) by Cut(relationRestrictionInRestrictedDomains of (x := dom(r)), lastStep)
    }
    have((relation(r), dom(r) ⊆ x) |- p ∈ relationRestriction(r, x, y) <=> p ∈ relationRestriction(r, dom(r), y)) by
      RightIff(forward, backward)
    thenHave((relation(r), dom(r) ⊆ x) |- ∀(p, p ∈ relationRestriction(r, x, y) <=> p ∈ relationRestriction(r, dom(r), y))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, x, y), y := relationRestriction(r, dom(r), y)))
  }

  val relationRestrictionSetUnion = Lemma(
    relationRestriction(r1 ∪ r2, x, y) === relationRestriction(r1, x, y) ∪ relationRestriction(r2, x, y)
  ) {
    have(p ∈ relationRestriction((r1 ∪ r2), x, y) <=> ((p ∈ r1 \/ (p ∈ r2)) /\ p ∈ (x × y))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := r1, y := r2))(relationRestrictionElem of (r := r1 ∪ r2))
    thenHave(p ∈ relationRestriction((r1 ∪ r2), x, y) <=> ((p ∈ r1 /\ p ∈ (x × y)) \/ (p ∈ r2 /\ p ∈ (x × y)))) by Tautology
    thenHave(p ∈ relationRestriction((r1 ∪ r2), x, y) <=> (p ∈ relationRestriction(r1, x, y) \/ (p ∈ relationRestriction(r2, x, y)))) by
      Substitution.ApplyRules(relationRestrictionElem of (r := r1), relationRestrictionElem of (r := r2))
    thenHave(p ∈ relationRestriction((r1 ∪ r2), x, y) <=> p ∈ 
    (relationRestriction(r1, x, y) ∪ relationRestriction(r2, x, y))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := relationRestriction(r1, x, y), y := relationRestriction(r2, x, y)))
    thenHave(∀(p, p ∈ relationRestriction((r1 ∪ r2), x, y) <=> p ∈ (relationRestriction(r1, x, y) ∪ relationRestriction(r2, x, y)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction((r1 ∪ r2), x, y), y := relationRestriction(r1, x, y) ∪ relationRestriction(r2, x, y)))
  }

  val relationRestrictionSetUnionDomain = Lemma(
    relationRestriction(r, x ∪ y, z) === relationRestriction(r, x, z) ∪ relationRestriction(r, y, z)
  ) {
    have(p ∈ relationRestriction(r, x ∪ y, z) <=> (p ∈ r /\ p ∈ ((x × z) ∪ (y × z)))) by
      Substitution.ApplyRules(cartesianProductLeftUnion)(relationRestrictionElem of (x := x ∪ y, y := z))
    thenHave(p ∈ relationRestriction(r, x ∪ y, z) <=> (p ∈ r /\ (p ∈ (x × z) \/ (p ∈ (y × z))))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := x × z, y := y × z))
    thenHave(p ∈ relationRestriction(r, x ∪ y, z) <=> (p ∈ r /\ p ∈ (x × z)) \/ (p ∈ r /\ p ∈ (y × z))) by Tautology
    thenHave(p ∈ relationRestriction(r, x ∪ y, z) <=> (p ∈ relationRestriction(r, x, z)) \/ (p ∈ relationRestriction(r, y, z))) by
      Substitution.ApplyRules(relationRestrictionElem of (y := z), relationRestrictionElem of (x := y, y := z))
    thenHave(p ∈ relationRestriction(r, x ∪ y, z) <=> p ∈ (relationRestriction(r, x, z) ∪ relationRestriction(r, y, z))) by
      Substitution.ApplyRules(setUnionMembership of (z := p, x := relationRestriction(r, x, z), y := relationRestriction(r, y, z)))
    thenHave(∀(p, p ∈ relationRestriction(r, x ∪ y, z) <=> p ∈ (relationRestriction(r, x, z) ∪ relationRestriction(r, y, z)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, x ∪ y, z), y := relationRestriction(r, x, z) ∪ relationRestriction(r, y, z)))
  }

  val relationRestrictionSubsetDomains = Lemma(
    (relation(r), w ⊆ y, x ⊆ z) |- relationRestriction(r, w, x) ⊆ relationRestriction(r, y, z)
  ) {
    have((relation(r), p ∈ relationRestriction(r, w, x), fst(p) ∈ y, snd(p) ∈ z) |- p ∈ relationRestriction(r, y, z)) by Cut(relationRestrictionInRelation of (x := w, y := x), relationRestrictionIntro of (x := y, y := z))
    have((relation(r), w ⊆ y, p ∈ relationRestriction(r, w, x), fst(p) ∈ w, snd(p) ∈ z) |- p ∈ relationRestriction(r, y, z)) by Cut(subsetElim of (z := fst(p), x := w, y := y), lastStep)
    have((relation(r), w ⊆ y, x ⊆ z, p ∈ relationRestriction(r, w, x), fst(p) ∈ w, snd(p) ∈ x) |- p ∈ relationRestriction(r, y, z)) by Cut(subsetElim of (z := snd(p), x := x, y := z), lastStep)
    thenHave((relation(r), w ⊆ y, x ⊆ z, p ∈ relationRestriction(r, w, x), fst(p) ∈ w /\ snd(p) ∈ x) |- p ∈ relationRestriction(r, y, z)) by LeftAnd
    have((relation(r), w ⊆ y, x ⊆ z, p ∈ relationRestriction(r, w, x)) |- p ∈ relationRestriction(r, y, z)) by Cut(relationRestrictionInRestrictedDomains of (x := w, y := x), lastStep)
    thenHave((relation(r), w ⊆ y, x ⊆ z) |- p ∈ relationRestriction(r, w, x) ==> p ∈ relationRestriction(r, y, z)) by RightImplies
    thenHave((relation(r), w ⊆ y, x ⊆ z) |- ∀(p, p ∈ relationRestriction(r, w, x) ==> p ∈ relationRestriction(r, y, z))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRestriction(r, w, x), y := relationRestriction(r, y, z)))
  }

  val relationRestrictionTwice = Lemma(
    relation(r) |- relationRestriction(relationRestriction(r, w, x), y, z) === relationRestriction(r, w ∩ y, x ∩ z)
  ) {
    val forward = have(relation(r) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z) ==> p ∈ relationRestriction(r, w ∩ y, x ∩ z)) subproof {
      have((relation(r), p ∈ r, fst(p) ∈ w, fst(p) ∈ y, snd(p) ∈ (x ∩ z)) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(setIntersectionIntro of (z := fst(p), x := w), relationRestrictionIntro of (x := w ∩ y, y := x ∩ z))
      have((relation(r), p ∈ r, fst(p) ∈ w, fst(p) ∈ y, snd(p) ∈ x, snd(p) ∈ z) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(setIntersectionIntro of (z := snd(p), y := z), lastStep)
      thenHave((relation(r), p ∈ r, fst(p) ∈ w /\ snd(p) ∈ x, fst(p) ∈ y /\ snd(p) ∈ z) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Restate
      have((relation(r), p ∈ r, p ∈ relationRestriction(r, w, x), fst(p) ∈ y /\ snd(p) ∈ z) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(relationRestrictionInRestrictedDomains of (x := w, y := x), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w, x), fst(p) ∈ y /\ snd(p) ∈ z) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(relationRestrictionInRelation of (x := w, y := x), lastStep)
      have((relation(r), p ∈ relationRestriction(relationRestriction(r, w, x), y, z), p ∈ relationRestriction(r, w, x)) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(relationRestrictionInRestrictedDomains of (r := relationRestriction(r, w, x), x := y, y := z), lastStep)
      have((relation(r), p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by Cut(relationRestrictionInRelation of (r := relationRestriction(r, w, x), x := y, y := z), lastStep)
    }
    val backward = have(relation(r) |- p ∈ relationRestriction(r, w ∩ y, x ∩ z) ==> p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) subproof {
      have((p ∈ relationRestriction(r, w, x), fst(p) ∈ y, snd(p) ∈ z) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(relationRestrictionIsRelation of (x := w, y := x), relationRestrictionIntro of (r := relationRestriction(r, w, x), x := y, y := z))
      thenHave((p ∈ relationRestriction(r, w, x), fst(p) ∈ y /\ snd(p) ∈ z) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by LeftAnd
      have((p ∈ relationRestriction(r, w, x), p ∈ relationRestriction(r, y, z)) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(relationRestrictionInRestrictedDomains of (x := y, y := z), lastStep)
      have((p ∈ relationRestriction(r, w ∩ y, x ∩ z), p ∈ relationRestriction(r, y, z), relationRestriction(r, w ∩ y, x ∩ z) ⊆ relationRestriction(r, w, x)) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(subsetElim of (z := p, x := relationRestriction(r, w ∩ y, x ∩ z), y := relationRestriction(r, w, x)), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), p ∈ relationRestriction(r, y, z), x ∩ z ⊆ x, w ∩ y ⊆ w) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(relationRestrictionSubsetDomains of (w := w ∩ y, y := w, x := x ∩ z, z := x), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), p ∈ relationRestriction(r, y, z), w ∩ y ⊆ w) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(setIntersectionLeftSubset of (y := z), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), p ∈ relationRestriction(r, y, z)) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(setIntersectionLeftSubset of (x := w), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), relationRestriction(r, w ∩ y, x ∩ z) ⊆ relationRestriction(r, y, z)) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(subsetElim of (z := p, x := relationRestriction(r, w ∩ y, x ∩ z), y := relationRestriction(r, y, z)), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), w ∩ y ⊆ y, x ∩ z ⊆ z) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(relationRestrictionSubsetDomains of (w := w ∩ y, x := x ∩ z), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z), x ∩ z ⊆ z) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(setIntersectionRightSubset of (x := w), lastStep)
      have((relation(r), p ∈ relationRestriction(r, w ∩ y, x ∩ z)) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z)) by Cut(setIntersectionRightSubset of (y := z), lastStep)
    }
    have(relation(r) |- p ∈ relationRestriction(relationRestriction(r, w, x), y, z) <=> p ∈ relationRestriction(r, w ∩ y, x ∩ z)) by RightIff(forward, backward)
    thenHave(relation(r) |- ∀(p, p ∈ relationRestriction(relationRestriction(r, w, x), y, z) <=> p ∈ relationRestriction(r, w ∩ y, x ∩ z))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(relationRestriction(r, w, x), y, z), y := relationRestriction(r, w ∩ y, x ∩ z)))
  }

  val relationRestrictionTwiceSubsetInner = Lemma(
    (relation(r), w ⊆ y, x ⊆ z) |- relationRestriction(relationRestriction(r, w, x), y, z) === relationRestriction(r, w, x)
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionOfSubsetForward)(relationRestrictionTwice)
  }

  val relationRestrictionTwiceSubsetOuter = Lemma(
    (relation(r), y ⊆ w, z ⊆ x) |- relationRestriction(relationRestriction(r, w, x), y, z) === relationRestriction(r, y, z)
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionOfSubsetBackward)(relationRestrictionTwice)
  }

  val relationRestrictionIdempotence = Lemma(
    relation(r) |- relationRestriction(relationRestriction(r, x, y), x, y) === relationRestriction(r, x, y)
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionIdempotence)(relationRestrictionTwice of (w := x, x := y, y := x, z := y))
  }

  val domainRestriction = DEF(f, x) --> relationRestriction(f, x, ran(f))

  extension (f: Term) 
    def ↾ (x: Term) = domainRestriction(f, x)

  val domainRestrictionIntro = Lemma(
    (pair(a, b) ∈ f, a ∈ x) |- pair(a, b) ∈ (f ↾ x)
  ) {
    have((pair(a, b) ∈ f, a ∈ x, b ∈ ran(f)) |- pair(a, b) ∈ (f ↾ x)) by Substitution.ApplyRules(domainRestriction.shortDefinition)(
      relationRestrictionIntroPair of (r := f, y := ran(f))
    )
    have(thesis) by Cut(relationRangeIntroPair of (r := f), lastStep)
  }

  val domainRestrictionPairInRelation = Lemma(
    (pair(a, b) ∈ (f ↾ x)) |- pair(a, b) ∈ f
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionPairInRelation of (r := f, y := ran(f), p := pair(a, b)))
  }

  val domainRestrictionEmpty = Lemma(
    f ↾ ∅ === ∅
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionLeftEmpty of (r := f, y := ran(f)))
  }

  val domainRestrictionSubset = Lemma(
    (f ↾ x) ⊆ f
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionSubset of (r := f, y := ran(f)))
  }

  val domainRestrictionIsRelation = Lemma(
    relation(f ↾ x)
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionIsRelation of (r := f, x := x, y := ran(f)))
  }

  /**
    * Lemma --- Domain of domain restriction of a relation
    * 
    *    `Dom(f|x) = Dom(f) ∩ x`
    */
  val domainRestrictionDomain = Lemma(
    dom(f ↾ x) === dom(f) ∩ x
  ) {
    val forward = have(dom(f ↾ x) ⊆ (dom(f) ∩ x)) by Substitution.ApplyRules(domainRestriction.shortDefinition)(
      relationRestrictionDomain of (r := f, y := ran(f))
    )
    val backward = have((dom(f) ∩ x) ⊆ dom(f ↾ x)) subproof {
      have((pair(a, b) ∈ f, a ∈ x) |- a ∈ dom(f ↾ x)) by Cut(domainRestrictionIntro, relationDomainIntroPair of (r := f ↾ x))
      thenHave((∃(b, pair(a, b) ∈ f), a ∈ x) |- a ∈ dom(f ↾ x)) by LeftExists
      have((a ∈ dom(f), a ∈ x) |- a ∈ dom(f ↾ x)) by Cut(relationDomainElim of (r := f), lastStep)
      thenHave(a ∈ dom(f) /\ a ∈ x |- a ∈ dom(f ↾ x)) by LeftAnd
      have(a ∈ (dom(f) ∩ x) |- a ∈ dom(f ↾ x)) by Cut(setIntersectionElim of (z := a, x := dom(f), y := x), lastStep)
      thenHave(a ∈ (dom(f) ∩ x) ==> a ∈ dom(f ↾ x)) by RightImplies
      thenHave(∀(a, a ∈ (dom(f) ∩ x) ==> a ∈ dom(f ↾ x))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := dom(f) ∩ x, y := dom(f ↾ x)))
    }
    have((dom(f) ∩ x) ⊆ dom(f ↾ x) |- dom(f ↾ x) === dom(f) ∩ x) by 
      Cut(forward, subsetAntisymmetry of (x := dom(f ↾ x), y := dom(f) ∩ x))
    have(thesis) by Cut(backward, lastStep)
  }

  val domainRestrictionRange = Lemma(
    ran(f ↾ x) ⊆ ran(f)
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition , setIntersectionIdempotence)(relationRestrictionRange of (r := f, y := ran(f)))
  }

  val domainRestrictionRelationFrom = Lemma(
    relationFrom(f ↾ x, dom(f) ∩ x)
  ) {
    have(relationFrom(f ↾ x, dom(f ↾ x))) by Cut (domainRestrictionIsRelation, relationIsRelationFrom of (r := f ↾ x))
    thenHave(thesis) by Substitution.ApplyRules(domainRestrictionDomain)
  }

  val domainRestrictionRelationBetween = Lemma(
    relationBetween(f, x, y) |- relationBetween(f ↾ z, x ∩ z, y)
  ) {
    have(relationBetween(f ↾ z, dom(f) ∩ z, ran(f ↾ z))) by Cut(domainRestrictionRelationFrom of (x := z), relationFromToRange of (r := f ↾ z, a := dom(f) ∩ z))
    have(((dom(f) ∩ z) ⊆ (x ∩ z), ran(f ↾ z) ⊆ ran(f)) |-  relationBetween(f ↾ z, x ∩ z, ran(f))) by Cut(lastStep, relationBetweenSubsetDomains of (r := f ↾ z, a := dom(f) ∩ z, b := ran(f ↾ z), c := x ∩ z, d := ran(f)))
    have((dom(f) ∩ z) ⊆ (x ∩ z) |- relationBetween(f ↾ z, x ∩ z, ran(f))) by Cut(domainRestrictionRange of (x := z), lastStep)
    have(dom(f) ⊆ x |- relationBetween(f ↾ z, x ∩ z, ran(f))) by Cut(setIntersectionLeftMonotonicity of (x := dom(f), y := x), lastStep)
    have(relationBetween(f, x, y) |- relationBetween(f ↾ z, x ∩ z, ran(f))) by Cut(relationBetweenDomain of (r := f, a := x, b := y), lastStep)
    have((relationBetween(f, x, y), ran(f) ⊆ y) |- relationBetween(f ↾ z, x ∩ z, y)) by Cut(lastStep, relationBetweenSubsetRightDomain of (r := f ↾ z, a := x ∩ z, b := ran(f), d := y))
    have(thesis) by Cut(relationBetweenRange of (r := f, a := x, b := y), lastStep)
  }

  val domainRestrictionOnDomain = Lemma(
    relation(f) |- f ↾ dom(f) === f
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionOnDomainRange of (r := f))
  }

  val domainRestrictionDisjoint = Lemma(
    disjoint(dom(f), x) |- f ↾ x === ∅
  ) {
    have(disjoint(dom(f), x) |- dom(f ↾ x) === ∅) by 
      Substitution.ApplyRules(disjointUnfold of (x := dom(f), y := x))(domainRestrictionDomain)
    have((relation(f ↾ x), disjoint(dom(f), x)) |- f ↾ x === ∅) by Cut(lastStep, relationDomainEmpty of (r := f ↾ x))
    have(thesis) by Cut(domainRestrictionIsRelation of (r := f), lastStep)
  }

  val domainRestrictionSetUnion = Lemma(
    (relation(f), relation(g)) |- f ∪ g ↾ x === (f ↾ x) ∪ (g ↾ x)
  ) {
    have(f ∪ g ↾ x === relationRestriction(f, x, ran(f ∪ g)) ∪ relationRestriction(g, x, ran(f ∪ g))) by
      Substitution.ApplyRules(domainRestriction.shortDefinition of (f := f ∪ g))(relationRestrictionSetUnion of (r1 := f, r2 := g, y := ran(f ∪ g)))
    thenHave(
      (relation(f), ran(f) ⊆ ran(f ∪ g)) |-
        f ∪ g ↾ x === relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(f ∪ g))
    ) by
      Substitution.ApplyRules(relationRestrictionSupersetRange of (r := f, y := ran(f ∪ g)))
    have(
      (relation(f), f ⊆ (f ∪ g)) |- f ∪ g ↾ x === 
        relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(f ∪ g))
    ) by
      Cut(relationRangeSubset of (r1 := f, r2 := f ∪ g), lastStep)
    have(relation(f) |- f ∪ g ↾ x === relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(f ∪ g))) by
      Cut(setUnionLeftSubset of (a := f, b := g), lastStep)
    thenHave(
      (relation(f), relation(g), ran(g) ⊆ ran(f ∪ g)) |-
        f ∪ g ↾ x === relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(g))
    ) by
      Substitution.ApplyRules(relationRestrictionSupersetRange of (r := g, y := ran(f ∪ g)))
    have(
      (relation(f), relation(g), g ⊆ (f ∪ g)) |- f ∪ g ↾ x === 
        relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(g))
    ) by
      Cut(relationRangeSubset of (r1 := g, r2 := f ∪ g), lastStep)
    have((relation(f), relation(g)) |- (f ∪ g) ↾ x === relationRestriction(f, x, ran(f)) ∪ relationRestriction(g, x, ran(g))) by
      Cut(setUnionRightSubset of (a := f, b := g), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)
  }

  val domainRestrictionSetUnionDomain = Lemma(
    f ↾ (x ∪ y) === (f ↾ x) ∪ (f ↾ y)
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(
      relationRestrictionSetUnionDomain of (r := f, z := ran(f))
    )
  }

  val domainRestrictionSubsetDomain = Lemma(
    (relation(f), x ⊆ y) |- (f ↾ x) ⊆ (f ↾ y)
  ) {
    have((relation(f), x ⊆ y, ran(f) ⊆ ran(f)) |- (f ↾ x) ⊆ (f ↾ y)) by 
      Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionSubsetDomains of (x := ran(f), z := ran(f), w := x, r := f))
    have(thesis) by Cut(subsetReflexivity of (x := ran(f)), lastStep)
  }

  val domainRestrictionRestrictionRange = Lemma(
    (relation(f), ran(f ↾ x) ⊆ y, y ⊆ ran(f)) |- relationRestriction(f, x, y) === f ↾ x
  ) {
    val forward = have((relation(f), y ⊆ ran(f)) |- p ∈ relationRestriction(f, x, y) ==> p ∈ relationRestriction(f, x, ran(f))) subproof {
      have((relation(f), y ⊆ ran(f)) |- relationRestriction(f, x, y) ⊆ relationRestriction(f, x, ran(f))) by Cut(subsetReflexivity, relationRestrictionSubsetDomains of (r := f, w := x, x := y, y := x, z := ran(f)))
      have((relation(f), y ⊆ ran(f), p ∈ relationRestriction(f, x, y)) |- p ∈ relationRestriction(f, x, ran(f))) by Cut(lastStep, subsetElim of (z := p, x := relationRestriction(f, x, y), y := relationRestriction(f, x, ran(f)))) 
    }
    
    val backward = have((relation(f), ran(f ↾ x) ⊆ y) |- p ∈ relationRestriction(f, x, ran(f)) ==> p ∈ relationRestriction(f, x, y)) subproof {
      have((relation(f), p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x, snd(p) ∈ y) |- p ∈ relationRestriction(f, x, y)) by Cut(relationRestrictionInRelation of (r := f, y := ran(f)), relationRestrictionIntro of (r := f))
      have((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x, snd(p) ∈ ran(f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by Cut(subsetElim of (z := snd(p), x := ran(f ↾ x)), lastStep)
      have((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x, pair(fst(p), snd(p)) ∈ (f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by Cut(relationRangeIntroPair of (a := fst(p), b := snd(p), r := f ↾ x), lastStep)
      thenHave((relation(f), ran(f ↾ x) ⊆ y, relation(f ↾ x), p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x, p ∈ (f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by Substitution.ApplyRules(pairReconstructionInRelation of (r := f ↾ x))
      have((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x, p ∈ (f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by Cut(domainRestrictionIsRelation, lastStep)
      thenHave((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f)), fst(p) ∈ x /\ snd(p) ∈ ran(f), p ∈ (f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by LeftAnd
      have((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f)), p ∈ (f ↾ x)) |- p ∈ relationRestriction(f, x, y)) by Cut(relationRestrictionInRestrictedDomains of (r := f, y := ran(f)), lastStep)
      thenHave((relation(f), ran(f ↾ x) ⊆ y, p ∈ relationRestriction(f, x, ran(f))) |- p ∈ relationRestriction(f, x, y)) by Substitution.ApplyRules(domainRestriction.shortDefinition)
    }
    
    have((relation(f), ran(f ↾ x) ⊆ y, y ⊆ ran(f)) |- p ∈ relationRestriction(f, x, y) <=> p ∈ relationRestriction(f, x, ran(f))) by RightIff(forward, backward)
    thenHave((relation(f), ran(f ↾ x) ⊆ y, y ⊆ ran(f)) |- p ∈ relationRestriction(f, x, y) <=> p ∈ (f ↾ x)) by Substitution.ApplyRules(domainRestriction.shortDefinition)
    thenHave((relation(f), ran(f ↾ x) ⊆ y, y ⊆ ran(f)) |- ∀(p, p ∈ relationRestriction(f, x, y) <=> p ∈ (f ↾ x))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(f, x, y), y := f ↾ x))  
  }

  val domainRestrictionTwice = Lemma(
    relation(f) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)
  ) {
    have((relation(f), ran(f ↾ x) ⊆ ran(f)) |- relationRestriction(relationRestriction(f, x, ran(f)), y, ran(f ↾ x)) === relationRestriction(f, x ∩ y, ran(f ↾ x))) by Substitution.ApplyRules(setIntersectionOfSubsetBackward of (x := ran(f), y := ran(f ↾ x)))(relationRestrictionTwice of (r := f, w := x, x := ran(f), z := ran(f ↾ x)))
    have(relation(f) |- relationRestriction(relationRestriction(f, x, ran(f)), y, ran(f ↾ x)) === relationRestriction(f, x ∩ y, ran(f ↾ x))) by Cut(domainRestrictionRange, lastStep)
    thenHave((relation(f), ran(f ↾ (x ∩ y)) ⊆ ran(f ↾ x), ran(f ↾ x) ⊆ ran(f)) |- relationRestriction(f ↾ x, y, ran(f ↾ x)) === f ↾ (x ∩ y)) by Substitution.ApplyRules(domainRestriction.shortDefinition, domainRestrictionRestrictionRange of (x := x ∩ y, y := ran(f ↾ x)))
    thenHave((relation(f), ran(f ↾ (x ∩ y)) ⊆ ran(f ↾ x), ran(f ↾ x) ⊆ ran(f)) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)) by Substitution.ApplyRules(domainRestriction.shortDefinition)
    have((relation(f), ran(f ↾ (x ∩ y)) ⊆ ran(f ↾ x)) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)) by Cut(domainRestrictionRange, lastStep)
    have((relation(f), (f ↾ (x ∩ y)) ⊆ (f ↾ x)) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)) by Cut(relationRangeSubset of (r1 := f ↾ (x ∩ y), r2 := f ↾ x), lastStep)
    have((relation(f), (x ∩ y) ⊆ x) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)) by Cut(domainRestrictionSubsetDomain of (x := x ∩ y, y := x), lastStep)
    have(relation(f) |- (f ↾ x) ↾ y === f ↾ (x ∩ y)) by Cut(setIntersectionLeftSubset, lastStep)
  }

  val domainRestrictionTwiceSubsetInner = Lemma(
    (relation(f), x ⊆ y) |- (f ↾ x) ↾ y === f ↾ x
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionOfSubsetForward)(domainRestrictionTwice)
  }

  val domainRestrictionTwiceSubsetOuter = Lemma(
    (relation(f), y ⊆ x) |- (f ↾ x) ↾ y === f ↾ y
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionOfSubsetBackward)(domainRestrictionTwice)
  }

  /**
   * Composition
   */

  val compositionUniqueness = Lemma(
    ∃!(z, ∀(p, p ∈ z <=> (p ∈ (dom(r1) × ran(r2)) /\ ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2))))
  ) {
    have(thesis) by UniqueComprehension(dom(r1) × ran(r2), lambda(p, ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2)))
  }

  val composition = DEF(r2, r1) --> The(z, ∀(p, p ∈ z <=> (p ∈ (dom(r1) × ran(r2))) /\ ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2)))(compositionUniqueness)

  extension (r2: Term) {
    infix def ∘(r1: Term) = composition(r2, r1)
  } 

  val compositionMembership = Lemma(
    p ∈ (r2 ∘ r1) <=> (p ∈ (dom(r1) × ran(r2)) /\ ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2))
  ) {
    have(∀(p, p ∈ (r2 ∘ r1) <=> (p ∈ (dom(r1) × ran(r2)) /\ ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2)))) by InstantiateForall(r2 ∘ r1)(composition.definition)
    thenHave(thesis) by InstantiateForall(p)
  }

  val compositionIsRelationBetween = Lemma(
    (relationBetween(r1, x, y), relationBetween(r2, y, z)) |- relationBetween(r2 ∘ r1, x, z)
  ) {
    have(p ∈ (r2 ∘ r1) ==> p ∈ (dom(r1) × ran(r2))) by Weakening(compositionMembership)
    thenHave(∀(p, p ∈ (r2 ∘ r1) ==> p ∈ (dom(r1) × ran(r2)))) by RightForall
    have((r2 ∘ r1) ⊆ (dom(r1) × ran(r2))) by Cut(lastStep, subsetIntro of (y := dom(r1) × ran(r2), x := r2 ∘ r1))
    have(relationBetween(r2 ∘ r1, dom(r1), ran(r2))) by Cut(lastStep, relationBetweenIntro of (r := r2 ∘ r1, a := dom(r1), b := ran(r2)))
    have((dom(r1) ⊆ x, ran(r2) ⊆ z) |- relationBetween(r2 ∘ r1, x, z)) by Cut(lastStep, relationBetweenSubsetDomains of (r := r2 ∘ r1, a := dom(r1), b := ran(r2), c := x, d := z))
    have((relationBetween(r1, x, y), ran(r2) ⊆ z) |- relationBetween(r2 ∘ r1, x, z)) by Cut(relationBetweenDomain of (r := r1, a := x, b := y), lastStep)
    have(thesis) by Cut(relationBetweenRange of (r := r2, a := y, b := z), lastStep)
  }

  val compositionMembershipPair = Lemma(
    pair(x, z) ∈ (r2 ∘ r1) <=> ∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2)
  ) {
    have((pair(x, y) ∈ r1, z ∈ ran(r2)) |- pair(x, z) ∈ (dom(r1) × ran(r2))) by Cut(relationDomainIntroPair of (a := x, b := y, r := r1), cartesianProductIntro of (a := x, b := z, x := dom(r1), y := ran(r2)))
    have((pair(x, y) ∈ r1, pair(y, z) ∈ r2) |- pair(x, z) ∈ (dom(r1) × ran(r2))) by Cut(relationRangeIntroPair of (a := y, b := z, r := r2), lastStep)
    thenHave(pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2 |- pair(x, z) ∈ (dom(r1) × ran(r2))) by LeftAnd
    thenHave(∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2) |- pair(x, z) ∈ (dom(r1) × ran(r2))) by LeftExists
    val redundancy = thenHave(∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2) ==> pair(x, z) ∈ (dom(r1) × ran(r2))) by RightImplies

    have(pair(x, z) ∈ (r2 ∘ r1) <=> (pair(x, z) ∈ (dom(r1) × ran(r2)) /\ ∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2))) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction)(compositionMembership of (p := pair(x, z)))
    thenHave(∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2) ==> pair(x, z) ∈ (dom(r1) × ran(r2)) |- pair(x, z) ∈ (r2 ∘ r1) <=> ∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2)) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  val compositionElimPair = Lemma(
    pair(x, z) ∈ (r2 ∘ r1) |- ∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2)
  ) {
    have(thesis) by Weakening(compositionMembershipPair)
  }

  val compositionElim = Lemma(
    (relationBetween(r1, x, y), relationBetween(r2, y, z), p ∈ (r2 ∘ r1)) |- ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2)
  ) {
    have((relationBetween(r2 ∘ r1, x, z), p ∈ (r2 ∘ r1)) |- ∃(y, pair(fst(p), y) ∈ r1 /\ pair(y, snd(p)) ∈ r2)) by Substitution.ApplyRules(pairReconstructionInRelationBetween of (r := r2 ∘ r1, a := x, b := z))(compositionElimPair of (x := fst(p), z := snd(p)))
    have(thesis) by Cut(compositionIsRelationBetween, lastStep)
  }

  val compositionIntro = Lemma(
    (pair(x, y) ∈ r1, pair(y, z) ∈ r2) |- pair(x, z) ∈ (r2 ∘ r1)
  ) {
    have((pair(x, y) ∈ r1, pair(y, z) ∈ r2) |- pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2) by Restate
    thenHave((pair(x, y) ∈ r1, pair(y, z) ∈ r2) |- ∃(y, pair(x, y) ∈ r1 /\ pair(y, z) ∈ r2)) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(compositionMembershipPair)
  }

  /**
   * Properties of relations
   */

  /**
   * Reflexive Relation --- `∀ x. x R x`
   */
  val reflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, y ∈ x ==> pair(y, y) ∈ r)

  val reflexiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, y ∈ x ==> pair(y, y) ∈ r)) |- reflexive(r, x)
  ) {
    have(thesis) by Weakening(reflexive.definition)
  }

  val reflexiveElim = Lemma(
    (reflexive(r, x), y ∈ x) |- pair(y, y) ∈ r
  ) {
    have(reflexive(r, x) |- ∀(y, y ∈ x ==> pair(y, y) ∈ r)) by Weakening(reflexive.definition)
    thenHave(thesis) by InstantiateForall(y)
  }

  val reflexiveRelationIsRelation = Lemma(
    reflexive(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(reflexive.definition)
  }

  /**
   * Lemma --- empty relation on the empty set is reflexive.
   */
  val emptyRelationReflexiveOnItself = Lemma(
    reflexive(∅, ∅)
  ) {
    have(y ∈ ∅ ==> pair(y, y) ∈ ∅) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, y ∈ ∅ ==> pair(y, y) ∈ ∅)) by RightForall
    have(relationBetween(∅, ∅, ∅) |- reflexive(∅, ∅)) by Cut(lastStep, reflexiveIntro of (r := ∅, x := ∅))
    have(thesis) by Cut(emptySetRelationOnItself, lastStep)
  }


  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, pair(y, z) ∈ r <=> pair(z, y) ∈ r))

  val symmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, pair(y, z) ∈ r <=> pair(z, y) ∈ r))) |- symmetric(r, x)
  ) {
    have(thesis) by Weakening(symmetric.definition)
  }

  val symmetricElim = Lemma(
    (symmetric(r, x), pair(y, z) ∈ r) |- pair(z, y) ∈ r
  ) {
    have(symmetric(r, x) |- ∀(y, ∀(z, pair(y, z) ∈ r <=> pair(z, y) ∈ r))) by Weakening(symmetric.definition)
    thenHave(symmetric(r, x) |- ∀(z, pair(y, z) ∈ r <=> pair(z, y) ∈ r)) by InstantiateForall(y)
    thenHave(symmetric(r, x) |- pair(y, z) ∈ r <=> pair(z, y) ∈ r) by InstantiateForall(z)
    thenHave(thesis) by Weakening
  }

  val symmetricRelationIsRelation = Lemma(
    symmetric(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(symmetric.definition)
  }


  /**
   * Lemma --- the empty relation is symmetric.
   */
  val emptyRelationSymmetric = Lemma(
    symmetric(∅, x)
  ) {
    val forward = have(pair(y, z) ∈ ∅ ==> pair(z, y) ∈ ∅) by Weakening(emptySetAxiom of (x := pair(y, z)))
    val backward = have(pair(z, y) ∈ ∅ ==> pair(y, z) ∈ ∅) by Weakening(emptySetAxiom of (x := pair(z, y)))
    have(pair(y, z) ∈ ∅ <=> pair(z, y) ∈ ∅) by RightIff(forward, backward)
    thenHave(∀(z, pair(y, z) ∈ ∅ <=> pair(z, y) ∈ ∅)) by RightForall
    thenHave(∀(y, ∀(z, pair(y, z) ∈ ∅ <=> pair(z, y) ∈ ∅))) by RightForall
    have(relationBetween(∅, x, x) |- symmetric(∅, x)) by Cut(lastStep, symmetricIntro of (r := ∅))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Transitive Relation --- `∀ x y z. x R y ∧ y R z ⇒ x R z`
   */
  val transitive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(w, ∀(y, ∀(z, (pair(w, y) ∈ r /\ pair(y, z) ∈ r) ==> pair(w, z) ∈ r)))

  /**
   * Lemma --- Transitive relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ w. ∀ y. ∀ z. (w, y) ∈ r ∧ (y, z) ∈ r ⇒ (w, z) ∈ r |- transitive(r, x)`
   */
  val transitiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(w, ∀(y, ∀(z, (pair(w, y) ∈ r /\ pair(y, z) ∈ r) ==> pair(w, z) ∈ r)))) |- transitive(r, x)
  ) {
    have(thesis) by Weakening(transitive.definition)
  }

  /**
   * Lemma --- Transitive relation elimination rule
   *
   *   `transitive(r, x), (w, y) ∈ r, (y, z) ∈ r |- (w, z) ∈ r`
   */
  val transitiveElim = Lemma(
    (transitive(r, x), pair(w, y) ∈ r, pair(y, z) ∈ r) |- pair(w, z) ∈ r
  ) {
    have(transitive(r, x) |- ∀(w, ∀(y, ∀(z, (pair(w, y) ∈ r /\ pair(y, z) ∈ r) ==> pair(w, z) ∈ r)))) by Weakening(transitive.definition)
    thenHave(transitive(r, x) |- ∀(y, ∀(z, (pair(w, y) ∈ r /\ pair(y, z) ∈ r) ==> pair(w, z) ∈ r))) by InstantiateForall(w)
    thenHave(transitive(r, x) |- ∀(z, (pair(w, y) ∈ r /\ pair(y, z) ∈ r) ==> pair(w, z) ∈ r)) by InstantiateForall(y)
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
    have((transitive(r, x), pair(a, b) ∈ r, pair(b, c) ∈ r, a ∈ y, c ∈ y) |- pair(a, c) ∈ relationRestriction(r, y, y)) by
      Cut(transitiveElim of (w := a, y := b, z := c), relationRestrictionIntroPair of (b := c, x := y))
    have((transitive(r, x), pair(a, b) ∈ relationRestriction(r, y, y), pair(b, c) ∈ r, a ∈ y, c ∈ y) |- pair(a, c) ∈ relationRestriction(r, y, y)) by
      Cut(relationRestrictionPairInRelation of (x := y, p := pair(a, b)), lastStep)
    have((transitive(r, x), pair(a, b) ∈ relationRestriction(r, y, y), pair(b, c) ∈ relationRestriction(r, y, y), a ∈ y, c ∈ y) |- pair(a, c) ∈ relationRestriction(r, y, y)) by
      Cut(relationRestrictionPairInRelation of (x := y, p := pair(b, c)), lastStep)
    thenHave(
      (transitive(r, x), pair(a, b) ∈ relationRestriction(r, y, y), pair(b, c) ∈ relationRestriction(r, y, y), a ∈ y /\ b ∈ y, b ∈ y /\ c ∈ y) |- pair(a, c) ∈ relationRestriction(r, y, y)
    ) by Weakening
    have((transitive(r, x), pair(a, b) ∈ relationRestriction(r, y, y), pair(b, c) ∈ relationRestriction(r, y, y), b ∈ y /\ c ∈ y) |- pair(a, c) ∈ relationRestriction(r, y, y)) by
      Cut(relationRestrictionPairInRestrictedDomains of (x := y), lastStep)
    have((transitive(r, x), pair(a, b) ∈ relationRestriction(r, y, y), pair(b, c) ∈ relationRestriction(r, y, y)) |- pair(a, c) ∈ relationRestriction(r, y, y)) by
      Cut(relationRestrictionPairInRestrictedDomains of (x := y, a := b, b := c), lastStep)
    thenHave(transitive(r, x) |- (pair(a, b) ∈ relationRestriction(r, y, y) /\ pair(b, c) ∈ relationRestriction(r, y, y)) ==> pair(a, c) ∈ relationRestriction(r, y, y)) by Restate
    thenHave(
      transitive(r, x) |- ∀(c, pair(a, b) ∈ relationRestriction(r, y, y) /\ pair(b, c) ∈ relationRestriction(r, y, y) ==> pair(a, c) ∈ relationRestriction(r, y, y))
    ) by RightForall
    thenHave(
      transitive(r, x) |- ∀(b, ∀(c, pair(a, b) ∈ relationRestriction(r, y, y) /\ pair(b, c) ∈ relationRestriction(r, y, y) ==> pair(a, c) ∈ relationRestriction(r, y, y)))
    ) by RightForall
    thenHave(
      transitive(r, x) |- ∀(a, ∀(b, ∀(c, pair(a, b) ∈ relationRestriction(r, y, y) /\ pair(b, c) ∈ relationRestriction(r, y, y) ==> pair(a, c) ∈ relationRestriction(r, y, y))))
    ) by RightForall
    have((transitive(r, x), relationBetween(relationRestriction(r, y, y), y, y)) |- transitive(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      transitiveIntro of (x := y, r := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Lemma --- the empty relation is transitive.
   */
  val emptyRelationTransitive = Lemma(
    transitive(∅, x)
  ) {
    have((pair(w, y) ∈ ∅ /\ pair(y, z) ∈ ∅) ==> pair(w, z) ∈ ∅) by Weakening(emptySetAxiom of (x := pair(w, y)))
    thenHave(∀(z, (pair(w, y) ∈ ∅ /\ pair(y, z) ∈ ∅) ==> pair(w, z) ∈ ∅)) by RightForall
    thenHave(∀(y, ∀(z, (pair(w, y) ∈ ∅ /\ pair(y, z) ∈ ∅) ==> pair(w, z) ∈ ∅))) by RightForall
    thenHave(∀(w, ∀(y, ∀(z, (pair(w, y) ∈ ∅ /\ pair(y, z) ∈ ∅) ==> pair(w, z) ∈ ∅)))) by RightForall
    have(relationBetween(∅, x, x) |- transitive(∅, x)) by Cut(lastStep, transitiveIntro of (r := ∅))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Equivalence Relation --- A relation is an equivalence relation if it is
   * [[reflexive]], [[symmetric]], and [[transitive]].
   */
  val equivalence = DEF(r, x) --> reflexive(r, x) /\ symmetric(r, x) /\ transitive(r, x)

  val equivalenceIntro = Lemma(
    (reflexive(r, x), symmetric(r, x), transitive(r, x)) |- equivalence(r, x)
  ) {
    have(thesis) by Weakening(equivalence.definition)
  }

  val equivalenceIsReflexive = Lemma(
    equivalence(r, x) |- reflexive(r, x)
  ) {
    have(thesis) by Weakening(equivalence.definition)
  }

  val equivalenceIsSymmetric = Lemma(
    equivalence(r, x) |- symmetric(r, x)
  ) {
    have(thesis) by Weakening(equivalence.definition)
  }

  val equivalenceIsTransitive = Lemma(
    equivalence(r, x) |- transitive(r, x)
  ) {
    have(thesis) by Weakening(equivalence.definition)
  }


  /**
   * Lemma --- the empty relation is an equivalence relation on the empty set.
   */
  val emptyRelationEquivalence = Lemma(
    equivalence(∅, ∅)
  ) {
    have((symmetric(∅, ∅), transitive(∅, ∅)) |- equivalence(∅, ∅)) by Cut(emptyRelationReflexiveOnItself, equivalenceIntro of (r := ∅, x := ∅))
    have(transitive(∅, ∅) |- equivalence(∅, ∅)) by Cut(emptyRelationSymmetric of (x := ∅), lastStep)
    have(thesis) by Cut(emptyRelationTransitive of (x := ∅), lastStep)
  }

  /**
   * Anti-reflexive Relation --- `∀ x. ! x R x`
   */
  val antiReflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, pair(y, y)∉ r)

  /**
   * Irreflexive Relation --- Alias for [[antiReflexive]].
   */
  val irreflexive = antiReflexive

  /**
   * Lemma --- Anti-reflexive relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ y. y ∈ x ==> pair(y, y) ∉ r |- antiReflexive(r, x)`
   */
  val antiReflexiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, pair(y, y) ∉ r)) |- antiReflexive(r, x)
  ) {
    have(thesis) by Weakening(antiReflexive.definition)
  }

  /**
   * Lemma --- Anti-reflexive relation elimination rule
   *
   *   `antiReflexive(r, x), y ∈ x |- (y, y) ∉ r`
   */
  val antiReflexiveElim = Lemma(
    antiReflexive(r, x) |- pair(y, y) ∉ r
  ) {
    have(antiReflexive(r, x) |- ∀(y, pair(y, y) ∉ r)) by Weakening(antiReflexive.definition)
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
    (antiReflexive(r, x), pair(a, b) ∈ r) |- a =/= b
  ) {
    have(pair(a, b) ∈ r |- pair(a, b) ∈ r) by Hypothesis
    thenHave((a === b, pair(a, b) ∈ r) |- pair(a, a) ∈ r) by RightSubstEq.withParametersSimple(
      List((a, b)),
      lambda(b, pair(a, b) ∈ r)
    )
    have((antiReflexive(r, x), pair(a, b) ∈ r, a === b) |- ()) by RightAnd(lastStep, antiReflexiveElim of (y := a))
    thenHave((antiReflexive(r, x), a ∈ x /\ b ∈ x, pair(a, b) ∈ r, a === b) |- ()) by Weakening
    have((antiReflexive(r, x), relationBetween(r, x, x), pair(a, b) ∈ r, a === b) |- ()) by Cut(relationBetweenElimPair of (a := x, b := x, x := a, y := b), lastStep)
    have((antiReflexive(r, x), pair(a, b) ∈ r, a === b) |- ()) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }

  /**
   * Lemma --- A subset of an irreflexive relation is also irreflexive
   *
   *   `irreflexive(r, x), t ⊆ r, relationBetween(t, y, y) |- irreflexive(t, y)`
   */
  val relationSubsetIrreflexive = Lemma(
    (irreflexive(r, x), t ⊆ r, relationBetween(t, y, y)) |- irreflexive(t, y)
  ) {
    have((pair(a, a) ∉ r, t ⊆ r) |- pair(a, a) ∉ t) by Restate.from(subsetElim of (z := pair(a, a), x := t, y := r))
    have((irreflexive(r, x), t ⊆ r) |- pair(a, a) ∉ t) by Cut(antiReflexiveElim of (y := a), lastStep)
    thenHave((irreflexive(r, x), t ⊆ r) |- ∀(a, pair(a, a) ∉ t)) by RightForall
    have(thesis) by Cut(lastStep, antiReflexiveIntro of (x := y, r := t))
  }

  /**
   * Lemma --- The restriction of an irreflexive relation remains irreflexive
   *
   *   `irreflexive(r, x) |- irreflexive(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionIrreflexive = Lemma(
    irreflexive(r, x) |- irreflexive(relationRestriction(r, y, y), y)
  ) {
    have((irreflexive(r, x), relationBetween(relationRestriction(r, y, y), y, y)) |- irreflexive(relationRestriction(r, y, y), y)) by Cut(
      relationRestrictionSubset of (x := y),
      relationSubsetIrreflexive of (t := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Lemma --- the empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Lemma(
    irreflexive(∅, x)
  ) {
    have(∀(y, pair(y, y) ∉ ∅)) by RightForall(emptySetAxiom of (x := pair(y, y)))
    have(relationBetween(∅, x, x) |- irreflexive(∅, x)) by Cut(lastStep, antiReflexiveIntro of (r := ∅))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (pair(y, z) ∈ r /\ pair(z, y) ∈ r) ==> (y === z)))

  val antiSymmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, (pair(y, z) ∈ r /\ pair(z, y) ∈ r) ==> (y === z)))) |- antiSymmetric(r, x)
  ) {
    have(thesis) by Weakening(antiSymmetric.definition)
  }

  val antiSymmetricElim = Lemma(
    (antiSymmetric(r, x), pair(y, z) ∈ r, pair(z, y) ∈ r) |- y === z
  ) {
    have(antiSymmetric(r, x) |- ∀(y, ∀(z, (pair(y, z) ∈ r /\ pair(z, y) ∈ r) ==> (y === z)))) by Weakening(antiSymmetric.definition)
    thenHave(antiSymmetric(r, x) |- ∀(z, (pair(y, z) ∈ r /\ pair(z, y) ∈ r) ==> (y === z))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  val antiSymmetricRelationIsRelation = Lemma(
    antiSymmetric(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(antiSymmetric.definition)
  }

  /**
   * Lemma --- the empty relation is anti-symmetric.
   */
  val emptyRelationAntiSymmetric = Lemma(
    antiSymmetric(∅, x)
  ) {
    have((pair(y, z) ∈ ∅ /\ pair(z, y) ∈ ∅) ==> (y === z)) by Weakening(emptySetAxiom of (x := pair(y, z)))
    thenHave(∀(z, (pair(y, z) ∈ ∅ /\ pair(z, y) ∈ ∅) ==> (y === z))) by RightForall
    thenHave(∀(y, ∀(z, (pair(y, z) ∈ ∅ /\ pair(z, y) ∈ ∅) ==> (y === z)))) by RightForall
    have(relationBetween(∅, x, x) |- antiSymmetric(∅, x)) by Cut(lastStep, antiSymmetricIntro of (r := ∅))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r))

  val asymmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r))) |- asymmetric(r, x)
  ) {
    have(thesis) by Weakening(asymmetric.definition)
  }

  val asymmetricElim = Lemma(
    (asymmetric(r, x), pair(y, z) ∈ r) |- pair(z, y) ∉ r
  ) {
    have(asymmetric(r, x) |- ∀(y, ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r))) by Weakening(asymmetric.definition)
    thenHave(asymmetric(r, x) |- ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r)) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  val asymmetricRelationIsRelation = Lemma(
    asymmetric(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(asymmetric.definition)
  }

  val antiReflexiveTransitiveIsAsymmetric = Lemma(
    (antiReflexive(r, x), transitive(r, x)) |- asymmetric(r, x)
  ) {
    have((antiReflexive(r, x), transitive(r, x), pair(z, y) ∈ r, pair(y, z) ∈ r) |- ()) by RightAnd(transitiveElim of (w := z), antiReflexiveElim of (y := z))
    thenHave((antiReflexive(r, x), transitive(r, x)) |- pair(y, z) ∈ r ==> pair(z, y) ∉ r) by Restate
    thenHave((antiReflexive(r, x), transitive(r, x)) |- ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r)) by RightForall
    thenHave((antiReflexive(r, x), transitive(r, x)) |- ∀(y, ∀(z, pair(y, z) ∈ r ==> pair(z, y) ∉ r))) by RightForall
    have((antiReflexive(r, x), transitive(r, x), relationBetween(r, x, x)) |- asymmetric(r, x)) by Cut(lastStep, asymmetricIntro)
    have(thesis) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }

  /**
   * Lemma --- the empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Lemma(
    asymmetric(∅, x)
  ) {
    have(pair(y, z) ∈ ∅ ==> pair(z, y) ∉ ∅) by Weakening(emptySetAxiom of (x := pair(y, z)))
    thenHave(∀(z, pair(y, z) ∈ ∅ ==> pair(z, y) ∉ ∅)) by RightForall
    thenHave(∀(y, ∀(z, pair(y, z) ∈ ∅ ==> pair(z, y) ∉ ∅))) by RightForall
    have(relationBetween(∅, x, x) |- asymmetric(∅, x)) by Cut(lastStep, asymmetricIntro of (r := ∅))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Connected Relation --- `∀ x y. (x R y) ∨ (y R x) ∨ (y = x)`
   */
  val connected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (y ∈ x /\ z ∈ x) ==> (pair(y, z) ∈ r \/ (pair(z, y) ∈ r) \/ (y === z))))

  /**
   * Total Relation --- Alias for [[connected]].
   */
  val total = connected

  /**
   * Lemma --- Connected relation introduction rule
   *
   *   `relationBetween(r, x, x), ∀ y. ∀ z. y ∈ x /\ z ∈ x ==> (pair(y, z) ∈ r ∨ pair(z, y) ∈ r ∨ (y = z)) |- connected(r, x)`
   */
  val connectedIntro = Lemma((relationBetween(r, x, x), ∀(y, ∀(z, (y ∈ x /\ z ∈ x) ==> (pair(y, z) ∈ r \/ (pair(z, y) ∈ r) \/ (y === z))))) |- connected(r, x)) {
    have(thesis) by Weakening(connected.definition)
  }

  /**
   * Lemma --- Connected relation elimination rule
   *
   *   `connected(r, x), y ∈ x, z ∈ x |- (y, z) ∈ r ∨ (z, y) ∈ r ∨ y = z`
   */
  val connectedElim = Lemma((connected(r, x), y ∈ x, z ∈ x) |- pair(y, z) ∈ r \/ (pair(z, y) ∈ r) \/ (y === z)) {
    have(connected(r, x) |- ∀(y, ∀(z, (y ∈ x /\ z ∈ x) ==> (pair(y, z) ∈ r \/ (pair(z, y) ∈ r) \/ (y === z))))) by Weakening(connected.definition)
    thenHave(connected(r, x) |- ∀(z, (y ∈ x /\ z ∈ x) ==> (pair(y, z) ∈ r \/ (pair(z, y) ∈ r) \/ (y === z)))) by InstantiateForall(y)
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
   * Lemma --- the empty relation is total on the empty set.
   */
  val emptyRelationTotalOnItself = Lemma(
    connected(∅, ∅)
  ) {
    have((y ∈ ∅ /\ z ∈ ∅) ==> (pair(y, z) ∈ ∅ \/(pair(z, y) ∈ ∅) \/ (y === z))) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(z, (y ∈ ∅ /\ z ∈ ∅) ==> (pair(y, z) ∈ ∅ \/ (pair(z, y) ∈ ∅) \/ (y === z)))) by RightForall
    thenHave(∀(y, ∀(z, (y ∈ ∅ /\ z ∈ ∅) ==> (pair(y, z) ∈ ∅ \/ (pair(z, y) ∈ ∅) \/ (y === z))))) by RightForall
    have(relationBetween(∅, ∅, ∅) |- connected(∅, ∅)) by Cut(lastStep, connectedIntro of (r := ∅, x := ∅))
    have(thesis) by Cut(emptySetRelationOnItself, lastStep)
  }

  /**
   * Lemma --- The restriction of a connected relation remains connected
   *
   *   `connected(r, x), y ⊆ x |- connected(relationRestriction(r, y, y), y)`
   */
  val relationRestrictionConnected = Lemma(
    (connected(r, x), y ⊆ x) |- connected(relationRestriction(r, y, y), y)
  ) {
    val left = have((pair(a, b) ∈ r, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Weakening(
      relationRestrictionIntroPair of (x := y)
    )
    val right = have((pair(b, a) ∈ r, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Weakening(
      relationRestrictionIntroPair of (x := y, a := b, b := a)
    )
    have(a === b |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Restate
    have((pair(b, a) ∈ r \/ (a === b), a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by LeftOr(lastStep, right)
    have(
      (pair(a, b) ∈ r \/ (pair(b, a) ∈ r) \/ (a === b), a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)
    ) by LeftOr(lastStep, left)
    have((connected(r, x), a ∈ x, b ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      connectedElim of (y := a, z := b),
      lastStep
    )
    have((connected(r, x), y ⊆ x, b ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      subsetElim of (z := a, y := x, x := y),
      lastStep
    )
    have((connected(r, x), y ⊆ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)) by Cut(
      subsetElim of (z := b, y := x, x := y),
      lastStep
    )
    thenHave((connected(r, x), y ⊆ x) |- (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b))) by Restate
    thenHave(
      (connected(r, x), y ⊆ x) |- ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b)))
    ) by RightForall
    thenHave(
      (connected(r, x), y ⊆ x) |- ∀(a, ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ relationRestriction(r, y, y) \/ (pair(b, a) ∈ relationRestriction(r, y, y)) \/ (a === b))))
    ) by RightForall
    have((connected(r, x), relationBetween(relationRestriction(r, y, y), y, y), y ⊆ x) |- connected(relationRestriction(r, y, y), y)) by Cut(
      lastStep,
      connectedIntro of (x := y, r := relationRestriction(r, y, y))
    )
    have(thesis) by Cut(relationRestrictionIsRelationBetweenRestrictedDomains of (w := x, z := x, x := y), lastStep)
  }

  /**
   * Strongly Connected Relation ---
   *     `∀ x y z. y R x ∧ z R x ⇒ y R z ∨ z R y`
   */
  val stronglyConnected = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (y ∈ x /\ z ∈ x) ==> (pair(y, z) ∈ r \/ (pair(z, y) ∈ r))))



}
