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
    have((relationBetween(r, a, b), in(pair(x, y), r)) |- in(pair(x, y), cartesianProduct(a, b))) by Substitution.ApplyRules(relationBetween.definition)(
      subsetElim of (z := pair(x, y), x := r, y := cartesianProduct(a, b))
    )
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
      Substitution.ApplyRules(relationBetween.definition of (r := r2))(subsetTransitivity of (x := r1, y := r2, z := cartesianProduct(a, b)))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := r1))
  }

  /**
   * Lemma --- the empty set is a relation, the empty relation, between any two sets.
   */
  val emptySetRelation = Lemma(
    relationBetween(emptySet, a, b)
  ) {
    have(thesis) by Cut(emptySetSubset of (x := cartesianProduct(a, b)), relationBetweenIntro of (r := emptySet))
  }

  val relationBetweenLeftEmptyIsEmpty = Lemma(
    relationBetween(r, emptySet, b) |- r === emptySet
  ) {
    have(subset(r, emptySet) |- r === emptySet) by Weakening(subsetEmptySet of (x := r))
    thenHave(subset(r, cartesianProduct(emptySet, b)) |- r === emptySet) by Substitution.ApplyRules(cartesianProductLeftEmpty of (y := b))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (a := emptySet))
  }

  val relationBetweenRightEmptyIsEmpty = Lemma(
    relationBetween(r, a, emptySet) |- r === emptySet
  ) {
    have(subset(r, emptySet) |- r === emptySet) by Weakening(subsetEmptySet of (x := r))
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
    have(
      (subset(r1, cartesianProduct(a, b)), subset(r2, cartesianProduct(c, d)), subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))) |-
        subset(setUnion(r1, r2), cartesianProduct(setUnion(a, c), setUnion(b, d)))
    ) by Cut(
      unionOfSubsetsOfDifferentSets of (a := r1, b := r2, c := cartesianProduct(a, b), d := cartesianProduct(c, d)),
      subsetTransitivity of (x := setUnion(r1, r2), y := setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), z := cartesianProduct(setUnion(a, c), setUnion(b, d)))
    )
    have((subset(r1, cartesianProduct(a, b)), subset(r2, cartesianProduct(c, d))) |- subset(setUnion(r1, r2), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Cut(
      unionOfCartesianProducts,
      lastStep
    )
    thenHave((relationBetween(r1, a, b), subset(r2, cartesianProduct(c, d))) |- relationBetween(setUnion(r1, r2), setUnion(a, c), setUnion(b, d))) by Substitution.ApplyRules(
      relationBetween.definition of (r := setUnion(r1, r2), a := setUnion(a, c), b := setUnion(b, d)),
      relationBetween.definition of (r := r1)
    )
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := r2, a := c, b := d))
  }

  val relationBetweenSingleton = Lemma(
    relationBetween(singleton(pair(x, y)), singleton(x), singleton(y))
  ) {
    have(relationBetween(cartesianProduct(singleton(x), singleton(y)), singleton(x), singleton(y))) by Cut(
      subsetReflexivity of (x := cartesianProduct(singleton(x), singleton(y))),
      relationBetweenIntro of (r := cartesianProduct(singleton(x), singleton(y)), a := singleton(x), b := singleton(y))
    )
    thenHave(thesis) by Substitution.ApplyRules(singletonCartesianProduct)
  }

  val relationBetweenSubsetDomains = Lemma(
    (relationBetween(r, a, b), subset(a, c), subset(b, d)) |- relationBetween(r, c, d)
  ) {
    have((subset(r, cartesianProduct(a, b)), subset(a, c), subset(b, d)) |- subset(r, cartesianProduct(c, d))) by Cut(
      cartesianProductSubset of (w := a, x := b, y := c, z := d),
      subsetTransitivity of (x := r, y := cartesianProduct(a, b), z := cartesianProduct(c, d))
    )
    thenHave((subset(r, cartesianProduct(a, b)), subset(a, c), subset(b, d)) |- relationBetween(r, c, d)) by Substitution.ApplyRules(relationBetween.definition of (a := c, b := d))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition)
  }

  val relationBetweenSubsetLeftDomain = Lemma(
    (relationBetween(r, a, b), subset(a, c)) |- relationBetween(r, c, b)
  ) {
    have(thesis) by Cut(subsetReflexivity of (x := b), relationBetweenSubsetDomains of (d := b))
  }

  val relationBetweenSubsetRightDomain = Lemma(
    (relationBetween(r, a, b), subset(b, d)) |- relationBetween(r, a, d)
  ) {
    have(thesis) by Cut(subsetReflexivity of (x := a), relationBetweenSubsetDomains of (c := a))
  }

  val relationDomainUniqueness = Lemma(
    ∃!(z, ∀(a, in(a, z) <=> (in(a, union(union(r))) /\ ∃(b, in(pair(a, b), r)))))
  ) {
    have(thesis) by UniqueComprehension(union(union(r)), lambda(a, ∃(b, in(pair(a, b), r))))
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
  val relationDomain = DEF(r) --> The(z, ∀(a, in(a, z) <=> (in(a, union(union(r))) /\ ∃(b, in(pair(a, b), r)))))(relationDomainUniqueness)

  val relationDomainMembership = Lemma(
    in(a, relationDomain(r)) <=> ∃(b, in(pair(a, b), r))
  ) {
    have(in(pair(a, b), r) |- in(a, union(union(r)))) by Weakening(pairComponentsInUnionUnion of (x := a, y := b))
    thenHave(exists(b, in(pair(a, b), r)) |- in(a, union(union(r)))) by LeftExists
    val redundancy = thenHave(exists(b, in(pair(a, b), r)) ==> in(a, union(union(r)))) by RightImplies

    have(∀(a, in(a, relationDomain(r)) <=> (in(a, union(union(r))) /\ ∃(b, in(pair(a, b), r))))) by InstantiateForall(relationDomain(r))(relationDomain.definition)
    thenHave(in(a, relationDomain(r)) <=> (in(a, union(union(r))) /\ ∃(b, in(pair(a, b), r)))) by InstantiateForall(a)
    thenHave(exists(b, in(pair(a, b), r)) ==> in(a, union(union(r))) |- in(a, relationDomain(r)) <=> ∃(b, in(pair(a, b), r))) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  /**
   * Lemma --- Relation Domain Introduction Rule
   *
   *   `(a, b) ∈ r ⊢ a ∈ dom(r)`
   */
  val relationDomainIntroPair = Lemma(
    in(pair(a, b), r) |- in(a, relationDomain(r))
  ) {
    have(in(pair(a, b), r) |- in(pair(a, b), r)) by Hypothesis
    thenHave(in(pair(a, b), r) |- exists(b, in(pair(a, b), r))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(relationDomainMembership)
  }

  /**
   * Lemma --- Relation Domain Elimination Rule
   *
   *   `a ∈ dom(r) ⊢ ∃ b. (a, b) ∈ r`
   */
  val relationDomainElim = Lemma(
    in(a, relationDomain(r)) |- ∃(b, in(pair(a, b), r))
  ) {
    have(thesis) by Weakening(relationDomainMembership)
  }

  /**
    * Lemma --- Domain of the singleton pair relation
    * 
    *  `dom({(a, b)}) = {a}`
    */
  val relationDomainSingleton = Lemma(
    relationDomain(singleton(pair(a, b))) === singleton(a)
  ) {
    val backward = have(in(x, singleton(a)) ==> in(x, relationDomain(singleton(pair(a, b))))) subproof {
      have(in(a, relationDomain(singleton(pair(a, b))))) by Cut(singletonIntro of (x := pair(a, b)), relationDomainIntroPair of (r := singleton(pair(a, b))))
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
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r1)), in(pair(a, b), r2))) by Cut(setUnionElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntroPair of (r := r1))
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r1)), in(a, relationDomain(r2)))) by Cut(lastStep, relationDomainIntroPair of (r := r2))
      have(in(pair(a, b), setUnion(r1, r2)) |- (in(a, relationDomain(r2)), in(a, setUnion(relationDomain(r1), relationDomain(r2))))) by Cut(
        lastStep,
        setUnionLeftIntro of (z := a, x := relationDomain(r1), y := relationDomain(r2))
      )
      have(in(pair(a, b), setUnion(r1, r2)) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by Cut(
        lastStep,
        setUnionRightIntro of (z := a, x := relationDomain(r1), y := relationDomain(r2))
      )
      thenHave(exists(b, in(pair(a, b), setUnion(r1, r2))) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by LeftExists
      have(in(a, relationDomain(setUnion(r1, r2))) |- in(a, setUnion(relationDomain(r1), relationDomain(r2)))) by Cut(relationDomainElim of (r := setUnion(r1, r2)), lastStep)
    }

    val backward = have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) ==> in(a, relationDomain(setUnion(r1, r2)))) subproof {

      have(in(pair(a, b), r1) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by RightExists(setUnionLeftIntro of (z := pair(a, b), x := r1, y := r2))
      val left = thenHave(exists(b, in(pair(a, b), r1)) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by LeftExists

      have(in(pair(a, b), r2) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by RightExists(setUnionRightIntro of (z := pair(a, b), x := r1, y := r2))
      val right = thenHave(exists(b, in(pair(a, b), r2)) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by LeftExists

      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), r1)), in(a, relationDomain(r2)))) by Cut(
        setUnionElim of (z := a, x := relationDomain(r1), y := relationDomain(r2)),
        relationDomainElim of (r := r1)
      )
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), r1)), exists(b, in(pair(a, b), r2)))) by Cut(lastStep, relationDomainElim of (r := r2))
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- (exists(b, in(pair(a, b), setUnion(r1, r2))), exists(b, in(pair(a, b), r2)))) by Cut(lastStep, left)
      have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- exists(b, in(pair(a, b), setUnion(r1, r2)))) by Cut(lastStep, right)
      thenHave(in(a, setUnion(relationDomain(r1), relationDomain(r2))) |- in(a, relationDomain(setUnion(r1, r2)))) by Substitution.ApplyRules(relationDomainMembership of (r := setUnion(r1, r2)))
    }

    have(in(a, setUnion(relationDomain(r1), relationDomain(r2))) <=> in(a, relationDomain(setUnion(r1, r2)))) by RightIff(forward, backward)
    thenHave(forall(a, in(a, setUnion(relationDomain(r1), relationDomain(r2))) <=> in(a, relationDomain(setUnion(r1, r2))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationDomain(setUnion(r1, r2)), y := setUnion(relationDomain(r1), relationDomain(r2))))
  }

  val relationDomainUnion = Lemma(
    in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))
  ) {
    val forward = have(exists(a, in(pair(t, a), union(z))) ==> exists(y, in(y, z) /\ in(t, relationDomain(y)))) subproof {
      have(in(y, z) |- in(y, z)) by Hypothesis
      have((in(pair(t, a), y), in(y, z)) |- in(t, relationDomain(y)) /\ in(y, z)) by RightAnd(relationDomainIntroPair of (a := t, b := a, r := y), lastStep)
      thenHave((in(pair(t, a), y), in(y, z)) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) by RightExists
      thenHave((in(pair(t, a), y) /\ in(y, z)) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) by LeftAnd
      thenHave(exists(y, in(pair(t, a), y) /\ in(y, z)) |- exists(y, in(t, relationDomain(y)) /\ in(y, z))) by LeftExists
      have(in(pair(t, a), union(z)) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) by Cut(unionElim of (z := pair(t, a), x := z), lastStep)
      thenHave(exists(a, in(pair(t, a), union(z))) |- exists(y, in(y, z) /\ in(t, relationDomain(y)))) by LeftExists
    }
    val backward = have(exists(y, in(y, z) /\ in(t, relationDomain(y))) ==> exists(a, in(pair(t, a), union(z)))) subproof {
      have((in(pair(t, a), y), in(y, z)) |- exists(a, in(pair(t, a), union(z)))) by RightExists(unionIntro of (z := pair(t, a), x := z))
      thenHave((exists(a, in(pair(t, a), y)), in(y, z)) |- exists(a, in(pair(t, a), union(z)))) by LeftExists
      have((in(y, z), in(t, relationDomain(y))) |- exists(a, in(pair(t, a), union(z)))) by Cut(relationDomainElim of (a := t, r := y), lastStep)
      thenHave((in(y, z) /\ in(t, relationDomain(y))) |- exists(a, in(pair(t, a), union(z)))) by LeftAnd
      thenHave(exists(y, in(y, z) /\ in(t, relationDomain(y))) |- exists(a, in(pair(t, a), union(z)))) by LeftExists
    }

    have(exists(a, in(pair(t, a), union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y)))) by RightIff(forward, backward)
    thenHave(thesis) by Substitution.ApplyRules(relationDomainMembership)
  }

  val relationDomainSubset = Lemma(
    subset(r1, r2) |- subset(relationDomain(r1), relationDomain(r2))
  ) {
    have((subset(r1, r2), in(pair(a, b), r1)) |- in(a, relationDomain(r2))) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationDomainIntroPair of (r := r2))
    thenHave((subset(r1, r2), exists(b, in(pair(a, b), r1))) |- in(a, relationDomain(r2))) by LeftExists
    have((subset(r1, r2), in(a, relationDomain(r1))) |- in(a, relationDomain(r2))) by Cut(relationDomainElim of (r := r1), lastStep)
    thenHave(subset(r1, r2) |- in(a, relationDomain(r1)) ==> in(a, relationDomain(r2))) by RightImplies
    thenHave(subset(r1, r2) |- forall(a, in(a, relationDomain(r1)) ==> in(a, relationDomain(r2)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationDomain(r1), y := relationDomain(r2)))
  }

  val relationRangeUniqueness = Lemma(
    ∃!(z, ∀(b, in(b, z) <=> (in(b, union(union(r))) /\ ∃(a, in(pair(a, b), r)))))
  ) {
    have(thesis) by UniqueComprehension(union(union(r)), lambda(b, ∃(a, in(pair(a, b), r))))
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
   *      `range(r) = {b | ∃ a. (a, b) ∈ r}`
   *
   * @param r relation (set)
   */
  val relationRange = DEF(r) --> The(z, ∀(b, in(b, z) <=> (in(b, union(union(r))) /\ ∃(a, in(pair(a, b), r)))))(relationRangeUniqueness)

  val relationRangeMembership = Lemma(
    in(b, relationRange(r)) <=> ∃(a, in(pair(a, b), r))
  ) {
    have(in(pair(a, b), r) |- in(b, union(union(r)))) by Weakening(pairComponentsInUnionUnion of (x := a, y := b))
    thenHave(exists(a, in(pair(a, b), r)) |- in(b, union(union(r)))) by LeftExists
    val redundancy = thenHave(exists(a, in(pair(a, b), r)) ==> in(b, union(union(r)))) by RightImplies

    have(∀(b, in(b, relationRange(r)) <=> (in(b, union(union(r))) /\ ∃(a, in(pair(a, b), r))))) by InstantiateForall(relationRange(r))(relationRange.definition)
    thenHave(in(b, relationRange(r)) <=> (in(b, union(union(r))) /\ ∃(a, in(pair(a, b), r)))) by InstantiateForall(b)
    thenHave(exists(a, in(pair(a, b), r)) ==> in(b, union(union(r))) |- in(b, relationRange(r)) <=> ∃(a, in(pair(a, b), r))) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  val relationRangeIntroPair = Lemma(
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
    have((subset(r1, r2), in(pair(a, b), r1)) |- in(b, relationRange(r2))) by Cut(subsetElim of (z := pair(a, b), x := r1, y := r2), relationRangeIntroPair of (r := r2))
    thenHave((subset(r1, r2), exists(a, in(pair(a, b), r1))) |- in(b, relationRange(r2))) by LeftExists
    have((subset(r1, r2), in(b, relationRange(r1))) |- in(b, relationRange(r2))) by Cut(relationRangeElim of (r := r1), lastStep)
    thenHave(subset(r1, r2) |- in(b, relationRange(r1)) ==> in(b, relationRange(r2))) by RightImplies
    thenHave(subset(r1, r2) |- forall(b, in(b, relationRange(r1)) ==> in(b, relationRange(r2)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(r1), y := relationRange(r2)))
  }

  val pairInRelation = Lemma(
    in(pair(a, b), r) |- in(a, relationDomain(r)) /\ in(b, relationRange(r))
  ) {
    have(thesis) by RightAnd(relationDomainIntroPair, relationRangeIntroPair)
  }

  val relationBetweenDomain = Lemma(
    relationBetween(r, a, b) |- subset(relationDomain(r), a)
  ) {
    have((relationBetween(r, a, b), in(pair(x, y), r)) |- in(x, a)) by Weakening(relationBetweenElimPair)
    thenHave((relationBetween(r, a, b), exists(y, in(pair(x, y), r))) |- in(x, a)) by LeftExists
    have((relationBetween(r, a, b), in(x, relationDomain(r))) |- in(x, a)) by Cut(relationDomainElim of (a := x), lastStep)
    thenHave(relationBetween(r, a, b) |- in(x, relationDomain(r)) ==> in(x, a)) by RightImplies
    thenHave(relationBetween(r, a, b) |- forall(x, in(x, relationDomain(r)) ==> in(x, a))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationDomain(r), y := a))
  }

  val relationBetweenRange = Lemma(
    relationBetween(r, a, b) |- subset(relationRange(r), b)
  ) {
    have((relationBetween(r, a, b), in(pair(x, y), r)) |- in(y, b)) by Weakening(relationBetweenElimPair)
    thenHave((relationBetween(r, a, b), exists(x, in(pair(x, y), r))) |- in(y, b)) by LeftExists
    have((relationBetween(r, a, b), in(y, relationRange(r))) |- in(y, b)) by Cut(relationRangeElim of (b := y), lastStep)
    thenHave(relationBetween(r, a, b) |- in(y, relationRange(r)) ==> in(y, b)) by RightImplies
    thenHave(relationBetween(r, a, b) |- forall(y, in(y, relationRange(r)) ==> in(y, b))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(r), y := b))
  }

  val relationBetweenBetweenDomainAndRange = Lemma(
    relationBetween(r, a, b) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), relationRange(r)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(relationDomain(r), relationRange(r)))) by LeftAnd(
      cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := relationDomain(r), y := relationRange(r))
    )
    have(in(pair(firstInPair(p), secondInPair(p)), r) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(relationDomain(r), relationRange(r)))) by Cut(
      pairInRelation of (a := firstInPair(p), b := secondInPair(p)),
      lastStep
    )
    thenHave((relationBetween(r, a, b), in(p, r)) |- in(p, cartesianProduct(relationDomain(r), relationRange(r)))) by Substitution.ApplyRules(pairReconstructionInRelationBetween)
    thenHave(relationBetween(r, a, b) |- in(p, r) ==> in(p, cartesianProduct(relationDomain(r), relationRange(r)))) by RightImplies
    thenHave(relationBetween(r, a, b) |- forall(p, in(p, r) ==> in(p, cartesianProduct(relationDomain(r), relationRange(r))))) by RightForall
    have(relationBetween(r, a, b) |- subset(r, cartesianProduct(relationDomain(r), relationRange(r)))) by Cut(
      lastStep,
      subsetIntro of (x := r, y := cartesianProduct(relationDomain(r), relationRange(r)))
    )
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
    have((relationBetween(r1, a, x), relationBetween(r2, b, y)) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by RightExists(
      unionOfTwoRelationsWithField of (c := b, b := x, d := y)
    )
    thenHave((exists(x, relationBetween(r1, a, x)), relationBetween(r2, b, y)) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by LeftExists
    thenHave((exists(x, relationBetween(r1, a, x)), exists(y, relationBetween(r2, b, y))) |- exists(y, relationBetween(setUnion(r1, r2), setUnion(a, b), y))) by LeftExists
    thenHave(thesis) by Substitution.ApplyRules(
      relationFrom.definition of (r := setUnion(r1, r2), a := setUnion(a, b)),
      relationFrom.definition of (r := r1),
      relationFrom.definition of (r := r2, a := b)
    )
  }

  val relationFromBetweenDomainAndRange = Lemma(
    relationFrom(r, a) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(exists(b, relationBetween(r, a, b)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists(relationBetweenBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

    val relationFromDomain = Lemma(
    relationFrom(r, a) |- subset(relationDomain(r), a)
  ) {
    have(exists(b, relationBetween(r, a, b)) |- subset(relationDomain(r), a)) by LeftExists(relationBetweenDomain)
    thenHave(thesis) by Substitution.ApplyRules(relationFrom.definition)
  }

  val relationFromToRange = Lemma(
    relationFrom(r, a) |- relationBetween(r, a, relationRange(r))
  ) {
    have((relationFrom(r, a), subset(relationDomain(r), a)) |- relationBetween(r, a, relationRange(r))) by 
      Cut(relationFromBetweenDomainAndRange, relationBetweenSubsetLeftDomain of (b := relationRange(r), a := relationDomain(r), c := a))
    have(thesis) by Cut(relationFromDomain, lastStep)
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

  val relationDomainIntro = Lemma(
    (relation(r), in(p, r)) |- in(firstInPair(p), relationDomain(r))
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationDomainIntroPair of (a := firstInPair(p), b := secondInPair(p)))
  }

  val relationRangeIntro = Lemma(
    (relation(r), in(p, r)) |- in(secondInPair(p), relationRange(r))
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationRangeIntroPair of (a := firstInPair(p), b := secondInPair(p)))
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
      have((domsDef, in(r, z)) |- subset(relationDomain(r), union(doms))) by Cut(lastStep, subsetUnion of (x := relationDomain(r), y := doms))
      have(thesis) by Cut(lastStep, subsetElim of (z := firstInPair(p), x := relationDomain(r), y := union(doms)))
    }

    val inRans = have((ransDef, in(r, z), in(secondInPair(p), relationRange(r))) |- in(secondInPair(p), union(rans))) subproof {
      have(in(r, z) |- in(r, z) /\ (relationRange(r) === relationRange(r))) by Restate
      val exDoms = thenHave(in(r, z) |- exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) by RightExists
      have(ransDef |- ransDef) by Hypothesis
      thenHave(ransDef |- in(relationRange(r), rans) <=> exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) by InstantiateForall(relationRange(r))
      thenHave((ransDef, exists(r2, in(r2, z) /\ (relationRange(r) === relationRange(r2)))) |- in(relationRange(r), rans)) by Weakening
      have((ransDef, in(r, z)) |- in(relationRange(r), rans)) by Cut(exDoms, lastStep)
      have((ransDef, in(r, z)) |- subset(relationRange(r), union(rans))) by Cut(lastStep, subsetUnion of (x := relationRange(r), y := rans))
      have(thesis) by Cut(lastStep, subsetElim of (z := secondInPair(p), x := relationRange(r), y := union(rans)))
    }

    val relSet = forall(r, in(r, z) ==> relation(r))
    have(relSet |- relSet) by Hypothesis
    val relSetMembership = thenHave((relSet, in(r, z)) |- relation(r)) by InstantiateForall(r)

    val inCartProduct = have(in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(union(doms), union(rans)))) by LeftAnd(
      cartesianProductIntro of (a := firstInPair(p), b := secondInPair(p), x := union(doms), y := union(rans))
    )

    have((domsDef, ransDef, in(r, z), in(firstInPair(p), relationDomain(r)), in(secondInPair(p), relationRange(r))) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))) by RightAnd(
      inDoms,
      inRans
    )
    thenHave(
      (domsDef, ransDef, in(r, z), in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), relationRange(r))) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))
    ) by LeftAnd
    have((domsDef, ransDef, in(p, r), relation(r), in(r, z)) |- in(firstInPair(p), union(doms)) /\ in(secondInPair(p), union(rans))) by Cut(relationElim, lastStep)
    have((domsDef, ransDef, in(p, r), relation(r), in(r, z)) |- in(pair(firstInPair(p), secondInPair(p)), cartesianProduct(union(doms), union(rans)))) by Cut(lastStep, inCartProduct)
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

  val relationIsRelationBetween = Lemma(
    relation(r) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    have(exists(a, relationFrom(r, a)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists(relationFromBetweenDomainAndRange)
    thenHave(thesis) by Substitution.ApplyRules(relation.definition)
  }

  val relationIsRelationFrom = Lemma(
    relation(r) |- relationFrom(r, relationDomain(r))
  ) {
    have(thesis) by Cut(relationIsRelationBetween, relationBetweenIsRelationFrom of (a := relationDomain(r), b := relationRange(r)))
  }

  /**
   * Lemma --- The only relation with an empty domain is the empty relation.
   *
   *     `relation(r), Dom(r) = ∅ |- r = ∅`
   */
  val relationDomainEmpty = Lemma(
    (relation(r), relationDomain(r) === emptySet) |- r === emptySet
  ) {
    have((relation(r), relationDomain(r) === emptySet) |- relationBetween(r, emptySet, relationRange(r))) by
      RightSubstEq.withParametersSimple(List((relationDomain(r), emptySet)), lambda(x, relationBetween(r, x, relationRange(r))))(relationIsRelationBetween)
    have(thesis) by Cut(lastStep, relationBetweenLeftEmptyIsEmpty of (b := relationRange(r)))
  }

  /**
   * Lemma --- The only relation with an empty range is the empty relation.
   *
   *     `relation(r), Ran(r) = ∅ |- r = ∅`
   */
  val relationRangeEmpty = Lemma(
    (relation(r), relationRange(r) === emptySet) |- r === emptySet
  ) {
    have((relation(r), relationRange(r) === emptySet) |- relationBetween(r, relationDomain(r), emptySet)) by
      RightSubstEq.withParametersSimple(List((relationRange(r), emptySet)), lambda(x, relationBetween(r, relationDomain(r), x)))(relationIsRelationBetween)
    have(thesis) by Cut(lastStep, relationBetweenRightEmptyIsEmpty of (a := relationDomain(r)))
  }

  val inverseRelationUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> exists(p, in(p, r) /\ (t === pair(secondInPair(p), firstInPair(p))))))
  ) {
    have(thesis) by Restate.from(replacementClassFunction of (A := r, F := lambda(p, pair(secondInPair(p), firstInPair(p)))))
  }

  val inverseRelation = DEF(r) --> The(z, ∀(t, in(t, z) <=> exists(p, in(p, r) /\ (t === pair(secondInPair(p), firstInPair(p))))))(inverseRelationUniqueness)

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
      .withParametersSimple(List((in(pair(a, b), cartesianProduct(x, y)), in(a, x) /\ in(b, y))), lambda(h, in(pair(a, b), relationRestriction(r, x, y)) <=> (in(pair(a, b), r) /\ h)))(
        relationRestrictionElem of (p := pair(a, b))
      )
    have(thesis) by Cut(cartesianProductMembershipPair, lastStep)
  }

  val relationRestrictionIntroPair = Lemma(
    (in(pair(a, b), r), in(a, x), in(b, y)) |- in(pair(a, b), relationRestriction(r, x, y))
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionIntro = Lemma(
    (relation(r), in(p, r), in(firstInPair(p), x), in(secondInPair(p), y)) |- in(p, relationRestriction(r, x, y))
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInRelation)(relationRestrictionIntroPair of (a := firstInPair(p), b := secondInPair(p)))
  }

  val relationRestrictionPairInRestrictedDomains = Lemma(
    in(pair(a, b), relationRestriction(r, x, y)) |- in(a, x) /\ in(b, y)
  ) {
    have(thesis) by Weakening(relationRestrictionElemPair)
  }

  val relationRestrictionInRestrictedDomains = Lemma(
    in(p, relationRestriction(r, x, y)) |- in(firstInPair(p), x) /\ in(secondInPair(p), y)
  ) {
    have(in(p, relationRestriction(r, x, y)) |- in(p, cartesianProduct(x, y))) by Weakening(relationRestrictionElem)
    have(thesis) by Cut(lastStep, cartesianProductElim)
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

  val relationRestrictionInRelation = Lemma(
    in(p, relationRestriction(r, x, y)) |- in(p, r)
  ) {
    have(thesis) by Cut(relationRestrictionSubset, subsetElim of (z := p, x := relationRestriction(r, x, y), y := r))
  }

  val relationRestrictionDomain = Lemma(
    subset(relationDomain(relationRestriction(r, x, y)), setIntersection(relationDomain(r), x))
  ) {
    have(in(pair(a, b), relationRestriction(r, x, y)) |- in(a, x)) by Weakening(relationRestrictionPairInRestrictedDomains)
    have((in(pair(a, b), relationRestriction(r, x, y)), in(a, relationDomain(r))) |- in(a, setIntersection(relationDomain(r), x))) by Cut(
      lastStep,
      setIntersectionIntro of (z := a, x := relationDomain(r), y := x)
    )
    have((in(pair(a, b), relationRestriction(r, x, y)), in(pair(a, b), r)) |- in(a, setIntersection(relationDomain(r), x))) by Cut(relationDomainIntroPair, lastStep)
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
    have((in(pair(a, b), relationRestriction(r, x, y)), in(b, relationRange(r))) |- in(b, setIntersection(relationRange(r), y))) by Cut(
      lastStep,
      setIntersectionIntro of (z := b, x := relationRange(r))
    )
    have((in(pair(a, b), relationRestriction(r, x, y)), in(pair(a, b), r)) |- in(b, setIntersection(relationRange(r), y))) by Cut(relationRangeIntroPair, lastStep)
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
    have(
      (relation(r), in(p, r), in(secondInPair(p), relationRange(r))) |-
        in(p, relationRestriction(r, relationDomain(r), relationRange(r)))
    ) by Cut(relationDomainIntro, relationRestrictionIntro of (x := relationDomain(r), y := relationRange(r)))
    have((relation(r), in(p, r)) |- in(p, relationRestriction(r, relationDomain(r), relationRange(r)))) by
      Cut(relationRangeIntro, lastStep)
    thenHave(relation(r) |- in(p, r) ==> in(p, relationRestriction(r, relationDomain(r), relationRange(r)))) by RightImplies
    thenHave(relation(r) |- forall(p, in(p, r) ==> in(p, relationRestriction(r, relationDomain(r), relationRange(r))))) by RightForall
    have(relation(r) |- subset(r, relationRestriction(r, relationDomain(r), relationRange(r)))) by
      Cut(lastStep, subsetIntro of (x := r, y := relationRestriction(r, relationDomain(r), relationRange(r))))
    have((relation(r), subset(relationRestriction(r, relationDomain(r), relationRange(r)), r)) |- relationRestriction(r, relationDomain(r), relationRange(r)) === r) by
      Cut(lastStep, subsetAntisymmetry of (x := relationRestriction(r, relationDomain(r), relationRange(r)), y := r))
    have(thesis) by
      Cut(relationRestrictionSubset of (r := r, x := relationDomain(r), y := relationRange(r)), lastStep)
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

  val relationRestrictionSupersetRange = Lemma(
    (relation(r), subset(relationRange(r), y)) |- relationRestriction(r, x, y) === relationRestriction(r, x, relationRange(r))
  ) {
    val forward = have(relation(r) |- in(p, relationRestriction(r, x, y)) ==> in(p, relationRestriction(r, x, relationRange(r)))) subproof {
      have((relation(r), in(p, r), in(firstInPair(p), x)) |- in(p, relationRestriction(r, x, relationRange(r)))) by Cut(relationRangeIntro, relationRestrictionIntro of (y := relationRange(r)))
      have((relation(r), in(p, relationRestriction(r, x, y)), in(firstInPair(p), x)) |- in(p, relationRestriction(r, x, relationRange(r)))) by Cut(relationRestrictionInRelation, lastStep)
      thenHave((relation(r), in(p, relationRestriction(r, x, y)), in(firstInPair(p), x) /\ in(secondInPair(p), y)) |- in(p, relationRestriction(r, x, relationRange(r)))) by LeftAnd
      have((relation(r), in(p, relationRestriction(r, x, y))) |- in(p, relationRestriction(r, x, relationRange(r)))) by Cut(relationRestrictionInRestrictedDomains, lastStep)
    }
    val backward = have((relation(r), subset(relationRange(r), y)) |- in(p, relationRestriction(r, x, relationRange(r))) ==> in(p, relationRestriction(r, x, y))) subproof {
      have((relation(r), subset(relationRange(r), y), in(p, r), in(firstInPair(p), x), in(secondInPair(p), relationRange(r))) |- in(p, relationRestriction(r, x, y))) by Cut(subsetElim of (z := secondInPair(p), x := relationRange(r)), relationRestrictionIntro)
      have((relation(r), subset(relationRange(r), y), in(p, relationRestriction(r, x, relationRange(r))), in(firstInPair(p), x), in(secondInPair(p), relationRange(r))) |- in(p, relationRestriction(r, x, y))) by Cut(relationRestrictionInRelation of (y := relationRange(r)), lastStep)
      thenHave((relation(r), subset(relationRange(r), y), in(p, relationRestriction(r, x, relationRange(r))), in(firstInPair(p), x) /\ in(secondInPair(p), relationRange(r))) |- in(p, relationRestriction(r, x, y))) by LeftAnd
      have((relation(r), subset(relationRange(r), y), in(p, relationRestriction(r, x, relationRange(r)))) |- in(p, relationRestriction(r, x, y))) by Cut(relationRestrictionInRestrictedDomains of (y := relationRange(r)), lastStep)
    }
    have((relation(r), subset(relationRange(r), y)) |- in(p, relationRestriction(r, x, y)) <=> in(p, relationRestriction(r, x, relationRange(r)))) by
      RightIff(forward, backward)
    thenHave((relation(r), subset(relationRange(r), y)) |- forall(p, in(p, relationRestriction(r, x, y)) <=> in(p, relationRestriction(r, x, relationRange(r))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, x, y), y := relationRestriction(r, x, relationRange(r))))
  }

  val relationRestrictionSupersetDomain = Lemma(
    (relation(r), subset(relationDomain(r), x)) |- relationRestriction(r, x, y) === relationRestriction(r, relationDomain(r), y)
  ) {
    val forward = have(relation(r) |- in(p, relationRestriction(r, x, y)) ==> in(p, relationRestriction(r, relationDomain(r), y))) subproof {
      have((relation(r), in(p, r), in(secondInPair(p), y)) |- in(p, relationRestriction(r, relationDomain(r), y))) by Cut(relationDomainIntro, relationRestrictionIntro of (x := relationDomain(r)))
      have((relation(r), in(p, relationRestriction(r, x, y)), in(secondInPair(p), y)) |- in(p, relationRestriction(r, relationDomain(r), y))) by Cut(relationRestrictionInRelation, lastStep)
      thenHave((relation(r), in(p, relationRestriction(r, x, y)), in(firstInPair(p), x) /\ in(secondInPair(p), y)) |- in(p, relationRestriction(r, relationDomain(r), y))) by LeftAnd
      have((relation(r), in(p, relationRestriction(r, x, y))) |- in(p, relationRestriction(r, relationDomain(r), y))) by Cut(relationRestrictionInRestrictedDomains, lastStep)
    }
    val backward = have((relation(r), subset(relationDomain(r), x)) |- in(p, relationRestriction(r, relationDomain(r), y)) ==> in(p, relationRestriction(r, x, y))) subproof {
      have((relation(r), subset(relationDomain(r), x), in(p, r), in(firstInPair(p), relationDomain(r)), in(secondInPair(p), y)) |- in(p, relationRestriction(r, x, y))) by Cut(subsetElim of (z := firstInPair(p), x := relationDomain(r), y := x), relationRestrictionIntro)
      have((relation(r), subset(relationDomain(r), x), in(p, relationRestriction(r, relationDomain(r), y)), in(firstInPair(p), relationDomain(r)), in(secondInPair(p), y)) |- in(p, relationRestriction(r, x, y))) by Cut(relationRestrictionInRelation of (x := relationDomain(r)), lastStep)
      thenHave((relation(r), subset(relationDomain(r), x), in(p, relationRestriction(r, relationDomain(r), y)), in(firstInPair(p), relationDomain(r)) /\ in(secondInPair(p), y)) |- in(p, relationRestriction(r, x, y))) by LeftAnd
      have((relation(r), subset(relationDomain(r), x), in(p, relationRestriction(r, relationDomain(r), y))) |- in(p, relationRestriction(r, x, y))) by Cut(relationRestrictionInRestrictedDomains of (x := relationDomain(r)), lastStep)
    }
    have((relation(r), subset(relationDomain(r), x)) |- in(p, relationRestriction(r, x, y)) <=> in(p, relationRestriction(r, relationDomain(r), y))) by
      RightIff(forward, backward)
    thenHave((relation(r), subset(relationDomain(r), x)) |- forall(p, in(p, relationRestriction(r, x, y)) <=> in(p, relationRestriction(r, relationDomain(r), y)))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := relationRestriction(r, x, y), y := relationRestriction(r, relationDomain(r), y)))
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
    have((in(pair(a, b), f), in(a, x), in(b, relationRange(f))) |- in(pair(a, b), domainRestriction(f, x))) by Substitution.ApplyRules(domainRestriction.shortDefinition)(
      relationRestrictionIntroPair of (r := f, y := relationRange(f))
    )
    have(thesis) by Cut(relationRangeIntroPair of (r := f), lastStep)
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

  val domainRestrictionIsRelation = Lemma(
    relation(domainRestriction(f, x))
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionIsRelation of (r := f, x := x, y := relationRange(f)))
  }

  /**
    * Lemma --- Domain of domain restriction of a relation
    * 
    *    `Dom(f|x) = Dom(f) ∩ x`
    */
  val domainRestrictionDomain = Lemma(
    relationDomain(domainRestriction(f, x)) === setIntersection(relationDomain(f), x)
  ) {
    val forward = have(subset(relationDomain(domainRestriction(f, x)), setIntersection(relationDomain(f), x))) by Substitution.ApplyRules(domainRestriction.shortDefinition)(
      relationRestrictionDomain of (r := f, y := relationRange(f))
    )
    val backward = have(subset(setIntersection(relationDomain(f), x), relationDomain(domainRestriction(f, x)))) subproof {
      have((in(pair(a, b), f), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(domainRestrictionIntro, relationDomainIntroPair of (r := domainRestriction(f, x)))
      thenHave((exists(b, in(pair(a, b), f)), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by LeftExists
      have((in(a, relationDomain(f)), in(a, x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(relationDomainElim of (r := f), lastStep)
      thenHave(in(a, relationDomain(f)) /\ in(a, x) |- in(a, relationDomain(domainRestriction(f, x)))) by LeftAnd
      have(in(a, setIntersection(relationDomain(f), x)) |- in(a, relationDomain(domainRestriction(f, x)))) by Cut(setIntersectionElim of (z := a, x := relationDomain(f), y := x), lastStep)
      thenHave(in(a, setIntersection(relationDomain(f), x)) ==> in(a, relationDomain(domainRestriction(f, x)))) by RightImplies
      thenHave(forall(a, in(a, setIntersection(relationDomain(f), x)) ==> in(a, relationDomain(domainRestriction(f, x))))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := setIntersection(relationDomain(f), x), y := relationDomain(domainRestriction(f, x))))
    }
    have(subset(setIntersection(relationDomain(f), x), relationDomain(domainRestriction(f, x))) |- relationDomain(domainRestriction(f, x)) === setIntersection(relationDomain(f), x)) by 
      Cut(forward, subsetAntisymmetry of (x := relationDomain(domainRestriction(f, x)), y := setIntersection(relationDomain(f), x)))
    have(thesis) by Cut(backward, lastStep)
  }

  val domainRestrictionOnDomain = Lemma(
    relation(f) |- domainRestriction(f, relationDomain(f)) === f
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition)(relationRestrictionOnDomainRange of (r := f))
  }

  val domainRestrictionDisjoint = Lemma(
    disjoint(relationDomain(f), x) |- domainRestriction(f, x) === emptySet
  ) {
    have(disjoint(relationDomain(f), x) |- relationDomain(domainRestriction(f, x)) === emptySet) by 
      Substitution.ApplyRules(disjointUnfold of (x := relationDomain(f), y := x))(domainRestrictionDomain)
    have((relation(domainRestriction(f, x)), disjoint(relationDomain(f), x)) |- domainRestriction(f, x) === emptySet) by Cut(lastStep, relationDomainEmpty of (r := domainRestriction(f, x)))
    have(thesis) by Cut(domainRestrictionIsRelation of (r := f), lastStep)
  }

  val domainRestrictionSetUnion = Lemma(
    (relation(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))
  ) {
    have(domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(setUnion(f, g))), relationRestriction(g, x, relationRange(setUnion(f, g))))) by
      Substitution.ApplyRules(domainRestriction.shortDefinition of (f := setUnion(f, g)))(relationRestrictionSetUnion of (r1 := f, r2 := g, y := relationRange(setUnion(f, g))))
    thenHave(
      (relation(f), subset(relationRange(f), relationRange(setUnion(f, g)))) |-
        domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(setUnion(f, g))))
    ) by
      Substitution.ApplyRules(relationRestrictionSupersetRange of (r := f, y := relationRange(setUnion(f, g))))
    have(
      (relation(f), subset(f, setUnion(f, g))) |- domainRestriction(setUnion(f, g), x) === setUnion(
        relationRestriction(f, x, relationRange(f)),
        relationRestriction(g, x, relationRange(setUnion(f, g)))
      )
    ) by
      Cut(relationRangeSubset of (r1 := f, r2 := setUnion(f, g)), lastStep)
    have(relation(f) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(setUnion(f, g))))) by
      Cut(setUnionLeftSubset of (a := f, b := g), lastStep)
    thenHave(
      (relation(f), relation(g), subset(relationRange(g), relationRange(setUnion(f, g)))) |-
        domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(g)))
    ) by
      Substitution.ApplyRules(relationRestrictionSupersetRange of (r := g, y := relationRange(setUnion(f, g))))
    have(
      (relation(f), relation(g), subset(g, setUnion(f, g))) |- domainRestriction(setUnion(f, g), x) === setUnion(
        relationRestriction(f, x, relationRange(f)),
        relationRestriction(g, x, relationRange(g))
      )
    ) by
      Cut(relationRangeSubset of (r1 := g, r2 := setUnion(f, g)), lastStep)
    have((relation(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(relationRestriction(f, x, relationRange(f)), relationRestriction(g, x, relationRange(g)))) by
      Cut(setUnionRightSubset of (a := f, b := g), lastStep)
    thenHave(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition, domainRestriction.shortDefinition of (x := g))
  }

  val domainRestrictionSetUnionDomain = Lemma(
    domainRestriction(f, setUnion(x, y)) === setUnion(domainRestriction(f, x), domainRestriction(f, y))
  ) {
    have(thesis) by Substitution.ApplyRules(domainRestriction.shortDefinition, domainRestriction.shortDefinition of (x := y), domainRestriction.shortDefinition of (x := setUnion(x, y)))(
      relationRestrictionSetUnionDomain of (r := f, z := relationRange(f))
    )
  }

  /**
   * Properties of relations
   */

  /**
   * Reflexive Relation --- `∀ x. x R x`
   */
  val reflexive = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, in(y, x) ==> in(pair(y, y), r))

  val reflexiveIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, in(y, x) ==> in(pair(y, y), r))) |- reflexive(r, x)
  ) {
    have(thesis) by Weakening(reflexive.definition)
  }

  val reflexiveElim = Lemma(
    (reflexive(r, x), in(y, x)) |- in(pair(y, y), r)
  ) {
    have(reflexive(r, x) |- ∀(y, in(y, x) ==> in(pair(y, y), r))) by Weakening(reflexive.definition)
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
    reflexive(emptySet, emptySet)
  ) {
    have(in(y, emptySet) ==> in(pair(y, y), emptySet)) by Weakening(emptySetAxiom of (x := y))
    thenHave(forall(y, in(y, emptySet) ==> in(pair(y, y), emptySet))) by RightForall
    have(relationBetween(emptySet, emptySet, emptySet) |- reflexive(emptySet, emptySet)) by Cut(lastStep, reflexiveIntro of (r := emptySet, x := emptySet))
    have(thesis) by Cut(emptySetRelationOnItself, lastStep)
  }


  /**
   * Symmetric Relation --- `∀ x y. x R y ⇔ y R x`
   */
  val symmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r)))

  val symmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r)))) |- symmetric(r, x)
  ) {
    have(thesis) by Weakening(symmetric.definition)
  }

  val symmetricElim = Lemma(
    (symmetric(r, x), in(pair(y, z), r)) |- in(pair(z, y), r)
  ) {
    have(symmetric(r, x) |- ∀(y, ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r)))) by Weakening(symmetric.definition)
    thenHave(symmetric(r, x) |- ∀(z, in(pair(y, z), r) <=> in(pair(z, y), r))) by InstantiateForall(y)
    thenHave(symmetric(r, x) |- in(pair(y, z), r) <=> in(pair(z, y), r)) by InstantiateForall(z)
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
    symmetric(emptySet, x)
  ) {
    val forward = have(in(pair(y, z), emptySet) ==> in(pair(z, y), emptySet)) by Weakening(emptySetAxiom of (x := pair(y, z)))
    val backward = have(in(pair(z, y), emptySet) ==> in(pair(y, z), emptySet)) by Weakening(emptySetAxiom of (x := pair(z, y)))
    have(in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)) by RightIff(forward, backward)
    thenHave(forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet))) by RightForall
    thenHave(forall(y, forall(z, in(pair(y, z), emptySet) <=> in(pair(z, y), emptySet)))) by RightForall
    have(relationBetween(emptySet, x, x) |- symmetric(emptySet, x)) by Cut(lastStep, symmetricIntro of (r := emptySet))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

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
      Cut(transitiveElim of (w := a, y := b, z := c), relationRestrictionIntroPair of (b := c, x := y))
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
   * Lemma --- the empty relation is transitive.
   */
  val emptyRelationTransitive = Lemma(
    transitive(emptySet, x)
  ) {
    have((in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)) by Weakening(emptySetAxiom of (x := pair(w, y)))
    thenHave(forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))) by RightForall
    thenHave(forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet)))) by RightForall
    thenHave(forall(w, forall(y, forall(z, (in(pair(w, y), emptySet) /\ in(pair(y, z), emptySet)) ==> in(pair(w, z), emptySet))))) by RightForall
    have(relationBetween(emptySet, x, x) |- transitive(emptySet, x)) by Cut(lastStep, transitiveIntro of (r := emptySet))
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
    equivalence(emptySet, emptySet)
  ) {
    have((symmetric(emptySet, emptySet), transitive(emptySet, emptySet)) |- equivalence(emptySet, emptySet)) by Cut(emptyRelationReflexiveOnItself, equivalenceIntro of (r := emptySet, x := emptySet))
    have(transitive(emptySet, emptySet) |- equivalence(emptySet, emptySet)) by Cut(emptyRelationSymmetric of (x := emptySet), lastStep)
    have(thesis) by Cut(emptyRelationTransitive of (x := emptySet), lastStep)
  }

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
   * Lemma --- the empty relation is irreflexive.
   */
  val emptyRelationIrreflexive = Lemma(
    irreflexive(emptySet, x)
  ) {
    have(in(y, x) ==> !in(pair(y, y), emptySet)) by Weakening(emptySetAxiom of (x := pair(y, y)))
    thenHave(forall(y, in(y, x) ==> !in(pair(y, y), emptySet))) by RightForall
    have(relationBetween(emptySet, x, x) |- irreflexive(emptySet, x)) by Cut(lastStep, antiReflexiveIntro of (r := emptySet))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Anti-symmetric Relation --- `∀ x y. x R y ∧ y R x ⇒ y = x`
   */
  val antiSymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))

  val antiSymmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))) |- antiSymmetric(r, x)
  ) {
    have(thesis) by Weakening(antiSymmetric.definition)
  }

  val antiSymmetricElim = Lemma(
    (antiSymmetric(r, x), in(pair(y, z), r), in(pair(z, y), r)) |- y === z
  ) {
    have(antiSymmetric(r, x) |- ∀(y, ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z)))) by Weakening(antiSymmetric.definition)
    thenHave(antiSymmetric(r, x) |- ∀(z, (in(pair(y, z), r) /\ in(pair(z, y), r)) ==> (y === z))) by InstantiateForall(y)
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
    antiSymmetric(emptySet, x)
  ) {
    have((in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)) by Weakening(emptySetAxiom of (x := pair(y, z)))
    thenHave(forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z))) by RightForall
    thenHave(forall(y, forall(z, (in(pair(y, z), emptySet) /\ in(pair(z, y), emptySet)) ==> (y === z)))) by RightForall
    have(relationBetween(emptySet, x, x) |- antiSymmetric(emptySet, x)) by Cut(lastStep, antiSymmetricIntro of (r := emptySet))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

  /**
   * Asymmetric Relation --- `∀ x y. x R y ⇔ ! y R x`
   */
  val asymmetric = DEF(r, x) --> relationBetween(r, x, x) /\ ∀(y, ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))

  val asymmetricIntro = Lemma(
    (relationBetween(r, x, x), ∀(y, ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))) |- asymmetric(r, x)
  ) {
    have(thesis) by Weakening(asymmetric.definition)
  }

  val asymmetricElim = Lemma(
    (asymmetric(r, x), in(pair(y, z), r)) |- !in(pair(z, y), r)
  ) {
    have(asymmetric(r, x) |- ∀(y, ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r)))) by Weakening(asymmetric.definition)
    thenHave(asymmetric(r, x) |- ∀(z, in(pair(y, z), r) ==> !in(pair(z, y), r))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  val asymmetricRelationIsRelation = Lemma(
    asymmetric(r, x) |- relationBetween(r, x, x)
  ) {
    have(thesis) by Weakening(asymmetric.definition)
  }

  /**
   * Lemma --- the empty relation is asymmetric.
   */
  val emptyRelationAsymmetric = Lemma(
    asymmetric(emptySet, x)
  ) {
    have(in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)) by Weakening(emptySetAxiom of (x := pair(y, z)))
    thenHave(forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet))) by RightForall
    thenHave(forall(y, forall(z, in(pair(y, z), emptySet) ==> !in(pair(z, y), emptySet)))) by RightForall
    have(relationBetween(emptySet, x, x) |- asymmetric(emptySet, x)) by Cut(lastStep, asymmetricIntro of (r := emptySet))
    have(thesis) by Cut(emptySetRelation of (a := x, b := x), lastStep)
  }

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
   * Lemma --- the empty relation is total on the empty set.
   */
  val emptyRelationTotalOnItself = Lemma(
    connected(emptySet, emptySet)
  ) {
    have((in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))) by Weakening(emptySetAxiom of (x := y))
    thenHave(forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z)))) by RightForall
    thenHave(forall(y, forall(z, (in(y, emptySet) /\ in(z, emptySet)) ==> (in(pair(y, z), emptySet) \/ in(pair(z, y), emptySet) \/ (y === z))))) by RightForall
    have(relationBetween(emptySet, emptySet, emptySet) |- connected(emptySet, emptySet)) by Cut(lastStep, connectedIntro of (r := emptySet, x := emptySet))
    have(thesis) by Cut(emptySetRelationOnItself, lastStep)
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
      relationRestrictionIntroPair of (x := y)
    )
    val right = have((in(pair(b, a), r), in(a, y), in(b, y)) |- in(pair(a, b), relationRestriction(r, y, y)) \/ in(pair(b, a), relationRestriction(r, y, y)) \/ (a === b)) by Weakening(
      relationRestrictionIntroPair of (x := y, a := b, b := a)
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



}
