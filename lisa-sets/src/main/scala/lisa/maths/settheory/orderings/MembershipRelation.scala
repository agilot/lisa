package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.orderings.PartialOrders.*

object MembershipRelation extends lisa.Main {

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
    * Theorem --- Uniqueness of the membership relation
    * 
    *     `∃!r. ∀t. t ∈ r ⇔ (t ∈ x × x ∧ ∃a. ∃b. a ∈ b ∧ t = (a, b))`
    */
  val membershipRelationUniqueness = Lemma(
    existsOne(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(x, x)) /\ exists(a, exists(b, in(a, b) /\ (t === pair(a, b)))))))
  ) {
    have(thesis) by UniqueComprehension(cartesianProduct(x, x), lambda(t, exists(a, exists(b, in(a, b) /\ (t === pair(a, b))))))
  }

  /**
   * Definition --- The relation induced by membership on a set
   *
   *    `∈_x = {(a, b) ∈ x * x | a ∈ b}`
   */
  val membershipRelation = DEF(x) --> The(z, forall(t, in(t, z) <=> (in(t, cartesianProduct(x, x)) /\ exists(a, exists(b, in(a, b) /\ (t === pair(a, b)))))))(membershipRelationUniqueness)

  /**
   * Theorem --- The membership relation is a relation.
   * 
   *   `∈_x ⊆ x × x`
   */
  val membershipRelationIsARelation = Lemma(relationBetween(membershipRelation(x), x, x)) {
    have(forall(t, in(t, membershipRelation(x)) <=> (in(t, cartesianProduct(x, x)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x))))))) by InstantiateForall(membershipRelation(x))(membershipRelation.definition)
    thenHave(in(t, membershipRelation(x)) <=> (in(t, cartesianProduct(x, x)) /\ exists(y, exists(x, in(y, x) /\ (t === pair(y, x)))))) by InstantiateForall(t)
    thenHave(in(t, membershipRelation(x)) ==> in(t, cartesianProduct(x, x))) by Weakening
    thenHave(forall(t, in(t, membershipRelation(x)) ==> in(t, cartesianProduct(x, x)))) by RightForall
    have(subset(membershipRelation(x), cartesianProduct(x, x))) by Cut(lastStep, subsetIntro of (x -> membershipRelation(x), y -> cartesianProduct(x, x)))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r -> membershipRelation(x), a -> x, b -> x))
  }

  /**
   * Theorem --- Definition of elements of the membership relation
   * 
   *    `(a, b) ∈ ∈_x <=> a ∈ x ∧ b ∈ x ∧ a ∈ b`
   */
  val membershipRelationElemPair = Lemma(
    in(pair(a, b), membershipRelation(x)) <=> (in(a, x) /\ in(b, x) /\ in(a, b))
  ) {
    val pairExists = have(in(a, b) <=> exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z))))) subproof {
      val forward = have(in(a, b) ==> exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z))))) subproof {
        have(in(a, b) |- in(a, b) /\ (pair(a, b) === pair(a, b))) by Restate
        thenHave(in(a, b) |- exists(z, in(a, z) /\ (pair(a, b) === pair(a, z)))) by RightExists
        thenHave(in(a, b) |- exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z))))) by RightExists
      }
      val backward = have(exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z)))) ==> in(a, b)) subproof {
        have(in(y, z) |- in(y, z)) by Hypothesis
        thenHave((in(y, z), a === y, b === z) |- in(a, b)) by RightSubstEq.withParametersSimple(List((y, a), (z, b)), lambda((y, z), in(y, z)))
        thenHave((in(y, z), (a === y) /\ (b === z)) |- in(a, b)) by LeftAnd
        thenHave((in(y, z), pair(a, b) === pair(y, z)) |- in(a, b)) by Substitution.ApplyRules(pairExtensionality of (c -> y, d -> x))
        thenHave(in(y, z) /\ (pair(a, b) === pair(y, z)) |- in(a, b)) by LeftAnd
        thenHave(exists(z, in(y, z) /\ (pair(a, b) === pair(y, z))) |- in(a, b)) by LeftExists
        thenHave(exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z)))) |- in(a, b)) by LeftExists
      }

      have(thesis) by RightIff(forward, backward)
    }

    have(forall(t, in(t, membershipRelation(x)) <=> (in(t, cartesianProduct(x, x)) /\ exists(y, exists(z, in(y, z) /\ (t === pair(y, z))))))) by InstantiateForall(membershipRelation(x))(membershipRelation.definition)
    thenHave(in(pair(a, b), membershipRelation(x)) <=> (in(pair(a, b), cartesianProduct(x, x)) /\ exists(y, exists(z, in(y, z) /\ (pair(a, b) === pair(y, z)))))) by InstantiateForall(pair(a, b))
    thenHave(in(pair(a, b), membershipRelation(x)) <=> (in(pair(a, b), cartesianProduct(x, x)) /\ in(a, b))) by Substitution.ApplyRules(pairExists)
    thenHave(thesis) by Substitution.ApplyRules(cartesianProductMembershipPair of (y -> x))
  }

  /**
    * Theorem --- Membership relation introduction rule
    * 
    *    `a ∈ x, b ∈ x, b ∈ x ⊢ (a, b) ∈ ∈_x`
    */
  val membershipRelationIntro = Lemma((in(a, x), in(b, x), in(a, b)) |- in(pair(a, b), membershipRelation(x))) {
    have(thesis) by Weakening(membershipRelationElemPair)
  }

  /**
    * Theorem --- Membership relation elimination rule (for pairs)
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ b /\ a ∈ x /\ b ∈ x`
    */
  val membershipRelationElimPair = Lemma(in(pair(a, b), membershipRelation(x)) |- in(a, b) /\ in(a, x) /\ in(b, x)){
    have(thesis) by Weakening(membershipRelationElemPair)
  }

  /**
    * Theorem --- Membership relation represents membership (for pairs)
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ b`
    */
  val membershipRelationIsMembershipPair = Lemma(in(pair(a, b), membershipRelation(x)) |- in(a, b)){
    have(thesis) by Weakening(membershipRelationElimPair)
  }

  /**
    * Theorem --- Pairs of elememts of the membership relation are in their respective domains
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ x /\ b ∈ x`
    */
  val membershipRelationInDomainPair = Lemma(in(pair(a, b), membershipRelation(x)) |- in(a, x) /\ in(b, x)){
    have(thesis) by Weakening(membershipRelationElimPair)
  }

  /**
    * Theorem --- Membership relation elimination rule
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ p._2 /\ p._1 ∈ x /\ p._2 ∈ x`
    */
  val membershipRelationElim = Lemma(in(p, membershipRelation(x)) |- in(firstInPair(p), secondInPair(p)) /\ in(firstInPair(p), x) /\ in(secondInPair(p), x)){
    have(in(p, membershipRelation(x)) |- p === pair(firstInPair(p), secondInPair(p))) by Cut(membershipRelationIsARelation, pairReconstructionInRelationBetween of (r -> membershipRelation(x), a -> x, b -> x))
    have(thesis) by Substitution.ApplyRules(lastStep)(membershipRelationElimPair of (a -> firstInPair(p), b -> secondInPair(p)))
  }

  /**
    * Theorem --- Membership relation represents membership
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ p._2`
    */
  val membershipRelationIsMembership = Lemma(in(p, membershipRelation(x)) |- in(firstInPair(p), secondInPair(p))){
    have(thesis) by Weakening(membershipRelationElim)
  }

  /**
    * Theorem --- Elements of the membership relation are in their respective domains
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ x /\ p._2 ∈ x`
    */
  val membershipRelationInDomain = Lemma(in(p, membershipRelation(x)) |- in(firstInPair(p), x) /\ in(secondInPair(p), x)){
    have(thesis) by Weakening(membershipRelationElim)
  }

  /**
    * Theorem --- The membership relation is irreflexive
    * 
    *  `∀a ∈ x. (a, a) ∉ ∈_x`
    */
  val membershipRelationIrreflexive = Lemma(antiReflexive(membershipRelation(x), x)) {
    have(in(pair(y, y), membershipRelation(x)) |- in(y, y)) by Weakening(membershipRelationElemPair of (a -> y, b -> y))
    have(in(pair(y, y), membershipRelation(x)) |- in(y, y) /\ !in(y, y)) by RightAnd(lastStep, selfNonInclusion of (x -> y))
    thenHave(in(y, x) ==> !in(pair(y, y), membershipRelation(x))) by Weakening
    thenHave(∀(y, in(y, x) ==> !in(pair(y, y), membershipRelation(x)))) by RightForall
    have(relationBetween(membershipRelation(x), x, x) /\ ∀(y, in(y, x) ==> !in(pair(y, y), membershipRelation(x)))) by RightAnd(membershipRelationIsARelation, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(irreflexive.definition of (r -> membershipRelation(x))) 
  }


  /**
   * Theorem --- The membership relation on the empty set is the empty set
   * 
   *  `∈_∅ = ∅`
   */
  val emptyMembershipRelation = Lemma(membershipRelation(emptySet) === emptySet) {
    have(in(p, membershipRelation(emptySet)) |- in(firstInPair(p), emptySet)) by Weakening(membershipRelationInDomain of (x -> emptySet))
    have(in(p, membershipRelation(emptySet)) |- !(emptySet === emptySet)) by Cut(lastStep, setWithElementNonEmpty of (y := firstInPair(p), x := emptySet))
    thenHave(!in(p, membershipRelation(emptySet))) by Restate
    thenHave(forall(p, !in(p, membershipRelation(emptySet)))) by RightForall
    have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty of (x := membershipRelation(emptySet)))
  }
}
