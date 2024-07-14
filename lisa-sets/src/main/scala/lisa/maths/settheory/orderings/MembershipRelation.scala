package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Relations.*
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
    ∃!(z, ∀(t, t ∈ z <=> (t ∈ (x × x) /\ ∃(a, ∃(b, a ∈ b /\ (t === pair(a, b)))))))
  ) {
    have(thesis) by UniqueComprehension(x × x, lambda(t, ∃(a, ∃(b, a ∈ b /\ (t === pair(a, b))))))
  }

  /**
   * Definition --- The relation induced by membership on a set
   *
   *    `∈_x = {(a, b) ∈ x * x | a ∈ b}`
   */
  val membershipRelation = DEF(x) --> The(z, ∀(t, t ∈ z <=> (t ∈ (x × x) /\ ∃(a, ∃(b, a ∈ b /\ (t === pair(a, b)))))))(membershipRelationUniqueness)

  /**
   * Theorem --- The membership relation is a relation.
   * 
   *   `∈_x ⊆ x × x`
   */
  val membershipRelationIsARelation = Lemma(relationBetween(membershipRelation(x), x, x)) {
    have(∀(t, t ∈ membershipRelation(x) <=> (t ∈ (x × x) /\ ∃(y, ∃(x, y ∈ x /\ (t === pair(y, x))))))) by InstantiateForall(membershipRelation(x))(membershipRelation.definition)
    thenHave(t ∈ membershipRelation(x) <=> (t ∈ (x × x) /\ ∃(y, ∃(x, y ∈ x /\ (t === pair(y, x)))))) by InstantiateForall(t)
    thenHave(t ∈ membershipRelation(x) ==> t ∈ (x × x)) by Weakening
    thenHave(∀(t, t ∈ membershipRelation(x) ==> t ∈ (x × x))) by RightForall
    have(membershipRelation(x) ⊆ (x × x)) by Cut(lastStep, subsetIntro of (x := membershipRelation(x), y := x × x))
    thenHave(thesis) by Substitution.ApplyRules(relationBetween.definition of (r := membershipRelation(x), a := x, b := x))
  }

  /**
   * Theorem --- Definition of elements of the membership relation
   * 
   *    `(a, b) ∈ ∈_x <=> a ∈ x ∧ b ∈ x ∧ a ∈ b`
   */
  val membershipRelationElemPair = Lemma(
    pair(a, b) ∈ membershipRelation(x) <=> (a ∈ x /\ b ∈ x /\ a ∈ b)
  ) {
    val pairExists = have(a ∈ b <=> ∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z))))) subproof {
      val forward = have(a ∈ b ==> ∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z))))) subproof {
        have(a ∈ b |- a ∈ b /\ (pair(a, b) === pair(a, b))) by Restate
        thenHave(a ∈ b |- ∃(z, a ∈ z /\ (pair(a, b) === pair(a, z)))) by RightExists
        thenHave(a ∈ b |- ∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z))))) by RightExists
      }
      val backward = have(∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z)))) ==> a ∈ b) subproof {
        have(y ∈ z |- y ∈ z) by Hypothesis
        thenHave((y ∈ z, a === y, b === z) |- a ∈ b) by RightSubstEq.withParametersSimple(List((y, a), (z, b)), lambda((y, z), y ∈ z))
        thenHave((y ∈ z, (a === y) /\ (b === z)) |- a ∈ b) by LeftAnd
        thenHave((y ∈ z, pair(a, b) === pair(y, z)) |- a ∈ b) by Substitution.ApplyRules(pairExtensionality of (c := y, d := x))
        thenHave(y ∈ z /\ (pair(a, b) === pair(y, z)) |- a ∈ b) by LeftAnd
        thenHave(∃(z, y ∈ z /\ (pair(a, b) === pair(y, z))) |- a ∈ b) by LeftExists
        thenHave(∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z)))) |- a ∈ b) by LeftExists
      }

      have(thesis) by RightIff(forward, backward)
    }

    have(∀(t, t ∈ membershipRelation(x) <=> (t ∈ (x × x) /\ ∃(y, ∃(z, y ∈ z /\ (t === pair(y, z))))))) by InstantiateForall(membershipRelation(x))(membershipRelation.definition)
    thenHave(pair(a, b) ∈ membershipRelation(x) <=> (pair(a, b) ∈ (x × x) /\ ∃(y, ∃(z, y ∈ z /\ (pair(a, b) === pair(y, z)))))) by InstantiateForall(pair(a, b))
    thenHave(pair(a, b) ∈ membershipRelation(x) <=> (pair(a, b) ∈ (x × x)) /\ a ∈ b) by Substitution.ApplyRules(pairExists)
    thenHave(thesis) by Substitution.ApplyRules(cartesianProductMembershipPair of (y := x))
  }

  /**
    * Theorem --- Membership relation introduction rule
    * 
    *    `a ∈ x, b ∈ x, b ∈ x ⊢ (a, b) ∈ ∈_x`
    */
  val membershipRelationIntro = Lemma((a ∈ x, b ∈ x, a ∈ b) |- pair(a, b) ∈ membershipRelation(x)) {
    have(thesis) by Weakening(membershipRelationElemPair)
  }

  /**
    * Theorem --- Membership relation elimination rule (for pairs)
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ b /\ a ∈ x /\ b ∈ x`
    */
  val membershipRelationElimPair = Lemma(pair(a, b) ∈ membershipRelation(x) |- a ∈ b /\ a ∈ x /\ b ∈ x){
    have(thesis) by Weakening(membershipRelationElemPair)
  }

  /**
    * Theorem --- Membership relation represents membership (for pairs)
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ b`
    */
  val membershipRelationIsMembershipPair = Lemma(pair(a, b) ∈ membershipRelation(x) |- a ∈ b){
    have(thesis) by Weakening(membershipRelationElimPair)
  }

  /**
    * Theorem --- Pairs of elememts of the membership relation are in their respective domains
    * 
    *   `(a, b) ∈ ∈_x ⊢ a ∈ x /\ b ∈ x`
    */
  val membershipRelationInDomainPair = Lemma(pair(a, b) ∈ membershipRelation(x) |- a ∈ x /\ b ∈ x){
    have(thesis) by Weakening(membershipRelationElimPair)
  }

  /**
    * Theorem --- Membership relation elimination rule
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ p._2 /\ p._1 ∈ x /\ p._2 ∈ x`
    */
  val membershipRelationElim = Lemma(p ∈ membershipRelation(x) |- fst(p) ∈ snd(p) /\ fst(p) ∈ x /\ snd(p) ∈ x){
    have(p ∈ membershipRelation(x) |- p === pair(fst(p), snd(p))) by Cut(membershipRelationIsARelation, pairReconstructionInRelationBetween of (r := membershipRelation(x), a := x, b := x))
    have(thesis) by Substitution.ApplyRules(lastStep)(membershipRelationElimPair of (a := fst(p), b := snd(p)))
  }

  /**
    * Theorem --- Membership relation represents membership
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ p._2`
    */
  val membershipRelationIsMembership = Lemma(p ∈ membershipRelation(x) |- fst(p) ∈ snd(p)){
    have(thesis) by Weakening(membershipRelationElim)
  }

  /**
    * Theorem --- Elements of the membership relation are in their respective domains
    * 
    *   `p ∈ ∈_x ⊢ p._1 ∈ x /\ p._2 ∈ x`
    */
  val membershipRelationInDomain = Lemma(p ∈ membershipRelation(x) |- fst(p) ∈ x /\ snd(p) ∈ x){
    have(thesis) by Weakening(membershipRelationElim)
  }

  /**
    * Theorem --- The membership relation is irreflexive
    * 
    *  `∀a ∈ x. (a, a) ∉ ∈_x`
    */
  val membershipRelationIrreflexive = Lemma(antiReflexive(membershipRelation(x), x)) {
    have(pair(y, y) ∈ membershipRelation(x) |- y ∈ y) by Weakening(membershipRelationElemPair of (a := y, b := y))
    have(pair(y, y) ∈ membershipRelation(x) |- ()) by RightAnd(lastStep, selfNonMembership of (x := y))
    thenHave(pair(y, y) ∉ membershipRelation(x)) by RightNot
    thenHave(∀(y, pair(y, y) ∉ membershipRelation(x))) by RightForall
    have(relationBetween(membershipRelation(x), x, x) |- antiReflexive(membershipRelation(x), x)) by Cut(lastStep, antiReflexiveIntro of (r := membershipRelation(x)))
    have(thesis) by Cut(membershipRelationIsARelation, lastStep)
  }


  /**
   * Theorem --- The membership relation on the empty set is the empty set
   * 
   *  `∈_∅ = ∅`
   */
  val emptyMembershipRelation = Lemma(membershipRelation(∅) === ∅) {
    have(p ∈ membershipRelation(∅) |- fst(p) ∈ ∅) by Weakening(membershipRelationInDomain of (x := ∅))
    have(p ∈ membershipRelation(∅) |- ∅ =/= ∅) by Cut(lastStep, setWithElementNonEmpty of (y := fst(p), x := ∅))
    thenHave(p ∉ membershipRelation(∅)) by Restate
    thenHave(∀(p, p ∉ membershipRelation(∅))) by RightForall
    have(thesis) by Cut(lastStep, setWithNoElementsIsEmpty of (x := membershipRelation(∅)))
  }
}
