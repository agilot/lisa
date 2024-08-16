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
    *     `∃!r. ∀p. p ∈ r ⇔ (p ∈ x × x ∧ fst(p) ∈ snd(p))`
    */
  val membershipRelationUniqueness = Lemma(
    ∃!(z, ∀(p, p ∈ z <=> (p ∈ (x × x) /\ fst(p) ∈ snd(p))))
  ) {
    have(thesis) by UniqueComprehension(x × x, lambda(p, fst(p) ∈ snd(p)))
  }

  /**
   * Definition --- The relation induced by membership on a set
   *
   *    `∈_x = {(a, b) ∈ x * x | a ∈ b}`
   */
  val membershipRelation = DEF(x) --> The(z, ∀(p, p ∈ z <=> (p ∈ (x × x) /\ fst(p) ∈ snd(p))))(membershipRelationUniqueness)

  val membershipRelationElem = Lemma(
    p ∈ membershipRelation(x) <=> (p ∈ (x × x) /\ fst(p) ∈ snd(p))
  ) {
    have(∀(p, p ∈ membershipRelation(x) <=> (p ∈ (x × x) /\ fst(p) ∈ snd(p)))) by InstantiateForall(membershipRelation(x))(membershipRelation.definition)
    thenHave(thesis) by InstantiateForall(p)
  }

  /**
   * Theorem --- The membership relation is a relation.
   * 
   *   `∈_x ⊆ x × x`
   */
  val membershipRelationRelationBetween = Lemma(relationBetween(membershipRelation(x), x, x)) {
    have(p ∈ membershipRelation(x) ==> p ∈ (x × x)) by Weakening(membershipRelationElem)
    thenHave(∀(p, p ∈ membershipRelation(x) ==> p ∈ (x × x))) by RightForall
    have(membershipRelation(x) ⊆ (x × x)) by Cut(lastStep, subsetIntro of (x := membershipRelation(x), y := x × x))
    have(thesis) by Cut(lastStep, relationBetweenIntro of (r := membershipRelation(x), a := x, b := x))
  }

  val membershipRelationRelation = Lemma(relation(membershipRelation(x))) {
    have(thesis) by Cut(membershipRelationRelationBetween, relationBetweenIsRelation of (r := membershipRelation(x), a := x, b := x))
  }

  

  /**
   * Theorem --- Definition of elements of the membership relation
   * 
   *    `(a, b) ∈ ∈_x <=> a ∈ x ∧ b ∈ x ∧ a ∈ b`
   */
  val membershipRelationElemPair = Lemma(
    pair(a, b) ∈ membershipRelation(x) <=> (a ∈ x /\ b ∈ x /\ a ∈ b)
  ) {
    have(thesis) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction, cartesianProductMembershipPair)(membershipRelationElem of (p := pair(a, b)))
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
    have(p ∈ membershipRelation(x) |- p === pair(fst(p), snd(p))) by Cut(membershipRelationRelationBetween, pairReconstructionInRelationBetween of (r := membershipRelation(x), a := x, b := x))
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
    have(thesis) by Cut(membershipRelationRelationBetween, lastStep)
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

  val membershipRelationSubset = Lemma(y ⊆ x |- membershipRelation(y) ⊆ membershipRelation(x)) {
    have((p ∈ (x × x), fst(p) ∈ snd(p)) |- p ∈ membershipRelation(x)) by Weakening(membershipRelationElem)
    have(((y × y) ⊆ (x × x), p ∈ (y × y), fst(p) ∈ snd(p)) |- p ∈ membershipRelation(x)) by Cut(subsetElim of (z := p, x := (y × y), y := (x × x)), lastStep)
    have((y ⊆ x, p ∈ (y × y), fst(p) ∈ snd(p)) |- p ∈ membershipRelation(x)) by Cut(cartesianProductSubset of (w := y, x := y, y := x, z := x), lastStep)
    thenHave((y ⊆ x, p ∈ (y × y) /\ fst(p) ∈ snd(p)) |- p ∈ membershipRelation(x)) by LeftAnd
    thenHave((y ⊆ x, p ∈ membershipRelation(y)) |- p ∈ membershipRelation(x)) by Substitution.ApplyRules(membershipRelationElem)
    thenHave(y ⊆ x |- p ∈ membershipRelation(y) ==> p ∈ membershipRelation(x)) by RightImplies
    thenHave(y ⊆ x |- ∀(p, p ∈ membershipRelation(y) ==> p ∈ membershipRelation(x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := membershipRelation(y), y := membershipRelation(x)))
  }

  val membershipRelationRestriction = Lemma(y ⊆ x |- membershipRelation(y) === relationRestriction(membershipRelation(x), y, y)) {
    val forward = have(y ⊆ x |- p ∈ membershipRelation(y) ==> p ∈ relationRestriction(membershipRelation(x), y, y)) subproof {
      have((relation(membershipRelation(x)), p ∈ membershipRelation(y), fst(p) ∈ y, snd(p) ∈ y, membershipRelation(y) ⊆ membershipRelation(x)) |- p ∈ relationRestriction(membershipRelation(x), y, y)) by Cut(subsetElim of (z := p, x := membershipRelation(y), y := membershipRelation(x)), relationRestrictionIntro of (r := membershipRelation(x), x := y))
      have((y ⊆ x, relation(membershipRelation(x)), p ∈ membershipRelation(y), fst(p) ∈ y, snd(p) ∈ y) |- p ∈ relationRestriction(membershipRelation(x), y, y)) by Cut(membershipRelationSubset, lastStep)
      have((y ⊆ x, p ∈ membershipRelation(y), fst(p) ∈ y, snd(p) ∈ y) |- p ∈ relationRestriction(membershipRelation(x), y, y)) by Cut(membershipRelationRelation, lastStep)
      thenHave((y ⊆ x, p ∈ membershipRelation(y), fst(p) ∈ y /\ snd(p) ∈ y) |- p ∈ relationRestriction(membershipRelation(x), y, y)) by LeftAnd
      have((y ⊆ x, p ∈ membershipRelation(y)) |- p ∈ relationRestriction(membershipRelation(x), y, y)) by Cut(membershipRelationInDomain of (x := y), lastStep)
    }

    val backward = have(p ∈ relationRestriction(membershipRelation(x), y, y) ==> p ∈ membershipRelation(y)) subproof {
      have((fst(p) ∈ y, snd(p) ∈ y, pair(fst(p), snd(p)) ∈ membershipRelation(x)) |- pair(fst(p), snd(p)) ∈ membershipRelation(y)) by Cut(membershipRelationIsMembershipPair of (a := fst(p), b := snd(p)), membershipRelationIntro of (x := y, a := fst(p), b := snd(p)))
      thenHave((fst(p) ∈ y /\ snd(p) ∈ y, pair(fst(p), snd(p)) ∈ membershipRelation(x)) |- pair(fst(p), snd(p)) ∈ membershipRelation(y)) by LeftAnd
      have(((pair(fst(p), snd(p)) ∈ relationRestriction(membershipRelation(x), y, y)), pair(fst(p), snd(p)) ∈ membershipRelation(x)) |- pair(fst(p), snd(p)) ∈ membershipRelation(y)) by Cut(relationRestrictionPairInRestrictedDomains of (x := y, r := membershipRelation(x), a := fst(p), b := snd(p)), lastStep)
      have((pair(fst(p), snd(p)) ∈ relationRestriction(membershipRelation(x), y, y)) |- pair(fst(p), snd(p)) ∈ membershipRelation(y)) by Cut(relationRestrictionInRelation of (p := pair(fst(p), snd(p)), r := membershipRelation(x), x := y), lastStep)
      thenHave((relation(relationRestriction(membershipRelation(x), y, y)), p ∈ relationRestriction(membershipRelation(x), y, y)) |- p ∈ membershipRelation(y)) by Substitution.ApplyRules(pairReconstructionInRelation of (r := relationRestriction(membershipRelation(x), y, y)))
      have(p ∈ relationRestriction(membershipRelation(x), y, y) |- p ∈ membershipRelation(y)) by Cut(relationRestrictionIsRelation of (r := membershipRelation(x), x := y, y := y), lastStep)
    }
    have(y ⊆ x |- p ∈ membershipRelation(y) <=> p ∈ relationRestriction(membershipRelation(x), y, y)) by RightIff(forward, backward)
    thenHave(y ⊆ x |- ∀(p, p ∈ membershipRelation(y) <=> p ∈ relationRestriction(membershipRelation(x), y, y))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := membershipRelation(y), y := relationRestriction(membershipRelation(x), y, y)))
  }
}
