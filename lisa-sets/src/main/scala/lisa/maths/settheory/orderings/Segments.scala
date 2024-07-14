package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Relations.*
import lisa.maths.settheory.Functions.*
import lisa.maths.settheory.orderings.MembershipRelation.*
import lisa.maths.settheory.orderings.PartialOrders.*

object Segments extends lisa.Main {

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
  private val s = variable
  // relation and function symbols
  private val r = variable
  private val r1 = variable
  private val r2 = variable
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
    * Theorem --- Uniqueness of the preimage of an element under a relation
    * 
    *    `∃!z. ∀a. a ∈ z ⇔ (a ∈ x ∧ (a, b) ∈ r)`
    */
  val elementPreimageUniqueness = Lemma(
    ∃!(z, ∀(a, a ∈ z <=> (a ∈ x /\ pair(a, b) ∈ r)))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(a, pair(a, b) ∈ r))
  }

  /**
   * Definition --- Preimage of an element under a relation
   *
   *    `elementPreimage(b, r, x) = {a | a ∈ x ∧ (a, b) ∈ r}`
   */
  val elementPreimage = DEF(b, r, x) --> The(z, ∀(a, a ∈ z <=> (a ∈ x /\ pair(a, b) ∈ r)))(elementPreimageUniqueness)

  /**
   * Theorem --- Definition of elements of the preimage of an element under a relation
   * 
   *    `relationBetween(r, x, x) |- a ∈ elementPreimage(b, r, x) ⇔ (a ∈ x ∧ (a, b) ∈ r)`
   */
  val elementPreimageDefinition = Lemma(
    relationBetween(r, x, x) |- a ∈ elementPreimage(b, r, x) <=> pair(a, b) ∈ r
  ) {

    val preimageInDomain = have(relationBetween(r, x, x) |- pair(a, b) ∈ r ==> a ∈ x) by Weakening(relationBetweenElimPair of (a := x, b := x, x := a, y:= b))

    have(∀(a, a ∈ elementPreimage(b, r, x) <=> (a ∈ x /\ pair(a, b) ∈ r))) by InstantiateForall(elementPreimage(b, r, x))(elementPreimage.definition)
    thenHave(a ∈ elementPreimage(b, r, x) <=> (a ∈ x /\ pair(a, b) ∈ r)) by InstantiateForall(a)
    thenHave(pair(a, b) ∈ r ==> a ∈ x |- a ∈ elementPreimage(b, r, x) <=> pair(a, b) ∈ r) by Tautology
    have(thesis) by Cut(preimageInDomain, lastStep)
  
  }


  /**
   * Theorem --- Preimage of element introduction rule
   * 
   *   `relationBetween(r, x, x), (a, b) ∈ r |- a ∈ elementPreimage(b, r, x)`
   */
  val elementPreimageIntro = Lemma(
    (relationBetween(r, x, x), pair(a, b) ∈ r) |- a ∈ elementPreimage(b, r, x)
  ) {
    have(thesis) by Weakening(elementPreimageDefinition)
  }

  /**
   * Theorem --- Preimage of element elimination rule
   * 
   *   `relationBetween(r, x, x), a ∈ elementPreimage(b, r, x) |- (a, b) ∈ r`
   */
  val elementPreimageElim = Lemma(
    (relationBetween(r, x, x), a ∈ elementPreimage(b, r, x)) |- pair(a, b) ∈ r
  ) {
    have(thesis) by Weakening(elementPreimageDefinition)
  }

  /**
    * Theorem --- The preimage of an element is a subset of the domain
    * 
    *   `relationBetween(r, x, x), a ∈ elementPreimage(b, r, x) |- a ∈ x ∧ b ∈ x` 
    */
  val elementPreimageInDomain = Lemma(
    (relationBetween(r, x, x), a ∈ elementPreimage(b, r, x)) |- a ∈ x /\ b ∈ x
  ){
    have(thesis) by Cut(elementPreimageElim, relationBetweenElimPair of (a := x, b := x, x := a, y := b))
  }

  val elementPreimageSubsetDomain = Lemma(
    relationBetween(r, x, x) |- elementPreimage(b, r, x) ⊆ x
  ) {
    have((relationBetween(r, x, x), a ∈ elementPreimage(b, r, x)) |- a ∈ x) by Weakening(elementPreimageInDomain)
    thenHave(relationBetween(r, x, x) |- a ∈ elementPreimage(b, r, x) ==> a ∈ x) by RightImplies
    thenHave(relationBetween(r, x, x) |- ∀(a, a ∈ elementPreimage(b, r, x) ==> a ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> elementPreimage(b, r, x), y -> x))
  }


  val irreflexiveRelationElementPreimage = Lemma(
    irreflexive(r, x) |- b ∉ elementPreimage(b, r, x)
  ){
    have((irreflexive(r, x), relationBetween(r, x, x), b ∈ elementPreimage(b, r, x)) |- ()) by RightAnd(antiReflexiveElim of (y := b), elementPreimageElim of (a := b))
    have((irreflexive(r, x), b ∈ elementPreimage(b, r, x)) |- ()) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }


  val initialSegment = elementPreimage

  /**
    * Theorem --- Initial segment introduction rule
    * 
    *   `strictWellOrder(r, x), (a, b) ∈ r |- a ∈ initialSegment(b, r, x)`
    */
  val initialSegmentIntro = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- a ∈ initialSegment(b, r, x)
  ) { 
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageIntro)
  }

  /**
    * Theorem --- Initial segment elimination rule
    * 
    *   `strictWellOrder(r, x), a ∈ initialSegment(b, r, x) |- (a, b) ∈ r`
    */
  val initialSegmentElim = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- pair(a, b) ∈ r
  ) {
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageElim)
  }


  val predecessorInInitialSegment = Lemma(
    isPredecessor(a, b, r, x) |- a ∈ initialSegment(b, r, x)
  ) {
    have((relationBetween(r, x, x), isPredecessor(a, b, r, x)) |- a ∈ initialSegment(b, r, x)) by Cut(isPredecessorBelow, elementPreimageIntro)
    have((strictTotalOrder(r, x), isPredecessor(a, b, r, x)) |- a ∈ initialSegment(b, r, x)) by Cut(strictTotalOrderIsRelation, lastStep)
    have(thesis) by Cut(isPredecessorInStrictTotalOrder, lastStep)
  }

  val initialSegmentSubset = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegment(a, r, x) ⊆ initialSegment(b, r, x)
  ) {
    have((strictWellOrder(r, x), pair(t, a) ∈ r, pair(a, b) ∈ r) |- pair(t, b) ∈ r) by Cut(strictWellOrderTransitive, transitiveElim of (w := t, y := a, z := b))
    have((strictWellOrder(r, x), pair(t, a) ∈ r, pair(a, b) ∈ r) |- t ∈ initialSegment(b, r, x)) by Tautology.from(lastStep, initialSegmentIntro of (a := t))
    have((strictWellOrder(r, x), t ∈ initialSegment(a, r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(b, r, x)) by Cut(initialSegmentElim of (a := t, b := a), lastStep)
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(a, r, x) ==> t ∈ initialSegment(b, r, x)) by RightImplies
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- ∀(t, t ∈ initialSegment(a, r, x) ==> t ∈ initialSegment(b, r, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> initialSegment(a, r, x), y -> initialSegment(b, r, x)))
  }

  val initialSegmentSubsetDomain = Lemma(
    strictWellOrder(r, x) |- initialSegment(b, r, x) ⊆ x
  ) {
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageSubsetDomain)
  }

  val notInSelfInitialSegment = Lemma(
    strictWellOrder(r, x) |- b ∉ initialSegment(b, r, x)
  ) {
    have(strictPartialOrder(r, x) |- b ∉ initialSegment(b, r, x)) by Cut(strictPartialOrderIrreflexive, irreflexiveRelationElementPreimage)
    have(strictTotalOrder(r, x) |- b ∉ initialSegment(b, r, x)) by Cut(strictTotalOrderIsPartial, lastStep)
    have(thesis) by Cut(strictWellOrderTotal, lastStep)
  }

  val initialSegmentTransitivity = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x), b ∈ initialSegment(c, r, x)) |- a ∈ initialSegment(c, r, x)
  ) {
    have((strictWellOrder(r, x), b ∈ initialSegment(c, r, x)) |- initialSegment(b, r, x) ⊆ initialSegment(c, r, x)) by 
      Cut(initialSegmentElim of (a := b, b := c), initialSegmentSubset of (a := b, b := c))
    have(thesis) by Cut(lastStep, subsetElim of (z := a, x := initialSegment(b, r, x), y := initialSegment(c, r, x)))
  }

  val belowInitialSegment = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x), pair(t, a) ∈ r) |- t ∈ initialSegment(b, r, x)
  ) {
    have((strictWellOrder(r, x), a ∈ initialSegment(b, r, x), transitive(r, x),  pair(t, a) ∈ r) |- pair(t, b) ∈ r) by Cut(initialSegmentElim, transitiveElim of (w := t, y := a, z := b))
    have((strictWellOrder(r, x), a ∈ initialSegment(b, r, x), pair(t, a) ∈ r) |- pair(t, b) ∈ r) by Cut(strictWellOrderTransitive, lastStep)  
    have(thesis) by Cut(lastStep, initialSegmentIntro of (a := t))
  }

  def initialSegmentOrder(b: Term, r: Term, x: Term) = relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x))

  val pairInInitialSegmentOrder = Lemma(
    (pair(s, t) ∈ initialSegmentOrder(b, r, x)) |- s ∈initialSegment(b, r, x) /\ t ∈ initialSegment(b, r, x)
  ) {
    have(thesis) by Cut(
      relationRestrictionIsRelationBetweenRestrictedDomains of (x := initialSegment(b, r, x), y := initialSegment(b, r, x), w := x, z := x), 
      relationBetweenElimPair of (r := initialSegmentOrder(b, r, x), a := initialSegment(b, r, x), b := initialSegment(b, r, x), x := s, y := t)
    )
  }

  /**
    * Theorem --- Initial segments of well orders are well ordered
    * 
    *  `strictWellOrder(r, x) |- strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x))`
    */
  val initialSegmentStrictWellOrder = Lemma(
    strictWellOrder(r, x) |- strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x))
  ) {
    have(thesis) by Cut(initialSegmentSubsetDomain, relationRestrictionStrictWellOrder of (y := initialSegment(b, r, x)))
  }

  val nonIdentitySetUniqueness = Lemma(
    ∃!(z, ∀(t, t ∈ z <=> (t ∈ x /\ (app(f, t) =/= t))))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(t, app(f, t) =/= t))
  }

  val nonIdentitySet = DEF(f, x) --> The(z, ∀(t, t ∈ z <=> (t ∈ x /\ (app(f, t) =/= t))))(nonIdentitySetUniqueness)

  val nonIdentitySetMembership = Lemma(
    t ∈ nonIdentitySet(f, x) <=> (t ∈ x /\ (app(f, t) =/= t))
  ) {
    have(∀(t, t ∈ nonIdentitySet(f, x) <=> (t ∈ x /\ (app(f, t) =/= t)))) by InstantiateForall(nonIdentitySet(f, x))(nonIdentitySet.definition)
    thenHave(thesis) by InstantiateForall(t)
  }

  val nonIdentitySetIntro = Lemma(
    (t ∈ x, app(f, t) =/= t) |- t ∈ nonIdentitySet(f, x)
  ) {
    have(thesis) by Weakening(nonIdentitySetMembership)
  }

  val nonIdentitySetElim = Lemma(
    t ∈ nonIdentitySet(f, x) |- app(f, t) =/= t
  ) {
    have(thesis) by Weakening(nonIdentitySetMembership)
  }

  val notInNonIdentitySetElim = Lemma(
    (t ∈ x, t ∉ nonIdentitySet(f, x)) |- app(f, t) === t
  ) {
    have(thesis) by Restate.from(nonIdentitySetIntro)
  }

  val notInNonIdentitySetIntro = Lemma(
    app(f, t) === t |- t ∉ nonIdentitySet(f, x)
  ) {
    have(thesis) by Restate.from(nonIdentitySetElim)
  }

  val nonIdentitySetSubsetDomain = Lemma(
    nonIdentitySet(f, x) ⊆ x
  ) {
    have(t ∈ nonIdentitySet(f, x) |- t ∈ x) by Weakening(nonIdentitySetMembership)
    thenHave(t ∈ nonIdentitySet(f, x) ==> t ∈ x) by RightImplies
    thenHave(∀(t, t ∈ nonIdentitySet(f, x) ==> t ∈ x)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> nonIdentitySet(f, x), y -> x))
  }

  val nonIdentitySetEmpty = Lemma(
    (surjective(f, x, y), nonIdentitySet(f, x) === ∅) |- x === y
  ) {
    val forward = have((surjective(f, x, y), nonIdentitySet(f, x) === ∅) |- a ∈ x ==> a ∈ y) subproof {
      have((functionFrom(f, x, y), a ∉ nonIdentitySet(f, x), a ∈ x) |- a ∈ y) by Substitution.ApplyRules(notInNonIdentitySetElim of (t := a))(functionFromAppInCodomain)
      have((functionFrom(f, x, y), a ∈ x, nonIdentitySet(f, x) === ∅) |- a ∈ y) by Cut(setEmptyHasNoElements of (x := nonIdentitySet(f, x), y := a), lastStep)
      have((surjective(f, x, y), a ∈ x, nonIdentitySet(f, x) === ∅) |- a ∈ y) by Cut(surjectiveIsFunctionFrom, lastStep)
    } 

    val backward = have((nonIdentitySet(f, x) === ∅, surjective(f, x, y)) |- b ∈ y ==> b ∈ x) subproof {
      have((nonIdentitySet(f, x) === ∅, a ∈ x) |- app(f, a) === a) by Cut(setEmptyHasNoElements of (x := nonIdentitySet(f, x), y := a), notInNonIdentitySetElim of (t := a))
      thenHave(nonIdentitySet(f, x) === ∅ |- a ∈ x ==> (app(f, a) === a)) by RightImplies
      val emptyIdSetProp = thenHave(nonIdentitySet(f, x) === ∅ |- ∀(a, a ∈ x ==> (app(f, a) === a))) by RightForall


      have(∀(a, a ∈ x ==> (app(f, a) === a)) |- ∀(a, a ∈ x ==> (app(f, a) === a))) by Hypothesis
      val idEmptyEq = thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), a ∈ x) |- app(f, a) === a) by InstantiateForall(a)
      have((a ∈ x, app(f, a) === b) |- (app(f, a) === b) /\ a ∈ x) by Restate
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), a ∈ x, app(f, a) === b) |- (a === b) /\ a ∈ x) by Substitution.ApplyRules(idEmptyEq)
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), a ∈ x /\ (app(f, a) === b)) |- (a === b) /\ a ∈ x) by LeftAnd
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), a ∈ x /\ (app(f, a) === b)) |- ∃(a, (a === b) /\ a ∈ x)) by RightExists
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), ∃(a, a ∈ x /\ (app(f, a) === b))) |- ∃(a, (a === b) /\ a ∈ x)) by LeftExists
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), surjective(f, x, y), b ∈ y) |- ∃(a, (a === b) /\ a ∈ x)) by Substitution.ApplyRules(surjectiveRangeMembership)
      thenHave((∀(a, a ∈ x ==> (app(f, a) === a)), surjective(f, x, y), b ∈ y) |- b ∈ x) by Substitution.ApplyRules(onePointRule of (Q := lambda(z, z ∈ x), x := app(f, a), y := b))
      have((nonIdentitySet(f, x) === ∅, surjective(f, x, y), b ∈ y) |- b ∈ x) by Cut(emptyIdSetProp, lastStep)
    }

    have((nonIdentitySet(f, x) === ∅, surjective(f, x, y)) |- a ∈ x <=> a ∈ y) by RightIff(forward, backward of (b := a))
    thenHave((nonIdentitySet(f, x) === ∅, surjective(f, x, y)) |- ∀(a, a ∈ x <=> a ∈ y)) by RightForall
    thenHave(thesis) by Substitution.ApplyRules(extensionalityAxiom)
  }
  

  val noIsomorphismWithInitialSegment = Lemma(
    (strictWellOrder(r, x), b ∈ x) |- !(∃(f, relationIsomorphism(f, r, x, initialSegmentOrder(b, r, x), initialSegment(b, r, x))))
  ) {
    val fIsIsomorphism = relationIsomorphism(f, r, x, initialSegmentOrder(b, r, x), initialSegment(b, r, x))
   
    val nonIdentitySetNotEmpty = have((b ∈ x, fIsIsomorphism, strictWellOrder(r, x)) |- nonIdentitySet(f, x) =/= ∅) subproof {
      have((b ∈ x, fIsIsomorphism, app(f, b) === b) |- b ∈ initialSegment(b, r, x)) by RightSubstEq.withParametersSimple(List((app(f, b), b)), lambda(z, z ∈ initialSegment(b, r, x)))(relationIsomorphismAppInCodomain of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := b))
      have((b ∈ x, fIsIsomorphism, app(f, b) === b, strictWellOrder(r, x)) |- ()) by RightAnd(lastStep, notInSelfInitialSegment)
      thenHave((b ∈ x, fIsIsomorphism, strictWellOrder(r, x)) |- app(f, b) =/= b) by RightNot
      have((b ∈ x, fIsIsomorphism,strictWellOrder(r, x)) |- b ∈ nonIdentitySet(f, x)) by Cut(lastStep, nonIdentitySetIntro of (t := b))
      have(thesis) by Cut(lastStep, setWithElementNonEmpty of (x := nonIdentitySet(f, x), y := b))
    } 


    val fANotBelowA = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), app(f, a) ∈ x) |- pair(app(f, a), a) ∉ r) subproof{

      have((irreflexive(initialSegmentOrder(b, r, x), initialSegment(b, r, x)), fIsIsomorphism, pair(app(f, a), a) ∈ r) |- app(f, app(f, a)) =/= app(f, a)) by Cut(
        relationIsomorphismElimForward of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := app(f, a), b := a), 
        pairInAntiReflexiveRelation of (r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x), a := app(f, app(f, a)), b := app(f, a)))
      have((strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x)), fIsIsomorphism, pair(app(f, a), a) ∈ r) |- app(f, app(f, a)) =/= app(f, a)) by Cut(strictWellOrderIrreflexive of (r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x)), lastStep)
      val right = have((strictWellOrder(r, x), fIsIsomorphism, pair(app(f, a), a) ∈ r) |- app(f, app(f, a)) =/= app(f, a)) by Cut(initialSegmentStrictWellOrder, lastStep)

      val left = have((isLeastElement(a, nonIdentitySet(f, x), r, x), pair(app(f, a), a) ∈ r, app(f, a) ∈ x) |- app(f, app(f, a)) === app(f, a)) by Cut(belowLeastElement of (b := app(f, a), y := nonIdentitySet(f, x)), notInNonIdentitySetElim of (t := app(f, a)))
    
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), pair(app(f, a), a) ∈ r, app(f, a) ∈ x) |- ()) by RightAnd(left, right)
    }

    val aNotBelowFA = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x) |- pair(a, app(f, a)) ∉ r) subproof{

      val fInverseBelowA = have((pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- pair(app(inverseRelation(f), a), a) ∈ r) by Substitution.ApplyRules(inverseRelationRightCancel of (b := a, y := initialSegment(b, r, x)))
        (relationIsomorphismElimBackward of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := app(inverseRelation(f), a), b := a))
      
      val left = have((pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inverseRelation(f), a) ∉ nonIdentitySet(f, x)) by Cut(fInverseBelowA, belowLeastElement of (b := app(inverseRelation(f), a), y := nonIdentitySet(f, x)))
      have((irreflexive(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inverseRelation(f), a) =/= a) by Cut(fInverseBelowA, pairInAntiReflexiveRelation of (a := app(inverseRelation(f), a), b := a))
      have((strictWellOrder(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inverseRelation(f), a) =/= a) by Cut(strictWellOrderIrreflexive, lastStep)
      thenHave((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, a ∈ initialSegment(b, r, x)) |- app(inverseRelation(f), a) =/= app(f, app(inverseRelation(f), a))) by Substitution.ApplyRules(inverseRelationRightCancel of (y := initialSegment(b, r, x), b := a))

      val right = have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, fIsIsomorphism, a ∈ initialSegment(b, r, x)) |- app(inverseRelation(f), a) ∈ nonIdentitySet(f, x)) by Cut(
        lastStep, nonIdentitySetIntro of (t := app(inverseRelation(f), a))
      )

      have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inverseRelation(f), a) ∈ x, a ∈ x, a ∈ initialSegment(b, r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x)) |- ()) by RightAnd(left, right)

      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), a ∈ initialSegment(b, r, x)) |- ()) by Cut(inverseFunctionImageInDomain of (y := initialSegment(b, r, x), b := a), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ r, a ∈ initialSegment(b, r, x), app(f, a) ∈ initialSegment(b, r, x)) |- ()) by Cut(relationRestrictionIntroPair of (b := app(f, a), x := initialSegment(b, r, x), y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ r, app(f, a) ∈ initialSegment(b, r, x)) |- ()) by Cut(belowInitialSegment of (t := a, a := app(f, a)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), functionFrom(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ r) |- ()) by Cut(functionFromAppInCodomain of (y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ r) |- ()) by Cut(bijectiveIsFunctionFrom of (y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      pair(a, app(f, a)) ∈ r) |- ()) by Cut(relationIsomorphismBijective of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x)), lastStep)
    }


    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, app(f, a) ∈ x) |- pair(app(f, a), a) ∉ r /\ pair(a, app(f, a)) ∉ r) by RightAnd(fANotBelowA, aNotBelowFA)
    val right = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, app(f, a) ∈ x, a ∈ nonIdentitySet(f, x)) |- pair(app(f, a), a) ∉ r /\ pair(a, app(f, a)) ∉ r /\ (a =/= app(f, a))) by RightAnd(lastStep, nonIdentitySetElim of (t := a))   

    val left = have((strictWellOrder(r, x), a ∈ x, app(f, a) ∈ x) |- pair(app(f, a), a) ∈ r \/ (pair(a, app(f, a)) ∈ r) \/ (a === app(f, a))) by Cut(
      strictWellOrderConnected, connectedElim of (z := app(f, a), y := a))
    
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, a ∈ nonIdentitySet(f, x), app(f, a) ∈ x) |- ()) by RightAnd(left, right)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, a ∈ nonIdentitySet(f, x), initialSegment(b, r, x) ⊆ x, app(f, a) ∈ initialSegment(b, r, x)) |- ()) by Cut(subsetElim of (z := app(f, a), x := initialSegment(b, r, x), y := x), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, a ∈ nonIdentitySet(f, x), app(f, a) ∈ initialSegment(b, r, x)) |- ()) by Cut(initialSegmentSubsetDomain, lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, a ∈ nonIdentitySet(f, x)) |- ()) by Cut(relationIsomorphismAppInCodomain of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x) |- ()) by Cut(isLeastElementInSubset of (y := nonIdentitySet(f, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x)) |- ()) by Cut(isLeastElementInDomain of (y := nonIdentitySet(f, x)), lastStep)
    thenHave((strictWellOrder(r, x), fIsIsomorphism, ∃(a, isLeastElement(a, nonIdentitySet(f, x), r, x))) |- ()) by LeftExists
    have((strictWellOrder(r, x), fIsIsomorphism, nonIdentitySet(f, x) ⊆ x, nonIdentitySet(f, x) =/= ∅) |- ()) by Cut(strictWellOrderElim of (y := nonIdentitySet(f, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, nonIdentitySet(f, x) =/= ∅) |- ()) by Cut(nonIdentitySetSubsetDomain, lastStep) 
    have((strictWellOrder(r, x), fIsIsomorphism, b ∈ x) |- ()) by Cut(nonIdentitySetNotEmpty, lastStep)
    thenHave((strictWellOrder(r, x), b ∈ x) |- !fIsIsomorphism) by RightNot
    thenHave((strictWellOrder(r, x), b ∈ x) |- ∀(f, !fIsIsomorphism)) by RightForall
  }

  val initialSegmentIsomorphicCases = Lemma(
    (strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∃(f,
      relationIsomorphism(f, r1, x, r2, y) \/
      ∃(a, a ∈ x /\ relationIsomorphism(f, initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), r2, y)) \/
      ∃(b, b ∈ y /\ relationIsomorphism(f, r1, x, initialSegmentOrder(b, r2, y), initialSegment(b, r2, y)))
    )  
  ) {
    val fDef = ∀(p, p ∈ f <=> (p ∈ (x × y) /\ 
      ∃(g, relationIsomorphism(g, initialSegmentOrder(fst(p), r1, x), initialSegment(fst(p), r1, x), initialSegmentOrder(snd(p), r2, y), initialSegment(snd(p), r2, y)))))
    sorry
  }

}
