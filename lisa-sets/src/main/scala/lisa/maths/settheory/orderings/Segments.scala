package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
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
    existsOne(z, forall(a, in(a, z) <=> (in(a, x) /\ in(pair(a, b), r))))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(a, in(pair(a, b), r)))
  }

  /**
   * Definition --- Preimage of an element under a relation
   *
   *    `elementPreimage(b, r, x) = {a | a ∈ x ∧ (a, b) ∈ r}`
   */
  val elementPreimage = DEF(b, r, x) --> The(z, forall(a, in(a, z) <=> (in(a, x) /\ in(pair(a, b), r))))(elementPreimageUniqueness)

  /**
   * Theorem --- Definition of elements of the preimage of an element under a relation
   * 
   *    `relationBetween(r, x, x) |- a ∈ elementPreimage(b, r, x) ⇔ (a ∈ x ∧ (a, b) ∈ r)`
   */
  val elementPreimageDefinition = Lemma(
    relationBetween(r, x, x) |- in(a, elementPreimage(b, r, x)) <=> in(pair(a, b), r)
  ) {

    val preimageInDomain = have(relationBetween(r, x, x) |- in(pair(a, b), r) ==> in(a, x)) by Weakening(relationBetweenElimPair of (a := x, b := x, x := a, y:= b))

    have(forall(a, in(a, elementPreimage(b, r, x)) <=> (in(a, x) /\ in(pair(a, b), r)))) by InstantiateForall(elementPreimage(b, r, x))(elementPreimage.definition)
    thenHave(in(a, elementPreimage(b, r, x)) <=> (in(a, x) /\ in(pair(a, b), r))) by InstantiateForall(a)
    thenHave(in(pair(a, b), r) ==> in(a, x) |- in(a, elementPreimage(b, r, x)) <=> in(pair(a, b), r)) by Tautology
    have(thesis) by Cut(preimageInDomain, lastStep)
  
  }


  /**
   * Theorem --- Preimage of element introduction rule
   * 
   *   `relationBetween(r, x, x), (a, b) ∈ r |- a ∈ elementPreimage(b, r, x)`
   */
  val elementPreimageIntro = Lemma(
    (relationBetween(r, x, x), in(pair(a, b), r)) |- in(a, elementPreimage(b, r, x))
  ) {
    have(thesis) by Weakening(elementPreimageDefinition)
  }

  /**
   * Theorem --- Preimage of element elimination rule
   * 
   *   `relationBetween(r, x, x), a ∈ elementPreimage(b, r, x) |- (a, b) ∈ r`
   */
  val elementPreimageElim = Lemma(
    (relationBetween(r, x, x), in(a, elementPreimage(b, r, x))) |- in(pair(a, b), r)
  ) {
    have(thesis) by Weakening(elementPreimageDefinition)
  }

  /**
    * Theorem --- The preimage of an element is a subset of the domain
    * 
    *   `relationBetween(r, x, x), a ∈ elementPreimage(b, r, x) |- a ∈ x ∧ b ∈ x` 
    */
  val elementPreimageInDomain = Lemma(
    (relationBetween(r, x, x), in(a, elementPreimage(b, r, x))) |- in(a, x) /\ in(b, x)
  ){
    have(thesis) by Cut(elementPreimageElim, relationBetweenElimPair of (a := x, b := x, x := a, y := b))
  }

  val elementPreimageSubsetDomain = Lemma(
    relationBetween(r, x, x) |- subset(elementPreimage(b, r, x), x)
  ) {
    have((relationBetween(r, x, x), in(a, elementPreimage(b, r, x))) |- in(a, x)) by Weakening(elementPreimageInDomain)
    thenHave(relationBetween(r, x, x) |- in(a, elementPreimage(b, r, x)) ==> in(a, x)) by RightImplies
    thenHave(relationBetween(r, x, x) |- forall(a, in(a, elementPreimage(b, r, x)) ==> in(a, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> elementPreimage(b, r, x), y -> x))
  }


  val irreflexiveRelationElementPreimage = Lemma(
    irreflexive(r, x) |- !in(b, elementPreimage(b, r, x))
  ){
    have((irreflexive(r, x), in(b, x), relationBetween(r, x, x), in(b, elementPreimage(b, r, x))) |- ()) by RightAnd(antiReflexiveElim of (y := b), elementPreimageElim of (a := b))
    have((irreflexive(r, x), relationBetween(r, x, x), in(b, elementPreimage(b, r, x))) |- ()) by Cut(elementPreimageInDomain of (a := b), lastStep)
    have((irreflexive(r, x), in(b, elementPreimage(b, r, x))) |- ()) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }


  val initialSegment = elementPreimage

  /**
    * Theorem --- Initial segment introduction rule
    * 
    *   `strictWellOrder(r, x), (a, b) ∈ r |- a ∈ initialSegment(b, r, x)`
    */
  val initialSegmentIntro = Lemma(
    (strictWellOrder(r, x), in(pair(a, b), r)) |- in(a, initialSegment(b, r, x))
  ) { 
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageIntro)
  }

  /**
    * Theorem --- Initial segment elimination rule
    * 
    *   `strictWellOrder(r, x), a ∈ initialSegment(b, r, x) |- (a, b) ∈ r`
    */
  val initialSegmentElim = Lemma(
    (strictWellOrder(r, x), in(a, initialSegment(b, r, x))) |- in(pair(a, b), r)
  ) {
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageElim)
  }


  val predecessorInInitialSegment = Lemma(
    isPredecessor(a, b, r, x) |- in(a, initialSegment(b, r, x))
  ) {
    have((relationBetween(r, x, x), isPredecessor(a, b, r, x)) |- in(a, initialSegment(b, r, x))) by Cut(isPredecessorBelow, elementPreimageIntro)
    have((strictTotalOrder(r, x), isPredecessor(a, b, r, x)) |- in(a, initialSegment(b, r, x))) by Cut(strictTotalOrderIsRelation, lastStep)
    have(thesis) by Cut(isPredecessorInStrictTotalOrder, lastStep)
  }

  val initialSegmentSubset = Lemma(
    (strictWellOrder(r, x), in(pair(a, b), r)) |- subset(initialSegment(a, r, x), initialSegment(b, r, x))
  ) {
    have((strictWellOrder(r, x), in(pair(t, a), r), in(pair(a, b), r)) |- in(pair(t, b), r)) by Cut(strictWellOrderTransitive, transitiveElim of (w := t, y := a, z := b))
    have((strictWellOrder(r, x), in(pair(t, a), r), in(pair(a, b), r)) |- in(t, initialSegment(b, r, x))) by Tautology.from(lastStep, initialSegmentIntro of (a := t))
    have((strictWellOrder(r, x), in(t, initialSegment(a, r, x)), in(pair(a, b), r)) |- in(t, initialSegment(b, r, x))) by Cut(initialSegmentElim of (a := t, b := a), lastStep)
    thenHave((strictWellOrder(r, x), in(pair(a, b), r)) |- in(t, initialSegment(a, r, x)) ==> in(t, initialSegment(b, r, x))) by RightImplies
    thenHave((strictWellOrder(r, x), in(pair(a, b), r)) |- forall(t, in(t, initialSegment(a, r, x)) ==> in(t, initialSegment(b, r, x)))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> initialSegment(a, r, x), y -> initialSegment(b, r, x)))
  }

  val initialSegmentSubsetDomain = Lemma(
    strictWellOrder(r, x) |- subset(initialSegment(b, r, x), x)
  ) {
    have(thesis) by Cut(strictWellOrderIsRelation, elementPreimageSubsetDomain)
  }

  val notInSelfInitialSegment = Lemma(
    strictWellOrder(r, x) |- !in(b, initialSegment(b, r, x))
  ) {
    have(strictPartialOrder(r, x) |- !in(b, initialSegment(b, r, x))) by Cut(strictPartialOrderIrreflexive, irreflexiveRelationElementPreimage)
    have(strictTotalOrder(r, x) |- !in(b, initialSegment(b, r, x))) by Cut(strictTotalOrderIsPartial, lastStep)
    have(thesis) by Cut(strictWellOrderTotal, lastStep)
  }

  val initialSegmentTransitivity = Lemma(
    (strictWellOrder(r, x), in(a, initialSegment(b, r, x)), in(b, initialSegment(c, r, x))) |- in(a, initialSegment(c, r, x))
  ) {
    have((strictWellOrder(r, x), in(b, initialSegment(c, r, x))) |- subset(initialSegment(b, r, x), initialSegment(c, r, x))) by 
      Cut(initialSegmentElim of (a := b, b := c), initialSegmentSubset of (a := b, b := c))
    have(thesis) by Cut(lastStep, subsetElim of (z := a, x := initialSegment(b, r, x), y := initialSegment(c, r, x)))
  }

  val belowInitialSegment = Lemma(
    (strictWellOrder(r, x), in(a, initialSegment(b, r, x)), in(pair(t, a), r)) |- in(t, initialSegment(b, r, x))
  ) {
    have((strictWellOrder(r, x), in(a, initialSegment(b, r, x)), transitive(r, x),  in(pair(t, a), r)) |- in(pair(t, b), r)) by Cut(initialSegmentElim, transitiveElim of (w := t, y := a, z := b))
    have((strictWellOrder(r, x), in(a, initialSegment(b, r, x)), in(pair(t, a), r)) |- in(pair(t, b), r)) by Cut(strictWellOrderTransitive, lastStep)  
    have(thesis) by Cut(lastStep, initialSegmentIntro of (a := t))
  }

  def initialSegmentOrder(b: Term, r: Term, x: Term) = relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x))

  val pairInInitialSegmentOrder = Lemma(
    (in(pair(s, t), initialSegmentOrder(b, r, x))) |- in(s, initialSegment(b, r, x)) /\ in(t, initialSegment(b, r, x))
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
    existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ !(app(f, t) === t))))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(t, !(app(f, t) === t)))
  }

  val nonIdentitySet = DEF(f, x) --> The(z, forall(t, in(t, z) <=> (in(t, x) /\ !(app(f, t) === t))))(nonIdentitySetUniqueness)

  val nonIdentitySetMembership = Lemma(
    in(t, nonIdentitySet(f, x)) <=> (in(t, x) /\ !(app(f, t) === t))
  ) {
    have(forall(t, in(t, nonIdentitySet(f, x)) <=> (in(t, x) /\ !(app(f, t) === t)))) by InstantiateForall(nonIdentitySet(f, x))(nonIdentitySet.definition)
    thenHave(thesis) by InstantiateForall(t)
  }

  val nonIdentitySetIntro = Lemma(
    (in(t, x), !(app(f, t) === t)) |- in(t, nonIdentitySet(f, x))
  ) {
    have(thesis) by Weakening(nonIdentitySetMembership)
  }

  val nonIdentitySetElim = Lemma(
    in(t, nonIdentitySet(f, x)) |- !(app(f, t) === t)
  ) {
    have(thesis) by Weakening(nonIdentitySetMembership)
  }

  val notInNonIdentitySetElim = Lemma(
    (in(t, x), !in(t, nonIdentitySet(f, x))) |- app(f, t) === t
  ) {
    have(thesis) by Restate.from(nonIdentitySetIntro)
  }

  val notInNonIdentitySetIntro = Lemma(
    app(f, t) === t |- !in(t, nonIdentitySet(f, x))
  ) {
    have(thesis) by Restate.from(nonIdentitySetElim)
  }

  val nonIdentitySetSubsetDomain = Lemma(
    subset(nonIdentitySet(f, x), x)
  ) {
    have(in(t, nonIdentitySet(f, x)) |- in(t, x)) by Weakening(nonIdentitySetMembership)
    thenHave(in(t, nonIdentitySet(f, x)) ==> in(t, x)) by RightImplies
    thenHave(forall(t, in(t, nonIdentitySet(f, x)) ==> in(t, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x -> nonIdentitySet(f, x), y -> x))
  }

  val nonIdentitySetEmpty = Lemma(
    (surjective(f, x, y), nonIdentitySet(f, x) === emptySet) |- x === y
  ) {
    have((functionFrom(f, x, y), !in(a, nonIdentitySet(f, x)), in(a, x)) |- in(a, y)) by Substitution.ApplyRules(notInNonIdentitySetElim of (t := a))(functionFromAppInCodomain)
    have((functionFrom(f, x, y), in(a, x), nonIdentitySet(f, x) === emptySet) |- in(a, y)) by Cut(setEmptyHasNoElements of (x := nonIdentitySet(f, x), y := a), lastStep)
    have((surjective(f, x, y), in(a, x), nonIdentitySet(f, x) === emptySet) |- in(a, y)) by Cut(surjectiveIsFunction, lastStep)
    val forward = thenHave((surjective(f, x, y), nonIdentitySet(f, x) === emptySet) |- in(a, x) ==> in(a, y)) by RightImplies 


    have((nonIdentitySet(f, x) === emptySet, in(a, x)) |- app(f, a) === a) by Cut(setEmptyHasNoElements of (x := nonIdentitySet(f, x), y := a), notInNonIdentitySetElim of (t := a))
    thenHave(nonIdentitySet(f, x) === emptySet |- in(a, x) ==> (app(f, a) === a)) by RightImplies
    val emptyIdSetProp = thenHave(nonIdentitySet(f, x) === emptySet |- forall(a, in(a, x) ==> (app(f, a) === a))) by RightForall


    have(forall(a, in(a, x) ==> (app(f, a) === a)) |- forall(a, in(a, x) ==> (app(f, a) === a))) by Hypothesis
    val idEmptyEq = thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), in(a, x)) |- app(f, a) === a) by InstantiateForall(a)
    have((in(a, x), app(f, a) === b) |- (app(f, a) === b) /\ in(a, x)) by Restate
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), in(a, x), app(f, a) === b) |- (a === b) /\ in(a, x)) by Substitution.ApplyRules(idEmptyEq)
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), in(a, x) /\ (app(f, a) === b)) |- (a === b) /\ in(a, x)) by LeftAnd
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), in(a, x) /\ (app(f, a) === b)) |- exists(a, (a === b) /\ in(a, x))) by RightExists
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), exists(a, in(a, x) /\ (app(f, a) === b))) |- exists(a, (a === b) /\ in(a, x))) by LeftExists
    have((forall(a, in(a, x) ==> (app(f, a) === a)), surjective(f, x, y), in(b, y)) |- exists(a, (a === b) /\ in(a, x))) by Cut(surjectiveElim, lastStep)
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), surjective(f, x, y), in(b, y)) |- in(b, x)) by Substitution.ApplyRules(onePointRule of (Q := lambda(z, in(z, x)), x := app(f, a), y := b))
    thenHave((forall(a, in(a, x) ==> (app(f, a) === a)), surjective(f, x, y)) |- in(b, y) ==> in(b, x)) by RightImplies
    val backward = have((nonIdentitySet(f, x) === emptySet, surjective(f, x, y)) |- in(b, y) ==> in(b, x)) by Cut(emptyIdSetProp, lastStep)

    have((nonIdentitySet(f, x) === emptySet, surjective(f, x, y)) |- in(a, x) <=> in(a, y)) by RightIff(forward, backward of (b := a))
    thenHave((nonIdentitySet(f, x) === emptySet, surjective(f, x, y)) |- forall(a, in(a, x) <=> in(a, y))) by RightForall
    thenHave(thesis) by Substitution.ApplyRules(extensionalityAxiom)
  }
  

  val noIsomorphismWithInitialSegment = Lemma(
    (strictWellOrder(r, x), in(b, x)) |- !exists(f, relationIsomorphism(f, r, x, initialSegmentOrder(b, r, x), initialSegment(b, r, x)))
  ) {
    val fIsIsomorphism = relationIsomorphism(f, r, x, initialSegmentOrder(b, r, x), initialSegment(b, r, x))
   
    val nonIdentitySetNotEmpty = have((in(b, x), fIsIsomorphism, strictWellOrder(r, x)) |- !(nonIdentitySet(f, x) === emptySet)) subproof {
      have((in(b, x), fIsIsomorphism, app(f, b) === b) |- in(b, initialSegment(b, r, x))) by RightSubstEq.withParametersSimple(List((app(f, b), b)), lambda(z, in(z, initialSegment(b, r, x))))(relationIsomorphismAppInCodomain of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := b))
      have((in(b, x), fIsIsomorphism, app(f, b) === b, strictWellOrder(r, x)) |- ()) by RightAnd(lastStep, notInSelfInitialSegment)
      thenHave((in(b, x), fIsIsomorphism, strictWellOrder(r, x)) |- !(app(f, b) === b)) by RightNot
      have((in(b, x), fIsIsomorphism,strictWellOrder(r, x)) |- in(b, nonIdentitySet(f, x))) by Cut(lastStep, nonIdentitySetIntro of (t := b))
      have(thesis) by Cut(lastStep, setWithElementNonEmpty of (x := nonIdentitySet(f, x), y := b))
    } 


    val fANotBelowA = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(app(f, a), x)) |- !in(pair(app(f, a), a), r)) subproof{

      have((irreflexive(initialSegmentOrder(b, r, x), initialSegment(b, r, x)), fIsIsomorphism, in(pair(app(f, a), a), r)) |- !(app(f, app(f, a)) === app(f, a))) by Cut(
        relationIsomorphismElimForward of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := app(f, a), b := a), 
        pairInAntiReflexiveRelation of (r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x), a := app(f, app(f, a)), b := app(f, a)))
      have((strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x)), fIsIsomorphism, in(pair(app(f, a), a), r)) |- !(app(f, app(f, a)) === app(f, a))) by Cut(strictWellOrderIrreflexive of (r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x)), lastStep)
      val right = have((strictWellOrder(r, x), fIsIsomorphism, in(pair(app(f, a), a), r)) |- !(app(f, app(f, a)) === app(f, a))) by Cut(initialSegmentStrictWellOrder, lastStep)

      val left = have((isLeastElement(a, nonIdentitySet(f, x), r, x), in(pair(app(f, a), a), r), in(app(f, a), x)) |- app(f, app(f, a)) === app(f, a)) by Cut(belowLeastElement of (b := app(f, a), y := nonIdentitySet(f, x)), notInNonIdentitySetElim of (t := app(f, a)))
    
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(pair(app(f, a), a), r), in(app(f, a), x)) |- ()) by RightAnd(left, right)
    }

    val aNotBelowFA = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x)) |- !in(pair(a, app(f, a)), r)) subproof{

      val fInverseBelowA = have((in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), in(a, initialSegment(b, r, x))) |- in(pair(app(inverseRelation(f), a), a), r)) by Substitution.ApplyRules(inverseRelationRightCancel of (b := a, y := initialSegment(b, r, x)))
        (relationIsomorphismElimBackward of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := app(inverseRelation(f), a), b := a))
      
      val left = have((in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), bijective(f, x, initialSegment(b, r, x)), in(a, initialSegment(b, r, x))) |- !in(app(inverseRelation(f), a), nonIdentitySet(f, x))) by Cut(fInverseBelowA, belowLeastElement of (b := app(inverseRelation(f), a), y := nonIdentitySet(f, x)))
      have((irreflexive(r, x), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), in(a, initialSegment(b, r, x))) |- !(app(inverseRelation(f), a) === a)) by Cut(fInverseBelowA, pairInAntiReflexiveRelation of (a := app(inverseRelation(f), a), b := a))
      have((strictWellOrder(r, x), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), in(a, initialSegment(b, r, x))) |- !(app(inverseRelation(f), a) === a)) by Cut(strictWellOrderIrreflexive, lastStep)
      thenHave((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, in(a, initialSegment(b, r, x))) |- !(app(inverseRelation(f), a) === app(f, app(inverseRelation(f), a)))) by Substitution.ApplyRules(inverseRelationRightCancel of (y := initialSegment(b, r, x), b := a))

      val right = have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), fIsIsomorphism, in(a, initialSegment(b, r, x))) |- in(app(inverseRelation(f), a), nonIdentitySet(f, x))) by Cut(
        lastStep, nonIdentitySetIntro of (t := app(inverseRelation(f), a))
      )

      have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(app(inverseRelation(f), a), x), in(a, x), in(a, initialSegment(b, r, x)), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x)) |- ()) by RightAnd(left, right)

      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), initialSegmentOrder(b, r, x)), in(a, initialSegment(b, r, x))) |- ()) by Cut(inverseFunctionImageInDomain of (y := initialSegment(b, r, x), b := a), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), r), in(a, initialSegment(b, r, x)), in(app(f, a), initialSegment(b, r, x))) |- ()) by Cut(relationRestrictionIntro of (b := app(f, a), x := initialSegment(b, r, x), y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), r), in(app(f, a), initialSegment(b, r, x))) |- ()) by Cut(belowInitialSegment of (t := a, a := app(f, a)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      bijective(f, x, initialSegment(b, r, x)), functionFrom(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), r)) |- ()) by Cut(functionFromAppInCodomain of (y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      bijective(f, x, initialSegment(b, r, x)), in(pair(a, app(f, a)), r)) |- ()) by Cut(bijectiveIsFunction of (y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), 
      in(pair(a, app(f, a)), r)) |- ()) by Cut(relationIsomorphismBijective of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x)), lastStep)
    }


    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(app(f, a), x)) |- !in(pair(app(f, a), a), r) /\ !in(pair(a, app(f, a)), r)) by RightAnd(fANotBelowA, aNotBelowFA)
    val right = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(app(f, a), x), in(a, nonIdentitySet(f, x))) |- !in(pair(app(f, a), a), r) /\ !in(pair(a, app(f, a)), r) /\ !(a === app(f, a))) by RightAnd(lastStep, nonIdentitySetElim of (t := a))   

    val left = have((strictWellOrder(r, x), in(a, x), in(app(f, a), x)) |- in(pair(app(f, a), a), r) \/ in(pair(a, app(f, a)), r) \/ (a === app(f, a))) by Cut(
      strictWellOrderConnected, connectedElim of (z := app(f, a), y := a))
    
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(a, nonIdentitySet(f, x)), in(app(f, a), x)) |- ()) by RightAnd(left, right)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(a, nonIdentitySet(f, x)), subset(initialSegment(b, r, x), x), in(app(f, a), initialSegment(b, r, x))) |- ()) by Cut(subsetElim of (z := app(f, a), x := initialSegment(b, r, x), y := x), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(a, nonIdentitySet(f, x)), in(app(f, a), initialSegment(b, r, x))) |- ()) by Cut(initialSegmentSubsetDomain, lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x), in(a, nonIdentitySet(f, x))) |- ()) by Cut(relationIsomorphismAppInCodomain of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), in(a, x)) |- ()) by Cut(isLeastElementInSubset of (y := nonIdentitySet(f, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x)) |- ()) by Cut(isLeastElementInDomain of (y := nonIdentitySet(f, x)), lastStep)
    thenHave((strictWellOrder(r, x), fIsIsomorphism, exists(a, isLeastElement(a, nonIdentitySet(f, x), r, x))) |- ()) by LeftExists
    have((strictWellOrder(r, x), fIsIsomorphism, subset(nonIdentitySet(f, x), x), !(nonIdentitySet(f, x) === emptySet)) |- ()) by Cut(strictWellOrderElim of (y := nonIdentitySet(f, x)), lastStep)
    have((strictWellOrder(r, x), fIsIsomorphism, !(nonIdentitySet(f, x) === emptySet)) |- ()) by Cut(nonIdentitySetSubsetDomain, lastStep) 
    have((strictWellOrder(r, x), fIsIsomorphism, in(b, x)) |- ()) by Cut(nonIdentitySetNotEmpty, lastStep)
    thenHave((strictWellOrder(r, x), in(b, x)) |- !fIsIsomorphism) by RightNot
    thenHave((strictWellOrder(r, x), in(b, x)) |- forall(f, !fIsIsomorphism)) by RightForall
  }

  val initialSegmentIsomorphicCases = Lemma(
    (strictWellOrder(r1, x), strictWellOrder(r2, y)) |- exists(f,
      relationIsomorphism(f, r1, x, r2, y) \/
      exists(a, in(a, x) /\ relationIsomorphism(f, initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), r2, y)) \/
      exists(b, in(b, y) /\ relationIsomorphism(f, r1, x, initialSegmentOrder(b, r2, y), initialSegment(b, r2, y)))
    )  
  ) {
    sorry
  }


  // val initialSegmentPredecessorSplit = Lemma(
  //   totalOrder(p) /\ predecessor(p, y, x) |- in(z, initialSegment(p, x)) <=> ((z === y) \/ in(z, initialSegment(p, y)))
  // ) {
  //   sorry
  // }

  // val initialSegmentIntersection = Lemma(
  //   partialOrder(p) /\ in(y, initialSegment(p, x)) |- setIntersection(initialSegment(p, y), initialSegment(p, x)) === initialSegment(p, y)
  // ) {
  //   sorry
  // }

  // /**
  //  * The restriction of a function `f` with respect to `a` relative to a
  //  * partial order `p = (X, <)`. The result is `f` with its domain restricted
  //  * to the elements less than `a` wrt `<`.
  //  */
  // val orderedRestriction = DEF(f, a, p) --> domainRestriction(f, initialSegment(p, a))

  // /**
  //  * Theorem --- Ordered Restriction Membership
  //  *
  //  * A pair `b` is in the ordered restriction of a function `f` to the initial
  //  * segment of `a` under a partial order `p` iff it is in `f` and its first element
  //  * (the one in the domain) is in the initial segment of `a`
  //  */
  // val orderedRestrictionMembership = Lemma(
  //   partialOrder(p) |- in(b, orderedRestriction(f, a, p)) <=> (in(b, f) /\ in(firstInPair(b), initialSegment(p, a)))
  // ) {
  //   sorry
  // }

  // val orderedRestrictionFunctionalOverInit = Lemma(
  //   in(a, initialSegment(p, b)) /\ functionalOver(f, initialSegment(p, b)) |- functionalOver(orderedRestriction(f, a, p), initialSegment(p, a))
  // ) {
  //   sorry
  // }

  // val orderedRestrictionAgreement = Lemma(
  //   partialOrder(p) /\ in(b, initialSegment(p, a)) /\ in(b, relationDomain(f)) /\ in(b, relationDomain(g)) |- (app(orderedRestriction(f, a, p), b) === app(orderedRestriction(g, a, p), b)) <=> (app(
  //     f,
  //     b
  //   ) === app(g, b))
  // ) {
  //   sorry
  // }

}
