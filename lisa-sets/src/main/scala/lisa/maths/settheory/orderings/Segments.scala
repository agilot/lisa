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
  private val r3 = variable
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
    have(thesis) by Cut(lastStep, subsetIntro of (x := elementPreimage(b, r, x), y := x))
  }


  val irreflexiveRelationElementPreimage = Lemma(
    irreflexive(r, x) |- b ∉ elementPreimage(b, r, x)
  ){
    have((irreflexive(r, x), relationBetween(r, x, x), b ∈ elementPreimage(b, r, x)) |- ()) by RightAnd(antiReflexiveElim of (y := b), elementPreimageElim of (a := b))
    have((irreflexive(r, x), b ∈ elementPreimage(b, r, x)) |- ()) by Cut(antiReflexiveRelationIsRelation, lastStep)
  }


  val initialSegment = DEF(b, r, x) --> elementPreimage(b, r, x)

  /**
    * Theorem --- Initial segment introduction rule
    * 
    *   `strictWellOrder(r, x), (a, b) ∈ r |- a ∈ initialSegment(b, r, x)`
    */
  val initialSegmentIntro = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- a ∈ initialSegment(b, r, x)
  ) { 
    have((strictWellOrder(r, x), pair(a, b) ∈ r) |- a ∈ elementPreimage(b, r, x)) by Cut(strictWellOrderIsRelationBetween, elementPreimageIntro)
    thenHave(thesis) by Substitution.ApplyRules(initialSegment.shortDefinition)
  }

  /**
    * Theorem --- Initial segment elimination rule
    * 
    *   `strictWellOrder(r, x), a ∈ initialSegment(b, r, x) |- (a, b) ∈ r`
    */
  val initialSegmentElim = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- pair(a, b) ∈ r
  ) {
    have((strictWellOrder(r, x), a ∈ elementPreimage(b, r, x)) |- pair(a, b) ∈ r) by Cut(strictWellOrderIsRelationBetween, elementPreimageElim)
    thenHave(thesis) by Substitution.ApplyRules(initialSegment.shortDefinition)
  }

  val initialSegmentBoundInDomain = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- b ∈ x
  ) {
    have((relationBetween(r, x, x), strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x /\ b ∈ x) by Cut(initialSegmentElim, relationBetweenElimPair of (a := x, b := x, x := a, y := b))
    have((strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x /\ b ∈ x) by Cut(strictWellOrderIsRelationBetween, lastStep)
    thenHave(thesis) by Weakening
  }

  val initialSegmentElementInDomain = Lemma(
    (strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x
  ) {
    have((relationBetween(r, x, x), strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x /\ b ∈ x) by Cut(initialSegmentElim, relationBetweenElimPair of (a := x, b := x, x := a, y := b))
    have((strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x /\ b ∈ x) by Cut(strictWellOrderIsRelationBetween, lastStep)
    thenHave(thesis) by Weakening
  }


  val predecessorInInitialSegment = Lemma(
    (strictWellOrder(r, x), isPredecessor(a, b, r, x)) |- a ∈ initialSegment(b, r, x)
  ) {
    have((relationBetween(r, x, x), isPredecessor(a, b, r, x)) |- a ∈ elementPreimage(b, r, x)) by Cut(isPredecessorBelow, elementPreimageIntro)
    have((strictWellOrder(r, x), isPredecessor(a, b, r, x)) |- a ∈ elementPreimage(b, r, x)) by Cut(strictWellOrderIsRelationBetween, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(initialSegment.shortDefinition)
  }

  val initialSegmentSubset = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegment(a, r, x) ⊆ initialSegment(b, r, x)
  ) {
    have((strictWellOrder(r, x), pair(t, a) ∈ r, pair(a, b) ∈ r) |- pair(t, b) ∈ r) by Cut(strictWellOrderTransitive, transitiveElim of (w := t, y := a, z := b))
    have((strictWellOrder(r, x), pair(t, a) ∈ r, pair(a, b) ∈ r) |- t ∈ initialSegment(b, r, x)) by Tautology.from(lastStep, initialSegmentIntro of (a := t))
    have((strictWellOrder(r, x), t ∈ initialSegment(a, r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(b, r, x)) by Cut(initialSegmentElim of (a := t, b := a), lastStep)
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(a, r, x) ==> t ∈ initialSegment(b, r, x)) by RightImplies
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- ∀(t, t ∈ initialSegment(a, r, x) ==> t ∈ initialSegment(b, r, x))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := initialSegment(a, r, x), y := initialSegment(b, r, x)))
  }

  val initialSegmentSubsetDomain = Lemma(
    strictWellOrder(r, x) |- initialSegment(b, r, x) ⊆ x
  ) {
    have(strictWellOrder(r, x) |- elementPreimage(b, r, x) ⊆ x) by Cut(strictWellOrderIsRelationBetween, elementPreimageSubsetDomain)
    thenHave(thesis) by Substitution.ApplyRules(initialSegment.shortDefinition)
  }

  val notInSelfInitialSegment = Lemma(
    strictWellOrder(r, x) |- b ∉ initialSegment(b, r, x)
  ) {
    have(strictPartialOrder(r, x) |- b ∉ elementPreimage(b, r, x)) by Cut(strictPartialOrderIrreflexive, irreflexiveRelationElementPreimage)
    have(strictWellOrder(r, x) |- b ∉ elementPreimage(b, r, x)) by Cut(strictWellOrderPartial, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(initialSegment.shortDefinition)
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

  val leastElementInitialSegment = Lemma(
    (strictWellOrder(r, x), isLeastElement(b, x, r, x)) |- initialSegment(b, r, x) === ∅
  ) {
    have((isLeastElement(b, x, r, x), strictPartialOrder(r, x), pair(a, b) ∈ r, a ∈ x) |- ()) by Restate.from(belowLeastElement of (a := b, b := a, y := x))
    have((isLeastElement(b, x, r, x), strictWellOrder(r, x), pair(a, b) ∈ r, a ∈ x) |- ()) by Cut(strictWellOrderPartial, lastStep)
    have((isLeastElement(b, x, r, x), strictWellOrder(r, x), a ∈ initialSegment(b, r, x), a ∈ x) |- ()) by Cut(initialSegmentElim, lastStep)
    have((isLeastElement(b, x, r, x), strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- ()) by Cut(initialSegmentElementInDomain, lastStep)
    thenHave((isLeastElement(b, x, r, x), strictWellOrder(r, x), ∃(a, a ∈ initialSegment(b, r, x))) |- ()) by LeftExists
    have((isLeastElement(b, x, r, x), strictWellOrder(r, x), initialSegment(b, r, x) =/= ∅) |- ()) by Cut(nonEmptySetHasAnElement of (x := initialSegment(b, r, x)), lastStep)
  }

  val initialSegmentOrder = DEF(b, r, x) --> relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x))

  val pairInInitialSegmentOrder = Lemma(
    pair(s, t) ∈ initialSegmentOrder(b, r, x) |- s ∈ initialSegment(b, r, x) /\ t ∈ initialSegment(b, r, x)
  ) {
    have(thesis) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)(relationRestrictionPairInRestrictedDomains of (a := s, b := t, x := initialSegment(b, r, x), y := initialSegment(b, r, x)))
  }

  val initialSegmentOrderIsOriginalOrder = Lemma(
    pair(s, t) ∈ initialSegmentOrder(b, r, x) |- pair(s, t) ∈ r
  ) {
    have(thesis) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)(relationRestrictionPairInRelation of (p := pair(s, t), x := initialSegment(b, r, x), y := initialSegment(b, r, x)))
  }

  val initialSegmentOrderIntro = Lemma(
    (s ∈ initialSegment(b, r, x), t ∈ initialSegment(b, r, x), pair(s, t) ∈ r) |- pair(s, t) ∈ initialSegmentOrder(b, r, x)
  ) {
    have(thesis) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)(relationRestrictionIntroPair of (a := s, b := t, x := initialSegment(b, r, x), y := initialSegment(b, r, x)))
  }

  /**
    * Theorem --- Initial segments of well orders are well ordered
    * 
    *  `strictWellOrder(r, x) |- strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x))`
    */
  val initialSegmentStrictWellOrder = Lemma(
    strictWellOrder(r, x) |- strictWellOrder(initialSegmentOrder(b, r, x), initialSegment(b, r, x))
  ) {
    have(strictWellOrder(r, x) |- strictWellOrder(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(b, r, x))) by Cut(initialSegmentSubsetDomain, relationRestrictionStrictWellOrder of (y := initialSegment(b, r, x)))
    thenHave(thesis) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
  }

  val initialSegmentRestriction = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegment(a, r, x) === initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x))  
  ) {

    val restriction = initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x))

    val forward = have((strictWellOrder(r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(a, r, x) ==> t ∈ restriction) subproof {
      have((strictWellOrder(r, x), pair(t, a) ∈ initialSegmentOrder(b, r, x)) |- t ∈ restriction) by Cut(initialSegmentStrictWellOrder, initialSegmentIntro of (a := t, b := a, r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x)))
      have((strictWellOrder(r, x), pair(t, a) ∈ r, t ∈ initialSegment(b, r, x), a ∈ initialSegment(b, r, x)) |- t ∈ restriction) by Cut(initialSegmentOrderIntro of (s := t, t := a), lastStep)
      have((strictWellOrder(r, x), t ∈ initialSegment(b, r, x), t ∈ initialSegment(a, r, x), a ∈ initialSegment(b, r, x)) |- t ∈ restriction) by Cut(initialSegmentElim of (a := t, b := a), lastStep)
      have((strictWellOrder(r, x), t ∈ initialSegment(a, r, x), initialSegment(a, r, x) ⊆ initialSegment(b, r, x), a ∈ initialSegment(b, r, x)) |- t ∈ restriction) by Cut(subsetElim of (z := t, x := initialSegment(a, r, x), y := initialSegment(b, r, x)), lastStep)
      have((strictWellOrder(r, x), t ∈ initialSegment(a, r, x), pair(a, b) ∈ r, a ∈ initialSegment(b, r, x)) |- t ∈ restriction) by Cut(initialSegmentSubset, lastStep)
      have((strictWellOrder(r, x), t ∈ initialSegment(a, r, x), pair(a, b) ∈ r) |- t ∈ restriction) by Cut(initialSegmentIntro, lastStep)
    }
    val backward = have(strictWellOrder(r, x) |- t ∈ restriction ==> t ∈ initialSegment(a, r, x)) subproof {
      have((strictWellOrder(r, x), t ∈ restriction) |- pair(t, a) ∈ initialSegmentOrder(b, r, x)) by Cut(initialSegmentStrictWellOrder, initialSegmentElim of (a := t, b := a, r := initialSegmentOrder(b, r, x), x := initialSegment(b, r, x)))
      have((strictWellOrder(r, x), t ∈ restriction) |- pair(t, a) ∈ r) by Cut(lastStep, initialSegmentOrderIsOriginalOrder of (s := t, t := a))
      have((strictWellOrder(r, x), t ∈ restriction) |- t ∈ initialSegment(a, r, x)) by Cut(lastStep, initialSegmentIntro of (a := t, b := a))
    }

    have((strictWellOrder(r, x), pair(a, b) ∈ r) |- t ∈ initialSegment(a, r, x) <=> t ∈ restriction) by RightIff(forward, backward)
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- ∀(t, t ∈ initialSegment(a, r, x) <=> t ∈ restriction)) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := initialSegment(a, r, x), y := restriction))
  }

  val initialSegmentOrderRestriction = Lemma(
    (strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegmentOrder(a, r, x) === initialSegmentOrder(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x))  
  ) {
    have((relation(r), initialSegment(a, r, x) ⊆ initialSegment(b, r, x)) |- relationRestriction(r, initialSegment(a, r, x), initialSegment(a, r, x)) === relationRestriction(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(a, r, x), initialSegment(a, r, x))) by Restate.from(relationRestrictionTwiceSubsetOuter of (w := initialSegment(b, r, x), x := initialSegment(b, r, x), y := initialSegment(a, r, x), z := initialSegment(a, r, x)))
    thenHave((relation(r), initialSegment(a, r, x) ⊆ initialSegment(b, r, x)) |- initialSegmentOrder(a, r, x) === relationRestriction(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(a, r, x), initialSegment(a, r, x))) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
    have((relation(r), strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegmentOrder(a, r, x) === relationRestriction(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(a, r, x), initialSegment(a, r, x))) by Cut(initialSegmentSubset, lastStep)
    have((strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegmentOrder(a, r, x) === relationRestriction(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(a, r, x), initialSegment(a, r, x))) by Cut(strictWellOrderIsRelation, lastStep)
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegmentOrder(a, r, x) === relationRestriction(relationRestriction(r, initialSegment(b, r, x), initialSegment(b, r, x)), initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x)), initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x)))) by Substitution.ApplyRules(initialSegmentRestriction)
    thenHave((strictWellOrder(r, x), pair(a, b) ∈ r) |- initialSegmentOrder(a, r, x) === relationRestriction(initialSegmentOrder(b, r, x), initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x)), initialSegment(a, initialSegmentOrder(b, r, x), initialSegment(b, r, x)))) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
    thenHave(thesis) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
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
    have(thesis) by Cut(lastStep, subsetIntro of (x := nonIdentitySet(f, x), y := x))
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
    (strictWellOrder(r, x), b ∈ x) |- !((r, x) ≃ (initialSegmentOrder(b, r, x), initialSegment(b, r, x)))
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

      have((strictPartialOrder(r, x), isLeastElement(a, nonIdentitySet(f, x), r, x), pair(app(f, a), a) ∈ r, app(f, a) ∈ x) |- app(f, app(f, a)) === app(f, a)) by Cut(belowLeastElement of (b := app(f, a), y := nonIdentitySet(f, x)), notInNonIdentitySetElim of (t := app(f, a)))
      val left = have((strictWellOrder(r, x), isLeastElement(a, nonIdentitySet(f, x), r, x), pair(app(f, a), a) ∈ r, app(f, a) ∈ x) |- app(f, app(f, a)) === app(f, a)) by Cut(strictWellOrderPartial, lastStep)
    
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), pair(app(f, a), a) ∈ r, app(f, a) ∈ x) |- ()) by RightAnd(left, right)
    }

    val aNotBelowFA = have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x) |- pair(a, app(f, a)) ∉ r) subproof{

      val fInverseBelowA = have((pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- pair(app(inv(f), a), a) ∈ r) by Substitution.ApplyRules(inverseRelationRightCancel of (b := a, y := initialSegment(b, r, x)))
        (relationIsomorphismElimBackward of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x), a := app(inv(f), a), b := a))
      
      have((strictPartialOrder(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inv(f), a) ∉ nonIdentitySet(f, x)) by Cut(fInverseBelowA, belowLeastElement of (b := app(inv(f), a), y := nonIdentitySet(f, x)))
      val left = have((strictWellOrder(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inv(f), a) ∉ nonIdentitySet(f, x)) by Cut(strictWellOrderPartial, lastStep)
      have((irreflexive(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inv(f), a) =/= a) by Cut(fInverseBelowA, pairInAntiReflexiveRelation of (a := app(inv(f), a), b := a))
      have((strictWellOrder(r, x), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, bijective(f, x, initialSegment(b, r, x)), a ∈ initialSegment(b, r, x)) |- app(inv(f), a) =/= a) by Cut(strictWellOrderIrreflexive, lastStep)
      thenHave((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, a ∈ initialSegment(b, r, x)) |- app(inv(f), a) =/= app(f, app(inv(f), a))) by Substitution.ApplyRules(inverseRelationRightCancel of (y := initialSegment(b, r, x), b := a))

      val right = have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, fIsIsomorphism, a ∈ initialSegment(b, r, x)) |- app(inv(f), a) ∈ nonIdentitySet(f, x)) by Cut(
        lastStep, nonIdentitySetIntro of (t := app(inv(f), a))
      )

      have((strictWellOrder(r, x), bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), app(inv(f), a) ∈ x, a ∈ x, a ∈ initialSegment(b, r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x)) |- ()) by RightAnd(left, right)

      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ initialSegmentOrder(b, r, x), a ∈ initialSegment(b, r, x)) |- ()) by Cut(inverseFunctionImageInDomain of (y := initialSegment(b, r, x), b := a), lastStep)
      have((strictWellOrder(r, x), fIsIsomorphism, isLeastElement(a, nonIdentitySet(f, x), r, x), a ∈ x, 
      bijective(f, x, initialSegment(b, r, x)), pair(a, app(f, a)) ∈ r, a ∈ initialSegment(b, r, x), app(f, a) ∈ initialSegment(b, r, x)) |- ()) by Cut(initialSegmentOrderIntro of (s := a, t := app(f, a)), lastStep)
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
    thenHave((strictWellOrder(r, x), ∃(f, fIsIsomorphism), b ∈ x) |- ()) by LeftExists
    have((strictWellOrder(r, x), (r, x) ≃ (initialSegmentOrder(b, r, x), initialSegment(b, r, x)), b ∈ x) |- ())  by Cut(isomorphicElim of (r1 := r, r2 := initialSegmentOrder(b, r, x), y := initialSegment(b, r, x)), lastStep)
  }

  val initialSegmentIsomorphismRestriction = Lemma(
    (relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x) |- 
    relationIsomorphism(f ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))
  ) {

    val frestr = f ↾ initialSegment(a, r1, x)
    val isorestr = relationIsomorphism(f ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))

    val xInterInitSegment = have(strictWellOrder(r1, x) |- x ∩ initialSegment(a, r1, x) === initialSegment(a, r1, x)) by Cut(initialSegmentSubsetDomain of (b := a, r := r1), setIntersectionOfSubsetBackward of (y := initialSegment(a, r1, x)))

    val inSegment = have((strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x)) |- b ∈ x) by Cut(initialSegmentSubsetDomain of (b := a, r := r1), subsetElim of (z := b, x := initialSegment(a, r1, x), y := x))
    
    val restrRange = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x) |- ran(frestr) === initialSegment(app(f, a), r2, y)) subproof {

      have((functionFrom(f, x, y), strictWellOrder(r1, x)) |- b ∈ ran(frestr) <=> ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) by Substitution.ApplyRules(xInterInitSegment)(functionRestrictionFromRangeMembership of (z := initialSegment(a, r1, x)))
      val rangeEq = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x)) |- b ∈ ran(frestr) <=> ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) by Cut(relationIsomorphismFunctionFrom, lastStep) 

      val forward = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y)) |- b ∈ ran(frestr) ==> b ∈ initialSegment(app(f, a), r2, y)) subproof { 
        have((strictWellOrder(r2, y), app(f, c) === b, pair(app(f, c), app(f, a)) ∈ r2) |- b ∈ initialSegment(app(f, a), r2, y)) by Substitution.ApplyRules(app(f, c) === b)(initialSegmentIntro of (b := app(f, a), r := r2, x := y, a := b))
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r2, y), app(f, c) === b, pair(c, a) ∈ r1) |- b ∈ initialSegment(app(f, a), r2, y)) by Cut(relationIsomorphismElimForward of (a := c, b := a), lastStep)
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, c) === b, c ∈ initialSegment(a, r1, x)) |- b ∈ initialSegment(app(f, a), r2, y)) by Cut(initialSegmentElim of (a := c, b := a, r := r1), lastStep)
        thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b)) |- b ∈ initialSegment(app(f, a), r2, y)) by LeftAnd
        thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) |- b ∈ initialSegment(app(f, a), r2, y)) by LeftExists
        thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ ran(frestr)) |- b ∈ initialSegment(app(f, a), r2, y)) by Substitution.ApplyRules(rangeEq)
      }

      val backward = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x) |- b ∈ initialSegment(app(f, a), r2, y) ==> b ∈ ran(frestr)) subproof {
        have((strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), b ∈ y, bijective(f, x, y)) |- pair(app(f, app(inv(f), b)), app(f, a)) ∈ r2) by Substitution.ApplyRules(inverseRelationRightCancel)(initialSegmentElim of (a := b, b := app(f, a), r := r2, x := y))
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), b ∈ y, bijective(f, x, y), app(inv(f), b) ∈ x, a ∈ x) |- pair(app(inv(f), b), a) ∈ r1) by Cut(lastStep, relationIsomorphismElimBackward of (a := app(inv(f), b), b := a))
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), b ∈ y, bijective(f, x, y), app(inv(f), b) ∈ x, a ∈ x) |- app(inv(f), b) ∈ initialSegment(a, r1, x)) by Cut(lastStep, initialSegmentIntro of (a := app(inv(f), b), b := a, r := r1))
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), b ∈ y, bijective(f, x, y), app(inv(f), b) ∈ x, a ∈ x) |- app(inv(f), b) ∈ initialSegment(a, r1, x) /\ (app(f, app(inv(f), b)) === b)) by RightAnd(lastStep, inverseRelationRightCancel)
        thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), b ∈ y, bijective(f, x, y), app(inv(f), b) ∈ x, a ∈ x) |- ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) by RightExists
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), bijective(f, x, y), b ∈ y, a ∈ x) |- ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) by Cut(inverseFunctionImageInDomain, lastStep)
        have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), b ∈ initialSegment(app(f, a), r2, y), bijective(f, x, y), a ∈ x) |- ∃(c, c ∈ initialSegment(a, r1, x) /\ (app(f, c) === b))) by Cut(initialSegmentElementInDomain of (a := b, b := app(f, a), r := r2, x := y), lastStep)
        thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x, b ∈ initialSegment(app(f, a), r2, y)) |- b ∈ ran(frestr)) by Substitution.ApplyRules(rangeEq)
      }
      have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x) |- b ∈ ran(frestr) <=> b ∈ initialSegment(app(f, a), r2, y)) by RightIff(forward, backward)
      thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x) |- ∀(b, b ∈ ran(frestr) <=> b ∈ initialSegment(app(f, a), r2, y))) by RightForall
      have(thesis) by Cut(lastStep, equalityIntro of (x := ran(frestr), y := initialSegment(app(f, a), r2, y)))
    }

    val restrBijective = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x) |- bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y))) subproof {
      have((injective(f, x, y), strictWellOrder(r1, x)) |- injective(f ↾ initialSegment(a, r1, x), initialSegment(a, r1, x), y)) by Substitution.ApplyRules(xInterInitSegment)(functionRestrictionInjective of (z := initialSegment(a, r1, x)))
      have((bijective(f, x, y), strictWellOrder(r1, x)) |- injective(f ↾ initialSegment(a, r1, x), initialSegment(a, r1, x), y)) by Cut(bijectiveInjective, lastStep)
      have((bijective(f, x, y), strictWellOrder(r1, x)) |- bijective(f ↾ initialSegment(a, r1, x), initialSegment(a, r1, x), ran(f ↾ initialSegment(a, r1, x)))) by Cut(lastStep, injectiveIsBijectiveOverRange of (f := f ↾ initialSegment(a, r1, x), x := initialSegment(a, r1, x)))
      thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, x, y), a ∈ x) |- bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y))) by Substitution.ApplyRules(restrRange)
      have(thesis) by Cut(relationIsomorphismBijective, lastStep)
    }

    have((functionFrom(f, x, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x)) |- app(f, b) === app(frestr, b)) by Cut(inSegment, functionRestrictionFromApp of (x := initialSegment(a, r1, x), y := x, z := y, a := b))
    have((bijective(f, x, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x)) |- app(f, b) === app(frestr, b)) by Cut(bijectiveIsFunctionFrom, lastStep)
    val appRestr = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x)) |- app(f, b) === app(frestr, b)) by Cut(relationIsomorphismBijective, lastStep)

    val forward = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x) ==> pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) subproof {
      have((functionFrom(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), b ∈ initialSegment(a, r1, x), app(frestr, c) ∈ initialSegment(app(f, a), r2, y), pair(app(frestr, b), app(frestr, c)) ∈ r2) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(functionFromAppInCodomain of (x := initialSegment(a, r1, x), y := initialSegment(app(f, a), r2, y), a := b, f := frestr), initialSegmentOrderIntro of (b := app(f, a), r := r2, x := y, s := app(frestr, b), t := app(frestr, c)))
      have((functionFrom(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(app(frestr, b), app(frestr, c)) ∈ r2) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(functionFromAppInCodomain of (x := initialSegment(a, r1, x), y := initialSegment(app(f, a), r2, y), a := c, f := frestr), lastStep)
      have((bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(app(frestr, b), app(frestr, c)) ∈ r2) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(bijectiveIsFunctionFrom of (f := frestr, x := initialSegment(a, r1, x), y := initialSegment(app(f, a), r2, y)), lastStep)
      thenHave((bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(app(f, b), app(f, c)) ∈ r2) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Substitution.ApplyRules(appRestr, appRestr of (b := c))
      have((bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(b, c) ∈ r1) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(relationIsomorphismElimForward of (a := b, b := c), lastStep)
      have((bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y)), relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(b, c) ∈ initialSegmentOrder(a, r1, x)) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(initialSegmentOrderIsOriginalOrder of (s := b, t := c, r := r1, b := a), lastStep)
      have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x), pair(b, c) ∈ initialSegmentOrder(a, r1, x)) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by Cut(restrBijective, lastStep)
    }

    val backward = have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y) ==> pair(b, c) ∈ initialSegmentOrder(a, r1, x)) subproof {
      have((relationIsomorphism(f, r1, x, r2, y), pair(app(f, b), app(f, c)) ∈ r2, b ∈ x, b ∈ initialSegment(a, r1, x), c ∈ x, c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x)) by Cut(relationIsomorphismElimBackward of (a := b, b := c), initialSegmentOrderIntro of (b := a, r := r1, s := b, t := c))
      have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), pair(app(f, b), app(f, c)) ∈ r2, b ∈ x, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x)) by Cut(inSegment of (b := c), lastStep)
      have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), pair(app(f, b), app(f, c)) ∈ r2, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x)) by Cut(inSegment, lastStep)
      thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), pair(app(frestr, b), app(frestr, c)) ∈ r2, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x)) by Substitution.ApplyRules(appRestr, appRestr of (b := c))
      have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y), b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x)) by Cut(initialSegmentOrderIsOriginalOrder of (s := app(frestr, b), t := app(frestr, c), r := r2, b := app(f, a), x := y), lastStep)
    }

    have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, b ∈ initialSegment(a, r1, x), c ∈ initialSegment(a, r1, x)) |- pair(b, c) ∈ initialSegmentOrder(a, r1, x) <=> pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)) by RightIff(forward, backward)
    thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x) |- (b ∈ initialSegment(a, r1, x) /\ c ∈ initialSegment(a, r1, x)) ==> (pair(b, c) ∈ initialSegmentOrder(a, r1, x) <=> pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y))) by Restate
    thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x) |- ∀(c, (b ∈ initialSegment(a, r1, x) /\ c ∈ initialSegment(a, r1, x)) ==> (pair(b, c) ∈ initialSegmentOrder(a, r1, x) <=> pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y)))) by RightForall
    thenHave((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x) |- ∀(b, ∀(c, (b ∈ initialSegment(a, r1, x) /\ c ∈ initialSegment(a, r1, x)) ==> (pair(b, c) ∈ initialSegmentOrder(a, r1, x) <=> pair(app(frestr, b), app(frestr, c)) ∈ initialSegmentOrder(app(f, a), r2, y))))) by RightForall
    have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, strictWellOrder(initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)), strictWellOrder(initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y)), bijective(frestr, initialSegment(a, r1, x), initialSegment(app(f, a), r2, y))) |- isorestr) by Cut(lastStep, strictWellOrderIsomorphismIntro of (f := frestr, r1 := initialSegmentOrder(a, r1, x), x := initialSegment(a, r1, x), r2 := initialSegmentOrder(app(f, a), r2, y), y := initialSegment(app(f, a), r2, y)))
    have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, strictWellOrder(initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)), strictWellOrder(initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) |- isorestr) by Cut(restrBijective, lastStep)
    have((relationIsomorphism(f, r1, x, r2, y), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, strictWellOrder(initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) |- isorestr) by Cut(initialSegmentStrictWellOrder of (b := a, r := r1), lastStep)
    have(thesis) by Cut(initialSegmentStrictWellOrder of (b := app(f, a), r := r2, x := y), lastStep)
  }

  val closedSetIsInitialSegment = Lemma(
    (strictWellOrder(r, x), z ⊆ x, ∀(a, ∀(b, (pair(a, b) ∈ r /\ b ∈ z) ==> a ∈ z))) |- (z === x, ∃(b, b ∈ x /\ (z === initialSegment(b, r, x))))
  ) {

    val closed = ∀(a, ∀(b, (pair(a, b) ∈ r /\ b ∈ z) ==> a ∈ z))

    val diffLeastElement = have((strictWellOrder(r, x), z ⊆ x) |- (z === x, ∃(b, isLeastElement(b, x \ z, r, x)))) subproof {
      have(z ⊆ x |- (z === x, !(x ⊆ z))) by Restate.from(subsetAntisymmetry of (y := z))
      thenHave(z ⊆ x |- (z === x, x \ z =/= ∅)) by Substitution.ApplyRules(setDifferenceEmpty)
      have((strictWellOrder(r, x), z ⊆ x, x \ z ⊆ x) |- (z === x, ∃(b, isLeastElement(b, x \ z, r, x)))) by Cut(lastStep, strictWellOrderElim of (y := x \ z))
      have(thesis) by Cut(setDifferenceSubsetDomain of (y := z), lastStep)
    }

    val diffMember = have(a ∈ x |- a ∈ (x \ z) <=> a ∉ z) by Tautology.from(setDifferenceMembership of (z := a, y := z))

    val forward = have((strictWellOrder(r, x), isLeastElement(b, x \ z, r, x)) |- a ∈ initialSegment(b, r, x) ==> a ∈ z) subproof {
      have((strictPartialOrder(r, x), isLeastElement(b, x \ z, r, x), pair(a, b) ∈ r, a ∈ x) |- !(a ∉ z)) by Substitution.ApplyRules(diffMember)(belowLeastElement of (y := x \ z, a := b, b := a))
      have((strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), pair(a, b) ∈ r, a ∈ x) |- a ∈ z) by Cut(strictWellOrderPartial, lastStep)
      have((strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), a ∈ initialSegment(b, r, x), a ∈ x) |- a ∈ z) by Cut(initialSegmentElim, lastStep)
      have((strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), a ∈ initialSegment(b, r, x)) |- a ∈ z) by Cut(initialSegmentElementInDomain, lastStep)
    }

    val backward = have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- a ∈ z ==> a ∈ initialSegment(b, r, x)) subproof {
      have((isLeastElement(b, x \ z, r, x), b ∈ x) |- b ∉ z) by Substitution.ApplyRules(diffMember)(isLeastElementInSubset of (a := b, y := x \ z))
      thenHave((isLeastElement(b, x \ z, r, x), b ∈ x, b ∈ z) |- ()) by Restate
      val middle = thenHave((isLeastElement(b, x \ z, r, x), a === b, b ∈ x, a ∈ z) |- ()) by Substitution.ApplyRules(a === b)

      have(closed |- closed) by Hypothesis
      thenHave((closed, pair(b, a) ∈ r, b ∉ z, a ∈ z) |- ()) by InstantiateForall(b, a)
      thenHave((closed, pair(b, a) ∈ r, b ∈ x, b ∈ (x \ z), a ∈ z) |- ()) by Substitution.ApplyRules(diffMember of (a := b))
      have((closed, isLeastElement(b, x \ z, r, x), pair(b, a) ∈ r, b ∈ x, b ∈ (x \ z), a ∈ z) |- ()) by Cut(isLeastElementInSubset of (a := b, y := x \ z), lastStep)
      val right = have((closed, isLeastElement(b, x \ z, r, x), pair(b, a) ∈ r, b ∈ x, a ∈ z) |- ()) by Cut(isLeastElementInSubset of (a := b, y := x \ z), lastStep)

      have((closed, isLeastElement(b, x \ z, r, x), (a === b) \/ (pair(b, a) ∈ r), b ∈ x, a ∈ z) |- ()) by LeftOr(right, middle)
      have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), (a === b) \/ (pair(b, a) ∈ r) \/ (pair(a, b) ∈ r), b ∈ x, a ∈ z) |- a ∈ initialSegment(b, r, x)) by LeftOr(initialSegmentIntro, lastStep)
      have((closed, connected(r, x), strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), a ∈ x, b ∈ x, a ∈ z) |- a ∈ initialSegment(b, r, x)) by Cut(connectedElim of (y := a, z := b), lastStep)
      have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), a ∈ x, b ∈ x, a ∈ z) |- a ∈ initialSegment(b, r, x)) by Cut(strictWellOrderConnected, lastStep)
      have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), a ∈ x, a ∈ z) |- a ∈ initialSegment(b, r, x)) by Cut(isLeastElementInDomain of (y := x \ z, a := b), lastStep)
      have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x, a ∈ z) |- a ∈ initialSegment(b, r, x)) by Cut(subsetElim of (z := a, x := z, y := x), lastStep)
    }

    have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- a ∈ z <=> a ∈ initialSegment(b, r, x)) by RightIff(forward, backward)
    thenHave((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- ∀(a, a ∈ z <=> a ∈ initialSegment(b, r, x))) by RightForall
    have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- z === initialSegment(b, r, x)) by Cut(lastStep, equalityIntro of (x := z, y := initialSegment(b, r, x)))
    have((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- b ∈ x /\ (z === initialSegment(b, r, x))) by RightAnd(isLeastElementInDomain of (y := x \ z, a := b), lastStep)
    thenHave((closed, strictWellOrder(r, x), isLeastElement(b, x \ z, r, x), z ⊆ x) |- ∃(b, b ∈ x /\ (z === initialSegment(b, r, x)))) by RightExists
    thenHave((closed, strictWellOrder(r, x), ∃(b, isLeastElement(b, x \ z, r, x)), z ⊆ x) |- ∃(b, b ∈ x /\ (z === initialSegment(b, r, x)))) by LeftExists
    have(thesis) by Cut(diffLeastElement, lastStep)
  }

  val initialSegmentIsomorphicCases = Lemma(
    (strictWellOrder(r1, x), strictWellOrder(r2, y)) |-
      (r1, x) ≃ (r2, y) \/
      ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)) \/
      ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y)))
  ) {
    val fDef = ∀(p, p ∈ f <=> (p ∈ (x × y) /\ 
      (initialSegmentOrder(fst(p), r1, x), initialSegment(fst(p), r1, x)) ≃ (initialSegmentOrder(snd(p), r2, y), initialSegment(snd(p), r2, y))))

    val fExistence = have(∃(f, fDef)) subproof {
      have(∃!(f, fDef)) by UniqueComprehension(x × y, lambda(p, (initialSegmentOrder(fst(p), r1, x), initialSegment(fst(p), r1, x)) ≃ (initialSegmentOrder(snd(p), r2, y), initialSegment(snd(p), r2, y))))
      have(thesis) by Cut(lastStep, existsOneImpliesExists of (P := lambda(f, fDef)))
    }

    val fDefElim = have((fDef, pair(a, b) ∈ f) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) subproof {
      have(fDef |- fDef) by Hypothesis
      thenHave(fDef |- pair(a, b) ∈ f <=> (pair(a, b) ∈ (x × y) /\ 
        (initialSegmentOrder(fst(pair(a, b)), r1, x), initialSegment(fst(pair(a, b)), r1, x)) ≃ (initialSegmentOrder(snd(pair(a, b)), r2, y), initialSegment(snd(pair(a, b)), r2, y)))) by InstantiateForall(pair(a, b))
      thenHave((fDef, pair(a, b) ∈ f) |- (initialSegmentOrder(fst(pair(a, b)), r1, x), initialSegment(fst(pair(a, b)), r1, x)) ≃ (initialSegmentOrder(snd(pair(a, b)), r2, y), initialSegment(snd(pair(a, b)), r2, y))) by Weakening
      thenHave(thesis) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction)
    }

    val fDefIntro = have((fDef, a ∈ x, b ∈ y, (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) |- pair(a, b) ∈ f) subproof {
      have(fDef |- fDef) by Hypothesis
      thenHave(fDef |- pair(a, b) ∈ f <=> (pair(a, b) ∈ (x × y) /\ 
        (initialSegmentOrder(fst(pair(a, b)), r1, x), initialSegment(fst(pair(a, b)), r1, x)) ≃ (initialSegmentOrder(snd(pair(a, b)), r2, y), initialSegment(snd(pair(a, b)), r2, y)))) by InstantiateForall(pair(a, b))
      thenHave((fDef, pair(a, b) ∈ (x × y), (initialSegmentOrder(fst(pair(a, b)), r1, x), initialSegment(fst(pair(a, b)), r1, x)) ≃ (initialSegmentOrder(snd(pair(a, b)), r2, y), initialSegment(snd(pair(a, b)), r2, y))) |-  pair(a, b) ∈ f) by Weakening
      have((fDef, a ∈ x, b ∈ y, (initialSegmentOrder(fst(pair(a, b)), r1, x), initialSegment(fst(pair(a, b)), r1, x)) ≃ (initialSegmentOrder(snd(pair(a, b)), r2, y), initialSegment(snd(pair(a, b)), r2, y))) |-  pair(a, b) ∈ f) by Cut(cartesianProductIntro, lastStep)
      thenHave(thesis) by Substitution.ApplyRules(firstInPairReduction, secondInPairReduction)
    }

    val fRelationBetween = have(fDef |- relationBetween(f, x, y)) subproof {
      have(fDef |- fDef) by Hypothesis
      thenHave(fDef |- p ∈ f <=> (p ∈ (x × y) /\ 
      (initialSegmentOrder(fst(p), r1, x), initialSegment(fst(p), r1, x)) ≃ (initialSegmentOrder(snd(p), r2, y), initialSegment(snd(p), r2, y)))) by InstantiateForall(p)
      thenHave((fDef, p ∈ f) |- p ∈ (x × y)) by Weakening
      thenHave(fDef |- p ∈ f ==> p ∈ (x × y)) by RightImplies
      thenHave(fDef |- ∀(p, p ∈ f ==> p ∈ (x × y))) by RightForall
      have(fDef |- f ⊆ (x × y)) by Cut(lastStep, subsetIntro of (x := f, y := (x × y)))
      have(fDef |- relationBetween(f, x, y)) by Cut(lastStep, relationBetweenIntro of (a := x, b := y, r := f))
    }

    val fRelation = have(fDef |- relation(f)) by Cut(fRelationBetween, relationBetweenIsRelation of (r := f, a := x, b := y))
    
    val fFunctionFrom = have((fDef, strictWellOrder(r2, y)) |- functionFrom(f, dom(f), ran(f)))  subproof {
      have((fDef, pair(a, b) ∈ f, (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x))) |- (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by 
        Cut(fDefElim, isomorphicTransitivity of (r1 := initialSegmentOrder(c, r2, y), x := initialSegment(c, r2, y), r2 := initialSegmentOrder(a, r1, x), y := initialSegment(a, r1, x), r3 := initialSegmentOrder(b, r2, y), z := initialSegment(b, r2, y)))
      have((fDef, pair(a, b) ∈ f, (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y))) |- (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by 
        Cut(isomorphicSymmetry of (r1 := initialSegmentOrder(a, r1, x), x := initialSegment(a, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((fDef, pair(a, b) ∈ f, pair(a, c) ∈ f) |- (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by 
        Cut(fDefElim of (b := c), lastStep)
      thenHave((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2) |- (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(b, initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), initialSegment(b, initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)))) by 
        Substitution.ApplyRules(initialSegmentRestriction of (a := b, b := c, r := r2, x := y), initialSegmentOrderRestriction of (a := b, b := c, r := r2, x := y))
      have((fDef, strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), b ∈ initialSegment(c, r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2) |- ()) by 
        RightAnd(lastStep, noIsomorphismWithInitialSegment of (r := initialSegmentOrder(c, r2, y), x := initialSegment(c, r2, y)))
      have((fDef, strictWellOrder(r2, y), b ∈ initialSegment(c, r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2) |- ()) by 
        Cut(initialSegmentStrictWellOrder of (b := c, r := r2, x := y), lastStep)
      have((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2) |- ()) by 
        Cut(initialSegmentIntro of (a := b, b := c, r := r2, x := y), lastStep)
      val neqContradiction = have((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2 \/ (pair(c, b) ∈ r2)) |- ()) by 
        LeftOr(lastStep, lastStep of (c := b, b := c))
      have(b === c |- b === c) by Hypothesis
      have((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, pair(b, c) ∈ r2 \/ (b === c) \/ (pair(c, b) ∈ r2)) |- b === c) by 
        LeftOr(lastStep, neqContradiction)
      have((fDef, connected(r2, y), strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, b ∈ y, c ∈ y) |- b === c) by 
        Cut(connectedElim of (r := r2, x := y, y := b, z := c), lastStep)
      have((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, b ∈ y, c ∈ y) |- b === c) by 
        Cut(strictWellOrderConnected of (r := r2, x := y), lastStep)
      thenHave((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f, a ∈ x /\ b ∈ y, a ∈ x /\ c ∈ y) |- b === c) by Weakening
      have((fDef, strictWellOrder(r2, y), relationBetween(f, x, y), pair(a, c) ∈ f, pair(a, b) ∈ f, a ∈ x /\ c ∈ y) |- b === c) by Cut(relationBetweenElimPair of (r := f, x := a, y := b, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r2, y), relationBetween(f, x, y), pair(a, c) ∈ f, pair(a, b) ∈ f) |- b === c) by 
        Cut(relationBetweenElimPair of (r := f, x := a, y := c, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r2, y), pair(a, c) ∈ f, pair(a, b) ∈ f) |- b === c) by Cut(fRelationBetween, lastStep)
      thenHave((fDef, strictWellOrder(r2, y)) |- (pair(a, c) ∈ f /\ pair(a, b) ∈ f) ==> (b === c)) by Restate
      thenHave((fDef, strictWellOrder(r2, y)) |- ∀(c, pair(a, c) ∈ f /\ pair(a, b) ∈ f ==> (b === c))) by RightForall
      thenHave((fDef, strictWellOrder(r2, y)) |- ∀(b, ∀(c, pair(a, c) ∈ f /\ pair(a, b) ∈ f ==> (b === c)))) by RightForall
      thenHave((fDef, strictWellOrder(r2, y)) |- ∀(a, ∀(b, ∀(c, pair(a, c) ∈ f /\ pair(a, b) ∈ f ==> (b === c))))) by RightForall
      have((fDef, strictWellOrder(r2, y), relation(f)) |- functional(f)) by Cut(lastStep, functionalIntro)
      have((fDef, strictWellOrder(r2, y)) |- functional(f)) by Cut(fRelation, lastStep)
      have(thesis) by Cut(lastStep, functionalIsFunctionFrom)
    }

    val fBijective = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- bijective(f, dom(f), ran(f))) subproof {
      have((fDef, pair(b, c) ∈ f, (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)) ≃ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x))) |- (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ) by 
        Cut(fDefElim of (a := b, b := c), isomorphicTransitivity of (r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y), r3 := initialSegmentOrder(a, r1, x), z := initialSegment(a, r1, x)))
      have((fDef, pair(b, c) ∈ f, (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y))) |- (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x))) by 
        Cut(isomorphicSymmetry of (r1 := initialSegmentOrder(a, r1, x), x := initialSegment(a, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((fDef, pair(a, c) ∈ f, pair(b, c) ∈ f) |- (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x))) by 
        Cut(fDefElim of (b := c), lastStep)
      thenHave((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1) |- (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(a, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), initialSegment(a, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)))) by 
        Substitution.ApplyRules(initialSegmentRestriction of (r := r1), initialSegmentOrderRestriction of (r := r1))
      have((fDef, strictWellOrder(r1, x), strictWellOrder(initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), a ∈ initialSegment(b, r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1) |- ()) by 
        RightAnd(lastStep, noIsomorphismWithInitialSegment of (b := a, r := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x)))
      have((fDef, strictWellOrder(r1, x), a ∈ initialSegment(b, r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1) |- ()) by 
        Cut(initialSegmentStrictWellOrder of (r := r1), lastStep)
      have((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1) |- ()) by 
        Cut(initialSegmentIntro of (r := r1), lastStep)
      val neqContradiction = have((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1 \/ (pair(b, a) ∈ r1)) |- ()) by LeftOr(lastStep, lastStep of (a := b, b := a))
      have(a === b |- a === b) by Hypothesis
      have((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, pair(a, b) ∈ r1 \/ (a === b) \/ (pair(b, a) ∈ r1)) |- a === b) by LeftOr(lastStep, neqContradiction)
      have((fDef, connected(r1, x), strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ x, b ∈ x) |- a === b) by Cut(connectedElim of (r := r1, y := a, z := b), lastStep)
      have((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ x, b ∈ x) |- a === b) by Cut(strictWellOrderConnected of (r := r1), lastStep)
      thenHave((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ x /\ c ∈ y, b ∈ x /\ c ∈ y) |- a === b) by Weakening
      have((fDef, strictWellOrder(r1, x), relationBetween(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ x /\ c ∈ y) |- a === b) by Cut(relationBetweenElimPair of (r := f, x := b, y := c, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r1, x), relationBetween(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f) |- a === b) by Cut(relationBetweenElimPair of (r := f, x := a, y := c, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r1, x), pair(a, c) ∈ f, pair(b, c) ∈ f) |- a === b) by Cut(fRelationBetween, lastStep)
      thenHave((fDef, strictWellOrder(r1, x)) |- (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b)) by Restate
      thenHave((fDef, strictWellOrder(r1, x)) |- ∀(c, pair(a, c) ∈ f /\ pair(b, c) ∈ f ==> (a === b))) by RightForall
      thenHave((fDef, strictWellOrder(r1, x)) |- ∀(b, ∀(c, pair(a, c) ∈ f /\ pair(b, c) ∈ f ==> (a === b)))) by RightForall
      thenHave((fDef, strictWellOrder(r1, x)) |- ∀(a, ∀(b, ∀(c, pair(a, c) ∈ f /\ pair(b, c) ∈ f ==> (a === b))))) by RightForall
      have((fDef, strictWellOrder(r1, x), functionFrom(f, dom(f), ran(f))) |- injective(f, dom(f), ran(f))) by Cut(lastStep, injectiveIntroAlt of (x := dom(f), y := ran(f)))
      have((fDef, strictWellOrder(r1, x), functionFrom(f, dom(f), ran(f))) |- bijective(f, dom(f), ran(f))) by Cut(lastStep, injectiveIsBijectiveOverRange of (x := dom(f), y := ran(f)))
      have(thesis) by Cut(fFunctionFrom, lastStep)
    }

    val inSegment = have((strictWellOrder(r, x), a ∈ initialSegment(b, r, x)) |- a ∈ x) by Cut(initialSegmentSubsetDomain, subsetElim of (z := a, x := initialSegment(b, r, x), y := x))

    val domClosed = have((fDef, b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) subproof {
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), strictWellOrder(initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), c) ∈ r2) |- 
      relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
        Substitution.ApplyRules(initialSegmentOrderRestriction, initialSegmentRestriction)(initialSegmentIsomorphismRestriction of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)))
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), c) ∈ r2) |- 
      relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
        Cut(initialSegmentStrictWellOrder of (r := r1), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), c) ∈ r2) |- relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
        Cut(initialSegmentStrictWellOrder of (b := c, r := r2, x := y), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, app(g, a) ∈ initialSegment(c, r2, y)) |- relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by Cut(initialSegmentElim of (a := app(g, a), b := c, r := r2, x := y), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1) |- relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by Cut(relationIsomorphismAppInCodomain of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by Cut(initialSegmentIntro of (r := r1), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by Cut(lastStep, isomorphicIntro of (f := g ↾ initialSegment(a, r1, x), r1 := initialSegmentOrder(a, r1, x), x := initialSegment(a, r1, x), r2 := initialSegmentOrder(app(g, a), r2, y), y := initialSegment(app(g, a), r2, y)))
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, app(g, a) ∈ y, pair(a, b) ∈ r1) |- pair(a, app(g, a)) ∈ f) by Cut(lastStep, fDefIntro of (b := app(g, a)))
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, app(g, a) ∈ y, pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(lastStep, relationDomainIntroPair of (r := f, b := app(g, a)))
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), app(g, a) ∈ y, pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(inSegment of (r := r1), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), app(g, a) ∈ initialSegment(c, r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(inSegment of (b := c, r := r2, x := y, a := app(g, a)), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(relationIsomorphismAppInCodomain of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(initialSegmentIntro of (r := r1), lastStep)
      thenHave((fDef, ∃(g, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y))), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by LeftExists
      have((fDef, (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(isomorphicElim of (r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((fDef, pair(b, c) ∈ f, strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by Cut(fDefElim of (a := b, b := c), lastStep)
      thenHave((fDef, ∃(c, pair(b, c) ∈ f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- a ∈ dom(f)) by LeftExists
      have(thesis) by Cut(relationDomainElim of (r := f, a := b), lastStep)
    }

    val domInitialSegment = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (dom(f) === x) \/ ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x)))) subproof {
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (pair(a, b) ∈ r1 /\ b ∈ dom(f)) ==> a ∈ dom(f)) by Restate.from(domClosed)
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(b, (pair(a, b) ∈ r1 /\ b ∈ dom(f)) ==> a ∈ dom(f))) by RightForall
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(a, ∀(b, (pair(a, b) ∈ r1 /\ b ∈ dom(f)) ==> a ∈ dom(f)))) by RightForall
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) ⊆ x) |- (dom(f) === x, ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))))) by Cut(lastStep, closedSetIsInitialSegment of (z := dom(f), r := r1))
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), relationBetween(f, x, y)) |- (dom(f) === x, ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))))) by Cut(relationBetweenDomain of (r := f, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (dom(f) === x, ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))))) by Cut(fRelationBetween, lastStep)
    }

    val ranInitialSegment = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (ran(f) === y) \/ ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y)))) subproof {

      val ig = app(inv(g), d)

      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(app(g, ig), c) ∈ r2) |- relationIsomorphism(g ↾ initialSegment(ig, r1, x), initialSegmentOrder(ig, r1, x), initialSegment(ig, r1, x), initialSegmentOrder(app(g, ig), r2, y), initialSegment(app(g, ig), r2, y))) by 
        Substitution.ApplyRules(initialSegmentOrderRestriction, initialSegmentRestriction)(initialSegmentIsomorphismRestriction of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y), a := ig))
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(app(g, ig), c) ∈ r2) |- relationIsomorphism(g ↾ initialSegment(ig, r1, x), initialSegmentOrder(ig, r1, x), initialSegment(ig, r1, x), initialSegmentOrder(app(g, ig), r2, y), initialSegment(app(g, ig), r2, y))) by
        Cut(initialSegmentStrictWellOrder of (r := r1), lastStep)
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(app(g, ig), c) ∈ r2) |- relationIsomorphism(g ↾ initialSegment(ig, r1, x), initialSegmentOrder(ig, r1, x), initialSegment(ig, r1, x), initialSegmentOrder(app(g, ig), r2, y), initialSegment(app(g, ig), r2, y))) by
        Cut(initialSegmentStrictWellOrder of (b := c, r := r2, x := y), lastStep)
      thenHave((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ initialSegment(c, r2, y), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(d, c) ∈ r2) |- relationIsomorphism(g ↾ initialSegment(ig, r1, x), initialSegmentOrder(ig, r1, x), initialSegment(ig, r1, x), initialSegmentOrder(d, r2, y), initialSegment(d, r2, y))) by
        Substitution.ApplyRules(inverseRelationRightCancel of (f := g, x := initialSegment(b, r1, x), y := initialSegment(c, r2, y), b := d))
      have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ initialSegment(c, r2, y), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(d, c) ∈ r2) |- (initialSegmentOrder(ig, r1, x), initialSegment(ig, r1, x)) ≃ (initialSegmentOrder(d, r2, y), initialSegment(d, r2, y))) by 
        Cut(lastStep, isomorphicIntro of (f := g ↾ initialSegment(ig, r1, x), r1 := initialSegmentOrder(ig, r1, x), x := initialSegment(ig, r1, x), r2 := initialSegmentOrder(d, r2, y), y := initialSegment(d, r2, y)))
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ y, d ∈ initialSegment(c, r2, y), ig ∈ x, ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(lastStep, fDefIntro of (a := ig, b := d))
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ y, d ∈ initialSegment(c, r2, y), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(inSegment of (a := ig, r := r1), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ initialSegment(c, r2, y), ig ∈ initialSegment(b, r1, x), pair(ig, b) ∈ r1, pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(inSegment of (a := d, b := c, r := r2, x := y), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ initialSegment(c, r2, y), ig ∈ initialSegment(b, r1, x), pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(initialSegmentElim of (a := ig, r := r1), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), d ∈ initialSegment(c, r2, y), pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(inverseFunctionImageInDomain of (f := g, x := initialSegment(b, r1, x), y := initialSegment(c, r2, y), b := d), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(initialSegmentIntro of (a := d, r := r2, x := y, b := c), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- pair(ig, d) ∈ f) by 
        Cut(relationIsomorphismBijective of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(c, r2, y), y := initialSegment(c, r2, y)), lastStep)
      have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by 
        Cut(lastStep, relationRangeIntroPair of (r := f, a := ig, b := d))
      thenHave((fDef, ∃(g, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(c, r2, y), initialSegment(c, r2, y))), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by LeftExists
      thenHave((fDef, (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(c, r2, y), initialSegment(c, r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by Substitution.ApplyRules(isomorphic.definition)
      have((fDef, pair(b, c) ∈ f, strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by Cut(fDefElim of (a := b, b := c), lastStep)
      thenHave((fDef, ∃(b, pair(b, c) ∈ f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by LeftExists
      have((fDef, c ∈ ran(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(d, c) ∈ r2) |- d ∈ ran(f)) by Cut(relationRangeElim of (b := c, r := f), lastStep)
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (pair(d, c) ∈ r2 /\ c ∈ ran(f)) ==> d ∈ ran(f)) by Restate
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(c, (pair(d, c) ∈ r2 /\ c ∈ ran(f)) ==> d ∈ ran(f))) by RightForall
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(d, ∀(c, (pair(d, c) ∈ r2 /\ c ∈ ran(f)) ==> d ∈ ran(f)))) by RightForall
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ran(f) ⊆ y) |- (ran(f) === y, ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y))))) by Cut(lastStep, closedSetIsInitialSegment of (z := ran(f), x := y, r := r2))
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), relationBetween(f, x, y)) |- (ran(f) === y, ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y))))) by Cut(relationBetweenRange of (r := f, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (ran(f) === y, ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y))))) by Cut(fRelationBetween, lastStep)
    }

    val r1Dom = relationRestriction(r1, dom(f), dom(f))
    val r2Ran = relationRestriction(r2, ran(f), ran(f))

    have((fDef, a ∈ dom(f), functionFrom(f, dom(f), ran(f))) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) by Cut(appIntroFunctionFrom of (x := dom(f), y := ran(f)), fDefElim of (b := app(f, a)))
    val fDefAppElim = have((fDef, a ∈ dom(f), strictWellOrder(r2, y)) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) by Cut(fFunctionFrom, lastStep)

    val fIsomorphism = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (r1Dom, dom(f)) ≃ (r2Ran, ran(f))) subproof{

      val forward = have((fDef, a ∈ dom(f), b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y)) |- pair(a, b) ∈ r1Dom ==> pair(app(f, a), app(f, b)) ∈ r2Ran) subproof {
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), pair(a, b) ∈ r1, strictWellOrder(r1, x)) |- app(g, a) ∈ initialSegment(app(f, b), r2, y)) by 
          Cut(initialSegmentIntro of (r := r1), relationIsomorphismAppInCodomain of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y), y := initialSegment(app(f, b), r2, y))) 
        val gLowerThanF = have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), pair(a, b) ∈ r1, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- pair(app(g, a), app(f, b)) ∈ r2) by 
          Cut(lastStep, initialSegmentElim of (a := app(g, a), b := app(f, b), r := r2, x := y))

        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), strictWellOrder(initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
          Substitution.ApplyRules(initialSegmentOrderRestriction, initialSegmentRestriction)(initialSegmentIsomorphismRestriction of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y), y := initialSegment(app(f, b), r2, y)))
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
          Cut(initialSegmentStrictWellOrder of (r := r1), lastStep)
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, pair(app(g, a), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
          Cut(initialSegmentStrictWellOrder of (b := app(f, b), r := r2, x := y), lastStep)
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1) |- 
        relationIsomorphism(g ↾ initialSegment(a, r1, x), initialSegmentOrder(a, r1, x), initialSegment(a, r1, x), initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
          Cut(gLowerThanF, lastStep)
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1) |- 
        (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(app(g, a), r2, y), initialSegment(app(g, a), r2, y))) by 
          Cut(lastStep, isomorphicIntro of (f := g ↾ initialSegment(a, r1, x), r1 := initialSegmentOrder(a, r1, x), x := initialSegment(a, r1, x), r2 := initialSegmentOrder(app(g, a), r2, y), y := initialSegment(app(g, a), r2, y)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1,
        x), strictWellOrder(r2, y), a ∈ x, a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, app(g, a) ∈ y) |- pair(a, app(g, a)) ∈ f) by 
          Cut(lastStep, fDefIntro of (b := app(g, a)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, app(g, a) ∈ initialSegment(app(f, b), r2, y)) |- pair(a, app(g, a)) ∈ f) by 
          Cut(inSegment of (a := app(g, a), b := app(f, b), r := r2, x := y), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1, app(g, a) ∈ initialSegment(app(f, b), r2, y)) |- pair(a, app(g, a)) ∈ f) by 
          Cut(inSegment of (r := r1), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ initialSegment(b, r1, x), pair(a, b) ∈ r1) |- pair(a, app(g, a)) ∈ f) by 
          Cut(relationIsomorphismAppInCodomain of (f := g, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y), y := initialSegment(app(f, b), r2, y)), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(a, app(g, a)) ∈ f) by 
          Cut(initialSegmentIntro of (r := r1), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), functionFrom(f, dom(f), ran(f)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- app(f, a) === app(g, a)) by 
          Cut(lastStep, pairIsAppFunctionFrom of (x := dom(f), y := ran(f), b := app(g, a)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- app(f, a) === app(g, a)) by 
          Cut(fFunctionFrom, lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by 
          Substitution.ApplyRules(lastStep)(gLowerThanF)
        thenHave((fDef, ∃(g, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y))), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by LeftExists
        have((fDef, (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by 
          Cut(isomorphicElim of (r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y), y := initialSegment(app(f, b), r2, y)), lastStep)
        have((fDef, b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2) by 
          Cut(fDefAppElim of (a := b), lastStep)
        have((fDef, b ∈ dom(f), app(f, a) ∈ ran(f), app(f, b) ∈ ran(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2Ran) by 
          Cut(lastStep, relationRestrictionIntroPair of (r := r2, a := app(f, a), b := app(f, b), x := ran(f), y := ran(f)))
        have((fDef, functionFrom(f, dom(f), ran(f)), b ∈ dom(f), app(f, a) ∈ ran(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2Ran) by 
          Cut(functionFromAppInCodomain of (a := b, x := dom(f), y := ran(f)), lastStep)
        have((fDef, functionFrom(f, dom(f), ran(f)), b ∈ dom(f), a ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1) |- pair(app(f, a), app(f, b)) ∈ r2Ran) by 
          Cut(functionFromAppInCodomain of (x := dom(f), y := ran(f)), lastStep)
        have((fDef, functionFrom(f, dom(f), ran(f)), b ∈ dom(f), a ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1Dom) |- pair(app(f, a), app(f, b)) ∈ r2Ran) by 
          Cut(relationRestrictionInRelation of (r := r1, x := dom(f), y := dom(f), p := pair(a, b)), lastStep)
        have((fDef, a ∈ dom(f), b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(a, b) ∈ r1Dom) |- pair(app(f, a), app(f, b)) ∈ r2Ran) by Cut(fFunctionFrom, lastStep)
      }

      val backward = have((fDef, a ∈ dom(f), b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y)) |- pair(app(f, a), app(f, b)) ∈ r2Ran ==> pair(a, b) ∈ r1Dom) subproof {

        val igfa = app(inv(g), app(f, a))

        have((bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), pair(app(f, a), app(f, b)) ∈ r2, strictWellOrder(r2, y)) |- igfa ∈ initialSegment(b, r1, x)) by 
          Cut(initialSegmentIntro of (a := app(f, a), b := app(f, b), r := r2, x := y), inverseFunctionImageInDomain of (f := g, x := initialSegment(b, r1, x), y := initialSegment(app(f, b), r2, y), b := app(f, a)))
        val igfaB = have((bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), pair(app(f, a), app(f, b)) ∈ r2, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- pair(igfa, b) ∈ r1) by 
          Cut(lastStep, initialSegmentElim of (a := igfa, r := r1))

        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)), strictWellOrder(initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(g, igfa), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(igfa, r1, x), initialSegmentOrder(igfa, r1, x), initialSegment(igfa, r1, x), initialSegmentOrder(app(g, igfa), r2, y), initialSegment(app(g, igfa), r2, y))) by 
          Substitution.ApplyRules(initialSegmentOrderRestriction, initialSegmentRestriction)(initialSegmentIsomorphismRestriction of (f := g, a := igfa, r1 := initialSegmentOrder(b, r1, x), x := initialSegment(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y), y := initialSegment(app(f, b), r2, y)))
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(g, igfa), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(igfa, r1, x), initialSegmentOrder(igfa, r1, x), initialSegment(igfa, r1, x), initialSegmentOrder(app(g, igfa), r2, y), initialSegment(app(g, igfa), r2, y))) by 
          Cut(initialSegmentStrictWellOrder of (r := r1), lastStep)
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(g, igfa), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(igfa, r1, x), initialSegmentOrder(igfa, r1, x), initialSegment(igfa, r1, x), initialSegmentOrder(app(g, igfa), r2, y), initialSegment(app(g, igfa), r2, y))) by 
          Cut(initialSegmentStrictWellOrder of (b := app(f, b), r := r2, x := y), lastStep)
        thenHave((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2) |- 
        relationIsomorphism(g ↾ initialSegment(igfa, r1, x), initialSegmentOrder(igfa, r1, x), initialSegment(igfa, r1, x), initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) by 
          Substitution.ApplyRules(inverseRelationRightCancel of (f := g, x := initialSegment(b, r1, x), y := initialSegment(app(f, b), r2, y), b := app(f, a)))
        have((relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2) |- 
        (initialSegmentOrder(igfa, r1, x), initialSegment(igfa, r1, x)) ≃ (initialSegmentOrder(app(f, a), r2, y), initialSegment(app(f, a), r2, y))) by Cut(lastStep, isomorphicIntro of (f := g ↾ initialSegment(igfa, r1, x), r1 := initialSegmentOrder(igfa, r1, x), x := initialSegment(igfa, r1, x), r2 := initialSegmentOrder(app(f, a), r2, y), y := initialSegment(app(f, a), r2, y)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2) |- pair(igfa, app(f, a)) ∈ f) by 
          Cut(lastStep, fDefIntro of (a := igfa, b := app(f, a)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), functionFrom(f, dom(f), ran(f)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2) |- app(f, igfa) === app(f, a)) by 
          Cut(lastStep, pairIsAppFunctionFrom of (x := dom(f), y := ran(f), a := igfa, b := app(f, a)))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), injective(f, dom(f), ran(f)), functionFrom(f, dom(f), ran(f)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), igfa ∈ dom(f)) |- igfa === a) by 
          Cut(lastStep, injectiveElim of (x := dom(f), y := ran(f), a := igfa, b := a))
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), injective(f, dom(f), ran(f)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), igfa ∈ dom(f)) |- igfa === a) by 
          Cut(fFunctionFrom, lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), bijective(f, dom(f), ran(f)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), igfa ∈ dom(f)) |- igfa === a) by 
          Cut(bijectiveInjective of (x := dom(f), y := ran(f)), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), igfa ∈ dom(f)) |- igfa === a) by 
          Cut(fBijective, lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(igfa, b) ∈ r1, pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- igfa === a) by 
          Cut(domClosed of (a := igfa), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- igfa === a) by 
          Cut(igfaB, lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ x, igfa ∈ initialSegment(b, r1, x), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Substitution.ApplyRules(lastStep)(igfaB)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ y, app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ initialSegment(b, r1, x), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Cut(inSegment of (a := igfa, r := r1), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ initialSegment(app(f, b), r2, y), igfa ∈ initialSegment(b, r1, x), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Cut(inSegment of (a := app(f, a), b := app(f, b), r := r2, x := y), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), app(f, a) ∈ initialSegment(app(f, b), r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Cut(inverseFunctionImageInDomain of (b := app(f, a), x := initialSegment(b, r1, x), y := initialSegment(app(f, b), r2, y), f := g), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), bijective(g, initialSegment(b, r1, x), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Cut(initialSegmentIntro of (a := app(f, a), b := app(f, b), r := r2, x := y), lastStep)
        have((fDef, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Cut(relationIsomorphismBijective of (f := g, x := initialSegment(b, r1, x), y := initialSegment(app(f, b), r2, y), r1 := initialSegmentOrder(b, r1, x), r2 := initialSegmentOrder(app(f, b), r2, y)), lastStep)
        thenHave((fDef, ∃(g, relationIsomorphism(g, initialSegmentOrder(b, r1, x), initialSegment(b, r1, x), initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y))), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by LeftExists
        thenHave((fDef, (initialSegmentOrder(b, r1, x), initialSegment(b, r1, x)) ≃ (initialSegmentOrder(app(f, b), r2, y), initialSegment(app(f, b), r2, y)), strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by 
          Substitution.ApplyRules(isomorphic.definition)
        have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1) by Cut(fDefAppElim of (a := b), lastStep)
        have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1Dom) by Cut(lastStep, relationRestrictionIntroPair of (r := r1, x := dom(f), y := dom(f)))
        have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), pair(app(f, a), app(f, b)) ∈ r2Ran, a ∈ dom(f), b ∈ dom(f)) |- pair(a, b) ∈ r1Dom) by Cut(relationRestrictionInRelation of (r := r2, x := ran(f), y := ran(f), p := pair(app(f, a), app(f, b))), lastStep)
      }
      
      have((fDef, a ∈ dom(f), b ∈ dom(f), strictWellOrder(r1, x), strictWellOrder(r2, y)) |- pair(a, b) ∈ r1Dom <=> pair(app(f, a), app(f, b)) ∈ r2Ran) by RightIff(forward, backward)
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (a ∈ dom(f) /\ b ∈ dom(f)) ==> (pair(a, b) ∈ r1Dom <=> pair(app(f, a), app(f, b)) ∈ r2Ran)) by Restate
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(b, (a ∈ dom(f) /\ b ∈ dom(f)) ==> (pair(a, b) ∈ r1Dom <=> pair(app(f, a), app(f, b)) ∈ r2Ran))) by RightForall
      thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- ∀(a, ∀(b, (a ∈ dom(f) /\ b ∈ dom(f)) ==> (pair(a, b) ∈ r1Dom <=> pair(app(f, a), app(f, b)) ∈ r2Ran)))) by RightForall
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), strictWellOrder(r1Dom, dom(f)), strictWellOrder(r2Ran, ran(f)), bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by Cut(lastStep, strictWellOrderIsomorphismIntro of (r1 := r1Dom, x := dom(f), r2 := r2Ran, y := ran(f)))
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) ⊆ x, strictWellOrder(r2Ran, ran(f)), bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by Cut(relationRestrictionStrictWellOrder of (r := r1, y := dom(f)), lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) ⊆ x, ran(f) ⊆ y, bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by 
        Cut(relationRestrictionStrictWellOrder of (r := r2, x := y, y := ran(f)), lastStep)
      have((fDef, relationBetween(f, x, y), strictWellOrder(r1, x), strictWellOrder(r2, y), ran(f) ⊆ y, bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by 
        Cut(relationBetweenDomain of (r := f, a := x, b := y), lastStep)
      have((fDef, relationBetween(f, x, y), strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by 
        Cut(relationBetweenRange of (r := f, a := x, b := y), lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), bijective(f, dom(f), ran(f))) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by 
        Cut(fRelationBetween, lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- relationIsomorphism(f, r1Dom, dom(f), r2Ran, ran(f))) by 
        Cut(fBijective, lastStep)
      have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- (r1Dom, dom(f)) ≃ (r2Ran, ran(f))) by 
        Cut(lastStep, isomorphicIntro of (r1 := r1Dom, x := dom(f), r2 := r2Ran, y := ran(f)))
    }

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x) |- (relationRestriction(r1, x, x), x) ≃ (r2Ran, ran(f))) by Substitution.ApplyRules(dom(f) === x)(fIsomorphism)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), relationBetween(r1, x, x), dom(f) === x) |- (r1, x) ≃ (r2Ran, ran(f))) by Substitution.ApplyRules(relationRestrictionOnItself of (r := r1, y := x))
    val case1 = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x) |- (r1, x) ≃ (r2Ran, ran(f))) by Cut(strictWellOrderIsRelationBetween of (r := r1), lastStep)

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, ran(f) === y) |- (r1, x) ≃ (relationRestriction(r2, y, y), y)) by Substitution.ApplyRules(ran(f) === y)(case1)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), relationBetween(r2, y, y), dom(f) === x, ran(f) === y) |- (r1, x) ≃ (r2, y)) by Substitution.ApplyRules(relationRestrictionOnItself of (r := r2, x := y))
    val case11 = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, ran(f) === y) |- (r1, x) ≃ (r2, y)) by Cut(strictWellOrderIsRelationBetween of (r := r2, x := y), lastStep)

    val hyp = have(b ∈ y |- b ∈ y) by Hypothesis

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, ran(f) === initialSegment(b, r2, y)) |- (r1, x) ≃ (relationRestriction(r2, initialSegment(b, r2, y), initialSegment(b, r2, y)), initialSegment(b, r2, y))) by Substitution.ApplyRules(ran(f) === initialSegment(b, r2, y))(case1)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, ran(f) === initialSegment(b, r2, y)) |- (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, b ∈ y, (ran(f) === initialSegment(b, r2, y))) |- b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by RightAnd(lastStep, hyp)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, b ∈ y /\ (ran(f) === initialSegment(b, r2, y))) |- b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by LeftAnd
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, b ∈ y /\ (ran(f) === initialSegment(b, r2, y))) |- ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y)))) by RightExists
    val case12 = thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y)))) |- ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y)))) by LeftExists

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x, (ran(f) === y) \/ ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y)))) |- ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))))) by LeftOr(case11, case12)
    val finalCase1 = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === x) |- ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))))) by Cut(ranInitialSegment, lastStep)

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x)) |- (relationRestriction(r1, initialSegment(a, r1, x), initialSegment(a, r1, x)), initialSegment(a, r1, x)) ≃ (r2Ran, ran(f))) by Substitution.ApplyRules(dom(f) === initialSegment(a, r1, x))(fIsomorphism)
    val case2 = thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x)) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2Ran, ran(f))) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)

    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x), ran(f) === y) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (relationRestriction(r2, y, y), y)) by Substitution.ApplyRules(ran(f) === y)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), relationBetween(r2, y, y), dom(f) === initialSegment(a, r1, x), ran(f) === y) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)) by Substitution.ApplyRules(relationRestrictionOnItself of (r := r2, x := y))
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x), ran(f) === y) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)) by Cut(strictWellOrderIsRelationBetween of (r := r2, x := y), lastStep)
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, dom(f) === initialSegment(a, r1, x), ran(f) === y) |- a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)) by RightAnd(lastStep, hyp of (b := a, y := x))
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x /\ (dom(f) === initialSegment(a, r1, x)), ran(f) === y) |- a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)) by LeftAnd
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x /\ (dom(f) === initialSegment(a, r1, x)), ran(f) === y) |- ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y))) by RightExists
    val case21 = thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))), ran(f) === y) |- ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y))) by LeftExists

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x), ran(f) === initialSegment(b, r2, y)) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (relationRestriction(r2, initialSegment(b, r2, y), initialSegment(b, r2, y)), initialSegment(b, r2, y))) by Substitution.ApplyRules(ran(f) === initialSegment(b, r2, y))(case2)
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), dom(f) === initialSegment(a, r1, x), ran(f) === initialSegment(b, r2, y)) |- (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))) by Substitution.ApplyRules(initialSegmentOrder.shortDefinition)
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, dom(f) === initialSegment(a, r1, x), b ∈ y, ran(f) === initialSegment(b, r2, y)) |- pair(a, b) ∈ f) by Cut(lastStep, fDefIntro)
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, dom(f) === initialSegment(a, r1, x), b ∈ y, ran(f) === initialSegment(b, r2, y)) |- b ∈ ran(f)) by Cut(lastStep, relationRangeIntroPair of (r := f))
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, dom(f) === initialSegment(a, r1, x), b ∈ y, ran(f) === initialSegment(b, r2, y)) |- b ∈ initialSegment(b, r2, y)) by RightSubstEq.withParametersSimple(List((ran(f), initialSegment(b, r2, y))), lambda(x, b ∈ x))
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x, dom(f) === initialSegment(a, r1, x), b ∈ y, ran(f) === initialSegment(b, r2, y)) |- ()) by RightAnd(lastStep, notInSelfInitialSegment of (r := r2, x := y))
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), a ∈ x /\ (dom(f) === initialSegment(a, r1, x)), b ∈ y /\ (ran(f) === initialSegment(b, r2, y))) |- ()) by Restate
    thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))), b ∈ y /\ (ran(f) === initialSegment(b, r2, y))) |- ()) by LeftExists
    val case22 = thenHave((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))), ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y)))) |- ()) by LeftExists

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x))), (ran(f) === y) \/ ∃(b, b ∈ y /\ (ran(f) === initialSegment(b, r2, y)))) |- ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y))) by LeftOr(case21, case22)
    val finalCase2 = have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x)))) |- ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y))) by Cut(ranInitialSegment, lastStep)

    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y), (dom(f) === x) \/ ∃(a, a ∈ x /\ (dom(f) === initialSegment(a, r1, x)))) |- 
      ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))),
      ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)))
    ) by LeftOr(finalCase1, finalCase2)
    have((fDef, strictWellOrder(r1, x), strictWellOrder(r2, y)) |- 
      ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))),
      ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)))
    ) by Cut(domInitialSegment, lastStep)
    thenHave((∃(f, fDef), strictWellOrder(r1, x), strictWellOrder(r2, y)) |- 
      ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))),
      ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)))
    ) by LeftExists
    have((strictWellOrder(r1, x), strictWellOrder(r2, y)) |- 
      ((r1, x) ≃ (r2, y), ∃(b, b ∈ y /\ (r1, x) ≃ (initialSegmentOrder(b, r2, y), initialSegment(b, r2, y))),
      ∃(a, a ∈ x /\ (initialSegmentOrder(a, r1, x), initialSegment(a, r1, x)) ≃ (r2, y)))
    ) by Cut(fExistence, lastStep)
  }

}
