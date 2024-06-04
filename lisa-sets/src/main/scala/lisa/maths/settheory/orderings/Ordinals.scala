package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.orderings.MembershipRelation.*
import lisa.maths.settheory.orderings.PartialOrders.*
import lisa.maths.settheory.InductiveSets.*
import lisa.maths.settheory.orderings.Segments.*
import lisa.SetTheoryLibrary.extensionalityAxiom
import lisa.automation.Tableau.Substitution
import lisa.automation.Tautology

object Ordinals extends lisa.Main {

  // var defs
  private val w = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val h = formulaVariable
  private val s = variable
  private val t = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable

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
   * *****************
   * TRANSITIVE SETS *
   * *****************
   */

  /**
   * Definition --- Transitive set
   *
   * We give two definitions of a transitive set and prove that they are equivalent:
   *
   * - A set `x` in which every element is a subset
   *
   *   `∀ y. y ∈ x ⇒ y ⊆ x`
   *
   * - A set `x` in which the membership is transitive
   *
   *   `∀ z. ∀ y. z ∈ y ⇒ y ∈ x ⇒ z ∈ x`
   */
  val transitiveSet = DEF(x) --> forall(y, in(y, x) ==> subset(y, x))

  /**
   * Theorem --- Transitive set introduction rule
   *
   *     `∀ y. y ∈ x ⇒ y ⊆ x |- transitiveSet(x)`
   */
  val transitiveSetIntro = Lemma(forall(y, in(y, x) ==> subset(y, x)) |- transitiveSet(x)) {
    have(forall(y, in(y, x) ==> subset(y, x)) |- forall(y, in(y, x) ==> subset(y, x))) by Hypothesis
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }

  /**
   * Theorem --- Transitive set elimination rule
   *
   *     `transitiveSet(x), y ∈ x |- y ⊆ x`
   */
  val transitiveSetElim = Lemma((transitiveSet(x), in(y, x)) |- subset(y, x)) {
    have(forall(y, in(y, x) ==> subset(y, x)) |- forall(y, in(y, x) ==> subset(y, x))) by Hypothesis
    thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- subset(y, x)) by InstantiateForall(y)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }


  /**
   * Theorem --- The two definitions of a transitive set are equivalent.
   *
   *    `(∀ y. y ∈ x ⇒ y ⊆ x) <=> (∀ z. ∀ y. z ∈ y ⇒ y ∈ x ⇒ z ∈ x)`
   */
  val transitiveSetAltDef = Lemma(transitiveSet(x) <=> forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) {

    val lhs = have(forall(y, in(y, x) ==> subset(y, x)) ==> forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) subproof {
      have(forall(y, in(y, x) ==> subset(y, x)) |- forall(y, in(y, x) ==> subset(y, x))) by Hypothesis
      thenHave((forall(y, in(y, x) ==> subset(y, x)), in(y, x)) |- subset(y, x)) by InstantiateForall(y)
      have((forall(y, in(y, x) ==> subset(y, x)), in(y, x), in(z, y)) |- in(z, x)) by Cut(lastStep, subsetElim of (x := y, y := x))
      thenHave((forall(y, in(y, x) ==> subset(y, x))) |- (in(z, y) /\ in(y, x)) ==> in(z, x)) by Restate
      thenHave((forall(y, in(y, x) ==> subset(y, x))) |- forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) by RightForall
      thenHave((forall(y, in(y, x) ==> subset(y, x))) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by RightForall
    }

    val rhs = have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) ==> forall(y, in(y, x) ==> subset(y, x))) subproof {
      have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by Hypothesis
      thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) by InstantiateForall(z)
      thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- (in(z, y)) ==> in(z, x)) by InstantiateForall(y)
      thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- forall(z, in(z, y) ==> in(z, x))) by RightForall
      have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) /\ in(y, x) |- subset(y, x)) by Cut(lastStep, subsetIntro of (x -> y, y -> x))
      thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- in(y, x) ==> subset(y, x)) by Restate
      thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(y, in(y, x) ==> subset(y, x))) by RightForall
    }

    have(forall(y, in(y, x) ==> subset(y, x)) <=> forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by RightIff(lhs, rhs)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }

  /**
   * Theorem --- Transitive set alternative introduction rule
   *
   *     `∀ z. ∀ y. z ∈ y ⇒ y ∈ x ⇒ z ∈ x |- transitiveSet(x)`
   */
  val transitiveSetAltIntro = Lemma(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- transitiveSet(x)) {
    have(thesis) by Weakening(transitiveSetAltDef)
  }

  /**
   * Theorem --- Transitive set alternative elimination rule
   *
   *     `transitiveSet(x), z ∈ y, y ∈ x |- z ∈ x`
   */
  val transitiveSetAltElim = Lemma((transitiveSet(x), in(z, y), in(y, x)) |- in(z, x)) {
    have(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x)))) by Hypothesis
    thenHave(forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) |- forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))) by InstantiateForall(z)
    thenHave((forall(z, forall(y, (in(z, y) /\ in(y, x)) ==> in(z, x))), in(z, y), in(y, x)) |- in(z, x)) by InstantiateForall(y)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSetAltDef)
  }

  /**
   * Theorem --- The empty set is transitive.
   *
   *   `transitiveSet(∅)`
   */
  val emptySetTransitive = Lemma(transitiveSet(emptySet)) {
    have(in(y, emptySet) ==> subset(y, emptySet)) by Weakening(emptySetAxiom of (x -> y))
    thenHave(forall(y, in(y, emptySet) ==> subset(y, emptySet))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetIntro of (x := emptySet))
  }

  /**
    * Theorem --- The union of transitive sets is transitive.
    * 
    *  `∀ x ∈ y. transitiveSet(x) |- transitiveSet(∪ y)
    */
  val unionTransitive = Lemma(forall(x, in(x, y) ==> transitiveSet(x)) |- transitiveSet(union(y))) {

    have((transitiveSet(x), in(w, z), in(z, x), in(x, y)) |- in(w, union(y))) by Cut(transitiveSetAltElim of (z := w, y := z), unionIntro of (z := w, x := y, y := x))
    thenHave((in(x, y) ==> transitiveSet(x), in(w, z), in(z, x) /\ in(x, y)) |- in(w, union(y))) by Tautology
    thenHave((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), in(z, x) /\ in(x, y)) |- in(w, union(y))) by LeftForall
    thenHave((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), exists(x, in(z, x) /\ in(x, y))) |- in(w, union(y))) by LeftExists
    have((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), in(z, union(y))) |- in(w, union(y))) by Cut(unionElim of (x := y), lastStep)
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- in(w, z) /\ in(z, union(y)) ==> in(w, union(y))) by Restate
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- forall(z, in(w, z) /\ in(z, union(y)) ==> in(w, union(y)))) by RightForall
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- forall(w, forall(z, in(w, z) /\ in(z, union(y)) ==> in(w, union(y))))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := union(y)))
  }

  /**
    * Theorem --- The union of a set and all its elements is transitive.
    * 
    *  `∀ x ∈ y. transitiveSet(x) |- transitiveSet((∪ y) ∪ y)`
    */
  val unionSetAndElementsTransitive = Lemma(forall(x, in(x, y) ==> transitiveSet(x)) |- transitiveSet(setUnion(union(y), y))) {

    val right = have((in(w, z), in(z, y)) |- in(w, setUnion(union(y), y))) by Cut(unionIntro of (z := w, y := z, x := y), setUnionLeftIntro of (z := w, x := union(y)))
    have((transitiveSet(union(y)), in(w, z), in(z, union(y))) |- in(w, setUnion(union(y), y))) by Cut(transitiveSetAltElim of (z := w, y := z, x := union(y)), setUnionLeftIntro of (z := w, x := union(y)))

    val left = have((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), in(z, union(y))) |- in(w, setUnion(union(y), y))) by Cut(unionTransitive, lastStep)

    have((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), in(z, union(y)) \/ in(z, y)) |- in(w, setUnion(union(y), y))) by LeftOr(left, right)
    have((forall(x, in(x, y) ==> transitiveSet(x)), in(w, z), in(z, setUnion(union(y), y))) |- in(w, setUnion(union(y), y))) by Cut(setUnionElim of (x := union(y)), lastStep)
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- in(w, z) /\ in(z, setUnion(union(y), y)) ==> in(w, setUnion(union(y), y))) by Restate
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- forall(z, in(w, z) /\ in(z, setUnion(union(y), y)) ==> in(w, setUnion(union(y), y)))) by RightForall
    thenHave(forall(x, in(x, y) ==> transitiveSet(x)) |- forall(w, forall(z, in(w, z) /\ in(z, setUnion(union(y), y)) ==> in(w, setUnion(union(y), y))))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := setUnion(union(y), y)))
  }

  /**
    * Theorem --- If the membership relation is transitive, then any member of a transitive set is transitive.
    * 
    *   `transitive(∈_x, x), transitiveSet(x), y ∈ x |- transitiveSet(y)`
    */
  val transitiveSetRelationTransitiveSet = Lemma((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- transitiveSet(y)) {
    have((transitive(membershipRelation(x), x), in(pair(w, z), membershipRelation(x)), in(pair(z, y), membershipRelation(x))) |- in(w, y)) by Cut(transitiveElim of (y := z, z := y, r := membershipRelation(x)), membershipRelationIsMembershipPair of (a := w, b := y))
    have((transitive(membershipRelation(x), x), in(w, z), in(w, x), in(z, x), in(pair(z, y), membershipRelation(x))) |- in(w, y)) by Cut(membershipRelationIntro of (a := w, b := z), lastStep)
    have((transitive(membershipRelation(x), x), in(w, z), in(w, x), in(z, x), in(z, y), in(y, x)) |- in(w, y)) by Cut(membershipRelationIntro of (a := z, b := y), lastStep)
    have((transitiveSet(x), transitive(membershipRelation(x), x), in(w, z), in(z, x), in(z, y), in(y, x)) |- in(w, y)) by Cut(transitiveSetAltElim of (z := w, y := z), lastStep)
    have((transitiveSet(x), transitive(membershipRelation(x), x), in(w, z), in(z, y), in(y, x)) |- in(w, y)) by Cut(transitiveSetAltElim, lastStep)
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- (in(w, z) /\ in(z, y)) ==> in(w, y)) by Restate
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- forall(z, (in(w, z) /\ in(z, y)) ==> in(w, y))) by RightForall
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- forall(w, forall(z, (in(w, z) /\ in(z, y)) ==> in(w, y)))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := y)) 
  }

  
  val membershipRelationInTransitiveSets = Lemma((transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y))) |- in(pair(a, b), membershipRelation(x))) {
    have((transitiveSet(x), in(a, b), in(a, y), in(b, x), in(y, x)) |- in(pair(a, b), membershipRelation(x))) by Cut(transitiveSetAltElim of (z := a), membershipRelationIntro)
    have((transitiveSet(x), in(a, b), in(a, y), in(b, y), in(y, x)) |- in(pair(a, b), membershipRelation(x))) by Cut(transitiveSetAltElim of (z := b), lastStep)
    thenHave((transitiveSet(x), in(a, b) /\ in(a, y) /\ in(b, y), in(y, x)) |- in(pair(a, b), membershipRelation(x))) by Restate
    have(thesis) by Cut(membershipRelationElimPair of (x := y), lastStep)
  }

  /**
    * Theorem --- If the membership relation is transitive on a transitive set, then any of its members induces a transitive relation.
    * 
    *   `transitive(∈_x, x), transitiveSet(x), y ∈ x |- transitive(∈_y, y)`
    */
  val transitiveSetRelationTransitive = Lemma((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- transitive(membershipRelation(y), y)) {
    have((transitive(membershipRelation(x), x), in(pair(a, b), membershipRelation(x)), in(pair(b, c), membershipRelation(x))) |- in(a, c)) by Cut(transitiveElim of (w := a, y := b, z := c, r := membershipRelation(x)), membershipRelationIsMembershipPair of (b := c))
    have((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(x))) |- in(a, c)) by Cut(membershipRelationInTransitiveSets, lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(y))) |- in(a, c)) by Cut(membershipRelationInTransitiveSets of (a := b, b := c), lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(y))) |- in(a, y) /\ in(b, y) /\ in(a, c)) by RightAnd(membershipRelationInDomainPair of (x := y), lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(y))) |- in(a, y) /\ in(b, y) /\ in(c, y) /\ in(a, c)) by RightAnd(membershipRelationInDomainPair of (x := y, a := b, b := c), lastStep)
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(y))) |- in(a, y) /\ in(c, y) /\ in(a, c)) by Weakening
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x), in(pair(a, b), membershipRelation(y)), in(pair(b, c), membershipRelation(y))) |- in(pair(a, c), membershipRelation(y))) by Substitution.ApplyRules(membershipRelationElemPair of (b := c, x := y))
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- (in(pair(a, b), membershipRelation(y)) /\ in(pair(b, c), membershipRelation(y))) ==> in(pair(a, c), membershipRelation(y))) by Restate
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- forall(c, (in(pair(a, b), membershipRelation(y)) /\ in(pair(b, c), membershipRelation(y))) ==> in(pair(a, c), membershipRelation(y)))) by RightForall
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- forall(b, forall(c, (in(pair(a, b), membershipRelation(y)) /\ in(pair(b, c), membershipRelation(y))) ==> in(pair(a, c), membershipRelation(y))))) by RightForall
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- forall(a, forall(b, forall(c, (in(pair(a, b), membershipRelation(y)) /\ in(pair(b, c), membershipRelation(y))) ==> in(pair(a, c), membershipRelation(y)))))) by RightForall
    have((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x), relationBetween(membershipRelation(y), y, y)) |- transitive(membershipRelation(y), y)) by Cut(lastStep, transitiveIntro of (r := membershipRelation(y), x := y))
    have(thesis) by Cut(membershipRelationIsARelation of (x := y), lastStep)

  }

  /**
    * Theorem --- If the membership relation is a strict partial order on a transitive set, then any of its members induces a strict partial order.
    * 
    *   `strictPartialOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictPartialOrder(∈_y, y)`
    */
  val transitiveStrictPartialOrderElem = Lemma((transitiveSet(x), strictPartialOrder(membershipRelation(x), x), in(y, x)) |- strictPartialOrder(membershipRelation(y), y)) {
    have(transitive(membershipRelation(y), y) |- strictPartialOrder(membershipRelation(y), y)) by Cut(membershipRelationIrreflexive of (x := y), strictPartialOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), transitive(membershipRelation(x), x), in(y, x)) |- strictPartialOrder(membershipRelation(y), y)) by Cut(transitiveSetRelationTransitive, lastStep)
    have(thesis) by Cut(strictPartialOrderTransitive of (r := membershipRelation(x)), lastStep)
  }

  /**
    * Theorem --- If the membership relation is connected on a transitive set, then any of its members induces a connected relation.
    * 
    *   `connected(∈_x, x), transitiveSet(x), y ∈ x |- connected(∈_y, y)`
    */
  val transitiveConnectedMembershipRelation = Lemma((transitiveSet(x), connected(membershipRelation(x), x), in(y, x)) |- connected(membershipRelation(y), y)) {

    have((in(pair(a, b), membershipRelation(x)), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y))) by Cut(membershipRelationIsMembershipPair, membershipRelationIntro of (x := y))
    val left = thenHave((in(pair(a, b), membershipRelation(x)), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Weakening

    have((in(pair(b, a), membershipRelation(x)), in(a, y), in(b, y)) |- in(pair(b, a), membershipRelation(y))) by Cut(membershipRelationIsMembershipPair of (a := b, b := a), membershipRelationIntro of (x := y, a := b, b := a))
    val right = thenHave((in(pair(b, a), membershipRelation(x)), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Weakening

    have(a === b |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Restate
    have((in(pair(b, a), membershipRelation(x)) \/ (a === b), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by LeftOr(right, lastStep)
    have((in(pair(a, b), membershipRelation(x)) \/ in(pair(b, a), membershipRelation(x)) \/ (a === b), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by LeftOr(left, lastStep)
    have((connected(membershipRelation(x), x), in(a, x), in(b, x), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Cut(connectedElim of (y := a, z := b, r := membershipRelation(x)), lastStep)
    have((connected(membershipRelation(x), x), transitiveSet(x), in(y, x), in(b, x), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Cut(transitiveSetAltElim of (z := a), lastStep)
    have((connected(membershipRelation(x), x), transitiveSet(x), in(y, x), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Cut(transitiveSetAltElim of (z := b), lastStep)
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), in(y, x), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)) by Restate
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b))) by Restate
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- ∀(b, (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b)))) by RightForall
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), in(y, x)) |- ∀(a, ∀(b, (in(a, y) /\ in(b, y)) ==> (in(pair(a, b), membershipRelation(y)) \/ in(pair(b, a), membershipRelation(y)) \/ (a === b))))) by RightForall
    have((connected(membershipRelation(x), x), transitiveSet(x), in(y, x), relationBetween(membershipRelation(y), y, y)) |- connected(membershipRelation(y), y)) by Cut(lastStep, connectedIntro of (r -> membershipRelation(y), x -> y)) 
    have(thesis) by Cut(membershipRelationIsARelation of (x -> y), lastStep)
  }

  /**
    * Theorem --- If the membership relation is a strict total order on a transitive set, then any of its members induces a strict total order.
    * 
    *   `strictTotalOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictTotalOrder(∈_y, y)`
    */
  val transitiveStrictTotalOrderElem = Lemma((transitiveSet(x), strictTotalOrder(membershipRelation(x), x), in(y, x)) |- strictTotalOrder(membershipRelation(y), y)) {
    have((transitiveSet(x), connected(membershipRelation(y), y), strictPartialOrder(membershipRelation(x), x), in(y, x)) |- strictTotalOrder(membershipRelation(y), y)) by Cut(transitiveStrictPartialOrderElem, strictTotalOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), connected(membershipRelation(x), x), strictPartialOrder(membershipRelation(x), x), in(y, x)) |- strictTotalOrder(membershipRelation(y), y)) by Cut(transitiveConnectedMembershipRelation, lastStep)
    have((transitiveSet(x), strictTotalOrder(membershipRelation(x), x), strictPartialOrder(membershipRelation(x), x), in(y, x)) |- strictTotalOrder(membershipRelation(y), y)) by Cut(strictTotalOrderConnected of (r := membershipRelation(x)), lastStep)
    have(thesis) by Cut(strictTotalOrderIsPartial of (r := membershipRelation(x)), lastStep)
  }

  val transitiveSetLeastElement = Lemma((transitiveSet(x), isLeastElement(a, z, membershipRelation(x), x), in(y, x), subset(z, y)) |- isLeastElement(a, z, membershipRelation(y), y)) {
 
    val eqCase = have(a === b |- in(pair(a, b), membershipRelation(y)) \/ (a === b)) by Restate

    have((in(pair(a, b), membershipRelation(x)), in(a, y), in(b, y)) |- in(pair(a, b), membershipRelation(y))) by Cut(membershipRelationIsMembershipPair, membershipRelationIntro of (x := y))
    have((in(pair(a, b), membershipRelation(x)), in(a, z), subset(z, y), in(b, y)) |- in(pair(a, b), membershipRelation(y))) by Cut(subsetElim of (z := a, x := z), lastStep)
    have((in(pair(a, b), membershipRelation(x)), in(a, z), subset(z, y), in(b, z)) |- in(pair(a, b), membershipRelation(y))) by Cut(subsetElim of (z := b, x := z), lastStep)
    thenHave((in(pair(a, b), membershipRelation(x)), in(a, z), subset(z, y), in(b, z)) |- in(pair(a, b), membershipRelation(y)) \/ (a === b)) by Weakening

    have((in(pair(a, b), membershipRelation(x)) \/ (a === b), in(a, z), subset(z, y), in(b, z)) |- in(pair(a, b), membershipRelation(y)) \/ (a === b)) by LeftOr(lastStep, eqCase)
    have((isLeastElement(a, z, membershipRelation(x), x), in(a, z), subset(z, y), in(b, z)) |- in(pair(a, b), membershipRelation(y)) \/ (a === b)) by Cut(isLeastElementElim of (r := membershipRelation(x), y := z), lastStep)
    thenHave((isLeastElement(a, z, membershipRelation(x), x), in(a, z), subset(z, y)) |- in(b, z) ==> in(pair(a, b), membershipRelation(y)) \/ (a === b)) by RightImplies
    thenHave((isLeastElement(a, z, membershipRelation(x), x), in(a, z), subset(z, y)) |- forall(b, in(b, z) ==> in(pair(a, b), membershipRelation(y)) \/ (a === b))) by RightForall
    have((isLeastElement(a, z, membershipRelation(x), x), in(a, z), subset(z, y), strictPartialOrder(membershipRelation(y), y)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(lastStep, isLeastElementIntro of (r := membershipRelation(y), y := z, x := y))
    have((isLeastElement(a, z, membershipRelation(x), x), subset(z, y), strictPartialOrder(membershipRelation(y), y)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(isLeastElementInSubset of (y := z, r := membershipRelation(x)), lastStep)
    have((isLeastElement(a, z, membershipRelation(x), x), subset(z, y), transitiveSet(x), in(y, x), strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(transitiveStrictPartialOrderElem, lastStep)
    have(thesis) by Cut(isLeastElementInStrictPartialOrder of (r := membershipRelation(x), y := z), lastStep) 
  }
  
  /**
    * Theorem --- If the membership relation is a strict well-order on a transitive set, then any of its members induces a strict well-order.
    * 
    *   `strictWellOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictWellOrder(∈_y, y)`
    */
  val transitiveStrictWellOrderElem = Lemma((transitiveSet(x), strictWellOrder(membershipRelation(x), x), in(y, x)) |- strictWellOrder(membershipRelation(y), y)) {
    have((transitiveSet(x), isLeastElement(a, z, membershipRelation(x), x), in(y, x), subset(z, y)) |- exists(a, isLeastElement(a, z, membershipRelation(y), y))) by RightExists(transitiveSetLeastElement)
    thenHave((transitiveSet(x), exists(a, isLeastElement(a, z, membershipRelation(x), x)), in(y, x), subset(z, y)) |- exists(a, isLeastElement(a, z, membershipRelation(y), y))) by LeftExists
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), subset(z, x), !(z === emptySet), in(y, x), subset(z, y)) |- exists(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(strictWellOrderElim of (y := z, r := membershipRelation(x)), lastStep)
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), !(z === emptySet), in(y, x), subset(y, x), subset(z, y)) |- exists(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(subsetTransitivity of (a := z, b := y, c := x), lastStep)
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), !(z === emptySet), in(y, x), subset(z, y)) |- exists(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(transitiveSetElim, lastStep)
    thenHave((transitiveSet(x), strictWellOrder(membershipRelation(x), x), in(y, x)) |- (subset(z, y) /\ !(z === emptySet)) ==> exists(a, isLeastElement(a, z, membershipRelation(y), y))) by Restate
    thenHave((transitiveSet(x), strictWellOrder(membershipRelation(x), x), in(y, x)) |- forall(z, (subset(z, y) /\ !(z === emptySet)) ==> exists(a, isLeastElement(a, z, membershipRelation(y), y)))) by RightForall
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), in(y, x), strictTotalOrder(membershipRelation(y), y)) |- strictWellOrder(membershipRelation(y), y)) by Cut(lastStep, strictWellOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), in(y, x), strictTotalOrder(membershipRelation(x), x)) |- strictWellOrder(membershipRelation(y), y)) by Cut(transitiveStrictTotalOrderElem, lastStep)
    have(thesis) by Cut(strictWellOrderTotal of (r := membershipRelation(x)), lastStep)
  }
  
  /**
   * **********
   * ORDINALS *
   * **********
   */

  /**
   * 
   * Definition --- Ordinal
   * 
   * An ordinal is a transitive set that is well-ordered by the membership relation.
   * 
   *   `transitiveSet(a) ∧ strictWellOrder(membershipRelation(a), a)`
   */
  val ordinal = DEF(a) --> transitiveSet(a) /\ strictWellOrder(membershipRelation(a), a)

  /**
    * Theorem --- Ordinal introduction rule
    * 
    *   `transitiveSet(a), strictWellOrder(membershipRelation(a), a) |- ordinal(a)`
    */
  val ordinalIntro = Lemma(
    (transitiveSet(a), strictWellOrder(membershipRelation(a), a)) |- ordinal(a)
  ) {
    have(thesis) by Weakening(ordinal.definition)
  }

  /**
    * Theorem --- Ordinals are transitive
    * 
    *   `ordinal(a) |- transitiveSet(a)`
    */
  val ordinalTransitiveSet = Lemma(
    ordinal(a) |- transitiveSet(a)
  ) {
    have(thesis) by Weakening(ordinal.definition)
  }

  /**
    * Theorem --- Ordinals are well-ordered by the membership relation
    * 
    *   `ordinal(a) |- strictWellOrder(membershipRelation(a), a)`
    */
  val ordinalStrictWellOrder = Lemma(
    ordinal(a) |- strictWellOrder(membershipRelation(a), a)
  ) {
    have(thesis) by Weakening(ordinal.definition)
  }

  /**
   * Theorem --- the empty set is an ordinal.
   *
   *    `0 ∈ Ord`
   */
  val emptySetOrdinal = Lemma(
    ordinal(emptySet)
  ) {
    have(strictWellOrder(membershipRelation(emptySet), emptySet) |- ordinal(emptySet)) by Cut(emptySetTransitive, ordinalIntro of (a := emptySet))
    thenHave(strictWellOrder(emptySet, emptySet) |- ordinal(emptySet)) by Substitution.ApplyRules(emptyMembershipRelation)
    have(thesis) by Cut(emptyStrictWellOrder, lastStep)
  }

  /**
   * Theorem --- Elements of ordinals are also ordinals
   *
   *   `a ∈ Ord /\ b ∈ a ==> b ∈ Ord`
   */
  val elementsOfOrdinalsAreOrdinals = Lemma(
    (ordinal(a), in(b, a)) |- ordinal(b)
  ) {
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), in(b, a), transitiveSet(b)) |- ordinal(b)) by Cut(transitiveStrictWellOrderElem of (x := a, y := b), ordinalIntro of (a := b))
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), in(b, a), transitive(membershipRelation(a), a)) |- ordinal(b)) by Cut(transitiveSetRelationTransitiveSet of (x := a, y := b), lastStep)
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), in(b, a)) |- ordinal(b)) by Cut(strictWellOrderTransitive of (r := membershipRelation(a), x := a), lastStep)
    have((transitiveSet(a), ordinal(a), in(b, a)) |- ordinal(b)) by Cut(ordinalStrictWellOrder, lastStep)
    have(thesis) by Cut(ordinalTransitiveSet, lastStep)
  }

  /**
    * Theorem --- Ordinals are transitive
    * 
    *   `c ∈ Ord, a ∈ b ∈ c |- a ∈ c` 
    */
  val ordinalTransitive = Lemma(
    (ordinal(c), in(a, b), in(b, c)) |- in(a, c)
  ) {
    have(thesis) by Cut(ordinalTransitiveSet of (a := c), transitiveSetAltElim of (x := c, y := b, z := a))
  }

  val elementOfOrdinalIsInitialSegment = Lemma(
    (ordinal(a), in(b, a)) |- b === initialSegment(b, membershipRelation(a), a)
  ) {
    have((strictWellOrder(membershipRelation(a), a), in(x, a), in(b, a), in(x, b)) |- in(x, initialSegment(b, membershipRelation(a), a))) by Cut(membershipRelationIntro of (a := x, x := a), initialSegmentIntro of (r := membershipRelation(a), x := a, a := x))
    have((ordinal(a), in(x, a), in(b, a), in(x, b)) |- in(x, initialSegment(b, membershipRelation(a), a))) by Cut(ordinalStrictWellOrder, lastStep)
    have((ordinal(a), in(b, a), in(x, b)) |- in(x, initialSegment(b, membershipRelation(a), a))) by Cut(ordinalTransitive of (c := a, a := x, b := b), lastStep)
    val forward = thenHave((ordinal(a), in(b, a)) |- in(x, b) ==> in(x, initialSegment(b, membershipRelation(a), a))) by RightImplies
    
    have((strictWellOrder(membershipRelation(a), a), in(x, initialSegment(b, membershipRelation(a), a))) |- in(x, b)) by Cut(initialSegmentElim of (r := membershipRelation(a), x := a, a := x), membershipRelationIsMembershipPair of (a := x, x := a))
    have((ordinal(a), in(x, initialSegment(b, membershipRelation(a), a))) |- in(x, b)) by Cut(ordinalStrictWellOrder, lastStep)
    val backward = thenHave(ordinal(a) |- in(x, initialSegment(b, membershipRelation(a), a)) ==> in(x, b)) by RightImplies

    have((ordinal(a), in(b, a)) |- in(x, b) <=> in(x, initialSegment(b, membershipRelation(a), a))) by RightIff(forward, backward)
    thenHave((ordinal(a), in(b, a)) |- forall(x, in(x, b) <=> in(x, initialSegment(b, membershipRelation(a), a)))) by RightForall
    thenHave(thesis) by Substitution.ApplyRules(extensionalityAxiom of (x := b, y := initialSegment(b, membershipRelation(a), a)))
  }

  val membershipRelationInitialSegment = Lemma(
    ordinal(a) |- membershipRelation(initialSegment(b, membershipRelation(a), a)) === initialSegmentOrder(b, membershipRelation(a), a)
  ) {
    sorry
  }

  /**
    * Theorem --- Two isomorphic ordinals are equal
    * 
    *   `(a, ∈_a) ≅ (b, ∈_b) |- a = b`
    */
  val isomorphicOrdinalsAreEqual = Lemma(
    (ordinal(a), ordinal(b), relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b)) |- a === b
  ) {

    val ordIsomorphism = relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b)
    val sLeastElem = isLeastElement(s, nonIdentitySet(f, a), membershipRelation(a), a)

    val forward = have((ordIsomorphism, ordinal(a), sLeastElem, in(s, a)) |- subset(s, app(f, s))) subproof {
      have((in(t, a), in(pair(t, s), membershipRelation(a)), sLeastElem) |- app(f, t) === t) by Cut(belowLeastElement of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a, b := t), notInNonIdentitySetElim of (x := a))
      have((ordIsomorphism, sLeastElem, in(t, a), in(pair(t, s), membershipRelation(a))) |- in(pair(t, app(f, s)), membershipRelation(b))) by Substitution.ApplyRules(lastStep)(relationIsomorphismElimForward of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := t, b := s))
      have((ordIsomorphism, sLeastElem, in(t, a), in(pair(t, s), membershipRelation(a))) |- in(t, app(f, s))) by Cut(lastStep, membershipRelationIsMembershipPair of (x := b, a := t, b := app(f, s)))
      have((ordIsomorphism, sLeastElem, in(t, a), in(t, s), in(s, a)) |- in(t, app(f, s))) by Cut(membershipRelationIntro of (x := a, a := t, b := s), lastStep)
      have((ordIsomorphism, ordinal(a), sLeastElem, in(t, s), in(s, a)) |- in(t, app(f, s))) by Cut(ordinalTransitive of (a := t, b := s, c := a), lastStep)
      thenHave((ordIsomorphism, ordinal(a), sLeastElem, in(s, a)) |- in(t, s) ==> in(t, app(f, s))) by RightImplies
      thenHave((ordIsomorphism, ordinal(a), sLeastElem, in(s, a)) |- forall(t, in(t, s) ==> in(t, app(f, s)))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := s, y := app(f, s)))
    }

    val backward = have((ordIsomorphism, ordinal(b), sLeastElem, in(s, a)) |- subset(app(f, s), s)) subproof { 

      val inverseFunctionBelow = have((ordIsomorphism, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- in(pair(app(inverseRelation(f), t), s), membershipRelation(a))) by Substitution.ApplyRules(inverseRelationRightCancel of (b := t, x := a, y := b))(relationIsomorphismElimBackward of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := app(inverseRelation(f), t), b := s))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- !in(app(inverseRelation(f), t), nonIdentitySet(f, a))) by Cut(lastStep, belowLeastElement of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a, b := app(inverseRelation(f), t)))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- app(f, app(inverseRelation(f), t)) === app(inverseRelation(f), t)) by Cut(lastStep, notInNonIdentitySetElim of (x := a, t := app(inverseRelation(f), t)))
      thenHave((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- t === app(inverseRelation(f), t)) by Substitution.ApplyRules(inverseRelationRightCancel of (b := t, x := a, y := b))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- in(pair(t, s), membershipRelation(a))) by Substitution.ApplyRules(lastStep)(inverseFunctionBelow)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(inverseRelation(f), t), a), in(s, a), in(pair(t, app(f, s)), membershipRelation(b))) |- in(t, s)) by Cut(lastStep, membershipRelationIsMembershipPair of (x := a, a := t, b := s))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(f, s), b), in(app(inverseRelation(f), t), a), in(s, a), in(t, app(f, s))) |- in(t, s)) by Cut(membershipRelationIntro of (x := b, a := t, b := app(f, s)),lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), in(t, b), in(app(f, s), b), in(s, a), in(t, app(f, s))) |- in(t, s)) by Cut(inverseFunctionImageInDomain of (b := t, x := a, y := b), lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), ordinal(b), in(app(f, s), b), in(s, a), in(t, app(f, s))) |- in(t, s)) by Cut(ordinalTransitive of (a := t, b := app(f, s), c := b), lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), ordinal(b), in(s, a), in(t, app(f, s))) |- in(t, s)) by Cut(relationIsomorphismAppInCodomain of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := s), lastStep)
      have((ordIsomorphism, sLeastElem, ordinal(b), in(s, a), in(t, app(f, s))) |- in(t, s)) by Cut(relationIsomorphismBijective of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
      thenHave((ordIsomorphism, sLeastElem, ordinal(b), in(s, a)) |- in(t, app(f, s)) ==> in(t, s)) by RightImplies
      thenHave((ordIsomorphism, sLeastElem, ordinal(b), in(s, a)) |- forall(t, in(t, app(f, s)) ==> in(t, s))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := app(f, s), y := s))
    }
    
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem, in(s, a)) |- subset(s, app(f, s)) /\ subset(app(f, s), s)) by RightAnd(forward, backward)
    thenHave((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem, in(s, a)) |- s === app(f, s)) by Substitution.ApplyRules(subsetAntisymmetry of (x := s, y := app(f, s)))
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem, in(s, a)) |- !in(s, nonIdentitySet(f, a))) by Cut(lastStep, notInNonIdentitySetIntro of (x := a, t := s))
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem) |- !in(s, nonIdentitySet(f, a))) by Cut(isLeastElementInDomain of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a), lastStep)
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem) |- ()) by RightAnd(lastStep, isLeastElementInSubset of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a))
    thenHave((ordIsomorphism, ordinal(a), ordinal(b), exists(s, sLeastElem)) |- ()) by LeftExists
    have((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b), subset(nonIdentitySet(f, a), a), !(nonIdentitySet(f, a) === emptySet)) |- ()) by Cut(strictWellOrderElim of (y := nonIdentitySet(f, a), r := membershipRelation(a), x := a), lastStep)
    have((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b), !(nonIdentitySet(f, a) === emptySet)) |- ()) by Cut(nonIdentitySetSubsetDomain of (x := a), lastStep)
    thenHave((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b)) |- nonIdentitySet(f, a) === emptySet) by Restate
    have((ordIsomorphism, ordinal(a), ordinal(b)) |-  nonIdentitySet(f, a) === emptySet) by Cut(ordinalStrictWellOrder, lastStep)
    have((ordIsomorphism, ordinal(a), ordinal(b), surjective(f, a, b)) |- a === b) by Cut(lastStep, nonIdentitySetEmpty of (x := a, y := b))
    have((ordIsomorphism, ordinal(a), ordinal(b), bijective(f, a, b)) |- a === b) by Cut(bijectiveSurjective of (x := a, y := b), lastStep)
    have(thesis) by Cut(relationIsomorphismBijective of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
  }

  val ordinalCases = Lemma(
    (ordinal(a), ordinal(b)) |- (in(a, b), in(b, a), (a === b))
  ) {
    val middle = have((ordinal(a), ordinal(b), relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b)) |- (in(a, b), in(b, a), a === b)) by Weakening(isomorphicOrdinalsAreEqual)

    have(in(c, a) |- in(c, a)) by Hypothesis
    thenHave((ordinal(c), ordinal(b), in(c, a), relationIsomorphism(f, membershipRelation(c), c, membershipRelation(b), b)) |- in(b, a)) by Substitution.ApplyRules(isomorphicOrdinalsAreEqual of (a := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), in(c, a), relationIsomorphism(f, membershipRelation(initialSegment(c, membershipRelation(a), a)), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- in(b, a)) by Substitution.ApplyRules(elementOfOrdinalIsInitialSegment of (b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), in(c, a), relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- in(b, a)) by Substitution.ApplyRules(membershipRelationInitialSegment of (b := c))
    have((ordinal(b), ordinal(a), in(c, a), relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- in(b, a)) by Cut(elementsOfOrdinalsAreOrdinals of (b := c), lastStep)
    thenHave((ordinal(b), ordinal(a), in(c, a) /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- (in(a, b), in(b, a), a === b)) by Weakening
    val right = thenHave((ordinal(b), ordinal(a), exists(c, in(c, a) /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (in(a, b), in(b, a), a === b)) by LeftExists

    have(in(c, b) |- in(c, b)) by Hypothesis
    thenHave((ordinal(a), ordinal(c), in(c, b), relationIsomorphism(f, membershipRelation(a), a, membershipRelation(c), c)) |- in(a, b)) by Substitution.ApplyRules(isomorphicOrdinalsAreEqual of (b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), in(c, b), relationIsomorphism(f, membershipRelation(a), a, membershipRelation(initialSegment(c, membershipRelation(b), b)), initialSegment(c, membershipRelation(b), b))) |- in(a, b)) by Substitution.ApplyRules(elementOfOrdinalIsInitialSegment of (a := b, b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), in(c, b), relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- in(a, b)) by Substitution.ApplyRules(membershipRelationInitialSegment of (b := c, a := b))
    have((ordinal(b), ordinal(a), in(c, b), relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- in(a, b)) by Cut(elementsOfOrdinalsAreOrdinals of (a := b, b := c), lastStep)
    thenHave((ordinal(b), ordinal(a), in(c, b) /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- (in(a, b), in(b, a), a === b)) by Weakening
    val left = thenHave((ordinal(b), ordinal(a), exists(c, in(c, b) /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b)))) |- (in(a, b), in(b, a), a === b)) by LeftExists

    have((ordinal(a), ordinal(b), 
      exists(c, in(c, b) /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      exists(c, in(c, a) /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (in(a, b), in(b, a), a === b)) by LeftOr(left, right)
    have((ordinal(a), ordinal(b), 
      relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b) \/
      exists(c, in(c, b) /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      exists(c, in(c, a) /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (in(a, b), in(b, a), a === b)) by LeftOr(middle, lastStep)
    thenHave((ordinal(a), ordinal(b), 
      exists(f, relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b) \/
      exists(c, in(c, b) /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      exists(c, in(c, a) /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)))) |- (in(a, b), in(b, a), (a === b))) by LeftExists
    have((ordinal(a), ordinal(b), strictWellOrder(membershipRelation(a), a), strictWellOrder(membershipRelation(b), b)) |- (in(a, b), in(b, a), (a === b))) by Cut(initialSegmentIsomorphicCases of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
    have((ordinal(a), ordinal(b), strictWellOrder(membershipRelation(b), b)) |- (in(a, b), in(b, a), (a === b))) by Cut(ordinalStrictWellOrder, lastStep)
    have(thesis) by Cut(ordinalStrictWellOrder of (a := b), lastStep)
  }

  val leqOrdinalIsSubset = Lemma(
    (ordinal(a), ordinal(b)) |- (in(a, b) \/ (a === b)) <=> subset(a, b)
  ) {
    val forward = have(ordinal(b) |- (in(a, b) \/ (a === b)) ==> subset(a, b)) subproof {
      have(a === b |- subset(a, b)) by RightSubstEq.withParametersSimple(List((a, b)), lambda(x, subset(a, x)))(subsetReflexivity of (x := a))
      have((transitiveSet(b), in(a, b) \/ (a === b)) |- subset(a, b)) by LeftOr(transitiveSetElim of (y := a, x := b), lastStep)
      have((ordinal(b), in(a, b) \/ (a === b)) |- subset(a, b)) by Cut(ordinalTransitiveSet of (a := b), lastStep)
    }

    val backward = have((ordinal(a), ordinal(b)) |- subset(a, b) ==> (in(a, b) \/ (a === b))) subproof {
      have(subset(a, b) |- subset(a, b)) by Hypothesis
      have((transitiveSet(a), in(b, a), subset(a, b)) |- subset(a, b) /\ subset(b, a)) by RightAnd(lastStep, transitiveSetElim of (x := a, y := b))
      thenHave((transitiveSet(a), in(b, a), subset(a, b)) |- a === b) by Substitution.ApplyRules(subsetAntisymmetry of (x := a, y := b))
      have((ordinal(a), in(b, a), subset(a, b)) |- a === b) by Cut(ordinalTransitiveSet, lastStep)
      have((ordinal(a), ordinal(b), subset(a, b)) |- (in(a, b), a === b)) by Cut(ordinalCases, lastStep)
    }

    have(thesis) by RightIff(forward, backward)
  }

  val elementOfOrdinalIsSubset = Lemma(
    (ordinal(b), in(a, b)) |- subset(a, b)
  ) {
    have((ordinal(a), ordinal(b), in(a, b)) |- subset(a, b)) by Weakening(leqOrdinalIsSubset)
    have(thesis) by Cut(elementsOfOrdinalsAreOrdinals of (a := b, b := a), lastStep)
  }
    

  val transitiveSetOfOrdinals = Lemma(
    (forall(a, in(a, x) ==> ordinal(a)), !(x === emptySet), transitiveSet(x)) |- ordinal(x)
  ) {
    sorry
    //have((ordinal(a), ordinal(b), !in(a, b) /\ !(a === b)) |- in(b, a)) by Restate(ordinalCases)
  }

  val successor = DEF(a) --> setUnion(a, singleton(a))

  val successorIsOrdinal = Lemma(ordinal(a) |- ordinal(successor(a))) {
    sorry
  }

  /**
   * Theorem --- Any number is smaller than its successor
   *
   *     `a < a + 1`
   */
  val inSuccessor = Lemma(in(a, successor(a))) {
    have(in(a, singleton(a)) |- in(a, successor(a))) by Substitution.ApplyRules(successor.shortDefinition)(setUnionRightIntro of (x := a, y := singleton(a), z := a))
    have(thesis) by Cut(singletonIntro of (x := a), lastStep)
  }

  val successorNonEmpty = Lemma(!(successor(a) === emptySet)) {
    have(thesis) by Cut(inSuccessor, setWithElementNonEmpty of (y := a, x := successor(a)))
  }

  val subsetSuccessor = Lemma(subset(a, successor(a))) {
    have(thesis) by Substitution.ApplyRules(successor.shortDefinition)(unionSubsetFirst of (b := singleton(a)))
  }

    /**
    * Theorem --- The successor of a transitive set is transitive
    * 
    *  `transitiveSet(x) |- transitiveSet(x + 1)`
    */
  val successorTransitive = Lemma(transitiveSet(x) |- transitiveSet(successor(x))) {
    have(transitiveSet(x) |- transitiveSet(x)) by Hypothesis
    thenHave((transitiveSet(x), z === x) |- transitiveSet(z)) by RightSubstEq.withParametersSimple(List((z, x)), lambda(x, transitiveSet(x)))
    have((transitiveSet(x), in(z, singleton(x))) |- transitiveSet(z)) by Cut(singletonElim of (y := z), lastStep)
    thenHave(transitiveSet(x) |- in(z, singleton(x)) ==> transitiveSet(z)) by RightImplies
    thenHave(transitiveSet(x) |- forall(z, in(z, singleton(x)) ==> transitiveSet(z))) by RightForall
    have(transitiveSet(x) |- transitiveSet(setUnion(union(singleton(x)), singleton(x)))) by Cut(lastStep, unionSetAndElementsTransitive of (y := singleton(x)))
    thenHave(transitiveSet(x) |- transitiveSet(setUnion(x, singleton(x)))) by Substitution.ApplyRules(unionOfSingletonIsTheOriginalSet)
    thenHave(transitiveSet(x) |- transitiveSet(successor(x))) by Substitution.ApplyRules(successor.shortDefinition)
  }

  /**
    * Theorem --- Every subclass of ordinals has a minimal element
    * 
    *   `0 ≠ P ⊆ Ord |- ∃a ∈ P. ∀b ∈ P. a ≤ b`
    */ 
  val ordinalSubclassHasMinimalElement = Lemma(
    (forall(x, P(x) ==> ordinal(x)), exists(x, P(x))) |- exists(a, P(a) /\ forall(b, P(b) ==> (in(a, b) \/ (a === b)))) 
  ) {

    val aInterP = forall(t, in(t, z) <=> (in(t, a) /\ P(t)))

    have(aInterP |- aInterP) by Hypothesis
    val aInterPDef = thenHave(aInterP |- in(t, z) <=> (in(t, a) /\ P(t))) by InstantiateForall(t)
    val inAInterP = thenHave((aInterP, in(t, z)) |- in(t, a) /\ P(t)) by Weakening
    val inAInterPRight = thenHave((aInterP, in(t, z)) |- P(t)) by Weakening
    have((aInterP, in(t, z)) |- in(t, a)) by Weakening(inAInterP)
    thenHave(aInterP |- in(t, z) ==> in(t, a)) by RightImplies
    thenHave(aInterP |- forall(t, in(t, z) ==> in(t, a))) by RightForall
    val inAInterPSubset = have(aInterP |- subset(z, a)) by Cut(lastStep, subsetIntro of (x := z, y := a))

    have(existsOne(z, aInterP)) by UniqueComprehension(a, lambda(x, P(x)))
    val aInterPExistence = have(exists(z, aInterP)) by Cut(lastStep, existsOneImpliesExists of (P := lambda(z, forall(t, in(t, z) <=> (in(t, a) /\ P(t))))))

    val ordClass = forall(x, P(x) ==> ordinal(x))
    have(ordClass |- ordClass) by Hypothesis
    val ordClassMembership = thenHave((ordClass, P(x)) |- ordinal(x)) by InstantiateForall(x)

    have((P(a), forall(b, P(b) ==> (in(a, b) \/ (a === b)))) |- P(a) /\ forall(b, P(b) ==> (in(a, b) \/ (a === b)))) by Restate
    val easyCase = thenHave((P(a), forall(b, P(b) ==> (in(a, b) \/ (a === b)))) |- exists(a, P(a) /\ forall(b, P(b) ==> (in(a, b) \/ (a === b))))) by RightExists
    
    val leastElementExists = have((aInterP, ordClass, ordinal(a), exists(b, P(b) /\ !in(a, b) /\ !(a === b))) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) subproof {
      have((ordinal(a), ordinal(b), P(b), !in(a, b), !(a === b)) |- in(b, a) /\ P(b)) by Tautology.from(ordinalCases)
      val bInZ = thenHave((aInterP, ordinal(a), ordinal(b), P(b), !in(a, b), !(a === b)) |- in(b, z)) by Substitution.ApplyRules(aInterPDef of (t := b))
      have((aInterP, ordinal(a), ordinal(b), P(b), !in(a, b), !(a === b)) |- !(z === emptySet)) by Cut(lastStep, setWithElementNonEmpty of (y := b, x := z))
      have((aInterP, ordinal(a), strictWellOrder(membershipRelation(a), a), subset(z, a), ordinal(b), P(b), !in(a, b), !(a === b)) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(lastStep, strictWellOrderElim of (y := z, r := membershipRelation(a), x := a))
      have((aInterP, ordinal(a), strictWellOrder(membershipRelation(a), a), ordinal(b), P(b), !in(a, b), !(a === b)) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(inAInterPSubset, lastStep)
      have((aInterP, ordinal(a), ordinal(b), P(b), !in(a, b), !(a === b)) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(ordinalStrictWellOrder, lastStep)
      have((aInterP, ordClass, ordinal(a), P(b), !in(a, b), !(a === b)) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(ordClassMembership of (x := b), lastStep)
      thenHave((aInterP, ordClass, ordinal(a), P(b) /\ !in(a, b) /\ !(a === b)) |- exists(c, isLeastElement(c, z, membershipRelation(a), a))) by Restate
      thenHave(thesis) by LeftExists
    }

    val inCase = have((aInterP, isLeastElement(c, z, membershipRelation(a), a), P(t), in(t, a)) |- in(c, t) \/ (c === t)) subproof {
      have((isLeastElement(c, z, membershipRelation(a), a), in(t, z)) |- (in(pair(c, t), membershipRelation(a)), (c === t))) by Restate.from(isLeastElementElim of (a := c, y := z, r := membershipRelation(a), x := a, b := t))
      have((isLeastElement(c, z, membershipRelation(a), a), in(t, z)) |- (in(c, t), (c === t))) by Cut(lastStep, membershipRelationIsMembershipPair of (x := a, a := c, b := t))
      thenHave((aInterP, isLeastElement(c, z, membershipRelation(a), a), P(t) /\ in(t, a)) |- (in(c, t), (c === t))) by Substitution.ApplyRules(aInterPDef)
    }

    have(in(c, a) |- in(c, a)) by Hypothesis
    val eqCase = thenHave((a === t, in(c, a)) |- in(c, t)) by RightSubstEq.withParametersSimple(List((a, t)), lambda(x, in(c, x)))
    have((ordinal(t), ordinal(a), !in(t, a)) |- (in(a, t), a === t)) by Restate.from(ordinalCases of (b := t))
    have((ordinal(t), ordinal(a), !in(t, a), in(c, a)) |- (in(a, t), in(c, t))) by Cut(lastStep, eqCase)
    have((ordinal(t), ordinal(a), !in(t, a), in(c, a)) |- in(c, t)) by Cut(lastStep, ordinalTransitive of (a := c, b := a, c := t))
    have((ordinal(t), ordinal(a), !in(t, a), isLeastElement(c, z, membershipRelation(a), a)) |- in(c, t)) by Cut(isLeastElementInDomain of (a := c, y := z, r := membershipRelation(a), x := a), lastStep)
    thenHave((ordinal(t), ordinal(a), !in(t, a), isLeastElement(c, z, membershipRelation(a), a)) |- in(c, t) \/ (c === t)) by RightOr
    have((ordClass, P(t), ordinal(a), !in(t, a), isLeastElement(c, z, membershipRelation(a), a)) |- in(c, t) \/ (c === t)) by Cut(ordClassMembership of (x := t), lastStep)
    have((aInterP, ordClass, P(t), ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- in(c, t) \/ (c === t)) by LeftOr(lastStep, inCase)
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- P(t) ==> (in(c, t) \/ (c === t))) by RightImplies
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- forall(t, P(t) ==> (in(c, t) \/ (c === t)))) by RightForall
    have((aInterP, ordClass, ordinal(a), in(c, z), isLeastElement(c, z, membershipRelation(a), a)) |- P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t)))) by RightAnd(lastStep, inAInterPRight of (t := c))
    have((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t)))) by Cut(isLeastElementInSubset of (a := c, y := z, r := membershipRelation(a), x := a), lastStep)
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by RightExists
    thenHave((aInterP, ordClass, ordinal(a), exists(c, isLeastElement(c, z, membershipRelation(a), a))) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by LeftExists
    have((aInterP, ordClass, ordinal(a), exists(b, P(b) /\ !in(a, b) /\ !(a === b))) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by Cut(leastElementExists, lastStep)
    have((aInterP, ordClass, P(a), exists(b, P(b) /\ !in(a, b) /\ !(a === b))) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by Cut(ordClassMembership of (x := a), lastStep)
    have((aInterP, ordClass, P(a)) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by LeftOr(lastStep, easyCase)
    thenHave((exists(z, aInterP), ordClass, P(a)) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by LeftExists
    have((ordClass, P(a)) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by Cut(aInterPExistence, lastStep)
    thenHave((ordClass, exists(a, P(a))) |- exists(c, P(c) /\ forall(t, P(t) ==> (in(c, t) \/ (c === t))))) by LeftExists
  }

  /**
    * Theorem --- Every set of ordinals has a least element
    * 
    *   `0 ≠ x ⊆ Ord |- ∃a ∈ x. ∀b ∈ x. a ≤ b`
    */
  val setOfOrdinalsHasLeastElement = Lemma(
    (forall(a, in(a, x) ==> ordinal(a)), !(x === emptySet)) |- exists(a, in(a, x) /\ forall(b, in(b, x) ==> (in(a, b) \/ (a === b))))
  ) {
    have(thesis) by Cut(nonEmptySetHasAnElement, ordinalSubclassHasMinimalElement of (P := lambda(a, in(a, x))))
  }

  /**
    * Theorem --- Any transitive set of ordinals is an ordinal
    * 
    *   `transitiveSet(x), ∀a ∈ x. ordinal(a) |- ordinal(x)` 
    */
  val transitiveSetOfOrdinalsIsOrdinal = Lemma(
    (forall(a, in(a, x) ==> ordinal(a)), transitiveSet(x)) |- ordinal(x)
  ) {

    val elemOrd = forall(a, in(a, x) ==> ordinal(a))
    have(elemOrd |- elemOrd) by Hypothesis
    val membershipIsOrd = thenHave((elemOrd, in(a, x)) |- ordinal(a)) by InstantiateForall(a)
    have((elemOrd, in(a, y), subset(y, x)) |- ordinal(a)) by Cut(subsetElim of (x := y, y := x, z := a), lastStep)
    thenHave((elemOrd, subset(y, x)) |- in(a, y) ==> ordinal(a)) by RightImplies
    val subsetElemOrdinals = thenHave((elemOrd, subset(y, x)) |- forall(a, in(a, y) ==> ordinal(a))) by RightForall


    val strictPartOrd = have(elemOrd |- strictPartialOrder(membershipRelation(x), x)) subproof {
      have((in(a, b), in(b, c), in(a, x), in(c, x), ordinal(c)) |- in(pair(a, c), membershipRelation(x))) by Cut(ordinalTransitive, membershipRelationIntro of (b := c))
      have((elemOrd, in(a, b), in(b, c), in(a, x), in(c, x)) |- in(pair(a, c), membershipRelation(x))) by Cut(membershipIsOrd of (a := c), lastStep)
      thenHave((elemOrd, in(a, b), in(b, c), in(a, x) /\ in(b, x), in(b, x) /\ in(c, x)) |- in(pair(a, c), membershipRelation(x))) by Weakening
      have((elemOrd, in(a, b), in(b, c), in(a, x) /\ in(b, x), in(pair(b, c), membershipRelation(x))) |- in(pair(a, c), membershipRelation(x))) by Cut(membershipRelationInDomainPair of (a := b , b := c), lastStep)
      have((elemOrd, in(a, b), in(a, x) /\ in(b, x), in(pair(b, c), membershipRelation(x))) |- in(pair(a, c), membershipRelation(x))) by Cut(membershipRelationIsMembershipPair of (a := b, b := c), lastStep)
      have((elemOrd, in(a, b), in(pair(a, b), membershipRelation(x)), in(pair(b, c), membershipRelation(x))) |- in(pair(a, c), membershipRelation(x))) by Cut(membershipRelationInDomainPair, lastStep)
      have((elemOrd, in(pair(a, b), membershipRelation(x)), in(pair(b, c), membershipRelation(x))) |- in(pair(a, c), membershipRelation(x))) by Cut(membershipRelationIsMembershipPair, lastStep)
      thenHave(elemOrd |- (in(pair(a, b), membershipRelation(x)) /\ in(pair(b, c), membershipRelation(x))) ==> in(pair(a, c), membershipRelation(x))) by Restate
      thenHave(elemOrd |- forall(c, (in(pair(a, b), membershipRelation(x)) /\ in(pair(b, c), membershipRelation(x))) ==> in(pair(a, c), membershipRelation(x)))) by RightForall
      thenHave(elemOrd |- forall(b, forall(c, in(pair(a, b), membershipRelation(x)) /\ in(pair(b, c), membershipRelation(x)) ==> in(pair(a, c), membershipRelation(x))))) by RightForall
      thenHave(elemOrd |- forall(a, forall(b, forall(c, in(pair(a, b), membershipRelation(x)) /\ in(pair(b, c), membershipRelation(x)) ==> in(pair(a, c), membershipRelation(x)))))) by RightForall
      have((elemOrd, relationBetween(membershipRelation(x), x, x)) |- transitive(membershipRelation(x), x)) by Cut(lastStep, transitiveIntro of (r := membershipRelation(x)))
      have(elemOrd |- transitive(membershipRelation(x), x)) by Cut(membershipRelationIsARelation, lastStep)
      have((elemOrd, irreflexive(membershipRelation(x), x)) |- strictPartialOrder(membershipRelation(x), x)) by Cut(lastStep, strictPartialOrderIntro of (r := membershipRelation(x)))
      have(thesis) by Cut(membershipRelationIrreflexive, lastStep)
    }

    val strictTotOrd = have(elemOrd |- strictTotalOrder(membershipRelation(x), x)) subproof {
      have((ordinal(a), ordinal(b), in(a, x), in(b, x)) |- (in(pair(a, b), membershipRelation(x)), in(b, a), a === b)) by Cut(ordinalCases, membershipRelationIntro)
      have((ordinal(a), ordinal(b), in(a, x), in(b, x)) |- (in(pair(a, b), membershipRelation(x)), in(pair(b, a), membershipRelation(x)), a === b)) by Cut(lastStep, membershipRelationIntro of (a := b, b := a))
      have((elemOrd, ordinal(b), in(a, x), in(b, x)) |- (in(pair(a, b), membershipRelation(x)), in(pair(b, a), membershipRelation(x)), a === b)) by Cut(membershipIsOrd, lastStep)
      have((elemOrd, in(a, x), in(b, x)) |- (in(pair(a, b), membershipRelation(x)), in(pair(b, a), membershipRelation(x)), a === b)) by Cut(membershipIsOrd of (a := b), lastStep)
      thenHave(elemOrd |- (in(a, x) /\ in(b, x)) ==> (in(pair(a, b), membershipRelation(x)) \/ in(pair(b, a), membershipRelation(x)) \/ (a === b))) by Restate
      thenHave(elemOrd |- forall(b, (in(a, x) /\ in(b, x)) ==> in(pair(a, b), membershipRelation(x)) \/ in(pair(b, a), membershipRelation(x)) \/ (a === b))) by RightForall
      thenHave(elemOrd |- forall(a, forall(b, (in(a, x) /\ in(b, x)) ==> in(pair(a, b), membershipRelation(x)) \/ in(pair(b, a), membershipRelation(x)) \/ (a === b)))) by RightForall
      have((elemOrd, relationBetween(membershipRelation(x), x, x)) |- connected(membershipRelation(x), x)) by Cut(lastStep, connectedIntro of (r := membershipRelation(x)))
      have(elemOrd |- connected(membershipRelation(x), x)) by Cut(membershipRelationIsARelation, lastStep)
      have((elemOrd, strictPartialOrder(membershipRelation(x), x)) |- strictTotalOrder(membershipRelation(x), x)) by Cut(lastStep, strictTotalOrderIntro of (r := membershipRelation(x)))
      have(thesis) by Cut(strictPartOrd, lastStep)
    }

    have(forall(b, in(b, y) ==> (in(a, b) \/ (a === b))) |- forall(b, in(b, y) ==> (in(a, b) \/ (a === b)))) by Hypothesis
    thenHave((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(b, y)) |- (in(a, b), a === b)) by InstantiateForall(b)
    have((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(a, x), in(b, x), in(b, y)) |- (in(pair(a, b), membershipRelation(x)), a === b)) by Cut(lastStep, membershipRelationIntro)
    have((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(a, x), subset(y, x), in(b, y)) |- (in(pair(a, b), membershipRelation(x)), a === b)) by Cut(subsetElim of (x := y, y := x, z := b), lastStep)
    thenHave((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(a, x), subset(y, x)) |- in(b, y) ==> (in(pair(a, b), membershipRelation(x)) \/ (a === b))) by Restate
    thenHave((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(a, x), subset(y, x)) |- forall(b, in(b, y) ==> (in(pair(a, b), membershipRelation(x)) \/ (a === b)))) by RightForall
    have((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), in(a, x), subset(y, x), in(a, y), strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(lastStep, isLeastElementIntro of (r := membershipRelation(x)))
    have((forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), subset(y, x), in(a, y), strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(subsetElim of (x := y, y := x, z := a), lastStep)
    have((elemOrd, forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), subset(y, x), in(a, y)) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(strictPartOrd, lastStep)
    thenHave((elemOrd, in(a, y) /\ forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), subset(y, x)) |- isLeastElement(a, y, membershipRelation(x), x)) by LeftAnd
    thenHave((elemOrd, in(a, y) /\ forall(b, in(b, y) ==> (in(a, b) \/ (a === b))), subset(y, x)) |- exists(a, isLeastElement(a, y, membershipRelation(x), x))) by RightExists
    thenHave((elemOrd, exists(a, in(a, y) /\ forall(b, in(b, y) ==> (in(a, b) \/ (a === b)))), subset(y, x)) |- exists(a, isLeastElement(a, y, membershipRelation(x), x))) by LeftExists
    have((elemOrd, forall(a, in(a, y) ==> ordinal(a)), subset(y, x), !(y === emptySet)) |- exists(a, isLeastElement(a, y, membershipRelation(x), x))) by Cut(setOfOrdinalsHasLeastElement of (x := y), lastStep)
    have((elemOrd, subset(y, x), !(y === emptySet)) |- exists(a, isLeastElement(a, y, membershipRelation(x), x))) by Cut(subsetElemOrdinals, lastStep)
    thenHave(elemOrd |- (subset(y, x) /\ !(y === emptySet)) ==> exists(a, isLeastElement(a, y, membershipRelation(x), x))) by Restate
    thenHave(elemOrd |- forall(y, subset(y, x) /\ !(y === emptySet) ==> exists(a, isLeastElement(a, y, membershipRelation(x), x)))) by RightForall
    have((elemOrd, strictTotalOrder(membershipRelation(x), x)) |- strictWellOrder(membershipRelation(x), x)) by Cut(lastStep, strictWellOrderIntro of (r := membershipRelation(x)))
    have(elemOrd |- strictWellOrder(membershipRelation(x), x)) by Cut(strictTotOrd, lastStep)
    have(thesis) by Cut(lastStep, ordinalIntro of (a := x))
  }

  /**
    * Theorem --- There is no set of ordinals
    * 
    *   `¬∃x. x = {a | ordinal(a)}`
    */
  val noSetOfOrdinals = Lemma(
    !exists(x, forall(a, in(a, x) <=> ordinal(a)))
  ) {
    val ordinalClass = forall(a, in(a, x) <=> ordinal(a))

    have(ordinalClass |- ordinalClass) by Hypothesis
    val ordinalClassDef = thenHave(ordinalClass |- in(a, x) <=> ordinal(a)) by InstantiateForall(a)
    thenHave(ordinalClass |- in(a, x) ==> ordinal(a)) by Weakening
    val ordinalClassIsSetOfOrd = thenHave(ordinalClass |- forall(a, in(a, x) ==> ordinal(a))) by RightForall
    
    have(ordinalClass |- transitiveSet(x)) subproof {
      have((in(a, x), in(b, a), ordinalClass) |- in(b, x)) by Substitution.ApplyRules(ordinalClassDef, ordinalClassDef of (a := b))(elementsOfOrdinalsAreOrdinals)
      thenHave(ordinalClass |- (in(b, a) /\ in(a, x)) ==> in(b, x)) by Restate
      thenHave(ordinalClass |- forall(a, (in(b, a) /\ in(a, x)) ==> in(b, x))) by RightForall
      thenHave(ordinalClass |- forall(b, forall(a, (in(b, a) /\ in(a, x)) ==> in(b, x)))) by RightForall
      have(thesis) by Cut(lastStep, transitiveSetAltIntro)
    }

    have((ordinalClass, forall(a, in(a, x) ==> ordinal(a))) |- ordinal(x)) by Cut(lastStep, transitiveSetOfOrdinalsIsOrdinal)
    have(ordinalClass |- ordinal(x)) by Cut(ordinalClassIsSetOfOrd, lastStep)
    thenHave(ordinalClass |- in(x, x)) by Substitution.ApplyRules(ordinalClassDef)
    have(ordinalClass |- ()) by RightAnd(lastStep, selfNonInclusion)
    thenHave(exists(x, ordinalClass) |- ()) by LeftExists
  }


  val transfiniteInductionOnAllOrdinals = Lemma(
    forall(a, ordinal(a) ==> (forall(b, in(b, a) ==> P(b)) ==> P(a))) |- forall(a, ordinal(a) ==> P(a))
  ) {
    val ih = forall(a, ordinal(a) ==> (forall(b, in(b, a) ==> P(b)) ==> P(a)))
    have(ih |- ih) by Hypothesis
    val ihImpliesPA = thenHave((ih, ordinal(a), forall(b, in(b, a) ==> P(b))) |- P(a)) by InstantiateForall(a)

    have((ordinal(x) /\ !P(x)) ==> ordinal(x)) by Restate
    val ordIsOrd = thenHave(forall(x, (ordinal(x) /\ !P(x)) ==> ordinal(x))) by RightForall

    val ordCases = have((ordinal(a), ordinal(b), in(b, a)) |- !in(a, b) /\ !(a === b)) by Sorry

    val minElement = forall(b, ((ordinal(b) /\ !P(b)) ==> (in(a, b) \/ (a === b))))
    have(minElement |- minElement) by Hypothesis
    thenHave((minElement, ordinal(b), !in(a, b) /\ !(a === b)) |- P(b)) by InstantiateForall(b)
    have((minElement, ordinal(a), ordinal(b), in(b, a)) |- P(b)) by Cut(ordCases, lastStep)
    have((minElement, ordinal(a), in(b, a)) |- P(b)) by Cut(elementsOfOrdinalsAreOrdinals, lastStep)
    thenHave((minElement, ordinal(a)) |- in(b, a) ==> P(b)) by RightImplies
    thenHave((minElement, ordinal(a)) |- forall(b, in(b, a) ==> P(b))) by RightForall
    have((minElement, ordinal(a), ih) |- P(a)) by Cut(lastStep, ihImpliesPA)
    thenHave((ordinal(a) /\ !P(a) /\ minElement, ih) |- ()) by Restate
    thenHave((exists(a, ordinal(a) /\ !P(a) /\ minElement), ih) |- ()) by LeftExists
    have((forall(x, (ordinal(x) /\ !P(x)) ==> ordinal(x)), exists(x, ordinal(x) /\ !P(x)), ih) |- ()) by Cut(ordinalSubclassHasMinimalElement of (P := lambda(x, ordinal(x) /\ !P(x))), lastStep)
    have((ih, exists(x, ordinal(x) /\ !P(x))) |- ()) by Cut(ordIsOrd, lastStep)
  }

  val transfiniteInductionOnOrdinal = Lemma(
    (ordinal(x), forall(a, in(a, x) ==> (forall(b, in(b, a) ==> P(b)) ==> P(a)))) |- forall(a, in(a, x) ==> P(a))
  ) {
    val ih = have((forall(b, in(b, a) ==> (in(b, x) ==> P(b))), in(a, x), ordinal(x)) |- forall(b, in(b, a) ==> P(b))) subproof {
      have(forall(b, in(b, a) ==> (in(b, x) ==> P(b))) |- forall(b, in(b, a) ==> (in(b, x) ==> P(b)))) by Hypothesis
      thenHave((forall(b, in(b, a) ==> (in(b, x) ==> P(b))), in(b, a), in(b, x)) |- P(b)) by InstantiateForall(b)
      have((forall(b, in(b, a) ==> (in(b, x) ==> P(b))), in(b, a), in(a, x), ordinal(x)) |- P(b)) by Cut(ordinalTransitive of (a := b, b := a, c := x), lastStep)
      thenHave((forall(b, in(b, a) ==> (in(b, x) ==> P(b))), in(a, x), ordinal(x)) |- in(b, a) ==> P(b)) by RightImplies
      thenHave(thesis) by RightForall
    }

    val assumptions = in(a, x) ==> (forall(b, in(b, a) ==> P(b)) ==> P(a))

    have((assumptions, forall(b, in(b, a) ==> P(b)), in(a, x)) |- P(a)) by Restate
    have((assumptions, in(a, x), forall(b, in(b, a) ==> (in(b, x) ==> P(b))), ordinal(x)) |- P(a)) by Cut(ih, lastStep)
    thenHave((forall(a, assumptions), in(a, x), forall(b, in(b, a) ==> (in(b, x) ==> P(b))), ordinal(x)) |- P(a)) by LeftForall
    thenHave((forall(a, assumptions), ordinal(x)) |-  ordinal(a) ==> (forall(b, in(b, a) ==> (in(b, x) ==> P(b))) ==> (in(a, x) ==> P(a)))) by Weakening
    thenHave((forall(a, assumptions), ordinal(x)) |-  forall(a, ordinal(a) ==> (forall(b, in(b, a) ==> (in(b, x) ==> P(b))) ==> (in(a, x) ==> P(a))))) by RightForall
    have((forall(a, assumptions), ordinal(x)) |- forall(a, ordinal(a) ==> (in(a, x) ==> P(a)))) by Cut(lastStep, transfiniteInductionOnAllOrdinals of (P := lambda(a, in(a, x) ==> P(a))))
    thenHave((forall(a, assumptions), ordinal(x), ordinal(a), in(a, x)) |- P(a)) by InstantiateForall(a)
    have((forall(a, assumptions), ordinal(x), in(a, x)) |- P(a)) by Cut(elementsOfOrdinalsAreOrdinals of (b := a, a := x), lastStep)
    thenHave((forall(a, assumptions), ordinal(x)) |- in(a, x) ==> P(a)) by RightImplies
    thenHave(thesis) by RightForall
  }
}
