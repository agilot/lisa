package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Relations.*
import lisa.maths.settheory.Functions.*
import lisa.maths.settheory.orderings.MembershipRelation.*
import lisa.maths.settheory.orderings.PartialOrders.*
import lisa.maths.settheory.InductiveSets.*
import lisa.maths.settheory.orderings.Segments.*

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
  private val e = variable
  private val m = variable
  private val n = variable

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

  private val A = variable
  private val B = variable
  private val P = predicate[1]
  private val Q = predicate[1]
  private val schemPred = predicate[1]
  private val R = predicate[2]

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
  val transitiveSet = DEF(x) --> ∀(y, y ∈ x ==> y ⊆ x)

  /**
   * Theorem --- Transitive set introduction rule
   *
   *     `∀ y. y ∈ x ⇒ y ⊆ x |- transitiveSet(x)`
   */
  val transitiveSetIntro = Lemma(∀(y, y ∈ x ==> y ⊆ x) |- transitiveSet(x)) {
    have(∀(y, y ∈ x ==> y ⊆ x) |- ∀(y, y ∈ x ==> y ⊆ x)) by Hypothesis
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }

  /**
   * Theorem --- Transitive set elimination rule
   *
   *     `transitiveSet(x), y ∈ x |- y ⊆ x`
   */
  val transitiveSetElim = Lemma((transitiveSet(x), y ∈ x) |- y ⊆ x) {
    have(∀(y, y ∈ x ==> y ⊆ x) |- ∀(y, y ∈ x ==> y ⊆ x)) by Hypothesis
    thenHave((∀(y, y ∈ x ==> y ⊆ x), y ∈ x) |- y ⊆ x) by InstantiateForall(y)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }


  /**
   * Theorem --- The two definitions of a transitive set are equivalent.
   *
   *    `(∀ y. y ∈ x ⇒ y ⊆ x) <=> (∀ z. ∀ y. z ∈ y ⇒ y ∈ x ⇒ z ∈ x)`
   */
  val transitiveSetAltDef = Lemma(transitiveSet(x) <=> ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) {

    val lhs = have(∀(y, y ∈ x ==> y ⊆ x) ==> ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) subproof {
      have(∀(y, y ∈ x ==> y ⊆ x) |- ∀(y, y ∈ x ==> y ⊆ x)) by Hypothesis
      thenHave((∀(y, y ∈ x ==> y ⊆ x), y ∈ x) |- y ⊆ x) by InstantiateForall(y)
      have((∀(y, y ∈ x ==> y ⊆ x), y ∈ x, z ∈ y) |- z ∈ x) by Cut(lastStep, subsetElim of (x := y, y := x))
      thenHave((∀(y, y ∈ x ==> y ⊆ x)) |- (z ∈ y /\ y ∈ x) ==> z ∈ x) by Restate
      thenHave((∀(y, y ∈ x ==> y ⊆ x)) |- ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) by RightForall
      thenHave((∀(y, y ∈ x ==> y ⊆ x)) |- ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) by RightForall
    }

    val rhs = have(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) ==> ∀(y, y ∈ x ==> y ⊆ x)) subproof {
      have(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) by Hypothesis
      thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) by InstantiateForall(z)
      thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) /\ y ∈ x |- (z ∈ y) ==> z ∈ x) by InstantiateForall(y)
      thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) /\ y ∈ x |- ∀(z, z ∈ y ==> z ∈ x)) by RightForall
      have(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) /\ y ∈ x |- y ⊆ x) by Cut(lastStep, subsetIntro of (x -> y, y -> x))
      thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- y ∈ x ==> y ⊆ x) by Restate
      thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- ∀(y, y ∈ x ==> y ⊆ x)) by RightForall
    }

    have(∀(y, y ∈ x ==> y ⊆ x) <=> ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) by RightIff(lhs, rhs)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSet.definition)
  }

  /**
   * Theorem --- Transitive set alternative introduction rule
   *
   *     `∀ z. ∀ y. z ∈ y ⇒ y ∈ x ⇒ z ∈ x |- transitiveSet(x)`
   */
  val transitiveSetAltIntro = Lemma(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- transitiveSet(x)) {
    have(thesis) by Weakening(transitiveSetAltDef)
  }

  /**
   * Theorem --- Transitive set alternative elimination rule
   *
   *     `transitiveSet(x), z ∈ y, y ∈ x |- z ∈ x`
   */
  val transitiveSetAltElim = Lemma((transitiveSet(x), z ∈ y, y ∈ x) |- z ∈ x) {
    have(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- ∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x))) by Hypothesis
    thenHave(∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) |- ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)) by InstantiateForall(z)
    thenHave((∀(z, ∀(y, (z ∈ y /\ y ∈ x) ==> z ∈ x)), z ∈ y, y ∈ x) |- z ∈ x) by InstantiateForall(y)
    thenHave(thesis) by Substitution.ApplyRules(transitiveSetAltDef)
  }

  /**
   * Theorem --- The empty set is transitive.
   *
   *   `transitiveSet(∅)`
   */
  val emptySetTransitive = Lemma(transitiveSet(∅)) {
    have(y ∈ ∅ ==> y ⊆ ∅) by Weakening(emptySetAxiom of (x -> y))
    thenHave(∀(y, y ∈ ∅ ==> y ⊆ ∅)) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetIntro of (x := ∅))
  }

  /**
    * Theorem --- The union of transitive sets is transitive.
    * 
    *  `∀ x ∈ y. transitiveSet(x) |- transitiveSet(∪ y)
    */
  val unionTransitive = Lemma(∀(x, x ∈ y ==> transitiveSet(x)) |- transitiveSet(union(y))) {

    have((transitiveSet(x), w ∈ z, z ∈ x, x ∈ y) |- w ∈ union(y)) by Cut(transitiveSetAltElim of (z := w, y := z), unionIntro of (z := w, x := y, y := x))
    thenHave((x ∈ y ==> transitiveSet(x), w ∈ z, z ∈ x /\ x ∈ y) |- w ∈ union(y)) by Tautology
    thenHave((∀(x, x ∈ y ==> transitiveSet(x)), w ∈ z, z ∈ x /\ x ∈ y) |- w ∈ union(y)) by LeftForall
    thenHave((∀(x, x ∈ y ==> transitiveSet(x)), w ∈ z, ∃(x, z ∈ x /\ x ∈ y)) |- w ∈ union(y)) by LeftExists
    have((∀(x, x ∈ y ==> transitiveSet(x)), w ∈ z, z ∈ union(y)) |- w ∈ union(y)) by Cut(unionElim of (x := y), lastStep)
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- w ∈ z /\ z ∈ union(y) ==> w ∈ union(y)) by Restate
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- ∀(z, w ∈ z /\ z ∈ union(y) ==> w ∈ union(y))) by RightForall
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- ∀(w, ∀(z, w ∈ z /\ z ∈ union(y) ==> w ∈ union(y)))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := union(y)))
  }

  /**
    * Theorem --- The union of a set and all its elements is transitive.
    * 
    *  `∀ x ∈ y. transitiveSet(x) |- transitiveSet((∪ y) ∪ y)`
    */
  val transitiveSetUnionAndElement = Lemma(∀(x, x ∈ y ==> transitiveSet(x)) |- transitiveSet(setUnion(union(y), y))) {
    
    have((z ∈ setUnion(union(y), y), w ∈ z) |- (z ∈ union(y), w ∈ union(y))) by Cut(setUnionElim of (x := union(y)), unionIntro of (z := w, y := z, x := y))
    have((z ∈ setUnion(union(y), y), w ∈ z) |- (z ∈ union(y), w ∈ setUnion(union(y), y))) by Cut(lastStep, setUnionLeftIntro of (z := w, x := union(y)))
    have((z ∈ setUnion(union(y), y), w ∈ z, transitiveSet(union(y))) |- (w ∈ union(y), w ∈ setUnion(union(y), y))) by Cut(lastStep, transitiveSetAltElim of (z := w, y := z, x := union(y)))
    have((z ∈ setUnion(union(y), y), w ∈ z, transitiveSet(union(y))) |- w ∈ setUnion(union(y), y)) by Cut(lastStep, setUnionLeftIntro of (z := w, x := union(y)))
    have((z ∈ setUnion(union(y), y), w ∈ z, ∀(x, x ∈ y ==> transitiveSet(x))) |- w ∈ setUnion(union(y), y)) by Cut(unionTransitive, lastStep)
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- w ∈ z /\ z ∈ setUnion(union(y), y) ==> w ∈ setUnion(union(y), y)) by Restate
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- ∀(z, w ∈ z /\ z ∈ setUnion(union(y), y) ==> w ∈ setUnion(union(y), y))) by RightForall
    thenHave(∀(x, x ∈ y ==> transitiveSet(x)) |- ∀(w, ∀(z, w ∈ z /\ z ∈ setUnion(union(y), y) ==> w ∈ setUnion(union(y), y)))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := setUnion(union(y), y)))
  }

  /**
    * Theorem --- If the membership relation is transitive, then any member of a transitive set is transitive.
    * 
    *   `transitive(∈_x, x), transitiveSet(x), y ∈ x |- transitiveSet(y)`
    */
  val transitiveSetRelationTransitiveSet = Lemma((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- transitiveSet(y)) {
    have((transitive(membershipRelation(x), x), pair(w, z) ∈ membershipRelation(x), pair(z, y) ∈ membershipRelation(x)) |- w ∈ y) by Cut(transitiveElim of (y := z, z := y, r := membershipRelation(x)), membershipRelationIsMembershipPair of (a := w, b := y))
    have((transitive(membershipRelation(x), x), w ∈ z, w ∈ x, z ∈ x, pair(z, y) ∈ membershipRelation(x)) |- w ∈ y) by Cut(membershipRelationIntro of (a := w, b := z), lastStep)
    have((transitive(membershipRelation(x), x), w ∈ z, w ∈ x, z ∈ x, z ∈ y, y ∈ x) |- w ∈ y) by Cut(membershipRelationIntro of (a := z, b := y), lastStep)
    have((transitiveSet(x), transitive(membershipRelation(x), x), w ∈ z, z ∈ x, z ∈ y, y ∈ x) |- w ∈ y) by Cut(transitiveSetAltElim of (z := w, y := z), lastStep)
    have((transitiveSet(x), transitive(membershipRelation(x), x), w ∈ z, z ∈ y, y ∈ x) |- w ∈ y) by Cut(transitiveSetAltElim, lastStep)
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- (w ∈ z /\ z ∈ y) ==> w ∈ y) by Restate
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- ∀(z, (w ∈ z /\ z ∈ y) ==> w ∈ y)) by RightForall
    thenHave((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- ∀(w, ∀(z, (w ∈ z /\ z ∈ y) ==> w ∈ y))) by RightForall
    have(thesis) by Cut(lastStep, transitiveSetAltIntro of (x := y)) 
  }

  
  val membershipRelationInTransitiveSets = Lemma((transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y)) |- pair(a, b) ∈ membershipRelation(x)) {
    have((transitiveSet(x), a ∈ b, a ∈ y, b ∈ x, y ∈ x) |- pair(a, b) ∈ membershipRelation(x)) by Cut(transitiveSetAltElim of (z := a), membershipRelationIntro)
    have((transitiveSet(x), a ∈ b, a ∈ y, b ∈ y, y ∈ x) |- pair(a, b) ∈ membershipRelation(x)) by Cut(transitiveSetAltElim of (z := b), lastStep)
    thenHave((transitiveSet(x), a ∈ b /\ a ∈ y /\ b ∈ y, y ∈ x) |- pair(a, b) ∈ membershipRelation(x)) by Restate
    have(thesis) by Cut(membershipRelationElimPair of (x := y), lastStep)
  }

  /**
    * Theorem --- If the membership relation is transitive on a transitive set, then any of its members induces a transitive relation.
    * 
    *   `transitive(∈_x, x), transitiveSet(x), y ∈ x |- transitive(∈_y, y)`
    */
  val transitiveSetRelationTransitive = Lemma((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- transitive(membershipRelation(y), y)) {
    have((transitive(membershipRelation(x), x), pair(a, b) ∈ membershipRelation(x), pair(b, c) ∈ membershipRelation(x)) |- a ∈ c) by Cut(transitiveElim of (w := a, y := b, z := c, r := membershipRelation(x)), membershipRelationIsMembershipPair of (b := c))
    have((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(x)) |- a ∈ c) by Cut(membershipRelationInTransitiveSets, lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(y)) |- a ∈ c) by Cut(membershipRelationInTransitiveSets of (a := b, b := c), lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(y)) |- a ∈ y /\ b ∈ y /\ a ∈ c) by RightAnd(membershipRelationInDomainPair of (x := y), lastStep)
    have((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(y)) |- a ∈ y /\ b ∈ y /\ c ∈ y /\ a ∈ c) by RightAnd(membershipRelationInDomainPair of (x := y, a := b, b := c), lastStep)
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(y)) |- a ∈ y /\ c ∈ y /\ a ∈ c) by Weakening
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x, pair(a, b) ∈ membershipRelation(y), pair(b, c) ∈ membershipRelation(y)) |- pair(a, c) ∈ membershipRelation(y)) by Substitution.ApplyRules(membershipRelationElemPair of (b := c, x := y))
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- (pair(a, b) ∈ membershipRelation(y) /\ pair(b, c) ∈ membershipRelation(y)) ==> pair(a, c) ∈ membershipRelation(y)) by Restate
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- ∀(c, (pair(a, b) ∈ membershipRelation(y) /\ pair(b, c) ∈ membershipRelation(y)) ==> pair(a, c) ∈ membershipRelation(y))) by RightForall
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- ∀(b, ∀(c, (pair(a, b) ∈ membershipRelation(y) /\ pair(b, c) ∈ membershipRelation(y)) ==> pair(a, c) ∈ membershipRelation(y)))) by RightForall
    thenHave((transitive(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- ∀(a, ∀(b, ∀(c, (pair(a, b) ∈ membershipRelation(y) /\ pair(b, c) ∈ membershipRelation(y)) ==> pair(a, c) ∈ membershipRelation(y))))) by RightForall
    have((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x, relationBetween(membershipRelation(y), y, y)) |- transitive(membershipRelation(y), y)) by Cut(lastStep, transitiveIntro of (r := membershipRelation(y), x := y))
    have(thesis) by Cut(membershipRelationIsARelation of (x := y), lastStep)

  }

  /**
    * Theorem --- If the membership relation is a strict partial order on a transitive set, then any of its members induces a strict partial order.
    * 
    *   `strictPartialOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictPartialOrder(∈_y, y)`
    */
  val transitiveStrictPartialOrderElem = Lemma((transitiveSet(x), strictPartialOrder(membershipRelation(x), x), y ∈ x) |- strictPartialOrder(membershipRelation(y), y)) {
    have(transitive(membershipRelation(y), y) |- strictPartialOrder(membershipRelation(y), y)) by Cut(membershipRelationIrreflexive of (x := y), strictPartialOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), transitive(membershipRelation(x), x), y ∈ x) |- strictPartialOrder(membershipRelation(y), y)) by Cut(transitiveSetRelationTransitive, lastStep)
    have(thesis) by Cut(strictPartialOrderTransitive of (r := membershipRelation(x)), lastStep)
  }

  /**
    * Theorem --- If the membership relation is connected on a transitive set, then any of its members induces a connected relation.
    * 
    *   `connected(∈_x, x), transitiveSet(x), y ∈ x |- connected(∈_y, y)`
    */
  val transitiveConnectedMembershipRelation = Lemma((transitiveSet(x), connected(membershipRelation(x), x), y ∈ x) |- connected(membershipRelation(y), y)) {

    have((pair(a, b) ∈ membershipRelation(x), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y)) by Cut(membershipRelationIsMembershipPair, membershipRelationIntro of (x := y))
    val left = thenHave((pair(a, b) ∈ membershipRelation(x), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Weakening

    have((pair(b, a) ∈ membershipRelation(x), a ∈ y, b ∈ y) |- pair(b, a) ∈ membershipRelation(y)) by Cut(membershipRelationIsMembershipPair of (a := b, b := a), membershipRelationIntro of (x := y, a := b, b := a))
    val right = thenHave((pair(b, a) ∈ membershipRelation(x), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Weakening

    have(a === b |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Restate
    have((pair(b, a) ∈ membershipRelation(x) \/ (a === b), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by LeftOr(right, lastStep)
    have((pair(a, b) ∈ membershipRelation(x) \/ (pair(b, a) ∈ membershipRelation(x)) \/ (a === b), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by LeftOr(left, lastStep)
    have((connected(membershipRelation(x), x), a ∈ x, b ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Cut(connectedElim of (y := a, z := b, r := membershipRelation(x)), lastStep)
    have((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x, b ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Cut(transitiveSetAltElim of (z := a), lastStep)
    have((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Cut(transitiveSetAltElim of (z := b), lastStep)
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x, a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)) by Restate
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b))) by Restate
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b)))) by RightForall
    thenHave((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x) |- ∀(a, ∀(b, (a ∈ y /\ b ∈ y) ==> (pair(a, b) ∈ membershipRelation(y) \/ (pair(b, a) ∈ membershipRelation(y)) \/ (a === b))))) by RightForall
    have((connected(membershipRelation(x), x), transitiveSet(x), y ∈ x, relationBetween(membershipRelation(y), y, y)) |- connected(membershipRelation(y), y)) by Cut(lastStep, connectedIntro of (r -> membershipRelation(y), x -> y)) 
    have(thesis) by Cut(membershipRelationIsARelation of (x -> y), lastStep)
  }

  /**
    * Theorem --- If the membership relation is a strict total order on a transitive set, then any of its members induces a strict total order.
    * 
    *   `strictTotalOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictTotalOrder(∈_y, y)`
    */
  val transitiveStrictTotalOrderElem = Lemma((transitiveSet(x), strictTotalOrder(membershipRelation(x), x), y ∈ x) |- strictTotalOrder(membershipRelation(y), y)) {
    have((transitiveSet(x), connected(membershipRelation(y), y), strictPartialOrder(membershipRelation(x), x), y ∈ x) |- strictTotalOrder(membershipRelation(y), y)) by Cut(transitiveStrictPartialOrderElem, strictTotalOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), connected(membershipRelation(x), x), strictPartialOrder(membershipRelation(x), x), y ∈ x) |- strictTotalOrder(membershipRelation(y), y)) by Cut(transitiveConnectedMembershipRelation, lastStep)
    have((transitiveSet(x), strictTotalOrder(membershipRelation(x), x), strictPartialOrder(membershipRelation(x), x), y ∈ x) |- strictTotalOrder(membershipRelation(y), y)) by Cut(strictTotalOrderConnected of (r := membershipRelation(x)), lastStep)
    have(thesis) by Cut(strictTotalOrderIsPartial of (r := membershipRelation(x)), lastStep)
  }

  val transitiveSetLeastElement = Lemma((transitiveSet(x), isLeastElement(a, z, membershipRelation(x), x), y ∈ x, z ⊆ y) |- isLeastElement(a, z, membershipRelation(y), y)) {
 
    val eqCase = have(a === b |- pair(a, b) ∈ membershipRelation(y) \/ (a === b)) by Restate

    have((pair(a, b) ∈ membershipRelation(x), a ∈ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y)) by Cut(membershipRelationIsMembershipPair, membershipRelationIntro of (x := y))
    have((pair(a, b) ∈ membershipRelation(x), a ∈ z, z ⊆ y, b ∈ y) |- pair(a, b) ∈ membershipRelation(y)) by Cut(subsetElim of (z := a, x := z), lastStep)
    have((pair(a, b) ∈ membershipRelation(x), a ∈ z, z ⊆ y, b ∈ z) |- pair(a, b) ∈ membershipRelation(y)) by Cut(subsetElim of (z := b, x := z), lastStep)
    thenHave((pair(a, b) ∈ membershipRelation(x), a ∈ z, z ⊆ y, b ∈ z) |- pair(a, b) ∈ membershipRelation(y) \/ (a === b)) by Weakening

    have((pair(a, b) ∈ membershipRelation(x) \/ (a === b), a ∈ z, z ⊆ y, b ∈ z) |- pair(a, b) ∈ membershipRelation(y) \/ (a === b)) by LeftOr(lastStep, eqCase)
    have((isLeastElement(a, z, membershipRelation(x), x), a ∈ z, z ⊆ y, b ∈ z) |- pair(a, b) ∈ membershipRelation(y) \/ (a === b)) by Cut(isLeastElementElim of (r := membershipRelation(x), y := z), lastStep)
    thenHave((isLeastElement(a, z, membershipRelation(x), x), a ∈ z, z ⊆ y) |- b ∈ z ==> pair(a, b) ∈ membershipRelation(y) \/ (a === b)) by RightImplies
    thenHave((isLeastElement(a, z, membershipRelation(x), x), a ∈ z, z ⊆ y) |- ∀(b, b ∈ z ==> pair(a, b) ∈ membershipRelation(y) \/ (a === b))) by RightForall
    have((isLeastElement(a, z, membershipRelation(x), x), a ∈ z, z ⊆ y, strictPartialOrder(membershipRelation(y), y)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(lastStep, isLeastElementIntro of (r := membershipRelation(y), y := z, x := y))
    have((isLeastElement(a, z, membershipRelation(x), x), z ⊆ y, strictPartialOrder(membershipRelation(y), y)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(isLeastElementInSubset of (y := z, r := membershipRelation(x)), lastStep)
    have((isLeastElement(a, z, membershipRelation(x), x), z ⊆ y, transitiveSet(x), y ∈ x, strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, z, membershipRelation(y), y)) by Cut(transitiveStrictPartialOrderElem, lastStep)
    have(thesis) by Cut(isLeastElementInStrictPartialOrder of (r := membershipRelation(x), y := z), lastStep) 
  }
  
  /**
    * Theorem --- If the membership relation is a strict well-order on a transitive set, then any of its members induces a strict well-order.
    * 
    *   `strictWellOrder(∈_x, x), transitiveSet(x), y ∈ x |- strictWellOrder(∈_y, y)`
    */
  val transitiveStrictWellOrderElem = Lemma((transitiveSet(x), strictWellOrder(membershipRelation(x), x), y ∈ x) |- strictWellOrder(membershipRelation(y), y)) {
    have((transitiveSet(x), isLeastElement(a, z, membershipRelation(x), x), y ∈ x, z ⊆ y) |- ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by RightExists(transitiveSetLeastElement)
    thenHave((transitiveSet(x), ∃(a, isLeastElement(a, z, membershipRelation(x), x)), y ∈ x, z ⊆ y) |- ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by LeftExists
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), z ⊆ x, !(z === ∅), y ∈ x, z ⊆ y) |- ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(strictWellOrderElim of (y := z, r := membershipRelation(x)), lastStep)
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), !(z === ∅), y ∈ x, y ⊆ x, z ⊆ y) |- ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(subsetTransitivity of (x := z, z := x), lastStep)
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), !(z === ∅), y ∈ x, z ⊆ y) |- ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by Cut(transitiveSetElim, lastStep)
    thenHave((transitiveSet(x), strictWellOrder(membershipRelation(x), x), y ∈ x) |- (z ⊆ y /\ !(z === ∅)) ==> ∃(a, isLeastElement(a, z, membershipRelation(y), y))) by Restate
    thenHave((transitiveSet(x), strictWellOrder(membershipRelation(x), x), y ∈ x) |- ∀(z, (z ⊆ y /\ !(z === ∅)) ==> ∃(a, isLeastElement(a, z, membershipRelation(y), y)))) by RightForall
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), y ∈ x, strictTotalOrder(membershipRelation(y), y)) |- strictWellOrder(membershipRelation(y), y)) by Cut(lastStep, strictWellOrderIntro of (r := membershipRelation(y), x := y))
    have((transitiveSet(x), strictWellOrder(membershipRelation(x), x), y ∈ x, strictTotalOrder(membershipRelation(x), x)) |- strictWellOrder(membershipRelation(y), y)) by Cut(transitiveStrictTotalOrderElem, lastStep)
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
    ordinal(∅)
  ) {
    have(strictWellOrder(membershipRelation(∅), ∅) |- ordinal(∅)) by Cut(emptySetTransitive, ordinalIntro of (a := ∅))
    thenHave(strictWellOrder(∅, ∅) |- ordinal(∅)) by Substitution.ApplyRules(emptyMembershipRelation)
    have(thesis) by Cut(emptyStrictWellOrder, lastStep)
  }

  /**
   * Theorem --- Elements of ordinals are also ordinals
   *
   *   `a ∈ Ord, b ∈ a |- b ∈ Ord`
   */
  val elementsOfOrdinalsAreOrdinals = Lemma(
    (ordinal(a), b ∈ a) |- ordinal(b)
  ) {
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), b ∈ a, transitiveSet(b)) |- ordinal(b)) by Cut(transitiveStrictWellOrderElem of (x := a, y := b), ordinalIntro of (a := b))
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), b ∈ a, transitive(membershipRelation(a), a)) |- ordinal(b)) by Cut(transitiveSetRelationTransitiveSet of (x := a, y := b), lastStep)
    have((transitiveSet(a), strictWellOrder(membershipRelation(a), a), b ∈ a) |- ordinal(b)) by Cut(strictWellOrderTransitive of (r := membershipRelation(a), x := a), lastStep)
    have((transitiveSet(a), ordinal(a), b ∈ a) |- ordinal(b)) by Cut(ordinalStrictWellOrder, lastStep)
    have(thesis) by Cut(ordinalTransitiveSet, lastStep)
  }

  /**
    * Theorem --- Ordinals are transitive
    * 
    *   `c ∈ Ord, a ∈ b ∈ c |- a ∈ c` 
    */
  val ordinalTransitive = Lemma(
    (ordinal(c), a ∈ b, b ∈ c) |- a ∈ c
  ) {
    have(thesis) by Cut(ordinalTransitiveSet of (a := c), transitiveSetAltElim of (x := c, y := b, z := a))
  }

  val elementOfOrdinalIsInitialSegment = Lemma(
    (ordinal(a), b ∈ a) |- b === initialSegment(b, membershipRelation(a), a)
  ) {
    have((strictWellOrder(membershipRelation(a), a), x ∈ a, b ∈ a, x ∈ b) |- x ∈ initialSegment(b, membershipRelation(a), a)) by Cut(membershipRelationIntro of (a := x, x := a), initialSegmentIntro of (r := membershipRelation(a), x := a, a := x))
    have((ordinal(a), x ∈ a, b ∈ a, x ∈ b) |- x ∈ initialSegment(b, membershipRelation(a), a)) by Cut(ordinalStrictWellOrder, lastStep)
    have((ordinal(a), b ∈ a, x ∈ b) |- x ∈ initialSegment(b, membershipRelation(a), a)) by Cut(ordinalTransitive of (c := a, a := x, b := b), lastStep)
    val forward = thenHave((ordinal(a), b ∈ a) |- x ∈ b ==> x ∈ initialSegment(b, membershipRelation(a), a)) by RightImplies
    
    have((strictWellOrder(membershipRelation(a), a), x ∈ initialSegment(b, membershipRelation(a), a)) |- x ∈ b) by Cut(initialSegmentElim of (r := membershipRelation(a), x := a, a := x), membershipRelationIsMembershipPair of (a := x, x := a))
    have((ordinal(a), x ∈ initialSegment(b, membershipRelation(a), a)) |- x ∈ b) by Cut(ordinalStrictWellOrder, lastStep)
    val backward = thenHave(ordinal(a) |- x ∈ initialSegment(b, membershipRelation(a), a) ==> x ∈ b) by RightImplies

    have((ordinal(a), b ∈ a) |- x ∈ b <=> x ∈ initialSegment(b, membershipRelation(a), a)) by RightIff(forward, backward)
    thenHave((ordinal(a), b ∈ a) |- ∀(x, x ∈ b <=> x ∈ initialSegment(b, membershipRelation(a), a))) by RightForall
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

    val forward = have((ordIsomorphism, ordinal(a), sLeastElem, s ∈ a) |- s ⊆ app(f, s)) subproof {
      have((t ∈ a, pair(t, s) ∈ membershipRelation(a), sLeastElem) |- app(f, t) === t) by Cut(belowLeastElement of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a, b := t), notInNonIdentitySetElim of (x := a))
      have((ordIsomorphism, sLeastElem, t ∈ a, pair(t, s) ∈ membershipRelation(a)) |- pair(t, app(f, s)) ∈ membershipRelation(b)) by Substitution.ApplyRules(lastStep)(relationIsomorphismElimForward of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := t, b := s))
      have((ordIsomorphism, sLeastElem, t ∈ a, pair(t, s) ∈ membershipRelation(a)) |- t ∈ app(f, s)) by Cut(lastStep, membershipRelationIsMembershipPair of (x := b, a := t, b := app(f, s)))
      have((ordIsomorphism, sLeastElem, t ∈ a, t ∈ s, s ∈ a) |- t ∈ app(f, s)) by Cut(membershipRelationIntro of (x := a, a := t, b := s), lastStep)
      have((ordIsomorphism, ordinal(a), sLeastElem, t ∈ s, s ∈ a) |- t ∈ app(f, s)) by Cut(ordinalTransitive of (a := t, b := s, c := a), lastStep)
      thenHave((ordIsomorphism, ordinal(a), sLeastElem, s ∈ a) |- t ∈ s ==> t ∈ app(f, s)) by RightImplies
      thenHave((ordIsomorphism, ordinal(a), sLeastElem, s ∈ a) |- ∀(t, t ∈ s ==> t ∈ app(f, s))) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := s, y := app(f, s)))
    }

    val backward = have((ordIsomorphism, ordinal(b), sLeastElem, s ∈ a) |- app(f, s) ⊆ s) subproof { 

      val inverseFunctionBelow = have((ordIsomorphism, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- pair(app(inverseRelation(f), t), s) ∈ membershipRelation(a)) by Substitution.ApplyRules(inverseRelationRightCancel of (b := t, x := a, y := b))(relationIsomorphismElimBackward of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := app(inverseRelation(f), t), b := s))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- app(inverseRelation(f), t) ∉ nonIdentitySet(f, a)) by Cut(lastStep, belowLeastElement of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a, b := app(inverseRelation(f), t)))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- app(f, app(inverseRelation(f), t)) === app(inverseRelation(f), t)) by Cut(lastStep, notInNonIdentitySetElim of (x := a, t := app(inverseRelation(f), t)))
      thenHave((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- t === app(inverseRelation(f), t)) by Substitution.ApplyRules(inverseRelationRightCancel of (b := t, x := a, y := b))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- pair(t, s) ∈ membershipRelation(a)) by Substitution.ApplyRules(lastStep)(inverseFunctionBelow)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, pair(t, app(f, s)) ∈ membershipRelation(b)) |- t ∈ s) by Cut(lastStep, membershipRelationIsMembershipPair of (x := a, a := t, b := s))
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(f, s) ∈ b, app(inverseRelation(f), t) ∈ a, s ∈ a, t ∈ app(f, s)) |- t ∈ s) by Cut(membershipRelationIntro of (x := b, a := t, b := app(f, s)),lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), t ∈ b, app(f, s) ∈ b, s ∈ a, t ∈ app(f, s)) |- t ∈ s) by Cut(inverseFunctionImageInDomain of (b := t, x := a, y := b), lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), ordinal(b), app(f, s) ∈ b, s ∈ a, t ∈ app(f, s)) |- t ∈ s) by Cut(ordinalTransitive of (a := t, b := app(f, s), c := b), lastStep)
      have((ordIsomorphism, sLeastElem, bijective(f, a, b), ordinal(b), s ∈ a, t ∈ app(f, s)) |- t ∈ s) by Cut(relationIsomorphismAppInCodomain of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b, a := s), lastStep)
      have((ordIsomorphism, sLeastElem, ordinal(b), s ∈ a, t ∈ app(f, s)) |- t ∈ s) by Cut(relationIsomorphismBijective of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
      thenHave((ordIsomorphism, sLeastElem, ordinal(b), s ∈ a) |- t ∈ app(f, s) ==> t ∈ s) by RightImplies
      thenHave((ordIsomorphism, sLeastElem, ordinal(b), s ∈ a) |- ∀(t, t ∈ app(f, s) ==> t ∈ s)) by RightForall
      have(thesis) by Cut(lastStep, subsetIntro of (x := app(f, s), y := s))
    }
    
    have((ordIsomorphism, ordinal(a), sLeastElem, s ∈ a, app(f, s) ⊆ s) |- s === app(f, s)) by Cut(forward, subsetAntisymmetry of (x := s, y := app(f, s)))
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem, s ∈ a) |- s === app(f, s)) by Cut(backward, lastStep)
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem, s ∈ a) |- s ∉ nonIdentitySet(f, a)) by Cut(lastStep, notInNonIdentitySetIntro of (x := a, t := s))
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem) |- s ∉ nonIdentitySet(f, a)) by Cut(isLeastElementInDomain of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a), lastStep)
    have((ordIsomorphism, ordinal(a), ordinal(b), sLeastElem) |- ()) by RightAnd(lastStep, isLeastElementInSubset of (a := s, y := nonIdentitySet(f, a), r := membershipRelation(a), x := a))
    thenHave((ordIsomorphism, ordinal(a), ordinal(b), ∃(s, sLeastElem)) |- ()) by LeftExists
    have((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b), nonIdentitySet(f, a) ⊆ a, !(nonIdentitySet(f, a) === ∅)) |- ()) by Cut(strictWellOrderElim of (y := nonIdentitySet(f, a), r := membershipRelation(a), x := a), lastStep)
    have((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b), !(nonIdentitySet(f, a) === ∅)) |- ()) by Cut(nonIdentitySetSubsetDomain of (x := a), lastStep)
    thenHave((strictWellOrder(membershipRelation(a), a), ordIsomorphism, ordinal(a), ordinal(b)) |- nonIdentitySet(f, a) === ∅) by Restate
    have((ordIsomorphism, ordinal(a), ordinal(b)) |-  nonIdentitySet(f, a) === ∅) by Cut(ordinalStrictWellOrder, lastStep)
    have((ordIsomorphism, ordinal(a), ordinal(b), surjective(f, a, b)) |- a === b) by Cut(lastStep, nonIdentitySetEmpty of (x := a, y := b))
    have((ordIsomorphism, ordinal(a), ordinal(b), bijective(f, a, b)) |- a === b) by Cut(bijectiveSurjective of (x := a, y := b), lastStep)
    have(thesis) by Cut(relationIsomorphismBijective of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
  }

  val ordinalCases = Lemma(
    (ordinal(a), ordinal(b)) |- (a ∈ b, b ∈ a, (a === b))
  ) {
    val middle = have((ordinal(a), ordinal(b), relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b)) |- (a ∈ b, b ∈ a, a === b)) by Weakening(isomorphicOrdinalsAreEqual)

    have(c ∈ a |- c ∈ a) by Hypothesis
    thenHave((ordinal(c), ordinal(b), c ∈ a, relationIsomorphism(f, membershipRelation(c), c, membershipRelation(b), b)) |- b ∈ a) by Substitution.ApplyRules(isomorphicOrdinalsAreEqual of (a := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), c ∈ a, relationIsomorphism(f, membershipRelation(initialSegment(c, membershipRelation(a), a)), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- b ∈ a) by Substitution.ApplyRules(elementOfOrdinalIsInitialSegment of (b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), c ∈ a, relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- b ∈ a) by Substitution.ApplyRules(membershipRelationInitialSegment of (b := c))
    have((ordinal(b), ordinal(a), c ∈ a, relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- b ∈ a) by Cut(elementsOfOrdinalsAreOrdinals of (b := c), lastStep)
    thenHave((ordinal(b), ordinal(a), c ∈ a /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)) |- (a ∈ b, b ∈ a, a === b)) by Weakening
    val right = thenHave((ordinal(b), ordinal(a), ∃(c, c ∈ a /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (a ∈ b, b ∈ a, a === b)) by LeftExists

    have(c ∈ b |- c ∈ b) by Hypothesis
    thenHave((ordinal(a), ordinal(c), c ∈ b, relationIsomorphism(f, membershipRelation(a), a, membershipRelation(c), c)) |- a ∈ b) by Substitution.ApplyRules(isomorphicOrdinalsAreEqual of (b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), c ∈ b, relationIsomorphism(f, membershipRelation(a), a, membershipRelation(initialSegment(c, membershipRelation(b), b)), initialSegment(c, membershipRelation(b), b))) |- a ∈ b) by Substitution.ApplyRules(elementOfOrdinalIsInitialSegment of (a := b, b := c))
    thenHave((ordinal(c), ordinal(b), ordinal(a), c ∈ b, relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- a ∈ b) by Substitution.ApplyRules(membershipRelationInitialSegment of (b := c, a := b))
    have((ordinal(b), ordinal(a), c ∈ b, relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- a ∈ b) by Cut(elementsOfOrdinalsAreOrdinals of (a := b, b := c), lastStep)
    thenHave((ordinal(b), ordinal(a), c ∈ b /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) |- (a ∈ b, b ∈ a, a === b)) by Weakening
    val left = thenHave((ordinal(b), ordinal(a), ∃(c, c ∈ b /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b)))) |- (a ∈ b, b ∈ a, a === b)) by LeftExists

    have((ordinal(a), ordinal(b), 
      ∃(c, c ∈ b /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      ∃(c, c ∈ a /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (a ∈ b, b ∈ a, a === b)) by LeftOr(left, right)
    have((ordinal(a), ordinal(b), 
      relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b) \/
      ∃(c, c ∈ b /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      ∃(c, c ∈ a /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b))) |- (a ∈ b, b ∈ a, a === b)) by LeftOr(middle, lastStep)
    thenHave((ordinal(a), ordinal(b), 
      ∃(f, relationIsomorphism(f, membershipRelation(a), a, membershipRelation(b), b) \/
      ∃(c, c ∈ b /\ relationIsomorphism(f, membershipRelation(a), a, initialSegmentOrder(c, membershipRelation(b), b), initialSegment(c, membershipRelation(b), b))) \/
      ∃(c, c ∈ a /\ relationIsomorphism(f, initialSegmentOrder(c, membershipRelation(a), a), initialSegment(c, membershipRelation(a), a), membershipRelation(b), b)))) |- (a ∈ b, b ∈ a, (a === b))) by LeftExists
    have((ordinal(a), ordinal(b), strictWellOrder(membershipRelation(a), a), strictWellOrder(membershipRelation(b), b)) |- (a ∈ b, b ∈ a, (a === b))) by Cut(initialSegmentIsomorphicCases of (r1 := membershipRelation(a), x := a, r2 := membershipRelation(b), y := b), lastStep)
    have((ordinal(a), ordinal(b), strictWellOrder(membershipRelation(b), b)) |- (a ∈ b, b ∈ a, (a === b))) by Cut(ordinalStrictWellOrder, lastStep)
    have(thesis) by Cut(ordinalStrictWellOrder of (a := b), lastStep)
  }

  /**
   * Theorem --- An ordinal is less or equal to another ordinal if and only if it is a subset of it.
   * 
   *  `a ∈ Ord, b ∈ Ord |- a ⊆ b ⇔ a ≤ b`
   */
  val leqOrdinalIsSubset = Lemma(
    (ordinal(a), ordinal(b)) |- (a ∈ b \/ (a === b)) <=> a ⊆ b
  ) {
    val forward = have(ordinal(b) |- (a ∈ b \/ (a === b)) ==> a ⊆ b) subproof {
      have(a === b |- a ⊆ b) by RightSubstEq.withParametersSimple(List((a, b)), lambda(x, a ⊆ x))(subsetReflexivity of (x := a))
      have((transitiveSet(b), a ∈ b \/ (a === b)) |- a ⊆ b) by LeftOr(transitiveSetElim of (y := a, x := b), lastStep)
      have((ordinal(b), a ∈ b \/ (a === b)) |- a ⊆ b) by Cut(ordinalTransitiveSet of (a := b), lastStep)
    }

    val backward = have((ordinal(a), ordinal(b)) |- a ⊆ b ==> (a ∈ b \/ (a === b))) subproof {
      have((transitiveSet(a), b ∈ a, a ⊆ b) |- a === b) by Cut(transitiveSetElim of (x := a, y := b), subsetAntisymmetry of (x := a, y := b))
      have((ordinal(a), b ∈ a, a ⊆ b) |- a === b) by Cut(ordinalTransitiveSet, lastStep)
      have((ordinal(a), ordinal(b), a ⊆ b) |- (a ∈ b, a === b)) by Cut(ordinalCases, lastStep)
    }

    have(thesis) by RightIff(forward, backward)
  }

  val ordinalSubsetImpliesLeq = Lemma(
    (ordinal(a), ordinal(b), a ⊆ b) |- (a ∈ b, (a === b))
  ) {
    have(thesis) by Weakening(leqOrdinalIsSubset)
  }

  val ordinalLeqImpliesSubset = Lemma(
    (ordinal(b), a ∈ b \/ (a === b)) |- a ⊆ b
  ) {
    sorry
  }

  val ordinalLeqLtImpliesLt = Lemma(
    (ordinal(c), a ∈ b \/ (a === b), b ∈ c) |- a ∈ c 
  ) {
    have(b ∈ c |- b ∈ c) by Hypothesis
    thenHave((a === b, b ∈ c) |- a ∈ c) by RightSubstEq.withParametersSimple(List((a, b)), lambda(x, x ∈ c))
    have(thesis) by LeftOr(ordinalTransitive, lastStep)
  }
  

  /**
    * Theorem --- The element of an ordinal is a subset of this ordinal
    * 
    *   `a ∈ b ∈ Ord |- a ⊆ b`
    */
  val elementOfOrdinalIsSubset = Lemma(
    (ordinal(b), a ∈ b) |- a ⊆ b
  ) {
    have((ordinal(a), ordinal(b), a ∈ b) |- a ⊆ b) by Weakening(leqOrdinalIsSubset)
    have(thesis) by Cut(elementsOfOrdinalsAreOrdinals of (a := b, b := a), lastStep)
  }
  

  /**
    * Theorem --- Every subclass of ordinals has a minimal element
    * 
    *   `0 ≠ P ⊆ Ord |- ∃a ∈ P. ∀b ∈ P. a ≤ b`
    */ 
  val ordinalSubclassHasMinimalElement = Lemma(
    (∀(x, P(x) ==> ordinal(x)), ∃(x, P(x))) |- ∃(a, P(a) /\ ∀(b, P(b) ==> (a ∈ b \/ (a === b)))) 
  ) {

    val aInterP = ∀(t, t ∈ z <=> (t ∈ a /\ P(t)))

    have(aInterP |- aInterP) by Hypothesis
    val aInterPDef = thenHave(aInterP |- t ∈ z <=> (t ∈ a /\ P(t))) by InstantiateForall(t)
    val inAInterP = thenHave((aInterP, t ∈ z) |- t ∈ a /\ P(t)) by Weakening
    val inAInterPRight = thenHave((aInterP, t ∈ z) |- P(t)) by Weakening
    have((aInterP, t ∈ z) |- t ∈ a) by Weakening(inAInterP)
    thenHave(aInterP |- t ∈ z ==> t ∈ a) by RightImplies
    thenHave(aInterP |- ∀(t, t ∈ z ==> t ∈ a)) by RightForall
    val inAInterPSubset = have(aInterP |- z ⊆ a) by Cut(lastStep, subsetIntro of (x := z, y := a))

    have(∃!(z, aInterP)) by UniqueComprehension(a, lambda(x, P(x)))
    val aInterPExistence = have(∃(z, aInterP)) by Cut(lastStep, existsOneImpliesExists of (P := lambda(z, ∀(t, t ∈ z <=> (t ∈ a /\ P(t))))))

    val ordClass = ∀(x, P(x) ==> ordinal(x))
    have(ordClass |- ordClass) by Hypothesis
    val ordClassMembership = thenHave((ordClass, P(x)) |- ordinal(x)) by InstantiateForall(x)

    have((P(a), ∀(b, P(b) ==> (a ∈ b \/ (a === b)))) |- P(a) /\ ∀(b, P(b) ==> (a ∈ b \/ (a === b)))) by Restate
    val easyCase = thenHave((P(a), ∀(b, P(b) ==> (a ∈ b \/ (a === b)))) |- ∃(a, P(a) /\ ∀(b, P(b) ==> (a ∈ b \/ (a === b))))) by RightExists
    
    val leastElementExists = have((aInterP, ordClass, ordinal(a), ∃(b, P(b) /\ a ∉ b /\ (a =/= b))) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) subproof {
      have((ordinal(a), ordinal(b), P(b), a ∉ b, a =/= b) |- b ∈ a /\ P(b)) by Tautology.from(ordinalCases)
      val bInZ = thenHave((aInterP, ordinal(a), ordinal(b), P(b), a ∉ b, a =/= b) |- b ∈ z) by Substitution.ApplyRules(aInterPDef of (t := b))
      have((aInterP, ordinal(a), ordinal(b), P(b), a ∉ b, a =/= b) |- !(z === ∅)) by Cut(lastStep, setWithElementNonEmpty of (y := b, x := z))
      have((aInterP, ordinal(a), strictWellOrder(membershipRelation(a), a), z ⊆ a, ordinal(b), P(b), a ∉ b, a =/= b) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(lastStep, strictWellOrderElim of (y := z, r := membershipRelation(a), x := a))
      have((aInterP, ordinal(a), strictWellOrder(membershipRelation(a), a), ordinal(b), P(b), a ∉ b, a =/= b) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(inAInterPSubset, lastStep)
      have((aInterP, ordinal(a), ordinal(b), P(b), a ∉ b, a =/= b) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(ordinalStrictWellOrder, lastStep)
      have((aInterP, ordClass, ordinal(a), P(b), a ∉ b, a =/= b) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) by Cut(ordClassMembership of (x := b), lastStep)
      thenHave((aInterP, ordClass, ordinal(a), P(b) /\ a ∉ b /\ (a =/= b)) |- ∃(c, isLeastElement(c, z, membershipRelation(a), a))) by Restate
      thenHave(thesis) by LeftExists
    }

    val inCase = have((aInterP, isLeastElement(c, z, membershipRelation(a), a), P(t), t ∈ a) |- c ∈ t \/ (c === t)) subproof {
      have((isLeastElement(c, z, membershipRelation(a), a), t ∈ z) |- (pair(c, t) ∈ membershipRelation(a), (c === t))) by Restate.from(isLeastElementElim of (a := c, y := z, r := membershipRelation(a), x := a, b := t))
      have((isLeastElement(c, z, membershipRelation(a), a), t ∈ z) |- (c ∈ t, (c === t))) by Cut(lastStep, membershipRelationIsMembershipPair of (x := a, a := c, b := t))
      thenHave((aInterP, isLeastElement(c, z, membershipRelation(a), a), P(t) /\ t ∈ a) |- (c ∈ t, (c === t))) by Substitution.ApplyRules(aInterPDef)
    }

    have(c ∈ a |- c ∈ a) by Hypothesis
    val eqCase = thenHave((a === t, c ∈ a) |- c ∈ t) by RightSubstEq.withParametersSimple(List((a, t)), lambda(x, c ∈ x))
    have((ordinal(t), ordinal(a), t ∉ a) |- (a ∈ t, a === t)) by Restate.from(ordinalCases of (b := t))
    have((ordinal(t), ordinal(a), t ∉ a, c ∈ a) |- (a ∈ t, c ∈ t)) by Cut(lastStep, eqCase)
    have((ordinal(t), ordinal(a), t ∉ a, c ∈ a) |- c ∈ t) by Cut(lastStep, ordinalTransitive of (a := c, b := a, c := t))
    have((ordinal(t), ordinal(a), t ∉ a, isLeastElement(c, z, membershipRelation(a), a)) |- c ∈ t) by Cut(isLeastElementInDomain of (a := c, y := z, r := membershipRelation(a), x := a), lastStep)
    thenHave((ordinal(t), ordinal(a), t ∉ a, isLeastElement(c, z, membershipRelation(a), a)) |- c ∈ t \/ (c === t)) by RightOr
    have((ordClass, P(t), ordinal(a), t ∉ a, isLeastElement(c, z, membershipRelation(a), a)) |- c ∈ t \/ (c === t)) by Cut(ordClassMembership of (x := t), lastStep)
    have((aInterP, ordClass, P(t), ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- c ∈ t \/ (c === t)) by LeftOr(lastStep, inCase)
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- P(t) ==> (c ∈ t \/ (c === t))) by RightImplies
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- ∀(t, P(t) ==> (c ∈ t \/ (c === t)))) by RightForall
    have((aInterP, ordClass, ordinal(a), c ∈ z, isLeastElement(c, z, membershipRelation(a), a)) |- P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t)))) by RightAnd(lastStep, inAInterPRight of (t := c))
    have((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t)))) by Cut(isLeastElementInSubset of (a := c, y := z, r := membershipRelation(a), x := a), lastStep)
    thenHave((aInterP, ordClass, ordinal(a), isLeastElement(c, z, membershipRelation(a), a)) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by RightExists
    thenHave((aInterP, ordClass, ordinal(a), ∃(c, isLeastElement(c, z, membershipRelation(a), a))) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by LeftExists
    have((aInterP, ordClass, ordinal(a), ∃(b, P(b) /\ a ∉ b /\ (a =/= b))) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by Cut(leastElementExists, lastStep)
    have((aInterP, ordClass, P(a), ∃(b, P(b) /\ a ∉ b /\ (a =/= b))) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by Cut(ordClassMembership of (x := a), lastStep)
    have((aInterP, ordClass, P(a)) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by LeftOr(lastStep, easyCase)
    thenHave((∃(z, aInterP), ordClass, P(a)) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by LeftExists
    have((ordClass, P(a)) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by Cut(aInterPExistence, lastStep)
    thenHave((ordClass, ∃(a, P(a))) |- ∃(c, P(c) /\ ∀(t, P(t) ==> (c ∈ t \/ (c === t))))) by LeftExists
  }

  /**
    * Theorem --- Every set of ordinals has a least element
    * 
    *   `0 ≠ x ⊆ Ord |- ∃a ∈ x. ∀b ∈ x. a ≤ b`
    */
  val setOfOrdinalsHasLeastElement = Lemma(
    (∀(a, a ∈ x ==> ordinal(a)), !(x === ∅)) |- ∃(a, a ∈ x /\ ∀(b, b ∈ x ==> (a ∈ b \/ (a === b))))
  ) {
    have(thesis) by Cut(nonEmptySetHasAnElement, ordinalSubclassHasMinimalElement of (P := lambda(a, a ∈ x)))
  }

  /**
    * Theorem --- Any transitive set of ordinals is an ordinal
    * 
    *   `transitiveSet(x), ∀a ∈ x. ordinal(a) |- ordinal(x)` 
    */
  val transitiveSetOfOrdinalsIsOrdinal = Lemma(
    (∀(a, a ∈ x ==> ordinal(a)), transitiveSet(x)) |- ordinal(x)
  ) {

    val elemOrd = ∀(a, a ∈ x ==> ordinal(a))
    have(elemOrd |- elemOrd) by Hypothesis
    val membershipIsOrd = thenHave((elemOrd, a ∈ x) |- ordinal(a)) by InstantiateForall(a)
    have((elemOrd, a ∈ y, y ⊆ x) |- ordinal(a)) by Cut(subsetElim of (x := y, y := x, z := a), lastStep)
    thenHave((elemOrd, y ⊆ x) |- a ∈ y ==> ordinal(a)) by RightImplies
    val subsetElemOrdinals = thenHave((elemOrd, y ⊆ x) |- ∀(a, a ∈ y ==> ordinal(a))) by RightForall


    val strictPartOrd = have(elemOrd |- strictPartialOrder(membershipRelation(x), x)) subproof {
      have((a ∈ b, b ∈ c, a ∈ x, c ∈ x, ordinal(c)) |- pair(a, c) ∈ membershipRelation(x)) by Cut(ordinalTransitive, membershipRelationIntro of (b := c))
      have((elemOrd, a ∈ b, b ∈ c, a ∈ x, c ∈ x) |- pair(a, c) ∈ membershipRelation(x)) by Cut(membershipIsOrd of (a := c), lastStep)
      thenHave((elemOrd, a ∈ b, b ∈ c, a ∈ x /\ b ∈ x, b ∈ x /\ c ∈ x) |- pair(a, c) ∈ membershipRelation(x)) by Weakening
      have((elemOrd, a ∈ b, b ∈ c, a ∈ x /\ b ∈ x, pair(b, c) ∈ membershipRelation(x)) |- pair(a, c) ∈ membershipRelation(x)) by Cut(membershipRelationInDomainPair of (a := b , b := c), lastStep)
      have((elemOrd, a ∈ b, a ∈ x /\ b ∈ x, pair(b, c) ∈ membershipRelation(x)) |- pair(a, c) ∈ membershipRelation(x)) by Cut(membershipRelationIsMembershipPair of (a := b, b := c), lastStep)
      have((elemOrd, a ∈ b, pair(a, b) ∈ membershipRelation(x), pair(b, c) ∈ membershipRelation(x)) |- pair(a, c) ∈ membershipRelation(x)) by Cut(membershipRelationInDomainPair, lastStep)
      have((elemOrd, pair(a, b) ∈ membershipRelation(x), pair(b, c) ∈ membershipRelation(x)) |- pair(a, c) ∈ membershipRelation(x)) by Cut(membershipRelationIsMembershipPair, lastStep)
      thenHave(elemOrd |- (pair(a, b) ∈ membershipRelation(x) /\ pair(b, c) ∈ membershipRelation(x)) ==> pair(a, c) ∈ membershipRelation(x)) by Restate
      thenHave(elemOrd |- ∀(c, (pair(a, b) ∈ membershipRelation(x) /\ pair(b, c) ∈ membershipRelation(x)) ==> pair(a, c) ∈ membershipRelation(x))) by RightForall
      thenHave(elemOrd |- ∀(b, ∀(c, pair(a, b) ∈ membershipRelation(x) /\ pair(b, c) ∈ membershipRelation(x) ==> pair(a, c) ∈ membershipRelation(x)))) by RightForall
      thenHave(elemOrd |- ∀(a, ∀(b, ∀(c, pair(a, b) ∈ membershipRelation(x) /\ pair(b, c) ∈ membershipRelation(x) ==> pair(a, c) ∈ membershipRelation(x))))) by RightForall
      have((elemOrd, relationBetween(membershipRelation(x), x, x)) |- transitive(membershipRelation(x), x)) by Cut(lastStep, transitiveIntro of (r := membershipRelation(x)))
      have(elemOrd |- transitive(membershipRelation(x), x)) by Cut(membershipRelationIsARelation, lastStep)
      have((elemOrd, irreflexive(membershipRelation(x), x)) |- strictPartialOrder(membershipRelation(x), x)) by Cut(lastStep, strictPartialOrderIntro of (r := membershipRelation(x)))
      have(thesis) by Cut(membershipRelationIrreflexive, lastStep)
    }

    val strictTotOrd = have(elemOrd |- strictTotalOrder(membershipRelation(x), x)) subproof {
      have((ordinal(a), ordinal(b), a ∈ x, b ∈ x) |- (pair(a, b) ∈ membershipRelation(x), b ∈ a, a === b)) by Cut(ordinalCases, membershipRelationIntro)
      have((ordinal(a), ordinal(b), a ∈ x, b ∈ x) |- (pair(a, b) ∈ membershipRelation(x), pair(b, a) ∈ membershipRelation(x), a === b)) by Cut(lastStep, membershipRelationIntro of (a := b, b := a))
      have((elemOrd, ordinal(b), a ∈ x, b ∈ x) |- (pair(a, b) ∈ membershipRelation(x), pair(b, a) ∈ membershipRelation(x), a === b)) by Cut(membershipIsOrd, lastStep)
      have((elemOrd, a ∈ x, b ∈ x) |- (pair(a, b) ∈ membershipRelation(x), pair(b, a) ∈ membershipRelation(x), a === b)) by Cut(membershipIsOrd of (a := b), lastStep)
      thenHave(elemOrd |- (a ∈ x /\ b ∈ x) ==> (pair(a, b) ∈ membershipRelation(x) \/ (pair(b, a) ∈ membershipRelation(x)) \/ (a === b))) by Restate
      thenHave(elemOrd |- ∀(b, (a ∈ x /\ b ∈ x) ==> pair(a, b) ∈ membershipRelation(x) \/ (pair(b, a) ∈ membershipRelation(x)) \/ (a === b))) by RightForall
      thenHave(elemOrd |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x) ==> pair(a, b) ∈ membershipRelation(x) \/ (pair(b, a) ∈ membershipRelation(x)) \/ (a === b)))) by RightForall
      have((elemOrd, relationBetween(membershipRelation(x), x, x)) |- connected(membershipRelation(x), x)) by Cut(lastStep, connectedIntro of (r := membershipRelation(x)))
      have(elemOrd |- connected(membershipRelation(x), x)) by Cut(membershipRelationIsARelation, lastStep)
      have((elemOrd, strictPartialOrder(membershipRelation(x), x)) |- strictTotalOrder(membershipRelation(x), x)) by Cut(lastStep, strictTotalOrderIntro of (r := membershipRelation(x)))
      have(thesis) by Cut(strictPartOrd, lastStep)
    }

    have(∀(b, b ∈ y ==> (a ∈ b \/ (a === b))) |- ∀(b, b ∈ y ==> (a ∈ b \/ (a === b)))) by Hypothesis
    thenHave((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), b ∈ y) |- (a ∈ b, a === b)) by InstantiateForall(b)
    have((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), a ∈ x, b ∈ x, b ∈ y) |- (pair(a, b) ∈ membershipRelation(x), a === b)) by Cut(lastStep, membershipRelationIntro)
    have((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), a ∈ x, y ⊆ x, b ∈ y) |- (pair(a, b) ∈ membershipRelation(x), a === b)) by Cut(subsetElim of (x := y, y := x, z := b), lastStep)
    thenHave((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), a ∈ x, y ⊆ x) |- b ∈ y ==> (pair(a, b) ∈ membershipRelation(x) \/ (a === b))) by Restate
    thenHave((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), a ∈ x, y ⊆ x) |- ∀(b, b ∈ y ==> (pair(a, b) ∈ membershipRelation(x) \/ (a === b)))) by RightForall
    have((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), a ∈ x, y ⊆ x, a ∈ y, strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(lastStep, isLeastElementIntro of (r := membershipRelation(x)))
    have((∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), y ⊆ x, a ∈ y, strictPartialOrder(membershipRelation(x), x)) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(subsetElim of (x := y, y := x, z := a), lastStep)
    have((elemOrd, ∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), y ⊆ x, a ∈ y) |- isLeastElement(a, y, membershipRelation(x), x)) by Cut(strictPartOrd, lastStep)
    thenHave((elemOrd, a ∈ y /\ ∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), y ⊆ x) |- isLeastElement(a, y, membershipRelation(x), x)) by LeftAnd
    thenHave((elemOrd, a ∈ y /\ ∀(b, b ∈ y ==> (a ∈ b \/ (a === b))), y ⊆ x) |- ∃(a, isLeastElement(a, y, membershipRelation(x), x))) by RightExists
    thenHave((elemOrd, ∃(a, a ∈ y /\ ∀(b, b ∈ y ==> (a ∈ b \/ (a === b)))), y ⊆ x) |- ∃(a, isLeastElement(a, y, membershipRelation(x), x))) by LeftExists
    have((elemOrd, ∀(a, a ∈ y ==> ordinal(a)), y ⊆ x, !(y === ∅)) |- ∃(a, isLeastElement(a, y, membershipRelation(x), x))) by Cut(setOfOrdinalsHasLeastElement of (x := y), lastStep)
    have((elemOrd, y ⊆ x, !(y === ∅)) |- ∃(a, isLeastElement(a, y, membershipRelation(x), x))) by Cut(subsetElemOrdinals, lastStep)
    thenHave(elemOrd |- (y ⊆ x /\ !(y === ∅)) ==> ∃(a, isLeastElement(a, y, membershipRelation(x), x))) by Restate
    thenHave(elemOrd |- ∀(y, y ⊆ x /\ !(y === ∅) ==> ∃(a, isLeastElement(a, y, membershipRelation(x), x)))) by RightForall
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
    !(∃(x, ∀(a, a ∈ x <=> ordinal(a))))
  ) {
    val ordinalClass = ∀(a, a ∈ x <=> ordinal(a))

    have(ordinalClass |- ordinalClass) by Hypothesis
    val ordinalClassDef = thenHave(ordinalClass |- a ∈ x <=> ordinal(a)) by InstantiateForall(a)
    thenHave(ordinalClass |- a ∈ x ==> ordinal(a)) by Weakening
    val ordinalClassIsSetOfOrd = thenHave(ordinalClass |- ∀(a, a ∈ x ==> ordinal(a))) by RightForall
    
    have(ordinalClass |- transitiveSet(x)) subproof {
      have((a ∈ x, b ∈ a, ordinalClass) |- b ∈ x) by Substitution.ApplyRules(ordinalClassDef, ordinalClassDef of (a := b))(elementsOfOrdinalsAreOrdinals)
      thenHave(ordinalClass |- (b ∈ a /\ a ∈ x) ==> b ∈ x) by Restate
      thenHave(ordinalClass |- ∀(a, (b ∈ a /\ a ∈ x) ==> b ∈ x)) by RightForall
      thenHave(ordinalClass |- ∀(b, ∀(a, (b ∈ a /\ a ∈ x) ==> b ∈ x))) by RightForall
      have(thesis) by Cut(lastStep, transitiveSetAltIntro)
    }

    have((ordinalClass, ∀(a, a ∈ x ==> ordinal(a))) |- ordinal(x)) by Cut(lastStep, transitiveSetOfOrdinalsIsOrdinal)
    have(ordinalClass |- ordinal(x)) by Cut(ordinalClassIsSetOfOrd, lastStep)
    thenHave(ordinalClass |- x ∈ x) by Substitution.ApplyRules(ordinalClassDef)
    have(ordinalClass |- ()) by RightAnd(lastStep, selfNonMembership)
    thenHave(∃(x, ordinalClass) |- ()) by LeftExists
  }

  /**
    * TRANSFINITE INDUCTION
    */

  val transfiniteInductionOnAllOrdinals = Lemma(
    ∀(a, ordinal(a) ==> (∀(b, b ∈ a ==> P(b)) ==> P(a))) |- ∀(a, ordinal(a) ==> P(a))
  ) {
    val ih = ∀(a, ordinal(a) ==> (∀(b, b ∈ a ==> P(b)) ==> P(a)))
    have(ih |- ih) by Hypothesis
    val ihImpliesPA = thenHave((ih, ordinal(a), ∀(b, b ∈ a ==> P(b))) |- P(a)) by InstantiateForall(a)

    have((ordinal(x) /\ !P(x)) ==> ordinal(x)) by Restate
    val ordIsOrd = thenHave(∀(x, (ordinal(x) /\ !P(x)) ==> ordinal(x))) by RightForall

    have(a === b |- b ∉ a) by RightSubstEq.withParametersSimple(List((a, b)), lambda(x, x ∉ a))(selfNonMembership of (x := a))
    val right = thenHave(b ∈ a |- a =/= b) by Restate
    val left = have(b ∈ a |- a ∉ b) by Restate.from(membershipAsymmetry of (x := a, y := b))
    val ordCases = have(b ∈ a |- a ∉ b /\ (a =/= b)) by RightAnd(left, right)

    val minElement = ∀(b, ((ordinal(b) /\ !P(b)) ==> (a ∈ b \/ (a === b))))
    have(minElement |- minElement) by Hypothesis
    thenHave((minElement, ordinal(b), a ∉ b /\ (a =/= b)) |- P(b)) by InstantiateForall(b)
    have((minElement, ordinal(b), b ∈ a) |- P(b)) by Cut(ordCases, lastStep)
    have((minElement, ordinal(a), b ∈ a) |- P(b)) by Cut(elementsOfOrdinalsAreOrdinals, lastStep)
    thenHave((minElement, ordinal(a)) |- b ∈ a ==> P(b)) by RightImplies
    thenHave((minElement, ordinal(a)) |- ∀(b, b ∈ a ==> P(b))) by RightForall
    have((minElement, ordinal(a), ih) |- P(a)) by Cut(lastStep, ihImpliesPA)
    thenHave((ordinal(a) /\ !P(a) /\ minElement, ih) |- ()) by Restate
    thenHave((∃(a, ordinal(a) /\ !P(a) /\ minElement), ih) |- ()) by LeftExists
    have((∀(x, (ordinal(x) /\ !P(x)) ==> ordinal(x)), ∃(x, ordinal(x) /\ !P(x)), ih) |- ()) by Cut(ordinalSubclassHasMinimalElement of (P := lambda(x, ordinal(x) /\ !P(x))), lastStep)
    have((ih, ∃(x, ordinal(x) /\ !P(x))) |- ()) by Cut(ordIsOrd, lastStep)
  }

  val transfiniteInductionOnOrdinal = Lemma(
    (ordinal(x), ∀(a, a ∈ x ==> (∀(b, b ∈ a ==> P(b)) ==> P(a)))) |- ∀(a, a ∈ x ==> P(a))
  ) {
    val ih = have((∀(b, b ∈ a ==> (b ∈ x ==> P(b))), a ∈ x, ordinal(x)) |- ∀(b, b ∈ a ==> P(b))) subproof {
      have(∀(b, b ∈ a ==> (b ∈ x ==> P(b))) |- ∀(b, b ∈ a ==> (b ∈ x ==> P(b)))) by Hypothesis
      thenHave((∀(b, b ∈ a ==> (b ∈ x ==> P(b))), b ∈ a, b ∈ x) |- P(b)) by InstantiateForall(b)
      have((∀(b, b ∈ a ==> (b ∈ x ==> P(b))), b ∈ a, a ∈ x, ordinal(x)) |- P(b)) by Cut(ordinalTransitive of (a := b, b := a, c := x), lastStep)
      thenHave((∀(b, b ∈ a ==> (b ∈ x ==> P(b))), a ∈ x, ordinal(x)) |- b ∈ a ==> P(b)) by RightImplies
      thenHave(thesis) by RightForall
    }

    val assumptions = a ∈ x ==> (∀(b, b ∈ a ==> P(b)) ==> P(a))

    have((assumptions, ∀(b, b ∈ a ==> P(b)), a ∈ x) |- P(a)) by Restate
    have((assumptions, a ∈ x, ∀(b, b ∈ a ==> (b ∈ x ==> P(b))), ordinal(x)) |- P(a)) by Cut(ih, lastStep)
    thenHave((∀(a, assumptions), a ∈ x, ∀(b, b ∈ a ==> (b ∈ x ==> P(b))), ordinal(x)) |- P(a)) by LeftForall
    thenHave((∀(a, assumptions), ordinal(x)) |-  ordinal(a) ==> (∀(b, b ∈ a ==> (b ∈ x ==> P(b))) ==> (a ∈ x ==> P(a)))) by Weakening
    thenHave((∀(a, assumptions), ordinal(x)) |-  ∀(a, ordinal(a) ==> (∀(b, b ∈ a ==> (b ∈ x ==> P(b))) ==> (a ∈ x ==> P(a))))) by RightForall
    have((∀(a, assumptions), ordinal(x)) |- ∀(a, ordinal(a) ==> (a ∈ x ==> P(a)))) by Cut(lastStep, transfiniteInductionOnAllOrdinals of (P := lambda(a, a ∈ x ==> P(a))))
    thenHave((∀(a, assumptions), ordinal(x), ordinal(a), a ∈ x) |- P(a)) by InstantiateForall(a)
    have((∀(a, assumptions), ordinal(x), a ∈ x) |- P(a)) by Cut(elementsOfOrdinalsAreOrdinals of (b := a, a := x), lastStep)
    thenHave((∀(a, assumptions), ordinal(x)) |- a ∈ x ==> P(a)) by RightImplies
    thenHave(thesis) by RightForall
  }



  val successor = DEF(a) --> setUnion(a, singleton(a))

  /**
   * Theorem --- Any number is smaller than its successor
   *
   *     `a < a + 1`
   */
  val inSuccessor = Lemma(a ∈ successor(a)) {
    have(a ∈ singleton(a) |- a ∈ successor(a)) by Substitution.ApplyRules(successor.shortDefinition)(setUnionRightIntro of (x := a, y := singleton(a), z := a))
    have(thesis) by Cut(singletonIntro of (x := a), lastStep)
  }

  val inSuccessorLeq = Lemma(b ∈ successor(a) |- (b ∈ a, a === b)) {
    have(b ∈ setUnion(a, singleton(a)) |-  (b ∈ a, a === b)) by Cut(setUnionElim of (x := a, y := singleton(a), z := b), singletonElim of (y := b, x := a))
    thenHave(thesis) by Substitution.ApplyRules(successor.shortDefinition)
  }

  val inSuccessorSubset = Lemma((ordinal(a), b ∈ successor(a)) |- b ⊆ a) {
    have(b ∈ successor(a) |- b ∈ a \/ (a === b)) by Restate.from(inSuccessorLeq)
    have(thesis) by Cut(lastStep, ordinalLeqImpliesSubset of (b := a, a := b))
  }

  val successorIsTransitiveSet = Lemma(transitiveSet(a) |- transitiveSet(successor(a))) {
    have(transitiveSet(a) |- transitiveSet(a)) by Hypothesis
    thenHave((transitiveSet(a), x ∈ singleton(a)) |- transitiveSet(x)) by Substitution.ApplyRules(singletonElim)
    thenHave(transitiveSet(a) |- x ∈ singleton(a) ==> transitiveSet(x)) by RightImplies
    thenHave(transitiveSet(a) |- ∀(x, x ∈ singleton(a) ==> transitiveSet(x))) by RightForall
    have(transitiveSet(a) |- transitiveSet(setUnion(union(singleton(a)), singleton(a)))) by Cut(lastStep, transitiveSetUnionAndElement of (y := singleton(a)))
    thenHave(transitiveSet(a) |- transitiveSet(setUnion(a, singleton(a)))) by Substitution.ApplyRules(unionSingleton)
    thenHave(thesis) by Substitution.ApplyRules(successor.shortDefinition)
  }

  val successorIsOrdinal = Lemma(ordinal(a) |- ordinal(successor(a))) {
    have(ordinal(a) |- ordinal(a)) by Hypothesis
    thenHave((ordinal(a), a === b) |- ordinal(b)) by RightSubstEq.withParametersSimple(List((b, a)), lambda(x, ordinal(x)))
    have((ordinal(a), b ∈ successor(a)) |- (b ∈ a, ordinal(b))) by Cut(inSuccessorLeq, lastStep)
    have((ordinal(a), b ∈ successor(a)) |- ordinal(b)) by Cut(lastStep, elementsOfOrdinalsAreOrdinals)
    thenHave(ordinal(a) |- b ∈ successor(a) ==> ordinal(b)) by RightImplies
    thenHave(ordinal(a) |- ∀(b, b ∈ successor(a) ==> ordinal(b))) by RightForall
    have((ordinal(a), transitiveSet(successor(a))) |- ordinal(successor(a))) by Cut(lastStep, transitiveSetOfOrdinalsIsOrdinal of (x := successor(a)))
    have((ordinal(a), transitiveSet(a)) |- ordinal(successor(a))) by Cut(successorIsTransitiveSet, lastStep)
    have(thesis) by Cut(ordinalTransitiveSet, lastStep)
  }

  val ordinalLeqImpliesInSuccessor = Lemma((ordinal(a), b ∈ a \/ (a === b)) |- b ∈ successor(a)) {
    have((ordinal(successor(a)), b ∈ a \/ (a === b)) |- b ∈ successor(a)) by Cut(inSuccessor, ordinalLeqLtImpliesLt of (a := b, b := a, c := successor(a)))
    have(thesis) by Cut(successorIsOrdinal, lastStep)
  }

  val ordinalSubsetImpliesInSuccessor = Lemma((ordinal(a), ordinal(b), b ⊆ a) |- b ∈ successor(a)) {
    have((ordinal(a), ordinal(b), b ⊆ a) |- b ∈ a \/ (a === b)) by Restate.from(ordinalSubsetImpliesLeq of (b := a, a := b))
    have(thesis) by Cut(lastStep, ordinalLeqImpliesInSuccessor)
  }

  val ordinalSubsetIffInSuccessor = Lemma((ordinal(a), ordinal(b)) |- b ⊆ a <=> b ∈ successor(a)) {
    val forward = have((ordinal(a), ordinal(b)) |- b ⊆ a ==> b ∈ successor(a)) by RightImplies(ordinalSubsetImpliesInSuccessor)
    val backward = have(ordinal(a) |- b ∈ successor(a) ==> b ⊆ a) by RightImplies(inSuccessorSubset)
    have(thesis) by RightIff(forward, backward)
  }
  

  val successorNoInBetween = Lemma(
    (a ∈ b, b ∈ successor(a)) |- ()
  ) {
    val subst = have((a ∈ b, b ∈ successor(a)) |- a === b) by Cut(inSuccessorLeq, membershipAsymmetry of (x := a, y := b))
    have(a ∈ b |- a ∈ b) by Hypothesis
    thenHave((a ∈ b, b ∈ successor(a)) |- a ∈ a) by Substitution.ApplyRules(subst)
    have(thesis) by RightAnd(lastStep, selfNonMembership of (x := a))
  }

  val successorIsOrdinalImpliesOrdinal = Lemma(ordinal(successor(a)) |- ordinal(a)) {
    have(thesis) by Cut(inSuccessor, elementsOfOrdinalsAreOrdinals of (b := a, a := successor(a)))
  }

  val successorPreservesSubset = Lemma(a ⊆ b |- successor(a) ⊆ successor(b)) {
    sorry
  }

  val successorInjectivity = Lemma(successor(a) === successor(b) |- a === b) {
    sorry
  }

  /**
   * Theorem --- The empty set is not the successor of any set
   * 
   *   `a ≠ 0`
   */
  val successorNonEmpty = Lemma(!(successor(a) === ∅)) {
    have(thesis) by Cut(inSuccessor, setWithElementNonEmpty of (y := a, x := successor(a)))
  }

  /**
    * Theorem --- Any number is a subset of its successor
    * 
    *    `a ⊆ a + 1`
    */
  val subsetSuccessor = Lemma(a ⊆ successor(a)) {
    have(thesis) by Substitution.ApplyRules(successor.shortDefinition)(setUnionLeftSubset of (b := singleton(a)))
  }




  val successorOrdinal = DEF(a) --> ordinal(a) /\ ∃(b, a === successor(b))
  val nonsuccessorOrdinal = DEF(a) --> ordinal(a) /\ !(∃(b, a === successor(b)))

  val successorOrdinalIntro = Lemma(
    (ordinal(a), a === successor(b)) |- successorOrdinal(a)
  ) {
    have(a === successor(b) |- a === successor(b)) by Hypothesis
    val right = thenHave(a === successor(b) |- ∃(b, a === successor(b))) by RightExists
    val left = have(ordinal(a) |- ordinal(a)) by Hypothesis
    have((ordinal(a), a === successor(b)) |- ordinal(a) /\ ∃(b, a === successor(b))) by RightAnd(left, right)
    thenHave(thesis) by Substitution.ApplyRules(successorOrdinal.definition)
  }

  val successorOrdinalIsOrdinal = Lemma(successorOrdinal(a) |- ordinal(a)) {
    have(thesis) by Weakening(successorOrdinal.definition)
  }

  val nonsuccessorOrdinalIsOrdinal = Lemma(nonsuccessorOrdinal(a) |- ordinal(a)) {
    have(thesis) by Weakening(nonsuccessorOrdinal.definition)
  }

  val successorIsSuccessorOrdinal = Lemma(ordinal(a) |- successorOrdinal(successor(a))) {
    have(ordinal(successor(a)) |- successorOrdinal(successor(a))) by Restate.from(successorOrdinalIntro of (a := successor(a), b := a))
    have(thesis) by Cut(successorIsOrdinal, lastStep)
  }

  val intersectionInOrdinal = Lemma((ordinal(a), b ∈ a) |- a ∩ b === b) {
    have(thesis) by Cut(elementOfOrdinalIsSubset of (a := b, b := a), setIntersectionOfSubsetBackward of (y := b, x := a))
  }

  val nonsuccessorOrdinalElim = Lemma(
    nonsuccessorOrdinal(a) |- !(a === successor(b))
  ) {
    have(nonsuccessorOrdinal(a) |- ∀(b, !(a === successor(b)))) by Weakening(nonsuccessorOrdinal.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  val nonsuccessorOrdinalIsInductive = Lemma((nonsuccessorOrdinal(a), b ∈ a) |- successor(b) ∈ a) {
    have((ordinal(a), ordinal(successor(b)), b ∈ a) |- (successor(b) ∈ a, a === successor(b))) by Cut(ordinalCases of (b := successor(b)), successorNoInBetween of (a := b, b := a))
    have((nonsuccessorOrdinal(a), ordinal(a), ordinal(successor(b)), b ∈ a) |- successor(b) ∈ a) by RightAnd(nonsuccessorOrdinalElim, lastStep)
    have((nonsuccessorOrdinal(a), ordinal(a), ordinal(b), b ∈ a) |- successor(b) ∈ a) by Cut(successorIsOrdinal of (a := b), lastStep)
    have((nonsuccessorOrdinal(a), ordinal(a), b ∈ a) |- successor(b) ∈ a) by Cut(elementsOfOrdinalsAreOrdinals, lastStep)
    have(thesis) by Cut(nonsuccessorOrdinalIsOrdinal, lastStep)
  }




  val nonsuccessorOrdinalIsNotSuccessorOrdinal = Lemma(nonsuccessorOrdinal(n) |- !successorOrdinal(n)) {
    sorry
  }

  val successorOrNonsuccessorOrdinal = Lemma(ordinal(n) |- successorOrdinal(n) \/ nonsuccessorOrdinal(n)) {
    sorry
  }

  val leqOrdinalDef = Lemma(ordinal(n) |- m ⊆ n <=> m ∈ successor(n)) {
    sorry
  }

  
}
