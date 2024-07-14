package lisa.maths.settheory

//import lisa.automation.settheory.SetTheoryTactics.*
//import lisa.maths.Quantifiers.*
//import lisa.automation.Substitution

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.settheory.SetTheory.*

object InductiveSets extends lisa.Main {

  // var defs
  private val a = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val r = variable
  private val t = variable

  // relation and function symbols

  private val P = predicate[1]
  private val schemPred = predicate[1]

  /**
   * Chapter 2
   * Ordinal Numbers
   */


  /**
   * Inductive set --- A set is inductive if it contains the empty set, and the
   * [[successor]]s of each of its elements.
   *
   * `inductive(x) ⇔ (∅ ∈ x ⋀ ∀ y. y ∈ x ⇒ successor(y) ∈ x)`
   *
   * @param x set
   */
  // val inductive = DEF(x) --> in(∅, x) /\ ∀(y, y ∈ x ==> in(successor(y), x))

  // /**
  //  * Theorem --- There exists an inductive set.
  //  *
  //  *    `∃ x. inductive(x)`
  //  *
  //  * Equivalent to the Axiom of Infinity ([[infinityAxiom]]). The proof shows
  //  * that the two forms are equivalent by folding the definitions of
  //  * [[successor]] and [[inductive]].
  //  */
  // val inductiveSetExists = Theorem(
  //   ∃(x, inductive(x))
  // ) {
  //   val form = formulaVariable

  //   val succDef = have((successor(y) === union(unorderedPair(y, singleton(x))))) by Restate.from(successor.shortDefinition)
  //   val inductDef = have(inductive(x) <=> in(∅, x) /\ ∀(y, y ∈ x ==> in(successor(y), x))) by Restate.from(inductive.definition)

  //   have((y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate
  //   val succEq = thenHave(
  //     (successor(y) === union(unorderedPair(y, unorderedPair(y, y)))) |- (y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (y ∈ x ==> in(successor(y), x))
  //   ) by RightSubstEq.withParametersSimple(
  //     List((successor(y), union(unorderedPair(y, unorderedPair(y, y))))),
  //     lambda(z, (y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (y ∈ x ==> z ∈ x))
  //   )
  //   val iffinst = have((y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> (y ∈ x ==> in(successor(y), x))) by Cut(succDef, succEq)

  //   val iffquant = {
  //     have((y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (y ∈ x ==> in(successor(y), x))) by Weakening(iffinst)
  //     thenHave(∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- (y ∈ x ==> in(successor(y), x))) by LeftForall
  //     thenHave(∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- ∀(y, y ∈ x ==> in(successor(y), x))) by RightForall
  //     val lhs = thenHave(∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) ==> ∀(y, y ∈ x ==> in(successor(y), x))) by Restate

  //     have((y ∈ x ==> in(successor(y), x)) |- (y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Weakening(iffinst)
  //     thenHave(∀(y, y ∈ x ==> in(successor(y), x)) |- (y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by LeftForall
  //     thenHave(∀(y, y ∈ x ==> in(successor(y), x)) |- ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by RightForall
  //     val rhs = thenHave(∀(y, y ∈ x ==> in(successor(y), x)) ==> ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) by Restate

  //     have(∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, y ∈ x ==> in(successor(y), x))) by RightIff(lhs, rhs)
  //   }

  //   have(
  //     in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) |- in(∅, x) /\ ∀(
  //       y,
  //       y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)
  //     )
  //   ) by Hypothesis
  //   thenHave(
  //     (
  //       ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, y ∈ x ==> in(successor(y), x)),
  //       in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
  //     ) |- in(∅, x) /\ ∀(y, y ∈ x ==> in(successor(y), x))
  //   ) by RightSubstIff.withParametersSimple(
  //     List((∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)), ∀(y, y ∈ x ==> in(successor(y), x)))),
  //     lambda(form, in(∅, x) /\ form)
  //   )
  //   val substituted = thenHave(
  //     (
  //       inductive(x) <=> in(∅, x) /\ ∀(y, y ∈ x ==> in(successor(y), x)),
  //       ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, y ∈ x ==> in(successor(y), x)),
  //       in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
  //     ) |- inductive(x)
  //   ) by RightSubstIff.withParametersSimple(List((inductive(x), in(∅, x) /\ ∀(y, y ∈ x ==> in(successor(y), x)))), lambda(form, form))
  //   val cut1 = have(
  //     (
  //       ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)) <=> ∀(y, y ∈ x ==> in(successor(y), x)),
  //       in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))
  //     ) |- inductive(x)
  //   ) by Cut(inductDef, substituted)
  //   val cut2 = have((in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- inductive(x)) by Cut(iffquant, cut1)

  //   thenHave((in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x))) |- ∃(x, inductive(x))) by RightExists
  //   val rhs = thenHave((∃(x, in(∅, x) /\ ∀(y, y ∈ x ==> in(union(unorderedPair(y, unorderedPair(y, y))), x)))) |- ∃(x, inductive(x))) by LeftExists

  //   have(∃(x, inductive(x))) by Cut(infinityAxiom, rhs)
  // }


  // /**
  //  * Theorem --- There exists an intersection of all inductive sets
  //  */
  // val inductiveIntersectionExistence = Theorem(
  //   ∃(z, ∀(t, t ∈ z <=> ∀(y, inductive(y) ==> t ∈ y)))
  // ) {
  //   val inductExt =
  //     have(∃(x, inductive(x)) |- ∃(z, ∀(t, t ∈ z <=> ∀(y, inductive(y) ==> t ∈ y)))) by InstPredSchema(Map(P -> lambda(x, inductive(x))))(intersectionOfPredicateClassExists)
  //   have(∃(z, ∀(t, t ∈ z <=> ∀(y, inductive(y) ==> t ∈ y)))) by Cut(inductiveSetExists, inductExt)
  // }

  // /**
  //  * Theorem --- The intersection of all inductive sets is unique
  //  */
  // val inductiveIntersectionUniqueness = Theorem(
  //   ∃!(z, ∀(t, t ∈ z <=> ∀(y, inductive(y) ==> t ∈ y)))
  // ) {
  //   val prop = ∀(y, inductive(y) ==> t ∈ y)
  //   val fprop = ∀(t, t ∈ z <=> prop)

  //   val existsRhs = have(∃(z, fprop) |- ∃!(z, fprop)) by InstPredSchema(Map(schemPred -> (t, prop)))(uniqueByExtension)
  //   val existsLhs = have(∃(z, fprop)) by Restate.from(inductiveIntersectionExistence)

  //   have(∃!(z, fprop)) by Cut(existsLhs, existsRhs)
  // }

  // /**
  //  * Natural Numbers (Inductive definition) --- The intersection of all
  //  * inductive sets is the set of natural numbers, N.
  //  */
  // val naturalsInductive = DEF() --> The(z, ∀(t, t ∈ z <=> (∀(y, inductive(y) ==> t ∈ y))))(inductiveIntersectionUniqueness)

  // /**
  //  * Theorem --- Natural numbers form an inductive set
  //  */
  // val naturalsAreInductive = Theorem(
  //   inductive(naturalsInductive)
  // ) {
  //   val defHypo = have(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- ∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x)))) by Hypothesis

  //   // emptySet is in N
  //   have(inductive(x) ==> in(∅, x)) by Weakening(inductive.definition)
  //   val inductEmpty = thenHave(∀(x, inductive(x) ==> in(∅, x))) by RightForall

  //   val defEmpty =
  //     have(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- (in(∅, z) <=> (∀(x, inductive(x) ==> in(∅, x))))) by InstantiateForall(∅)(defHypo)

  //   have(
  //     ∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- (in(∅, z) <=> (∀(x, inductive(x) ==> in(∅, x)))) /\ ∀(x, inductive(x) ==> in(∅, x))
  //   ) by RightAnd(defEmpty, inductEmpty)
  //   val baseCase = thenHave(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- in(∅, z)) by Tautology

  //   // if y in N, then succ y in N
  //   have(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- (t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x)))) by InstantiateForall(t)(defHypo)
  //   thenHave(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z |- (t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x)))) by Weakening
  //   thenHave(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z |- (∀(x, inductive(x) ==> t ∈ x))) by Tautology
  //   thenHave(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z |- (inductive(x) ==> t ∈ x)) by InstantiateForall(x)
  //   val inInductive = thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z, inductive(x)) |- t ∈ x) by Restate

  //   have(inductive(x) |- ∀(t, t ∈ x ==> in(successor(t), x))) by Weakening(inductive.definition)
  //   val inInductiveDef = thenHave(inductive(x) |- t ∈ x ==> in(successor(t), x)) by InstantiateForall(t)

  //   have((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z, inductive(x)) |- t ∈ x /\ (t ∈ x ==> in(successor(t), x))) by RightAnd(inInductive, inInductiveDef)
  //   thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) /\ t ∈ z, inductive(x)) |- in(successor(t), x)) by Tautology
  //   thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))), t ∈ z) |- inductive(x) ==> in(successor(t), x)) by Restate
  //   val succInst = thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))), t ∈ z) |- ∀(x, inductive(x) ==> in(successor(t), x))) by RightForall

  //   val nDefSucc =
  //     have(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- (in(successor(t), z) <=> (∀(x, inductive(x) ==> in(successor(t), x))))) by InstantiateForall(successor(t))(defHypo)
  //   have(
  //     (∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))), t ∈ z) |- ∀(x, inductive(x) ==> in(successor(t), x)) /\ (in(successor(t), z) <=> (∀(
  //       x,
  //       inductive(x) ==> in(successor(t), x)
  //     )))
  //   ) by RightAnd(succInst, nDefSucc)
  //   thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))), t ∈ z) |- in(successor(t), z)) by Tautology
  //   thenHave((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x)))) |- t ∈ z ==> in(successor(t), z)) by Restate
  //   val inductiveCase = thenHave(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- ∀(t, t ∈ z ==> in(successor(t), z))) by RightForall

  //   have(∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))) |- in(∅, z) /\ ∀(t, t ∈ z ==> in(successor(t), z))) by RightAnd(baseCase, inductiveCase)

  //   val form = formulaVariable
  //   val inductIff = thenHave(
  //     (∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x))), inductive(z) <=> (in(∅, z) /\ ∀(y, y ∈ z ==> in(successor(y), z)))) |- inductive(z)
  //   ) by RightSubstIff.withParametersSimple(List((inductive(z), in(∅, z) /\ ∀(y, y ∈ z ==> in(successor(y), z)))), lambda(form, form))

  //   val inductDef = have(inductive(z) <=> (in(∅, z) /\ ∀(y, y ∈ z ==> in(successor(y), z)))) by InstFunSchema(Map(x -> z))(inductive.definition)

  //   have((∀(t, t ∈ z <=> (∀(x, inductive(x) ==> t ∈ x)))) |- inductive(z)) by Cut(inductDef, inductIff)
  //   val inductExpansion =
  //     thenHave((forall(t, in(t, naturalsInductive) <=> (forall(x, inductive(x) ==> t ∈ x)))) |- inductive(naturalsInductive)) by InstFunSchema(Map(z -> naturalsInductive))

  //   have((naturalsInductive === naturalsInductive) <=> forall(t, in(t, naturalsInductive) <=> (forall(x, inductive(x) ==> t ∈ x)))) by InstantiateForall(naturalsInductive)(
  //     naturalsInductive.definition
  //   )
  //   val natDef = thenHave(forall(t, in(t, naturalsInductive) <=> forall(x, inductive(x) ==> t ∈ x))) by Restate

  //   have(inductive(naturalsInductive)) by Cut(natDef, inductExpansion)
  // }

  /*
  private val R = predicate(2)
  /**
   * Show that the restriction of a functional to a set exists.
   */
  val predicateRestrictionExists = makeTHM(
     ∃!(r, forall(x,  forall(y, pair(x, y) ∈ r <=> x ∈ A /\ in(y, A) /\ R(x, y))))
  ) {
    val z1 = fst(z)
    val z2 = snd(z)

    have ( ∃!(r, forall(z, in(z, r) <=> in(z, cartesianProduct(A, A)) /\ R(z1, z2)))) by UniqueComprehension(cartesianProduct(A, A), lambda(Seq(z, x), R(z1, z2)))
    showCurrentProof()

  }
   */

}
