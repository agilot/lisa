package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import Relations.*
import SetTheory.*
export Relations.*

object Functions extends lisa.Main {

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
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) ∧ ∀ x. (∃ y. (x, y) ∈ f) ⟹ (∃! y. (x, y) ∈ f)`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> relation(f) /\ ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))

  val functionalIsRelation = Lemma(
    functional(f) |- relation(f)
  ) {
    have(thesis) by Weakening(functional.definition)
  }

  /**
   * Lemma --- Function Introduction Rule
   * 
   *    `relation(f), ∀ x. ∀ y. ∀ z. (x, y) ∈ f ∧ (x, z) ∈ f ⟹ y = z |- functional(f)`
   */
  val functionalIntro = Lemma(
    (relation(f), ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) |- functional(f)
  ) {
    have(thesis) by Weakening(functional.definition)
  }

  /**
   * Lemma --- a function cannot have two pairs representing different values
   * for a given element.
   *
   *    `functional(f) /\ (x, y) \in f /\ (x, z) \in f /\ !(y = z) |- \bot`
   */
  val functionalElim = Lemma(
    (functional(f), in(pair(x, y), f), in(pair(x, z), f)) |- y === z
  ) {
    have(functional(f) |- ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) by Weakening(functional.definition)
    thenHave(functional(f) |- ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z)))) by InstantiateForall(x)
    thenHave(functional(f) |- ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- Subset of functions are functions
   * 
   *   `functional(g), f ⊆ g |- functional(f)`
   */
  val functionalSubset = Lemma(
    (functional(g), subset(f, g)) |- functional(f)
  ) {
    have((functional(g), subset(f, g), in(pair(x, y), f), in(pair(x, z), g)) |- y === z) by Cut(subsetElim of (z := pair(x, y), x := f, y := g), functionalElim of (f := g))
    have((functional(g), subset(f, g), in(pair(x, y), f), in(pair(x, z), f)) |- y === z) by Cut(subsetElim of (z := pair(x, z), x := f, y := g), lastStep)
    thenHave((functional(g), subset(f, g)) |- in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z)) by Restate
    thenHave((functional(g), subset(f, g)) |- forall(z, (in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z)))) by RightForall
    thenHave((functional(g), subset(f, g)) |- forall(y, forall(z, (in(pair(x, y), f) /\ in(pair(x, z), f) ==> (y === z))))) by RightForall
    thenHave((functional(g), subset(f, g)) |- ∀(x, ∀(y, ∀(z, (in(pair(x, y), f) /\ in(pair(x, z), f)) ==> (y === z))))) by RightForall
    have((functional(g), subset(f, g), relation(f)) |- functional(f)) by Cut(lastStep, functionalIntro of (f := f))
    have((functional(g), subset(f, g), relation(g)) |- functional(f)) by Cut(relationSubset of (r1 := f, r2 := g), lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  val functionalSingleton = Lemma(
    functional(singleton(pair(x, y)))
  ) {
    val pairExtensionality1 = have(pair(z, a) === pair(x, y) |- a === y) by Weakening(pairExtensionality of (a := z, b := a, c := x, d := y)) 
    val pairExtensionality2 = have(pair(z, b) === pair(x, y) |- b === y) by Weakening(pairExtensionality of (a := z, c := x, d := y))

    have(in(pair(z, a), singleton(pair(x, y))) |- a === y) by Cut(singletonElim of (y := pair(z, a), x := pair(x, y)), pairExtensionality1)
    have((in(pair(z, a), singleton(pair(x, y))), b === y) |- a === b) by Cut(lastStep, equalityTransitivity of (x := a, z := b))
    have((in(pair(z, a), singleton(pair(x, y))), pair(z, b) === pair(x, y)) |- a === b) by Cut(pairExtensionality2, lastStep)
    have((in(pair(z, a), singleton(pair(x, y))), in(pair(z, b), singleton(pair(x, y)))) |- a === b) by Cut(singletonElim of (y := pair(z, b), x := pair(x, y)), lastStep)
    thenHave((in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b)) by Restate
    thenHave(forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b))) by RightForall
    thenHave(forall(a, forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b)))) by RightForall
    thenHave(forall(z, forall(a, forall(b, (in(pair(z, a), singleton(pair(x, y))) /\ in(pair(z, b), singleton(pair(x, y)))) ==> (a === b))))) by RightForall
    have(relation(singleton(pair(x, y))) |- functional(singleton(pair(x, y)))) by Cut(lastStep, functionalIntro of (f := singleton(pair(x, y))))
    have(relationBetween(singleton(pair(x, y)), singleton(x), singleton(y)) |- functional(singleton(pair(x, y)))) by Cut(relationBetweenIsRelation of (r := singleton(pair(x, y)), a := singleton(x), b := singleton(y)), lastStep)
    have(thesis) by Cut(relationBetweenSingleton, lastStep)
  }



  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[relationDomain]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (relationDomain(f) === x)




  /**
   * Lemma --- A function with domain x has domain x
   *
   *   `functionalOver(f, x) |- dom(f) = x`
   */
  val functionalOverDomain = Lemma(
    functionalOver(f, x) |- relationDomain(f) === x
  ) {
    have(thesis) by Weakening(functionalOver.definition)
  }

  /**
   * Lemma --- A total function is partial
   *
   *  `functionalOver(f, x) |- functional(f)`
   */
  val functionalOverIsFunctional = Lemma(
    functionalOver(f, x) |- functional(f)
  ) {
    have(thesis) by Weakening(functionalOver.definition)
  }

  val functionalOverIntro = Lemma(
    functional(f) |- functionalOver(f, relationDomain(f))
  ) {
    have(thesis) by Weakening(functionalOver.definition of (x := relationDomain(f)))
  }

  val functionalOverSingleton = Lemma(
    functionalOver(singleton(pair(x, y)), singleton(x))
  ) {
    
    have(functionalOver(singleton(pair(x, y)), relationDomain(singleton(pair(x, y))))) by Cut(functionalSingleton, functionalOverIntro of (f := singleton(pair(x, y))))
    thenHave(thesis) by Substitution.ApplyRules(relationDomainSingleton)
  }



  val setOfFunctionsUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))
  ) {
    have(thesis) by UniqueComprehension(powerSet(cartesianProduct(x, y)), lambda(t, functionalOver(t, x)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x → y` or
   * `→(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a ∈
   * x, b ∈ y`, it is a filtering on the power set of their product, i.e. `x
   * → y ⊆ PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f ∈ x → y` or `f: x → y`.
   */
  val functionFrom = DEF(f, x, y) --> in(f, setOfFunctions(x, y))

  /**
   * Lemma --- A function between two sets is [[functional]]
   */
  val functionFromIsFunctionalOver = Lemma(
    functionFrom(f, x, y) |- functionalOver(f, x)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)
    thenHave(in(f, setOfFunctions(x, y)) |- functionalOver(f, x)) by Weakening
    thenHave(thesis) by Substitution.ApplyRules(functionFrom.definition)
  }

  /**
   * Lemma --- A function between two sets is [[functional]]
   */
  val functionFromIsFunctional = Lemma(
    functionFrom(f, x, y) |- functional(f)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverIsFunctional)
  }

  /**
   * Lemma --- The domain of a function from `x` to `y` is `x`.
   *
   *   `f ∈ x → y ⊢ dom(f) = x`
   */
  val functionFromImpliesDomainEq = Lemma(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverDomain)
  }

  /**
   * Lemma --- The range of a function is a subset of its codomain.
   *
   *   `f ∈ x → y ⊢ ran(f) ⊆ y`
   */
  val functionFromRangeSubsetCodomain = Lemma(
    functionFrom(f, x, y) |- subset(relationRange(f), y)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(functionFrom(f, x, y) |- ∀(z, in(z, f) ==> in(z, cartesianProduct(x, y)))) by Tautology.from(
      functionFrom.definition,
      funSetDef,
      powerAxiom of (x := f, y := cartesianProduct(x, y)),
      subsetAxiom of (x := f, y := cartesianProduct(x, y))
    )
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(pair(a, t), cartesianProduct(x, y))) by InstantiateForall(pair(a, t))
    have((functionFrom(f, x, y), in(pair(a, t), f)) |- in(a, x) /\ in(t, y)) by Cut(lastStep, cartesianProductElimPair of (b := t))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(t, y)) by Weakening
    thenHave((functionFrom(f, x, y), ∃(a, in(pair(a, t), f))) |- in(t, y)) by LeftExists
    have((functionFrom(f, x, y), in(t, relationRange(f))) |- in(t, y)) by Cut(relationRangeElim of (b := t, r := f), lastStep)
    thenHave((functionFrom(f, x, y)) |- in(t, relationRange(f)) ==> in(t, y)) by Restate
    thenHave((functionFrom(f, x, y)) |- ∀(t, in(t, relationRange(f)) ==> in(t, y))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := relationRange(f)))
  }

  val functionApplicationUniqueness = Lemma(
    ∃!(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))
  ) {
    val prem = functional(f) /\ in(x, relationDomain(f))

    // we prove thesis by two cases, first by assuming prem, and then by assuming !prem

    have((relationDomain(f) === relationDomain(f)) <=> ∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r := f)
    )
    thenHave(∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by Restate
    thenHave(in(x, relationDomain(f)) <=> (∃(y, in(pair(x, y), f)))) by InstantiateForall(x)
    val domDef = thenHave(in(x, relationDomain(f)) |- ∃(y, in(pair(x, y), f))) by Weakening

    val uniqPrem = have(functional(f) /\ in(x, relationDomain(f)) |- ∃!(z, in(pair(x, z), f))) by Sorry

    val positive = have(prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ ⊤))) subproof {
        val iff = have(prem |- (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) by Restate
        have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> in(pair(x, y), f))) by Restate
        val subst = thenHave((prem /\ ((z === y) <=> in(pair(x, y), f)), (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by RightSubstIff
          .withParametersSimple(
            List(((in(pair(x, y), f)), (prem ==> in(pair(x, y), f)))),
            lambda(h, ((z === y) <=> h))
          )

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(prem |- (!prem ==> (y === ∅)) <=> ⊤) by Restate
        val topSubst = have(
          (prem /\ ((z === y) <=> in(pair(x, y), f)), ((!prem ==> (y === ∅)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((!prem ==> (y === ∅)), ⊤)), lambda(h, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ h))))(lhs)

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification = have((prem, ∃!(z, in(pair(x, z), f))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
        have((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) by RightForall
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
        thenHave(
          (prem, ∃(z, ∀(y, ((z === y) <=> in(pair(x, y), f))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
        ) by LeftExists
        thenHave(thesis) by Restate
      }

      have(thesis) by Cut(uniqPrem, quantification)
    }

    // negative
    have((∅ === y) <=> (∅ === y)) by Restate
    thenHave(∀(y, (∅ === y) <=> (∅ === y))) by RightForall
    thenHave(∃(z, ∀(y, (z === y) <=> (∅ === y)))) by RightExists
    val emptyPrem = thenHave(∃!(z, (z === ∅))) by Restate

    val negative = have(!prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> ((!prem ==> (y === ∅)) /\ ⊤))) subproof {
        val iff = have(!prem |- ((y === ∅)) <=> (!prem ==> (y === ∅))) by Restate
        have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> (y === ∅))) by Restate
        val subst = thenHave(
          (!prem /\ ((z === y) <=> (y === ∅)), ((y === ∅)) <=> (!prem ==> (y === ∅))) |- ((z === y) <=> (!prem ==> (y === ∅)))
        ) by RightSubstIff.withParametersSimple(List((((y === ∅)), (!prem ==> (y === ∅)))), lambda(h, ((z === y) <=> h)))

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> (!prem ==> (y === ∅)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(!prem |- (prem ==> in(pair(x, y), f)) <=> ⊤) by Restate
        val topSubst = have(
          (!prem /\ ((z === y) <=> (y === ∅)), ((prem ==> in(pair(x, y), f)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((prem ==> in(pair(x, y), f)), ⊤)), lambda(h, ((z === y) <=> ((!prem ==> (y === ∅)) /\ h))))(lhs)

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification =
        have((!prem, ∃!(z, (z === ∅))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
          have((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∀(y, (z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by RightForall
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
          thenHave(
            (!prem, ∃(z, ∀(y, ((z === y) <=> (y === ∅))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
          ) by LeftExists
          thenHave(thesis) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- (prem, ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅)))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) ∈ f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  val functionalApp = Lemma(
    functional(f) |- in(pair(a, b), f) <=> (in(a, relationDomain(f)) /\ (app(f, a) === b))
  ) {
    val appDef = have(
      (app(f, a) === b) <=> (((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (b === ∅)))
    ) by InstantiateForall(b)(app.definition of (x := a))
    have((functional(f), in(a, relationDomain(f)), in(pair(a, b), f)) |- app(f, a) === b) by Weakening(appDef)
    have((functional(f), in(a, relationDomain(f)), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))) by RightAnd(
      lastStep,
      pairInRelation of (r := f, x := a, y := b)
    )
    thenHave(
      (functional(f), in(a, relationDomain(f)) /\ in(b, relationRange(f)), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))
    ) by LeftAnd
    have((functional(f), in(pair(a, b), f)) |- (app(f, a) === b) /\ in(a, relationDomain(f)) /\ in(b, relationRange(f))) by Cut(pairInRelation of (r := f, x := a, y := b), lastStep)
    val forward = thenHave(functional(f) |- in(pair(a, b), f) ==> ((app(f, a) === b) /\ in(a, relationDomain(f)))) by Weakening
    val backward = have(functional(f) |- ((app(f, a) === b) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) by Weakening(appDef)
    have(thesis) by RightIff(forward, backward)
  }

  val appIntroFunctional = Lemma(
    (functional(f), in(a, relationDomain(f))) |- in(pair(a, app(f, a)), f)
  ) {
    have(thesis) by Weakening(functionalApp of (b := app(f, a)))
  }

  val pairIsAppFunctional = Lemma(
    (functional(f), in(pair(a, b), f)) |- app(f, a) === b
  ) {
    have(thesis) by Weakening(functionalApp)
  }

  val functionalOverApp = Lemma(
    functionalOver(f, x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))
  ) {
    have((functional(f), relationDomain(f) === x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((relationDomain(f), x)),
      lambda(x, in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b)))
    )(functionalApp)
    have((functionalOver(f, x), relationDomain(f) === x) |- in(pair(a, b), f) <=> (in(a, x) /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val appIntroFunctionalOver = Lemma(
    (functionalOver(f, x), in(a, x)) |- in(pair(a, app(f, a)), f)
  ) {
    have((functionalOver(f, x), in(a, relationDomain(f))) |- in(pair(a, app(f, a)), f)) by Cut(functionalOverIsFunctional, appIntroFunctional)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain)
  }

  val pairIsAppFunctionalOver = Lemma(
    (functionalOver(f, x), in(pair(a, b), f)) |- app(f, a) === b
  ) {
    have(thesis) by Cut(functionalOverIsFunctional, pairIsAppFunctional)
  }

  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functional(f) |- b ∈ ran(f) <=> ∃ a ∈ dom(f). f(a) = b`
   */
  val functionalRangeMembership = Lemma(
    functional(f) |- in(b, relationRange(f)) <=> exists(a, in(a, relationDomain(f)) /\ (app(f, a) === b))
  ) {
    have(functional(f) |- forall(a, in(pair(a, b), f) <=> (in(a, relationDomain(f)) /\ (app(f, a) === b)))) by RightForall(functionalApp)
    have(functional(f) |- exists(a, in(pair(a, b), f)) <=> exists(a, in(a, relationDomain(f)) /\ (app(f, a) === b))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, in(pair(a, b), f)), Q := lambda(a, in(a, relationDomain(f)) /\ (app(f, a) === b)))
    )
    thenHave(thesis) by Substitution.ApplyRules(relationRangeMembership of (r := f))
  }


  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functionalOver(f, x) |- b ∈ ran(f) <=> ∃ a ∈ x. f(a) = b`
   */
  val functionalOverRangeMembership = Lemma(
    functionalOver(f, x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))
  ) {
    have((functional(f), relationDomain(f) === x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((relationDomain(f), x)),
      lambda(x, in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b)))
    )(functionalRangeMembership)
    have((functionalOver(f, x), relationDomain(f) === x) |- in(b, relationRange(f)) <=> exists(a, in(a, x) /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val functionalAppInRange = Lemma(
    (functional(f), in(a, relationDomain(f))) |- in(app(f, a), relationRange(f))
  ) {
    have(in(a, relationDomain(f)) |- in(a, relationDomain(f)) /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(in(a, relationDomain(f)) |- exists(z, in(z, relationDomain(f)) /\ (app(f, z) === app(f, a)))) by RightExists
    have((functional(f), exists(z, in(z, relationDomain(f)) /\ (app(f, z) === app(f, a)))) |- in(app(f, a), relationRange(f))) by Weakening(functionalRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionalOverAppInRange = Lemma(
    (functionalOver(f, x), in(a, x)) |- in(app(f, a), relationRange(f))
  ) {
    have(in(a, x) |- in(a, x) /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(in(a, x) |- exists(z, in(z, x) /\ (app(f, z) === app(f, a)))) by RightExists
    have((functionalOver(f, x), exists(z, in(z, x) /\ (app(f, z) === app(f, a)))) |- in(app(f, a), relationRange(f))) by Weakening(functionalOverRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionFromAppInCodomain = Lemma(
    (functionFrom(f, x, y), in(a, x)) |- in(app(f, a), y)
  ) {
    have((functionFrom(f, x, y), in(a, x)) |- in(app(f, a), relationRange(f))) by Cut(functionFromIsFunctionalOver, functionalOverAppInRange)
    have((functionFrom(f, x, y), in(a, x), subset(relationRange(f), y)) |- in(app(f, a), y)) by Cut(lastStep, subsetElim of (z := app(f, a), x := relationRange(f), y := y))
    have(thesis) by Cut(functionFromRangeSubsetCodomain, lastStep)
  }

  
  /**
   * Surjective (function) --- a function `f: x → y` is surjective iff it
   * maps to every `b ∈ y` from atleast one `a ∈ x`.
   *
   * `surjective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Lemma --- A surjective function is a function.
   *
   *   `surjective(f, x, y) |- functionFrom(f, x, y)`
   */
  val surjectiveIsFunction = Lemma(
    surjective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  /**
   * Lemma --- Surjective function introduction rule.
   *
   *  `functionFrom(f, x, y), ∀ b ∈ y. (∃ a ∈ x. f(a) = b) |- surjective(f, x, y)`
   */
  val surjectiveIntro = Lemma(
    (functionFrom(f, x, y), ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))) |- surjective(f, x, y)
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  /**
   * Lemma --- Surjective function elimination rule.
   *
   *  `surjective(f, x, y), b ∈ y |- ∃ a ∈ x. f(a) = b`
   */
  val surjectiveElim = Lemma(
    (surjective(f, x, y), in(b, y)) |- ∃(a, in(a, x) /\ (app(f, a) === b))
  ) {
    have(surjective(f, x, y) |- ∀(b, in(b, y) ==> ∃(a, in(a, x) /\ (app(f, a) === b)))) by Weakening(surjective.definition)
    thenHave(thesis) by InstantiateForall(b)
  }

  /**
   * Injective (function) --- a function `f: x → y` is injective iff it maps
   * to every `b ∈ y` from atmost one `a ∈ x`.
   *
   * `injective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b) ⟹ (∃! a ∈ x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> (∃(a, in(a, x) /\ in(pair(a, b), f)) ==> ∃!(a, in(a, x) /\ in(pair(a, b), f))))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  val injectiveIsFunction = Lemma(
    injective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Tautology.from(injective.definition)
  }

  /**
   * Bijective function --- a function `f: x → y` is bijective iff it is
   * [[injective]] and [[surjective]].
   */
  val bijective = DEF(f, x, y) --> injective(f, x, y) /\ surjective(f, x, y)

  /**
   * Invertible Function --- a function from `x` to `y` is invertible iff it is
   * [[bijective]]. See also, [[inverseFunction]]
   */
  val invertibleFunction = bijective

  val bijectiveInjective = Lemma(
    bijective(f, x, y) |- injective(f, x, y)
  ) {
    have(thesis) by Weakening(bijective.definition)
  }

  val bijectiveSurjective = Lemma(
    bijective(f, x, y) |- surjective(f, x, y)
  ) {
    have(thesis) by Weakening(bijective.definition)
  }

  val bijectiveIsFunction = Lemma(
    bijective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Cut(bijectiveInjective, injectiveIsFunction)
  }


  val inverseRelationLeftCancel = Lemma((bijective(f, x, y), in(a, x)) |- app(inverseRelation(f), app(f, a)) === a) {
    sorry
  }

  val inverseRelationRightCancel = Lemma((bijective(f, x, y), in(b, y)) |- app(f, app(inverseRelation(f), b)) === b) {
    sorry
  }

  val inverseFunctionImageInDomain = Lemma(
    (bijective(f, x, y), in(b, y)) |- in(app(inverseRelation(f), b), x)
  ) {
    sorry
  }

  val relationRestrictionFunctional = Lemma(
    functional(f) |- functional(relationRestriction(f, x, y))
  ) {
    have(thesis) by Cut(relationRestrictionSubset of (r := f), functionalSubset of (f := relationRestriction(f, x, y), g := f))
  }

  val functionRestrictionOnDomain = Lemma(
    functional(f) |- domainRestriction(f, relationDomain(f)) === f
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionOnDomain)
  }

  val domainRestrictionFunctional = Lemma(
    functional(f) |- functional(domainRestriction(f, x))
  ) {
    have(thesis) by Cut(domainRestrictionSubset, functionalSubset of (f := domainRestriction(f, x), g := f))
  }

  val functionRestrictionSetUnion = Lemma(
    (functional(f), functional(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))
  ) {
    have((functional(f), relation(g)) |- domainRestriction(setUnion(f, g), x) === setUnion(domainRestriction(f, x), domainRestriction(g, x))) by Cut(functionalIsRelation, domainRestrictionSetUnion)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  val restrictedFunctionApplication = Lemma(
    in(y, x) |- app(f, y) === app(domainRestriction(f, x), y)
  ) {
    sorry
  }


  // TODO: any subset of a functional is functional
  // TODO: a functional over something restricted to x is still functional

  /**
   * Sigma Pi Lambda
   */

  /**
   * Dependent Sum (Sigma)
   *
   * TODO: explain
   */
  val Sigma = DEF(x, f) --> union(domainRestriction(f, x))

  val piUniqueness = Lemma(
    ∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    have(∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(z, (subset(x, relationDomain(z)) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))(piUniqueness)


  /**
   * Lemma --- The range of a surjective function is equal to its codomain.
   *
   *   `surjective(f, x, y) |- y = ran(f)`
   */
  val surjectiveImpliesRangeIsCodomain = Lemma(
    surjective(f, x, y) |- y === relationRange(f)
  ) {
    have((surjective(f, x, y), functionalOver(f, x), in(b, y)) |- in(b, relationRange(f))) by Substitution.ApplyRules(functionalOverRangeMembership)(surjectiveElim)
    have((surjective(f, x, y), functionFrom(f, x, y), in(b, y)) |- in(b, relationRange(f))) by Cut(functionFromIsFunctionalOver, lastStep)
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- in(b, y) ==> in(b, relationRange(f))) by RightImplies
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- ∀(b, in(b, y) ==> in(b, relationRange(f)))) by RightForall
    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f))) by Cut(lastStep, subsetIntro of (x := y, y := relationRange(f)))
    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, relationRange(f)) /\ subset(relationRange(f), y)) by RightAnd(lastStep, functionFromRangeSubsetCodomain)
    thenHave((surjective(f, x, y), functionFrom(f, x, y)) |- y === relationRange(f)) by Substitution.ApplyRules(subsetAntisymmetry of (x := y, y := relationRange(f)))
    have(thesis) by Cut(surjectiveIsFunction, lastStep)
  }

  /**
   * Lemma --- Cantor's Lemma
   *
   * There is no [[surjective]] mapping ([[functionFrom]]) a set to its [[powerSet]].
   *
   * In terms of cardinality, it asserts that a set is strictly smaller than
   * its power set.
   */
  val cantorTheorem = Lemma(
    surjective(f, x, powerSet(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = ∀(t, in(t, y) <=> (in(t, x) /\ !in(t, app(f, t))))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(t, y) <=> (in(t, x) /\ !in(t, app(f, t)))) by InstantiateForall(t)
    thenHave(ydef |- in(t, y) ==> in(t, x)) by Weakening
    thenHave(ydef |- ∀(t, in(t, y) ==> in(t, x))) by RightForall
    andThen(Substitution.applySubst(subsetAxiom of (x := y, y := x)))
    andThen(Substitution.applySubst(powerAxiom of (x := y, y := x)))
    thenHave(ydef |- in(y, powerSet(x))) by Restate
    val existsZ = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by Cut(lastStep, surjectiveElim of (y := powerSet(x), b := y))

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by InstantiateForall(z)
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by Weakening
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, app(f, z)) <=> (in(z, x) /\ !in(z, app(f, z)))) by RightSubstEq.withParametersSimple(
      List((y, app(f, z))),
      lambda(y, in(z, y) <=> (in(z, x) /\ !in(z, app(f, z))))
    )
    thenHave((ydef, in(z, x) /\ (app(f, z) === y)) |- ()) by Tautology
    thenHave((ydef, ∃(z, in(z, x) /\ (app(f, z) === y))) |- ()) by LeftExists
    have((ydef, surjective(f, x, powerSet(x))) |- ()) by Cut(existsZ, lastStep)
    val yToContra = thenHave((∃(y, ydef), surjective(f, x, powerSet(x))) |- ()) by LeftExists
    val yexists = have(∃(y, ydef)) by Restate.from(comprehensionSchema of (z := x, φ := lambda(t, !in(t, app(f, t)))))

    have(thesis) by Cut(yexists, yToContra)
  }

  /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalSetUnion = Lemma(
    (functional(f), functional(g), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))
  ) {
    val commonDomains = forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))
    have(commonDomains |- commonDomains) by Hypothesis
    thenHave((commonDomains, in(x, relationDomain(f)), in(x, relationDomain(g))) |- app(f, x) === app(g, x)) by InstantiateForall(x)
    have((commonDomains, in(pair(x, y), f),  in(x, relationDomain(g))) |- app(f, x) === app(g, x)) by Cut(relationDomainIntro of (a := x, b := y, r := f), lastStep)
    have((commonDomains, in(pair(x, y), f),  in(pair(x, z), g)) |- app(f, x) === app(g, x)) by Cut(relationDomainIntro of (a := x, b := z, r := g), lastStep)
    thenHave((commonDomains, functional(f), in(pair(x, y), f),  in(pair(x, z), g)) |- y === app(g, x)) by Substitution.ApplyRules(pairIsAppFunctional)
    thenHave((commonDomains, functional(f), functional(g), in(pair(x, y), f),  in(pair(x, z), g)) |- y === z) by Substitution.ApplyRules(pairIsAppFunctional)
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), g)) |- (in(pair(x, y), g), y === z)) by Cut(setUnionElim of (x := f, y := g, z := pair(x, y)), lastStep)
    val right = have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), g)) |- y === z) by Cut(lastStep, functionalElim of (f := g))
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)),  in(pair(x, z), f)) |- y === z) by Substitution.ApplyRules(setUnionCommutativity)(lastStep of (f := g, g := f))
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)), in(pair(x, z), setUnion(f, g))) |- (in(pair(x, z), g), y === z)) by Cut(setUnionElim of (x := f, y := g, z := pair(x, z)), lastStep)
    have((commonDomains, functional(f), functional(g), in(pair(x, y), setUnion(f, g)), in(pair(x, z), setUnion(f, g))) |- y === z) by Cut(lastStep, right)
    thenHave((commonDomains, functional(f), functional(g)) |- (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g)) ==> (y === z))) by Restate
    thenHave((commonDomains, functional(f), functional(g)) |- forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- forall(y, forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z)))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- forall(x, forall(y, forall(z, (in(pair(x, y), setUnion(f, g)) /\ in(pair(x, z), setUnion(f, g))) ==> (y === z))))) by RightForall
    have((commonDomains, functional(f), functional(g), relation(setUnion(f, g))) |- functional(setUnion(f, g))) by Cut(lastStep, functionalIntro of (f := setUnion(f, g)))
    have((commonDomains, functional(f), functional(g), relation(f), relation(g)) |- functional(setUnion(f, g))) by Cut(relationSetUnion of (r1 := f, r2 := g), lastStep)
    have((commonDomains, functional(f), functional(g), relation(g)) |- functional(setUnion(f, g))) by Cut(functionalIsRelation, lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

    /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalOverSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, b))
  ) {
    have((functionalOver(f, a), functional(g), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))) by Cut(functionalOverIsFunctional of (x := a), functionalSetUnion)
    have((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functional(setUnion(f, g))) by Cut(functionalOverIsFunctional of (f := g, x := b), lastStep)
    have((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), relationDomain(setUnion(f, g)))) by Cut(lastStep, functionalOverIntro of (f := setUnion(f, g), x := setUnion(a, b)))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(relationDomain(f), relationDomain(g)))) by Substitution.ApplyRules(relationDomainSetUnion of (r1 := f, r2 := g))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, relationDomain(g))) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, relationDomain(g)))) by Substitution.ApplyRules(functionalOverDomain of (x := a))
    thenHave((functionalOver(f, a), functionalOver(g, b), forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) |- functionalOver(setUnion(f, g), setUnion(a, b))) by Substitution.ApplyRules(functionalOverDomain of (f :=g, x := b))
  }

  val functionalOverDisjointSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), setIntersection(a, b) === emptySet) |- functionalOver(setUnion(f, g), setUnion(a, b))
  ) {
    have((setIntersection(a, b) === emptySet, in(x, setIntersection(a, b))) |- ()) by Restate.from(setEmptyHasNoElements of (y := x, x := setIntersection(a, b)))
    have((setIntersection(a, b) === emptySet, in(x, a), in(x, b)) |- ()) by Cut(setIntersectionIntro of (t := x, x := a, y := b), lastStep)
    thenHave((setIntersection(a, b) === emptySet, in(x, a), in(x, b)) |- app(f, x) === app(g, x)) by Weakening
    thenHave(setIntersection(a, b) === emptySet |- (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x))) by Restate
    thenHave(setIntersection(a, b) === emptySet |- forall(x, (in(x, a) /\ in(x, b)) ==> (app(f, x) === app(g, x)))) by RightForall
    have(thesis) by Cut(lastStep, functionalOverSetUnion)
  }



  /**
   * Lemma --- Union of a Set of Functions is a Function
   *
   * Given a set `z` of functions (weakly or [[reflexive]]ly) totally ordered by
   * the [[subset]] relation on the elements' domains ([[relationDomain]]), `∪
   * z` is [[functional]] (in particular, with domain as the union of the
   * elements' domains).
   */
  val unionOfFunctionSet = Lemma(
    (forall(t, in(t, z) ==> functional(t)), forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))))|- functional(union(z))
  ) {
    // add assumptions
    assume(forall(t, in(t, z) ==> functional(t)), forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))))

    // assume, towards a contradiction
    assume(!functional(union(z)))

    val u = union(z)

    // begin proof ----------------

    // u is a relation

    have(in(t, z) ==> functional(t)) by InstantiateForall
    have(in(t, z) ==> relation(t)) by Tautology.from(lastStep, functional.definition of (f := t))
    thenHave(forall(t, in(t, z) ==> relation(t))) by RightForall
    val relU = have(relation(u)) by Tautology.from(lastStep, unionOfRelationSet)

    // if u is not functional, there exists a violating pair in it
    val notFun = have(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)))) by Sorry

    have((exists(f, in(f, z) /\ in(pair(x, y), f)), exists(g, in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) subproof {
      have(forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x))))) by Restate
      val subfg = thenHave((in(f, z) /\ in(g, z)) ==> (subset(f, g) \/ subset(g, f))) by InstantiateForall(f, g)

      have(forall(t, in(t, z) ==> functional(t))) by Restate
      val funF = thenHave(in(f, z) ==> functional(f)) by InstantiateForall(f)

      val fg = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(f, g)) |- ()) by Tautology.from(subsetElim of (z := pair(x, y), x := f, y := g), funF of (f := g), functionalElim of (f := g, z := w))
      val gf = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(g, f)) |- ()) by Tautology.from(subsetElim of (z := pair(x, w), x := g, y := f), funF, functionalElim of (f := f, z := w))

      have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w)) |- ()) by Tautology.from(subfg, fg, gf)
      thenHave((exists(f, in(f, z) /\ in(pair(x, y), f)), (in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) by LeftExists
      thenHave(thesis) by LeftExists
    }
    have((in(pair(x, y), u), exists(g, in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) by Cut(unionElim of (x := z, z := pair(x, y)), lastStep)
    have((in(pair(x, y), u), in(pair(x, w), u), !(y === w)) |- ()) by Cut(unionElim of (x := z, z := pair(x, w)), lastStep)
    thenHave(in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w) |- ()) by Restate
    thenHave(exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w)) |- ()) by LeftExists
    thenHave(exists(y, exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w))) |- ()) by LeftExists

    have(exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)) |- ()) by Tautology.from(lastStep, atleastTwoExist of (P := lambda(y, in(pair(x, y), u))))
    thenHave(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u))) |- ()) by LeftExists

    // contradiction
    have(thesis) by Tautology.from(lastStep, notFun)
  }

  /**
   * Lemma --- Domain of Functional Union
   *
   * If the unary union of a set is functional, then its domain is defined
   * precisely by the union of the domains of its elements.
   *
   *    functional(\cup z) |- \forall t. t \in dom(U z) <=> \exists y \in z. t
   *    \in dom(y)
   *
   * This holds, particularly, as the elements of z must be functions
   * themselves, which follows from the assumption.
   */
  val domainOfFunctionalUnion = Lemma(
    functional(union(z)) |- forall(t, in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y))))
  ) {
    assume(functional(union(z)))
    have(relation(union(z))) by Tautology.from(functional.definition of (f := union(z)))
    have(thesis) by Tautology.from(lastStep, domainOfRelationalUnion)
  }

}
