package lisa.maths.settheory

import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import Relations.*
import SetTheory.*
import lisa.prooflib.BasicStepTactic.Hypothesis
import lisa.prooflib.BasicStepTactic.RightExists
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
  private val e = variable
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

  private val q = formulaVariable
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
  val functional = DEF(f) --> relation(f) /\ ∀(x, ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z))))

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
    (relation(f), ∀(x, ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z))))) |- functional(f)
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
    (functional(f), pair(x, y) ∈ f, pair(x, z) ∈ f) |- y === z
  ) {
    have(functional(f) |- ∀(x, ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z))))) by Weakening(functional.definition)
    thenHave(functional(f) |- ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z)))) by InstantiateForall(x)
    thenHave(functional(f) |- ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z))) by InstantiateForall(y)
    thenHave(thesis) by InstantiateForall(z)
  }

  /**
   * Lemma --- Subset of functions are functions
   *
   *   `functional(g), f ⊆ g |- functional(f)`
   */
  val functionalSubset = Lemma(
    (functional(g), f ⊆ g) |- functional(f)
  ) {
    have((functional(g), f ⊆ g, pair(x, y) ∈ f, pair(x, z) ∈ g) |- y === z) by Cut(subsetElim of (z := pair(x, y), x := f, y := g), functionalElim of (f := g))
    have((functional(g), f ⊆ g, pair(x, y) ∈ f, pair(x, z) ∈ f) |- y === z) by Cut(subsetElim of (z := pair(x, z), x := f, y := g), lastStep)
    thenHave((functional(g), f ⊆ g) |- pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z)) by Restate
    thenHave((functional(g), f ⊆ g) |- ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z)))) by RightForall
    thenHave((functional(g), f ⊆ g) |- ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z))))) by RightForall
    thenHave((functional(g), f ⊆ g) |- ∀(x, ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f) ==> (y === z))))) by RightForall
    have((functional(g), f ⊆ g, relation(f)) |- functional(f)) by Cut(lastStep, functionalIntro of (f := f))
    have((functional(g), f ⊆ g, relation(g)) |- functional(f)) by Cut(relationSubset of (r1 := f, r2 := g), lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  /**
    * Lemma --- A singleton pair is a function
    * 
    *   `functional({(x, y)})`
    */
  val functionalSingleton = Lemma(
    functional(singleton(pair(x, y)))
  ) {
    val pairExtensionality1 = have(pair(z, a) === pair(x, y) |- a === y) by Weakening(pairExtensionality of (a := z, b := a, c := x, d := y))
    val pairExtensionality2 = have(pair(z, b) === pair(x, y) |- b === y) by Weakening(pairExtensionality of (a := z, c := x, d := y))

    have(pair(z, a) ∈ singleton(pair(x, y)) |- a === y) by Cut(singletonElim of (y := pair(z, a), x := pair(x, y)), pairExtensionality1)
    have((pair(z, a) ∈ singleton(pair(x, y)), b === y) |- a === b) by Cut(lastStep, equalityTransitivity of (x := a, z := b))
    have((pair(z, a) ∈ singleton(pair(x, y)), pair(z, b) === pair(x, y)) |- a === b) by Cut(pairExtensionality2, lastStep)
    have((pair(z, a) ∈ singleton(pair(x, y)), pair(z, b) ∈ singleton(pair(x, y))) |- a === b) by Cut(singletonElim of (y := pair(z, b), x := pair(x, y)), lastStep)
    thenHave((pair(z, a) ∈ singleton(pair(x, y)) /\ pair(z, b) ∈ singleton(pair(x, y))) ==> (a === b)) by Restate
    thenHave(∀(b, (pair(z, a) ∈ singleton(pair(x, y)) /\ pair(z, b) ∈ singleton(pair(x, y))) ==> (a === b))) by RightForall
    thenHave(∀(a, ∀(b, (pair(z, a) ∈ singleton(pair(x, y)) /\ pair(z, b) ∈ singleton(pair(x, y))) ==> (a === b)))) by RightForall
    thenHave(∀(z, ∀(a, ∀(b, (pair(z, a) ∈ singleton(pair(x, y)) /\ pair(z, b) ∈ singleton(pair(x, y))) ==> (a === b))))) by RightForall
    have(relation(singleton(pair(x, y))) |- functional(singleton(pair(x, y)))) by Cut(lastStep, functionalIntro of (f := singleton(pair(x, y))))
    have(relationBetween(singleton(pair(x, y)), singleton(x), singleton(y)) |- functional(singleton(pair(x, y)))) by Cut(
      relationBetweenIsRelation of (r := singleton(pair(x, y)), a := singleton(x), b := singleton(y)),
      lastStep
    )
    have(thesis) by Cut(relationBetweenSingleton, lastStep)
  }

  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[dom]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (dom(f) === x)

  /**
   * Lemma --- A function with domain x has domain x
   *
   *   `functionalOver(f, x) |- dom(f) = x`
   */
  val functionalOverDomain = Lemma(
    functionalOver(f, x) |- dom(f) === x
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

  /**
   * Lemma --- Functional Over Introduction Rule
   * 
   *   `functional(f) |- functionalOver(f, dom(f))`
   */
  val functionalOverIntro = Lemma(
    functional(f) |- functionalOver(f, dom(f))
  ) {
    have(thesis) by Weakening(functionalOver.definition of (x := dom(f)))
  }


  val functionalOverSingleton = Lemma(
    functionalOver(singleton(pair(x, y)), singleton(x))
  ) {
    have(functionalOver(singleton(pair(x, y)), dom(singleton(pair(x, y))))) by Cut(functionalSingleton, functionalOverIntro of (f := singleton(pair(x, y))))
    thenHave(thesis) by Substitution.ApplyRules(relationDomainSingleton)
  }

  val functionalOverIsRelationFrom = Lemma(
    functionalOver(f, x) |- relationFrom(f, x)
  ) {
    have(functional(f) |- relationFrom(f, dom(f))) by Cut(functionalIsRelation, relationIsRelationFrom of (r := f))
    have(functionalOver(f, x) |- relationFrom(f, dom(f))) by Cut(functionalOverIsFunctional, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain)
  }

  /**
   * Function From (x to y) --- denoted  `f ∈ x → y` or `f: x → y`.
   */
  val functionFrom = DEF(f, x, y) --> functionalOver(f, x) /\ ran(f) ⊆ y

  /**
   * Lemma --- Function From Introduction Rule
   * 
   *  `functionalOver(f, x) |- functionFrom(f, x, ran(f))`
   */
  val functionFromIntro = Lemma(
    functionalOver(f, x) |- functionFrom(f, x, ran(f))
  ) {
    have(functionalOver(f, x) |- functionalOver(f, x)) by Hypothesis
    have(functionalOver(f, x) |- functionalOver(f, x) /\ ran(f) ⊆ ran(f)) by RightAnd(lastStep, subsetReflexivity of (x := ran(f)))
    thenHave(thesis) by Substitution.ApplyRules(functionFrom.definition)
  }

  val functionalIsFunctionFrom = Lemma(
    functional(f) |- functionFrom(f, dom(f), ran(f))
  ) {
    have(thesis) by Cut(functionalOverIntro, functionFromIntro of (x := dom(f)))
  }


  /**
   * Lemma --- A function between two sets is [[functional]]
   */
  val functionFromIsFunctionalOver = Lemma(
    functionFrom(f, x, y) |- functionalOver(f, x)
  ) {
    have(thesis) by Weakening(functionFrom.definition)
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
    functionFrom(f, x, y) |- (dom(f) === x)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverDomain)
  }

  /**
   * Lemma --- The range of a function is a subset of its codomain.
   *
   *   `f ∈ x → y ⊢ ran(f) ⊆ y`
   */
  val functionFromRangeSubsetCodomain = Lemma(
    functionFrom(f, x, y) |- ran(f) ⊆ y
  ) {
    have(thesis) by Weakening(functionFrom.definition)
  }

  val functionFromSupersetRange = Lemma(
    (functionFrom(f, x, y), y ⊆ z) |- functionFrom(f, x, z)
  ) {
    have((functionFrom(f, x, y), y ⊆ z) |- ran(f) ⊆ z) by Cut(functionFromRangeSubsetCodomain, subsetTransitivity of (x := ran(f)))
    have((functionFrom(f, x, y), y ⊆ z) |- functionalOver(f, x) /\ ran(f) ⊆ z) by RightAnd(functionFromIsFunctionalOver, lastStep)
    thenHave(thesis) by Substitution.ApplyRules(functionFrom.definition)
  }

  val functionFromIntroAlt = Lemma(
    (functionalOver(f, x), relationBetween(f, x, y)) |- functionFrom(f, x, y)
  ) {
    have((functionalOver(f, x), ran(f) ⊆ y) |- functionFrom(f, x, y)) by Cut(functionFromIntro, functionFromSupersetRange of (y := ran(f), z := y))
    have(thesis) by Cut(relationBetweenRange of (r := f, a := x, b := y), lastStep)
  }

  val functionFromIsRelationBetween = Lemma(
    functionFrom(f, x, y) |- relationBetween(f, x, y)
  ) {
    have(functionalOver(f, x) |- relationBetween(f, x, ran(f))) by Cut(functionalOverIsRelationFrom, relationFromToRange of (r := f, a := x))
    have((functionalOver(f, x), ran(f) ⊆ y) |- relationBetween(f, x, y)) by Cut(lastStep, relationBetweenSubsetRightDomain of (r := f, a := x, b := ran(f), d := y))
    have((functionFrom(f, x, y), ran(f) ⊆ y) |- relationBetween(f, x, y)) by Cut(functionFromIsFunctionalOver, lastStep)
    have(thesis) by Cut(functionFromRangeSubsetCodomain, lastStep)
  }

  val functionApplicationUniqueness = Lemma(
    ∃!(z, ((functional(f) /\ x ∈ dom(f)) ==> pair(x, z) ∈ f) /\ (!(functional(f) /\ x ∈ dom(f)) ==> (z === ∅)))
  ) {
    have(functional(f) |- pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z)) by Restate.from(functionalElim)
    thenHave(functional(f) |- ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z)))) by RightForall
    thenHave(functional(f) |- ∀(y, ∀(z, (pair(x, y) ∈ f /\ pair(x, z) ∈ f ==> (y === z))))) by RightForall
    have((functional(f), ∃(z, pair(x, z) ∈ f)) |- ∃!(z, pair(x, z) ∈ f)) by Cut(lastStep, existenceAndUniqueness of (P := lambda(z, pair(x, z) ∈ f)))
    have((functional(f), x ∈ dom(f)) |- ∃!(z, pair(x, z) ∈ f)) by Cut(relationDomainElim of (a := x, r := f), lastStep)
    val left = thenHave((functional(f) /\ x ∈ dom(f)) ==> ∃!(z, pair(x, z) ∈ f)) by Restate
    val right = have(!(functional(f) /\ x ∈ dom(f)) ==> ∃!(z, z === ∅)) by Weakening(existsOneEquality of (y := ∅))

    have(!(functional(f) /\ x ∈ dom(f)) ==> ∃!(z, z === ∅) |- ∃!(z, ((functional(f) /\ x ∈ dom(f)) ==> pair(x, z) ∈ f) /\ (!(functional(f) /\ x ∈ dom(f)) ==> (z === ∅)))) by Cut(left, existsOneCases of (q := functional(f) /\ x ∈ dom(f), P := lambda(z, pair(x, z) ∈ f), Q := lambda(z, z === ∅)))
    have(thesis) by Cut(right, lastStep)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) ∈ f` if it ∃ and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ x ∈ dom(f)) ==> pair(x, z) ∈ f) /\ (!(functional(f) \/ (x ∈ dom(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  val functionalApp = Lemma(
    functional(f) |- pair(a, b) ∈ f <=> (a ∈ dom(f) /\ (app(f, a) === b))
  ) {
    val appDef = have(
      (app(f, a) === b) <=> (((functional(f) /\ a ∈ dom(f)) ==> pair(a, b) ∈ f) /\ (!(functional(f) \/ (a ∈ dom(f))) ==> (b === ∅)))
    ) by InstantiateForall(b)(app.definition of (x := a))
    have((functional(f), a ∈ dom(f), pair(a, b) ∈ f) |- app(f, a) === b) by Weakening(appDef)
    have((functional(f), a ∈ dom(f), pair(a, b) ∈ f) |- (app(f, a) === b) /\ a ∈ dom(f) /\ b ∈ ran(f)) by RightAnd(
      lastStep,
      pairInRelation of (r := f, x := a, y := b)
    )
    thenHave(
      (functional(f), a ∈ dom(f) /\ b ∈ ran(f), pair(a, b) ∈ f) |- (app(f, a) === b) /\ a ∈ dom(f) /\ b ∈ ran(f)
    ) by LeftAnd
    have((functional(f), pair(a, b) ∈ f) |- (app(f, a) === b) /\ a ∈ dom(f) /\ b ∈ ran(f)) by Cut(pairInRelation of (r := f, x := a, y := b), lastStep)
    val forward = thenHave(functional(f) |- pair(a, b) ∈ f ==> ((app(f, a) === b) /\ a ∈ dom(f))) by Weakening
    val backward = have(functional(f) |- ((app(f, a) === b) /\ a ∈ dom(f)) ==> pair(a, b) ∈ f) by Weakening(appDef)
    have(thesis) by RightIff(forward, backward)
  }

  val appIntroFunctional = Lemma(
    (functional(f), a ∈ dom(f)) |- pair(a, app(f, a)) ∈ f
  ) {
    have(thesis) by Weakening(functionalApp of (b := app(f, a)))
  }

    val appIntroFunctionalOver = Lemma(
    (functionalOver(f, x), a ∈ x) |- pair(a, app(f, a)) ∈ f
  ) {
    have((functionalOver(f, x), a ∈ dom(f)) |- pair(a, app(f, a)) ∈ f) by Cut(functionalOverIsFunctional, appIntroFunctional)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain)
  }

  val appIntroFunctionFrom = Lemma(
    (functionFrom(f, x, y), a ∈ x) |- pair(a, app(f, a)) ∈ f
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, appIntroFunctionalOver)
  }

  val pairIsAppFunctional = Lemma(
    (functional(f), pair(a, b) ∈ f) |- app(f, a) === b
  ) {
    have(thesis) by Weakening(functionalApp)
  }

  val pairIsAppFunctionalOver = Lemma(
    (functionalOver(f, x), pair(a, b) ∈ f) |- app(f, a) === b
  ) {
    have(thesis) by Cut(functionalOverIsFunctional, pairIsAppFunctional)
  }

  val pairIsAppFunctionFrom = Lemma(
    (functionFrom(f, x, y), pair(a, b) ∈ f) |- app(f, a) === b
  ) {
    have(thesis) by Cut(functionFromIsFunctional, pairIsAppFunctional)
  }

  val pairReconstructionInFunctional = Lemma(
    (functional(f), p ∈ f) |- p === pair(fst(p), snd(p))
  ) {
    have(thesis) by Cut(functionalIsRelation, pairReconstructionInRelation of (r := f))
  }

  val elemOfFunctionalIsApp = Lemma(
    (functional(f), p ∈ f) |- app(f, fst(p)) === snd(p)
  ) {
    have(thesis) by Substitution.ApplyRules(pairReconstructionInFunctional)(pairIsAppFunctional of (a := fst(p), b := snd(p)))
  }

  val pairAppReconstruction = Lemma(
    (functional(f), p ∈ f) |- p === pair(fst(p), app(f, fst(p)))
  ) {
    have(thesis) by Substitution.ApplyRules(elemOfFunctionalIsApp)(pairReconstructionInFunctional)
  }

  val appSubset = Lemma(
    (functional(g), f ⊆ g, a ∈ dom(f)) |- app(g, a) === app(f, a)
  ) {
    have((functional(f), f ⊆ g, a ∈ dom(f)) |- pair(a, app(f, a)) ∈ g) by Cut(appIntroFunctional, subsetElim of (x := f, y := g, z := pair(a, app(f, a))))
    have((functional(g), functional(f), f ⊆ g, a ∈ dom(f)) |- app(f, a) === app(g, a)) by Cut(lastStep, pairIsAppFunctional of (b := app(f, a), f := g))
    have(thesis) by Cut(functionalSubset, lastStep)
  }

  val appSetUnionRight = Lemma(
    (functional(f ∪ g), a ∈ dom(f)) |- app(f ∪ g, a) === app(f, a)
  ) {
    have(thesis) by Cut(setUnionLeftSubset of (a := f, b := g), appSubset of (g := f ∪ g))
  }

  val appUnion = Lemma(
    (functional(union(z)), f ∈ z, a ∈ dom(f)) |- app(union(z), a) === app(f, a)
  ) {
    have(thesis) by Cut(subsetUnion of (x := f, y := z), appSubset of (g := union(z)))
  }

  /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalSetUnion = Lemma(
    (functional(f), functional(g), ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functional(f ∪ g)
  ) {
    val commonDomains = ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))
    have(commonDomains |- commonDomains) by Hypothesis
    thenHave((commonDomains, x ∈ dom(f), x ∈ dom(g)) |- app(f, x) === app(g, x)) by InstantiateForall(x)
    have((commonDomains, pair(x, y) ∈ f, x ∈ dom(g)) |- app(f, x) === app(g, x)) by Cut(relationDomainIntroPair of (a := x, b := y, r := f), lastStep)
    have((commonDomains, pair(x, y) ∈ f, pair(x, z) ∈ g) |- app(f, x) === app(g, x)) by Cut(relationDomainIntroPair of (a := x, b := z, r := g), lastStep)
    thenHave((commonDomains, functional(f), pair(x, y) ∈ f, pair(x, z) ∈ g) |- y === app(g, x)) by Substitution.ApplyRules(pairIsAppFunctional)
    thenHave((commonDomains, functional(f), functional(g), pair(x, y) ∈ f, pair(x, z) ∈ g) |- y === z) by Substitution.ApplyRules(pairIsAppFunctional)
    have((commonDomains, functional(f), functional(g), pair(x, y) ∈ (f ∪ g), pair(x, z) ∈ g) |- (pair(x, y) ∈ g, y === z)) by Cut(
      setUnionElim of (x := f, y := g, z := pair(x, y)),
      lastStep
    )
    val right = have((commonDomains, functional(f), functional(g), pair(x, y) ∈ (f ∪ g), pair(x, z) ∈ g) |- y === z) by Cut(lastStep, functionalElim of (f := g))
    have((commonDomains, functional(f), functional(g), pair(x, y) ∈ (f ∪ g), pair(x, z) ∈ f) |- y === z) by Substitution.ApplyRules(setUnionCommutativity)(lastStep of (f := g, g := f))
    have((commonDomains, functional(f), functional(g), pair(x, y) ∈ (f ∪ g), pair(x, z) ∈ (f ∪ g)) |- (pair(x, z) ∈ g, y === z)) by Cut(
      setUnionElim of (x := f, y := g, z := pair(x, z)),
      lastStep
    )
    have((commonDomains, functional(f), functional(g), pair(x, y) ∈ (f ∪ g), pair(x, z) ∈ (f ∪ g)) |- y === z) by Cut(lastStep, right)
    thenHave((commonDomains, functional(f), functional(g)) |- (pair(x, y) ∈ (f ∪ g) /\ pair(x, z) ∈ (f ∪ g) ==> (y === z))) by Restate
    thenHave((commonDomains, functional(f), functional(g)) |- ∀(z, (pair(x, y) ∈ (f ∪ g) /\ pair(x, z) ∈ (f ∪ g)) ==> (y === z))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- ∀(y, ∀(z, (pair(x, y) ∈ (f ∪ g) /\ pair(x, z) ∈ (f ∪ g)) ==> (y === z)))) by RightForall
    thenHave((commonDomains, functional(f), functional(g)) |- ∀(x, ∀(y, ∀(z, (pair(x, y) ∈ (f ∪ g) /\ pair(x, z) ∈ (f ∪ g)) ==> (y === z))))) by RightForall
    have((commonDomains, functional(f), functional(g), relation(f ∪ g)) |- functional(f ∪ g)) by Cut(lastStep, functionalIntro of (f := f ∪ g))
    have((commonDomains, functional(f), functional(g), relation(f), relation(g)) |- functional(f ∪ g)) by Cut(relationSetUnion of (r1 := f, r2 := g), lastStep)
    have((commonDomains, functional(f), functional(g), relation(g)) |- functional(f ∪ g)) by Cut(functionalIsRelation, lastStep)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  val functionalSubsetApp = Lemma(
    (functional(f), functional(g), dom(f) ⊆ dom(g), ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a)))) |- f ⊆ g
  ) {
    val appEq = ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a)))

    have(appEq |- appEq) by Hypothesis
    val subst = thenHave((appEq, fst(p) ∈ dom(f)) |- app(f, fst(p)) === app(g, fst(p))) by InstantiateForall(fst(p))
    
    have((functional(g), fst(p) ∈ dom(f), dom(f) ⊆ dom(g)) |- pair(fst(p), app(g, fst(p))) ∈ g) by Cut(subsetElim of (x := dom(f), y := dom(g), z := fst(p)), appIntroFunctional of (f := g, a := fst(p)))
    thenHave((functional(g), appEq, fst(p) ∈ dom(f), dom(f) ⊆ dom(g)) |- pair(fst(p), app(f, fst(p))) ∈ g) by Substitution.ApplyRules(subst)
    have((functional(g), appEq, pair(fst(p), snd(p)) ∈ f, dom(f) ⊆ dom(g)) |- pair(fst(p), app(f, fst(p))) ∈ g) by Cut(relationDomainIntroPair of (a := fst(p), b := snd(p), r := f), lastStep)
    thenHave((functional(f), functional(g), appEq, p ∈ f, dom(f) ⊆ dom(g)) |- p ∈ g) by Substitution.ApplyRules(pairReconstructionInFunctional, pairAppReconstruction)
    thenHave((functional(f), functional(g), appEq, dom(f) ⊆ dom(g)) |- p ∈ f ==> p ∈ g) by RightImplies
    thenHave((functional(f), functional(g), appEq, dom(f) ⊆ dom(g)) |- ∀(p, p ∈ f ==> p ∈ g)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := f, y := g))
  }

  val functionalEqualApp = Lemma(
    (functional(f), functional(g), dom(f) === dom(g), ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a)))) |- f === g
  ) {
    have((functional(f), functional(g), dom(f) ⊆ dom(g), ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a))), g ⊆ f) |- f === g) by Cut(functionalSubsetApp, subsetAntisymmetry of (x := f, y := g))
    have((functional(f), functional(g), dom(f) ⊆ dom(g), dom(g) ⊆ dom(f), ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a))), ∀(a, a ∈ dom(g) ==> (app(f, a) === app(g, a)))) |- f === g) by Cut(functionalSubsetApp of (f := g, g := f), lastStep)
    thenHave((functional(f), functional(g), dom(f) === dom(g), dom(f) ⊆ dom(f), ∀(a, a ∈ dom(f) ==> (app(f, a) === app(g, a)))) |- f === g) by Substitution.ApplyRules(dom(f) === dom(g))
    have(thesis) by Cut(subsetReflexivity of (x := dom(f)), lastStep)
  }

  val functionalOverApp = Lemma(
    functionalOver(f, x) |- pair(a, b) ∈ f <=> (a ∈ x /\ (app(f, a) === b))
  ) {
    have((functional(f), dom(f) === x) |- pair(a, b) ∈ f <=> (a ∈ x /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((dom(f), x)),
      lambda(x, pair(a, b) ∈ f <=> (a ∈ x /\ (app(f, a) === b)))
    )(functionalApp)
    have((functionalOver(f, x), dom(f) === x) |- pair(a, b) ∈ f <=> (a ∈ x /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val functionalOverSubsetApp = Lemma(
    (functionalOver(f, x), functionalOver(g, y), x ⊆ y, ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f ⊆ g
  ) {
    have((functional(f), functionalOver(f, x), functional(g), functionalOver(g, y), x ⊆ y, ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f ⊆ g) by Substitution.ApplyRules(functionalOverDomain, functionalOverDomain of (f := g, x := y))(functionalSubsetApp)
    have((functionalOver(f, x), functional(g), functionalOver(g, y), x ⊆ y, ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f ⊆ g) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverIsFunctional of (f := g, x := y), lastStep)
  }

  val functionalOverEqualApp = Lemma(
    (functionalOver(f, x), functionalOver(g, x), ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f === g
  ) {
    have((functional(f), functionalOver(f, x), functional(g), x === dom(g), ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f === g) by Substitution.ApplyRules(functionalOverDomain)(functionalEqualApp)
    have((functionalOver(f, x), functional(g), x === dom(g), ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f === g) by Cut(functionalOverIsFunctional, lastStep)
    have((functionalOver(f, x), functionalOver(g, x), x === dom(g), ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f === g) by Cut(functionalOverIsFunctional of (f := g), lastStep)
    thenHave((functionalOver(f, x), functionalOver(g, x), x === x, ∀(a, a ∈ x ==> (app(f, a) === app(g, a)))) |- f === g) by Substitution.ApplyRules(functionalOverDomain)
  }

  val functionOverUniqueDomain = Lemma(
    (functionalOver(f, x), functionalOver(f, y)) |- x === y
  ) {
    have((functionalOver(f, x), dom(f) === y) |- x === y) by Cut(functionalOverDomain, equalityTransitivity of (y := dom(f), z := y))
    have(thesis) by Cut(functionalOverDomain of (x := y), lastStep)
  }

  /**
   * Lemma --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val functionalOverSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ a /\ x ∈ b) ==> (app(f, x) === app(g, x)))) |- functionalOver(f ∪ g, a ∪ b)
  ) {
    have((functionalOver(f, a), functional(g), ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functional(f ∪ g)) by Cut(
      functionalOverIsFunctional of (x := a),
      functionalSetUnion
    )
    have((functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functional(f ∪ g)) by Cut(
      functionalOverIsFunctional of (f := g, x := b),
      lastStep
    )
    have(
      (functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functionalOver(
        f ∪ g,
        dom(f ∪ g)
      )
    ) by Cut(lastStep, functionalOverIntro of (f := f ∪ g, x := a ∪ b))
    thenHave(
      (functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ dom(f) /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functionalOver(f ∪ g, dom(f) ∪ dom(g))
    ) by Substitution.ApplyRules(relationDomainSetUnion of (r1 := f, r2 := g))
    thenHave(
      (functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ a /\ x ∈ dom(g)) ==> (app(f, x) === app(g, x)))) |- functionalOver(f ∪ g, a ∪ dom(g))
    ) by Substitution.ApplyRules(functionalOverDomain of (x := a))
    thenHave((functionalOver(f, a), functionalOver(g, b), ∀(x, (x ∈ a /\ x ∈ b) ==> (app(f, x) === app(g, x)))) |- functionalOver(f ∪ g, a ∪ b)) by Substitution
      .ApplyRules(functionalOverDomain of (f := g, x := b))
  }

  val functionalOverDisjointSetUnion = Lemma(
    (functionalOver(f, a), functionalOver(g, b), disjoint(a, b)) |- functionalOver(f ∪ g, a ∪ b)
  ) {
    have(disjoint(a, b) |- (x ∈ a /\ x ∈ b) ==> (app(f, x) === app(g, x))) by Weakening(disjointElim of (x := a, y := b, z := x))
    thenHave(disjoint(a, b) |- ∀(x, (x ∈ a /\ x ∈ b) ==> (app(f, x) === app(g, x)))) by RightForall
    have(thesis) by Cut(lastStep, functionalOverSetUnion)
  }


  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functional(f) |- b ∈ ran(f) <=> ∃ a ∈ dom(f). f(a) = b`
   */
  val functionalRangeMembership = Lemma(
    functional(f) |- b ∈ ran(f) <=> ∃(a, a ∈ dom(f) /\ (app(f, a) === b))
  ) {
    have(functional(f) |- ∀(a, pair(a, b) ∈ f <=> (a ∈ dom(f) /\ (app(f, a) === b)))) by RightForall(functionalApp)
    have(functional(f) |- ∃(a, pair(a, b) ∈ f) <=> ∃(a, a ∈ dom(f) /\ (app(f, a) === b))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, pair(a, b) ∈ f), Q := lambda(a, a ∈ dom(f) /\ (app(f, a) === b)))
    )
    thenHave(thesis) by Substitution.ApplyRules(relationRangeMembership of (r := f))
  }

  val functionalRangeIntro = Lemma(
    (functional(f), a ∈ dom(f)) |- app(f, a) ∈ ran(f)
  ) {
    have(a ∈ dom(f) |- a ∈ dom(f) /\ (app(f, a) === app(f, a))) by Restate
    thenHave(a ∈ dom(f) |- ∃(c, c ∈ dom(f) /\ (app(f, c) === app(f, a)))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(functionalRangeMembership of (b := app(f, a))) 
  }
  

  /**
   * Lemma --- An element is in the range of a function iff there is an element in the domain that maps to it.
   *
   *   `functionalOver(f, x) |- b ∈ ran(f) <=> ∃ a ∈ x. f(a) = b`
   */
  val functionalOverRangeMembership = Lemma(
    functionalOver(f, x) |- b ∈ ran(f) <=> ∃(a, a ∈ x /\ (app(f, a) === b))
  ) {
    have((functional(f), dom(f) === x) |- b ∈ ran(f) <=> ∃(a, a ∈ x /\ (app(f, a) === b))) by RightSubstEq.withParametersSimple(
      List((dom(f), x)),
      lambda(x, b ∈ ran(f) <=> ∃(a, a ∈ x /\ (app(f, a) === b)))
    )(functionalRangeMembership)
    have((functionalOver(f, x), dom(f) === x) |- b ∈ ran(f) <=> ∃(a, a ∈ x /\ (app(f, a) === b))) by Cut(functionalOverIsFunctional, lastStep)
    have(thesis) by Cut(functionalOverDomain, lastStep)
  }

  val functionalAppInRange = Lemma(
    (functional(f), a ∈ dom(f)) |- app(f, a) ∈ ran(f)
  ) {
    have(a ∈ dom(f) |- a ∈ dom(f) /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(a ∈ dom(f) |- ∃(z, z ∈ dom(f) /\ (app(f, z) === app(f, a)))) by RightExists
    have((functional(f), ∃(z, z ∈ dom(f) /\ (app(f, z) === app(f, a)))) |- app(f, a) ∈ ran(f)) by Weakening(functionalRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionalOverAppInRange = Lemma(
    (functionalOver(f, x), a ∈ x) |- app(f, a) ∈ ran(f)
  ) {
    have(a ∈ x |- a ∈ x /\ (app(f, a) === app(f, a))) by Restate
    val existsElem = thenHave(a ∈ x |- ∃(z, z ∈ x /\ (app(f, z) === app(f, a)))) by RightExists
    have((functionalOver(f, x), ∃(z, z ∈ x /\ (app(f, z) === app(f, a)))) |- app(f, a) ∈ ran(f)) by Weakening(functionalOverRangeMembership of (b := app(f, a)))
    have(thesis) by Cut(existsElem, lastStep)
  }

  val functionalFromAppInRange = Lemma(
    (functionFrom(f, x, y), a ∈ x) |- app(f, a) ∈ ran(f)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionalOverAppInRange)
  }

  val functionFromAppInCodomain = Lemma(
    (functionFrom(f, x, y), a ∈ x) |- app(f, a) ∈ y
  ) {
    have((functionFrom(f, x, y), a ∈ x) |- app(f, a) ∈ ran(f)) by Cut(functionFromIsFunctionalOver, functionalOverAppInRange)
    have((functionFrom(f, x, y), a ∈ x, ran(f) ⊆ y) |- app(f, a) ∈ y) by Cut(lastStep, subsetElim of (z := app(f, a), x := ran(f), y := y))
    have(thesis) by Cut(functionFromRangeSubsetCodomain, lastStep)
  }

  val compositionFunctional = Lemma(
    (functionFrom(f, x, y), functionFrom(g, y, z)) |- functional(g ∘ f)
  ) {
    have((functional(f), functional(g), pair(a, b) ∈ f, pair(a, c) ∈ f, pair(b, d) ∈ g, pair(c, e) ∈ g) |- d === e) by Substitution.ApplyRules(functionalElim of (x := a, y := b, z := c))(functionalElim of (f := g, x := c, y := d, z := e))
    thenHave((functional(f), functional(g), pair(a, b) ∈ f /\ pair(b, d) ∈ g, pair(a, c) ∈ f /\ pair(c, e) ∈ g) |- d === e) by Restate
    thenHave((functional(f), functional(g), ∃(b, pair(a, b) ∈ f /\ pair(b, d) ∈ g), pair(a, c) ∈ f /\ pair(c, e) ∈ g) |- d === e) by LeftExists
    thenHave((functional(f), functional(g), ∃(b, pair(a, b) ∈ f /\ pair(b, d) ∈ g), ∃(c, pair(a, c) ∈ f /\ pair(c, e) ∈ g)) |- d === e) by LeftExists
    have((functional(f), functional(g), pair(a, d) ∈ (g ∘ f), ∃(c, pair(a, c) ∈ f /\ pair(c, e) ∈ g)) |- d === e) by Cut(compositionElimPair of (x := a, z := d, r1 := f, r2 := g), lastStep)
    have((functional(f), functional(g), pair(a, d) ∈ (g ∘ f), pair(a, e) ∈ (g ∘ f)) |- d === e) by Cut(compositionElimPair of (x := a, z := e, r1 := f, r2 := g), lastStep)
    thenHave((functional(f), functional(g)) |- (pair(a, d) ∈ (g ∘ f) /\ pair(a, e) ∈ (g ∘ f)) ==> (d === e)) by Restate
    thenHave((functional(f), functional(g)) |- ∀(e, (pair(a, d) ∈ (g ∘ f) /\ pair(a, e) ∈ (g ∘ f)) ==> (d === e))) by RightForall
    thenHave((functional(f), functional(g)) |- ∀(d, ∀(e, (pair(a, d) ∈ (g ∘ f) /\ pair(a, e) ∈ (g ∘ f)) ==> (d === e)))) by RightForall
    thenHave((functional(f), functional(g)) |- ∀(a, ∀(d, ∀(e, (pair(a, d) ∈ (g ∘ f) /\ pair(a, e) ∈ (g ∘ f)) ==> (d === e))))) by RightForall
    have((functional(f), functional(g), relation(g ∘ f)) |- functional(g ∘ f)) by Cut(lastStep, functionalIntro of (f := g ∘ f))
    have((functionFrom(f, x, y), functional(g), relation(g ∘ f)) |- functional(g ∘ f)) by Cut(functionFromIsFunctional, lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relation(g ∘ f)) |- functional(g ∘ f)) by Cut(functionFromIsFunctional of (f := g, x := y, y := z), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g ∘ f, x, z)) |- functional(g ∘ f)) by Cut(relationBetweenIsRelation of (r := g ∘ f, a := x, b := z), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(f, x, y), relationBetween(g, y, z)) |- functional(g ∘ f)) by Cut(compositionIsRelationBetween of (r1 := f, r2 := g), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g, y, z)) |- functional(g ∘ f)) by Cut(functionFromIsRelationBetween, lastStep)
    have(thesis) by Cut(functionFromIsRelationBetween of (f := g, x := y, y := z), lastStep)
  }

  val functionCompositionDomain = Lemma(
    (functionFrom(f, x, y), functionFrom(g, y, z)) |- dom(g ∘ f) === x
  ) {
    have((functionFrom(f, x, y), a ∈ x, pair(app(f, a), app(g, app(f, a))) ∈ g) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(appIntroFunctionFrom, compositionIntro of (r1 := f, r2 := g, x := a, y := app(f, a), z := app(g, app(f, a))))
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, app(f, a) ∈ y) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(appIntroFunctionFrom of (f := g, x := y, y := z, a := app(f, a)), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(functionFromAppInCodomain, lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- a ∈ dom(g ∘ f)) by Cut(lastStep, relationDomainIntroPair of (r := g ∘ f, b := app(g, app(f, a))))
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z)) |- a ∈ x ==> a ∈ dom(g ∘ f)) by RightImplies
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z)) |- ∀(a, a ∈ x ==> a ∈ dom(g ∘ f))) by RightForall
    have((functionFrom(f, x, y), functionFrom(g, y, z)) |- x ⊆ dom(g ∘ f)) by Cut(lastStep, subsetIntro of (y := dom(g ∘ f)))
    have((functionFrom(f, x, y), functionFrom(g, y, z), dom(g ∘ f) ⊆ x) |- dom(g ∘ f) === x) by Cut(lastStep, subsetAntisymmetry of (x := dom(g ∘ f), y := x))
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g ∘ f, x, z)) |- dom(g ∘ f) === x) by Cut(relationBetweenDomain of (r := g ∘ f, a := x, b := z), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(f, x, y), relationBetween(g, y, z)) |- dom(g ∘ f) === x) by Cut(compositionIsRelationBetween of (r1 := f, r2 := g), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g, y, z)) |- dom(g ∘ f) === x) by Cut(functionFromIsRelationBetween, lastStep)
    have(thesis) by Cut(functionFromIsRelationBetween of (f := g, x := y, y := z), lastStep)
  }

  val compositionFunctionFrom = Lemma(
    (functionFrom(f, x, y), functionFrom(g, y, z)) |- functionFrom(g ∘ f, x, z)
  ) {
    have((functionFrom(f, x, y), functionFrom(g, y, z)) |- functionalOver(g ∘ f, dom(g ∘ f))) by Cut(compositionFunctional, functionalOverIntro of (f := g ∘ f))
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z)) |- functionalOver(g ∘ f, x)) by Substitution.ApplyRules(functionCompositionDomain)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g ∘ f, x, z)) |- functionFrom(g ∘ f, x, z)) by Cut(lastStep, functionFromIntroAlt of (f := g ∘ f, y := z))
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(f, x, y), relationBetween(g, y, z)) |- functionFrom(g ∘ f, x, z)) by Cut(compositionIsRelationBetween of (r1 := f, r2 := g), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), relationBetween(g, y, z)) |- functionFrom(g ∘ f, x, z)) by Cut(functionFromIsRelationBetween, lastStep)
    have(thesis) by Cut(functionFromIsRelationBetween of (f := g, x := y, y := z), lastStep)
  }

  val functionCompositionApp = Lemma(
    (functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- app(g ∘ f, a) === app(g, app(f, a))
  ) {
    have((functionFrom(f, x, y), a ∈ x, pair(app(f, a), app(g, app(f, a))) ∈ g) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(appIntroFunctionFrom, compositionIntro of (r1 := f, r2 := g, x := a, y := app(f, a), z := app(g, app(f, a))))
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, app(f, a) ∈ y) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(appIntroFunctionFrom of (f := g, x := y, y := z, a := app(f, a)), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- pair(a, app(g, app(f, a))) ∈ (g ∘ f)) by Cut(functionFromAppInCodomain, lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, functionFrom(g ∘ f, x, z)) |- app(g ∘ f, a) === app(g, app(f, a))) by Cut(lastStep, pairIsAppFunctionFrom of (f := g ∘ f, b := app(g, app(f, a)), y := z))
    have(thesis) by Cut(compositionFunctionFrom, lastStep)
  }
  /**
   * Surjective (function) --- a function `f: x → y` is surjective iff it
   * maps to every `b ∈ y` from atleast one `a ∈ x`.
   *
   * `surjective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ (ran(f) === y)

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Lemma --- Surjective function introduction rule.
   *
   *  `functionOver(f, x) |- surjective(f, x, Ran(f))`
   */
  val surjectiveIntro = Lemma(
    functionalOver(f, x) |- surjective(f, x, ran(f))
  ) {
    have(functionFrom(f, x, ran(f)) |- surjective(f, x, ran(f))) by Weakening(surjective.definition of (y := ran(f)))
    have(thesis) by Cut(functionFromIntro, lastStep)
  }

  val surjectiveBetweenDomainRange = Lemma(
    functional(f) |- surjective(f, dom(f), ran(f))
  ) {
    have(thesis) by Cut(functionalOverIntro, surjectiveIntro of (x := dom(f)))
  }

  /**
   * Lemma --- A surjective function is a function.
   *
   *   `surjective(f, x, y) |- functionFrom(f, x, y)`
   */
  val surjectiveIsFunctionFrom = Lemma(
    surjective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  val surjectiveIsFunctionalOver = Lemma(
    surjective(f, x, y) |- functionalOver(f, x)
  ) {
    have(thesis) by Cut(surjectiveIsFunctionFrom, functionFromIsFunctionalOver)
  }

  val surjectiveIsFunctional = Lemma(
    surjective(f, x, y) |- functional(f)
  ) {
    have(thesis) by Cut(surjectiveIsFunctionalOver, functionalOverIsFunctional)
  }

  /**
   * Lemma --- Surjective function elimination rule.
   *
   *  `surjective(f, x, y), b ∈ y |- ∃ a ∈ x. f(a) = b`
   */
  val surjectiveElim = Lemma(
    surjective(f, x, y) |- ran(f) === y
  ) {
    have(thesis) by Weakening(surjective.definition)
  }

  val surjectiveRangeMembership = Lemma(
    surjective(f, x, y) |- b ∈ y <=> ∃(a, a ∈ x /\ (app(f, a) === b))
  ) {
    have((surjective(f, x, y), functionalOver(f, x)) |- b ∈ y <=> ∃(a, a ∈ x /\ (app(f, a) === b))) by Substitution.ApplyRules(surjectiveElim)(functionalOverRangeMembership)
    have(thesis) by Cut(surjectiveIsFunctionalOver, lastStep)
  }

  val inverseFunctionDomain = Lemma(
    surjective(f, x, y) |- dom(inverseRelation(f)) === y
  ) {
    have(thesis) by Substitution.ApplyRules(inverseRelationDomain)(surjectiveElim)
  }

  val functionCompositionSurjective = Lemma(
    (surjective(f, x, y), surjective(g, y, z)) |- surjective(g ∘ f, x, z)
  ) {
    have((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- app(g ∘ f, a) ∈ ran(g ∘ f)) by Cut(compositionFunctionFrom, functionalFromAppInRange of (f := g ∘ f, y := z))
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x) |- app(g, app(f, a)) ∈ ran(g ∘ f)) by Substitution.ApplyRules(functionCompositionApp)
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, app(f, a) === b) |- app(g, b) ∈ ran(g ∘ f)) by Substitution.ApplyRules(app(f, a) === b)
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, app(g, b) === c, app(f, a) === b) |- c ∈ ran(g ∘ f)) by Substitution.ApplyRules(app(g, b) === c)
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x /\ (app(f, a) === b), app(g, b) === c) |- c ∈ ran(g ∘ f)) by LeftAnd
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), ∃(a, a ∈ x /\ (app(f, a) === b)), app(g, b) === c) |- c ∈ ran(g ∘ f)) by LeftExists
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), b ∈ y, app(g, b) === c) |- c ∈ ran(g ∘ f)) by Substitution.ApplyRules(surjectiveRangeMembership)
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), b ∈ y /\ (app(g, b) === c)) |- c ∈ ran(g ∘ f)) by LeftAnd
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), ∃(b, b ∈ y /\ (app(g, b) === c))) |- c ∈ ran(g ∘ f)) by LeftExists
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z), c ∈ z) |- c ∈ ran(g ∘ f)) by Substitution.ApplyRules(surjectiveRangeMembership of (f := g, x := y, y := z, b := c))
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- c ∈ z ==> c ∈ ran(g ∘ f)) by RightImplies
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- ∀(c, c ∈ z ==> c ∈ ran(g ∘ f))) by RightForall
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- z ⊆ ran(g ∘ f)) by Cut(lastStep, subsetIntro of (x := z, y := ran(g ∘ f)))
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z), ran(g ∘ f) ⊆ z) |- ran(g ∘ f) === z) by Cut(lastStep, subsetAntisymmetry of (x := ran(g ∘ f), y := z))
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z), relationBetween(g ∘ f, x, z)) |- ran(g ∘ f) === z) by Cut(relationBetweenRange of (r := g ∘ f, a := x, b := z), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z), relationBetween(f, x, y), relationBetween(g, y, z)) |- ran(g ∘ f) === z) by Cut(compositionIsRelationBetween of (r1 := f, r2 := g), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z), relationBetween(g, y, z)) |- ran(g ∘ f) === z) by Cut(functionFromIsRelationBetween, lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- ran(g ∘ f) === z) by Cut(functionFromIsRelationBetween of (f := g, x := y, y := z), lastStep)
    have((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- (ran(g ∘ f) === z) /\ functionFrom(g ∘ f, x, z)) by RightAnd(lastStep, compositionFunctionFrom)
    thenHave((functionFrom(f, x, y), functionFrom(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- surjective(g ∘ f, x, z)) by Substitution.ApplyRules(surjective.definition of (f := g ∘ f, y := z))
    have((functionFrom(f, x, y), surjective(f, x, y), surjective(g, y, z)) |- surjective(g ∘ f, x, z)) by Cut(surjectiveIsFunctionFrom of (f := g, x := y, y := z), lastStep)
    have(thesis) by Cut(surjectiveIsFunctionFrom, lastStep)
  }

  /**
   * Injective (function) --- a function `f: x → y` is injective iff it maps
   * to every `b ∈ y` from atmost one `a ∈ x`.
   *
   * `injective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b) ⟹ (∃! a ∈ x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  val injectiveIsFunctionFrom = Lemma(
    injective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Weakening(injective.definition)
  }

  val injectiveIsFunctional = Lemma(
    injective(f, x, y) |- functional(f)
  ) {
    have(thesis) by Cut(injectiveIsFunctionFrom, functionFromIsFunctional)
  }

  val injectiveIntro = Lemma(
    (functionFrom(f, x, y), ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)))) |- injective(f, x, y)
  ) {
    have(thesis) by Weakening(injective.definition)
  }

  val injectiveIntroAlt = Lemma(
    (functionFrom(f, x, y), ∀(a, ∀(b, ∀(c, (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b))))) |- injective(f, x, y)
  ) {
    val injectivityCondition = ∀(a, ∀(b, ∀(c, (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b))))
    have(injectivityCondition |- injectivityCondition) by Hypothesis
    thenHave((injectivityCondition, pair(a, app(f, a)) ∈ f, pair(b, app(f, a)) ∈ f) |- a === b) by InstantiateForall(a, b, app(f, a))
    thenHave((injectivityCondition, functionFrom(f, x, y), pair(a, app(f, a)) ∈ f, pair(b, app(f, b)) ∈ f, app(f, a) === app(f, b)) |- a === b) by Substitution.ApplyRules(app(f, a) === app(f, b))
    have((injectivityCondition, functionFrom(f, x, y), pair(a, app(f, a)) ∈ f, b ∈ x, app(f, a) === app(f, b)) |- a === b) by Cut(appIntroFunctionFrom of (a := b), lastStep)
    have((injectivityCondition, functionFrom(f, x, y), a ∈ x, b ∈ x, app(f, a) === app(f, b)) |- a === b) by Cut(appIntroFunctionFrom, lastStep)
    thenHave((injectivityCondition, functionFrom(f, x, y)) |- (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)) by Restate
    thenHave((injectivityCondition, functionFrom(f, x, y)) |- ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b))) by RightForall
    thenHave((injectivityCondition, functionFrom(f, x, y)) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)))) by RightForall
    have(thesis) by Cut(lastStep, injectiveIntro)
  }

  val injectiveElim = Lemma(
    (injective(f, x, y), a ∈ x, b ∈ x, app(f, a) === app(f, b)) |- a === b
  ) {
    have(injective(f, x, y) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)))) by Weakening(injective.definition)
    thenHave(injective(f, x, y) |- ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b))) by InstantiateForall(a)
    thenHave(thesis) by InstantiateForall(b)
  }

  val inverseFunctional = Lemma(
    functionFrom(f, x, y) |- injective(f, x, y) <=> functional(inverseRelation(f))
  ) {
    val forward = have(injective(f, x, y) ==> functional(inverseRelation(f))) subproof {
      have((injective(f, x, y), functionFrom(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ x, b ∈ x, c === c) |- a === b) by Substitution.ApplyRules(pairIsAppFunctionFrom)(injectiveElim)
      thenHave((injective(f, x, y), functionFrom(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, a ∈ dom(f), b ∈ dom(f), c === c) |- a === b) by Substitution.ApplyRules(functionFromImpliesDomainEq)
      have((injective(f, x, y), functionFrom(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, b ∈ dom(f), c === c) |- a === b) by Cut(relationDomainIntroPair of (r := f, b := c), lastStep)
      have((injective(f, x, y), functionFrom(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, c === c) |- a === b) by Cut(relationDomainIntroPair of (r := f, a := b, b := c), lastStep)
      have((injective(f, x, y), pair(a, c) ∈ f, pair(b, c) ∈ f, c === c) |- a === b) by Cut(injectiveIsFunctionFrom, lastStep)
      thenHave((injective(f, x, y), pair(c, a) ∈ inverseRelation(f), pair(b, c) ∈ f, c === c) |- a === b) by Substitution.ApplyRules(inverseRelationMembershipPair)
      thenHave((injective(f, x, y), pair(c, a) ∈ inverseRelation(f), pair(c, b) ∈ inverseRelation(f), c === c) |- a === b) by Substitution.ApplyRules(inverseRelationMembershipPair)
      thenHave(injective(f, x, y) |- (pair(c, a) ∈ inverseRelation(f) /\ pair(c, b) ∈ inverseRelation(f)) ==> (a === b)) by Restate
      thenHave(injective(f, x, y) |- ∀(b, (pair(c, a) ∈ inverseRelation(f) /\ pair(c, b) ∈ inverseRelation(f)) ==> (a === b))) by RightForall
      thenHave(injective(f, x, y) |- ∀(a, ∀(b, (pair(c, a) ∈ inverseRelation(f) /\ pair(c, b) ∈ inverseRelation(f)) ==> (a === b)))) by RightForall
      thenHave(injective(f, x, y) |- ∀(c, ∀(a, ∀(b, (pair(c, a) ∈ inverseRelation(f) /\ pair(c, b) ∈ inverseRelation(f)) ==> (a === b))))) by RightForall
      have((injective(f, x, y), relation(inverseRelation(f))) |- functional(inverseRelation(f))) by Cut(lastStep, functionalIntro of (f := inverseRelation(f)))
      thenHave((injective(f, x, y), relation(f)) |- functional(inverseRelation(f))) by Substitution.ApplyRules(inverseRelationIsRelation)
      have((injective(f, x, y), functional(f)) |- functional(inverseRelation(f))) by Cut(functionalIsRelation, lastStep)
      have(injective(f, x, y) |- functional(inverseRelation(f))) by Cut(injectiveIsFunctional, lastStep)
    }

    val backward = have(functionFrom(f, x, y) |- functional(inverseRelation(f)) ==> injective(f, x, y)) subproof {
      have((functional(inverseRelation(f)), pair(c, a) ∈ inverseRelation(f), pair(b, c) ∈ f) |- a === b) by Substitution.ApplyRules(inverseRelationMembershipPair)(functionalElim of (f := inverseRelation(f), x := c, y := a, z := b))
      thenHave((functional(inverseRelation(f)), pair(a, c) ∈ f, pair(b, c) ∈ f) |- a === b) by Substitution.ApplyRules(inverseRelationMembershipPair, app(f, a) === app(f, b))
      thenHave(functional(inverseRelation(f)) |- (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b)) by Restate
      thenHave(functional(inverseRelation(f)) |- ∀(c, (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b))) by RightForall
      thenHave(functional(inverseRelation(f)) |- ∀(b, ∀(c, (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b)))) by RightForall
      thenHave(functional(inverseRelation(f)) |- ∀(a, ∀(b, ∀(c, (pair(a, c) ∈ f /\ pair(b, c) ∈ f) ==> (a === b))))) by RightForall
      have((functionFrom(f, x, y), functional(inverseRelation(f))) |- injective(f, x, y)) by Cut(lastStep, injectiveIntroAlt)
    }
    have(thesis) by RightIff(forward, backward)
  }

  val injectiveIndependentFromCodomain = Lemma(
    (injective(f, x, y), functionFrom(f, x, z)) |- injective(f, x, z)
  ) {
    have(injective(f, x, y) |- (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)) by Restate.from(injectiveElim)
    thenHave(injective(f, x, y) |- ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b))) by RightForall
    thenHave(injective(f, x, y) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(f, a) === app(f, b))) ==> (a === b)))) by RightForall
    have(thesis) by Cut(lastStep, injectiveIntro of (y := z))
  }

  val injectiveOverRange = Lemma(
    injective(f, x, y) |- injective(f, x, ran(f))
  ) {
    have((injective(f, x, y), functionalOver(f, x)) |- injective(f, x, ran(f))) by Cut(functionFromIntro, injectiveIndependentFromCodomain of (z := ran(f)))
    have((injective(f, x, y), functionFrom(f, x, y)) |- injective(f, x, ran(f))) by Cut(functionFromIsFunctionalOver, lastStep)
    have(thesis) by Cut(injectiveIsFunctionFrom, lastStep)
  }

  val functionCompositionInjective = Lemma(
    (injective(f, x, y), injective(g, y, z)) |- injective(g ∘ f, x, z)
  ) {
    have((injective(f, x, y), injective(g, y, z), a ∈ x, b ∈ x, app(f, a) ∈ y, app(f, b) ∈ y, app(g, app(f, a)) === app(g, app(f, b))) |- a === b) by Cut(injectiveElim of (f := g, a := app(f, a), b := app(f, b), x := y, y := z), injectiveElim)
    thenHave((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, b ∈ x, app(f, a) ∈ y, app(f, b) ∈ y, app(g ∘ f, a) === app(g ∘ f, b)) |- a === b) by Substitution.ApplyRules(functionCompositionApp)
    thenHave((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, b ∈ x, app(f, a) ∈ y, app(f, b) ∈ y, app(g ∘ f, a) === app(g ∘ f, b)) |- a === b) by Substitution.ApplyRules(functionCompositionApp)
    have((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, b ∈ x, app(f, b) ∈ y, app(g ∘ f, a) === app(g ∘ f, b)) |- a === b) by Cut(functionFromAppInCodomain, lastStep)
    have((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z), a ∈ x, b ∈ x,app(g ∘ f, a) === app(g ∘ f, b)) |- a === b) by Cut(functionFromAppInCodomain of (a := b), lastStep)
    thenHave((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z)) |- (a ∈ x /\ b ∈ x /\ (app(g ∘ f, a) === app(g ∘ f, b))) ==> (a === b)) by Restate
    thenHave((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z)) |- ∀(b, (a ∈ x /\ b ∈ x /\ (app(g ∘ f, a) === app(g ∘ f, b))) ==> (a === b))) by RightForall
    thenHave((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z)) |- ∀(a, ∀(b, (a ∈ x /\ b ∈ x /\ (app(g ∘ f, a) === app(g ∘ f, b))) ==> (a === b)))) by RightForall
    have((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z), functionFrom(g ∘ f, x, z)) |- injective(g ∘ f, x, z)) by Cut(lastStep, injectiveIntro of (f := g ∘ f, y := z))
    have((injective(f, x, y), injective(g, y, z), functionFrom(f, x, y), functionFrom(g, y, z)) |- injective(g ∘ f, x, z)) by Cut(compositionFunctionFrom, lastStep)
    have((injective(f, x, y), injective(g, y, z), functionFrom(g, y, z)) |- injective(g ∘ f, x, z)) by Cut(injectiveIsFunctionFrom, lastStep)
    have((injective(f, x, y), injective(g, y, z)) |- injective(g ∘ f, x, z)) by Cut(injectiveIsFunctionFrom of (f := g, x := y, y := z), lastStep)
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

  val bijectiveIntro = Lemma(
    (injective(f, x, y), surjective(f, x, y)) |- bijective(f, x, y)
  ) {
    have(thesis) by Weakening(bijective.definition)
  }

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

  val bijectiveIsFunctionFrom = Lemma(
    bijective(f, x, y) |- functionFrom(f, x, y)
  ) {
    have(thesis) by Cut(bijectiveInjective, injectiveIsFunctionFrom)
  }
  
  val inverseFunctionFrom = Lemma(
    bijective(f, x, y) |- functionFrom(inverseRelation(f), y, x)
  ) {
    have((injective(f, x, y), functionFrom(f, x, y)) |- functionalOver(inverseRelation(f), dom(inverseRelation(f))))  by Substitution.ApplyRules(inverseFunctional)(functionalOverIntro of (f := inverseRelation(f)))
    thenHave((injective(f, x, y), surjective(f, x, y), functionFrom(f, x, y)) |- functionalOver(inverseRelation(f), y)) by Substitution.ApplyRules(inverseFunctionDomain)
    have((injective(f, x, y), surjective(f, x, y), functionFrom(f, x, y), relationBetween(inverseRelation(f), y, x)) |- functionFrom(inverseRelation(f), y, x)) by Cut(lastStep, functionFromIntroAlt of (f := inverseRelation(f), x := y, y := x))
    have((bijective(f, x, y), surjective(f, x, y), functionFrom(f, x, y), relationBetween(inverseRelation(f), y, x)) |- functionFrom(inverseRelation(f), y, x)) by Cut(bijectiveInjective, lastStep)
    have((bijective(f, x, y), functionFrom(f, x, y), relationBetween(inverseRelation(f), y, x)) |- functionFrom(inverseRelation(f), y, x)) by Cut(bijectiveSurjective, lastStep)
    thenHave((bijective(f, x, y), functionFrom(f, x, y), relationBetween(f, x, y)) |- functionFrom(inverseRelation(f), y, x)) by Substitution.ApplyRules(inverseRelationIsRelationBetween)
    have((bijective(f, x, y), functionFrom(f, x, y)) |- functionFrom(inverseRelation(f), y, x)) by Cut(functionFromIsRelationBetween, lastStep)
    have(thesis) by Cut(bijectiveIsFunctionFrom, lastStep)
  }

  val injectiveIsBijectiveOverRange = Lemma(
    injective(f, x, y) |- bijective(f, x, ran(f))
  ) {
    have((injective(f, x, ran(f)), functionalOver(f, x)) |- bijective(f, x, ran(f))) by Cut(surjectiveIntro, bijectiveIntro of (y := ran(f)))
    have((injective(f, x, y), functionalOver(f, x)) |- bijective(f, x, ran(f))) by Cut(injectiveOverRange, lastStep)
    have((injective(f, x, y), functionFrom(f, x, y)) |- bijective(f, x, ran(f))) by Cut(functionFromIsFunctionalOver, lastStep)
    have(thesis) by Cut(injectiveIsFunctionFrom, lastStep)
  }




  val inverseFunctionBijective = Lemma(
    bijective(f, x, y) <=> bijective(inverseRelation(f), y, x)
  ) {
    val forward = have(bijective(f, x, y) ==> bijective(inverseRelation(f), y, x)) subproof {
      have(functionalOver(inverseRelation(f), y) |- surjective(inverseRelation(f), y, dom(f))) by Substitution.ApplyRules(inverseRelationRange)(surjectiveIntro of (f := inverseRelation(f), x := y))
      have(functionFrom(inverseRelation(f), y, x) |- surjective(inverseRelation(f), y, dom(f))) by Cut(functionFromIsFunctionalOver of (f := inverseRelation(f), x := y, y := x), lastStep)
      thenHave((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x)) |- surjective(inverseRelation(f), y, x)) by Substitution.ApplyRules(functionFromImpliesDomainEq)
      have((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x), injective(inverseRelation(f), y, x)) |- bijective(inverseRelation(f), y, x)) by Cut(lastStep, bijectiveIntro of (f := inverseRelation(f), x := y, y := x))
      thenHave((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x), functional(inverseRelation(inverseRelation(f)))) |- bijective(inverseRelation(f), y, x)) by Substitution.ApplyRules(inverseFunctional)
      thenHave((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x), functional(f)) |- bijective(inverseRelation(f), y, x)) by Substitution.ApplyRules(inverseInverseRelation)
      have((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x)) |- bijective(inverseRelation(f), y, x)) by Cut(functionFromIsFunctional, lastStep)
      have((functionFrom(f, x, y), bijective(f, x, y)) |- bijective(inverseRelation(f), y, x)) by Cut(inverseFunctionFrom, lastStep)
      have(bijective(f, x, y) |- bijective(inverseRelation(f), y, x)) by Cut(bijectiveIsFunctionFrom, lastStep)
    }
    val backward = have(bijective(inverseRelation(f), y, x) ==> bijective(f, x, y)) by Substitution.ApplyRules(inverseInverseRelation)(forward of (f := inverseRelation(f), x := y, y := x))
    have(thesis) by RightIff(forward, backward)
  }

  val functionCompositionBijective = Lemma(
    (bijective(f, x, y), bijective(g, y, z)) |- bijective(g ∘ f, x, z)
  ) {
    have((bijective(f, x, y), injective(g, y, z)) |- injective(g ∘ f, x, z)) by Cut(bijectiveInjective, functionCompositionInjective)
    have((bijective(f, x, y), bijective(g, y, z)) |- injective(g ∘ f, x, z)) by Cut(bijectiveInjective of (f := g, x := y, y := z), lastStep)
    have((bijective(f, x, y), bijective(g, y, z), surjective(g ∘ f, x, z)) |- bijective(g ∘ f, x, z)) by Cut(lastStep, bijectiveIntro of (f := g ∘ f, y := z))
    have((bijective(f, x, y), bijective(g, y, z), surjective(f, x, y), surjective(g, y, z)) |- bijective(g ∘ f, x, z)) by Cut(functionCompositionSurjective, lastStep) 
    have((bijective(f, x, y), bijective(g, y, z), surjective(g, y, z)) |- bijective(g ∘ f, x, z)) by Cut(bijectiveSurjective, lastStep)
    have(thesis) by Cut(bijectiveSurjective of (f := g, x := y, y := z), lastStep)
  }

  val inverseRelationLeftCancel = Lemma((bijective(f, x, y), a ∈ x) |- app(inverseRelation(f), app(f, a)) === a) {
    have((functionFrom(f, x, y), a ∈ x) |- pair(app(f, a), a) ∈ inverseRelation(f)) by Substitution.ApplyRules(inverseRelationMembershipPair)(appIntroFunctionFrom)
    have((functionFrom(f, x, y), functionFrom(inverseRelation(f), y, x), a ∈ x) |- app(inverseRelation(f), app(f, a)) === a) by Cut(lastStep, pairIsAppFunctionFrom of (f := inverseRelation(f), a := app(f, a), b := a, x := y, y := x))
    have((functionFrom(f, x, y), bijective(f, x, y), a ∈ x) |- app(inverseRelation(f), app(f, a)) === a) by Cut(inverseFunctionFrom, lastStep)
    have(thesis) by Cut(bijectiveIsFunctionFrom, lastStep)
  }

  val inverseRelationRightCancel = Lemma((bijective(f, x, y), b ∈ y) |- app(f, app(inverseRelation(f), b)) === b) {
    have(thesis) by Substitution.ApplyRules(inverseInverseRelation, inverseFunctionBijective)(inverseRelationLeftCancel of (f := inverseRelation(f), x := y, y := x, a := b))
  }



  val inverseFunctionImageInDomain = Lemma(
    (bijective(f, x, y), b ∈ y) |- app(inverseRelation(f), b) ∈ x
  ) {
    have(thesis) by Cut(inverseFunctionFrom, functionFromAppInCodomain of (f := inverseRelation(f), x := y, y := x, a := b))
  }

  val relationRestrictionFunctional = Lemma(
    functional(f) |- functional(relationRestriction(f, x, y))
  ) {
    have(thesis) by Cut(relationRestrictionSubset of (r := f), functionalSubset of (f := relationRestriction(f, x, y), g := f))
  }

  val functionRestrictionDomainFunctionalOver = Lemma(
    functionalOver(f, y) |- dom(f ↾ x) === y ∩ x
  ) {
    have(thesis) by Substitution.ApplyRules(functionalOverDomain)(domainRestrictionDomain)
  }

  val functionRestrictionOnDomain = Lemma(
    functional(f) |- f ↾ dom(f) === f
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionOnDomain)
  }

  val domainRestrictionFunctional = Lemma(
    functional(f) |- functional(f ↾ x)
  ) {
    have(thesis) by Cut(domainRestrictionSubset, functionalSubset of (f := f ↾ x, g := f))
  }

  val functionRestrictionSetUnion = Lemma(
    (functional(f), functional(g)) |- f ∪ g ↾ x === (f ↾ x) ∪ (g ↾ x)
  ) {
    have((functional(f), relation(g)) |- f ∪ g ↾ x === (f ↾ x) ∪ (g ↾ x)) by Cut(functionalIsRelation, domainRestrictionSetUnion)
    have(thesis) by Cut(functionalIsRelation of (f := g), lastStep)
  }

  val functionRestrictionFunctionalOver = Lemma(
    functionalOver(f, a) |- functionalOver(f ↾ x, a ∩ x)
  ) {
    have(functional(f) |- functionalOver(f ↾ x, dom(f ↾ x))) by Cut(domainRestrictionFunctional, functionalOverIntro of (f := f ↾ x))
    have(functionalOver(f, a) |- functionalOver(f ↾ x, dom(f ↾ x))) by Cut(functionalOverIsFunctional of (x := a), lastStep)
    thenHave(functionalOver(f, a) |- functionalOver(f ↾ x, dom(f) ∩ x)) by Substitution.ApplyRules(domainRestrictionDomain)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain of (x := a))
  }

  val functionRestrictionFunctionFrom = Lemma(
    functionFrom(f, a, b) |- functionFrom(f ↾ x, a ∩ x, b)
  ) {
    have((functionalOver(f, a), relationBetween(f ↾ x, a ∩ x, b)) |- functionFrom(f ↾ x, a ∩ x, b)) by Cut(functionRestrictionFunctionalOver, functionFromIntroAlt of (f := f ↾ x, x := a ∩ x, y := b))
    have((functionalOver(f, a), relationBetween(f, a, b)) |- functionFrom(f ↾ x, a ∩ x, b)) by Cut(domainRestrictionRelationBetween of (z := x, x := a, y := b), lastStep)
    have((functionFrom(f, a, b), relationBetween(f, a, b)) |- functionFrom(f ↾ x, a ∩ x, b)) by Cut(functionFromIsFunctionalOver of (x := a, y := b), lastStep)
    have(thesis) by Cut(functionFromIsRelationBetween of (x := a, y := b), lastStep)
  }

  val functionRestrictionFunctionalOverSubset = Lemma(
    (functionalOver(f, a), x ⊆ a) |- functionalOver(f ↾ x, x)
  ) {
    have(thesis) by Substitution.ApplyRules(setIntersectionOfSubsetBackward)(functionRestrictionFunctionalOver)
  }

  val functionRestrictionApp = Lemma(
    (functional(f), a ∈ x, a ∈ dom(f)) |- app(f, a) === app(f ↾ x, a)
  ) {
    have((functional(f), pair(a, app(f, a)) ∈ (f ↾ x)) |- app(f, a) === app(f ↾ x, a)) by Cut(domainRestrictionFunctional, pairIsAppFunctional of (f := f ↾ x, b := app(f, a)))
    have((functional(f), a ∈ x, pair(a, app(f, a)) ∈ f) |- app(f, a) === app(f ↾ x, a)) by Cut(domainRestrictionIntro of (b := app(f, a)), lastStep)
    have((functional(f), a ∈ x, a ∈ dom(f)) |- app(f, a) === app(f ↾ x, a)) by Cut(appIntroFunctional, lastStep)
  }

  val functionRestrictionOverApp = Lemma(
    (functionalOver(f, y), a ∈ x, a ∈ y) |- app(f, a) === app(f ↾ x, a)
  ) {
    have((functionalOver(f, y), a ∈ x, a ∈ dom(f)) |- app(f, a) === app(f ↾ x, a)) by Cut(functionalOverIsFunctional of (x := y), functionRestrictionApp)
    thenHave(thesis) by Substitution.ApplyRules(functionalOverDomain)
  }

  val functionRestrictionFromApp = Lemma(
    (functionFrom(f, y, z), a ∈ x, a ∈ y) |- app(f, a) === app(f ↾ x, a)
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver of (x := y, y := z), functionRestrictionOverApp)
  }

  val functionRestrictionEqualApp = Lemma(
    (functionalOver(f, a), functionalOver(g, b), x ⊆ a, x ⊆ b, ∀(z, z ∈ x ==> (app(f, z) === app(g, z)))) |- f ↾ x === g ↾ x
  ) {
    have(∀(z, z ∈ x ==> (app(f, z) === app(g, z))) |- ∀(z, z ∈ x ==> (app(f, z) === app(g, z)))) by Hypothesis
    thenHave((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), z ∈ x) |- app(f, z) === app(g, z)) by InstantiateForall(z)
    thenHave((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), z ∈ x, z ∈ a) |- app(f ↾ x, z) === app(g, z)) by Substitution.ApplyRules(functionRestrictionOverApp of (a := z, y := a))
    thenHave((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), z ∈ x, z ∈ a, z ∈ b) |- app(f ↾ x, z) === app(g ↾ x, z)) by Substitution.ApplyRules(functionRestrictionOverApp of (a := z, y := b, f := g))
    have((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), z ∈ x, x ⊆ a, z ∈ b) |- app(f ↾ x, z) === app(g ↾ x, z)) by Cut(subsetElim of (y := a), lastStep)
    have((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), z ∈ x, x ⊆ a, x ⊆ b) |- app(f ↾ x, z) === app(g ↾ x, z)) by Cut(subsetElim of (y := b), lastStep)
    thenHave((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), x ⊆ a, x ⊆ b) |- z ∈ x ==> (app(f ↾ x, z) === app(g ↾ x, z))) by RightImplies
    thenHave((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), x ⊆ a, x ⊆ b) |- ∀(z, z ∈ x ==> (app(f ↾ x, z) === app(g ↾ x, z)))) by RightForall
    have((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), x ⊆ a, x ⊆ b, functionalOver(f ↾ x, x), functionalOver(g ↾ x, x)) |- f ↾ x === g ↾ x) by Cut(lastStep, functionalOverEqualApp of (f := f ↾ x, g := g ↾ x))
    have((∀(z, z ∈ x ==> (app(f, z) === app(g, z))), functionalOver(f, a), functionalOver(g, b), x ⊆ a, x ⊆ b, functionalOver(g ↾ x, x)) |- f ↾ x === g ↾ x) by Cut(functionRestrictionFunctionalOverSubset, lastStep)
    have(thesis) by Cut(functionRestrictionFunctionalOverSubset of (f := g, a := b), lastStep)
  }

  val functionRestrictionInjective = Lemma(
    injective(f, x, y) |- injective(f ↾ z, x ∩ z, y)
  ) {
    have((injective(f, x, y), a ∈ x, b ∈ x, app(f, a) === app(f, b)) |- a === b) by Restate.from(injectiveElim)
    thenHave((injective(f, x, y), functionFrom(f, x, y), a ∈ x, b ∈ x, a ∈ z, b ∈ z, app(f ↾ z, a) === app(f ↾ z, b)) |- a === b) by Substitution.ApplyRules(functionRestrictionFromApp of (x := z, y := x, z := y),functionRestrictionFromApp of (x := z, y := x, z := y, a := b))
    thenHave((injective(f, x, y), functionFrom(f, x, y), a ∈ x /\ a ∈ z, b ∈ x /\ b ∈ z, app(f ↾ z, a) === app(f ↾ z, b)) |- a === b) by Restate
    have((injective(f, x, y), functionFrom(f, x, y), a ∈ (x ∩ z), b ∈ x /\ b ∈ z, app(f ↾ z, a) === app(f ↾ z, b)) |- a === b) by Cut(setIntersectionElim of (z := a, y := z), lastStep)
    have((injective(f, x, y), functionFrom(f, x, y), a ∈ (x ∩ z), b ∈ (x ∩ z), app(f ↾ z, a) === app(f ↾ z, b)) |- a === b) by Cut(setIntersectionElim of (z := b, y := z), lastStep)
    thenHave((injective(f, x, y), functionFrom(f, x, y)) |- (a ∈ (x ∩ z) /\ b ∈ (x ∩ z) /\ (app(f ↾ z, a) === app(f ↾ z, b))) ==> (a === b)) by Restate
    thenHave((injective(f, x, y), functionFrom(f, x, y)) |- ∀(b, (a ∈ (x ∩ z) /\ b ∈ (x ∩ z) /\ (app(f ↾ z, a) === app(f ↾ z, b))) ==> (a === b))) by RightForall
    thenHave((injective(f, x, y), functionFrom(f, x, y)) |- ∀(a, ∀(b, (a ∈ (x ∩ z) /\ b ∈ (x ∩ z) /\ (app(f ↾ z, a) === app(f ↾ z, b))) ==> (a === b)))) by RightForall
    have((injective(f, x, y), functionFrom(f, x, y), functionFrom(f ↾ z, x ∩ z, y)) |- injective(f ↾ z, x ∩ z, y)) by Cut(lastStep, injectiveIntro of (x := x ∩ z, f := f ↾ z))
    have((injective(f, x, y), functionFrom(f, x, y)) |- injective(f ↾ z, x ∩ z, y)) by Cut(functionRestrictionFunctionFrom of (a := x, b := y, x := z), lastStep)
    have(thesis) by Cut(injectiveIsFunctionFrom, lastStep)
  }

  val functionRestrictionRangeMembership = Lemma(
    functional(f) |- b ∈ ran(f ↾ z) <=> ∃(a, a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))
  ) {
    have((functional(f), a ∈ dom(f) /\ a ∈ z) |- app(f, a) === app(f ↾ z, a)) by LeftAnd(functionRestrictionApp of (x := z))
    val subst = have((functional(f), a ∈ (dom(f) ∩ z)) |- app(f, a) === app(f ↾ z, a)) by Cut(setIntersectionElim of (z := a, x := dom(f), y := z), lastStep)
    have((a ∈ (dom(f) ∩ z) /\ (app(f, a) === b)) <=> (a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Restate
    thenHave((functional(f), a ∈ (dom(f) ∩ z)) |- (a ∈ (dom(f) ∩ z) /\ (app(f ↾ z, a) === b)) <=> (a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Substitution.ApplyRules(subst)
    thenHave(functional(f) |- (a ∈ (dom(f) ∩ z) /\ (app(f ↾ z, a) === b)) <=> (a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Tautology
    thenHave(functional(f) |- (a ∈ dom(f ↾ z) /\ (app(f ↾ z, a) === b)) <=> (a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Substitution.ApplyRules(domainRestrictionDomain)
    thenHave(functional(f) |- ∀(a, (a ∈ dom(f ↾ z) /\ (app(f ↾ z, a) === b)) <=> (a ∈ (dom(f) ∩ z) /\ (app(f, a) === b)))) by RightForall
    have(functional(f) |- ∃(a, a ∈ dom(f ↾ z) /\ (app(f ↾ z, a) === b)) <=> ∃(a, a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Cut(lastStep, existentialEquivalenceDistribution of (P := lambda(a, a ∈ dom(f ↾ z) /\ (app(f ↾ z, a) === b)), Q := lambda(a, a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))))
    thenHave((functional(f), functional(f ↾ z)) |- b ∈ ran(f ↾ z) <=> ∃(a, a ∈ (dom(f) ∩ z) /\ (app(f, a) === b))) by Substitution.ApplyRules(functionalRangeMembership)
    have(thesis) by Cut(domainRestrictionFunctional of (x := z), lastStep)
  }

  val functionRestrictionOverRangeMembership = Lemma(
    functionalOver(f, x) |- b ∈ ran(f ↾ z) <=> ∃(a, a ∈ (x ∩ z) /\ (app(f, a) === b))
  ) {
    have((functional(f), functionalOver(f, x)) |- b ∈ ran(f ↾ z) <=> ∃(a, a ∈ (x ∩ z) /\ (app(f, a) === b))) by Substitution.ApplyRules(functionalOverDomain)(functionRestrictionRangeMembership)
    have(thesis) by Cut(functionalOverIsFunctional, lastStep)
  }

  val functionRestrictionFromRangeMembership = Lemma(
    functionFrom(f, x, y) |- b ∈ ran(f ↾ z) <=> ∃(a, a ∈ (x ∩ z) /\ (app(f, a) === b))
  ) {
    have(thesis) by Cut(functionFromIsFunctionalOver, functionRestrictionOverRangeMembership)
  }

  val functionRestrictionSubsetDomain = Lemma(
    (functional(f), x ⊆ y) |- (f ↾ x) ⊆ (f ↾ y)
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionSubsetDomain)
  }

  val functionRestrictionTwiceSubsetInner = Lemma(
    (functional(f), x ⊆ y) |- (f ↾ x) ↾ y === f ↾ x
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionTwiceSubsetInner)
  }

  val functionRestrictionTwiceSubsetOuter = Lemma(
    (functional(f), y ⊆ x) |- (f ↾ x) ↾ y === f ↾ y
  ) {
    have(thesis) by Cut(functionalIsRelation, domainRestrictionTwiceSubsetOuter)
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
  val Sigma = DEF(x, f) --> union(f ↾ x)

  val piUniqueness = Lemma(
    ∃!(z, ∀(g, g ∈ z <=> (g ∈ 𝓟(Sigma(x, f)) /\ x ⊆ dom(g) /\ functional(g))))
  ) {
    have(∃!(z, ∀(g, g ∈ z <=> (g ∈ 𝓟(Sigma(x, f)) /\ x ⊆ dom(g) /\ functional(g))))) by UniqueComprehension(
      𝓟(Sigma(x, f)),
      lambda(z, (x ⊆ dom(z) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(z, ∀(g, g ∈ z <=> (g ∈ 𝓟(Sigma(x, f)) /\ (x ⊆ dom(g) /\ functional(g)))))(piUniqueness)

  /**
   * Lemma --- Cantor's Lemma
   *
   * There is no [[surjective]] mapping ([[functionFrom]]) a set to its [[powerSet]].
   *
   * In terms of cardinality, it asserts that a set is strictly smaller than
   * its power set.
   */
  val cantorTheorem = Lemma(
    surjective(f, x, 𝓟(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = ∀(t, t ∈ y <=> (t ∈ x /\ t ∉ app(f, t)))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- t ∈ y <=> (t ∈ x /\ t ∉ app(f, t))) by InstantiateForall(t)
    thenHave(ydef |- t ∈ y ==> t ∈ x) by Weakening
    thenHave(ydef |- ∀(t, t ∈ y ==> t ∈ x)) by RightForall
    have(ydef |- y ⊆ x) by Cut(lastStep, subsetIntro of (x := y, y := x))
    have(ydef |- y ∈ 𝓟(x)) by Cut(lastStep, powerSetIntro of (x := y, y := x))
    val existsZ = thenHave((ydef, surjective(f, x, 𝓟(x))) |- ∃(z, z ∈ x /\ (app(f, z) === y))) by Substitution.ApplyRules(surjectiveRangeMembership)

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- z ∈ y <=> (z ∈ x /\ z ∉ app(f, z))) by InstantiateForall(z)
    thenHave((ydef, app(f, z) === y) |- z ∈ app(f, z) <=> (z ∈ x /\ z ∉ app(f, z))) by Substitution.ApplyRules(app(f, z) === y)
    thenHave((ydef, z ∈ x /\ (app(f, z) === y)) |- ()) by Tautology
    thenHave((ydef, ∃(z, z ∈ x /\ (app(f, z) === y))) |- ()) by LeftExists
    have((ydef, surjective(f, x, 𝓟(x))) |- ()) by Cut(existsZ, lastStep)
    val yToContra = thenHave((∃(y, ydef), surjective(f, x, 𝓟(x))) |- ()) by LeftExists
    val yexists = have(∃(y, ydef)) by Restate.from(comprehensionSchema of (z := x, φ := lambda(t, t ∉ app(f, t))))

    have(thesis) by Cut(yexists, yToContra)
  }



  /**
   * Lemma --- Union of a Set of Functions is a Function
   *
   * Given a set `z` of functions (weakly or [[reflexive]]ly) totally ordered by
   * the [[subset]] relation on the elements' domains ([[dom]]), `∪
   * z` is [[functional]] (in particular, with domain as the union of the
   * elements' domains).
   */
  val unionOfFunctionSet = Lemma(
    (∀(f, f ∈ z ==> functional(f)), ∀(x, ∀(y, (x ∈ z /\ y ∈ z) ==> (x ⊆ y \/ (y ⊆ x))))) |- functional(union(z))
  ) {

    val allFun = ∀(f, f ∈ z ==> functional(f))
    val allSubset = ∀(x, ∀(y, (x ∈ z /\ y ∈ z) ==> (x ⊆ y \/ (y ⊆ x))))

    have(allFun |- allFun) by Hypothesis
    val allFunElim = thenHave((allFun, f ∈ z) |- functional(f)) by InstantiateForall(f)

    val relationUnion = have(allFun |- relation(union(z))) subproof { 
      have((allFun, f ∈ z) |- relation(f)) by Cut(allFunElim, functionalIsRelation)
      thenHave(allFun |- f ∈ z ==> relation(f)) by RightImplies
      thenHave(allFun |- ∀(f, f ∈ z ==> relation(f))) by RightForall
      have(thesis) by Cut(lastStep, unionOfRelationSet)
    }

    have(allSubset |- allSubset) by Hypothesis
    thenHave((allSubset, f ∈ z, g ∈ z) |- (f ⊆ g, g ⊆ f)) by InstantiateForall(g, f)
    have((allSubset, pair(w, x) ∈ f, f ∈ z, g ∈ z) |- (pair(w, x) ∈ g, g ⊆ f)) by Cut(lastStep, subsetElim of (z := pair(w, x), x := f, y := g))
    have((allSubset, pair(w, x) ∈ f, pair(w, y) ∈ g, f ∈ z, g ∈ z) |- (pair(w, x) ∈ g, pair(w, y) ∈ f)) by Cut(lastStep, subsetElim of (z := pair(w, y), x := g, y := f))
    have((allSubset, pair(w, x) ∈ f, pair(w, y) ∈ g, functional(f), f ∈ z, g ∈ z) |- (pair(w, x) ∈ g, x === y)) by Cut(lastStep, functionalElim of (x := w, y := x, z := y))
    have((allSubset, pair(w, x) ∈ f, pair(w, y) ∈ g, functional(f), functional(g), f ∈ z, g ∈ z) |- x === y) by Cut(lastStep, functionalElim of (f := g, x := w, y := x, z := y))
    have((allSubset, allFun, pair(w, x) ∈ f, pair(w, y) ∈ g, functional(g), f ∈ z, g ∈ z) |- x === y) by Cut(allFunElim, lastStep)
    have((allSubset, allFun, pair(w, x) ∈ f, pair(w, y) ∈ g, f ∈ z, g ∈ z) |- x === y) by Cut(allFunElim of (f := g), lastStep)
    thenHave((allSubset, allFun, pair(w, x) ∈ f /\ f ∈ z, pair(w, y) ∈ g /\ g ∈ z) |- x === y) by Restate
    thenHave((allSubset, allFun, ∃(f, f ∈ z /\ pair(w, x) ∈ f), pair(w, y) ∈ g /\ g ∈ z) |- x === y) by LeftExists
    thenHave((allSubset, allFun, ∃(f, f ∈ z /\ pair(w, x) ∈ f), ∃(g, g ∈ z /\ pair(w, y) ∈ g)) |- x === y) by LeftExists
    have((allSubset, allFun, pair(w, x) ∈ union(z) , ∃(g, g ∈ z /\ pair(w, y) ∈ g)) |- x === y) by Cut(unionElim of (z := pair(w, x), x := z), lastStep)
    have((allSubset, allFun, pair(w, x) ∈ union(z) , pair(w, y) ∈ union(z)) |- x === y) by Cut(unionElim of (z := pair(w, y), x := z), lastStep)
    thenHave((allSubset, allFun) |- (pair(w, x) ∈ union(z)  /\ pair(w, y) ∈ union(z)) ==> (x === y)) by Restate
    thenHave((allSubset, allFun) |- ∀(y, (pair(w, x) ∈ union(z)  /\ pair(w, y) ∈ union(z)) ==> (x === y))) by RightForall
    thenHave((allSubset, allFun) |- ∀(x, ∀(y, (pair(w, x) ∈ union(z)  /\ pair(w, y) ∈ union(z)) ==> (x === y)))) by RightForall
    thenHave((allSubset, allFun) |- ∀(w, ∀(x, ∀(y, (pair(w, x) ∈ union(z)  /\ pair(w, y) ∈ union(z)) ==> (x === y))))) by RightForall
    have((allSubset, allFun, relation(union(z))) |- functional(union(z))) by Cut(lastStep, functionalIntro of (f := union(z)))
    have(thesis) by Cut(relationUnion, lastStep)
  }

  val setOfFunctionsUniqueness = Lemma(
    ∃!(z, ∀(f, f ∈ z <=> (f ∈ 𝓟(x × y) /\ functionFrom(f, x, y))))
  ) {
    have(thesis) by UniqueComprehension(𝓟(x × y), lambda(f, functionFrom(f, x, y)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x → y` or
   * `→(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a ∈
   * x, b ∈ y`, it is a filtering on the power set of their product, i.e. `x
   * → y ⊆ PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(f, f ∈ z <=> (f ∈ 𝓟((x × y)) /\ functionFrom(f, x, y))))(setOfFunctionsUniqueness)

  extension (x: Term) {
    def |=>(y: Term): Term = setOfFunctions(x, y)
  }

  val setOfFunctionsMembership = Lemma(
    f ∈ (x |=> y) <=> functionFrom(f, x, y)
  ) {
    have(functionFrom(f, x, y) |- f ⊆ (x × y)) by Substitution.ApplyRules(relationBetween.definition)(functionFromIsRelationBetween)
    have(functionFrom(f, x, y) |- f ∈ 𝓟((x × y))) by Cut(lastStep, powerSetIntro of (x := f, y := x × y))
    val redundancy = thenHave(functionFrom(f, x, y) ==> (f ∈ 𝓟((x × y)))) by RightImplies

    have(∀(f, f ∈ (x |=> y) <=> (f ∈ 𝓟((x × y)) /\ functionFrom(f, x, y)))) by InstantiateForall((x |=> y))(setOfFunctions.definition)
    thenHave(f ∈ (x |=> y) <=> (f ∈ 𝓟((x × y)) /\ functionFrom(f, x, y))) by InstantiateForall(f)
    thenHave(functionFrom(f, x, y) ==> (f ∈ 𝓟((x × y))) |- f ∈ (x |=> y) <=> functionFrom(f, x, y)) by Tautology
    have(thesis) by Cut(redundancy, lastStep)
  }

  /**
   * Lemma --- Function spaces are monotonic on the right.
   *
   *     `y ⊆ z |- x |=> y ⊆ x |=> z`
   */
  val setOfFunctionsRightMonotonic = Lemma(y ⊆ z |- (x |=> y) ⊆ (x |=> z)) {
    have((f ∈ (x |=> y), y ⊆ z) |- f ∈ (x |=> z)) by Substitution.ApplyRules(setOfFunctionsMembership)(functionFromSupersetRange)
    thenHave(y ⊆ z |- f ∈ (x |=> y) ==> f ∈ (x |=> z)) by RightImplies
    thenHave(y ⊆ z |- ∀(f, f ∈ (x |=> y) ==> f ∈ (x |=> z))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := x |=> y, y := x |=> z))
  }

}
