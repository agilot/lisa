package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Relations.*
import lisa.maths.settheory.Functions.*
import lisa.maths.settheory.orderings.Ordinals.*

object Recursion extends lisa.Main {

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

  // def transfiniteDefinedFunction(f : Term, d : Term) = functionalOver(f, d) /\ ∀(b, b ∈ d ==> R(f ↾ b, app(f, b)))



  val transfiniteRecursionClassFunction = Theorem(
    (classFunction(R), ordinal(a)) |- ∃!(f, functionalOver(f, a) /\ ∀(b, b < a ==> R(f ↾ b, app(f, b))))
  ) {

    def isF(f: Term, d: Term) = functionalOver(f, d) /\ ∀(b, b < d ==> R(f ↾ b, app(f, b)))

    val isFFunctionalOver = have(isF(f, d) |- functionalOver(f, d)) by Restate
    val isFFunctional = have(isF(f, d) |- functional(f)) by Cut(isFFunctionalOver, functionalOverIsFunctional of (x := d))
    val isFDomain = have(isF(f, d) |- dom(f) === d) by Cut(isFFunctionalOver, functionalOverDomain of (x := d))

    val isFAppElement = have((isF(f, d), b < d) |- R(f ↾ b, app(f, b))) subproof {
      have(∀(b, b < d ==> R(f ↾ b, app(f, b))) |-
            ∀(b, b < d ==> R(f ↾ b, app(f, b)))) by Hypothesis
      thenHave(isF(f, d) |- ∀(b, b < d ==> R(f ↾ b, app(f, b)))) by Weakening
      thenHave(thesis) by InstantiateForall(b)
    }

    val isFAppEq = have(isF(f, successor(d)) |- R(f ↾ d, app(f, d))) subproof {
      have(thesis) by Cut(inSuccessor of (a := d), isFAppElement of (b := d, d := successor(d)))
    }

    val isFSubset = have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), d <= e) |- f ⊆ g) subproof {
      have((isF(f, d), functionalOver(f, d), functionalOver(g, e), x ∈ d, x ⊆ d, x ⊆ e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y)))) |- R(g ↾ x, app(f, x))) by 
        Substitution.ApplyRules(functionRestrictionEqualApp of (a := d, b := e))(isFAppElement of (b := x))
      have((classFunction(R), isF(f, d), functionalOver(f, d), functionalOver(g, e), x ∈ d, x ⊆ d, x ⊆ e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y))), R(g ↾ x, app(g, x))) |- app(f, x) === app(g, x)) by 
        Cut(lastStep, totalClassFunctionUniqueness of (x := g ↾ x, y := app(g, x), z := app(f, x)))
      have((classFunction(R), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), x ∈ d, x ∈ e, x ⊆ d, x ⊆ e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by 
        Cut(isFAppElement of (f := g, d := e, b := x), lastStep)
      have((classFunction(R), ordinal(d), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), x ∈ d, x ∈ e, x ⊆ e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by 
        Cut(elementOfOrdinalIsSubset of (a := x, b := d), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), x ∈ d, x ∈ e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by 
        Cut(elementOfOrdinalIsSubset of (a := x, b := e), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), x ∈ d, d <= e, ∀(y, y ∈ x ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by 
        Cut(ordinalLtLeqImpliesLt of (a := x, b := d, c := e), lastStep)
  
      thenHave((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), d <= e) |- x ∈ d ==> (∀(y, y ∈ x ==> (app(f, y) === app(g, y))) ==> (app(f, x) === app(g, x)))) by Restate
      thenHave((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), d <= e) |- ∀(x, x ∈ d ==> (∀(y, y ∈ x ==> (app(f, y) === app(g, y))) ==> (app(f, x) === app(g, x))))) by RightForall
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), d <= e) |- ∀(x, x ∈ d ==> (app(f, x) ===  app(g, x)))) by 
        Cut(lastStep, transfiniteInductionOnOrdinal of (x := d, P := lambda(x, app(f, x) === app(g, x))))
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), d <= e, d ⊆ e) |- f ⊆ g) by 
        Cut(lastStep, functionalOverSubsetApp of (x := d, y := e))
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, d), functionalOver(g, e), d <= e) |- f ⊆ g) by 
        Cut(ordinalLeqImpliesSubset of (a := d, b := e), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(g, e), d <= e) |- f ⊆ g) by 
        Cut(isFFunctionalOver, lastStep)
      have(thesis) by Cut(isFFunctionalOver of (f := g, d := e), lastStep)
    }

    val isFUniqueness = have((classFunction(R), ordinal(d), isF(f, d), isF(g, d)) |- f === g) subproof {
      val forward = have((classFunction(R), ordinal(d), isF(f, d), isF(g, d)) |- f ⊆ g) by Cut(lessOrEqualLeftReflexivity of (a := d), isFSubset of (e := d))
      have((classFunction(R), ordinal(d), isF(f, d), isF(g, d), g ⊆ f) |- f === g) by Cut(forward, subsetAntisymmetry of (x := f, y := g))
      have(thesis) by Cut(forward of (f := g, g := f), lastStep) 
    }

    val isFExistenceSuccessor = have((classFunction(R), ordinal(a)) |- ∃(f, isF(f, successor(a)))) subproof {

      val sDef = ∀(f, f ∈ s <=> ∃(d, (d < a) /\ isF(f, successor(d))))
      val sElim = have((sDef, f ∈ s) |- ∃(d, (d < a) /\ isF(f, successor(d)))) subproof {
        have(sDef |- sDef) by Hypothesis
        thenHave(sDef |- f ∈ s <=> ∃(d, (d < a) /\ isF(f, successor(d)))) by InstantiateForall(f)
        thenHave(thesis) by Weakening
      }
      val sIntro = have((sDef, d < a, isF(f, successor(d))) |- f ∈ s) subproof{
        have((d < a, isF(f, successor(d))) |- (d < a) /\ isF(f, successor(d))) by Restate
        val exIntro = thenHave((d < a, isF(f, successor(d))) |- ∃(d, (d < a) /\ isF(f, successor(d)))) by RightExists

        have(sDef |- sDef) by Hypothesis
        thenHave(sDef |- f ∈ s <=> ∃(d, (d < a) /\ isF(f, successor(d)))) by InstantiateForall(f)
        thenHave((sDef, ∃(d, (d < a) /\ isF(f, successor(d)))) |- f ∈ s) by Weakening
        have(thesis) by Cut(exIntro, lastStep)
      }

      val isFExistsBelow = ∀(d, d < a ==> ∃(f, isF(f, successor(d))))

      val isFExistsBelowElim = have((isFExistsBelow, d < a) |- ∃(f, isF(f, successor(d)))) subproof {
        have(isFExistsBelow |- isFExistsBelow) by Hypothesis
        thenHave(thesis) by InstantiateForall(d)
      }

      val sExistence = have((classFunction(R), ordinal(a), isFExistsBelow) |- ∃(s, sDef)) subproof {
        have((classFunction(R), ordinal(successor(d))) |- (isF(f, successor(d)) /\ isF(g, successor(d))) ==> (f === g)) by Restate.from(isFUniqueness of (d := successor(d)))
        have((classFunction(R), ordinal(d)) |- (isF(f, successor(d)) /\ isF(g, successor(d))) ==> (f === g)) by Cut(successorIsOrdinal of (a := d), lastStep)
        thenHave((classFunction(R), ordinal(d)) |- ∀(g, (isF(f, successor(d)) /\ isF(g, successor(d))) ==> (f === g))) by RightForall
        thenHave((classFunction(R), ordinal(d)) |- ∀(f, ∀(g, isF(f, successor(d)) ==> (isF(g, successor(d)) ==> (f === g))))) by RightForall
        have((classFunction(R), ordinal(d), ∃(f, isF(f, successor(d)))) |- ∃!(f, isF(f, successor(d)))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(f, isF(f, successor(d)))))
        have((classFunction(R), ordinal(d), isFExistsBelow, d < a) |- ∃!(f, isF(f, successor(d)))) by Cut(isFExistsBelowElim, lastStep)
        have((classFunction(R), ordinal(a), isFExistsBelow, d < a) |- ∃!(f, isF(f, successor(d)))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
        thenHave((classFunction(R), ordinal(a), isFExistsBelow) |- d < a ==> ∃!(f, isF(f, successor(d)))) by RightImplies
        thenHave((classFunction(R), ordinal(a), isFExistsBelow) |- ∀(d, d < a ==> ∃!(f, isF(f, successor(d))))) by RightForall
        have(thesis) by Cut(lastStep, replacementExistence of (A := a, R := lambda((d, f), isF(f, successor(d)))))
      }

      val ihFunctional = have((classFunction(R), sDef, ordinal(a)) |- functional(union(s))) subproof {
        have((d < a) /\ isF(f, successor(d)) |- functional(f)) by Weakening(isFFunctional of (d := successor(d)))
        thenHave(∃(d, (d < a) /\ isF(f, successor(d))) |- functional(f)) by LeftExists
        have((sDef, f ∈ s) |- functional(f)) by Cut(sElim, lastStep)
        thenHave(sDef |- f ∈ s ==> functional(f)) by RightImplies
        val allFun = thenHave(sDef |- ∀(f, f ∈ s ==> functional(f))) by RightForall
        
        have((classFunction(R), ordinal(d), ordinal(successor(d)), ordinal(e), ordinal(successor(e)), isF(f, successor(d)), isF(g, successor(e)), d <= e) |- f ⊆ g) by Cut(successorPreservesLeq of (a := d, b := e), isFSubset of (d := successor(d), e := successor(e)))
        have((classFunction(R), ordinal(d), ordinal(e), ordinal(successor(e)), isF(f, successor(d)), isF(g, successor(e)), d <= e) |- f ⊆ g) by Cut(successorIsOrdinal of (a := d), lastStep)
        val isFSubsetMembership = have((classFunction(R), ordinal(d), ordinal(e), isF(f, successor(d)), isF(g, successor(e)), d <= e) |- f ⊆ g) by Cut(successorIsOrdinal of (a := e), lastStep)

        have((classFunction(R), ordinal(d), ordinal(e), isF(f, successor(d)), isF(g, successor(e))) |- (f ⊆ g, e <= d)) by Cut(ordinalCasesLeqLeq of (a := d, b := e), isFSubsetMembership)
        have((classFunction(R), ordinal(d), ordinal(e), isF(f, successor(d)), isF(g, successor(e))) |- (f ⊆ g, g ⊆ f)) by Cut(lastStep, isFSubsetMembership of (f := g, g := f, d := e, e := d))
        have((classFunction(R), ordinal(a), d < a, ordinal(e), isF(f, successor(d)), isF(g, successor(e))) |- (f ⊆ g, g ⊆ f)) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
        have((classFunction(R), ordinal(a), d < a, e < a, isF(f, successor(d)), isF(g, successor(e))) |- (f ⊆ g, g ⊆ f)) by Cut(elementsOfOrdinalsAreOrdinals of (b := e), lastStep)
        thenHave((classFunction(R), ordinal(a), (d < a) /\ isF(f, successor(d)), (e < a) /\ isF(g, successor(e))) |- (f ⊆ g, g ⊆ f)) by Restate
        thenHave((classFunction(R), ordinal(a), ∃(d, (d < a) /\ isF(f, successor(d))), (e < a) /\ isF(g, successor(e))) |- (f ⊆ g, g ⊆ f)) by LeftExists
        thenHave((classFunction(R), ordinal(a), ∃(d, (d < a) /\ isF(f, successor(d))), ∃(e, (e < a) /\ isF(g, successor(e)))) |- (f ⊆ g, g ⊆ f)) by LeftExists
        have((classFunction(R), sDef, ordinal(a), f ∈ s, ∃(e, (e < a) /\ isF(g, successor(e)))) |- (f ⊆ g, g ⊆ f)) by Cut(sElim, lastStep)
        have((classFunction(R), sDef, ordinal(a), f ∈ s, g ∈ s) |- (f ⊆ g, g ⊆ f)) by Cut(sElim of (f := g), lastStep)
        thenHave((classFunction(R), sDef, ordinal(a)) |- (f ∈ s /\ g ∈ s) ==> (f ⊆ g \/ (g ⊆ f))) by Restate
        thenHave((classFunction(R), sDef, ordinal(a)) |- ∀(g, f ∈ s /\ g ∈ s ==> (f ⊆ g \/ (g ⊆ f)))) by RightForall
        thenHave((classFunction(R), sDef, ordinal(a)) |- ∀(f, ∀(g, f ∈ s /\ g ∈ s ==> (f ⊆ g \/ (g ⊆ f))))) by RightForall
        have((classFunction(R), ∀(f, f ∈ s ==> functional(f)), sDef, ordinal(a)) |- functional(union(s))) by Cut(lastStep, unionOfFunctionSet of (z := s))
        have(thesis) by Cut(allFun, lastStep)
      }

      val ihDomain = have((isFExistsBelow, sDef, ordinal(a)) |- dom(union(s)) === a) subproof {
        val forward = have((sDef, ordinal(a)) |- d ∈ dom(union(s)) ==> d < a) subproof {
          have(d < successor(e) |- d <= e) by Restate.from(inSuccessorLeq of (a := e, b := d))
          have((d < successor(e), e < a, ordinal(a)) |- d < a) by Cut(lastStep, ordinalLeqLtImpliesLt of (a := d, b := e, c := a))
          thenHave((d ∈ dom(f), e < a, ordinal(a), isF(f, successor(e))) |- d < a) by Substitution.ApplyRules(isFDomain of (d := successor(e)))
          thenHave((d ∈ dom(f), ordinal(a), (e < a) /\ isF(f, successor(e))) |- d < a) by LeftAnd
          thenHave((d ∈ dom(f), ordinal(a), ∃(e, (e < a) /\ isF(f, successor(e)))) |- d < a) by LeftExists
          have((sDef, d ∈ dom(f), ordinal(a), f ∈ s) |- d < a) by Cut(sElim, lastStep)
          thenHave((sDef, d ∈ dom(f) /\ f ∈ s, ordinal(a)) |- d < a) by LeftAnd
          thenHave((sDef, ∃(f, d ∈ dom(f) /\ f ∈ s), ordinal(a)) |- d < a) by LeftExists
          thenHave((sDef, d ∈ dom(union(s)), ordinal(a)) |- d < a) by Substitution.ApplyRules(relationDomainUnion of (t := d, z := s))
        } 
        val backward = have((isFExistsBelow, sDef) |- d < a ==> d ∈ dom(union(s))) subproof {
          have(isF(f, successor(d)) |- d ∈ dom(f)) by Substitution.ApplyRules(isFDomain)(inSuccessor of (a := d))
          have((sDef, d < a, isF(f, successor(d))) |- d ∈ dom(f) /\ f ∈ s) by RightAnd(sIntro, lastStep)
          thenHave((sDef, d < a, isF(f, successor(d))) |- ∃(f, d ∈ dom(f) /\ f ∈ s)) by RightExists
          thenHave((sDef, d < a, isF(f, successor(d))) |- d ∈ dom(union(s))) by Substitution.ApplyRules(relationDomainUnion of (t := d, z := s))
          thenHave((sDef, d < a, ∃(f, isF(f, successor(d)))) |- d ∈ dom(union(s))) by LeftExists
          have((sDef, d < a, isFExistsBelow) |- d ∈ dom(union(s))) by Cut(isFExistsBelowElim, lastStep)
        }
        have((isFExistsBelow, sDef, ordinal(a)) |- d < a <=> d ∈ dom(union(s))) by RightIff(forward, backward)
        thenHave((isFExistsBelow, sDef, ordinal(a)) |- ∀(d, d < a <=> d ∈ dom(union(s)))) by RightForall
        have(thesis) by Cut(lastStep, equalityIntro of (x := dom(union(s)), y := a))
      }

      val ihFunctionalOver = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(union(s), a)) subproof {
        have((isFExistsBelow, classFunction(R), sDef, ordinal(a), functional(union(s))) |- functionalOver(union(s), a)) by Substitution.ApplyRules(ihDomain)(functionalOverIntro of (f := union(s)))
        have(thesis) by Cut(ihFunctional, lastStep)
      }

      val newF = union(s) ∪ singleton(pair(a, b))

      val newFFunctionalOver = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(newF, successor(a))) subproof {
        have((functionalOver(union(s), a), functionalOver(singleton(pair(a, b)), singleton(a))) |- functionalOver(newF, a ∪ singleton(a))) by 
          Cut(singletonDisjointSelf of (x := a), functionalOverDisjointSetUnion of (f := union(s), g := singleton(pair(a, b)), b := singleton(a)))
        have((classFunction(R), isFExistsBelow, sDef, ordinal(a), functionalOver(singleton(pair(a, b)), singleton(a))) |- functionalOver(newF, a ∪ singleton(a))) by 
          Cut(ihFunctionalOver, lastStep)
        have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(newF, a ∪ singleton(a))) by Cut(functionalOverSingleton of (x := a, y := b), lastStep)
        thenHave(thesis) by Substitution.ApplyRules(successor.shortDefinition)
      }

      val newFFunctional = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functional(newF)) by Cut(newFFunctionalOver, functionalOverIsFunctional of (f := newF, x := successor(a)))

      val newFApp = have((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- ∀(d, d ∈ successor(a) ==> R(newF ↾ d, app(newF, d)))) subproof {
        val newFAppEq = have((classFunction(R), isFExistsBelow, sDef, ordinal(a), d === a, R(union(s), b)) |- R(newF ↾ d, app(newF, d))) subproof {
          
          val newFRestr = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- newF ↾ a === union(s)) subproof {
            have((disjoint(dom(singleton(pair(a, b))), a), functional(union(s)), functional(singleton(pair(a, b)))) |- newF ↾ a === union(s) ↾ a ∪ ∅) by 
              Substitution.ApplyRules(domainRestrictionDisjoint of (f := singleton(pair(a, b)), x := a))(functionRestrictionSetUnion of (f := union(s), g := singleton(pair(a, b)), x := a))
            have((disjoint(dom(singleton(pair(a, b))), a), functional(union(s))) |- newF ↾ a === union(s) ↾ a ∪ ∅) by
              Cut(functionalSingleton of (x := a, y := b), lastStep)
            thenHave((disjoint(singleton(a), a), functional(union(s))) |- newF ↾ a === union(s) ↾ a ∪ ∅) by Substitution.ApplyRules(relationDomainSingleton of (x := a))
            thenHave((disjoint(a, singleton(a)), functional(union(s))) |- newF ↾ a === union(s) ↾ a ∪ ∅) by Substitution.ApplyRules(disjointSymmetry of (x := singleton(a), y := a))
            have(functional(union(s)) |- newF ↾ a === union(s) ↾ a ∪ ∅) by Cut(singletonDisjointSelf of (x := a), lastStep)
            thenHave(functional(union(s)) |- newF ↾ a === union(s) ↾ a) by Substitution.ApplyRules(setUnionRightEmpty of (a := union(s) ↾ a))
            thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), functional(union(s))) |- newF ↾ a === union(s) ↾ dom(union(s))) by Substitution.ApplyRules(ihDomain)
            thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), functional(union(s))) |- newF ↾ a === union(s)) by Substitution.ApplyRules(functionRestrictionOnDomain of (f := union(s), x := a))
            have(thesis) by Cut(ihFunctional, lastStep)
          }

          have(R(union(s), b) |- R(union(s), b)) by Hypothesis
          thenHave((classFunction(R), sDef, isFExistsBelow, ordinal(a), R(union(s), b)) |- R(newF ↾ a, b)) by Substitution.ApplyRules(newFRestr)
          thenHave((classFunction(R), sDef, isFExistsBelow, ordinal(a), functional(newF), pair(a, b) ∈ newF, R(union(s), b)) |- R(newF ↾ a, app(newF, a))) by Substitution.ApplyRules(pairIsAppFunctional of (f := newF))
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), pair(a, b) ∈ newF, R(union(s), b)) |- R(newF ↾ a, app(newF, a))) by Cut(newFFunctional, lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), pair(a, b) ∈ singleton(pair(a, b)), R(union(s), b)) |- R(newF ↾ a, app(newF, a))) by Cut(setUnionRightIntro of (z := pair(a, b), x := union(s), y := singleton(pair(a, b))), lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), R(union(s), b)) |- R(newF ↾ a, app(newF, a))) by Cut(singletonIntro of (x := pair(a, b)), lastStep)
          thenHave(thesis) by Substitution.ApplyRules(d === a)
        }      

        val newFAppIn = have((classFunction(R), sDef, ordinal(a), d < a, isFExistsBelow) |- R(newF ↾ d, app(newF, d))) subproof {

          val appNewF = have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), z <= d, d < a, isF(f, successor(d))) |- app(newF, z) === app(f, z)) subproof {
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z < a) |- app(newF, z) === app(union(s), z)) by Substitution.ApplyRules(ihDomain)(appSetUnionRight of (a := z, f := union(s), g := singleton(pair(a, b))))
            thenHave((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z < a, f ∈ s, functional(union(s)), z ∈ dom(f)) |- app(newF, z) === app(f, z)) by Substitution.ApplyRules(appUnion of (z := s, a := z))
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z < a, isF(f, successor(d)), d < a, functional(union(s)), z ∈ dom(f)) |- app(newF, z) === app(f, z)) by Cut(sIntro, lastStep)
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z < a, isF(f, successor(d)), d < a, z ∈ dom(f)) |- app(newF, z) === app(f, z)) by Cut(ihFunctional, lastStep)
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z <= d, isF(f, successor(d)), d < a, z ∈ dom(f)) |- app(newF, z) === app(f, z)) by Cut(ordinalLeqLtImpliesLt of (a := z, b := d, c := a), lastStep)
            thenHave((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), z <= d, isF(f, successor(d)), d < a, z < successor(d)) |- app(newF, z) === app(f, z)) by Substitution.ApplyRules(isFDomain of (d := successor(d)))
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), z <= d, isF(f, successor(d)), d < a) |- app(newF, z) === app(f, z)) by Cut(ordinalLeqImpliesInSuccessor of (b := z, a := d), lastStep)
            have(thesis) by Cut(functionalOverIsFunctional of (f := newF, x := successor(a)), lastStep)
          }

          val domainRestrNewF = have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- newF ↾ d === f ↾ d) subproof {
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), z < d, d < a, isF(f, successor(d))) |- app(newF, z) === app(f, z)) by Cut(ltImpliesLeq of (a := z, b := d), appNewF)
            thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- z < d ==> (app(newF, z) === app(f, z))) by RightImplies
            thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- ∀(z, z < d ==> (app(newF, z) === app(f, z)))) by RightForall
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, d ⊆ successor(a), d ⊆ successor(d), isF(f, successor(d)), functionalOver(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(lastStep, functionRestrictionEqualApp of (f := newF, a := successor(a), g := f, b := successor(d), x := d))
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, d ⊆ successor(a), d ⊆ successor(d), isF(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(isFFunctionalOver of (d := successor(d)), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, d ⊆ successor(a), isF(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(subsetSuccessor of (a := d), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), d < a, d ∈ successor(a), isF(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(elementOfOrdinalIsSubset of (a := d, b := successor(a)), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), d < a, a ∈ successor(a), isF(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(ordinalTransitive of (a := d, b := a, c := successor(a)), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), d < a, isF(f, successor(d))) |- newF ↾ d === f ↾ d) by Cut(inSuccessor, lastStep)
            have(thesis) by Cut(successorIsOrdinal, lastStep)
          }

          have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- app(newF, d) === app(f, d)) by Cut(lessOrEqualLeftReflexivity of (a := d), appNewF of (z := d))
          have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- R(f ↾ d, app(newF, d))) by Substitution.ApplyRules(lastStep)(isFAppEq)
          thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- R(newF ↾ d, app(newF, d))) by Substitution.ApplyRules(domainRestrNewF)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), d < a, isF(f, successor(d))) |- R(newF ↾ d, app(newF, d))) by Cut(newFFunctionalOver, lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), d < a, isF(f, successor(d))) |- R(newF ↾ d, app(newF, d))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
          thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), d < a, ∃(f, isF(f, successor(d)))) |- R(newF ↾ d, app(newF, d))) by LeftExists
          have(thesis) by Cut(isFExistsBelowElim, lastStep)
        }

        have((classFunction(R), isFExistsBelow, sDef, ordinal(a), d <= a, R(union(s), b)) |- (R(newF ↾ d, app(newF, d)), d < a)) by Cut(lessOrEqualElim of (a := d, b := a), newFAppEq)
        have((classFunction(R), sDef, ordinal(a), d <= a, isFExistsBelow, R(union(s), b)) |- R(newF ↾ d, app(newF, d))) by Cut(lastStep, newFAppIn)
        have((classFunction(R), sDef, ordinal(a), d < successor(a), isFExistsBelow, R(union(s), b)) |- R(newF ↾ d, app(newF, d))) by Cut(inSuccessorLeq of (b := d), lastStep)
        thenHave((classFunction(R), sDef, ordinal(a), isFExistsBelow, R(union(s), b)) |- d < successor(a) ==> R(newF ↾ d, app(newF, d))) by RightImplies
        thenHave(thesis) by RightForall
      }

      have((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- isF(f, successor(a)).substitute(f := newF)) by RightAnd(newFFunctionalOver, newFApp)
      thenHave((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by RightExists
      thenHave((classFunction(R), sDef, ordinal(a), ∃(b, R(union(s), b)), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by LeftExists
      have((classFunction(R), sDef, ordinal(a), ∃!(b, R(union(s), b)), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by Cut(existsOneImpliesExists of (P := lambda(b, R(union(s), b))), lastStep)
      have((classFunction(R), sDef, ordinal(a), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by Cut(totalClassFunctionElim of (x := union(s)), lastStep)
      thenHave((classFunction(R), ∃(s, sDef), ordinal(a), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by LeftExists
      have((classFunction(R), ordinal(a), isFExistsBelow) |- ∃(f, isF(f, successor(a)))) by Cut(sExistence, lastStep)
      thenHave(classFunction(R) |- ordinal(a) ==> (isFExistsBelow ==> ∃(f, isF(f, successor(a))))) by Restate
      thenHave(classFunction(R) |- ∀(a, ordinal(a) ==> (isFExistsBelow ==> ∃(f, isF(f, successor(a)))))) by RightForall
      have(classFunction(R) |- ∀(a, ordinal(a) ==> ∃(f, isF(f, successor(a))))) by Cut(lastStep, transfiniteInductionOnAllOrdinals of (P := lambda(a, ∃(f, isF(f, successor(a))))))
      thenHave(thesis) by InstantiateForall(a)
    }

    val isFExistence = have((classFunction(R), ordinal(a)) |- ∃(f, isF(f, a))) subproof {
      
      val isFRestriction = have((isF(f, successor(a)), ordinal(a)) |- isF(f ↾ a, a)) subproof {
        have(∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))) |- ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b)))) by Hypothesis
        thenHave((∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), b < successor(a)) |- R(f ↾ b, app(f, b))) by InstantiateForall(b)
        thenHave((∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), b < successor(a), functional(f), b ⊆ a, b < a, b ∈ dom(f)) |- R((f ↾ a) ↾ b, app(f ↾ a, b))) by Substitution.ApplyRules(functionRestrictionTwiceSubsetOuter, functionRestrictionApp)
        thenHave((isF(f, successor(a)), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), b < successor(a), functional(f), b ⊆ a, b < a) |- R((f ↾ a) ↾ b, app(f ↾ a, b))) by Substitution.ApplyRules(isFDomain of (d := successor(a)))
        have((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), b < successor(a), functional(f), b < a) |- R((f ↾ a) ↾ b, app(f ↾ a, b))) by Cut(inSuccessorSubset, lastStep)
        have((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f), b < a) |- R((f ↾ a) ↾ b, app(f ↾ a, b))) by Cut(ordinalLtImpliesInSuccessor, lastStep)
        thenHave((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f)) |- b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b))) by RightImplies
        thenHave((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f)) |- ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by RightForall
        have((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f), functional(f ↾ a)) |- functionalOver(f ↾ a, dom(f ↾ a)) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by RightAnd(lastStep, functionalOverIntro of (f := f ↾ a))
        have((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f)) |- functionalOver(f ↾ a, dom(f ↾ a)) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Cut(domainRestrictionFunctional of (x := a), lastStep)
        thenHave((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functional(f)) |- functionalOver(f ↾ a, dom(f) ∩ a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Substitution.ApplyRules(domainRestrictionDomain)
        have((isF(f, successor(a)), ordinal(a), ∀(b, b < successor(a) ==> R(f ↾ b, app(f, b))), functionalOver(f, successor(a))) |- functionalOver(f ↾ a, dom(f) ∩ a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Cut(functionalOverIsFunctional of (x := successor(a)), lastStep)
        thenHave((isF(f, successor(a)), ordinal(a)) |- functionalOver(f ↾ a, dom(f) ∩ a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by LeftAnd
        thenHave((isF(f, successor(a)), ordinal(a)) |- functionalOver(f ↾ a, successor(a) ∩ a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Substitution.ApplyRules(isFDomain)
        thenHave((isF(f, successor(a)), ordinal(a), ordinal(successor(a)), a < successor(a)) |- functionalOver(f ↾ a, a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Substitution.ApplyRules(intersectionInOrdinal)
        have((isF(f, successor(a)), ordinal(a), ordinal(successor(a))) |- functionalOver(f ↾ a, a) /\ ∀(b, b < a ==> R((f ↾ a) ↾ b, app(f ↾ a, b)))) by Cut(inSuccessor, lastStep)
        have(thesis) by Cut(successorIsOrdinal, lastStep)
      }
      
      have((isF(f, successor(a)), ordinal(a)) |- ∃(f, isF(f, a))) by RightExists(isFRestriction)
      thenHave((∃(f, isF(f, successor(a))), ordinal(a)) |- ∃(f, isF(f, a))) by LeftExists
      have(thesis) by Cut(isFExistenceSuccessor, lastStep)
    }
    
    have((classFunction(R), ordinal(a), isF(f, a) /\ isF(g, a)) |- f === g) by LeftAnd(isFUniqueness of (d := a))
    thenHave((classFunction(R), ordinal(a)) |- (isF(f, a) /\ isF(g, a)) ==> (f === g)) by RightImplies
    thenHave((classFunction(R), ordinal(a)) |- ∀(g, isF(f, a) /\ isF(g, a) ==> (f === g))) by RightForall
    thenHave((classFunction(R), ordinal(a)) |- ∀(f, ∀(g, isF(f, a) /\ isF(g, a) ==> (f === g)))) by RightForall
    have((classFunction(R), ordinal(a), ∃(f, isF(f, a))) |- ∃!(f, isF(f, a))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(f, isF(f, a))))
    have(thesis) by Cut(isFExistence, lastStep)
  }

  val transfiniteRecursion = Theorem(
    ordinal(a) |- ∃!(f, functionalOver(f, a) /\ ∀(b, b < a ==> (app(f, b) === F(f ↾ b))))
  ) {
    have(thesis) by Cut(functionIsClassFunction of (P := lambda(x, True)), transfiniteRecursionClassFunction of (R := lambda((x, y), F(x) === y)))
  }
}