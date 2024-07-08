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

  val transfiniteRecursionClassFunction = Lemma(
    (classFunction(R), ordinal(a)) |- existsOne(f, functionalOver(f, successor(a)) /\ forall(b, (in(b, a) \/ (b === a)) ==> R(domainRestriction(f, b), app(f, b))))
  ) {

    def isF(f: Term, d: Term) = functionalOver(f, successor(d)) /\ forall(b, (in(b, d) \/ (b === d)) ==> R(domainRestriction(f, b), app(f, b)))

    val isFFunctionalOver = have(isF(f, d) |- functionalOver(f, successor(d))) by Restate
    val isFFunctional = have(isF(f, d) |- functional(f)) by Cut(isFFunctionalOver, functionalOverIsFunctional of (x := successor(d)))
    val isFDomain = have(isF(f, d) |- relationDomain(f) === successor(d)) by Cut(isFFunctionalOver, functionalOverDomain of (x := successor(d)))

    val isFAppSubset = have((ordinal(b), ordinal(d), isF(f, d), subset(b, d)) |- R(domainRestriction(f, b), app(f, b))) subproof {
      have(forall(b, (in(b, d) \/ (b === d)) ==> R(domainRestriction(f, b), app(f, b))) |-
            forall(b, (in(b, d) \/ (b === d)) ==> R(domainRestriction(f, b), app(f, b)))) by Hypothesis
      thenHave(isF(f, d) |- forall(b, (in(b, d) \/ (b === d)) ==> R(domainRestriction(f, b), app(f, b)))) by Weakening
      thenHave((isF(f, d), in(b, d) \/ (b === d)) |- R(domainRestriction(f, b), app(f, b))) by InstantiateForall(b)
      thenHave(thesis) by Substitution.ApplyRules(leqOrdinalIsSubset of (a := b, b := d))
    }

    val isFAppEq = have((isF(f, d), ordinal(d)) |- R(domainRestriction(f, d), app(f, d))) subproof {
      have(thesis) by Cut(subsetReflexivity of (x := d), isFAppSubset of (b := d))
    }

    val isFSubset = have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), in(d, e) \/ (d === e)) |- subset(f, g)) subproof {
      have((functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(d, successor(d)), subset(x, successor(e)), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- domainRestriction(f, x) === domainRestriction(g, x)) by Cut(subsetTransitivity of (y := d, z := successor(d)), functionRestrictionEqualApp of (a := successor(d), b := successor(e)))
      have((functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, successor(e)), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- domainRestriction(f, x) === domainRestriction(g, x)) by Cut(subsetSuccessor of (a := d), lastStep)
      have((functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, e), subset(e, successor(e)), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- domainRestriction(f, x) === domainRestriction(g, x)) by Cut(subsetTransitivity of (y := e, z := successor(e)), lastStep)
      val subst = have((functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- domainRestriction(f, x) === domainRestriction(g, x)) by Cut(subsetSuccessor of (a := e), lastStep)

      have((ordinal(d), ordinal(x), isF(f, d), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- R(domainRestriction(g, x), app(f, x))) by Substitution.ApplyRules(subst)(isFAppSubset of (b := x))
      have((classFunction(R), ordinal(d), ordinal(x), isF(f, d), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y))), R(domainRestriction(g, x), app(g, x))) |- app(f, x) === app(g, x)) by Cut(lastStep, totalClassFunctionUniqueness of (x := domainRestriction(g, x), y := app(g, x), z := app(f, x)))
      have((classFunction(R), ordinal(d), ordinal(e), ordinal(x), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(x, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by Cut(isFAppSubset of (f := g, d := e, b := x), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), ordinal(x), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(x, d), subset(d, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by Cut(subsetTransitivity of (y := d, z := e), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), ordinal(x), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), in(x, successor(d)), subset(d, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by Cut(inSuccessorSubset of (b := x, a := d), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), ordinal(successor(d)), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), in(x, successor(d)), subset(d, e), forall(y, in(y, x) ==> (app(f, y) === app(g, y)))) |- app(f, x) === app(g, x)) by Cut(elementsOfOrdinalsAreOrdinals of (b := x, a := successor(d)), lastStep)
      thenHave((classFunction(R), ordinal(d), ordinal(e), ordinal(successor(d)), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e)) |- in(x, successor(d)) ==> (forall(y, in(y, x) ==> (app(f, y) === app(g, y))) ==> (app(f, x) === app(g, x)))) by Restate
      thenHave((classFunction(R), ordinal(d), ordinal(successor(d)), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e)) |- forall(x, in(x, successor(d)) ==> (forall(y, in(y, x) ==> (app(f, y) === app(g, y))) ==> (app(f, x) === app(g, x))))) by RightForall
      have((classFunction(R), ordinal(d), ordinal(successor(d)), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e)) |- forall(x, in(x, successor(d)) ==> (app(f, x) ===  app(g, x)))) by Cut(lastStep, transfiniteInductionOnOrdinal of (x := successor(d), P := lambda(x, app(f, x) === app(g, x))))
      have((classFunction(R), ordinal(d), ordinal(successor(d)), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e), subset(successor(d), successor(e))) |- subset(f, g)) by Cut(lastStep, functionalOverSubsetApp of (x := successor(d), y := successor(e)))
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e), subset(successor(d), successor(e))) |- subset(f, g)) by Cut(successorIsOrdinal of (a := d), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(f, successor(d)), functionalOver(g, successor(e)), subset(d, e)) |- subset(f, g)) by Cut(successorPreservesSubset of (a := d, b := e), lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), functionalOver(g, successor(e)), subset(d, e)) |- subset(f, g)) by Cut(isFFunctionalOver, lastStep)
      have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), subset(d, e)) |- subset(f, g)) by Cut(isFFunctionalOver of (f := g, d := e), lastStep)
      have(thesis) by Cut(ordinalLeqImpliesSubset of (a := d, b := e), lastStep)
    }

    val isFUniqueness = have((classFunction(R), ordinal(d), isF(f, d), isF(g, d)) |- f === g) subproof {
      val forward = have((classFunction(R), ordinal(d), isF(f, d), isF(g, d)) |- subset(f, g)) by Restate.from(isFSubset of (e := d))
      have((classFunction(R), ordinal(d), isF(f, d), isF(g, d), subset(g, f)) |- f === g) by Cut(forward, subsetAntisymmetry of (x := f, y := g))
      have(thesis) by Cut(forward of (f := g, g := f), lastStep) 
    }

    val isFExistence = have((classFunction(R), ordinal(a)) |- exists(f, isF(f, a))) subproof {

      val sDef = forall(f, in(f, s) <=> exists(d, in(d, a) /\ isF(f, d)))
      val sElim = have((sDef, in(f, s)) |- exists(d, in(d, a) /\ isF(f, d))) subproof {
        have(sDef |- sDef) by Hypothesis
        thenHave(sDef |- in(f, s) <=> exists(d, in(d, a) /\ isF(f, d))) by InstantiateForall(f)
        thenHave(thesis) by Weakening
      }
      val sIntro = have((sDef, in(d, a), isF(f, d)) |- in(f, s)) subproof{
        have((in(d, a), isF(f, d)) |- in(d, a) /\ isF(f, d)) by Restate
        val exIntro = thenHave((in(d, a), isF(f, d)) |- exists(d, in(d, a) /\ isF(f, d))) by RightExists

        have(sDef |- sDef) by Hypothesis
        thenHave(sDef |- in(f, s) <=> exists(d, in(d, a) /\ isF(f, d))) by InstantiateForall(f)
        thenHave((sDef, exists(d, in(d, a) /\ isF(f, d))) |- in(f, s)) by Weakening
        have(thesis) by Cut(exIntro, lastStep)
      }

      val isFExistsBelow = forall(d, in(d, a) ==> exists(f, isF(f, d)))

      val isFExistsBelowElim = have((isFExistsBelow, in(d, a)) |- exists(f, isF(f, d))) subproof {
        have(isFExistsBelow |- isFExistsBelow) by Hypothesis
        thenHave(thesis) by InstantiateForall(d)
      }

      val sExistence = have((classFunction(R), ordinal(a), isFExistsBelow) |- exists(s, sDef)) subproof {
        have((classFunction(R), ordinal(d)) |- (isF(f, d) /\ isF(g, d)) ==> (f === g)) by Restate.from(isFUniqueness)
        thenHave((classFunction(R), ordinal(d)) |- forall(g, (isF(f, d) /\ isF(g, d)) ==> (f === g))) by RightForall
        thenHave((classFunction(R), ordinal(d)) |- forall(f, forall(g, isF(f, d) ==> (isF(g, d) ==> (f === g))))) by RightForall
        have((classFunction(R), ordinal(d), exists(f, isF(f, d))) |- existsOne(f, isF(f, d))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(f, isF(f, d))))
        have((classFunction(R), ordinal(d), isFExistsBelow, in(d, a)) |- existsOne(f, isF(f, d))) by Cut(isFExistsBelowElim, lastStep)
        have((classFunction(R), ordinal(a), isFExistsBelow, in(d, a)) |- existsOne(f, isF(f, d))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
        thenHave((classFunction(R), ordinal(a), isFExistsBelow) |- in(d, a) ==> existsOne(f, isF(f, d))) by RightImplies
        thenHave((classFunction(R), ordinal(a), isFExistsBelow) |- forall(d, in(d, a) ==> existsOne(f, isF(f, d)))) by RightForall
        have(thesis) by Cut(lastStep, replacementExistence of (A := a, R := lambda((d, f), isF(f, d))))
      }

      val ihFunctional = have((classFunction(R), sDef, ordinal(a)) |- functional(union(s))) subproof {
        have(in(d, a) /\ isF(f, d) |- functional(f)) by Weakening(isFFunctional)
        thenHave(exists(d, in(d, a) /\ isF(f, d)) |- functional(f)) by LeftExists
        have((sDef, in(f, s)) |- functional(f)) by Cut(sElim, lastStep)
        thenHave(sDef |- in(f, s) ==> functional(f)) by RightImplies
        val allFun = thenHave(sDef |- forall(f, in(f, s) ==> functional(f))) by RightForall
        
        val isFSubsetMembership = have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), in(d, e)) |- subset(f, g)) by Weakening(isFSubset)
        have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), d === e) |- f === g) by Substitution.ApplyRules(d === e)(isFUniqueness)
        val isFSubsetEquality = have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e), d === e) |- subset(f, g)) by Substitution.ApplyRules(lastStep)(subsetReflexivity of (x := f))

        have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e)) |- (subset(f, g), in(e, d), d === e)) by Cut(ordinalCases of (a := d, b := e), isFSubsetMembership)
        have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e)) |- (subset(f, g), in(e, d))) by Cut(lastStep, isFSubsetEquality)
        have((classFunction(R), ordinal(d), ordinal(e), isF(f, d), isF(g, e)) |- (subset(f, g), subset(g, f))) by Cut(lastStep, isFSubsetMembership of (f := g, g := f, d := e, e := d))
        have((classFunction(R), ordinal(a), in(d, a), ordinal(e), isF(f, d), isF(g, e)) |- (subset(f, g), subset(g, f))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
        have((classFunction(R), ordinal(a), in(d, a), in(e, a), isF(f, d), isF(g, e)) |- (subset(f, g), subset(g, f))) by Cut(elementsOfOrdinalsAreOrdinals of (b := e), lastStep)
        thenHave((classFunction(R), ordinal(a), in(d, a) /\ isF(f, d), in(e, a) /\ isF(g, e)) |- (subset(f, g), subset(g, f))) by Restate
        thenHave((classFunction(R), ordinal(a), exists(d, in(d, a) /\ isF(f, d)), in(e, a) /\ isF(g, e)) |- (subset(f, g), subset(g, f))) by LeftExists
        thenHave((classFunction(R), ordinal(a), exists(d, in(d, a) /\ isF(f, d)), exists(e, in(e, a) /\ isF(g, e))) |- (subset(f, g), subset(g, f))) by LeftExists
        have((classFunction(R), sDef, ordinal(a), in(f, s), exists(e, in(e, a) /\ isF(g, e))) |- (subset(f, g), subset(g, f))) by Cut(sElim, lastStep)
        have((classFunction(R), sDef, ordinal(a), in(f, s), in(g, s)) |- (subset(f, g), subset(g, f))) by Cut(sElim of (f := g), lastStep)
        thenHave((classFunction(R), sDef, ordinal(a)) |- (in(f, s) /\ in(g, s)) ==> (subset(f, g) \/ subset(g, f))) by Restate
        thenHave((classFunction(R), sDef, ordinal(a)) |- forall(g, in(f, s) /\ in(g, s) ==> (subset(f, g) \/ subset(g, f)))) by RightForall
        thenHave((classFunction(R), sDef, ordinal(a)) |- forall(f, forall(g, in(f, s) /\ in(g, s) ==> (subset(f, g) \/ subset(g, f))))) by RightForall
        have((classFunction(R), forall(f, in(f, s) ==> functional(f)), sDef, ordinal(a)) |- functional(union(s))) by Cut(lastStep, unionOfFunctionSet of (z := s))
        have(thesis) by Cut(allFun, lastStep)
      }

      val ihDomain = have((isFExistsBelow, sDef, ordinal(a)) |- relationDomain(union(s)) === a) subproof {
        val forward = have((sDef, ordinal(a)) |- in(d, relationDomain(union(s))) ==> in(d, a)) subproof {
          have(in(d, successor(e)) |- in(d, e) \/ (d === e)) by Restate.from(inSuccessorLeq of (a := e, b := d))
          have((in(d, successor(e)), in(e, a), ordinal(a)) |- in(d, a)) by Cut(lastStep, ordinalLeqLtImpliesLt of (a := d, b := e, c := a))
          thenHave((in(d, relationDomain(f)), in(e, a), ordinal(a), isF(f, e)) |- in(d, a)) by Substitution.ApplyRules(isFDomain of (d := e))
          thenHave((in(d, relationDomain(f)), ordinal(a), in(e, a) /\ isF(f, e)) |- in(d, a)) by LeftAnd
          thenHave((in(d, relationDomain(f)), ordinal(a), exists(e, in(e, a) /\ isF(f, e))) |- in(d, a)) by LeftExists
          have((sDef, in(d, relationDomain(f)), ordinal(a), in(f, s)) |- in(d, a)) by Cut(sElim, lastStep)
          thenHave((sDef, in(d, relationDomain(f)) /\ in(f, s), ordinal(a)) |- in(d, a)) by LeftAnd
          thenHave((sDef, exists(f, in(d, relationDomain(f)) /\ in(f, s)), ordinal(a)) |- in(d, a)) by LeftExists
          thenHave((sDef, in(d, relationDomain(union(s))), ordinal(a)) |- in(d, a)) by Substitution.ApplyRules(relationDomainUnion of (t := d, z := s))
        } 
        val backward = have((isFExistsBelow, sDef) |- in(d, a) ==> in(d, relationDomain(union(s)))) subproof {
          have(isF(f, d) |- in(d, relationDomain(f))) by Substitution.ApplyRules(isFDomain)(inSuccessor of (a := d))
          have((sDef, in(d, a), isF(f, d)) |- in(d, relationDomain(f)) /\ in(f, s)) by RightAnd(sIntro, lastStep)
          thenHave((sDef, in(d, a), isF(f, d)) |- exists(f, in(d, relationDomain(f)) /\ in(f, s))) by RightExists
          thenHave((sDef, in(d, a), isF(f, d)) |- in(d, relationDomain(union(s)))) by Substitution.ApplyRules(relationDomainUnion of (t := d, z := s))
          thenHave((sDef, in(d, a), exists(f, isF(f, d))) |- in(d, relationDomain(union(s)))) by LeftExists
          have((sDef, in(d, a), isFExistsBelow) |- in(d, relationDomain(union(s)))) by Cut(isFExistsBelowElim, lastStep)
        }
        have((isFExistsBelow, sDef, ordinal(a)) |- in(d, a) <=> in(d, relationDomain(union(s)))) by RightIff(forward, backward)
        thenHave((isFExistsBelow, sDef, ordinal(a)) |- forall(d, in(d, a) <=> in(d, relationDomain(union(s))))) by RightForall
        have(thesis) by Cut(lastStep, equalityIntro of (x := relationDomain(union(s)), y := a))
      }

      val ihFunctionalOver = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(union(s), a)) subproof {
        have((isFExistsBelow, classFunction(R), sDef, ordinal(a), functional(union(s))) |- functionalOver(union(s), a)) by Substitution.ApplyRules(ihDomain)(functionalOverIntro of (f := union(s)))
        have(thesis) by Cut(ihFunctional, lastStep)
      }

      val newF = setUnion(union(s), singleton(pair(a, b)))

      val newFFunctionalOver = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(newF, successor(a))) subproof {
        have((functionalOver(union(s), a), functionalOver(singleton(pair(a, b)), singleton(a))) |- functionalOver(newF, setUnion(a, singleton(a)))) by 
          Cut(singletonDisjointSelf of (x := a), functionalOverDisjointSetUnion of (f := union(s), g := singleton(pair(a, b)), b := singleton(a)))
        have((classFunction(R), isFExistsBelow, sDef, ordinal(a), functionalOver(singleton(pair(a, b)), singleton(a))) |- functionalOver(newF, setUnion(a, singleton(a)))) by 
          Cut(ihFunctionalOver, lastStep)
        have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functionalOver(newF, setUnion(a, singleton(a)))) by Cut(functionalOverSingleton of (x := a, y := b), lastStep)
        thenHave(thesis) by Substitution.ApplyRules(successor.shortDefinition)
      }

      val newFFunctional = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- functional(newF)) by Cut(newFFunctionalOver, functionalOverIsFunctional of (f := newF, x := successor(a)))

      val newFApp = have((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- forall(d, (in(d, a) \/ (d === a)) ==> R(domainRestriction(newF, d), app(newF, d)))) subproof {
        val newFAppEq = have((classFunction(R), isFExistsBelow, sDef, ordinal(a), d === a, R(union(s), b)) |- R(domainRestriction(newF, d), app(newF, d))) subproof {
          
          val newFRestr = have((classFunction(R), isFExistsBelow, sDef, ordinal(a)) |- domainRestriction(newF, a) === union(s)) subproof {
            have((disjoint(relationDomain(singleton(pair(a, b))), a), functional(union(s)), functional(singleton(pair(a, b)))) |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by 
              Substitution.ApplyRules(domainRestrictionDisjoint of (f := singleton(pair(a, b)), x := a))(functionRestrictionSetUnion of (f := union(s), g := singleton(pair(a, b)), x := a))
            have((disjoint(relationDomain(singleton(pair(a, b))), a), functional(union(s))) |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by
              Cut(functionalSingleton of (x := a, y := b), lastStep)
            thenHave((disjoint(singleton(a), a), functional(union(s))) |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Substitution.ApplyRules(relationDomainSingleton of (x := a))
            thenHave((disjoint(a, singleton(a)), functional(union(s))) |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Substitution.ApplyRules(disjointSymmetry of (x := singleton(a), y := a))
            have(functional(union(s)) |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Cut(singletonDisjointSelf of (x := a), lastStep)
            thenHave(functional(union(s)) |- domainRestriction(newF, a) === domainRestriction(union(s), a)) by Substitution.ApplyRules(setUnionRightEmpty of (a := domainRestriction(union(s), a)))
            thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), functional(union(s))) |- domainRestriction(newF, a) === domainRestriction(union(s), relationDomain(union(s)))) by Substitution.ApplyRules(ihDomain)
            thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), functional(union(s))) |- domainRestriction(newF, a) === union(s)) by Substitution.ApplyRules(functionRestrictionOnDomain of (f := union(s), x := a))
            have(thesis) by Cut(ihFunctional, lastStep)
          }

          have(R(union(s), b) |- R(union(s), b)) by Hypothesis
          thenHave((classFunction(R), sDef, isFExistsBelow, ordinal(a), R(union(s), b)) |- R(domainRestriction(newF, a), b)) by Substitution.ApplyRules(newFRestr)
          thenHave((classFunction(R), sDef, isFExistsBelow, ordinal(a), functional(newF), in(pair(a, b), newF), R(union(s), b)) |- R(domainRestriction(newF, a), app(newF, a))) by Substitution.ApplyRules(pairIsAppFunctional of (f := newF))
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), in(pair(a, b), newF), R(union(s), b)) |- R(domainRestriction(newF, a), app(newF, a))) by Cut(newFFunctional, lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), in(pair(a, b), singleton(pair(a, b))), R(union(s), b)) |- R(domainRestriction(newF, a), app(newF, a))) by Cut(setUnionRightIntro of (z := pair(a, b), x := union(s), y := singleton(pair(a, b))), lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), R(union(s), b)) |- R(domainRestriction(newF, a), app(newF, a))) by Cut(singletonIntro of (x := pair(a, b)), lastStep)
          thenHave(thesis) by Substitution.ApplyRules(d === a)
        }      

        val newFAppIn = have((classFunction(R), sDef, ordinal(a), in(d, a), isFExistsBelow) |- R(domainRestriction(newF, d), app(newF, d))) subproof {

          val appNewF = have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(z, d) \/ (z === d), in(d, a), isF(f, d)) |- app(newF, z) === app(f, z)) subproof {
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, a)) |- app(newF, z) === app(union(s), z)) by Substitution.ApplyRules(ihDomain)(appSetUnionRight of (a := z, f := union(s), g := singleton(pair(a, b))))
            thenHave((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, a), in(f, s), functional(union(s)), in(z, relationDomain(f))) |- app(newF, z) === app(f, z)) by Substitution.ApplyRules(appUnion of (z := s, a := z))
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, a), isF(f, d), in(d, a), functional(union(s)), in(z, relationDomain(f))) |- app(newF, z) === app(f, z)) by Cut(sIntro, lastStep)
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, a), isF(f, d), in(d, a), in(z, relationDomain(f))) |- app(newF, z) === app(f, z)) by Cut(ihFunctional, lastStep)
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, d) \/ (z === d), isF(f, d), in(d, a), in(z, relationDomain(f))) |- app(newF, z) === app(f, z)) by Cut(ordinalLeqLtImpliesLt of (a := z, b := d, c := a), lastStep)
            thenHave((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), in(z, d) \/ (z === d), isF(f, d), in(d, a), in(z, successor(d))) |- app(newF, z) === app(f, z)) by Substitution.ApplyRules(isFDomain)
            have((functional(newF), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(z, d) \/ (z === d), isF(f, d), in(d, a)) |- app(newF, z) === app(f, z)) by Cut(ordinalLeqImpliesInSuccessor of (b := z, a := d), lastStep)
            have(thesis) by Cut(functionalOverIsFunctional of (f := newF, x := successor(a)), lastStep)
          }

          val domainRestrNewF = have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) subproof {
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(z, d), in(d, a), isF(f, d)) |- app(newF, z) === app(f, z)) by Weakening(appNewF)
            thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- in(z, d) ==> (app(newF, z) === app(f, z))) by RightImplies
            thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- forall(z, in(z, d) ==> (app(newF, z) === app(f, z)))) by RightForall
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), subset(d, successor(a)), subset(d, successor(d)), isF(f, d), functionalOver(f, successor(d))) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(lastStep, functionRestrictionEqualApp of (f := newF, a := successor(a), g := f, b := successor(d), x := d))
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), subset(d, successor(a)), subset(d, successor(d)), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(isFFunctionalOver, lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), subset(d, successor(a)), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(subsetSuccessor of (a := d), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), in(d, a), in(d, successor(a)), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(elementOfOrdinalIsSubset of (a := d, b := successor(a)), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), in(d, a), in(a, successor(a)), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(ordinalTransitive of (a := d, b := a, c := successor(a)), lastStep)
            have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), ordinal(successor(a)), in(d, a), isF(f, d)) |- domainRestriction(newF, d) === domainRestriction(f, d)) by Cut(inSuccessor, lastStep)
            have(thesis) by Cut(successorIsOrdinal, lastStep)
          }

          have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- app(newF, d) === app(f, d)) by Restate.from(appNewF of (z := d))
          have((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- R(domainRestriction(f, d), app(newF, d))) by Substitution.ApplyRules(lastStep)(isFAppEq)
          thenHave((functionalOver(newF, successor(a)), classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- R(domainRestriction(newF, d), app(newF, d))) by Substitution.ApplyRules(domainRestrNewF)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), ordinal(d), in(d, a), isF(f, d)) |- R(domainRestriction(newF, d), app(newF, d))) by Cut(newFFunctionalOver, lastStep)
          have((classFunction(R), isFExistsBelow, sDef, ordinal(a), in(d, a), isF(f, d)) |- R(domainRestriction(newF, d), app(newF, d))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d), lastStep)
          thenHave((classFunction(R), isFExistsBelow, sDef, ordinal(a), in(d, a), exists(f, isF(f, d))) |- R(domainRestriction(newF, d), app(newF, d))) by LeftExists
          have(thesis) by Cut(isFExistsBelowElim, lastStep)
        }

        have((classFunction(R), sDef, ordinal(a), in(d, a) \/ (d === a), isFExistsBelow, R(union(s), b)) |- R(domainRestriction(newF, d), app(newF, d))) by LeftOr(newFAppIn, newFAppEq)
        thenHave((classFunction(R), sDef, ordinal(a), isFExistsBelow, R(union(s), b)) |- (in(d, a) \/ (d === a)) ==> R(domainRestriction(newF, d), app(newF, d))) by RightImplies
        thenHave(thesis) by RightForall
      }

      have((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- isF(f, a).substitute(f := newF)) by RightAnd(newFFunctionalOver, newFApp)
      thenHave((classFunction(R), sDef, ordinal(a), R(union(s), b), isFExistsBelow) |- exists(f, isF(f, a))) by RightExists
      thenHave((classFunction(R), sDef, ordinal(a), exists(b, R(union(s), b)), isFExistsBelow) |- exists(f, isF(f, a))) by LeftExists
      have((classFunction(R), sDef, ordinal(a), existsOne(b, R(union(s), b)), isFExistsBelow) |- exists(f, isF(f, a))) by Cut(existsOneImpliesExists of (P := lambda(b, R(union(s), b))), lastStep)
      have((classFunction(R), sDef, ordinal(a), isFExistsBelow) |- exists(f, isF(f, a))) by Cut(totalClassFunctionElim of (x := union(s)), lastStep)
      thenHave((classFunction(R), exists(s, sDef), ordinal(a), isFExistsBelow) |- exists(f, isF(f, a))) by LeftExists
      have((classFunction(R), ordinal(a), isFExistsBelow) |- exists(f, isF(f, a))) by Cut(sExistence, lastStep)
      thenHave(classFunction(R) |- ordinal(a) ==> (isFExistsBelow ==> exists(f, isF(f, a)))) by Restate
      thenHave(classFunction(R) |- forall(a, ordinal(a) ==> (isFExistsBelow ==> exists(f, isF(f, a))))) by RightForall
      have(classFunction(R) |- forall(a, ordinal(a) ==> exists(f, isF(f, a)))) by Cut(lastStep, transfiniteInductionOnAllOrdinals of (P := lambda(a, exists(f, isF(f, a)))))
      thenHave(thesis) by InstantiateForall(a)
    }
    
    have((classFunction(R), ordinal(a), isF(f, a) /\ isF(g, a)) |- f === g) by LeftAnd(isFUniqueness of (d := a))
    thenHave((classFunction(R), ordinal(a)) |- (isF(f, a) /\ isF(g, a)) ==> (f === g)) by RightImplies
    thenHave((classFunction(R), ordinal(a)) |- forall(g, isF(f, a) /\ isF(g, a) ==> (f === g))) by RightForall
    thenHave((classFunction(R), ordinal(a)) |- forall(f, forall(g, isF(f, a) /\ isF(g, a) ==> (f === g)))) by RightForall
    have((classFunction(R), ordinal(a), exists(f, isF(f, a))) |- existsOne(f, isF(f, a))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(f, isF(f, a))))
    have(thesis) by Cut(isFExistence, lastStep)
  }
}