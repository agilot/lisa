package lisa.maths.settheory.orderings

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.orderings.MembershipRelation.*
import lisa.maths.settheory.orderings.PartialOrders.*
import lisa.maths.settheory.InductiveSets.*
import lisa.maths.settheory.orderings.Segments.*
import lisa.maths.settheory.orderings.Ordinals.*

/**
 * This file is dedicated to proving the well-ordered and transfinite recursion
 * theorems. Auxiliary lemmas are sections of the recursion proof separated out
 * for readability and faster compilation.
 */
object Recursion extends lisa.Main {
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
  private val t1 = variable
  private val t2 = variable
  private val r1 = variable
  private val r2 = variable
  private val s = variable

  // relation and function symbols
  private val r = variable
  private val p = variable
  private val q = variable
  private val f = variable
  private val g = variable
  private val F = function[1]
  private val G = function[2]

  private val P = predicate[1]
  private val Q = predicate[1]
  private val R = predicate[2]
  private val schemPred = predicate[1]

  val transfiniteRecursionClassFunction = Lemma(
    (classFunction(R, ordinal), ordinal(a)) |- existsOne(f, functionalOver(f, successor(a)) /\ forall(b, (in(b, a) \/ (b === a)) ==> R(domainRestriction(f, b), app(f, b))))
  ) {


    val existence = have((classFunction(R, ordinal), ordinal(a)) |- exists(f, functionalOver(f, successor(a)) /\ forall(b, (in(b, a) \/ (b === a)) ==> R(domainRestriction(f, b), app(f, b))))) subproof {

    //    val sDef = in(f, s) <=> exists(b, in(b, a) /\ functionalOver(f, successor(b)) /\ forall(c, (in(c, b) \/ (c === a)) ==> R(domainRestriction(f, b), app(f, b))))

      val ihFunctional = have(functional(union(s))) subproof {
        sorry
      }
      
      val ihDomain = have(relationDomain(union(s)) === a) subproof {
        sorry
      }

      val ihFunctionalOver = have(functionalOver(union(s), a)) subproof {
        have(functional(union(s)) |- functionalOver(union(s), a)) by Substitution.ApplyRules(ihDomain)(functionalOverIntro of (f := union(s)))
        have(thesis) by Cut(ihFunctional, lastStep)
      }

      val newF = setUnion(union(s), singleton(pair(a, b)))

      have(functionalOver(newF, successor(a))) subproof {
        have((functionalOver(union(s), a), functionalOver(singleton(pair(a, b)), singleton(a))) |- functionalOver(newF, setUnion(a, singleton(a)))) by 
          Cut(singletonDisjointSelf of (x := a), functionalOverDisjointSetUnion of (f := union(s), g := singleton(pair(a, b)), b := singleton(a)))
        have(functionalOver(singleton(pair(a, b)), singleton(a)) |- functionalOver(newF, setUnion(a, singleton(a)))) by 
          Cut(ihFunctionalOver, lastStep)
        have(functionalOver(newF, setUnion(a, singleton(a)))) by Cut(functionalOverSingleton of (x := a, y := b), lastStep)
        thenHave(thesis) by Substitution.ApplyRules(successor.shortDefinition)
      }

      have(domainRestriction(newF, a) === union(s)) subproof {
        // have(setIntersection(relationDomain(singleton(pair(a, b))), a) === emptySet |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), domainRestriction(singleton(pair(a, b)), a))) by (domainRestrictionSetUnion of (x := union(s), y := singleton(pair(a, b)), 
        have(setIntersection(relationDomain(singleton(pair(a, b))), a) === emptySet |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Sorry
        thenHave(setIntersection(singleton(a), a) === emptySet |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Substitution.ApplyRules(relationDomainSingleton of (x := a))
        thenHave(setIntersection(a, singleton(a)) === emptySet |- domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Substitution.ApplyRules(setIntersectionCommutativity of (x := singleton(a), y := a))
        have(domainRestriction(newF, a) === setUnion(domainRestriction(union(s), a), emptySet)) by Cut(singletonDisjointSelf of (x := a), lastStep)
        thenHave(domainRestriction(newF, a) === domainRestriction(union(s), a)) by Substitution.ApplyRules(setUnionRightEmpty of (a := domainRestriction(union(s), a)))
        thenHave(domainRestriction(newF, a) === domainRestriction(union(s), relationDomain(union(s)))) by Substitution.ApplyRules(ihDomain)
        thenHave(functional(union(s)) |- domainRestriction(newF, a) === union(s)) by Substitution.ApplyRules(functionRestrictionOnDomain of (f := union(s), x := a))
        have(thesis) by Cut(ihFunctional, lastStep)
      }

      have(in(d, a) |- R(domainRestriction(newF, d), app(f, d))) subproof {
        sorry
      }
      sorry
    }
    sorry
  }
}
