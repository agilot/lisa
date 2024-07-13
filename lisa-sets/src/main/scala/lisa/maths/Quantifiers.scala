package lisa.maths

/**
 * Implements theorems about first-order logic.
 */
object Quantifiers extends lisa.Main {

  private val x = variable
  private val y = variable
  private val z = variable
  private val a = variable
  private val q = formulaVariable
  private val p = formulaVariable
  private val p1 = formulaVariable
  private val p2 = formulaVariable
  private val P = predicate[1]
  private val Q = predicate[1]
  private val P1 = predicate[1]
  private val P2 = predicate[1]
  private val R = predicate[2]

  /**
   * Theorem --- A formula is equivalent to itself universally quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaUniversal = Theorem(
    () |- ∀(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- A formula is equivalent to itself existentially quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaExistential = Theorem(
    () |- ∃(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Equality relation is transitive.
   */
  val equalityTransitivity = Theorem(
    (x === y, y === z) |- (x === z)
  ) {
    have((x === y) |- (x === y)) by Hypothesis
    thenHave(thesis) by RightSubstEq.withParametersSimple(List((y, z)), lambda(y, x === y))
  }

  /**
   * Theorem --- If there exists a *unique* element satisfying a predicate,
   * then we can say there *exists* an element satisfying it as well.
   */
  val existsOneImpliesExists = Theorem(
    ∃!(x, P(x)) |- ∃(x, P(x))
  ) {
    have((x === y) <=> P(y) |- (x === y) <=> P(y)) by Hypothesis
    thenHave(∀(y, (x === y) <=> P(y)) |- (x === y) <=> P(y)) by LeftForall
    thenHave(∀(y, (x === y) <=> P(y)) |- P(x)) by InstFunSchema(Map(y -> x))
    thenHave(∀(y, (x === y) <=> P(y)) |- ∃(x, P(x))) by RightExists
    thenHave(∃(x, ∀(y, (x === y) <=> P(y))) |- ∃(x, P(x))) by LeftExists
  }

  val existsOneImpliesUniqueness = Theorem(
    (∃!(x, P(x)), P(x), P(y)) |- x === y
  ) {
    val hyp = have(∀(x, (x === z) <=> P(x)) |- ∀(x, (x === z) <=> P(x))) by Hypothesis
    thenHave((∀(x, (x === z) <=> P(x))) |- (x === z) <=> P(x)) by InstantiateForall(x)
    thenHave((∀(x, (x === z) <=> P(x)), P(x)) |- x === z) by Weakening
    val right = have((∀(x, (x === z) <=> P(x)), P(x), y === z) |- x === y) by Cut(lastStep, equalityTransitivity of (y := z, z := y))
    
    have((∀(x, (x === z) <=> P(x))) |- (y === z) <=> P(y)) by InstantiateForall(y)(hyp)
    val left = thenHave((∀(x, (x === z) <=> P(x)), P(y)) |- y === z) by Weakening

    have((∀(x, (x === z) <=> P(x)), P(x), P(y)) |- x === y) by Cut(left, right)
    thenHave((∃(z, ∀(x, (x === z) <=> P(x))), P(x), P(y)) |- x === y) by LeftExists
    thenHave(thesis) by LeftExistsOne
  }

  /**
   * Theorem --- Top level existential quantifiers can be swapped.
   */
  val existentialSwap = Lemma(∃(x, ∃(y, R(x, y))) <=> ∃(y, ∃(x, R(x, y)))) {
    have(thesis) by Tableau
  }


  /**
   * Theorem --- Conjunction and universal quantification commute.
   */
  val universalConjunctionCommutation = Theorem(
    () |- ∀(x, P(x) /\ Q(x)) <=> ∀(x, P(x)) /\ ∀(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- Existential quantification distributes conjunction.
   */
  val existentialConjunctionDistribution = Theorem(
    ∃(x, P(x) /\ Q(x)) |- ∃(x, P(x)) /\ ∃(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- Existential quantification fully distributes when the conjunction involves one closed formula.
   */
  val existentialConjunctionWithClosedFormula = Theorem(
    ∃(x, P(x) /\ p) <=> (∃(x, P(x)) /\ p)
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- If there is an equality on the existential quantifier's bound variable inside its body, then we can reduce
   * the existential quantifier to the satisfaction of the remaining body.
   */
  val equalityInExistentialQuantifier = Theorem(
    ∃(x, P(x) /\ (y === x)) <=> P(y)
  ) {
    have(∃(x, P(x) /\ (y === x)) |- P(y)) subproof {
      have(P(x) |- P(x)) by Hypothesis
      thenHave((P(x), y === x) |- P(y)) by RightSubstEq.withParametersSimple(List((y, x)), lambda(y, P(y)))
      thenHave(P(x) /\ (y === x) |- P(y)) by Restate
      thenHave(thesis) by LeftExists
    }
    val forward = thenHave(∃(x, P(x) /\ (y === x)) ==> P(y)) by Restate

    have(P(y) |- ∃(x, P(x) /\ (y === x))) subproof {
      have(P(x) /\ (y === x) |- P(x) /\ (y === x)) by Hypothesis
      thenHave(P(x) /\ (y === x) |- ∃(x, P(x) /\ (y === x))) by RightExists
      thenHave(P(y) /\ (y === y) |- ∃(x, P(x) /\ (y === x))) by InstFunSchema(Map(x -> y))
    }
    val backward = thenHave(P(y) ==> ∃(x, P(x) /\ (y === x))) by Restate

    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Theorem --- Disjunction and existential quantification commute.
   */
  val existentialDisjunctionCommutation = Theorem(
    () |- ∃(x, P(x) \/ Q(x)) <=> ∃(x, P(x)) \/ ∃(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification distributes over equivalence
   */
  val universalEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∀(z, P(z)) <=> ∀(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of equivalence implies equivalence
   * of existential quantification.
   */
  val existentialEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∃(z, P(z)) <=> ∃(z, Q(z)))
  ) {
    have(thesis) by Tableau

  }

  /**
   * Theorem --- Universal quantification distributes over implication
   */
  val universalImplicationDistribution = Theorem(
    ∀(z, P(z) ==> Q(z)) |- (∀(z, P(z)) ==> ∀(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of implication implies implication
   * of existential quantification.
   */
  val existentialImplicationDistribution = Theorem(
    ∀(z, P(z) ==> Q(z)) |- (∃(z, P(z)) ==> ∃(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of equivalence implies equivalence
   * of unique existential quantification.
   */
  val uniqueExistentialEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∃!(z, P(z)) <=> ∃!(z, Q(z)))
  ) {
    val yz = have(∀(z, P(z) <=> Q(z)) |- ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y))) subproof {
      have(∀(z, P(z) <=> Q(z)) |- ∀(z, P(z) <=> Q(z))) by Hypothesis
      val quant = thenHave(∀(z, P(z) <=> Q(z)) |- P(y) <=> Q(y)) by InstantiateForall(y)

      val lhs = have((∀(z, P(z) <=> Q(z)), ((y === z) <=> P(y))) |- ((y === z) <=> Q(y))) subproof {
        have((P(y) <=> Q(y), ((y === z) <=> P(y))) |- ((y === z) <=> Q(y))) by Tautology
        have(thesis) by Tautology.from(lastStep, quant)
      }
      val rhs = have((∀(z, P(z) <=> Q(z)), ((y === z) <=> Q(y))) |- ((y === z) <=> P(y))) subproof {
        have((P(y) <=> Q(y), ((y === z) <=> Q(y))) |- ((y === z) <=> P(y))) by Tautology
        have(thesis) by Tautology.from(lastStep, quant)
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    val fy = thenHave(∀(z, P(z) <=> Q(z)) |- ∀(y, ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y)))) by RightForall

    have(∀(y, P(y) <=> Q(y)) |- (∀(y, P(y)) <=> ∀(y, Q(y)))) by Restate.from(universalEquivalenceDistribution)
    val univy = thenHave(∀(y, ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y))) |- (∀(y, ((y === z) <=> P(y))) <=> ∀(y, ((y === z) <=> Q(y))))) by InstPredSchema(
      Map((P -> lambda(y, (y === z) <=> P(y))), (Q -> lambda(y, (y === z) <=> Q(y))))
    )

    have(∀(z, P(z) <=> Q(z)) |- (∀(y, ((y === z) <=> P(y))) <=> ∀(y, ((y === z) <=> Q(y))))) by Cut(fy, univy)

    thenHave(∀(z, P(z) <=> Q(z)) |- ∀(z, ∀(y, ((y === z) <=> P(y))) <=> ∀(y, ((y === z) <=> Q(y))))) by RightForall
    have(∀(z, P(z) <=> Q(z)) |- ∃(z, ∀(y, ((y === z) <=> P(y)))) <=> ∃(z, ∀(y, ((y === z) <=> Q(y))))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P -> lambda(z, ∀(y, (y === z) <=> P(y))), Q -> lambda(z, ∀(y, (y === z) <=> Q(y))))
    )
    
  }

  /**
   * Theorem --- if atleast two distinct elements exist, then there is no unique
   * existence
   */
  val atleastTwoExist = Theorem(
    (∃(x, P(x)) /\ !(∃!(x, P(x))) <=> ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))))
  ) {
    val forward = have((∃(x, P(x)) /\ !(∃!(x, P(x))) ==> ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))))) subproof {
      have((P(x), ((x === y) /\ !P(y))) |- P(x) /\ !P(y)) by Restate
      thenHave((P(x), ((x === y) /\ !P(y))) |- P(y) /\ !P(y)) by Substitution.ApplyRules(x === y) // contradiction
      val xy = thenHave((P(x), ((x === y) /\ !P(y))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by Weakening

      have((P(x), (!(x === y) /\ P(y))) |- (!(x === y) /\ P(y) /\ P(x))) by Restate
      thenHave((P(x), (!(x === y) /\ P(y))) |- ∃(y, !(x === y) /\ P(y) /\ P(x))) by RightExists
      val nxy = thenHave((P(x), (!(x === y) /\ P(y))) |- ∃(x, ∃(y, !(x === y) /\ P(y) /\ P(x)))) by RightExists

      have((P(x), (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by Tautology.from(xy, nxy)
      thenHave((P(x), ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y)))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists
      thenHave((P(x), ∀(x, ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftForall
      thenHave((∃(x, P(x)), ∀(x, ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists
    }

    val backward = have(∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))) ==> (∃(x, P(x)) /\ !(∃!(x, P(x))))) subproof {
      have((P(x), P(y), !(x === y)) |- P(x)) by Restate
      val ex = thenHave((P(x), P(y), !(x === y)) |- ∃(x, P(x))) by RightExists

      have((P(x), P(y), !(x === y)) |- P(y) /\ !(y === x)) by Restate
      thenHave((P(x), P(y), !(x === y), (x === z)) |- P(y) /\ !(y === z)) by Substitution.ApplyRules(x === z)
      thenHave((P(x), P(y), !(x === y), (x === z)) |- (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z))) by Weakening
      val xz = thenHave((P(x), P(y), !(x === y), (x === z)) |- ∃(y, (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z)))) by RightExists

      have((P(x), P(y), !(x === y), !(x === z)) |- (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))) by Restate
      val nxz = thenHave((P(x), P(y), !(x === y), !(x === z)) |- ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by RightExists

      have((P(x), P(y), !(x === y)) |- ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by Tautology.from(xz, nxz)
      thenHave((P(x), P(y), !(x === y)) |- ∀(z, ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))))) by RightForall
      val uex = thenHave(P(x) /\ P(y) /\ !(x === y) |- !(∃!(z, P(z)))) by Restate

      have(P(x) /\ P(y) /\ !(x === y) |- ∃(x, P(x)) /\ !(∃!(z, P(z)))) by Tautology.from(ex, uex)
      thenHave(∃(y, P(x) /\ P(y) /\ !(x === y)) |- ∃(x, P(x)) /\ !(∃!(z, P(z)))) by LeftExists
      thenHave(∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))) |- ∃(x, P(x)) /\ !(∃!(z, P(z)))) by LeftExists
    }

    have(thesis) by Tautology.from(forward, backward)
  }

  val onePointRule = Theorem(
    ∃(x, (x === y) /\ Q(x)) <=> Q(y)
  ) {
    val s1 = have(∃(x, (x === y) /\ Q(x)) ==> Q(y)) subproof {
      assume(∃(x, (x === y) /\ Q(x)))
      val ex = witness(lastStep)
      val s1 = have(Q(ex)) by Tautology.from(ex.definition)
      val s2 = have(ex === y) by Tautology.from(ex.definition)
      have(Q(y)) by Substitution.ApplyRules(s2)(s1)
    }
    val s2 = have(Q(y) ==> ∃(x, (x === y) /\ Q(x))) subproof {
      assume(Q(y))
      thenHave((y === y) /\ Q(y)) by Restate
      thenHave(∃(x, (x === y) /\ Q(x))) by RightExists
    }
    have(thesis) by Tautology.from(s1, s2)
  }

  val existenceAndUniqueness = Theorem(
    (∃(y, P(y)), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- ∃!(x, P(x)) 
  ) {
    val forward = have((P(y), P(x) /\ P(y) ==> (x === y)) |- P(x) ==> (x === y)) by Restate
    have(P(y) |- P(y)) by Hypothesis
    thenHave((x === y, P(y)) |- P(x)) by RightSubstEq.withParametersSimple(List((y, x)), lambda(y, P(y)))
    val backward = thenHave(P(y) |- (x === y) ==> P(x)) by RightImplies
    have((P(y), P(x) /\ P(y) ==> (x === y)) |- (x === y) <=> P(x)) by RightIff(forward, backward)
    thenHave((P(y), ∀(y, P(x) /\ P(y) ==> (x === y))) |- (x === y) <=> P(x)) by LeftForall 
    thenHave((P(y), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- (x === y) <=> P(x)) by LeftForall
    thenHave((P(y), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- ∀(x, (x === y) <=> P(x))) by RightForall
    thenHave((P(y), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- ∃(y, ∀(x, (x === y) <=> P(x)))) by RightExists
    thenHave(thesis) by LeftExists
  }

  val existsOneEquality = Theorem(
    ∃!(x, x === y)
  ) {
    have(y === y) by RightRefl
    val existence = thenHave(∃(x, x === y)) by RightExists

    have(((x === y) /\ (z === y)) ==> (x === z)) by Restate.from(equalityTransitivity)
    thenHave(∀(z, (x === y) /\ (z === y) ==> (x === z))) by RightForall
    thenHave(∀(x, ∀(z, (x === y) /\ (z === y) ==> (x === z)))) by RightForall
    have(∃(x, x === y) |- ∃!(x, x === y)) by Cut(lastStep, existenceAndUniqueness of (P := lambda(x, x === y)))
    have(thesis) by Cut(existence, lastStep)
  }

  val existsCases = Theorem(
    (q ==> ∃(x, P(x)), !q ==> ∃(x, Q(x))) |- ∃(x, (q ==> P(x)) /\ (!q ==> Q(x)))
  ) {
    have(thesis) by Tableau
  }

  val existsOneCases = Theorem(
    (q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x))) |- ∃!(x, (q ==> P(x)) /\ (!q ==> Q(x)))
  ) {
    val existenceLeft = have(q ==> ∃!(x, P(x)) |- q ==> ∃(x, P(x))) by Tautology.from(existsOneImpliesExists)
    val existenceRight = existenceLeft of (q := !q, P := Q)
    have((q ==> ∃!(x, P(x)), !q ==> ∃(x, Q(x))) |- ∃(x, (q ==> P(x)) /\ (!q ==> Q(x)))) by Cut(existenceLeft, existsCases)
    val existence = have((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x))) |- ∃(x, (q ==> P(x)) /\ (!q ==> Q(x)))) by Cut(existenceRight, lastStep) 

    val uniquenessLeft = have((q ==> ∃!(x, P(x)), q ==> P(x), q ==> P(y)) |- q ==> (x === y)) by Tautology.from(existsOneImpliesUniqueness)
    val uniquenessRight = uniquenessLeft of (q := !q, P := Q)
    have((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x)), q ==> P(x), q ==> P(y), !q ==> Q(x), !q ==> Q(y)) |- (q ==> (x === y)) /\ (!q ==> (x === y))) by RightAnd(uniquenessLeft, uniquenessRight)
    thenHave((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x))) |- (((q ==> P(x)) /\ (!q ==> Q(x))) /\ ((q ==> P(y)) /\ (!q ==> Q(y)))) ==> (x === y)) by Tautology
    thenHave((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x))) |- ∀(y, (((q ==> P(x)) /\ (!q ==> Q(x))) /\ ((q ==> P(y)) /\ (!q ==> Q(y)))) ==> (x === y))) by RightForall
    thenHave((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x))) |- ∀(x, ∀(y, (((q ==> P(x)) /\ (!q ==> Q(x))) /\ ((q ==> P(y)) /\ (!q ==> Q(y)))) ==> (x === y)))) by RightForall
    have((q ==> ∃!(x, P(x)), !q ==> ∃!(x, Q(x)), ∃(x, (q ==> P(x)) /\ (!q ==> Q(x)))) |- ∃!(x, (q ==> P(x)) /\ (!q ==> Q(x)))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(x, (q ==> P(x)) /\ (!q ==> Q(x)))))
    have(thesis) by Cut(existence, lastStep)
  }
}
