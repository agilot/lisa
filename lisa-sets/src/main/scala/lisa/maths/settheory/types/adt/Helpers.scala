package lisa.maths.settheory.types.adt


/**
  * Tactic that proves every goal of the form:
  *
  * ` ... |- ..., ∀x1, ..., xn. P(x), ...`
  * 
  * ` ..., ∀x1, ..., xn . P(x), ... |- ...`
  * 
  * ` ... |- ..., ∃x1, ..., xn. P(x), ...`
  * 
  * ` ..., ∃x1, ..., xn . P(x), ... |- ...`
  * 
  * given a proof of the sequents without quantification.
  */
object QuantifiersIntro extends lisa.prooflib.ProofTacticLib.ProofTactic {

  import lisa.prooflib.SimpleDeducedSteps.Restate
  import lisa.prooflib.BasicStepTactic.*
  import lisa.fol.FOL.*

  /**
    * Executes the tactic on a specific goal.
    *
    * @param lib the library that is currently being used
    * @param proof the ongoing proof in which the tactic is called
    * @param vars the variables that needs to be quantified
    * @param fact the proof of the sequent without quantification
    * @param bot the statement to prove
    */
  def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)(vars: Seq[Variable])(fact: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
    TacticSubproof { sp ?=>
      if vars.isEmpty then
        lib.have(bot) by Restate.from(fact)
      else
        val diff: Sequent = bot -- fact.statement

        diff match
          case Sequent(s, _) if s.size == 1 =>
            val diffRest = bot.left -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.left -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(_, s) if s.size == 1 =>
            val diffRest = bot.right -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.right -- diffRest).head
            f match
              case BinderFormula(Forall, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = forall(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = exists(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(s1, s2) if s1.isEmpty && s2.isEmpty => lib.have(bot) by Restate.from(fact)
          case _ => return proof.InvalidProofTactic("Two or more formulas in the sequent have changed.")

          
    }  
}

/**
 * General purpose helpers.
 */
private [adt] object Helpers {

  import lisa.fol.FOL.{*, given}

  /**
    * Benchmarks a block of code.
    *
    * @param name the name of the benchmark
    * @param f the block of code to benchmark
    * @return the result of the block of code and prints how long it took to execute
    */
  def benchmark[T](using name: sourcecode.Name)(f: => T): T = {
    val before = System.nanoTime

    val res = f

    val totalTime = (System.nanoTime - before) / 1000000

    println(s"${name.value} time: $totalTime ms")

    res
  }

  /**
    * Exception thrown when code that should not be accessed is reached.
    */
  object UnreachableException extends Exception("This code should not be accessed. If you see this message, please report it to the library maintainers.")

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************

  val A = variable
  val B = variable

  val a = variable
  val b = variable
  val c = variable
  val d = variable

  val f = variable
  val g = variable
  val h = variable

  val n = variable
  val m = variable

  val p = formulaVariable
  val p1 = formulaVariable
  val p2 = formulaVariable
  val p3 = formulaVariable
  val p4 = formulaVariable

  val q1 = formulaVariable
  val q2 = formulaVariable

  val r = variable
  val r1 = variable
  val r2 = variable
  val s = variable
  val t = variable

  val x = variable
  val y = variable
  val z = variable

  val Q = predicate[1]
  val P = predicate[1]
  val P2 = predicate[2]
  val F = predicate[2]
  val schemPred = predicate[1]

  /**
   * Formula representing whether two sequences of terms are pairwise equal.
   *
   * @param s2 the sequence to compare with
   */
  extension (s1: Seq[Term]) def ===+(s2: Seq[Term]): Formula = /\+(s1.zip(s2).map(_ === _))

  /**
   * Disjunction of a sequence of formulas.
   *
   * @param s the formulas to which the disjunction is applied
   */
  def \/+(s: Iterable[Formula]): Formula =
    if s.isEmpty then False
    else s.fold(False)(_ \/ _)

  /**
   * Conjunction of a sequence of formulas.
   *
   * @param s the formulas to which the conjunction is applied
   */
  def /\+(s: Iterable[Formula]): Formula =
    if s.isEmpty then True
    else s.fold(True)(_ /\ _)

  /**
   * Repeats existential quantification over a sequence of variables.
   *
   * @param vars the variables to quantify over
   * @param f the formula to which the quantifiers are applied
   * @return the quantified formula
   */
  def existsSeq(vars: Seq[Variable], f: Formula): Formula =
    vars.foldRight(f)(exists(_, _))

  /**
   * Repeats universal quantification over a sequence of variables.
   *
   * @param vars the variables to quantify over
   * @param f the formula to which the quantifiers are applied
   * @return the quantified formula
   */
  def forallSeq(vars: Seq[Variable], f: Formula): Formula =
    vars.foldRight(f)(forall(_, _))

  /**
   * Simplifies a formula by removing True and False constants.
   *
   * @param f the formula to simplify
   */
  def simplify(f: Formula): Formula =
    f match
      case Or(False, phi) => simplify(phi)
      case Or(phi, False) => simplify(phi)
      case Or(phi, psi) => simplify(phi) \/ simplify(psi)
      case And(True, phi) => simplify(phi)
      case And(phi, True) => simplify(phi)
      case And(phi, psi) => simplify(phi) /\ simplify(psi)
      case Implies(True, phi) => simplify(phi)
      case Implies(phi, psi) => Implies(simplify(phi), simplify(psi))
      case _ => f


  /**
   * Picks fresh variables starting with a given prefix .
   * 
   * @param prefix the prefix of the fresh variables
   * @param size the number of fresh variables to output
   * @param assigned the variables that are already used
   * @param counter the index to append to the prefix
   * @param acc the variables that have already been generated by this method
   * 
   */
  def chooseVars(prefix: String, size: Int, assigned: Set[Variable] = Set.empty, counter: Int = 0, acc: Seq[Variable] = Seq.empty): Seq[Variable] =
    if size == 0 then 
      acc
    else
      val newVar = Variable(s"${prefix}${counter}")
      if assigned.contains(newVar) then
        chooseVars(prefix, size, assigned, counter + 1, acc)
      else 
        chooseVars(prefix, size - 1, assigned, counter + 1, acc :+ newVar)


}

/**
  * Definitions and helper functions for ADT.
  */
private[adt] object ADTDefinitions extends lisa.Main {

  import lisa.maths.settheory.SetTheory.*
  import lisa.maths.settheory.Relations.*
  import lisa.maths.settheory.types.TypeSystem.*
  import lisa.maths.settheory.types.TypeLib.{|=>}
  import Helpers.*
  import lisa.maths.settheory.orderings.Ordinals.{successor}

  /**
   * The specification of a constructor can either contain terms or a self reference, i.e. a reference to the ADT itself.
   */
  sealed trait ConstructorArgument {
    /**
     * Returns the term associated to a constructor argument, or in case it is a self reference, returns the term associated to the ADT.
     *
     * @param arg the constructor argument
     * @param adt the term representing the ADT
     */
    def getOrElse(adt: Term): Term =
      this match {
        case Self => adt
        case GroundType(term) => term
        case FunctionType(from, to) => from |=> to.getOrElse(adt)
      }
    
    /**
      * Substitutes the type variables of a constructor argument.
      * 
      * @param p the substitution pairs
      */
    def substitute(p: SubstPair*): ConstructorArgument = 
      this match
        case Self => Self
        case GroundType(t) => GroundType(t.substitute(p *))
        case FunctionType(from, to) => FunctionType(from.substitute(p *), to.substitute(p *))
  }
  
  /**
   * A symbol for self reference
   */
  case object Self extends ConstructorArgument

  /**
    * Syntactic represenation of a term
    *
    * @param t the underlying term
    */
  case class GroundType(t: Term) extends ConstructorArgument

  /**
   * Syntactic representation of a function from a term to another type
   * 
   * @param from the domain of this function
   * @param to the type of the codomain of this function
   */
  case class FunctionType(from: Term, to: ConstructorArgument) extends ConstructorArgument {

    val domains: List[Term] = to match
      case Self => List(from)
      case GroundType(t) => throw IllegalArgumentException("A function type cannot have a ground type as codomain")
      case f: FunctionType => from :: f.domains
    
    val variables = for i <- 0 until domains.size yield Variable(s"z${i}")

    val signature = variables.zip(domains)
    
    val wellTypedDomains = wellTypedFormula(signature)
    

    val monotonicity: THM = Lemma(subset(y, z) |- subset(getOrElse(y), getOrElse(z))) {
      to match
        case Self => 
          have(thesis) by Restate.from(ADTHelperTheorems.functionSpaceRightMonotonic of (x := from))
        case GroundType(t) =>
          have(thesis) by Restate.from(subsetReflexivity of (x := getOrElse(y)))
        case f: FunctionType =>
          have(thesis) by Cut(
            f.monotonicity,
            ADTHelperTheorems.functionSpaceRightMonotonic of (x := from, y := f.getOrElse(y), z := f.getOrElse(z))
          )
      
    }

  }

  /**
   * Shorthand for the union of the range of a function.
   *
   * @param f the function
   */
  def unionRange(f: Term) = union(relationRange(f))

  /**
   * Shorthand for the range of a restricted function.
   *
   * @param f the function
   * @param n the domain to which the function is restricted
   */
  def restrRange(f: Term, n: Term) = relationRange(domainRestriction(f, n))

  /**
   * Applies a sequence of arguments to a function.
   *
   * @param f the function
   * @param args the arguments to apply
   */
  def appSeq(f: Term)(args: Seq[Term]): Term = args.foldLeft(f)(_ * _)

  /**
   * Converts an integer to the associated ordinal.
   *
   * @param n the integer to convert
   */
  def toTerm(n: Int): Term =
    require(n >= 0, "n must be a non-negative integer")
    if n == 0 then emptySet
    else successor(toTerm(n - 1))

  /**
    * Returns a sequence of formulas asserting that all terms of a sequence are well-typed. 
    *
    * @param s the terms and their respective types
    */
  def wellTyped(s: Seq[(Term, Term)]): Seq[Formula] = s.map(_ :: _)

    /**
    * Returns a sequence of formulas asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTyped(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Seq[Formula] = s.map((t, arg) => t :: arg.getOrElse(orElse))

  /**
   * Returns a set of formulas asserting that all terms of a sequence are well-typed. 
   * 
   * @param s the terms and their respective types
   */
  def wellTypedSet(s: Seq[(Term, Term)]): Set[Formula] = wellTyped(s).toSet

    /**
    * Returns a set of formulas asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTypedSet(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Set[Formula] = wellTyped(s)(orElse).toSet

  /**
   * Returns a formula asserting that all terms of a sequence are well-typed. 
   * 
   * @param s the terms and their respective types
   */
  def wellTypedFormula(s: Seq[(Term, Term)]): Formula = /\+(wellTyped(s))

  /**
    * Returns a formula asserting that all terms of a sequence are well-typed with respect to the
    * specification of a constructor. 
    *
    * @param s the terms and their respective type
    * @param orElse the term to use in case of a self reference
    */
  def wellTypedFormula(s: Seq[(Term, ConstructorArgument)])(orElse: Term): Formula = /\+ (wellTyped(s)(orElse))

}


/**
 * List of external set theoretic theorems needed for proofs about ADT.
 * Some of these theorems are not yet implemented in the library and
 * will be added in the future.
 */
private [adt] object ADTHelperTheorems extends lisa.Main {

  import lisa.maths.settheory.SetTheory.*
  import lisa.maths.settheory.Relations.*
  import lisa.maths.settheory.Functions.*
  import lisa.maths.Quantifiers.*
  import ADTDefinitions.*
  import Helpers.*
  import lisa.maths.settheory.types.TypeLib.{|=>}
  import lisa.maths.settheory.orderings.Ordinals.*
  //import lisa.maths.Quantifiers.*

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************

  /**
   * Lemma --- Transitivity of equivalence.
   */
  val equivalenceRewriting = Lemma((p1 <=> p2, p2 <=> p3) |- p1 <=> p3) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Modus ponens for equivalence.
   */
  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Top level existential quantifiers can be swapped.
   */
  val existentialSwap = Lemma(∃(x, ∃(y, P2(x, y))) <=> ∃(y, ∃(x, P2(x, y)))) {
    have(thesis) by Tableau
  }

  /**
   * Lemma --- Modus ponens for reversed equivalence.
   */
  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If a statement is equivalent to the conjunction of two other statements, and one of them is true, then it can be removed from the equivalence.
   */
  val equivalenceAnd = Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding a disjunction on their right side preserves the equivalence.
   */
  val rightAndEquivalence = Lemma(p1 <=> p2 |- (p1 /\ p) <=> (p2 /\ p)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding an implication on their left side preserves the equivalence.
   */
  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- If two formulas are equivalent then adding an implication on their left side preserves the equivalence.
   */
  val leftImpliesEquivalenceWeak = Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

  /**
   * Lemma --- Implication distributes over equivalence.
   */
  val leftImpliesEquivalenceStrong = Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2)) {
    have(thesis) by Tautology
  }

  // ************
  // * ORDINALS *
  // ************



  val successorOrdinal = DEF(n) --> ordinal(n) /\ exists(m, n === successor(m))
  val nonsuccessorOrdinal = DEF(n) --> ordinal(n) /\ !exists(m, n === successor(m))
  val limitOrdinal = DEF(n) --> nonsuccessorOrdinal(n) /\ !(n === emptySet)



  val successorOrdinalIsOrdinal = Lemma(successorOrdinal(n) |- ordinal(n)) {
    sorry
  }

  val nonsuccessorOrdinalIsOrdinal = Lemma(nonsuccessorOrdinal(n) |- ordinal(n)) {
    sorry
  }

  val limitOrdinalIsOrdinal = Lemma(limitOrdinal(n) |- ordinal(n)) {
    sorry
  }

  val nonsuccessorOrdinalIsNotSuccessorOrdinal = Lemma((ordinal(n), nonsuccessorOrdinal(n)) |- !successorOrdinal(n)) {
    sorry
  }

  val successorIsOrdinalImpliesOrdinal = Lemma(ordinal(successor(n)) |- ordinal(n)) {
    sorry
  }

  val successorIsSuccessorOrdinal = Lemma(ordinal(n) |- successorOrdinal(successor(n))) {
    sorry
  }
  
  val successorIsSuccessorOrdinal2 = Lemma(ordinal(successor(n)) |- successorOrdinal(successor(n))) {
    sorry
  }

  val nonsuccessorOrdinalIsInductive = Lemma((nonsuccessorOrdinal(n), in(m, n)) |- in(successor(m), n)) {
    sorry
  }

  val limitOrdinalIsInductive = Lemma((limitOrdinal(n), in(m, n)) |- in(successor(m), n)) {
    sorry
  }

  val leqOrdinal = Lemma((ordinal(n), subset(m, n)) |- in(m, n) \/ (m === n)) {
    sorry
  }

  val leqOrdinalDef = Lemma(ordinal(n) |- subset(m, n) <=> m ∈ successor(n)) {
    sorry
  }


  val intersectionInOrdinal = Lemma((ordinal(n), in(m, n)) |- m ∩ n === m) {
    sorry
  }

  val successorOrNonsuccessorOrdinal = Lemma(ordinal(n) |- successorOrdinal(n) \/ nonsuccessorOrdinal(n)) {
    sorry
  }



  // Natural numbers
  val N = Constant("N")
  addSymbol(N)

  val domainIsOrdinal = Axiom(ordinal(N))


  /**
   * Lemma --- 0 is a natural number.
   *
   *    `0 ∈ N`
   */
  val zeroIsNat = Lemma(in(emptySet, N)) {
    sorry
  }

  /**
   * Lemma --- The natural numbers are not empty.
   *
   *   `N != ∅`
   */
  val natNotEmpty = Lemma(N === emptySet |- ()) {
    have(!(N === emptySet)) by Cut(zeroIsNat, setWithElementNonEmpty of (y := emptySet, x := N))
  }

  /**
   * Lemma --- There exists a natural number.
   *
   *  `∃n ∈ N`
   */
  val existsNat = Lemma(exists(n, in(n, N))) {
    have(thesis) by RightExists(zeroIsNat)
  }

  /**
   * Lemma --- Successor is an injective function.
   *
   *   `n = m <=> n + 1 = m + 1`
   */
  val successorInjectivity = Lemma((n === m) <=> (successor(n) === successor(m))) {
    sorry
  }

  /**
   * Lemma --- A term is a natural number if and only if its successor is a natural number.
   *
   *  `n ∈ N <=> n + 1 ∈ N`
   */
  val successorIsNat = Lemma(in(n, N) |- in(successor(n), N)) {
    sorry
  }


  // *************
  // * FUNCTIONS *
  // *************


  val inRestrictedFunctionRange = Lemma((functional(f), in(x, d ∩ relationDomain(f))) |- in(app(f, x), relationRange(domainRestriction(f, d)))) {
    sorry
  }

  /**
   * Lemma --- If an element is in the image of a restricted function, then it has a preimage inside its domain.
   *
   *     `functional(f) |- y ⊆ Im(f) <=> ∃x ∈ d ∩ Dom(f). f|d(x) = y`
   */
  val restrictedFunctionRangeMembership = Lemma(functional(f) |- in(y, relationRange(domainRestriction(f, d))) <=> ∃(x, in(x, d ∩ relationDomain(f)) /\ (app(domainRestriction(f, d), x) === y))) {
    have(functional(f) |- in(y, relationRange(domainRestriction(f, d))) <=> ∃(x, in(x, relationDomain(domainRestriction(f, d))) /\ (app(domainRestriction(f, d), x) === y))) by Cut(
      domainRestrictionFunctional of (x := d),
      functionalRangeMembership of (f := domainRestriction(f, d), b := y)
    )
    thenHave(functional(f) |- in(y, relationRange(domainRestriction(f, d))) <=> ∃(x, in(x, d ∩ relationDomain(f)) /\ (app(domainRestriction(f, d), x) === y))) by Substitution.ApplyRules(
      domainRestrictionDomain of (x := d)
    )
  }

  /**
   * Lemma --- Characterization of the union of the range of a function.
   *
   *     `∪ Im(h) = {z | ∃n ∈ Dom(h). z ∈ h(n)}`
   */
  val unionRangeMembership = Lemma(functional(h) |- in(z, unionRange(h)) <=> exists(n, in(n, relationDomain(h)) /\ in(z, app(h, n)))) {
    val iffAfterAnd = have(functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)) /\ z ∈ y) by Cut(
      functionalRangeMembership of (f := h, b := y),
      rightAndEquivalence of (p1 := y ∈ relationRange(h), p2 := ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y)), p := z ∈ y)
    )
    have(functional(h) |- (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) by Apply(equivalenceRewriting).on(
      iffAfterAnd,
      existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ relationDomain(h) /\ (app(h, m) === y)), p := z ∈ y)
    )

    thenHave(functional(h) |- ∀(y, (y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))) by RightForall

    val beforeExSwap = have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P := lambda(y, y ∈ relationRange(h) /\ z ∈ y),
        Q := lambda(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y))
      )
    )

    have(∃(y, ∃(m, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) subproof {

      have(m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y <=> m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)) by Restate
      thenHave(forall(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y <=> m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) by RightForall
      have(∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=> ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y),
          Q := lambda(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))
        )
      )
      thenHave(forall(m, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y) <=> ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by RightForall
      have(∃(m, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(y, ∃(y, m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)),
          Q := lambda(y, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))
        )
      )
      have(thesis) by Apply(equivalenceRewriting).on(lastStep, existentialSwap of (P2 := lambda((y, m), m ∈ relationDomain(h) /\ (app(h, m) === y) /\ z ∈ y)))
    }

    val introM =
      have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) by Apply(equivalenceRewriting).on(beforeExSwap, lastStep)

    have(
      ∀(m, (∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))) <=> (m ∈ relationDomain(h) /\ z ∈ app(h, m)))
    ) by RightForall(equalityInExistentialQuantifier of (P := lambda(y, m ∈ relationDomain(h) /\ z ∈ y), y := app(h, m)))

    have(
      ∃(m, (∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y)))) <=> ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
    ) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P := lambda(m, ∃(y, m ∈ relationDomain(h) /\ z ∈ y /\ (app(h, m) === y))),
        Q := lambda(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))
      )
    )

    have(functional(h) |- ∃(y, y ∈ relationRange(h) /\ z ∈ y) <=> ∃(m, m ∈ relationDomain(h) /\ z ∈ app(h, m))) by Apply(equivalenceRewriting).on(
      introM,
      lastStep
    )

    have(thesis) by Apply(equivalenceRewriting).on(
      lastStep,
      unionAxiom.asInstanceOf
    )
  }

  // *************
  // * EMPTYNESS *
  // *************


  /**
   * Lemma --- Restricting the domain of a function to the empty set yields the empty set.
   *
   *     `h|∅ = ∅`
   */
  val restrictedFunctionEmptyDomain = Lemma(domainRestriction(h, emptySet) === emptySet) {
    sorry
  }

  /**
   * Lemma --- If the domain of a function is non empty, then the function is non empty as well.
   *
   *     `Dom(h) != ∅ |- h != ∅`
   */
  val nonEmptyDomain = Lemma(!(relationDomain(h) === emptySet) |- !(h === emptySet)) {
    sorry
  }

  /**
   * Lemma --- A superset of a non empty set is non empty.
   *
   *     `x ⊆ y, x != ∅ |- y != ∅`
   */
  val subsetNotEmpty = Lemma((subset(x, y), !(x === emptySet)) |- !(y === emptySet)) {
    val subst = have(y === emptySet |- y === emptySet) by Hypothesis
    have((subset(x, emptySet), y === emptySet) |- (x === emptySet)) by Apply(equivalenceApply of (p1 := subset(x, emptySet))).on(emptySetIsItsOwnOnlySubset.asInstanceOf)
    thenHave((subset(x, y), y === emptySet) |- (x === emptySet)) by Substitution.ApplyRules(subst)
  }


  /**
   * Lemma --- The range of the empty function is empty.
   *
   *     `Im(∅) = ∅`
   */
  val unionRangeEmpty = Lemma(unionRange(emptySet) === emptySet) {
    have(unionRange(emptySet) === unionRange(emptySet)) by RightRefl
    thenHave(unionRange(emptySet) === union(emptySet)) by Substitution.ApplyRules(rangeEmpty)
    thenHave(thesis) by Substitution.ApplyRules(unionEmpty)
  }

  /**
   * Lemma --- If a function and a domain are non empty, then restricting this function to this
   * domain yields a non empty set.
   *
   *    `h != ∅, d != ∅ |- h|d != ∅`
   */
  val restrictedFunctionNotEmpty = Lemma((!(h === emptySet), !(d === emptySet)) |- !(domainRestriction(h, d) === emptySet)) {
    sorry
  }

  // ****************
  // * MONOTONICITY *
  // ****************

  /**
   * Lemma --- Function spaces are monotonic on the right.
   *
   *     `y ⊆ z |- x |=> y ⊆ x |=> z`
   */
  val functionSpaceRightMonotonic = Lemma(subset(y, z) |- subset(x |=> y, x |=> z)) {
    sorry
  }

  /**
   * Lemma --- Union is a monotonic operation with respect to set inclusion.
   *
   *     `x ⊆ y |- ∪ x ⊆ ∪ y`
   */
  val unionMonotonic = Lemma(subset(x, y) |- subset(union(x), union(y))) {
    sorry
  }


  /**
   * Lemma --- The union of the range is a monotonic operation with respect to set inclusion.
   *
   *     `f ⊆ g |- ∪ Im(f) ⊆ ∪ Im(g)`
   */
  val unionRangeMonotonic = Lemma(subset(f, g) |- subset(unionRange(f), unionRange(g))) {
    have(thesis) by Apply(unionMonotonic).on(relationRangeSubset of (r1 := f, r2 := g))
  }

  /**
   * Lemma --- If two implications are true then disjuncting on both sides is also a valid implication.
   */
  val disjunctionsImplies = Lemma((p1 ==> p2, q1 ==> q2) |- (p1 \/ q1) ==> (p2 \/ q2)) {

    val right = have((p1 ==> p2, q1 ==> q2, p1) |- p2 \/ q2) by Restate
    val left = have((p1 ==> p2, q1 ==> q2, q1) |- p2 \/ q2) by Restate

    have((p1 ==> p2, q1 ==> q2, p1 \/ q1) |- p2 \/ q2) by LeftOr(left, right)
  }

  /**
   * Lemma --- If a class function F (whose representation is P) is monotonic then with respect to set inclusion, then S -> F(S) ∪ S is also
   * a monotonic function.
   *
   *      `s ⊆ t, F(s) ⊆ F(t) |- F(s) ∪ s ⊆ F(t) ∪ t`
   */
  val unionPreimageMonotonic = Lemma((subset(s, t), P(s) ==> P(t)) |- (P(s) \/ in(x, s)) ==> (P(t) \/ in(x, t))) {
    have(subset(s, t) |- forall(z, in(z, s) ==> in(z, t))) by Cut(
      subsetAxiom of (x := s, y := t),
      equivalenceApply of (p1 := subset(s, t), p2 := forall(z, in(z, s) ==> in(z, t)))
    )
    thenHave(subset(s, t) |- in(x, s) ==> in(x, t)) by InstantiateForall(x)
    have(thesis) by Cut(lastStep, disjunctionsImplies of (p1 := in(x, s), p2 := in(x, t), q1 := P(s), q2 := P(t)))
  }

  /**
   * Lemma --- Resticting a function to a smaller domain yields a subset of the original function.
   *
   *     `x ⊆ y |- f|x ⊆ f|y`
   */
  val restrictedFunctionDomainMonotonic = Lemma(subset(x, y) |- subset(domainRestriction(f, x), domainRestriction(f, y))) {
    sorry
  }

  // *******************
  // * SPECIFIC LEMMAS *
  // *******************


  /**
   * Lemma --- Characterization of the union of the range of a monotonic function restricted to the successor of a natural number.
   *
   *     `monotonic(h) and Dom(h) = N |- ∪ Im(h|n + 1) = h(n)`
   */
  val unionRangeCumulativeRestrictedFunction =
    Lemma((functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h)), ∀(m, subset(m, n) ==> subset(app(h, m), app(h, n)))) |- unionRange(domainRestriction(h, successor(n))) === app(h, n)) {

      have(functional(h) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, m ∈ (successor(n) ∩ relationDomain(h)) /\ (app(domainRestriction(h, successor(n)), m) === y)) /\ z ∈ y) by Cut(
        restrictedFunctionRangeMembership of (f := h, d := successor(n)),
        rightAndEquivalence of (p1 := y ∈ restrRange(h, successor(n)), p2 := ∃(m, m ∈ (successor(n) ∩ relationDomain(h)) /\ (app(domainRestriction(h, successor(n)), m) === y)), p := z ∈ y)
      )

      thenHave(
        (functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> 
        ∃(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y)) /\ z ∈ y
      ) by Substitution.ApplyRules(intersectionInOrdinal of (m := successor(n), n := relationDomain(h)))

      thenHave(
        (functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> 
        ∃(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y) /\ z ∈ y)
      ) by Substitution.ApplyRules(existentialConjunctionWithClosedFormula of (P := lambda(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y)), p := z ∈ y)
      )

      thenHave(
        (functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- ∀(y, (y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> 
        ∃(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y) /\ z ∈ y))
      ) by RightForall

      have(
        (functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> 
        ∃(y, ∃(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y) /\ z ∈ y))
      ) by Cut(
        lastStep, existentialEquivalenceDistribution of (
          P := lambda(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y),
          Q := lambda(y, ∃(m, m ∈ successor(n) /\ (app(domainRestriction(h, successor(n)), m) === y) /\ z ∈ y))
        )
      )

      val introM =
        thenHave(
          (functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> 
          ∃(m, ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y)))
        ) by Tableau

      have((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(domainRestriction(h, successor(n)), m))) by Exact(
        equalityInExistentialQuantifier of (P := lambda(y, m ∈ successor(n) /\ z ∈ y))
      )

      thenHave(m ∈ successor(n) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(h, m))) by Substitution.ApplyRules(restrictedFunctionApplication)
      thenHave((∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))) <=> (m ∈ successor(n) /\ z ∈ app(h, m))) by Tableau
      thenHave(ordinal(n) |- (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))) <=> (subset(m, n) /\ z ∈ app(h, m))) by Substitution.ApplyRules(leqOrdinalDef)

      thenHave(ordinal(n) |- ∀(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))) <=> (subset(m, n) /\ z ∈ app(h, m)))) by RightForall

      have(ordinal(n) |- ∃(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y)))) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (
          P := lambda(m, ∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))),
          Q := lambda(m, subset(m, n) /\ z ∈ app(h, m))
        )
      )

      thenHave((ordinal(n), ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y))))) |- 
        ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by RightSubstIff.withParametersSimple(
          List((∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y), ∃(m, (∃(y, m ∈ successor(n) /\ z ∈ y /\ (app(domainRestriction(h, successor(n)), m) === y)))))),
          lambda(p, p <=> ∃(m, subset(m, n) /\ z ∈ app(h, m)))
        )

      have((functional(h), ordinal(n), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- 
        ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Cut(introM, lastStep)

      have((functional(h), ordinal(successor(n)), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- 
        ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Cut(successorIsOrdinalImpliesOrdinal, lastStep)
      have((functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- 
        ∃(y, y ∈ restrRange(h, successor(n)) /\ z ∈ y) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Cut(elementsOfOrdinalsAreOrdinals of (b := successor(n), a := relationDomain(h)), lastStep)

      val unionIsExists =
        thenHave((functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h))) |- z ∈ unionRange(domainRestriction(h, successor(n))) <=> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by Substitution.ApplyRules(unionAxiom of (x := restrRange(h, successor(n))))

      val monotonicity = ∀(m, subset(m, n) ==> subset(app(h, m), app(h, n)))

      have(monotonicity |- ∃(m, subset(m, n) /\ z ∈ app(h, m)) <=> z ∈ app(h, n)) subproof {
        have(z ∈ app(h, n) |- z ∈ app(h, n)) by Hypothesis
        have(z ∈ app(h, n) |- subset(n, n) /\ z ∈ app(h, n)) by RightAnd(lastStep, subsetReflexivity of (x := n))
        thenHave(z ∈ app(h, n) |- ∃(m, subset(m, n) /\ z ∈ app(h, m))) by RightExists
        val backward = thenHave(z ∈ app(h, n) ==> ∃(m, subset(m, n) /\ z ∈ app(h, m))) by RightImplies

        have(monotonicity |- monotonicity) by Hypothesis
        thenHave((monotonicity, subset(m, n)) |- subset(app(h, m), app(h, n))) by InstantiateForall(m)
        have((monotonicity, subset(m, n), z ∈ app(h, m)) |- z ∈ app(h, n)) by Cut(lastStep,subsetElim of (x := app(h, m), y := app(h, n)))
        thenHave((monotonicity, subset(m, n) /\ z ∈ app(h, m)) |- z ∈ app(h, n)) by LeftAnd
        thenHave((monotonicity, ∃(m, subset(m, n) /\ z ∈ app(h, m))) |- z ∈ app(h, n)) by LeftExists
        val forward = thenHave(monotonicity |- ∃(m, subset(m, n) /\ z ∈ app(h, m)) ==> z ∈ app(h, n)) by RightImplies

        have(thesis) by RightIff(forward, backward)
      }

      have((functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h)), monotonicity) |- (z ∈ unionRange(domainRestriction(h, successor(n)))) <=> z ∈ app(h, n)) by Substitution.ApplyRules(lastStep)(unionIsExists)
      thenHave((functional(h), ordinal(relationDomain(h)), in(successor(n), relationDomain(h)), monotonicity) |- ∀(z, z ∈ unionRange(domainRestriction(h, successor(n))) <=> z ∈ app(h, n))) by RightForall
      have(thesis) by Cut(lastStep, equalityIntro of (x := unionRange(domainRestriction(h, successor(n))), y := app(h, n)))
    }

  def fixpointClassFunction(h: Term)(c: PredicateLabel[2]) =
    functional(h) /\ ordinal(relationDomain(h)) /\ 
    forall(n, in(n, relationDomain(h)) ==> 
      forall(x, in(x, app(h, n)) <=> 
        ((successorOrdinal(n) ==> c(x, unionRange(domainRestriction(h, n)))) /\
        (!successorOrdinal(n) ==> in(x, unionRange(domainRestriction(h, n)))))
      )
    )

  def classFunctionCumulative(c: PredicateLabel[2]) = forall(n, forall(x, in(x, n) ==> c(x, n)))
  def classFunctionMonotonic(c: PredicateLabel[2]) = forall(m, forall(n, subset(m, n) ==> forall(x, c(x, m) ==> c(x, n))))

  val inFixpointFunctionDomain = Lemma((fixpointClassFunction(h)(P2), in(n, relationDomain(h))) |- ordinal(n)) {
    sorry
  }

  val subsetElemFixpointFunctionDomain = Lemma((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n)) |- in(m,  relationDomain(h))) {
      sorry
  }

  val successorElemFixpointFunctionDomain = Lemma((fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- in(n,  relationDomain(h))) {
      sorry
  }


  val fixpointFunctionSuccessorUnfold = Lemma((fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- in(x, app(h, successor(n))) <=> P2(x, unionRange(domainRestriction(h, successor(n))))) {

    // Caching
    def funBody(n: Term) = in(x, app(h, n)) <=> 
      ((successorOrdinal(n) ==> P2(x, unionRange(domainRestriction(h, n)))) /\
      (!successorOrdinal(n) ==> in(x, unionRange(domainRestriction(h, n)))))
    val funBodySucc = funBody(successor(n))
    val funApplicationDef = forall(n, in(n, relationDomain(h)) ==> forall(x, funBody(n)))

    // Nothing fancy, just instantiations and restates
    have(funApplicationDef |- funApplicationDef) by Hypothesis 
    thenHave((funApplicationDef, in(successor(n), relationDomain(h))) |- forall(x, funBodySucc)) by InstantiateForall(successor(n))
    thenHave((funApplicationDef, in(successor(n), relationDomain(h))) |- funBodySucc) by InstantiateForall(x)
    thenHave((fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h)), successorOrdinal(successor(n))) |- in(x, app(h, successor(n))) <=> P2(x, unionRange(domainRestriction(h, successor(n))))) by Tautology
    have((fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h)), ordinal(successor(n))) |- in(x, app(h, successor(n))) <=> P2(x, unionRange(domainRestriction(h, successor(n))))) by Cut(successorIsSuccessorOrdinal2, lastStep)
    have(thesis) by Cut(inFixpointFunctionDomain of (n := successor(n)), lastStep)
  }

  val fixpointFunctionNonsuccessorUnfold = Lemma((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- app(h, n) === unionRange(domainRestriction(h, n))) {

    // Caching
    def funBody = in(x, app(h, n)) <=> 
      ((successorOrdinal(n) ==> P2(x, unionRange(domainRestriction(h, n)))) /\
      (!successorOrdinal(n) ==> in(x, unionRange(domainRestriction(h, n)))))
    val funApplicationDef = forall(n, in(n, relationDomain(h)) ==> forall(x, funBody))

    // Nothing fancy, just instantiations and restates
    have(funApplicationDef |- funApplicationDef) by Hypothesis
    thenHave((funApplicationDef, in(n, relationDomain(h))) |- forall(x, funBody)) by InstantiateForall(n)
    thenHave((funApplicationDef, in(n, relationDomain(h))) |- funBody) by InstantiateForall(x)
    thenHave((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), !successorOrdinal(n)) |- in(x, app(h, n)) <=> in(x, unionRange(domainRestriction(h, n)))) by Tautology
    have((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), ordinal(n), nonsuccessorOrdinal(n)) |- in(x, app(h, n)) <=> in(x, unionRange(domainRestriction(h, n)))) by Cut(nonsuccessorOrdinalIsNotSuccessorOrdinal, lastStep)
    have((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- in(x, app(h, n)) <=> in(x, unionRange(domainRestriction(h, n)))) by Cut(inFixpointFunctionDomain, lastStep)
    thenHave((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- forall(x, in(x, app(h, n)) <=> in(x, unionRange(domainRestriction(h, n))))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := app(h, n), y := unionRange(domainRestriction(h, n))))
  }
  
  val fixpointFunctionMonotonicity = benchmark(Lemma((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n)) |- subset(app(h, m), app(h, n))) {

    val succCase = have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), successorOrdinal(n)) |- subset(app(h, m), app(h, n))) subproof {

      val unionRangeRestrMon = have(subset(m, n) |- subset(unionRange(domainRestriction(h, m)), unionRange(domainRestriction(h, n)))) by Cut(
          restrictedFunctionDomainMonotonic of (x := m, y := n, f := h), 
          unionRangeMonotonic of (f := domainRestriction(h, m), g := domainRestriction(h, n))
        )

      val succSuccCase = have((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), successorOrdinal(m)) |- subset(app(h, m), app(h, successor(b)))) subproof {

        have(classFunctionMonotonic(P2) |- classFunctionMonotonic(P2)) by Hypothesis
        
        thenHave(classFunctionMonotonic(P2) |- forall(n, subset(unionRange(domainRestriction(h, successor(a))), n) ==> forall(x, P2(x, unionRange(domainRestriction(h, successor(a)))) ==> P2(x, n)))) by InstantiateForall(unionRange(domainRestriction(h, successor(a))))
        
        thenHave(classFunctionMonotonic(P2) |- subset(unionRange(domainRestriction(h, successor(a))), unionRange(domainRestriction(h, successor(b)))) ==> forall(x, P2(x, unionRange(domainRestriction(h, successor(a)))) ==> P2(x, unionRange(domainRestriction(h, successor(b)))))) by InstantiateForall(unionRange(domainRestriction(h, successor(b))))

        thenHave((classFunctionMonotonic(P2), subset(unionRange(domainRestriction(h, successor(a))), unionRange(domainRestriction(h, successor(b))))) |- forall(x, P2(x, unionRange(domainRestriction(h, successor(a)))) ==> P2(x, unionRange(domainRestriction(h, successor(b)))))) by Restate

        have((classFunctionMonotonic(P2), subset(successor(a), successor(b))) |- forall(x, P2(x, unionRange(domainRestriction(h, successor(a)))) ==> P2(x, unionRange(domainRestriction(h, successor(b)))))) by Cut(unionRangeRestrMon of (m := successor(a), n := successor(b)), lastStep)

        thenHave((classFunctionMonotonic(P2), subset(successor(a), successor(b))) |- P2(x, unionRange(domainRestriction(h, successor(a)))) ==> P2(x, unionRange(domainRestriction(h, successor(b))))) by InstantiateForall(x)

        thenHave((classFunctionMonotonic(P2), subset(successor(a), successor(b)), in(x, app(h, successor(a))) <=> P2(x, unionRange(domainRestriction(h, successor(a))))) |- in(x, app(h, successor(a))) ==> P2(x, unionRange(domainRestriction(h, successor(b))))) by RightSubstIff.withParametersSimple(
          List((in(x, app(h, successor(a))), P2(x, unionRange(domainRestriction(h, successor(a)))))),
          lambda(p, p ==> P2(x, unionRange(domainRestriction(h, successor(b)))))
        )

        have((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(a), relationDomain(h)), subset(successor(a), successor(b))) |- in(x, app(h, successor(a))) ==> P2(x, unionRange(domainRestriction(h, successor(b))))) by Cut(fixpointFunctionSuccessorUnfold of (n := a), lastStep)

        thenHave((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(a), relationDomain(h)), subset(successor(a), successor(b)), in(x, app(h, successor(b))) <=> P2(x, unionRange(domainRestriction(h, successor(b))))) |- in(x, app(h, successor(a))) ==> in(x, app(h, successor(b)))) by 
        RightSubstIff.withParametersSimple(
          List((in(x, app(h, successor(b))), P2(x, unionRange(domainRestriction(h, successor(b)))))),
          lambda(p, in(x, app(h, successor(a))) ==> p)
        )

        have((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(a), relationDomain(h)), in(successor(b), relationDomain(h)), subset(successor(a), successor(b))) |- in(x, app(h, successor(a))) ==> in(x, app(h, successor(b)))) by 
        Cut(fixpointFunctionSuccessorUnfold of (n := b), lastStep) 

        thenHave((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(a), relationDomain(h)), in(successor(b), relationDomain(h)), subset(successor(a), successor(b))) |- forall(x, in(x, app(h, successor(a))) ==> in(x, app(h, successor(b))))) by RightForall

        have((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(a), relationDomain(h)), in(successor(b), relationDomain(h)), subset(successor(a), successor(b))) |- subset(app(h, successor(a)), app(h, successor(b)))) by Cut(lastStep, subsetIntro of (x := app(h, successor(a)), y := app(h, successor(b))))

        have((classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(successor(a), successor(b))) |- subset(app(h, successor(a)), app(h, successor(b)))) by Cut(subsetElemFixpointFunctionDomain of (m := successor(a), n := successor(b)), lastStep)

        thenHave((m === successor(a), classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(successor(a), successor(b))) |- subset(app(h, m), app(h, successor(b)))) by RightSubstEq.withParametersSimple(
          List((m, successor(a))),
          lambda(m , subset(app(h, m), app(h, successor(b))))
        )

        thenHave((m === successor(a), classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(app(h, m), app(h, successor(b)))) by LeftSubstEq.withParametersSimple(
          List((m, successor(a))),
          lambda(m, subset(m, successor(b)))
        )

        thenHave((exists(a, m === successor(a)), classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(app(h, m), app(h, successor(b)))) by LeftExists

        thenHave((ordinal(m) /\ exists(a, m === successor(a)), classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(app(h, m), app(h, successor(b)))) by Weakening

        thenHave((successorOrdinal(m) <=> ordinal(m) /\ exists(a, m === successor(a)), successorOrdinal(m), classFunctionMonotonic(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(app(h, m), app(h, successor(b)))) by LeftSubstIff.withParametersSimple(
          List((successorOrdinal(m), ordinal(m) /\ exists(a, m === successor(a)))),
          lambda(p, p)
        )

        have(thesis) by Cut(successorOrdinal.definition of (n := m), lastStep)

      }

      val succNonSuccCase = have((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), nonsuccessorOrdinal(m)) |- subset(app(h, m), app(h, successor(b)))) subproof {

        have(classFunctionCumulative(P2) |- classFunctionCumulative(P2)) by Hypothesis
        thenHave(classFunctionCumulative(P2) |- forall(x, in(x, unionRange(domainRestriction(h, successor(b)))) ==> P2(x, unionRange(domainRestriction(h, successor(b)))))) by InstantiateForall(unionRange(domainRestriction(h, successor(b))))
        thenHave((classFunctionCumulative(P2), in(x, unionRange(domainRestriction(h, successor(b))))) |- P2(x, unionRange(domainRestriction(h, successor(b))))) by InstantiateForall(x)
        thenHave((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), in(x, unionRange(domainRestriction(h, successor(b))))) |- in(x, app(h, successor(b)))) by Substitution.ApplyRules(fixpointFunctionSuccessorUnfold of (n := b))
        have((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(unionRange(domainRestriction(h, m)), unionRange(domainRestriction(h, successor(b)))), in(x, unionRange(domainRestriction(h, m)))) |- in(x, app(h, successor(b)))) by Cut(
          subsetElim of (x := unionRange(domainRestriction(h, m)), y := unionRange(domainRestriction(h, successor(b))), z := x),
          lastStep
        )
        have((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), in(x, unionRange(domainRestriction(h, m)))) |- in(x, app(h, successor(b)))) by Cut(unionRangeRestrMon of (n := successor(b)), lastStep)
        thenHave((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- in(x, unionRange(domainRestriction(h, m))) ==> in(x, app(h, successor(b)))) by RightImplies
        thenHave((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- forall(x, in(x, unionRange(domainRestriction(h, m))) ==> in(x, app(h, successor(b))))) by RightForall
        have((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(unionRange(domainRestriction(h, m)), app(h, successor(b)))) by Cut(lastStep, subsetIntro of (x := unionRange(domainRestriction(h, m)), y := app(h, successor(b))))
        thenHave((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), nonsuccessorOrdinal(m), in(m, relationDomain(h))) |- subset(app(h, m), app(h, successor(b)))) by Substitution.ApplyRules(fixpointFunctionNonsuccessorUnfold of (n := m))
        have((classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), nonsuccessorOrdinal(m)) |- subset(app(h, m), app(h, successor(b)))) by Cut(subsetElemFixpointFunctionDomain of (n := successor(b)), lastStep)
      }

      have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), successorOrdinal(m) \/ nonsuccessorOrdinal(m)) |- subset(app(h, m), app(h, successor(b)))) by LeftOr(succSuccCase, succNonSuccCase)

      have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), ordinal(m)) |- subset(app(h, m), app(h, successor(b)))) by Cut(successorOrNonsuccessorOrdinal of (n := m), lastStep)

      have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), in(m, relationDomain(h))) |- subset(app(h, m), app(h, successor(b)))) by Cut(inFixpointFunctionDomain of (n := m), lastStep)

      have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b))) |- subset(app(h, m), app(h, successor(b)))) by Cut(subsetElemFixpointFunctionDomain of (n := successor(b)), lastStep)

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, successor(b)), n === successor(b)) |- subset(app(h, m), app(h, n))) by RightSubstEq.withParametersSimple(
        List((n, successor(b))),
        lambda(n, subset(app(h, m), app(h, n)))
      )

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(b), relationDomain(h)), subset(m, n), n === successor(b)) |- subset(app(h, m), app(h, n))) by LeftSubstEq.withParametersSimple(
        List((n, successor(b))),
        lambda(n, subset(m, n))
      )

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), n === successor(b)) |- subset(app(h, m), app(h, n))) by LeftSubstEq.withParametersSimple(
        List((n, successor(b))),
        lambda(n, in(n, relationDomain(h)))
      )

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), exists(b, n === successor(b))) |- subset(app(h, m), app(h, n))) by LeftExists

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), ordinal(n) /\ exists(b, n === successor(b))) |- subset(app(h, m), app(h, n))) by Weakening

      thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), successorOrdinal(n) <=> ordinal(n) /\ exists(b, n === successor(b)), successorOrdinal(n)) |- subset(app(h, m), app(h, n))) by LeftSubstIff.withParametersSimple(
        List((successorOrdinal(n), ordinal(n) /\ exists(b, n === successor(b)))),
        lambda(p, p)
      )

      have(thesis) by Cut(successorOrdinal.definition, lastStep)
    }

    val nonSuccCase = have((fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), nonsuccessorOrdinal(n)) |- subset(app(h, m), app(h, n))) subproof {
      have((functional(h), in(m, n), n ∩ relationDomain(h) === n) |- in(app(h, m), relationRange(domainRestriction(h, n)))) by LeftSubstEq.withParametersSimple(
        List((n ∩ relationDomain(h), n)),
        lambda(s, in(m, s))
      )(inRestrictedFunctionRange of (f := h, x := m, d := n))

      have((ordinal(relationDomain(h)), functional(h), in(m, n), in(n, relationDomain(h))) |- in(app(h, m), relationRange(domainRestriction(h, n)))) by Cut(intersectionInOrdinal of (m := n, n := relationDomain(h)), lastStep)

      have((ordinal(relationDomain(h)), functional(h), in(m, n), in(n, relationDomain(h))) |- subset(app(h, m), unionRange(domainRestriction(h, n)))) by Cut(lastStep, inSetSubsetUnion of (x := app(h, m), y := relationRange(domainRestriction(h, n))))

      thenHave((fixpointClassFunction(h)(P2), in(m, n), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- subset(app(h, m), unionRange(domainRestriction(h, n)))) by Weakening

      thenHave((fixpointClassFunction(h)(P2), in(m, n), in(n, relationDomain(h)), nonsuccessorOrdinal(n), unionRange(domainRestriction(h, n)) === app(h, n)) |- subset(app(h, m), app(h, n))) by RightSubstEq.withParametersSimple(
        List((unionRange(domainRestriction(h, n)), app(h, n))),
        lambda(s, subset(app(h, m), s))
      )

      val nonSuccCaseIn = have((fixpointClassFunction(h)(P2), in(m, n), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- subset(app(h, m), app(h, n))) by Cut(fixpointFunctionNonsuccessorUnfold, lastStep)

      have(m === n |- subset(app(h, m), app(h, n))) by RightSubstEq.withParametersSimple(
        List((m, n)),
        lambda(s, subset(app(h, m), app(h, s)))
      )(subsetReflexivity of (x := app(h, m)))

      have((fixpointClassFunction(h)(P2), in(m, n) \/ (m === n), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- subset(app(h, m), app(h, n))) by LeftOr(nonSuccCaseIn, lastStep)
      have((fixpointClassFunction(h)(P2), ordinal(n), subset(m, n), in(n, relationDomain(h)), nonsuccessorOrdinal(n)) |- subset(app(h, m), app(h, n))) by Cut(leqOrdinal, lastStep)
      have(thesis) by Cut(nonsuccessorOrdinalIsOrdinal, lastStep)
    }

    have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), successorOrdinal(n) \/ nonsuccessorOrdinal(n)) |- subset(app(h, m), app(h, n))) by LeftOr(succCase, nonSuccCase)

    have((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h)), subset(m, n), ordinal(n)) |- subset(app(h, m), app(h, n))) by Cut(successorOrNonsuccessorOrdinal, lastStep)

    have(thesis) by Cut(inFixpointFunctionDomain, lastStep)

  })
  
  val fixpointFunctionSuccessor = Lemma((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- in(x, app(h, successor(n))) <=> P2(x, app(h, n))) {
    
    have(((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h))) |- subset(m, n) ==> subset(app(h, m), app(h, n)))) by RightImplies(fixpointFunctionMonotonicity)
    thenHave(((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(n, relationDomain(h))) |- forall(m, subset(m, n) ==> subset(app(h, m), app(h, n))))) by RightForall
    have(((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- forall(m, subset(m, n) ==> subset(app(h, m), app(h, n))))) by Cut(successorElemFixpointFunctionDomain, lastStep)
    have((functional(h), ordinal(relationDomain(h)), classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- unionRange(domainRestriction(h, successor(n))) === app(h, n)) by Cut(lastStep, unionRangeCumulativeRestrictedFunction)
    val unionRangeSucc = thenHave((classFunctionMonotonic(P2), classFunctionCumulative(P2), fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h))) |- unionRange(domainRestriction(h, successor(n))) === app(h, n)) by Restate
    
    have((fixpointClassFunction(h)(P2), in(successor(n), relationDomain(h)), unionRange(domainRestriction(h, successor(n))) === app(h, n)) |- in(x, app(h, successor(n))) <=> P2(x, app(h, n))) by RightSubstEq.withParametersSimple(
      List((unionRange(domainRestriction(h, successor(n))), app(h, n))),
      lambda(s, in(x, app(h, successor(n))) <=> P2(x, s))
    )(fixpointFunctionSuccessorUnfold)

    have(thesis) by Cut(unionRangeSucc, lastStep)
  }

  def fixpointClassFunctionWithDomain(h: Term)(c: PredicateLabel[2])(d: Term) = fixpointClassFunction(h)(c) /\ (d === relationDomain(h))

  val fixpointClassFunctionWithDomainOrdinal = Lemma(fixpointClassFunctionWithDomain(h)(P2)(d) |- ordinal(d)) {
    sorry
  }

  val fixpointClassFunctionWithDomainUniqueness = Lemma(ordinal(d) |- existsOne(h, fixpointClassFunctionWithDomain(h)(P2)(d))) {
    sorry
  }

  val fixpointClassFunctionWithDomainExistence = Lemma(ordinal(d) |- exists(h, fixpointClassFunctionWithDomain(h)(P2)(d))) {
    have(thesis) by Cut(fixpointClassFunctionWithDomainUniqueness, lisa.maths.Quantifiers.existsOneImpliesExists of (P := lambda(h, fixpointClassFunctionWithDomain(h)(P2)(d))))
  }

  /**
   * Lemma --- If two functions are the height function then they are the same.
   *
   *     `f = height /\ h = height => f = h`
   */
  val fixpointClassFunctionWithDomainUniqueness2 = Lemma((fixpointClassFunctionWithDomain(f)(P2)(d), fixpointClassFunctionWithDomain(h)(P2)(d)) |- f === h) {
    have((ordinal(d), fixpointClassFunctionWithDomain(f)(P2)(d), fixpointClassFunctionWithDomain(h)(P2)(d)) |- f === h) by Cut(fixpointClassFunctionWithDomainUniqueness, existsOneImpliesUniqueness of (P := lambda(h, fixpointClassFunctionWithDomain(h)(P2)(d)), x := f, y := h))
    have(thesis) by Cut(fixpointClassFunctionWithDomainOrdinal, lastStep)
  }

  def fixpointDescription(c: PredicateLabel[2])(d: Term)(fix: Term) = forall(t, in(t, fix) <=> forall(h, fixpointClassFunctionWithDomain(h)(c)(d) ==> in(t, unionRange(h))))

  val fixpointUniqueness = Lemma(ordinal(d) |- existsOne(z, fixpointDescription(P2)(d)(z))) {
    // STEP 0: Caching
        val fixpointDefinitionRight = forall(h, fixpointClassFunctionWithDomain(h)(P2)(d) ==> in(t, unionRange(h)))
        val inUnionRangeF = in(t, unionRange(f))

        // STEP 1: Prove that there exists a term satisfying the definition of this ADT.
        // Specifically, this term is the union of all the terms with a height.
        have(ordinal(d) |- exists(z, fixpointDescription(P2)(d)(z))) subproof {

          // STEP 1.1: Prove the forward implication of the definition, using the uniqueness of the height function
          have(inUnionRangeF |- inUnionRangeF) by Hypothesis
          thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by RightSubstEq.withParametersSimple(
            List((f, h)),
            lambda(f, inUnionRangeF)
          )
          have((fixpointClassFunctionWithDomain(f)(P2)(d), fixpointClassFunctionWithDomain(h)(P2)(d), inUnionRangeF) |- in(t, unionRange(h))) by Cut(fixpointClassFunctionWithDomainUniqueness2, lastStep)
          thenHave((fixpointClassFunctionWithDomain(f)(P2)(d), inUnionRangeF) |- fixpointClassFunctionWithDomain(h)(P2)(d) ==> in(t, unionRange(h))) by RightImplies
          thenHave((fixpointClassFunctionWithDomain(f)(P2)(d), inUnionRangeF) |- fixpointDefinitionRight) by RightForall
          val forward = thenHave(fixpointClassFunctionWithDomain(f)(P2)(d) |- inUnionRangeF ==> fixpointDefinitionRight) by RightImplies

          // STEP 1.2: Prove the backward implication of the definition
          have(fixpointDefinitionRight |- fixpointDefinitionRight) by Hypothesis
          thenHave(fixpointDefinitionRight |- fixpointClassFunctionWithDomain(f)(P2)(d) ==> inUnionRangeF) by InstantiateForall(f)
          val backward = thenHave(fixpointClassFunctionWithDomain(f)(P2)(d) |- fixpointDefinitionRight ==> inUnionRangeF) by Restate

          // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
          have(fixpointClassFunctionWithDomain(f)(P2)(d) |- inUnionRangeF <=> fixpointDefinitionRight) by RightIff(forward, backward)
          thenHave(fixpointClassFunctionWithDomain(f)(P2)(d) |- forall(t, inUnionRangeF <=> fixpointDefinitionRight)) by RightForall

          thenHave(fixpointClassFunctionWithDomain(f)(P2)(d) |- exists(z, forall(t, in(t, z) <=> fixpointDefinitionRight))) by RightExists
          thenHave(exists(f, fixpointClassFunctionWithDomain(f)(P2)(d)) |- exists(z, forall(t, in(t, z) <=> fixpointDefinitionRight))) by LeftExists
          have(thesis) by Cut(fixpointClassFunctionWithDomainExistence, lastStep)
        }

        // STEP 2: Conclude using the extension by definition

        have(thesis) by Cut(lastStep, uniqueByExtension of (schemPred := lambda(t, fixpointDefinitionRight)))
  }

}