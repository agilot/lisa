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
              case BinderFormula(∀, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = ∀(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = ∃(v, accFormula)
                  (lib.have(diffRest + newFormula |- bot.right) by LeftExists(accFact), newFormula)
                )
              case _ => return proof.InvalidProofTactic(s"The formula that changed is not quantified: $f.")
          case Sequent(_, s) if s.size == 1 =>
            val diffRest = bot.right -- s
            val f = s.head
            val fWithoutQuant = (fact.statement.right -- diffRest).head
            f match
              case BinderFormula(∀, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = ∀(v, accFormula)
                  (lib.have(bot.left |- diffRest + newFormula) by RightForall(accFact), newFormula)
                )
              case BinderFormula(Exists, _, _) => 
                vars.foldRight[(sp.Fact, Formula)](fact, fWithoutQuant)( (v, acc) => 
                  val (accFact, accFormula) = acc
                  val newFormula = ∃(v, accFormula)
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
    
    //val before = System.nanoTime

    val res = f

    //val totalTime = (System.nanoTime - before) / 1000000

    //println(s"${name.value} time: $totalTime ms")

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
  val w = variable

  val Q = predicate[1]
  val P = predicate[1]
  val P2 = predicate[2]
  val R = predicate[2]
  val F = function[1]
  val schemPred = predicate[1]
  val S = predicate[3]
  val S2 = predicate[3]

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
    vars.foldRight(f)(∃(_, _))

  /**
   * Repeats universal quantification over a sequence of variables.
   *
   * @param vars the variables to quantify over
   * @param f the formula to which the quantifiers are applied
   * @return the quantified formula
   */
  def forallSeq(vars: Seq[Variable], f: Formula): Formula =
    vars.foldRight(f)(∀(_, _))

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
      case Iff(True, phi) => simplify(phi)
      case Iff(phi, True) => simplify(phi)
      case Iff(phi, psi) => Iff(simplify(phi), simplify(psi))
      case ∀(v, phi) => ∀(v, simplify(phi))
      case Exists(v, phi) => Exists(v, simplify(phi))
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
  import lisa.maths.settheory.Functions.*
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
    

    val monotonicity: THM = Lemma(y ⊆ z |- getOrElse(y) ⊆ getOrElse(z)) {
      to match
        case Self => 
          have(thesis) by Restate.from(setOfFunctionsRightMonotonic of (x := from))
        case GroundType(t) =>
          have(thesis) by Restate.from(subsetReflexivity of (x := getOrElse(y)))
        case f: FunctionType =>
          have(thesis) by Cut(
            f.monotonicity,
            setOfFunctionsRightMonotonic of (x := from, y := f.getOrElse(y), z := f.getOrElse(z))
          )
      
    }

  }

  /**
   * Shorthand for the union of the range of a function.
   *
   * @param f the function
   */
  def uran(f: Term) = union(ran(f))

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
    if n == 0 then ∅
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
  import lisa.maths.settheory.orderings.Recursion.*
  //import lisa.maths.Quantifiers.*

  // *********************
  // * FIRST ORDER LOGIC *
  // *********************

  /**
   * Lemma --- Modus ponens for equivalence.
   */
  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2) {
    have(thesis) by Tautology
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


  val restrictedFunctionRangeIntro = Lemma(
    (functional(f), x ∈ d, x ∈ dom(f)) |- app(f, x) ∈ ran(f ↾ d)
  ) {
    have((functional(f), functional(f ↾ d), x ∈ d, x ∈ dom(f), x ∈ (dom(f) ∩ d)) |- app(f, x) ∈ ran(f ↾ d)) by Substitution.ApplyRules(functionRestrictionApp, domainRestrictionDomain)(functionalRangeIntro of (f := f ↾ d, a := x))
    have((functional(f), x ∈ d, x ∈ dom(f), x ∈ (dom(f) ∩ d)) |- app(f, x) ∈ ran(f ↾ d)) by Cut(domainRestrictionFunctional of (x := d), lastStep)
    thenHave((functional(f), x ∈ d, x ∈ dom(f), x ∈ dom(f) /\ x ∈ d) |- app(f, x) ∈ ran(f ↾ d)) by Substitution.ApplyRules(setIntersectionMembership of (z := x, x := dom(f), y := d))
  }

  val restrictedFunctionRangeElim = Lemma(
    (functional(f), y ∈ ran(f ↾ d)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))
  ) {
    have((x ∈ (dom(f) ∩ d), app(f, x) === y) |- x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) by Restate
    thenHave((functional(f), x ∈ d, x ∈ dom(f), x ∈ (dom(f) ∩ d), app(f ↾ d, x) === y) |- x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) by Substitution.ApplyRules(functionRestrictionApp of (x := d))
    thenHave((functional(f), x ∈ d /\ x ∈ dom(f), x ∈ (dom(f) ∩ d), app(f ↾ d, x) === y) |- x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) by LeftAnd
    thenHave((functional(f), x ∈ (dom(f) ∩ d), app(f ↾ d, x) === y) |- x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) by Substitution.ApplyRules(setIntersectionMembership of (z := x, x := dom(f), y := d))
    thenHave((functional(f), x ∈ (dom(f) ∩ d), app(f ↾ d, x) === y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by RightExists
    thenHave((functional(f), x ∈ (dom(f) ∩ d) /\ (app(f ↾ d, x) === y)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by LeftAnd
    thenHave((functional(f), x ∈ dom(f ↾ d) /\ (app(f ↾ d, x) === y)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by Substitution.ApplyRules(domainRestrictionDomain)
    thenHave((functional(f), ∃(x, x ∈ dom(f ↾ d) /\ (app(f ↾ d, x) === y))) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by LeftExists
    thenHave((functional(f), functional(f ↾ d), y ∈ ran(f ↾ d)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by Substitution.ApplyRules(functionalRangeMembership)
    have(thesis) by Cut(domainRestrictionFunctional of (x := d), lastStep)
  }

  /**
   * Lemma --- If an element is in the image of a restricted function, then it has a preimage inside its domain.
   *
   *     `functional(f) |- y ⊆ Im(f) <=> ∃x ∈ Dom(f) ∩ d. f(x) = y`
   */
  val restrictedFunctionRangeMembership = Lemma(
    functional(f) |- y ∈ ran(f ↾ d) <=> ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))
  ) {
    val left = have(functional(f) |- y ∈ ran(f ↾ d) ==> ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) by RightImplies(restrictedFunctionRangeElim)

    have((functional(f), x ∈ d, x ∈ dom(f), app(f, x) === y) |- y ∈ ran(f ↾ d)) by Substitution.ApplyRules(app(f, x) === y)(restrictedFunctionRangeIntro)
    thenHave((functional(f), x ∈ d /\ x ∈ dom(f) /\ (app(f, x) === y)) |- y ∈ ran(f ↾ d)) by Restate
    thenHave((functional(f), x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) |- y ∈ ran(f ↾ d)) by Substitution.ApplyRules(setIntersectionMembership of (z := x, x := dom(f), y := d))
    thenHave((functional(f), ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y))) |- y ∈ ran(f ↾ d)) by LeftExists
    val right = thenHave(functional(f) |- ∃(x, x ∈ (dom(f) ∩ d) /\ (app(f, x) === y)) ==> y ∈ ran(f ↾ d)) by RightImplies

    have(thesis) by RightIff(left, right)
  }

  val unionRangeElim = Lemma(
    (functional(f), z ∈ uran(f)) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))
  ) {
    have((z ∈ app(f, x), x ∈ dom(f)) |- x ∈ dom(f) /\ z ∈ app(f, x)) by Restate
    thenHave((z ∈ app(f, x), x ∈ dom(f)) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by RightExists
    thenHave((z ∈ y, x ∈ dom(f), app(f, x) === y) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by Substitution.ApplyRules(app(f, x) === y)
    thenHave((z ∈ y, x ∈ dom(f) /\ (app(f, x) === y)) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by LeftAnd
    thenHave((z ∈ y, ∃(x, x ∈ dom(f) /\ (app(f, x) === y))) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by LeftExists
    thenHave((functional(f), z ∈ y, y ∈ ran(f)) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by Substitution.ApplyRules(functionalRangeMembership)
    thenHave((functional(f), z ∈ y /\ y ∈ ran(f)) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by LeftAnd
    thenHave((functional(f), ∃(y, z ∈ y /\ y ∈ ran(f))) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by LeftExists
    have(thesis) by Cut(unionElim of (x := ran(f)), lastStep)
  }

  val unionRangeIntro = Lemma(
    (functional(f), x ∈ dom(f), z ∈ app(f, x)) |- z ∈ uran(f)
  ) {
    have(thesis) by Cut(functionalRangeIntro of (a := x), unionIntro of (y := app(f, x), x := ran(f)))
  }

  /**
   * Lemma --- Characterization of the union of the range of a function.
   *
   *     `∪ Im(f) = {z | ∃x ∈ Dom(f). z ∈ f(x)}`
   */
  val unionRangeMembership = Lemma(
    functional(f) |- z ∈ uran(f) <=> ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))
  ) {
    val forward = have(functional(f) |- z ∈ uran(f) ==> ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) by RightImplies(unionRangeElim)

    have((functional(f), x ∈ dom(f) /\ z ∈ app(f, x)) |- z ∈ uran(f)) by LeftAnd(unionRangeIntro)
    thenHave((functional(f), ∃(x, x ∈ dom(f) /\ z ∈ app(f, x))) |- z ∈ uran(f)) by LeftExists
    val backward = thenHave(functional(f) |- ∃(x, x ∈ dom(f) /\ z ∈ app(f, x)) ==> z ∈ uran(f)) by RightImplies
    have(thesis) by RightIff(forward, backward)
  }

  val unionRangeRestrIntro = Lemma(
    (functional(f), x ∈ d, x ∈ dom(f), z ∈ app(f, x)) |- z ∈ uran(f ↾ d)
  ) {
    have(thesis) by Cut(restrictedFunctionRangeIntro, unionIntro of (y := app(f, x), x := ran(f ↾ d)))
  }

  val unionRangeRestrElim = Lemma(
    (functional(f), z ∈ uran(f ↾ d)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))
  ) {
    have((z ∈ app(f ↾ d, x), x ∈ dom(f ↾ d)) |- x ∈ dom(f ↾ d) /\ z ∈ app(f ↾ d, x)) by Restate
    thenHave((functional(f), x ∈ d, x ∈ dom(f), z ∈ app(f ↾ d, x), x ∈ dom(f ↾ d)) |- x ∈ dom(f ↾ d) /\ z ∈ app(f, x)) by Substitution.ApplyRules(functionRestrictionApp)
    thenHave((functional(f), x ∈ d /\ x ∈ dom(f), z ∈ app(f ↾ d, x), x ∈ dom(f ↾ d)) |- x ∈ dom(f ↾ d) /\ z ∈ app(f, x)) by LeftAnd
    thenHave((functional(f), x ∈ (dom(f) ∩ d), z ∈ app(f ↾ d, x), x ∈ dom(f ↾ d)) |- x ∈ dom(f ↾ d) /\ z ∈ app(f, x)) by Substitution.ApplyRules(setIntersectionMembership of (z := x, x := dom(f), y := d))
    thenHave((functional(f), x ∈ dom(f ↾ d), z ∈ app(f ↾ d, x)) |- x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x)) by Substitution.ApplyRules(domainRestrictionDomain)
    thenHave((functional(f), x ∈ dom(f ↾ d), z ∈ app(f ↾ d, x)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by RightExists
    thenHave((functional(f), x ∈ dom(f ↾ d), z ∈ y, app(f ↾ d, x) === y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by Substitution.ApplyRules(app(f ↾ d, x) === y)
    thenHave((functional(f), x ∈ dom(f ↾ d) /\ (app(f ↾ d, x) === y), z ∈ y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by LeftAnd
    thenHave((functional(f), ∃(x, x ∈ dom(f ↾ d) /\ (app(f ↾ d, x) === y)), z ∈ y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by LeftExists
    thenHave((functional(f), functional(f ↾ d), y ∈ ran(f ↾ d), z ∈ y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by Substitution.ApplyRules(functionalRangeMembership)
    have((functional(f), y ∈ ran(f ↾ d), z ∈ y) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by Cut(domainRestrictionFunctional of (x := d), lastStep)
    thenHave((functional(f), z ∈ y /\ y ∈ ran(f ↾ d)) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by LeftAnd
    thenHave((functional(f), ∃(y, z ∈ y /\ y ∈ ran(f ↾ d))) |- ∃(x, x ∈ (dom(f) ∩ d) /\ z ∈ app(f, x))) by LeftExists
    have(thesis) by Cut(unionElim of (x := ran(f ↾ d)), lastStep)
  }


  /**
   * Lemma --- The range of the empty function is empty.
   *
   *     `Im(∅) = ∅`
   */
  val unionRangeEmpty = Lemma(uran(∅) === ∅) {
    have(uran(∅) === uran(∅)) by RightRefl
    thenHave(uran(∅) === union(∅)) by Substitution.ApplyRules(rangeEmpty)
    thenHave(thesis) by Substitution.ApplyRules(unionEmpty)
  }

  // ****************
  // * MONOTONICITY *
  // ****************

  /**
   * Lemma --- The union of the range is a monotonic operation with respect to set inclusion.
   *
   *     `f ⊆ g |- ∪ Im(f) ⊆ ∪ Im(g)`
   */
  val unionRangeMonotonic = Lemma(
    f ⊆ g |- uran(f) ⊆ uran(g)
  ) {
    have(thesis) by Apply(unionMonotonicity).on(relationRangeSubset of (r1 := f, r2 := g))
  }

  /**
   * Lemma --- The union of the range of a restricted function is a monotonic operation with respect to set inclusion.
   *
   *     `f ⊆ g |- ∪ Im(f|d) ⊆ ∪ Im(g|d)`
   */
  val unionRangeRestrMonotonic = Lemma(
    (functional(f), x ⊆ y) |- uran(f ↾ x) ⊆ uran(f ↾ y)
  ) {
    have(thesis) by Cut(
      functionRestrictionSubsetDomain, unionRangeMonotonic of (f := f ↾ x, g := f ↾ y)
    )
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
  val unionPreimageMonotonic = Lemma((s ⊆ t, P(s) ==> P(t)) |- (P(s) \/ (x ∈ s)) ==> (P(t) \/ (x ∈ t))) {
    have(s ⊆ t |- x ∈ s ==> x ∈ t) by RightImplies(subsetElim of (z := x, x := s, y := t))
    have(thesis) by Cut(lastStep, disjunctionsImplies of (p1 := x ∈ s, p2 := x ∈ t, q1 := P(s), q2 := P(t)))
  }

  val monotonic = DEF(f) --> ∀(m, ∀(n, (m ∈ dom(f) /\ n ∈ dom(f)) ==> (m ⊆ n ==> app(f, m) ⊆ app(f, n))))

  val monotonicIntro = Lemma(
    ∀(m, ∀(n, (m ∈ dom(f) /\ n ∈ dom(f)) ==> (m ⊆ n ==> app(f, m) ⊆ app(f, n)))) |- monotonic(f)
  ) {
    have(thesis) by Weakening(monotonic.definition)
  }

  val monotonicElim = Lemma(
    (monotonic(f), m ∈ dom(f), n ∈ dom(f), m ⊆ n) |- app(f, m) ⊆ app(f, n) 
  ) {
    have(monotonic(f) |- monotonic(f)) by Hypothesis
    thenHave(monotonic(f) |- ∀(m, ∀(n, (m ∈ dom(f) /\ n ∈ dom(f)) ==> (m ⊆ n ==> app(f, m) ⊆ app(f, n))))) by Substitution.ApplyRules(monotonic.definition)
    thenHave(thesis) by InstantiateForall(m, n)
  }

  /**
   * Lemma --- Characterization of the union of the range of a monotonic function restricted to the successor of a natural number.
   *
   *     `monotonic(f) and Dom(f) = N |- ∪ Im(f|n + 1) = h(n)`
   */
  val unionRangeCumulativeRestrictedFunction = Lemma(
    (functional(f), ordinal(dom(f)), n ∈ dom(f), monotonic(f)) |- uran(f ↾ successor(n)) === app(f, n)
  ) {
    have((ordinal(dom(f)), n ∈ dom(f)) |- successor(n) <= dom(f)) by Weakening(ltIffSuccessorLeq of (a := n, b := dom(f)))
    val subsDomain = have((ordinal(dom(f)), n ∈ dom(f)) |- successor(n) ⊆ dom(f)) by Cut(lastStep, ordinalLeqImpliesSubset of (a := successor(n), b := dom(f)))
    val succSubset = have((ordinal(dom(f)), n ∈ dom(f)) |- dom(f) ∩ successor(n) === successor(n)) by Cut(lastStep, setIntersectionOfSubsetBackward of (x := dom(f), y := successor(n)))

    val forward = have((functional(f), monotonic(f), n ∈ dom(f), ordinal(dom(f))) |- z ∈ uran(f ↾ successor(n)) ==> z ∈ app(f, n)) subproof {
      have((monotonic(f), x ∈ dom(f), n ∈ dom(f), ordinal(n), x < successor(n)) |- app(f, x) ⊆ app(f, n)) by Cut(inSuccessorSubset of (b := x, a := n), monotonicElim of (m := x))
      have((monotonic(f), x ∈ dom(f), n ∈ dom(f), ordinal(n), x < successor(n), z ∈ app(f, x)) |- z ∈ app(f, n)) by Cut(lastStep, subsetElim of (x := app(f, x), y := app(f, n)))
      have((monotonic(f), n ∈ dom(f), ordinal(n), ordinal(dom(f)), x <= n, x < successor(n), z ∈ app(f, x)) |- z ∈ app(f, n)) by Cut(ordinalLeqLtImpliesLt of (a := x, b := n, c := dom(f)), lastStep)
      have((monotonic(f), n ∈ dom(f), ordinal(n), ordinal(dom(f)), x < successor(n), z ∈ app(f, x)) |- z ∈ app(f, n)) by Cut(inSuccessorLeq of (a := n, b := x), lastStep)
      have((monotonic(f), n ∈ dom(f), ordinal(dom(f)), x < successor(n), z ∈ app(f, x)) |- z ∈ app(f, n)) by Cut(elementsOfOrdinalsAreOrdinals of (b := n, a := dom(f)), lastStep)
      thenHave((monotonic(f), n ∈ dom(f), ordinal(dom(f)), (x < successor(n)) /\ z ∈ app(f, x)) |- z ∈ app(f, n)) by LeftAnd
      thenHave((monotonic(f), n ∈ dom(f), ordinal(dom(f)), ∃(x, (x < successor(n)) /\ z ∈ app(f, x))) |- z ∈ app(f, n)) by LeftExists
      thenHave((monotonic(f), n ∈ dom(f), ordinal(dom(f)), ∃(x, (x < (dom(f) ∩ successor(n))) /\ z ∈ app(f, x))) |- z ∈ app(f, n)) by Substitution.ApplyRules(succSubset)
      have((functional(f), monotonic(f), n ∈ dom(f), ordinal(dom(f)), z ∈ uran(f ↾ successor(n))) |- z ∈ app(f, n)) by Cut(unionRangeRestrElim of (d := successor(n)), lastStep)
    }
    
    val backward = have((functional(f), n ∈ dom(f)) |- z ∈ app(f, n) ==> z ∈ uran(f ↾ successor(n))) subproof {
      have((functional(f), n ∈ dom(f), z ∈ app(f, n)) |- z ∈ uran(f ↾ successor(n))) by Cut(inSuccessor of (a := n), unionRangeRestrIntro of (d := successor(n), x := n))
    }

    have((functional(f), monotonic(f), n ∈ dom(f), ordinal(dom(f))) |- z ∈ uran(f ↾ successor(n)) <=> z ∈ app(f, n)) by RightIff(forward, backward)
    thenHave((functional(f), monotonic(f), n ∈ dom(f), ordinal(dom(f))) |- ∀(z, z ∈ uran(f ↾ successor(n)) <=> z ∈ app(f, n))) by RightForall
    have(thesis) by Cut(lastStep, equalityIntro of (x := uran(f ↾ successor(n)), y := app(f, n)))
  }


  // ************
  // * FIXPOINT *
  // ************

  def fixpointClassFunction(f: Term, n: Term)(S: Term ** 3 |-> Formula) =
    functionalOver(f, n) /\ ∀(m, m < n ==> 
      ((dom(f ↾ m) === ∅) ==> (app(f, m) === ∅)) /\
      (successorOrdinal(dom(f ↾ m)) ==> S(union(dom(f ↾ m)), app(f ↾ m, union(dom(f ↾ m))), app(f, m))) /\
      (limitOrdinal(dom(f ↾ m)) ==> (app(f, m) === uran(f ↾ m))) /\
      (!ordinal(dom(f ↾ m)) ==> (app(f, m) === ∅))
    )

  val fixpointClassFunctionExistsOne = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S)) |- ∃!(f, fixpointClassFunction(f, n)(S))
  ) {
    have((ordinal(n), classFunctionTwoArgs(S)) |- ∃!(f, fixpointClassFunction(f, n)(S))) by Cut(functionIsClassFunction of (F := lambda(x, uran(x)), P := (lambda(x, True))), transfiniteRecursionClassFunctionCases of (a := n, R := lambda((x, y), y === uran(x)), z := ∅))
    have(thesis) by Cut(limitOrdinalIsOrdinal of (a := n), lastStep)
  }

  val fixpointClassFunctionUniqueness = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointClassFunction(g, n)(S)) |- f === g
  ) {
    have(thesis) by Cut(fixpointClassFunctionExistsOne, existsOneImpliesUniqueness of (x := f, y := g, P := lambda(f, fixpointClassFunction(f, n)(S))))
  }

  val fixpointClassFunctionExistence = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S)) |- ∃(f, fixpointClassFunction(f, n)(S))
  ) {
    have(thesis) by Cut(fixpointClassFunctionExistsOne, existsOneImpliesExists of (P := lambda(f, fixpointClassFunction(f, n)(S))))
  }
  
  val fixpointClassFunctionZeroUnfold = Lemma(
    (fixpointClassFunction(f, n)(S), limitOrdinal(n)) |- app(f, ∅) === ∅
  ) {
    // Caching
    def funBody = 
      ((dom(f ↾ m) === ∅) ==> (app(f, m) === ∅)) /\
      (successorOrdinal(dom(f ↾ m)) ==> S(union(dom(f ↾ m)), app(f ↾ m, union(dom(f ↾ m))), app(f, m))) /\
      (limitOrdinal(dom(f ↾ m)) ==> (app(f, m) === uran(f ↾ m))) /\
      (!ordinal(dom(f ↾ m)) ==> (app(f, m) === ∅))

    have(fixpointClassFunction(f, n)(S) |- ∀(m, m < n ==> funBody)) by Restate
    thenHave((fixpointClassFunction(f, n)(S), m < n) |- funBody) by InstantiateForall(m)
    thenHave((fixpointClassFunction(f, n)(S), m < n, dom(f ↾ m) === ∅) |- app(f, m) === ∅) by Weakening
    thenHave((functionalOver(f, n), fixpointClassFunction(f, n)(S), m < n, m === ∅, ordinal(n)) |- app(f, m) === ∅) by Substitution.ApplyRules(domRestr of (b := m, a := n))
    have((functionalOver(f, n), fixpointClassFunction(f, n)(S), limitOrdinal(n), ∅ === ∅, ordinal(n)) |- app(f, ∅) === ∅) by Cut(limitOrdinalGtZero of (a := n), lastStep of (m := ∅))
    have((functionalOver(f, n), fixpointClassFunction(f, n)(S), limitOrdinal(n), ∅ === ∅) |- app(f, ∅) === ∅) by Cut(limitOrdinalIsOrdinal of (a := n), lastStep)
  }

  val fixpointClassFunctionSuccessorUnfold = Lemma(
    (fixpointClassFunction(f, n)(S), m < n, limitOrdinal(n)) |- S(m, app(f, m), app(f, successor(m)))
  ) {
    // Caching
    def funBody = 
      ((dom(f ↾ m) === ∅) ==> (app(f, m) === ∅)) /\
      (successorOrdinal(dom(f ↾ m)) ==> S(union(dom(f ↾ m)), app(f ↾ m, union(dom(f ↾ m))), app(f, m))) /\
      (limitOrdinal(dom(f ↾ m)) ==> (app(f, m) === uran(f ↾ m))) /\
      (!ordinal(dom(f ↾ m)) ==> (app(f, m) === ∅))

    have(fixpointClassFunction(f, n)(S) |- ∀(m, m < n ==> funBody)) by Restate
    thenHave((fixpointClassFunction(f, n)(S), successor(m) < n) |- funBody.substitute(m := successor(m))) by InstantiateForall(successor(m))
    thenHave((fixpointClassFunction(f, n)(S), successor(m) < n, successorOrdinal(dom(f ↾ successor(m)))) |- S(union(dom(f ↾ successor(m))), app(f ↾ successor(m), union(dom(f ↾ successor(m)))), app(f, successor(m)))) by Weakening
    thenHave((fixpointClassFunction(f, n)(S), successor(m) < n, successorOrdinal(successor(m)), ordinal(n), m < n) |- S(m, app(f, m), app(f, successor(m)))) by Substitution.ApplyRules(unionDomRestrApp of (a := n, b := m), unionDomRestr of (a := n, b := m), domRestr of (a := n, b := successor(m)))
    have((fixpointClassFunction(f, n)(S), limitOrdinal(n), successorOrdinal(successor(m)), ordinal(n), m < n) |- S(m, app(f, m), app(f, successor(m)))) by
      Cut(limitOrdinalIsInductive of (b := m, a := n), lastStep)
    have((fixpointClassFunction(f, n)(S), limitOrdinal(n), ordinal(m), ordinal(n), m < n) |- S(m, app(f, m), app(f, successor(m)))) by
      Cut(successorIsSuccessorOrdinal of (a := m), lastStep)
    have((fixpointClassFunction(f, n)(S), limitOrdinal(n), ordinal(n), m < n) |- S(m, app(f, m), app(f, successor(m)))) by
      Cut(elementsOfOrdinalsAreOrdinals of (b := m, a := n), lastStep)
    have(thesis) by Cut(limitOrdinalIsOrdinal of (a := n), lastStep)
  }

  val fixpointClassFunctionLimitUnfold = Lemma(
    (fixpointClassFunction(f, n)(S), m < n, limitOrdinal(m), limitOrdinal(n)) |- app(f, m) === uran(f ↾ m)
  ) {

    // Caching
    def funBody = 
      ((dom(f ↾ m) === ∅) ==> (app(f, m) === ∅)) /\
      (successorOrdinal(dom(f ↾ m)) ==> S(union(dom(f ↾ m)), app(f ↾ m, union(dom(f ↾ m))), app(f, m))) /\
      (limitOrdinal(dom(f ↾ m)) ==> (app(f, m) === uran(f ↾ m))) /\
      (!ordinal(dom(f ↾ m)) ==> (app(f, m) === ∅))

    have(fixpointClassFunction(f, n)(S) |- ∀(m, m < n ==> funBody)) by Restate
    thenHave((fixpointClassFunction(f, n)(S), m < n) |- funBody) by InstantiateForall(m)
    thenHave((fixpointClassFunction(f, n)(S), m < n, limitOrdinal(dom(f ↾ m))) |- app(f, m) === uran(f ↾ m)) by Weakening
    thenHave((functionalOver(f, n), fixpointClassFunction(f, n)(S), m < n, limitOrdinal(m), ordinal(n)) |- app(f, m) === uran(f ↾ m)) by Substitution.ApplyRules(domRestr of (b := m, a := n))
    have((functionalOver(f, n), fixpointClassFunction(f, n)(S), m < n, limitOrdinal(m), limitOrdinal(n)) |- app(f, m) === uran(f ↾ m)) by Cut(limitOrdinalIsOrdinal of (a := n), lastStep)
  }
  
  def classFunctionCumulative(S: Term ** 3 |-> Formula) = (∀(a, ∀(b, ∀(c, S2(a, b, c) ==> b ⊆ c)))).substitute(S2 := S)

  val classFunctionCumulativeElim = Lemma(
    (classFunctionCumulative(S), S(a, b, c)) |- b ⊆ c
  ) {
    have(classFunctionCumulative(S) |- classFunctionCumulative(S)) by Hypothesis
    thenHave(thesis) by InstantiateForall(a, b, c)
  }

  val cumulativeFixpointClassFunctionSubsetSuccessor = Lemma(
    (fixpointClassFunction(f, n)(S), m < n, limitOrdinal(n), classFunctionCumulative(S)) |- app(f, m) ⊆ app(f, successor(m))
  ) {
    have(thesis) by Cut(fixpointClassFunctionSuccessorUnfold, classFunctionCumulativeElim of (a := m, b := app(f, m), c := app(f, successor(m))))
  }

  
  val fixpointFunctionMonotonicity = Lemma(
    (classFunctionCumulative(S), limitOrdinal(n), fixpointClassFunction(f, n)(S)) |- monotonic(f)
  ) {

    def ih(b: Term) = ∀(c, c < b ==> (a ⊆ c ==> app(f, a) ⊆ app(f, c)))

    val eqCase = have(a === b |- app(f, a) ⊆ app(f, b)) by Substitution.ApplyRules(a === b)(subsetReflexivity of (x := app(f, a)))

    have(b === ∅ |- !(a < b)) by Substitution.ApplyRules(b === ∅)(emptySetAxiom of (x := a))
    val zeroCase = thenHave((a < b, b === ∅) |- app(f, a) ⊆ app(f, b)) by Weakening

    val successorCase = have((fixpointClassFunction(f, n)(S), a < b, b < n, limitOrdinal(n), classFunctionCumulative(S), ih(b), successorOrdinal(b)) |- app(f, a) ⊆ app(f, b)) subproof {
      have(ih(b) |- ih(b)) by Hypothesis
      have((ih(successor(d)), d < successor(d), a ⊆ d) |- app(f, a) ⊆ app(f, d)) by InstantiateForall(d)(lastStep of (b := successor(d)))
      have((ih(successor(d)),  a ⊆ d) |- app(f, a) ⊆ app(f, d)) by Cut(inSuccessor of (a := d), lastStep)
      have((ih(successor(d)),  a ⊆ d, app(f, d) ⊆ app(f, successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(lastStep, subsetTransitivity of (x := app(f, a), y := app(f, d), z := app(f, successor(d))))
      have((fixpointClassFunction(f, n)(S),  a ⊆ d, d < n, limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(cumulativeFixpointClassFunctionSubsetSuccessor of (m := d), lastStep)
      have((fixpointClassFunction(f, n)(S),  a <= d, d < n, ordinal(d), limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(ordinalLeqImpliesSubset of (b := d), lastStep)
      thenHave((fixpointClassFunction(f, n)(S),  a < successor(d), d < n, ordinal(d), limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Substitution.ApplyRules(ordinalLeqIffLtSuccessor)
      have((fixpointClassFunction(f, n)(S),  a < successor(d), d < n, ordinal(n), limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(elementsOfOrdinalsAreOrdinals of (b := d, a := n), lastStep)
      have((fixpointClassFunction(f, n)(S),  a < successor(d), d < successor(d), successor(d) < n, ordinal(n), limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(ordinalTransitive of (a := d, b := successor(d), c := n), lastStep)
      have((fixpointClassFunction(f, n)(S),  a < successor(d), successor(d) < n, ordinal(n), limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(inSuccessor of (a := d), lastStep)
      have((fixpointClassFunction(f, n)(S), a < successor(d), successor(d) < n, limitOrdinal(n), classFunctionCumulative(S), ih(successor(d))) |- app(f, a) ⊆ app(f, successor(d))) by Cut(limitOrdinalIsOrdinal of (a := n), lastStep)
      thenHave((fixpointClassFunction(f, n)(S), a < b, b < n, limitOrdinal(n), classFunctionCumulative(S), ih(b), b === successor(d)) |- app(f, a) ⊆ app(f, b)) by Substitution.ApplyRules(b === successor(d))
      thenHave((fixpointClassFunction(f, n)(S), a < b, b < n, limitOrdinal(n), classFunctionCumulative(S), ih(b), ∃(d, b === successor(d))) |- app(f, a) ⊆ app(f, b)) by LeftExists
      thenHave((fixpointClassFunction(f, n)(S), a < b, b < n, limitOrdinal(n), classFunctionCumulative(S), ih(b), ordinal(b) /\ ∃(d, b === successor(d))) |- app(f, a) ⊆ app(f, b)) by LeftAnd
      thenHave(thesis) by Substitution.ApplyRules(successorOrdinal.definition)
    }

    val limitCase = have((fixpointClassFunction(f, n)(S), a < b, a ∈ dom(f), b < n, limitOrdinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) subproof {
      have((functionalOver(f, n), a < b, a ∈ dom(f)) |- app(f, a) ∈ ran(f ↾ b)) by Cut(functionalOverIsFunctional of (x := n), restrictedFunctionRangeIntro of (x := a, d := b))
      have((functionalOver(f, n), a < b, a ∈ dom(f)) |- app(f, a) ⊆ uran(f ↾ b)) by Cut(lastStep, subsetUnion of (x := app(f, a), y := ran(f ↾ b)))
      thenHave((functionalOver(f, n), a < b, a ∈ dom(f), fixpointClassFunction(f, n)(S), b < n, limitOrdinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Substitution.ApplyRules(fixpointClassFunctionLimitUnfold)
    }

    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a < b, a ∈ dom(f), b < n, successorOrdinal(b) \/ limitOrdinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by LeftOr(limitCase, successorCase)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a < b, a ∈ dom(f), b < n, (b === ∅) \/ successorOrdinal(b) \/ limitOrdinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by LeftOr(zeroCase, lastStep)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a < b, a ∈ dom(f), b < n, ordinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Cut(successorOrNonsuccessorOrdinal of (a := b), lastStep)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a <= b, a ∈ dom(f), b < n, ordinal(b), limitOrdinal(n)) |- (app(f, a) ⊆ app(f, b), a === b)) by Cut(lessOrEqualElim, lastStep)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a <= b, a ∈ dom(f), b < n, ordinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Cut(lastStep, eqCase)
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a ⊆ b, a ∈ dom(f), b < n, ordinal(a), ordinal(b), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Substitution.ApplyRules(leqOrdinalIsSubset)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a ⊆ b, a ∈ dom(f), b < n, ordinal(b), ordinal(dom(f)), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Cut(elementsOfOrdinalsAreOrdinals of (b := a, a := dom(f)), lastStep)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ih(b), a ⊆ b, a ∈ dom(f), b < n, ordinal(n), ordinal(dom(f)), limitOrdinal(n)) |- app(f, a) ⊆ app(f, b)) by Cut(elementsOfOrdinalsAreOrdinals of (a := n), lastStep)
    thenHave((fixpointClassFunction(f, n)(S), functionalOver(f, n), classFunctionCumulative(S), ih(b), a ⊆ b, a ∈ dom(f), b ∈ dom(f), ordinal(dom(f)), limitOrdinal(dom(f))) |- app(f, a) ⊆ app(f, b)) by Substitution.ApplyRules(functionalOverDomain of (x := n))
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), a ∈ dom(f), ordinal(dom(f)), limitOrdinal(dom(f))) |- b ∈ dom(f) ==> (ih(b) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b)))) by Restate
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), a ∈ dom(f), ordinal(dom(f)), limitOrdinal(dom(f))) |- ∀(b, b ∈ dom(f) ==> (ih(b) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b))))) by RightForall
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), a ∈ dom(f), ordinal(dom(f)), limitOrdinal(dom(f))) |- ∀(b, b ∈ dom(f) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b)))) by Cut(lastStep, transfiniteInductionOnOrdinal of (x := dom(f), P := lambda(b, a ⊆ b ==> app(f, a) ⊆ app(f, b))))
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ordinal(dom(f)), limitOrdinal(dom(f))) |- (a ∈ dom(f) /\ b ∈ dom(f)) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b))) by InstantiateForall(b)
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ordinal(dom(f)), limitOrdinal(dom(f))) |- ∀(b, (a ∈ dom(f) /\ b ∈ dom(f)) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b)))) by RightForall
    thenHave((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ordinal(dom(f)), limitOrdinal(dom(f))) |- ∀(a, ∀(b, (a ∈ dom(f) /\ b ∈ dom(f)) ==> (a ⊆ b ==> app(f, a) ⊆ app(f, b))))) by RightForall
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), ordinal(dom(f)), limitOrdinal(dom(f))) |- monotonic(f)) by Cut(lastStep, monotonicIntro)
    have((fixpointClassFunction(f, n)(S), classFunctionCumulative(S), limitOrdinal(dom(f))) |- monotonic(f)) by Cut(limitOrdinalIsOrdinal of (a := dom(f)), lastStep)
    thenHave((fixpointClassFunction(f, n)(S), functionalOver(f, n), classFunctionCumulative(S), limitOrdinal(n)) |- monotonic(f)) by Substitution.ApplyRules(functionalOverDomain of (x := n))
  }


  def fixpointDescription(n: Term)(S: Term ** 3 |-> Formula)(fix: Term) = ∀(t, t ∈ fix <=> ∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f)))

  val fixpointExistence = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S)) |- ∃(z, fixpointDescription(n)(S)(z))
  ) {
    val inUnionRangeG = t ∈ uran(g)
    val fixpointDefinitionRight = ∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f))

    // STEP 1.1: Prove the forward implication of the definition, using the uniqueness of the height function
    have(inUnionRangeG |- inUnionRangeG) by Hypothesis
    thenHave((f === g, inUnionRangeG) |- t ∈ uran(f)) by Substitution.ApplyRules(f === g)
    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointClassFunction(g, n)(S), inUnionRangeG) |- t ∈ uran(f)) by Cut(fixpointClassFunctionUniqueness, lastStep)
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S), inUnionRangeG) |- fixpointClassFunction(f, n)(S) ==> t ∈ uran(f)) by RightImplies
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S), inUnionRangeG) |- fixpointDefinitionRight) by RightForall
    val forward = thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S)) |- inUnionRangeG ==> fixpointDefinitionRight) by RightImplies

    // STEP 1.2: Prove the backward implication of the definition
    have(fixpointDefinitionRight |- fixpointDefinitionRight) by Hypothesis
    thenHave(fixpointDefinitionRight |- fixpointClassFunction(g, n)(S) ==> inUnionRangeG) by InstantiateForall(g)
    val backward = thenHave(fixpointClassFunction(g, n)(S) |- fixpointDefinitionRight ==> inUnionRangeG) by Restate

    // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S)) |- inUnionRangeG <=> fixpointDefinitionRight) by RightIff(forward, backward)
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S)) |- ∀(t, inUnionRangeG <=> fixpointDefinitionRight)) by RightForall

    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(g, n)(S)) |- ∃(z, ∀(t, t ∈ z <=> fixpointDefinitionRight))) by RightExists
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), ∃(g, fixpointClassFunction(g, n)(S))) |- ∃(z, ∀(t, t ∈ z <=> fixpointDefinitionRight))) by LeftExists
    have(thesis) by Cut(fixpointClassFunctionExistence, lastStep)
  }

  val fixpointUniqueness = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S)) |- ∃!(z, fixpointDescription(n)(S)(z))
  ) {
    have(thesis) by Cut(fixpointExistence, uniqueByExtension of (schemPred := lambda(t, ∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f)))))
  }

  val fixpointDescriptionIsUran = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S)) |- fixpointDescription(n)(S)(uran(f))
  ) {
    have(t ∈ uran(g) |- t ∈ uran(g)) by Hypothesis
    thenHave((f === g, t ∈ uran(f)) |- t ∈ uran(g)) by Substitution.ApplyRules(f === g)
    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointClassFunction(g, n)(S), t ∈ uran(f)) |- t ∈ uran(g)) by Cut(fixpointClassFunctionUniqueness, lastStep)
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), t ∈ uran(f)) |- fixpointClassFunction(g, n)(S) ==> t ∈ uran(g)) by RightImplies
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), t ∈ uran(f)) |- ∀(g, fixpointClassFunction(g, n)(S) ==> t ∈ uran(g))) by RightForall
    val forward = thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S)) |- t ∈ uran(f) ==> ∀(g, fixpointClassFunction(g, n)(S) ==> t ∈ uran(g))) by RightImplies

    have((fixpointClassFunction(f, n)(S) ==> t ∈ uran(f), fixpointClassFunction(f, n)(S)) |- t ∈ uran(f)) by Restate
    thenHave((∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f)), fixpointClassFunction(f, n)(S)) |- t ∈ uran(f)) by LeftForall
    val backward = thenHave(fixpointClassFunction(f, n)(S) |- ∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f)) ==> t ∈ uran(f)) by RightImplies

    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S)) |- t ∈ uran(f) <=> ∀(f, fixpointClassFunction(f, n)(S) ==> t ∈ uran(f))) by RightIff(forward, backward)
    thenHave(thesis) by RightForall
  }

  val fixpointDescriptionEquality = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z)) |- z === uran(f)
  ) {
    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointDescription(n)(S)(z), fixpointDescription(n)(S)(uran(f))) |- z === uran(f)) by Cut(fixpointUniqueness, existsOneImpliesUniqueness of (P := (lambda(z, fixpointDescription(n)(S)(z))), x := z, y := uran(f)))
    have(thesis) by Cut(fixpointDescriptionIsUran, lastStep)
  }

  val fixpointDescriptionMembership = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z)) |- x ∈ z <=> ∃(m, m ∈ n /\ x ∈ app(f, m))
  ) {
    have((functional(f), functionalOver(f, n), limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z)) |- x ∈ z <=> ∃(m, m ∈ n /\ x ∈ app(f, m))) by Substitution.ApplyRules(functionalOverDomain, fixpointDescriptionEquality)(unionRangeMembership of (z := x))
    have((functionalOver(f, n), limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z)) |- x ∈ z <=> ∃(m, m ∈ n /\ x ∈ app(f, m))) by Cut(functionalOverIsFunctional of (x := n), lastStep)
    thenHave(thesis) by Weakening
  }

  val fixpointDescriptionElim = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z), x ∈ z) |- ∃(m, m ∈ n /\ x ∈ app(f, m))
  ) {
    have(thesis) by Weakening(fixpointDescriptionMembership)
  }

  val fixpointDescriptionIntro = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z), m ∈ n, x ∈ app(f, m)) |- x ∈ z
  ) {
    have((m ∈ n, x ∈ app(f, m)) |- m ∈ n /\ x ∈ app(f, m)) by Restate
    thenHave((m ∈ n, x ∈ app(f, m)) |- ∃(m, m ∈ n /\ x ∈ app(f, m))) by RightExists
    thenHave(thesis) by Substitution.ApplyRules(fixpointDescriptionMembership)
  }

  val fixpointFunctionSubsetFixpoint = Lemma(
    (limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z), m ∈ n) |- app(f, m) ⊆ z
  ) {
    have((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z), m ∈ n) |- x ∈ app(f, m) ==> x ∈ z) by RightImplies(fixpointDescriptionIntro)
    thenHave((limitOrdinal(n), classFunctionTwoArgs(S), fixpointClassFunction(f, n)(S), fixpointDescription(n)(S)(z), m ∈ n) |- ∀(x, x ∈ app(f, m) ==> x ∈ z)) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := app(f, m), y := z))
  }

  val N = Constant("N")
  addSymbol(N)

  val heightDomainLimit = Axiom(
    limitOrdinal(N)
  )

  val heightDomainOrdinal = Lemma(
    ordinal(N)
  ) {
    have(thesis) by Cut(heightDomainLimit, limitOrdinalIsOrdinal of (a := N))
  }

  val successorIsInHeightDomain = Lemma(
    n ∈ N |- successor(n) ∈ N
  ) {
    have(thesis) by Cut(heightDomainLimit, limitOrdinalIsInductive of (b := n, a := N))
  }

  val zeroInHeightDomain = Lemma(
    ∅ ∈ N
  ) {
    have(thesis) by Cut(heightDomainLimit, limitOrdinalGtZero of (a := N))
  }

  val heightDomainHasElement = Lemma(
    ∃(n, n ∈ N)
  ) {
    have(thesis) by RightExists(zeroInHeightDomain)
  }


}