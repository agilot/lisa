/**
 * This file implements tactics to generate polymorphic set theoretic inductive algebraic data types (or ADT) and prove properties about them.
 * An algebraic data type is the least set closed under introduction rules, also known as constructors.
 * A constructor takes arguments as input that can either belong to other types (non inductive arguments)
 * or to the ADT itself (inductive arguments).
 *
 * An example of algebraic data type is the type of singly linked lists:
 *
 *   list ::= nil() | cons(head: T, tail: list)
 */

package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import Helpers.*
import Helpers.{/\, \/, ===}
import ADTDefinitions.*
import ADTHelperTheorems as ADTThm
import ADTThm.{N, successorOrdinal}
import lisa.maths.settheory.types.TypeLib.{ |=>}
import lisa.maths.settheory.types.TypeSystem.{ :: }
import lisa.maths.Quantifiers.{universalEquivalenceDistribution, equalityTransitivity}
import lisa.fol.FOL.Variable
import lisa.maths.settheory.types.TypeLib.funcspaceAxiom
import lisa.maths.settheory.orderings.Ordinals.{successor}
import lisa.maths.settheory.orderings.Ordinals

/**
 * Helpers for constructors
 */
private object Constructors {

  /**
   * Global counter used to uniquely identify constructors and thereby avoid structural subtyping.
   */
  var tagCounter = 0
}

/**
 * Syntactic set theoretical interpretation of a constructor for an algebraic data type.
 * In set theory, a constructor is a tuple containing the arguments it has been applied to, in addition to a tag
 * uniquely identifying it.
 * 
 * E.g. `cons(1, nil())` is represented as `(tagcons, (1, ((tagnil, ∅), ∅)))`
 * 
 * Constructors injectivity is proved within this class.
 *
 * @constructor creates a new constructor out of a user specification
 * @param specification types that the constructor takes as arguments
 * @param variables1 variables used to represent the arguments of the constructor
 * @param variables2 alternative set of variables to avoid capture issues
 */
private class SyntacticConstructor(
  val specification: Seq[ConstructorArgument], 
  val variables1: Seq[Variable], 
  val variables2: Seq[Variable],
  ) {

  /**
   * Unique identifier of this constructor
   */
  val tag: Int = Constructors.tagCounter
  Constructors.tagCounter = Constructors.tagCounter + 1

  /**
   * Term representation of the tag of this constructor
   */
  val tagTerm: Term = toTerm(tag)

  /**
    * Sequence of variables used to represent the arguments of the constructor
    */
  val variables: Seq[Variable] = variables1

  /**
   * Number of arguments that this constructor takes
   */
  val arity: Int = specification.length
  
  /**
   * Sequence of variables of the constructor with their respective domains.
   */
  val signature1: Seq[(Variable, ConstructorArgument)] = variables1.zip(specification)

  /**
   * Alternative sequence of variables of the constructor with their respective domains.
   */
  val signature2: Seq[(Variable, ConstructorArgument)] = variables2.zip(specification)

  /**
   * Sequence of variables of the constructor with their respective domains.
   */
  val signature: Seq[(Variable, ConstructorArgument)] = signature1

  /**
   * Internally, an instance of this constructor is represented as a list.
   * The first element of this list is the tag of this constructor.
   * The following elements are its arguments. We represent lists as chained
   * pairs followed by the empty set.
   *
   * e.g. cons(1, nil()) --> (tagcons, (1, ((tagnil, ∅), ∅)))
   *
   * @param args the arguments of this instance of the constructor
   */
  def term(args: Seq[Term]): Term = pair(tagTerm, subterm(args))

  /**
    * Internal representation of an instance of this constructor in which arguments are schematic variables.
    */
  val term1: Term = term(variables1)

  /**
    * Internal representation of an instance of this constructor in which arguments are an alternative set of schematic variables.
    */
  val term2: Term = term(variables2)

  /**
    * Internal representation of an instance of this constructor in which arguments are schematic variables.
    */
  val term: Term = term1

  /**
   * Internal representation of an instance of this constructor without the tag
   *
   * @param args the arguments of this instance of the constructor
   *
   * @see [[this.term]]
   */
  def subterm(args: Seq[Term]): Term = args.foldRight[Term](emptySet)(pair(_, _))

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
   */
  val subterm1: Term = subterm(variables1)

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are an alternative set 
   * of schematic variables.
   */
  val subterm2: Term = subterm(variables2)

  /**
   * Internal representation of an instance of this constructor without the tag, in which arguments are schematic variables.
   */
  val subterm: Term = subterm1

  /**
   * Theorem --- Injectivity of constructors.
   *
   *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
   *
   * e.g. cons(head1, tail1) === cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
   */
  lazy val injectivity =
    if arity == 0 then
      Lemma(term1 === term2) {
        have(thesis) by RightRefl
      }
    else
      Lemma((term1 === term2) <=> (variables1 === variables2)) {

        // STEP 1: Get rid of the tag using pair extensionality
        have((term1 === term2) <=> (subterm1 === subterm2)) by Restate.from(pairExtensionality of (a := tagTerm, b := subterm1, c := tagTerm, d := subterm2))

        // STEP 2: Repeat pair extensionality until all variables have been pulled out of the term
        variables1
          .zip(variables2)
          .foldLeft(Seq.empty[Variable], variables1, Seq.empty[Variable], variables2, lastStep)((acc, v) =>

            // pulledVars1 are the variables that have been pulled out of the left term
            // remainingVars1 are the variables that are still in the left term
            // pulledVars2 are the variables that have been pulled out of the right term
            // remainingVars2 are the variables that are still in the right term
            val (pulledVars1, remainingVars1, pulledVars2, remainingVars2, previousFact) = acc

            // v1 and v2 are the variables that are being pulled out
            val (v1, v2) = v

            val updatedPulledVars1 = pulledVars1 :+ v1
            val updatedPulledVars2 = pulledVars2 :+ v2
            val updatedRemainingVars1 = remainingVars1.tail
            val updatedRemainingVars2 = remainingVars2.tail

            val subsubterm1 = subterm(updatedRemainingVars1)
            val subsubterm2 = subterm(updatedRemainingVars2)

            have(
              ((pulledVars1 === pulledVars2) /\ (pair(v1, subsubterm1) === pair(v2, subsubterm2))) <=>
                ((pulledVars1 === pulledVars2) /\ (v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Cut(
              pairExtensionality of (a := v1, b := subsubterm1, c := v2, d := subsubterm2),
              ADTThm.rightAndEquivalence of (p := pulledVars1 === pulledVars2, p1 := pair(v1, subsubterm1) === pair(v2, subsubterm2), p2 := (v1 === v2) /\ (subsubterm1 === subsubterm2))
            )
            val newFact = have(
              (term1 === term2) <=>
                ((updatedPulledVars1 === updatedPulledVars2) /\ (subsubterm1 === subsubterm2))
            ) by Apply(ADTThm.equivalenceRewriting).on(lastStep, previousFact)

            (updatedPulledVars1, updatedRemainingVars1, updatedPulledVars2, updatedRemainingVars2, newFact)
          )
      }
    
}

/**
  * Syntactic set theoretical interpretation of an algebraic data type. That is the least set closed under [[SyntacticConstructor]].
  * 
  * E.g. list is the smallest set containing nil and closed under the syntactic operation cons.
  * 
  * Injectivity between different constructors, introduction rules and structural induction are proved within this class.
  *
  * @constructor creates a new algebraic data type out of a user specification.
  * @param line the line at which the ADT is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param file the file in which the ADT is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param name the name of the ADT
  * @param constructors constructors of the ADT
  * @param typeVariables type variables used in the definition of this ADT
  */
private class SyntacticADT[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val name: String, 
  val constructors: Seq[SyntacticConstructor],
  val typeVariables: Variable ** N,
  ) {

  /**
   * Sequence of type variables used in the definition of this ADT
   */
  val typeVariablesSeq: Seq[Variable] = typeVariables.toSeq

  /**
   * Number of type variables used in the definition of this ADT
   */
  val typeArity: N = typeVariablesSeq.length.asInstanceOf[N]

  // ***************
  // * INJECTIVITY *
  // ***************

  /**
   * Theorem --- Injectivity of constructors.
   *
   *    Two instances of different construcors are always different.
   *
   * e.g. Nil != Cons(head, tail)
   */
  def injectivity(c1: SyntacticConstructor, c2: SyntacticConstructor) =
    require(c1.tag != c2.tag, "The given constructors must be different.")

    Lemma(!(c1.term1 === c2.term2)) {

      // STEP 0: Caching
      val tagTerm1: Term = c1.tagTerm
      val tagTerm2: Term = c2.tagTerm

      // STEP 1: Prove that the tags are different
      val diffTag = have(!(tagTerm1 === tagTerm2)) subproof {

        // STEP 1.1: Order the tags
        val minTag: Int = Math.min(c1.tag, c2.tag)
        val maxTag: Int = Math.max(c1.tag, c2.tag)

        val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

        // STEP 1.2: Apply successor injectivity to both tags until one becomes 0
        (1 to minTag).foldLeft(start)((fact, i) =>
          val midMaxTag = toTerm(maxTag - i)
          val midMinTag = toTerm(minTag - i)
          have(successor(midMaxTag) === successor(midMinTag) |- midMaxTag === midMinTag) by Cut(
            ADTThm.successorInjectivity of (n := midMaxTag, m := midMinTag),
            ADTThm.equivalenceApply of (p1 := successor(midMaxTag) === successor(midMinTag), p2 := midMaxTag === midMinTag)
          )
          have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(fact, lastStep)
        )

        val chainInjectivity = thenHave(!(toTerm(maxTag - minTag) === emptySet) |- !(tagTerm1 === tagTerm2)) by Restate

        // STEP 1.3: Conclude using the fact that 0 is not the successor of any number
        have(!(toTerm(maxTag - minTag) === emptySet)) by Exact(Ordinals.successorNonEmpty)
        have(thesis) by Cut(lastStep, chainInjectivity)
      }

      // STEP 2: Prove that the terms are different if the tags are different
      have(c1.term1 === c2.term2 |- (tagTerm1 === tagTerm2) /\ (c1.subterm1 === c2.subterm2)) by Apply(ADTThm.equivalenceRevApply).on(
        pairExtensionality of (a := tagTerm1, b := c1.subterm1, c := tagTerm2, d := c2.subterm2)
      )
      thenHave(!(tagTerm1 === tagTerm2) |- !(c1.term1 === c2.term2)) by Weakening

      // STEP 3: Conclude
      have(!(c1.term1 === c2.term2)) by Cut(diffTag, lastStep)
    }

  // *************************
  // * INTRODUCTION FUNCTION *
  // *************************

  /**
   * Formula describing whether the variables of a constructor belongs to their respective domain or s when they are self-referencing.
   *
   * @param c The considered constructor
   * @param s The set of elements in which self-referencing variables of the constructor are.
   */
  private def constructorVarsInDomain(c: SyntacticConstructor, s: Term): Formula = wellTypedFormula(c.signature)(s)

  /**
   * Formula describing whether an element x is an instance of a specific constructor.
   *
   * @param c The constructor we want to check if x is an instance of
   * @param x The element we want to check if it is an instance of c
   * @param s The set of elements in which self-referencing arguments of the constructor are.
   */
  private def isConstructor(c: SyntacticConstructor, x: Term, s: Term): Formula =
    existsSeq(c.variables2, wellTypedFormula(c.signature2)(s) /\ (x === c.term2))

  /**
   * Formula describing whether an element x is an instance of one of this ADT's constructors.
   *
   * @param x The element we want to check if it is an instance of some constructor.
   * @param s The set of elements in which self-referencing arguments of the constructor are.
   */
  private def isConstructor(x: Term, s: Term): Formula = \/(constructors.map(c => isConstructor(c, x, s)))

  /**
   * The introduction (class) function applies this ADT's constructors to the argument to given to it.
   * It then adds to elements of the resulting set to the one given in argument. For example, if all arguments of the
   * constructors were self-referencing we would have:
   *
   *    introductionFunction(s) = {y | y = c(x1, ..., xn) for some c ∈ constructors and x1, ..., xn ∈ s} ∪ s
   *
   * In order to avoid introducing a new symbol in the theory, we describe this function with a predicate.
   *
   * @param s the argument of this function, i.e. set of elements on which the constructors are applied
   * @param y the element we want to check if it is in the image of s under the introduction function.
   *
   * @return a formula describing whether y ∈ introductionFunction(s)
   *
   * @note The existence of the image of the introduction function is guaranteed by the union and replacement axioms. Moreover, it is not necessary to compute the union with s. It however simplifies further proofs. See [[this.heightSuccessorStrong]] for a proof of the equivalence of the two definitions.
   */
  private def isInIntroductionFunctionImage(s: Term)(y: Term): Formula = isConstructor(y, s) \/ in(y, s)
  

  /**
   * Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *      `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private val introductionFunctionMonotonic = benchmark(Lemma(ADTThm.classFunctionMonotonic(P2).substitute(P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)))) {
    // In the rest of the proof we assume that s ⊆ t

    // STEP 0: Caching predicates that are often used
    val subsetST = subset(s, t)
    val isConstructorXS = isConstructor(x, s)
    val isConstructorXT = isConstructor(x, t)

    // STEP 1: For each constructor, prove that if x is an instance of that constructor with self referencing arguments in s
    // then it is also an instance of some constructor with self referencing arguments in t
    val isConstructorXSImpliesT =
      for c <- constructors yield
        // STEP 2.0: Caching predicates that are often used
        // TODO change identifier
        val labelEq = x === c.term2
        val isConstructorCXS = isConstructor(c, x, s)
        val isConstructorCXT = isConstructor(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature2)(s)
        val varsWellTypedT = wellTypedFormula(c.signature2)(t)

        if c.arity == 0 then have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          // STEP 2.1: Prove that we can expand the domain of the (quantified) variables of the constructor
          val andSeq =
            for (v, ty) <- c.signature2 yield 
              ty match
                case Self => have((subsetST, varsWellTypedS) |- in(v, t)) by Weakening(subsetElim of (x := s, y := t, z := v))
                case GroundType(term) => have((subsetST, varsWellTypedS) |- in(v, term)) by Restate
                case f: FunctionType =>
                  have((subsetST, in(v, f.getOrElse(s))) |- in(v, f.getOrElse(t))) by Cut(f.monotonicity of (y := s, z := t), subsetElim of (x := f.getOrElse(s), y := f.getOrElse(t), z := v))
                  thenHave((subsetST, varsWellTypedS) |- in(v, f.getOrElse(t))) by Weakening
              
              
          val expandingDomain = have((subsetST, varsWellTypedS) |- varsWellTypedT) by RightAnd(andSeq: _*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have((subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq) by RightAnd(expandingDomain, weakeningLabelEq)

          // STEP 2.2: Prove that x stays an instance of this constructor if we expand the domain of the variables
          thenHave((subsetST, varsWellTypedS, labelEq) |- isConstructorCXT) by QuantifiersIntro(c.variables2)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- isConstructorCXT) by LeftAnd
          thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by QuantifiersIntro(c.variables2)

          // STEP 2.3: Weaken the conclusion to some constructor instead of a specific one
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    // STEP 3: Prove that this holds for any constructor
    // ? Steps 2 and 3 can be merged and optimized through the repeated use of an external theorem like [[ADTHelperTheorems.unionPreimageMonotonic]]
    if constructors.isEmpty then have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
    else have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(isConstructorXSImpliesT: _*)

    // STEP 4: Prove the thesis by showing that making the union with the function argument does not change the monotonicity
    thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
    have(subset(s, t) |- isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x)) by Cut(lastStep, ADTThm.unionPreimageMonotonic of (P := lambda(s, isConstructorXS)))
    thenHave(subset(s, t) |- forall(x, isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x))) by RightForall
    thenHave(subset(s, t) ==> forall(x, isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x))) by RightImplies
    thenHave(forall(t, subset(s, t) ==> forall(x, isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x)))) by RightForall
    thenHave(forall(s, forall(t, subset(s, t) ==> forall(x, isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(t)(x))))) by RightForall
  })

  private val introductionFunctionCumulative = benchmark(Lemma(ADTThm.classFunctionCumulative(P2).substitute(P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)))) {
    have(in(x, s) ==> isInIntroductionFunctionImage(s)(x)) by Restate
    thenHave(forall(x, in(x, s) ==> isInIntroductionFunctionImage(s)(x))) by RightForall
    thenHave(forall(s, forall(x, in(x, s) ==> isInIntroductionFunctionImage(s)(x)))) by RightForall
  })

  /**
   * Lemma --- Every constructor is in the image of the introduction function.
   *
   *      `For every c ∈ constructors, xi ∈ s, ..., xj ∈ s |- c(x1, ..., xn) ∈ introductionFunction(s)`
   */
  private val constructorIsInIntroductionFunction = benchmark(constructors
    .map(c =>
      // Caching
      val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

      c -> Lemma(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) {

        have(constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)) by Restate

        // Replace each variable on the LHS of the equality by a quantified variable and then introduce an existential quantifier
        (c.variables2).foldRight((c.variables1, List[Variable]()))((v, acc) =>

          // At each step remove a variable and add a quantified one
          val oldVariables = acc._1.init
          val newVariables = v :: acc._2
          val vars = oldVariables ++ newVariables

          thenHave(constructorVarsInDomainCS |- existsSeq(newVariables, wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term(vars) === c.term))) by RightExists

          (oldVariables, newVariables)
        )

        thenHave(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) by Weakening
      }
    )
    .toMap)

  // *******************
  // * HEIGHT FUNCTION *
  // *******************

  /**
   * The height function assigns to each natural number the set of elements of the ADT of that height or below.
   * The set of terms with height 0 is empty. Non inductive constructors have height one.
   * The height of an instance of an inductive constructor is the maximum height of its arguments plus one.
   * The height function is guaranteed to exists and is unique.
   *
   * @see [[this.heightFunctionUniqueness]]
   *
   * @param g the function we want to know if it is the height function
   *
   * @return a formula that is true if and only if g is the height function
   */
  private def isTheHeightFunction(h: Term): Formula = ADTThm.fixpointClassFunctionWithDomain(h)(P2)(N).substitute(P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)))

  private val heightDomainLimit = Axiom(ADTThm.nonsuccessorOrdinal(N))

  // Caching
  private val fIsTheHeightFunction: Formula = isTheHeightFunction(f)
  private val hIsTheHeightFunction: Formula = isTheHeightFunction(h)


  /**
   * Lemma --- The height function exists.
   *
   *     `∃h. h = height`
   */
  private val heightFunctionExistence = Lemma(exists(h, hIsTheHeightFunction)) {
    have(thesis) by Cut(ADTThm.domainIsOrdinal, ADTThm.fixpointClassFunctionWithDomainExistence of (P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)), d := N))
  }

  /**
   * Lemma --- If two functions are the height function then they are the same.
   *
   *     `f = height /\ h = height => f = h`
   */
  private val heightFunctionUniqueness2 = Lemma((fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) {
    have(thesis) by Restate.from(ADTThm.fixpointClassFunctionWithDomainUniqueness2 of (P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)), d := N))
  }

  /**
   * Lemma --- The height function is monotonic
   *
   *     `n <= m => height(n) ⊆ height(m)`
   *
   * TODO: Try to pull out
   */
  private val heightMonotonic = benchmark(Lemma((hIsTheHeightFunction, in(n, N), subset(m, n)) |- subset(app(h, m), app(h, n))) {
    have((introductionFunctionMonotonic.statement.right.head, introductionFunctionCumulative.statement.right.head, hIsTheHeightFunction, in(n, relationDomain(h)), subset(m, n)) |- subset(app(h, m), app(h, n))) by Weakening(ADTThm.fixpointFunctionMonotonicity of (P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x))))
    have((introductionFunctionCumulative.statement.right.head, hIsTheHeightFunction, in(n, relationDomain(h)), subset(m, n)) |- subset(app(h, m), app(h, n))) by 
      Cut(introductionFunctionMonotonic, lastStep)
    have((hIsTheHeightFunction, in(n, relationDomain(h)), subset(m, n)) |- subset(app(h, m), app(h, n))) by 
      Cut(introductionFunctionCumulative, lastStep)
    thenHave((hIsTheHeightFunction, in(n, N), subset(m, n), relationDomain(h) === N) |- subset(app(h, m), app(h, n))) by LeftSubstEq.withParametersSimple(
      List((relationDomain(h), N)),
      lambda(d, in(n, d))
    )
  })

  /**
   * Lemma --- The set of elements of height n + 1 is the set of elements of height n to which the introduction function is applied.
   *
   *     `height(n + 1) = introductionFunction(height(n))`
   */
  private val heightSuccessorWeak = benchmark(Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) {
    have((introductionFunctionMonotonic.statement.right.head, introductionFunctionCumulative.statement.right.head, hIsTheHeightFunction, in(successor(n), relationDomain(h))) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by Weakening(ADTThm.fixpointFunctionSuccessor of (P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x))))
    have((introductionFunctionCumulative.statement.right.head, hIsTheHeightFunction, in(successor(n), relationDomain(h))) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by 
      Cut(introductionFunctionMonotonic, lastStep)
    have((hIsTheHeightFunction, in(successor(n), relationDomain(h))) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by 
      Cut(introductionFunctionCumulative, lastStep)
    thenHave((hIsTheHeightFunction, in(successor(n), N), relationDomain(h) === N) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by LeftSubstEq.withParametersSimple(
      List((relationDomain(h), N)),
      lambda(d, in(successor(n), d))
    )
    have((hIsTheHeightFunction, ADTThm.nonsuccessorOrdinal(N), in(n, N), relationDomain(h) === N) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by Cut(ADTThm.nonsuccessorOrdinalIsInductive of (m := n, n := N), lastStep)
    have((hIsTheHeightFunction, in(n, N), relationDomain(h) === N) |- in(x, app(h, successor(n))) <=> isInIntroductionFunctionImage(app(h, n))(x)) by Cut(heightDomainLimit, lastStep)
  })

  // ********
  // * TERM *
  // ********

  /**
   * Formula describing this ADT's term, i.e. the set of all its instances.
   * It equal to the union of all the terms that have a height.
   *
   *   `adt = ∪ height(n) = {x | ∃n ∈ N. x ∈ height(n)}`
   *
   * @param adt the set chracterizing this ADT
   */
  private def termDescription(adt: Term): Formula = forall(t, in(t, adt) <=> forall(h, hIsTheHeightFunction ==> in(t, unionRange(h))))

  /**
   * Lemma --- There exists a unique set satisfying the definition of this ADT
   *
   *     `∃!z. z = ADT
   */
  private val termExistence = benchmark(Lemma(existsOne(z, termDescription(z))) {
    have(thesis) by Cut(ADTThm.domainIsOrdinal, ADTThm.fixpointUniqueness of (P2 := lambda((x, s), isInIntroductionFunctionImage(s)(x)), d := N))
  })

  /**
   * Class function defining the ADT. Takes as parameters the type variables of the ADT and return the set of all its instances.
   */
  val polymorphicTerm = FunctionDefinition[N](name, line.value, file.value)(typeVariablesSeq, z, termDescription(z), termExistence).label

  /**
   * The set of all instances of the ADT where the type variables are not instantiated (i.e. are kept variable).
   */
  val term = polymorphicTerm.applySeq(typeVariablesSeq)

  private val termDef = Lemma(hIsTheHeightFunction |- term === unionRange(h)) {

      // STEP 0 : Instantiate the definition of this ADT and recover the forward and backward implications
      have(termDescription(term)) by InstantiateForall(term)(polymorphicTerm.definition)
      val termDescr = thenHave(in(x, term) <=> forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by InstantiateForall(x)
      val termDescrForward = have(in(x, term) |- forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by Cut(
        termDescr,
        ADTThm.equivalenceApply of (p1 := in(x, term), p2 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
      )
      val termDescrBackward = have(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- in(x, term)) by Cut(
        termDescr,
        ADTThm.equivalenceRevApply of (p2 := in(x, term), p1 := forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))))
      )

      // STEP 1.1 : Forward implication
      have(forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))) |- forall(h, hIsTheHeightFunction ==> in(x, unionRange(h)))) by Hypothesis
      thenHave((forall(h, hIsTheHeightFunction ==> in(x, unionRange(h))), hIsTheHeightFunction) |- in(x, unionRange(h))) by InstantiateForall(h)
      have((hIsTheHeightFunction, in(x, term)) |- in(x, unionRange(h))) by Cut(termDescrForward, lastStep)
      val forward = thenHave(hIsTheHeightFunction |- in(x, term) ==> in(x, unionRange(h))) by RightImplies

      // STEP 1.2 : Backward implication, follows from uniqueness of the height function
      have(in(x, unionRange(h)) |- in(x, unionRange(h))) by Hypothesis
      thenHave((f === h, in(x, unionRange(h))) |- in(x, unionRange(f))) by RightSubstEq.withParametersSimple(List((f, h)), lambda(h, in(x, unionRange(h))))
      have((fIsTheHeightFunction, hIsTheHeightFunction, in(x, unionRange(h))) |- in(x, unionRange(f))) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave((hIsTheHeightFunction, in(x, unionRange(h))) |- fIsTheHeightFunction ==> in(x, unionRange(f))) by RightImplies
      thenHave((hIsTheHeightFunction, in(x, unionRange(h))) |- forall(f, fIsTheHeightFunction ==> in(x, unionRange(f)))) by RightForall
      have((hIsTheHeightFunction, in(x, unionRange(h))) |- in(x, term)) by Cut(lastStep, termDescrBackward)
      val backward = thenHave(hIsTheHeightFunction |- in(x, unionRange(h)) ==> in(x, term)) by RightImplies

      have(hIsTheHeightFunction |- in(x, term) <=> in(x, unionRange(h))) by RightIff(forward, backward)
      thenHave(hIsTheHeightFunction |- forall(x, in(x, term) <=> in(x, unionRange(h)))) by RightForall
      thenHave((hIsTheHeightFunction, (term === unionRange(h)) <=> forall(x, in(x, term) <=> in(x, unionRange(h)))) |- term === unionRange(h)) by RightSubstIff.withParametersSimple(
        List((term === unionRange(h), forall(x, in(x, term) <=> in(x, unionRange(h))))),
        lambda(p, p)
      )
      have(thesis) by Cut(extensionalityAxiom of (x := term, y := unionRange(h)), lastStep)
    }

  // *************************
  // * TYPING / INTRODUCTION *
  // *************************

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` x ∈ ADT <=> ∃n ∈ N. x ∈ height(n)`
   */
  private val termHasHeight = benchmark(Lemma(hIsTheHeightFunction |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) {
    have((functional(h), relationDomain(h) === N) |- in(x, unionRange(h)) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) by RightSubstEq.withParametersSimple(
      List((relationDomain(h), N)),
      lambda(z, in(x, unionRange(h)) <=> ∃(n, in(n, z) /\ in(x, app(h, n))))
    )(ADTThm.unionRangeMembership of (z := x))
    thenHave(hIsTheHeightFunction |- in(x, unionRange(h)) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) by Weakening
    thenHave((hIsTheHeightFunction, term === unionRange(h)) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))) by RightSubstEq.withParametersSimple(
      List((term, unionRange(h))),
      lambda(z, in(x, z) <=> ∃(n, in(n, N) /\ in(x, app(h, n))))
    )
    have(thesis) by Cut(termDef, lastStep)
  })

  private val termHasHeightBackward = benchmark(Lemma((hIsTheHeightFunction, in(n, N), in(x, app(h, n))) |- in(x, term)) {
    have((in(n, N), in(x, app(h, n))) |- in(n, N) /\ in(x, app(h, n))) by Restate
    thenHave((in(n, N), in(x, app(h, n))) |- exists(m, in(m, N) /\ in(x, app(h, m)))) by RightExists
    have(thesis) by Apply(ADTThm.equivalenceRevApply).on(lastStep, termHasHeight.asInstanceOf)
  })

  private val heightSubsetTerm = benchmark(Lemma((hIsTheHeightFunction, in(n, N)) |- subset(app(h, n), term)) {
    have((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, n)) ==> in(x, term)) by RightImplies(termHasHeightBackward)
    thenHave((hIsTheHeightFunction, in(n, N)) |- forall(x, in(x, app(h, n)) ==> in(x, term))) by RightForall
    have(thesis) by Cut(lastStep, subsetIntro of (x := app(h, n), y := term))
  })

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` xi, ..., xj ∈ ADT <=> ∃n ∈ N. xi, ..., xj ∈ height(n)`
   *
   * TODO: Work this out
   * TODO: Split into two lemmas
   */
  private val termsHaveHeight = benchmark(constructors
    .map(c =>
      c -> Lemma(hIsTheHeightFunction |- (constructorVarsInDomain(c, term) <=> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))) {

        if c.variables.isEmpty then have(thesis) by Weakening(ADTThm.existsNat)
        else

          // STEP 1: Backward implication

          val backward = have(hIsTheHeightFunction |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)) subproof {
            val andSeq = for (v, ty) <- c.signature yield 
              ty match
                case Self =>
                  have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, term)) by Weakening(termHasHeightBackward of (x := v))
                case GroundType(t) =>
                  have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, t)) by Restate
                case f: FunctionType =>
                  have((hIsTheHeightFunction, in(n, N)) |- subset(f.getOrElse(app(h, n)), f.getOrElse(term))) by Cut(heightSubsetTerm, f.monotonicity of (y := app(h, n), z := term))
                  have((hIsTheHeightFunction, in(n, N), in(v, f.getOrElse(app(h, n)))) |- in(v, f.getOrElse(term))) by Cut(
                    lastStep, subsetElim of (z := v, x := f.getOrElse(app(h, n)), y := f.getOrElse(term))
                  )
                  thenHave((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(v, f.getOrElse(term))) by Weakening

            have((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by RightAnd(andSeq: _*)
            thenHave((hIsTheHeightFunction, exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by LeftExists
          }

          // STEP 2: Forward implication

          val forward = have(hIsTheHeightFunction |- constructorVarsInDomain(c, term) ==> ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) subproof {
            val nSeq: Seq[Variable] = (0 until c.variables.size).map(i => Variable(s"n$i"))

            val niInN = /\(nSeq.map(ni => in(ni, N)))
            val constructorVarsInHNi = /\ (c.signature.zip(nSeq).map((p, ni) => in(p._1, p._2.getOrElse(app(h, ni)))))
            val constructorVarsInHNiAndN = c.signature.zip(nSeq).map((p, ni) => in(ni, N) /\ in(p._1, p._2.getOrElse(app(h, ni))))

            val max = if c.arity == 0 then emptySet else nSeq.reduce[Term](setUnion(_, _))
            val maxInN = have(niInN |- in(max, N)) by Sorry

            val andSeq = for ((v, ty), ni) <- c.signature.zip(nSeq) yield
              val niInMax = have(subset(ni, max)) by Sorry

              ty match
                case Self =>
                  have((hIsTheHeightFunction, in(max, N)) |- subset(app(h, ni), app(h, max))) by 
                    Cut(niInMax, heightMonotonic of (m := ni, n := max))
                  have((hIsTheHeightFunction, in(max, N), in(v, app(h, ni))) |- in(v, app(h, max))) by 
                    Cut(lastStep, subsetElim of (z := v, x := app(h, ni), y := app(h, max)))
                case GroundType(t) =>
                  have((hIsTheHeightFunction, in(max, N), in(v, t)) |- in(v, t)) by Restate
                case f: FunctionType => 
                  have((hIsTheHeightFunction, in(max, N)) |- subset(app(h, ni), app(h, max))) by 
                    Cut(niInMax, heightMonotonic of (m := ni, n := max))
                  have((hIsTheHeightFunction, in(max, N)) |- subset(f.getOrElse(app(h, ni)), f.getOrElse(app(h, max)))) by 
                    Cut(lastStep, f.monotonicity of (y := app(h, ni), z := app(h, max)))
                  have((hIsTheHeightFunction, in(max, N), in(v, f.getOrElse(app(h, ni)))) |- in(v, f.getOrElse(app(h, max)))) by 
                    Cut(lastStep, subsetElim of (z := v, x := f.getOrElse(app(h, ni)), y := f.getOrElse(app(h, max))))
            
              thenHave((hIsTheHeightFunction, in(max, N), constructorVarsInHNi) |- in(v, ty.getOrElse(app(h, max)))) by Weakening
            
            have((hIsTheHeightFunction, in(max, N), constructorVarsInHNi) |- constructorVarsInDomain(c, app(h, max))) by RightAnd(andSeq: _*)
            have((hIsTheHeightFunction, niInN, constructorVarsInHNi) |- constructorVarsInDomain(c, app(h, max))) by Cut(maxInN, lastStep)
            have((hIsTheHeightFunction, niInN, constructorVarsInHNi) |- in(max, N) /\ constructorVarsInDomain(c, app(h, max))) by RightAnd(maxInN, lastStep)
            thenHave((hIsTheHeightFunction, niInN, constructorVarsInHNi) |- exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by RightExists
            thenHave(constructorVarsInHNiAndN.toSet + hIsTheHeightFunction |- exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by Restate

            


            // c.signature.zip(nSeq).foldLeft((Seq[Formula](), constructorVarsInHNiAndN.toList))( (p, el) => 
            //   val ((v, ty), ni) = el
            //   val (processedFormulas, remainingFormulas) = p
            //   val (processedFormulasSet, remainingFormulasSet) = (processedFormulas.toSet, remainingFormulas.tail.toSet)

            //   thenHave((processedFormulasSet + exists(ni, in(ni, N) /\ in(v, ty.getOrElse(app(h, ni))))) ++ remainingFormulas) by LeftExists
            //   thenHave((processedFormulasSet + ) ++ remainingFormulas) by LeftExists

            //   (processedFormulas, remainingFormulas.tail)
            // )

            sorry
          }

          // STEP 3: Conclude
          have(thesis) by RightIff(forward, backward)
      }
    )
    .toMap)

  /**
   * Lemma --- If all inductive arguments of a constructor have height below n then the instance of
   * this constructor has height below n + 1.
   *
   *      ` xi, ..., xj ∈ height(n) |- c(x1, ..., xn) ∈ height(n + 1)`
   */
  private val heightConstructor = benchmark(constructors
    .map(c =>
      c -> Lemma((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) {

        // Caching
        val constructorInIntroFunHeight = isInIntroductionFunctionImage(app(h, n))(c.term)

        // Chaining the lemma on the elements of height n + 1 and the one on constructors being in the image of the introduction function
        have((hIsTheHeightFunction, in(n, N), constructorInIntroFunHeight) |- in(c.term, app(h, successor(n)))) by Cut(
          heightSuccessorWeak of (x := c.term),
          ADTThm.equivalenceRevApply of (p1 := constructorInIntroFunHeight, p2 := in(c.term, app(h, successor(n))))
        )
        have((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, app(h, successor(n)))) by Cut(constructorIsInIntroductionFunction(c) of (s := app(h, n)), lastStep)
      }
    )
    .toMap)

  /**
   * Lemma --- If all inductive arguments of a constructor are in this ADT, and the non inductive ones in their respective domain,
   * then the instance of this constructor is in this ADT as well. Also known as introduction rules.
   *
   *      ` xi, ..., xj ∈ ADT |- c(x1, ..., xn) ∈ ADT`
   */
  val intro = benchmark(constructors
    .map(c => {
      c ->
        Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))) {
          // STEP 0: Instantiate the forward direction of termsHaveHeight.
          val termsHaveHeightForward = have((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) by Cut(
            termsHaveHeight(c),
            ADTThm.equivalenceApply of (p1 := constructorVarsInDomain(c, term), p2 := exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
          )

          // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
          have((hIsTheHeightFunction, in(n, N), in(c.term, app(h, successor(n)))) |- in(c.term, term)) by Cut(ADTThm.successorIsNat, termHasHeightBackward of (n := successor(n), x := c.term))

          // STEP 2: Prove that if the inductive arguments of the constructor have height then the instance of the constructor is in the ADT.
          have((hIsTheHeightFunction, in(n, N), constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by Cut(heightConstructor(c), lastStep)

          // STEP 3: Prove that if the inductive arguments of the constructor are in the ADT then they have a height and therefore
          // the instance of the constructor is in the ADT.
          thenHave((hIsTheHeightFunction, in(n, N) /\ constructorVarsInDomain(c, app(h, n))) |- in(c.term, term)) by LeftAnd
          thenHave((hIsTheHeightFunction, exists(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))) |- in(c.term, term)) by LeftExists
          have((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- in(c.term, term)) by Cut(termsHaveHeightForward, lastStep)

          // STEP 4: Remove lingering assumptions
          thenHave((exists(h, hIsTheHeightFunction), constructorVarsInDomain(c, term)) |- in(c.term, term)) by LeftExists
          have(constructorVarsInDomain(c, term) |- in(c.term, term)) by Cut(heightFunctionExistence, lastStep)
        }
    })
    .toMap)

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  /**
   * Lemma --- An element has height n + 1 if and only if it is the instance of some constructor with inductive arguments of height n.
   *
   *    ` x ∈ height(n + 1) <=> x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n)`
   */
  private lazy val heightSuccessorStrong = benchmark(Lemma((hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isConstructor(x, app(h, n))) {

    // STEP 0: Caching
    val isIntroductionFunImageHN = isInIntroductionFunctionImage(app(h, n))(x)
    val isConstructorXHN = isConstructor(x, app(h, n))

    // STEP 1: Prove the forward implication
    val forward = have((hIsTheHeightFunction, in(n, N)) |- isIntroductionFunImageHN ==> isConstructorXHN) subproof {

      def inductionFormulaN: Formula = isIntroductionFunImageHN ==> isConstructorXHN
      val inductionFormulaSuccN: Formula = inductionFormulaN.substitute(n := successor(n))

      // STEP 1.1 : Base case
      val isContructorXHEmptySet = isConstructor(x, app(h, emptySet))
      val baseCaseLeft = have(isContructorXHEmptySet |- isContructorXHEmptySet) by Hypothesis
      val baseCaseRight = have((hIsTheHeightFunction, in(x, app(h, emptySet))) |- ()) by Sorry //Restate.from(heightZero)
      have((hIsTheHeightFunction, isInIntroductionFunctionImage(app(h, emptySet))(x)) |- isContructorXHEmptySet) by LeftOr(baseCaseLeft, baseCaseRight)
      thenHave(hIsTheHeightFunction |- isInIntroductionFunctionImage(app(h, emptySet))(x) ==> isContructorXHEmptySet) by RightImplies
      val inductiveCaseRemaining = have((hIsTheHeightFunction, forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) |- forall(n, in(n, N) ==> inductionFormulaN)) by 
      Sorry
      // Cut(
      //   lastStep,
      //   ADTThm.natInduction of (P := lambda(n, inductionFormulaN))
      // )

      // STEP 1.2 : Use monotonicity to prove that y ∈ height(n) => y ∈ height(n + 1)
      have((hIsTheHeightFunction, in(n, N), subset(n, successor(n))) |- subset(app(h, n), app(h, successor(n)))) by Cut(ADTThm.successorIsNat, heightMonotonic of (n := successor(n), m := n))
      val heightSubsetSucc = have((hIsTheHeightFunction, in(n, N)) |- subset(app(h, n), app(h, successor(n)))) by Cut(Ordinals.subsetSuccessor of (a := n), lastStep)
      val liftHeight = have((hIsTheHeightFunction, in(n, N), in(z, app(h, n))) |- in(z, app(h, successor(n)))) by Cut(lastStep, subsetElim of (x := app(h, n), y := app(h, successor(n))))

      // STEP 1.3 : Generalize the above result to show that if for some c, x = c(x1, ..., xn) with xi, ..., xj ∈ height(n)
      // then for some c', x = c'(x1, ..., xn) with xi, ..., xj ∈ height(n + 1).

      // Caching
      val isConstructorXHSuccN = isConstructor(x, app(h, successor(n)))
      val liftConstructorHeight =
        if constructors.size == 0 then have((hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN) by Restate
        else
          val liftConstructorHeightOrSequence =
            for c <- constructors yield

              // Caching
              val isConstructorCXHN = isConstructor(c, x, app(h, n))
              val isConstructorCXHSuccN = isConstructor(c, x, app(h, successor(n)))
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHSuccN = constructorVarsInDomain(c, app(h, successor(n)))

              if c.arity == 0 then have((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by Restate
              else
                val liftHeightAndSequence =
                  for (v, ty) <- c.signature yield 
                    ty match
                      case Self => 
                        have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(v, app(h, successor(n)))) by Weakening(liftHeight of (z := v))
                      case GroundType(t) =>
                        have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(v, t)) by Restate
                      case f: FunctionType =>
                        have((hIsTheHeightFunction, in(n, N)) |- subset(f.getOrElse(app(h, n)), f.getOrElse(app(h, successor(n))))) by Cut(heightSubsetSucc, f.monotonicity of (y := app(h, n), z := app(h, successor(n))))
                        have((hIsTheHeightFunction, in(n, N), in(v, f.getOrElse(app(h, n)))) |- in(v, f.getOrElse(app(h, successor(n))))) by Cut(lastStep, subsetElim of (x := f.getOrElse(app(h, n)), y := f.getOrElse(app(h, successor(n))), z := v))
                        thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(v, f.getOrElse(app(h, successor(n))))) by Weakening

                val left = have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInHSuccN) by RightAnd(liftHeightAndSequence: _*)
                val right = have(x === c.term |- x === c.term) by Hypothesis

                have((hIsTheHeightFunction, in(n, N), constructorVarsInHN, (x === c.term)) |- constructorVarsInHSuccN /\ (x === c.term )) by RightAnd(
                  left,
                  right
                )
                thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN /\ (x === c.term)) |- constructorVarsInHSuccN /\ (x === c.term)) by LeftAnd
                thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN /\ (x === c.term)) |- isConstructorCXHSuccN) by QuantifiersIntro(c.variables)
                thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorCXHSuccN) by QuantifiersIntro(c.variables)

              thenHave((hIsTheHeightFunction, in(n, N), isConstructorCXHN) |- isConstructorXHSuccN) by Weakening

          have((hIsTheHeightFunction, in(n, N), isConstructorXHN) |- isConstructorXHSuccN) by LeftOr(liftConstructorHeightOrSequence: _*)

      // STEP 1.4: Show that x ∈ introductionFunction(height(n + 1)) => for some c, x = c(x1, ..., xn)
      // with xi, ..., xj ∈ height(n + 1).
      val heightSuccessorWeakForward = have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isIntroductionFunImageHN) by Cut(
        heightSuccessorWeak,
        ADTThm.equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isIntroductionFunImageHN)
      )
      have((inductionFormulaN, isIntroductionFunImageHN) |- isConstructorXHN) by Restate
      have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n))), inductionFormulaN) |- isConstructorXHN) by Cut(heightSuccessorWeakForward, lastStep)
      val right = have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n))), inductionFormulaN) |- isConstructorXHSuccN) by Cut(lastStep, liftConstructorHeight)
      val left = have(isConstructorXHSuccN |- isConstructorXHSuccN) by Hypothesis
      have((hIsTheHeightFunction, in(n, N), inductionFormulaN, isInIntroductionFunctionImage(app(h, successor(n)))(x)) |- isConstructorXHSuccN) by LeftOr(left, right)

      // STEP 1.5: Conclude
      thenHave((hIsTheHeightFunction, in(n, N), inductionFormulaN) |- inductionFormulaSuccN) by RightImplies
      thenHave((hIsTheHeightFunction, in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN) by RightImplies
      thenHave(hIsTheHeightFunction |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)) by RightImplies
      thenHave(hIsTheHeightFunction |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) by RightForall
      have(hIsTheHeightFunction |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(lastStep, inductiveCaseRemaining)
      thenHave(hIsTheHeightFunction |- in(n, N) ==> inductionFormulaN) by InstantiateForall(n)
    }

    // STEP 2: Prove the backward implication
    val backward = have((hIsTheHeightFunction, in(n, N)) |- isConstructorXHN ==> isIntroductionFunImageHN) by Restate

    // STEP 3: Conclude
    have((hIsTheHeightFunction, in(n, N)) |- isIntroductionFunImageHN <=> isConstructorXHN) by RightIff(forward, backward)
    
    thenHave((hIsTheHeightFunction, in(n, N), isIntroductionFunImageHN <=> in(x, app(h, successor(n)))) |- in(x, app(h, successor(n))) <=> isConstructorXHN) by RightSubstIff.withParametersSimple(
      List((isIntroductionFunImageHN, in(x, app(h, successor(n))))),
      lambda(p, p <=> isConstructorXHN)
    )
    have(thesis) by Cut(heightSuccessorWeak, lastStep)
  })

  /**
   * Generates the structural inductive case for a given constructor.
   *
   * @param c the constructor
   */
  lazy val inductiveCase: Map[SyntacticConstructor, Formula] = constructors
    .map(c =>
      c -> c.signature.foldRight[Formula](P(c.term))((el, fc) =>
        val (v, ty) = el
        ty match
          case Self => forall(v, in(v, term) ==> (P(v) ==> fc))
          case GroundType(t) => forall(v, in(v, t) ==> fc)
          case f : FunctionType => 
            forall(v, in(v, f.getOrElse(term)) ==> (forallSeq(f.variables, f.wellTypedDomains ==>  P(appSeq(v)(f.variables))) ==> fc))
      )
    )
    .toMap

  /**
   * Lemma --- Structural induction principle for this ADT.
   *
   *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
   */
  lazy val induction = benchmark(Lemma(constructors.foldRight[Formula](forall(x, in(x, term) ==> P(x)))((c, f) => inductiveCase(c) ==> f)) {

    // List of cases to prove for structural induction to hold
    val structuralInductionPreconditions: Formula = /\(constructors.map(inductiveCase))

    // We want to prove the claim by induction on the height of n, i.e. prove that for any
    // n in N, P holds.
    def inductionFormula(n: Term): Formula = forall(x, in(x, app(h, n)) ==> P(x))
    val inductionFormulaN: Formula = inductionFormula(n)
    val inductionFormulaSuccN: Formula = inductionFormula(successor(n))

    // STEP 1: Prove the base case
    have(hIsTheHeightFunction |- in(x, app(h, emptySet)) ==> P(x)) by Sorry //Weakening(heightZero)
    val zeroCase = thenHave(hIsTheHeightFunction |- inductionFormula(emptySet)) by RightForall

    val inductiveCaseRemaining = have((hIsTheHeightFunction, forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) |- forall(n, in(n, N) ==> inductionFormulaN)) by 
    Sorry
    // Cut(
    //   zeroCase,
    //   ADTThm.natInduction of (P := lambda(n, inductionFormulaN))
    // )

    // STEP 2: Prove the inductive case
    val succCase = have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN))) subproof {

      // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
      val isConstructorImpliesP = have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) subproof {

        if constructors.isEmpty then have(thesis) by Restate
        else
          val orSeq =
            (for c <- constructors yield

              // Caching
              val constructorPrecondition = inductiveCase(c)
              val constructorVarsInHN = constructorVarsInDomain(c, app(h, n))
              val constructorVarsInHNEx = ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n)))
              val constructorVarsInTerm = constructorVarsInDomain(c, term)

              // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
              val constructorQuantVarsInHNToTerm = have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInTerm) subproof {
                have((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- in(n, N) /\ constructorVarsInHN) by Restate
                val consVarL = thenHave((hIsTheHeightFunction, in(n, N), constructorVarsInHN) |- constructorVarsInHNEx) by RightExists
                have((constructorVarsInTerm <=> constructorVarsInHNEx, constructorVarsInHNEx) |- constructorVarsInTerm) by Restate.from(
                  ADTThm.equivalenceRevApply of (p1 := constructorVarsInTerm, p2 := constructorVarsInHNEx)
                )
                have((hIsTheHeightFunction, constructorVarsInHNEx) |- constructorVarsInTerm) by Cut(
                  termsHaveHeight(c),
                  lastStep
                )
                have(thesis) by Cut(consVarL, lastStep)
              }


              // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
              have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- constructorPrecondition) by Restate

              c.signature
                .foldLeft(lastStep)((fact, el) =>
                  val (v, ty) = el

                  fact.statement.right.head match
                    case Forall(_, factCclWithoutForall) =>
                      thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- factCclWithoutForall) by InstantiateForall(v)

                      factCclWithoutForall match
                        case Implies(membership, subformula) =>
                          ty match
                            case Self =>
                              subformula match
                                case Implies(hypothesis, subSubFormula) =>
                                  val proofSubSubFormula = thenHave(
                                    (hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN, P(v)) |- subSubFormula
                                  ) by Weakening

                                  have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                                  thenHave(inductionFormulaN |- in(v, app(h, n)) ==> P(v)) by InstantiateForall(v)
                                  thenHave((inductionFormulaN, constructorVarsInHN) |- P(v)) by Weakening

                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN) |- subSubFormula) by Cut(
                                    lastStep,
                                    proofSubSubFormula
                                  )
                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- subSubFormula) by Cut(
                                    constructorQuantVarsInHNToTerm,
                                    lastStep
                                  )

                                case _ => throw UnreachableException

                            case GroundType(t) =>
                              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- subformula) by Restate

                            case fn: FunctionType => 
                              subformula match
                                case Implies(hypothesis, subSubFormula) =>
                                  val proofSubSubFormula = thenHave(
                                    (hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN, hypothesis) |- subSubFormula
                                  ) by Weakening

                                  val appliedFun = appSeq(v)(fn.variables)

                                  val appVZInHN = have((in(v, fn.getOrElse(app(h, n))), fn.wellTypedDomains) |- in(appliedFun, app(h, n))) by TypeChecker.prove

                                  have(inductionFormulaN |- inductionFormulaN) by Hypothesis
                                  thenHave((inductionFormulaN, in(appliedFun, app(h, n))) |- P(appliedFun)) by InstantiateForall(appliedFun)
                                  have((inductionFormulaN, in(v, fn.getOrElse(app(h, n))), fn.wellTypedDomains) |- P(appliedFun)) by Cut(appVZInHN, lastStep)
                                  thenHave((inductionFormulaN, in(v, fn.getOrElse(app(h, n)))) |- fn.wellTypedDomains ==>
                                  P(appliedFun)) by RightImplies
                                  thenHave((inductionFormulaN, in(v, fn.getOrElse(app(h, n)))) |- forallSeq(fn.variables, fn.wellTypedDomains ==> P(appliedFun))) by QuantifiersIntro(fn.variables)
                                  thenHave((inductionFormulaN, constructorVarsInHN) |- forallSeq(fn.variables, fn.wellTypedDomains ==> P(appliedFun))) by Weakening

                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInTerm, constructorVarsInHN) |- subSubFormula) by Cut(
                                    lastStep,
                                    proofSubSubFormula
                                  )
                                  have((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- subSubFormula) by Cut(
                                    constructorQuantVarsInHNToTerm,
                                    lastStep
                                  )
                                
                                case _ => throw UnreachableException

                        case _ => throw UnreachableException
                    case _ => throw UnreachableException
                )

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN) |- P(c.term)) by Restate

              // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(n) then P(x).
              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN, x === c.term) |- P(x)) by RightSubstEq
                .withParametersSimple(List((x, c.term)), lambda(x, P(x)))

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, constructorVarsInHN /\ (x === c.term)) |- P(x)) by LeftAnd

              thenHave((hIsTheHeightFunction, constructorPrecondition, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by QuantifiersIntro(c.variables)
              thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(c, x, app(h, n))) |- P(x)) by Weakening
            ).toSeq


          have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, isConstructor(x, app(h, n))) |- P(x)) by LeftOr(orSeq: _*)
      }

      // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
      have((hIsTheHeightFunction, in(n, N), in(x, app(h, successor(n)))) |- isConstructor(x, app(h, n))) by Cut(
        heightSuccessorStrong,
        ADTThm.equivalenceApply of (p1 := in(x, app(h, successor(n))), p2 := isConstructor(x, app(h, n)))
      )
      have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN, in(x, app(h, successor(n)))) |- P(x)) by Cut(lastStep, isConstructorImpliesP)

      // STEP 2.3: Conclude
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN) |- in(x, app(h, successor(n))) ==> P(x)) by RightImplies

      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaN) |- inductionFormulaSuccN) by RightForall
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- inductionFormulaN ==> inductionFormulaSuccN) by RightImplies
      thenHave((hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> (inductionFormulaN ==> inductionFormulaSuccN)) by RightImplies
      thenHave(thesis) by RightForall
    }

    // STEP 3: Conclude

    have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(lastStep, inductiveCaseRemaining)
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- inductionFormulaN) by InstantiateForall(n)
    thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N) /\ in(x, app(h, n))) |- P(x)) by InstantiateForall(x)
    val exImpliesP = thenHave((hIsTheHeightFunction, structuralInductionPreconditions, exists(n, in(n, N) /\ in(x, app(h, n)))) |- P(x)) by LeftExists
    have((hIsTheHeightFunction, in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))) by Cut(termHasHeight, ADTThm.equivalenceApply of (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n)))))

    have((hIsTheHeightFunction, structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(lastStep, exImpliesP)
    thenHave((exists(h, hIsTheHeightFunction), structuralInductionPreconditions, in(x, term)) |- P(x)) by LeftExists
    have((structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(heightFunctionExistence, lastStep)
    thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
    thenHave(structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
  })


  // /**
  //  * Lemma --- Structural induction principle for this ADT.
  //  *
  //  *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
  //  */
  // lazy val induction = benchmark(Lemma(constructors.foldRight[Formula](forall(x, in(x, term) ==> P(x)))((c, f) => inductiveCase(c) ==> f)) {

  //   // List of cases to prove for structural induction to hold
  //   val structuralInductionPreconditions: Formula = /\(constructors.map(inductiveCase))

  //   // We want to prove the claim by induction on the height of n, i.e. prove that for any
  //   // n in N, P holds.
  //   def inductionFormula = (t: Term) => forall(x, in(x, app(h, t)) ==> P(x))
  //   val inductionFormulaM: Formula = inductionFormula(m)
  //   val inductionFormulaN: Formula = inductionFormula(n)

  //   // STEP 2: Prove the inductive case
  //   val inductiveStep = have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> (forall(m, in(m, n) ==> inductionFormulaM) ==> inductionFormulaN))) subproof {

  //     have(hIsTheHeightFunction |- in(x, app(h, emptySet)) ==> P(x)) by Weakening(heightZero)
  //     thenHave(hIsTheHeightFunction |- inductionFormula(emptySet)) by RightForall
  //     val zeroCase = thenHave((hIsTheHeightFunction, n === emptySet) |- inductionFormulaN) by RightSubstEq.withParametersSimple(
  //       List((n, emptySet)), lambda(n, inductionFormulaN)
  //     )

  //     // STEP 2.1 : Prove that if the x = c(x1, ..., xn) for some c and xi, ..., xj ∈ height(n) then P(x) holds.
  //     val isConstructorImpliesP = have((hIsTheHeightFunction, structuralInductionPreconditions, inductionFormulaM, in(m, N), isConstructor(x, app(h, m))) |- P(x)) subproof {

  //       if constructors.isEmpty then have(thesis) by Restate
  //       else
  //         val orSeq =
  //           (for c <- constructors yield

  //             // Caching
  //             val constructorPrecondition = inductiveCase(c)
  //             val constructorVarsInHM = constructorVarsInDomain(c, app(h, m))
  //             val constructorVarsInHMEx = ∃(m, in(m, N) /\ constructorVarsInDomain(c, app(h, m)))
  //             val constructorVarsInTerm = constructorVarsInDomain(c, term)

  //             // STEP 2.1.1: Prove that if xi, ..., xj ∈ height(n) then xi, ..., xj ∈ ADT.
  //             val constructorQuantVarsInHNToTerm = have((hIsTheHeightFunction, in(m, N), constructorVarsInHM) |- constructorVarsInTerm) subproof {
  //               have((hIsTheHeightFunction, in(m, N), constructorVarsInHM) |- in(m, N) /\ constructorVarsInHM) by Restate
  //               val consVarL = thenHave((hIsTheHeightFunction, in(m, N), constructorVarsInHM) |- constructorVarsInHMEx) by RightExists
  //               have((constructorVarsInTerm <=> constructorVarsInHMEx, constructorVarsInHMEx) |- constructorVarsInTerm) by Restate.from(
  //                 ADTThm.equivalenceRevApply of (p1 := constructorVarsInTerm, p2 := constructorVarsInHMEx)
  //               )
  //               have((hIsTheHeightFunction, constructorVarsInHMEx) |- constructorVarsInTerm) by Cut(
  //                 termsHaveHeight(c),
  //                 lastStep
  //               )
  //               have(thesis) by Cut(consVarL, lastStep)
  //             }


  //             // STEP 2.1.2: Prove that if xi, ..., xj ∈ height(n) then P(c(x1, ..., xn)).
  //             have((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- constructorPrecondition) by Restate

  //             c.signature
  //               .foldLeft(lastStep)((fact, el) =>
  //                 val (v, ty) = el

  //                 fact.statement.right.head match
  //                   case Forall(_, factCclWithoutForall) =>
  //                     thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- factCclWithoutForall) by InstantiateForall(v)

  //                     factCclWithoutForall match
  //                       case Implies(membership, subformula) =>
  //                         ty match
  //                           case Self =>
  //                             subformula match
  //                               case Implies(hypothesis, subSubFormula) =>
  //                                 val proofSubSubFormula = thenHave(
  //                                   (hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInTerm, constructorVarsInHM, P(v)) |- subSubFormula
  //                                 ) by Weakening
  //                                 have(inductionFormulaM |- inductionFormulaM) by Hypothesis
  //                                 thenHave(inductionFormulaM |- in(v, app(h, m)) ==> P(v)) by InstantiateForall(v)
  //                                 thenHave((inductionFormulaM, constructorVarsInHM) |- P(v)) by Weakening

  //                                 have((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInTerm, constructorVarsInHM) |- subSubFormula) by Cut(
  //                                   lastStep,
  //                                   proofSubSubFormula
  //                                 )
  //                                 have((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- subSubFormula) by Cut(
  //                                   constructorQuantVarsInHNToTerm,
  //                                   lastStep
  //                                 )

  //                               case _ => throw UnreachableException

  //                           case GroundType(t) =>
  //                             thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- subformula) by Restate

  //                           case fn: FunctionType => 
  //                             subformula match
  //                               case Implies(hypothesis, subSubFormula) =>
  //                                 val proofSubSubFormula = thenHave(
  //                                   (hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInTerm, constructorVarsInHM, hypothesis) |- subSubFormula
  //                                 ) by Weakening

  //                                 val appliedFun = appSeq(v)(fn.variables)

  //                                 val appVZInHN = have((in(v, fn.getOrElse(app(h, m))), fn.wellTypedDomains) |- in(appliedFun, app(h, m))) by TypeChecker.prove

  //                                 have(inductionFormulaM |- inductionFormulaM) by Hypothesis
  //                                 thenHave(inductionFormulaM |- in(appliedFun, app(h, m)) ==> P(appliedFun)) by InstantiateForall(appliedFun)
  //                                 thenHave((inductionFormulaM, in(appliedFun, app(h, m))) |- P(appliedFun)) by Restate
  //                                 have((inductionFormulaM, in(v, fn.getOrElse(app(h, m))), fn.wellTypedDomains) |- P(appliedFun)) by Cut(appVZInHN, lastStep)
  //                                 thenHave((inductionFormulaM, in(v, fn.getOrElse(app(h, m)))) |- fn.wellTypedDomains ==>
  //                                 P(appliedFun)) by RightImplies
  //                                 thenHave((inductionFormulaM, in(v, fn.getOrElse(app(h, m)))) |- forallSeq(fn.variables, fn.wellTypedDomains ==> P(appliedFun))) by QuantifiersIntro(fn.variables)
  //                                 thenHave((inductionFormulaM, constructorVarsInHM) |- forallSeq(fn.variables, fn.wellTypedDomains ==> P(appliedFun))) by Weakening

  //                                 have((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInTerm, constructorVarsInHM) |- subSubFormula) by Cut(
  //                                   lastStep,
  //                                   proofSubSubFormula
  //                                 )
  //                                 have((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- subSubFormula) by Cut(
  //                                   constructorQuantVarsInHNToTerm,
  //                                   lastStep
  //                                 )

  //                               case _ => throw UnreachableException

  //                       case _ => throw UnreachableException
  //                   case _ => throw UnreachableException
  //               )

  //             thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM) |- P(c.term)) by Restate

  //             // STEP 2.1.3: Prove that if xi, ..., xj ∈ height(m) then P(x).
  //             thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM, x === c.term) |- P(x)) by RightSubstEq
  //               .withParametersSimple(List((x, c.term)), lambda(x, P(x)))

  //             thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, constructorVarsInHM /\ (x === c.term)) |- P(x)) by LeftAnd

  //             thenHave((hIsTheHeightFunction, constructorPrecondition, in(m, N), inductionFormulaM, isConstructor(c, x, app(h, m))) |- P(x)) by QuantifiersIntro(c.variables)
  //             thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(m, N), inductionFormulaM, isConstructor(c, x, app(h, m))) |- P(x)) by Weakening
  //           ).toSeq


  //         have((hIsTheHeightFunction, structuralInductionPreconditions, in(m, N), inductionFormulaM, isConstructor(x, app(h, m))) |- P(x)) by LeftOr(orSeq: _*)
  //     }

  //     // STEP 2.2: Prove that if x ∈ height(n + 1) then P(x) holds.
  //     have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), inductionFormulaM, in(m, n), isConstructor(x, app(h, m))) |- P(x)) by Cut(
  //       ADTThm.natTransitivity of (a := m, b := n), lastStep
  //     )
  //     have((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), in(m, n) ==> inductionFormulaM, in(m, n) /\ isConstructor(x, app(h, m))) |- P(x)) by Sorry
  //     thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), forall(m, in(m, n) ==> inductionFormulaM), in(m, n) /\ isConstructor(x, app(h, m))) |- P(x)) by LeftForall
  //     thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N), forall(m, in(m, n) ==> inductionFormulaM), exists(m, in(m, n) /\ isConstructor(x, app(h, m)))) |- P(x)) by LeftExists
  //     have((hIsTheHeightFunction, structuralInductionPreconditions, !(n === emptySet), in(n, N), forall(m, in(m, n) ==> inductionFormulaM), in(x, app(h, n))) |- P(x)) by Cut(
  //       heightSuccessorStrong, lastStep
  //     )

  //     // STEP 2.3: Conclude
  //     thenHave((hIsTheHeightFunction, structuralInductionPreconditions, !(n === emptySet), in(n, N), forall(m, in(m, n) ==> inductionFormulaM)) |- in(x, app(h, n)) ==> P(x)) by RightImplies
  //     thenHave((hIsTheHeightFunction, structuralInductionPreconditions, !(n === emptySet), in(n, N), forall(m, in(m, n) ==> inductionFormulaM)) |- inductionFormulaN) by RightForall
  //     have((hIsTheHeightFunction, structuralInductionPreconditions, (n === emptySet) \/ !(n === emptySet), in(n, N), forall(m, in(m, n) ==> inductionFormulaM)) |- inductionFormulaN) by LeftOr(zeroCase, lastStep)
  //     thenHave((hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> (forall(m, in(m, n) ==> inductionFormulaM) ==> inductionFormulaN)) by Restate
  //     thenHave(thesis) by RightForall
  //   }

  //   // STEP 3: Conclude

  //   have((hIsTheHeightFunction, structuralInductionPreconditions) |- forall(n, in(n, N) ==> inductionFormulaN)) by Cut(lastStep, ADTThm.natInduction of (P := lambda(n, inductionFormulaN)))
  //   thenHave((hIsTheHeightFunction, structuralInductionPreconditions) |- in(n, N) ==> inductionFormulaN) by InstantiateForall(n)
  //   thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- inductionFormulaN) by Restate
  //   thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N)) |- in(x, app(h, n)) ==> P(x)) by InstantiateForall(x)
  //   thenHave((hIsTheHeightFunction, structuralInductionPreconditions, in(n, N) /\ in(x, app(h, n))) |- P(x)) by Restate
  //   val exImpliesP = thenHave((hIsTheHeightFunction, structuralInductionPreconditions, exists(n, in(n, N) /\ in(x, app(h, n)))) |- P(x)) by LeftExists
  //   have((hIsTheHeightFunction, in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))) by Cut(termHasHeight, ADTThm.equivalenceApply of (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n)))))

  //   have((hIsTheHeightFunction, structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(lastStep, exImpliesP)
  //   thenHave((exists(h, hIsTheHeightFunction), structuralInductionPreconditions, in(x, term)) |- P(x)) by LeftExists
  //   have((structuralInductionPreconditions, in(x, term)) |- P(x)) by Cut(heightFunctionExistence, lastStep)
  //   thenHave(structuralInductionPreconditions |- in(x, term) ==> P(x)) by RightImplies
  //   thenHave(structuralInductionPreconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
  // })


}

/**
  * Semantic set theoretical interpretation of a constructor for an algebraic data type.
  * That is a function from the arguments' domains to the set of instances of the algebraic data type.
  * 
  *   `c : T1 -> ... -> Tn -> ADT`
  * 
  * Since polymorphism is supported, this function is parametrized by the type variables appearing inside
  * the specification of the ADT. In this sense, a constructor is a class function whose parameters are 
  * type variables and whose body is the set theoretic function detailed above. With polymorphism, the signature
  * thus becomes:
  * 
  *   `c(X1, ..., Xn) : T1(X1, ..., Xn) -> ... -> Tn(X1, ..., Xn) -> ADT(X1, ..., Xn)`
  * 
  * Injectivity and introduction rule are proven within this class.
  *
  * @constructor generates a class function for this constructor
  * @param line the line at which this constructor is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param file the file in which this constructor is defined. Usually fetched automatically by the compiler. 
  * Used for error reporting
  * @param name the name of this constructor
  * @param underlying the syntactic constructor
  * @param adt the algebraic data type to which this constructor belongs
  */
private class SemanticConstructor[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val name: String,
  val underlying: SyntacticConstructor,
  val adt: SyntacticADT[N],
) {
   /**
     * Full name of this constructor, i.e. concatenation of the ADT name and this constructor name.
     */
    val fullName: String = s"${adt.name}/${name}"

    /**
     * Type variables that may appear in the signature of this constructor.
     */
    val typeVariables: Variable ** N = adt.typeVariables

    /**
      * Sequence of type variables that may appear in the signature of this constructor.
      */
    val typeVariablesSeq: Seq[Variable] = adt.typeVariablesSeq

    /**
      * Number of type variables in the signature of this constructor.
      */
    val typeArity: N = adt.typeArity

    /**
     * Variables used for constructor arguments.
     */
    val variables: Seq[Variable] = underlying.variables

    /**
     * Variables used for constructor arguments.
     */
    val variables1: Seq[Variable] = underlying.variables1

    /**
     * Alternative set of variables used for constructor arguments.
     */
    val variables2: Seq[Variable] = underlying.variables2

    /**
     * Set of variables for this constructor with their respective domain or a 
     * special symbol in case the domain is the ADT.
     * 
     * @param vars variables
     */
    def syntacticSignature(vars: Seq[Variable]): Seq[(Variable, ConstructorArgument)] = 
      vars.zip(underlying.specification)

    /**
     * Variables of this constructor with their respective domain or a special symbol in case the domain is the ADT.
     */
    val syntacticSignature: Seq[(Variable, ConstructorArgument)] = underlying.signature

    /**
     * Constructor arguments with their respective domains.
     * 
     * @param vars this constructor arguments
     */
    def semanticSignature(vars: Seq[Variable]): Seq[(Variable, Term)] = vars.zip(underlying.specification.map(_.getOrElse(adt.term)))

    /**
     * Variables of this constructor with their respective domains.
     */
    val semanticSignature: Seq[(Variable, Term)] = semanticSignature(variables)

    /**
     * Variables of this constructor with their respective domains.
     */
    val semanticSignature1: Seq[(Variable, Term)] = semanticSignature

    /**
     * Alternative set of variables of this constructor with their respective domain.
     */
    val semanticSignature2: Seq[(Variable, Term)] = semanticSignature(variables2)

    /**
     * Type of this constructor.
     */
    val typ: Term = semanticSignature.unzip._2.foldRight[Term](adt.term)((a, b) => a |=> b)

    /**
     * Arity of this constructor.
     */
    val arity: Int = variables.size

    /**
     * Internal representation of this constructor (i.e. as a tuple).
     */
    val structuralTerm: Term = underlying.term
    /**
    * Internal representation of this constructor (i.e. as a tuple).
    */
    val structuralTerm1: Term = underlying.term1
    /**
    * Internal representation of this constructor (i.e. as a tuple) with an alternative set of variables.
    */
    val structuralTerm2: Term = underlying.term2

    /**
     * Definition of this constructor.
     *
     * Formally it is the only function whose codomain is the ADT such that for all variables x1 :: S1, ...,xn :: Sn
     * c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))
     */
    private val untypedDefinition = (c :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appSeq(c)(variables) === structuralTerm))

    /**
     * Lemma --- Uniqueness of this constructor.
     *
     *     ` ∃!c. c ∈ T1 -> ... -> Tn -> ADT /\ ∀x1, ..., xn. c * x1 * ...* xn = (tagc, (x1, (..., (xn, ∅)...))`
     */
    private val uniqueness = Axiom(existsOne(c, untypedDefinition))

    /**
     * Class function representing this constructor
     */
    private val classFunction = FunctionDefinition[N](fullName, line.value, file.value)(typeVariablesSeq, c, untypedDefinition, uniqueness).label

    /**
      * Identifier of this constructor.
      */
    val id: Identifier = classFunction.id

    /**
      * This constructor in which type variables are instantiated.
      *
      * @param args the instances of this constructor's type variables
      */
    def term(args: Seq[Term]): Term = classFunction.applySeq(args)

    /**
     * Constructor where type variables are instantiated with schematic variables.
     */
    private val term: Term = term(typeVariablesSeq)

    /**
     * Constructor where type variables are instantiated with schematic variables and arguments instantiated.
     * 
     * @param args the instances of this constructor arguments
     */
    def appliedTerm(args: Seq[Term]): Term = appSeq(term)(args)

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     */
    val appliedTerm: Term = appliedTerm(variables)

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     */
    val appliedTerm1: Term = appliedTerm

    /**
     * Constructor where type variables and arguments are instantiated with schematic variables.
     * Arguments variables are however drawn from an alternative set of variables.
     */
    val appliedTerm2: Term = appliedTerm(variables2)

    /**
     * Lemma --- This constructor is equal to its internal representation.
     *
     *     `∀x1, ..., xn. c * x1 * ... * xn = (tagc, (x1, (..., (xn, ∅)...))`
     */
    val shortDefinition = Lemma(forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm))) {
      have(forall(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)))) by InstantiateForall(term)
      thenHave(thesis) by Weakening
    }

    /**
     * Lemma --- Introduction rule for this constructor.
     * 
     *    `∀A1, ..., Am. c(X1, ..., Xm) ∈ T1(X1, ..., Xm) -> ... -> Tn(X1, ..., Xm) -> ADT(X1, ..., Xm)`
     * 
     * where Ai are the type variables of the ADT and Ti are domains of this constructor arguments.
     * 
     * e.g. `∀T. nil(T) ∈ list(T)` and  `∀T. cons(T) ∈ T -> list(T) -> list(T)`
     */
    val intro = Lemma(forallSeq(typeVariablesSeq, term :: typ)) {
      have(forall(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
      thenHave((term === term) <=> ((term :: typ) /\ forallSeq(variables, wellTypedFormula(semanticSignature) ==> (appliedTerm === structuralTerm)))) by InstantiateForall(term)
      thenHave(term :: typ) by Weakening
      thenHave(thesis) by QuantifiersIntro(typeVariablesSeq)
    }

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of this constructor are equal if and only if all of their arguments are pairwise equal
     *
     * e.g. Cons(head1, tail1) === Cons(head2, tail2) <=> head1 === head2 /\ tail1 === tail2
     */
    lazy val injectivity = 
      val vars1WellTyped: Set[Formula] = wellTypedSet(semanticSignature1)
      val vars2WellTyped: Set[Formula] = wellTypedSet(semanticSignature2)

      if arity == 0 then
        Lemma(appliedTerm1 === appliedTerm2) {
          have(thesis) by RightRefl
        }
      else
        Lemma(vars1WellTyped ++ vars2WellTyped |- simplify((appliedTerm1 === appliedTerm2) <=> (variables1 === variables2))) {

          have(forallSeq(variables1, wellTypedFormula(semanticSignature1) ==> (appliedTerm1 === structuralTerm1))) by Restate.from(shortDefinition)

          variables1.foldLeft(lastStep)((fact, v) =>
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )
          val tappTerm1Def = thenHave(vars1WellTyped |- appliedTerm1 === structuralTerm1) by Restate

          have(forallSeq(variables2, wellTypedFormula(semanticSignature2) ==> (appliedTerm2 === structuralTerm2))) by Restate.from(shortDefinition)

          variables2.foldLeft(lastStep)((fact, v) =>
              fact.statement.right.head match
                case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )
          val tappTerm2Def = thenHave(vars2WellTyped |- appliedTerm2 === structuralTerm2) by Restate


          val s0 = have(vars2WellTyped + (appliedTerm1 === appliedTerm2) |- appliedTerm1 === structuralTerm2) by Cut(tappTerm2Def,
            equalityTransitivity of (x := appliedTerm1, y := appliedTerm2, z := structuralTerm2))
          have(vars1WellTyped + (appliedTerm1 === structuralTerm2) |- structuralTerm1 === structuralTerm2) by Cut(tappTerm1Def,
            equalityTransitivity of (x := structuralTerm1, y := appliedTerm1, z := structuralTerm2))
          have((vars1WellTyped ++ vars2WellTyped) + (appliedTerm1 === appliedTerm2) |- structuralTerm1 === structuralTerm2) by Cut(s0, lastStep)
          val forward = thenHave(vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) ==> (structuralTerm1 === structuralTerm2)) by RightImplies

          val s1 = have(vars1WellTyped + (structuralTerm1 === structuralTerm2) |- appliedTerm1 === structuralTerm2) by Cut(tappTerm1Def,
            equalityTransitivity of (x := appliedTerm1, y := structuralTerm1, z := structuralTerm2))
          have(vars2WellTyped + (appliedTerm1 === structuralTerm2) |- appliedTerm1 === appliedTerm2) by Cut(tappTerm2Def,
            equalityTransitivity of (x := appliedTerm1, y := structuralTerm2, z := appliedTerm2))
          have((vars1WellTyped ++ vars2WellTyped) + (structuralTerm1 === structuralTerm2) |- appliedTerm1 === appliedTerm2) by Cut(s1, lastStep)
          val backward = thenHave(vars1WellTyped ++ vars2WellTyped |- (structuralTerm1 === structuralTerm2) ==> (appliedTerm1 === appliedTerm2)) by RightImplies

          val definitionUnfolding = have(vars1WellTyped ++ vars2WellTyped |- (appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2)) by RightIff(forward, backward)
          have((appliedTerm1 === appliedTerm2) <=> (structuralTerm1 === structuralTerm2) |- (appliedTerm1 === appliedTerm2) <=> /\(variables1.zip(variables2).map(_ === _))) by Cut(
            underlying.injectivity,
            ADTThm.equivalenceRewriting of (p1 := (appliedTerm1 === appliedTerm2), p2 := (structuralTerm1 === structuralTerm2), p3 := /\(variables1.zip(variables2).map(_ === _)))
          )
          have(thesis) by Cut(definitionUnfolding, lastStep)
        }

    
    /**
     * Case generated by this constructor when performing a proof by induction
     */
    lazy val inductiveCase: Formula =
      syntacticSignature.foldRight[Formula](P(appliedTerm1))
        ((el, fc) =>
          val (v, typ) = el
          typ match
            case Self => forall(v, v :: adt.term ==> (P(v) ==> fc))
            case GroundType(t) => forall(v, v :: t ==> fc)
            case f: FunctionType => forall(v, v :: f.getOrElse(adt.term) ==> (forallSeq(f.variables, f.wellTypedDomains ==> P(appSeq(v)(f.variables))) ==> fc))
        )  
}

/**
  * Semantic set theoretical interpretation of an algebraic data type. That is the least set closed under [[SemanticConstructor]].
  * 
  * E.g. list is the smallest set containing nil and closed under the cons function.
  *  
  * Injectivity between different constructors, structural induction and elimination rule are proved within this class.
  *
  * @constructor generates a semantic interpretation for this ADT out of a syntactic one
  * @param underlying the syntactic representation of this ADT
  * @param constructors constructors of this ADT
  */
  private class SemanticADT[N <: Arity](
    val underlying: SyntacticADT[N], 
    val constructors: Seq[SemanticConstructor[N]]
    ) {

    /**
     * Name of this ADT.
     */
    val name: String = underlying.name

    /**
      * Identifier of this ADT.
      */
    val id: Identifier = underlying.polymorphicTerm.id

    /**
     * Type variables of this ADT.
     */
    val typeVariables: Variable ** N = underlying.typeVariables

    /**
      * Sequence of type variables of this ADT.
      */
    val typeVariablesSeq: Seq[Variable] = underlying.typeVariablesSeq

    /**
      * Number of type variables in this ADT.
      */
    val typeArity: N = underlying.typeArity

    /**
     * Term representing this ADT where type variables are instantiated with given arguments.
     * 
     * @param args the instances of this ADT type variables
     */
    def term(args: Seq[Term]) = underlying.polymorphicTerm.applySeq(args)

    /**
     * Term representing this ADT where type variables are instantiated with schematic variables.
     */
    val term: Term = underlying.term

    /**
     * Theorem --- Injectivity of constructors.
     *
     *    Two instances of different construcors are always different.
     *
     * e.g. Nil != Cons(head, tail)
     */
    def injectivity(c1: SemanticConstructor[N], c2: SemanticConstructor[N]) =

      val vars1WellTyped: Set[Formula] = wellTypedSet(c1.semanticSignature1)
      val vars2WellTyped: Set[Formula] = wellTypedSet(c2.semanticSignature2)

      Lemma(vars1WellTyped ++ vars2WellTyped |- !(c1.appliedTerm1 === c2.appliedTerm2)) {

        val defUnfolding = have((vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- c1.structuralTerm1 === c2.structuralTerm2) subproof {
          have(forallSeq(c1.variables1, wellTypedFormula(c1.semanticSignature1) ==> (c1.appliedTerm1 === c1.structuralTerm1))) by Restate.from(c1.shortDefinition)

          c1.variables1.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi.substitute(v := x)) by InstantiateForall(x)
              case _ => throw UnreachableException
          )
          val tappTerm1Def = thenHave(vars1WellTyped |- c1.structuralTerm1 === c1.appliedTerm1) by Restate

          have(forallSeq(c2.variables2, wellTypedFormula(c2.semanticSignature2) ==> (c2.appliedTerm2 === c2.structuralTerm2))) by Restate.from(c2.shortDefinition)

          c2.variables2.foldLeft(lastStep)((fact, v) =>
            fact.statement.right.head match
              case Forall(_, phi) => thenHave(phi) by InstantiateForall(v)
              case _ => throw UnreachableException
          )
          val tappTerm2Def = thenHave(vars2WellTyped |- c2.appliedTerm2 === c2.structuralTerm2) by Restate

          val s0 = have(vars2WellTyped + (c1.appliedTerm1 === c2.appliedTerm2) |- c1.appliedTerm1 === c2.structuralTerm2) by Cut(
            tappTerm2Def,
            equalityTransitivity of (x := c1.appliedTerm1, y := c2.appliedTerm2, z := c2.structuralTerm2)
          )
          have(vars1WellTyped + (c1.appliedTerm1 === c2.structuralTerm2) |- c1.structuralTerm1 === c2.structuralTerm2) by Cut(
            tappTerm1Def,
            equalityTransitivity of (x := c1.structuralTerm1, y := c1.appliedTerm1, z := c2.structuralTerm2)
          )
          have(thesis) by Cut(s0, lastStep)
        }

        have(!(c1.structuralTerm1 === c2.structuralTerm2)) by Restate.from(underlying.injectivity(c1.underlying, c2.underlying))
        thenHave(c1.structuralTerm1 === c2.structuralTerm2 |- ()) by Restate

        have((vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- ()) by Cut(defUnfolding, lastStep)
      }

    /**
     * Theorem --- Structural induction principle for this ADT.
     *
     *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
     */
    lazy val induction = Lemma(constructors.foldRight[Formula](forall(x, x :: term ==> P(x)))((c, f) => c.inductiveCase ==> f)) { sp ?=>
      constructors.foldRight[(Formula, Formula, sp.Fact)] {
        val prop = forall(x, x :: term ==> P(x))
        (prop, prop, have(prop <=> prop) by Restate)
      }((c, acc) =>
        val (oldBefore, oldAfter, fact) = acc
        val newBefore = underlying.inductiveCase(c.underlying) ==> oldBefore
        val newAfter = c.inductiveCase ==> oldAfter

        have(underlying.inductiveCase(c.underlying) <=> c.inductiveCase) subproof {
          val wellTypedVars: Seq[Formula] = wellTyped(c.semanticSignature)
          val wellTypedVarsSet = wellTypedVars.toSet


          have(forallSeq(c.variables, wellTypedFormula(c.semanticSignature) ==> (c.appliedTerm === c.structuralTerm))) by Restate.from(c.shortDefinition)
          if c.arity > 0 then
            c.variables1.foldLeft(lastStep)((l, _) =>
              lastStep.statement.right.head match
                case Forall(v, phi) => thenHave(phi) by InstantiateForall(v)
                case _ => throw UnreachableException
            )

          val eq = thenHave(wellTypedVarsSet |- c.appliedTerm === c.structuralTerm) by Restate
          have(P(c.appliedTerm) <=> P(c.appliedTerm)) by Restate
          thenHave(c.structuralTerm === c.appliedTerm |- P(c.structuralTerm) <=> P(c.appliedTerm)) by RightSubstEq.withParametersSimple(
            List((c.structuralTerm, c.appliedTerm)),
            lambda(s, P(c.structuralTerm) <=> P(s))
          )
          have(wellTypedVarsSet |- P(c.structuralTerm) <=> P(c.appliedTerm)) by Cut(eq, lastStep)

          c.syntacticSignature
            .foldRight[(Formula, Formula, Seq[Formula])]((P(c.structuralTerm), P(c.appliedTerm), wellTypedVars))((el, fc) =>
              val (v, ty) = el
              val (fc1, fc2, wellTypedVars) = fc
              ty match
                case Self =>
                  val wellTypedV: Formula = v :: term
                  have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(lastStep, ADTThm.leftImpliesEquivalenceWeak of (p := P(v), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- wellTypedV ==> ((P(v) ==> fc1) <=> (P(v) ==> fc2))) by RightImplies
                  have(wellTypedVars.init |- (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2))) by Cut(
                    lastStep,
                    ADTThm.leftImpliesEquivalenceStrong of (p := wellTypedV, p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
                  )
                  thenHave(wellTypedVars.init |- forall(v, (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- forall(v, (wellTypedV ==> (P(v) ==> fc1))) <=> forall(v, (wellTypedV ==> (P(v) ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, wellTypedV ==> (P(v) ==> fc1)), Q := lambda(v, wellTypedV ==> (P(v) ==> fc2)))
                  )
                  (forall(v, wellTypedV ==> (P(v) ==> fc1)), forall(v, wellTypedV ==> (P(v) ==> fc2)), wellTypedVars.init)
                case GroundType(t) =>
                  thenHave(wellTypedVars.init |- v :: t ==> (fc1 <=> fc2)) by RightImplies
                  have(wellTypedVars.init |- (in(v, t) ==> fc1) <=> (v :: t ==> fc2)) by Cut(lastStep, ADTThm.leftImpliesEquivalenceStrong of (p := in(v, t), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1) <=> (v :: t ==> fc2))) by RightForall
                  have(wellTypedVars.init |- forall(v, (in(v, t) ==> fc1)) <=> forall(v, (v :: t ==> fc2))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, in(v, t) ==> fc1), Q := lambda(v, v :: t ==> fc2))
                  )
                  (forall(v, (in(v, t) ==> fc1)), forall(v, (v :: t ==> fc2)), wellTypedVars.init)
                case f: FunctionType =>
                  val indHypothesis: Formula = forallSeq(f.variables, f.wellTypedDomains ==> P(appSeq(v)(f.variables)))
                  val wellTypedV: Formula = v :: f.getOrElse(term)
                  have(wellTypedVars |- (indHypothesis ==> fc1) <=> (indHypothesis ==> fc2)) by Cut(lastStep, ADTThm.leftImpliesEquivalenceWeak of (p := indHypothesis, p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- wellTypedV ==> ((indHypothesis ==> fc1) <=> (indHypothesis ==> fc2))) by RightImplies
                  have(wellTypedVars.init |- (wellTypedV ==> (indHypothesis ==> fc1)) <=> (wellTypedV ==> (indHypothesis ==> fc2))) by Cut(
                    lastStep,
                    ADTThm.leftImpliesEquivalenceStrong of (p := wellTypedV, p1 := indHypothesis ==> fc1, p2 := indHypothesis ==> fc2)
                  )
                  thenHave(wellTypedVars.init |- forall(v, (wellTypedV ==> (indHypothesis ==> fc1)) <=> (wellTypedV ==> (indHypothesis ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- forall(v, (wellTypedV ==> (indHypothesis ==> fc1))) <=> forall(v, (wellTypedV ==> (indHypothesis ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, wellTypedV ==> (indHypothesis ==> fc1)), Q := lambda(v, wellTypedV ==> (indHypothesis ==> fc2)))
                  )
                  (forall(v, wellTypedV ==> (indHypothesis ==> fc1)), forall(v, wellTypedV ==> (indHypothesis ==> fc2)), wellTypedVars.init)
            )
        }
        (newBefore, newAfter, have(newBefore <=> newAfter) by Apply(ADTThm.impliesEquivalence).on(lastStep, fact))
      )
      have(underlying.induction.statement.right.head |- thesis.right.head) by Cut(
        lastStep,
        ADTThm.equivalenceApply of (
          p1 := underlying.induction.statement.right.head, p2 := thesis.right.head
        )
      )
      have(thesis) by Cut(underlying.induction, lastStep)
    }

    /**
      * Returns a map binding each constructor to formula describing whether x is an instance of it.
      */
    private lazy val isConstructorMap: Map[SemanticConstructor[N], Formula] =
      constructors.map(c => c -> existsSeq(c.variables, wellTypedFormula(c.semanticSignature) /\ (x === c.appliedTerm))).toMap

    /**
      * Returns a formula describing whether x is an instance of one of this ADT's constructors.
      */
    private lazy val isConstructor =
      \/(constructors.map(c => isConstructorMap(c)))

    /**
     * Theorem --- Pattern matching principle (also known as elimination rule) for this ADT.
     *
     *    `x ∈ ADT |- x = c * x1 * ... * xn for some constructor c and xi, ..., xj ∈ ADT`
     */
    lazy val elim = Lemma(x :: term |- simplify(isConstructor)) {

      // Induction preconditions with P(z) = z != x
      val inductionPreconditionIneq = constructors.map(c => c -> c.inductiveCase.substitute((P -> lambda(z, !(x === z))))).toMap
      val inductionPreconditionsIneq = /\(inductionPreconditionIneq.map(_._2))

      // Weakening of the negation of the induction preconditions
      val weakNegInductionPreconditionIneq: Map[SemanticConstructor[N], Formula] = constructors
        .map(c =>
          c ->
            c.semanticSignature
              .foldRight[Formula](x === c.appliedTerm)((el, fc) =>
                val (v, t) = el
                exists(v, (v :: t) /\ fc)
              )
        )
        .toMap

      // STEP 1: Prove that if the induction preconditions with P(z) = z != x do not hold then x is the instance of some constructor
      val strengtheningOfInductionPreconditions = have(!inductionPreconditionsIneq |- isConstructor) subproof {
        if constructors.isEmpty then have(thesis) by Restate
        else

          // STEP 1.1: Prove the claim for each constructor
          val negInductionPreconditionsOrSequence =
            for c <- constructors yield

              // STEP 1.1.1: Prove the strengthening of the negations of the induction preconditions
              val conditionStrenghtening = have(!inductionPreconditionIneq(c) |- weakNegInductionPreconditionIneq(c)) subproof {
                have(x === c.appliedTerm |- x === c.appliedTerm) by Hypothesis

                c.syntacticSignature
                  .foldRight(lastStep)((el, fact) =>
                    val (v, ty) = el
                    val left = fact.statement.left.head
                    val right = fact.statement.right.head

                    ty match
                      case Self =>
                        thenHave(!(x === v) /\ left |- right) by Weakening
                      case _ => ()

                    val weakr = thenHave(in(v, ty.getOrElse(term)) /\ left |- right) by Weakening
                    val weakl = have(in(v, ty.getOrElse(term)) /\ left |- in(v, ty.getOrElse(term))) by Restate

                    have((v :: ty.getOrElse(term)) /\ left |- (v :: ty.getOrElse(term)) /\ right) by RightAnd(weakl, weakr)
                    thenHave((v :: ty.getOrElse(term)) /\ left |- exists(v, (v :: ty.getOrElse(term)) /\ right)) by RightExists
                    thenHave(exists(v, (v :: ty.getOrElse(term)) /\ left) |- exists(v, (v :: ty.getOrElse(term)) /\ right)) by LeftExists
                  )

              }

              // STEP 1.1.2: Conclude
              // TODO: Change to a more efficient way of proving this
              have(weakNegInductionPreconditionIneq(c) |- isConstructorMap(c)) by Tableau
              have(!inductionPreconditionIneq(c) |- isConstructorMap(c)) by Cut(conditionStrenghtening, lastStep)
              thenHave(!inductionPreconditionIneq(c) |- isConstructor) by Weakening

          have(thesis) by LeftOr(negInductionPreconditionsOrSequence: _*)
      }

      // STEP 2: Conclude
      have(inductionPreconditionsIneq |- forall(z, z :: term ==> !(x === z))) by Restate.from(induction of (P := lambda(z, !(x === z))))
      val ind = thenHave(x :: term |- !inductionPreconditionsIneq) by InstantiateForall(x)
      have(x :: term |- isConstructor) by Cut(lastStep, strengtheningOfInductionPreconditions)
    }
  }






