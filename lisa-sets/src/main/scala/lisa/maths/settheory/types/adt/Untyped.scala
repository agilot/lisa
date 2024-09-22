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

import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.Functions.*
import lisa.maths.settheory.Relations.*
import Helpers.*
import ADTDefinitions.*
import ADTHelperTheorems.*
import lisa.maths.settheory.types.TypeLib.{ |=>}
import lisa.maths.settheory.types.TypeSystem.{ :: , TypeChecker}
import lisa.maths.Quantifiers.{universalEquivalenceDistribution, equalityTransitivity}
import lisa.fol.FOL.Variable
import lisa.maths.settheory.types.TypeLib.funcspaceAxiom
import lisa.maths.settheory.orderings.Ordinals.*

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
  ) extends lisa.Main{

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
  def subterm(args: Seq[Term]): Term = args.foldRight[Term](∅)(pair(_, _))

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
      Lemma((term1 === term2) <=> (variables1 ===+ variables2)) {

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
              ((pulledVars1 ===+ pulledVars2) /\ (pair(v1, subsubterm1) === pair(v2, subsubterm2))) <=>
                ((pulledVars1 ===+ pulledVars2) /\ (v1 === v2) /\ (subsubterm1 === subsubterm2))
            ) by Cut(
              pairExtensionality of (a := v1, b := subsubterm1, c := v2, d := subsubterm2),
              rightAndEquivalence of (p := pulledVars1 ===+ pulledVars2, p1 := pair(v1, subsubterm1) === pair(v2, subsubterm2), p2 := (v1 === v2) /\ (subsubterm1 === subsubterm2))
            )
            val newFact = thenHave(
              (term1 === term2) <=>
                ((updatedPulledVars1 ===+ updatedPulledVars2) /\ (subsubterm1 === subsubterm2))
            ) by Substitution.ApplyRules(previousFact)

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
  ) extends lisa.Main {

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

    Lemma(c1.term1 =/= c2.term2) { 

      // STEP 0: Caching
      val tagTerm1: Term = c1.tagTerm
      val tagTerm2: Term = c2.tagTerm

      // STEP 1: Prove that the tags are different
      val diffTag = have(tagTerm1 =/= tagTerm2) subproof { sp ?=>

        // STEP 1.1: Order the tags
        val minTag: Int = Math.min(c1.tag, c2.tag)
        val maxTag: Int = Math.max(c1.tag, c2.tag)

        val start = have(tagTerm1 === tagTerm2 |- toTerm(maxTag) === toTerm(minTag)) by Restate

        val ordinals = (1 to minTag).scanLeft[sp.Fact](emptySetOrdinal)((fact, i) =>
          val term = toTerm(i - 1)
          have(ordinal(successor(term))) by Cut(fact, successorIsOrdinal of (a := term))
        )

        // STEP 1.2: Apply successor injectivity to both tags until one becomes 0
        (1 to minTag).foldLeft(start)((fact, i) =>
          val midMaxTag = toTerm(maxTag - i)
          val midMinTag = toTerm(minTag - i)
          have((ordinal(midMinTag), tagTerm1 === tagTerm2) |- midMaxTag === midMinTag) by Cut(fact, successorInjectivity of (a := midMaxTag, b := midMinTag))
          have(tagTerm1 === tagTerm2 |- midMaxTag === midMinTag) by Cut(ordinals(minTag - i), lastStep)
        )

        val chainInjectivity = thenHave(toTerm(maxTag - minTag) =/= ∅ |- tagTerm1 =/= tagTerm2) by Restate

        // STEP 1.3: Conclude using the fact that 0 is not the successor of any number
        have(toTerm(maxTag - minTag) =/= ∅) by Exact(successorNotEmpty)
        have(thesis) by Cut(lastStep, chainInjectivity)
      }

      // STEP 2: Prove that the terms are different if the tags are different
      have(c1.term1 === c2.term2 |- (tagTerm1 === tagTerm2) /\ (c1.subterm1 === c2.subterm2)) by Apply(equivalenceRevApply).on(
        pairExtensionality of (a := tagTerm1, b := c1.subterm1, c := tagTerm2, d := c2.subterm2)
      )
      thenHave(tagTerm1 =/= tagTerm2 |- c1.term1 =/= c2.term2) by Weakening

      // STEP 3: Conclude
      have(c1.term1 =/= c2.term2) by Cut(diffTag, lastStep)
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
  private def isConstructor(x: Term, s: Term): Formula = \/+(constructors.map(c => isConstructor(c, x, s)))

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
  private def isInIntroductionFunctionImage(s: Term)(y: Term): Formula = isConstructor(y, s) \/ (y ∈ s)

  private def isFunctionImage(s : Term)(z : Term) = ∀(y, y ∈ z <=> isInIntroductionFunctionImage(s)(y))


  private val functionImageExistence = Axiom(∃(z, isFunctionImage(s)(z)))

  private val functionImageClassFunction = Lemma(
    classFunctionTwoArgs(lambda((x, s, z), isFunctionImage(s)(z)))
  ) {
    have(isFunctionImage(s)(z) |- isFunctionImage(s)(z)) by Hypothesis
    thenHave(isFunctionImage(s)(z) |- y ∈ z <=> isInIntroductionFunctionImage(s)(y)) by InstantiateForall(y)
    have((isFunctionImage(s)(z), isFunctionImage(s)(w)) |- y ∈ z <=> y ∈ w) by Substitution.ApplyRules(lastStep of (z := w))(lastStep)
    thenHave((isFunctionImage(s)(z), isFunctionImage(s)(w)) |- ∀(y, y ∈ z <=> y ∈ w)) by RightForall
    have((isFunctionImage(s)(z), isFunctionImage(s)(w)) |- z === w) by Cut(lastStep, equalityIntro of (x := z, y := w))
    thenHave((isFunctionImage(s)(z) /\ isFunctionImage(s)(w)) ==> (z === w)) by Restate
    thenHave(∀(w, (isFunctionImage(s)(z) /\ isFunctionImage(s)(w)) ==> (z === w))) by RightForall
    thenHave(∀(z, ∀(w, (isFunctionImage(s)(z) /\ isFunctionImage(s)(w)) ==> (z === w)))) by RightForall
    have(∃(z, isFunctionImage(s)(z)) |- ∃!(z, isFunctionImage(s)(z))) by Cut(lastStep, existenceAndUniqueness of (P := lambda(z, isFunctionImage(s)(z))))
    have(∃!(z, isFunctionImage(s)(z))) by Cut(functionImageExistence, lastStep)
    thenHave(∀(s, ∃!(z, isFunctionImage(s)(z)))) by RightForall
    thenHave(thesis) by RightForall
  }

  private val introductionFunctionCumulative = Lemma(
    classFunctionCumulative(lambda((x, s, z), isFunctionImage(s)(z)))
  ) {
    have(isFunctionImage(s)(z) |- isFunctionImage(s)(z)) by Hypothesis
    thenHave(isFunctionImage(s)(z) |- y ∈ z <=> isInIntroductionFunctionImage(s)(y)) by InstantiateForall(y)
    thenHave(isFunctionImage(s)(z) |- y ∈ s ==> y ∈ z) by Weakening
    thenHave(isFunctionImage(s)(z) |- ∀(y, y ∈ s ==> y ∈ z)) by RightForall
    have(isFunctionImage(s)(z) |- s ⊆ z) by Cut(lastStep, subsetIntro of (x := s, y := z))
    thenHave(isFunctionImage(s)(z) ==> s ⊆ z) by RightImplies
    thenHave(∀(z, isFunctionImage(s)(z) ==> s ⊆ z)) by RightForall
    thenHave(∀(s, ∀(z, isFunctionImage(s)(z) ==> s ⊆ z))) by RightForall
    thenHave(∀(x, ∀(s, ∀(z, isFunctionImage(s)(z) ==> s ⊆ z)))) by RightForall
    // thenHave(classFunctionCumulative(lambda((x, s, z), isFunctionImage(s)(z)))) by RightForall
  }

  /**
   * Lemma --- Every constructor is in the image of the introduction function.
   *
   *      `For every c ∈ constructors, xi ∈ s, ..., xj ∈ s |- c(x1, ..., xn) ∈ introductionFunction(s)`
   */
  private val constructorIsInIntroductionFunction = constructors
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
    .toMap

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
  private def isTheHeightFunction(h: Term): Formula = fixpointClassFunction(h, N)(lambda((x, s, z), isFunctionImage(s)(z)))


  // Caching
  private val fIsTheHeightFunction: Formula = isTheHeightFunction(f)
  private val hIsTheHeightFunction: Formula = isTheHeightFunction(h)


  /**
   * Lemma --- The height function exists.
   *
   *     `∃h. h = height`
   */
  private val heightFunctionExistence = Lemma(∃(h, hIsTheHeightFunction)) {
    have(limitOrdinal(N) |- ∃(h, hIsTheHeightFunction)) by Cut(functionImageClassFunction, fixpointClassFunctionExistence of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N))
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  /**
   * Lemma --- If two functions are the height function then they are the same.
   *
   *     `f = height /\ h = height => f = h`
   */
  private val heightFunctionUniqueness2 = Lemma((fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) {
    have((limitOrdinal(N), fIsTheHeightFunction, hIsTheHeightFunction) |- f === h) by Cut(functionImageClassFunction, fixpointClassFunctionUniqueness of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N, g := h))
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  private val heightFunctionDomain = Lemma(hIsTheHeightFunction |- dom(h) === N) {
    have(thesis) by Weakening(functionalOverDomain of (f := h, x := N))
  }

  /**
   * Lemma --- The height function is monotonic
   *
   *     `n <= m => height(n) ⊆ height(m)`
   */
  private val heightMonotonic = Lemma(
    (hIsTheHeightFunction, n < N, m < N, m ⊆ n) |- app(h, m) ⊆ app(h, n)
  ) {
    have((limitOrdinal(N), hIsTheHeightFunction) |- monotonic(h)) by 
      Cut(introductionFunctionCumulative, fixpointFunctionMonotonicity of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N, f := h))
    have(hIsTheHeightFunction |- monotonic(h)) by 
      Cut(heightDomainLimit, lastStep)
    have((hIsTheHeightFunction, n < dom(h), m < dom(h), m ⊆ n) |- app(h, m) ⊆ app(h, n)) by Cut(lastStep, monotonicElim of (f := h))
    thenHave(thesis) by Substitution.ApplyRules(heightFunctionDomain)
  }

  private val heightSubsetSuccessor = Lemma(
    (hIsTheHeightFunction, n < N) |- app(h, n) ⊆ app(h, successor(n))
  ) {
    have((hIsTheHeightFunction, n < N, limitOrdinal(N)) |- app(h, n) ⊆ app(h, successor(n))) by Cut(introductionFunctionCumulative, cumulativeFixpointClassFunctionSubsetSuccessor of (f := h, m := n, n := N, S := lambda((x, s, z), isFunctionImage(s)(z))))
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  /**
   * Lemma --- The set of elements of height n + 1 is the set of elements of height n to which the introduction function is applied.
   *
   *     `height(n + 1) = introductionFunction(height(n))`
   */
  private val heightSuccessor = Lemma((hIsTheHeightFunction, n < N) |- x ∈ app(h, successor(n)) <=> isInIntroductionFunctionImage(app(h, n))(x)) {
    have((hIsTheHeightFunction, n < N) |- isFunctionImage(app(h, n))(app(h, successor(n)))) by Cut (heightDomainLimit, fixpointClassFunctionSuccessorUnfold of (f := h, n := N, S := lambda((x, s, z), isFunctionImage(s)(z)), m := n))
    thenHave(thesis) by InstantiateForall(x)
  }

  private val heightZero = Lemma(hIsTheHeightFunction |- app(h, ∅) === ∅) {
    have(thesis) by Cut(heightDomainLimit, fixpointClassFunctionZeroUnfold of (f := h, n := N, S := lambda((x, s, z), isFunctionImage(s)(z))))
  }

  private val heightLimit = Lemma((hIsTheHeightFunction, n < N, limitOrdinal(n)) |- app(h, n) === uran(h ↾ n)) {
    have(thesis) by Cut(heightDomainLimit, fixpointClassFunctionLimitUnfold of (f := h, n := N, S := lambda((x, s, z), isFunctionImage(s)(z)), m := n))
  }

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
  private def termDescription(adt: Term): Formula = fixpointDescription(N)(lambda((x, s, z), isFunctionImage(s)(z)))(adt)

  /**
   * Lemma --- There exists a unique set satisfying the definition of this ADT
   *
   *     `∃!z. z = ADT
   */
  private val termExistence = Lemma(∃!(z, termDescription(z))) {
    have(limitOrdinal(N) |- ∃!(z, termDescription(z))) by Cut(functionImageClassFunction, fixpointUniqueness of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N))
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  /**
   * Class function defining the ADT. Takes as parameters the type variables of the ADT and return the set of all its instances.
   */
  val polymorphicTerm = FunctionDefinition[N](name, line.value, file.value)(typeVariablesSeq, z, termDescription(z), termExistence).label

  /**
   * The set of all instances of the ADT where the type variables are not instantiated (i.e. are kept variable).
   */
  val term = polymorphicTerm.applySeq(typeVariablesSeq)

  private val termDef = Lemma(
    termDescription(term)
  ) {
    have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
  }

  // *************************
  // * TYPING / INTRODUCTION *
  // *************************

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` x ∈ ADT <=> ∃n ∈ N. x ∈ height(n)`
   *
   */
  private val termHasHeight = Lemma(
    hIsTheHeightFunction |- x ∈ term <=> ∃(n, (n < N) /\ x ∈ app(h, n))
  ) {
    have((limitOrdinal(N), classFunctionTwoArgs(lambda((x, s, z), isFunctionImage(s)(z))), hIsTheHeightFunction) |- x ∈ term <=> ∃(n, n ∈ N /\ x ∈ app(h, n))) by Cut(termDef, fixpointDescriptionMembership of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N, f := h, z := term))
    have((limitOrdinal(N), hIsTheHeightFunction) |- x ∈ term <=> ∃(n, n ∈ N /\ x ∈ app(h, n))) by Cut(functionImageClassFunction, lastStep)
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  private val termHasHeightIntro = Lemma(
    (hIsTheHeightFunction, n < N, x ∈ app(h, n)) |- x ∈ term
  ) {
    have((limitOrdinal(N), classFunctionTwoArgs(lambda((x, s, z), isFunctionImage(s)(z))), hIsTheHeightFunction, n ∈ N, x ∈ app(h, n)) |- x ∈ term) by Cut(termDef, fixpointDescriptionIntro of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N, f := h, z := term, m := n))
    have((limitOrdinal(N), hIsTheHeightFunction, n ∈ N, x ∈ app(h, n)) |- x ∈ term) by Cut(functionImageClassFunction, lastStep)
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  private val heightSubsetTerm = Lemma(
    (hIsTheHeightFunction, n < N) |- app(h, n) ⊆ term
  ) {
    have((limitOrdinal(N), classFunctionTwoArgs(lambda((x, s, z), isFunctionImage(s)(z))), hIsTheHeightFunction, n ∈ N) |- app(h, n) ⊆ term) by Cut(termDef, fixpointFunctionSubsetFixpoint of (S := lambda((x, s, z), isFunctionImage(s)(z)), n := N, f := h, z := term, m := n))
    have((limitOrdinal(N), hIsTheHeightFunction, n ∈ N) |- app(h, n) ⊆ term) by Cut(functionImageClassFunction, lastStep)
    have(thesis) by Cut(heightDomainLimit, lastStep)
  }

  private def getOrElseMonotonic(ty : ConstructorArgument): THM = Lemma(
    (hIsTheHeightFunction, n < N, m < N, m ⊆ n) |- ty.getOrElse(app(h, m)) ⊆ ty.getOrElse(app(h, n))
  ) {
    ty match 
      case GroundType(t) => have(thesis) by Weakening(subsetReflexivity of (x := t))
      case Self => have(thesis) by Restate.from(heightMonotonic)
      case FunctionType(from, to) => 
        have(thesis) by Cut(getOrElseMonotonic(to), setOfFunctionsRightMonotonic of (x := from, y := to.getOrElse(app(h, m)), z := to.getOrElse(app(h, n))))
  }

  private def getOrElseHeightSubsetTerm(ty : ConstructorArgument): THM = Lemma(
    (hIsTheHeightFunction, n < N) |- ty.getOrElse(app(h, n)) ⊆ ty.getOrElse(term)
  ) {
    ty match 
      case GroundType(t) => have(thesis) by Weakening(subsetReflexivity of (x := t))
      case Self => have(thesis) by Restate.from(heightSubsetTerm)
      case FunctionType(from, to) => 
        have(thesis) by Cut(getOrElseHeightSubsetTerm(to), setOfFunctionsRightMonotonic of (x := from, y := to.getOrElse(app(h, n)), z := to.getOrElse(term)))
  }

  private def getOrElseHasHeightFunctionType(from : Term, to : ConstructorArgument) = Axiom(
    hIsTheHeightFunction ==> (x ∈ (from |=> to.getOrElse(term)) <=> ∃(n, (n < N) /\ x ∈ (from |=> to.getOrElse(app(h, n)))))
  )

  private def getOrElseHasHeight(ty : ConstructorArgument) = Lemma(
    hIsTheHeightFunction |- x ∈ ty.getOrElse(term) <=> ∃(n, (n < N) /\ x ∈ ty.getOrElse(app(h, n)))
  ) {
    ty match 
      case GroundType(t) => 
        have(∃(n, n < N) |- x ∈ t <=> ∃(n, (n < N) /\ x ∈ t)) by Tableau
        have(x ∈ t <=> ∃(n, (n < N) /\ x ∈ t)) by Cut(heightDomainHasElement, lastStep)
        thenHave(thesis) by Weakening
      case Self => have(thesis) by Restate.from(termHasHeight)
      case FunctionType(from, to) => have(thesis) by Restate.from(getOrElseHasHeightFunctionType(from, to))
  }

  /**
   * Lemma --- Every element of this ADT has a height. Conversely, if an element has a height, it is in this ADT.
   *
   *     ` xi, ..., xj ∈ ADT <=> ∃n ∈ N. xi, ..., xj ∈ height(n)`
   *
   */
  private val getOrElseHaveHeight = constructors
    .map(co =>
      co -> Lemma(hIsTheHeightFunction |- (constructorVarsInDomain(co, term) <=> ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n))))) {
        if co.variables.isEmpty then 
          have(thesis) by Weakening(heightDomainHasElement)
        else

          val forward = have(hIsTheHeightFunction |- constructorVarsInDomain(co, term) ==> ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) subproof {

            val si = co.specification.size

            have(∅ < N) by Restate.from(zeroInHeightDomain)

            val (unionNi, niInN) = 
              Range(0, si).foldLeft[(Term, Set[Formula])]((∅, Set()))((acc, i) =>
                val (un, assumptions) = acc
                val ni = Variable(s"n${i}")
                val newUn = un ∪ ni

                have(assumptions + (ni < N) + (ordinal(N)) |- newUn < N) by Cut(lastStep, unionOrdinalMembership of (a := un, b := ni, c := N))

                (newUn, assumptions + (ni < N) + (ordinal(N)))
              )

            val unionNiInN = have(niInN |- unionNi < N) by Cut(heightDomainOrdinal, lastStep)

            val operands = for (typeInd, zi) <- co.specification.zipWithIndex.zip(co.variables) yield

              val (ty, i) = typeInd
              val ni = Variable(s"n${i}")

              // ni ⊆ unionNi
              Range(0, si).foldLeft[Term](∅)((acc, j) =>
                val nj = Variable(s"n${j}")
                val newAcc = acc ∪ nj

                if i == j then
                  have(ni ⊆ newAcc) by Restate.from(setUnionRightSubset of (a := acc, b := nj))
                else if j > i then
                  have(acc ⊆ newAcc |- ni ⊆ newAcc) by Cut(lastStep, subsetTransitivity of (x := ni, y := acc, z := newAcc))
                  have(ni ⊆ newAcc) by Cut(setUnionLeftSubset of (a := acc, b := nj), lastStep)

                newAcc
              )
              
              have((hIsTheHeightFunction, unionNi < N, ni < N) |- ty.getOrElse(app(h, ni)) ⊆ ty.getOrElse(app(h, unionNi))) by Cut(lastStep, getOrElseMonotonic(ty) of (m := ni, n := unionNi))
              have(niInN + hIsTheHeightFunction |- ty.getOrElse(app(h, ni)) ⊆ ty.getOrElse(app(h, unionNi))) by Cut(unionNiInN, lastStep)
              have((niInN + hIsTheHeightFunction + zi ∈ ty.getOrElse(app(h, ni))) |- zi ∈ ty.getOrElse(app(h, unionNi))) by Cut(lastStep, subsetElim of (z := zi, x := ty.getOrElse(app(h, ni)), y := ty.getOrElse(app(h, unionNi))))


            val constructorVarsInDomainHNSplit = co.specification.zipWithIndex.zip(co.variables).map((typeInd, zi) => zi ∈ typeInd._1.getOrElse(app(h, Variable(s"n${typeInd._2}"))))

            have(niInN ++ constructorVarsInDomainHNSplit + hIsTheHeightFunction |- constructorVarsInDomain(co, app(h, unionNi))) by RightAnd(operands*)
            have(niInN ++ constructorVarsInDomainHNSplit + hIsTheHeightFunction |- (unionNi < N) /\ constructorVarsInDomain(co, app(h, unionNi))) by RightAnd(lastStep, unionNiInN)
            thenHave(niInN ++ constructorVarsInDomainHNSplit + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by RightExists

            val constructorVarsInDomainHNSplitWithBound = (co.specification.zipWithIndex.zip(co.variables).map((typeInd, zi) => (Variable(s"n${typeInd._2}") < N) /\ zi ∈ typeInd._1.getOrElse(app(h, Variable(s"n${typeInd._2}"))))).toSet

            thenHave(constructorVarsInDomainHNSplitWithBound + ordinal(N) + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by Restate
            have(constructorVarsInDomainHNSplitWithBound + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by Cut(heightDomainOrdinal, lastStep)


            co.specification.zipWithIndex.zip(co.variables).foldLeft(constructorVarsInDomainHNSplitWithBound.toSet)((acc, el) => 
              val ((ty, i), zi) = el
              val ni = Variable(s"n${i}") 
              val varInDomain = (ni < N) /\ zi ∈ ty.getOrElse(app(h, ni))
              val newAcc = acc - varInDomain + ∃(ni, varInDomain)
              thenHave(newAcc + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by LeftExists
              newAcc
            )
            

            val exConstructorVarsInDomainHN: Seq[Formula] = (co.specification.zip(co.variables).map((ty, zi) => ∃(n, (n < N) /\ zi ∈ ty.getOrElse(app(h, n)))))
            thenHave((/\+(exConstructorVarsInDomainHN), hIsTheHeightFunction) |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by Weakening

            val formVars = co.specification.zipWithIndex.map((ty, i) => VariableFormula(s"form${i}"))
            val constructorVarsInTerm = co.specification.zip(co.variables).map((ty, zi) => zi ∈ ty.getOrElse(term))
            val zipConstructorVars = exConstructorVarsInDomainHN.zip(constructorVarsInTerm)

            thenHave(
              zipConstructorVars.map(_ <=> _).toSet +
              constructorVarsInDomain(co, term) + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))
            ) by 
              LeftSubstIff.withParametersSimple(zipConstructorVars.toList, lambda(formVars, /\+ (formVars)))

            co.specification.zip(co.variables).foldLeft(zipConstructorVars.map(_ <=> _))((acc, el) => 
              val (ty, zi) = el
              val tailAcc = acc.tail
              have(tailAcc.toSet + constructorVarsInDomain(co, term) + hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by Cut(getOrElseHasHeight(ty) of (x := zi), lastStep)
              tailAcc
            )
          }

          val backward = have(hIsTheHeightFunction |- ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n))) ==> constructorVarsInDomain(co, term)) subproof {
            val operands = co.specification.zip(co.variables).map( (ty, zi) => 
              have((hIsTheHeightFunction, (n < N), zi ∈ ty.getOrElse(app(h, n))) |- zi ∈ ty.getOrElse(term)) by Cut(getOrElseHeightSubsetTerm(ty), subsetElim of (z := zi, x := ty.getOrElse(app(h, n)), y := ty.getOrElse(term)))
              thenHave((hIsTheHeightFunction, (n < N) /\ constructorVarsInDomain(co, app(h, n))) |- zi ∈ ty.getOrElse(term)) by Weakening
              thenHave((hIsTheHeightFunction, ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) |- zi ∈ ty.getOrElse(term)) by LeftExists
            )
            have((hIsTheHeightFunction, ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) |- constructorVarsInDomain(co, term)) by RightAnd(operands*)
          }

          have(hIsTheHeightFunction |- constructorVarsInDomain(co, term) <=> ∃(n, (n < N) /\ constructorVarsInDomain(co, app(h, n)))) by RightIff(forward, backward)
      }
    )
    .toMap

  /**
   * Lemma --- If all inductive arguments of a constructor have height below n then the instance of
   * this constructor has height below n + 1.
   *
   *      ` xi, ..., xj ∈ height(n) |- c(x1, ..., xn) ∈ height(n + 1)`
   */
  private val heightConstructor = benchmark(constructors
    .map(c =>
      c -> Lemma((hIsTheHeightFunction, n < N, constructorVarsInDomain(c, app(h, n))) |- c.term ∈ app(h, successor(n))) {
        have((hIsTheHeightFunction, n < N, constructorVarsInDomain(c, app(h, n))) |- c.term ∈ app(h, successor(n))) by Substitution.ApplyRules(heightSuccessor of (x := c.term))(constructorIsInIntroductionFunction(c) of (s := app(h, n)))
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
        Lemma(simplify(constructorVarsInDomain(c, term)) |- simplify(c.term ∈ term)) {

          // STEP 1: Prove that if an instance of a constructor has height n + 1 then it is in this ADT.
          have((hIsTheHeightFunction, n < N, c.term ∈ app(h, successor(n))) |- c.term ∈ term) by Cut(successorIsInHeightDomain, termHasHeightIntro of (n := successor(n), x := c.term))

          // STEP 2: Prove that if the inductive arguments of the constructor have height then the instance of the constructor is in the ADT.
          have((hIsTheHeightFunction, n < N, constructorVarsInDomain(c, app(h, n))) |- c.term ∈ term) by Cut(heightConstructor(c), lastStep)

          // STEP 3: Prove that if the inductive arguments of the constructor are in the ADT then they have a height and therefore
          // the instance of the constructor is in the ADT.
          thenHave((hIsTheHeightFunction, (n < N) /\ constructorVarsInDomain(c, app(h, n))) |- c.term ∈ term) by LeftAnd
          thenHave((hIsTheHeightFunction, ∃(n, (n < N) /\ constructorVarsInDomain(c, app(h, n)))) |- c.term ∈ term) by LeftExists
          thenHave((hIsTheHeightFunction, constructorVarsInDomain(c, term)) |- c.term ∈ term) by Substitution.ApplyRules(getOrElseHaveHeight(c))

          // STEP 4: Remove lingering assumptions
          thenHave((∃(h, hIsTheHeightFunction), constructorVarsInDomain(c, term)) |- c.term ∈ term) by LeftExists
          have(constructorVarsInDomain(c, term) |- c.term ∈ term) by Cut(heightFunctionExistence, lastStep)
        }
    })
    .toMap)

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

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
          case Self => ∀(v, v ∈ term ==> (P(v) ==> fc))
          case GroundType(t) => ∀(v, v ∈ t ==> (True ==> fc))
          case f : FunctionType => 
            ∀(v, v ∈ f.getOrElse(term) ==> (forallSeq(f.variables, f.wellTypedDomains ==>  P(appSeq(v)(f.variables))) ==> fc))
      )
    )
    .toMap

  /**
   * Lemma --- Structural induction principle for this ADT.
   *
   *    `inductive cases => ∀x ∈ ADT. P(x)`
   */
  lazy val induction = benchmark(Lemma(constructors.foldRight[Formula](∀(x, x ∈ term ==> P(x)))((c, f) => inductiveCase(c) ==> f)) {

    // List of cases to prove for structural induction to hold
    val structuralInductionPreconditions: Formula = /\+(constructors.map(inductiveCase))

    // We want to prove the claim by induction on the height of n, i.e. prove that for any
    // n in N, P holds.
    def inductionFormula(n: Term): Formula = ∀(x, x ∈ app(h, n) ==> P(x))

    // STEP 1: Prove the base case
    have(hIsTheHeightFunction |- x ∉ app(h, ∅)) by Cut(heightZero, emptySetHasNoElements of (x := app(h, ∅), y := x))
    thenHave((hIsTheHeightFunction, n === ∅) |- x ∉ app(h, n)) by Substitution.ApplyRules(n === ∅)
    val zeroCase = thenHave((hIsTheHeightFunction, n === ∅) |- x ∈ app(h, n) ==> P(x)) by Weakening

    // STEP 2: Prove the inductive case
    val succCase = have((structuralInductionPreconditions, hIsTheHeightFunction, successorOrdinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) subproof {

      val ih = ∀(m, (m < successor(a)) ==> inductionFormula(m))

      have(ih |- ih) by Hypothesis
      thenHave((a < successor(a), ih) |- ∀(x, x ∈ app(h, a) ==> P(x))) by InstantiateForall(a)
      have(ih |- ∀(x, x ∈ app(h, a) ==> P(x))) by Cut(inSuccessor, lastStep)
      val proofP = thenHave((ih, x ∈ app(h, a)) |- P(x)) by InstantiateForall(x)

      val operands = 
        for c <- constructors yield

          have((ih, inductiveCase(c)) |- inductiveCase(c)) by Restate

          c.signature.foldLeft[(Formula, Set[Formula])]((inductiveCase(c), Set(ih, hIsTheHeightFunction, inductiveCase(c), a < N)))((acc, el) => 
            val (v, ty) = el
            val (remCases, vars) = acc
            val newVars = vars + v ∈ ty.getOrElse(app(h, a))
            
            (remCases match
              case Forall(bindVar, Implies(typedVar, Implies(precond, core))) =>
                thenHave(vars + v ∈ ty.getOrElse(term) + precond |- core) by InstantiateForall(v)
                have(newVars + ty.getOrElse(app(h, a)) ⊆ ty.getOrElse(term) + precond |- core) by Cut(subsetElim of (z := v, x := ty.getOrElse(app(h, a)), y := ty.getOrElse(term)), lastStep)
                val precondToProve = have(newVars + precond |- core) by Cut(getOrElseHeightSubsetTerm(ty) of (n := a), lastStep)
                ty match
                  case Self => have(newVars |- core) by Cut(proofP of (x := v), lastStep)
                  case f : FunctionType => have(newVars |- core) by Sorry
                  case GroundType(_) => thenHave(newVars  |- core) by Weakening
                core
              case _ => throw UnreachableException
            , newVars) 
          )

          thenHave((constructorVarsInDomain(c, app(h, a)), ih, hIsTheHeightFunction, inductiveCase(c), a < N) |- P(c.term)) by Restate
          thenHave((constructorVarsInDomain(c, app(h, a)), x === c.term, ih, hIsTheHeightFunction, inductiveCase(c), a < N) |- P(x)) by Substitution.ApplyRules(x === c.term)
          thenHave((constructorVarsInDomain(c, app(h, a)) /\ (x === c.term), ih, hIsTheHeightFunction, inductiveCase(c), a < N) |- P(x)) by LeftAnd
          thenHave((existsSeq(c.variables, constructorVarsInDomain(c, app(h, a)) /\ (x === c.term)), a < N, ih, hIsTheHeightFunction, inductiveCase(c)) |- P(x)) by QuantifiersIntro(c.variables)

      val preconditionsSet = constructors.map(inductiveCase).toSet + hIsTheHeightFunction

      have((preconditionsSet + isConstructor(x, app(h, a)) + (a < N) + ih) |- P(x)) by LeftOr(operands*)
      have((preconditionsSet + isInIntroductionFunctionImage(app(h, a))(x) + (a < N) + ih) |- P(x)) by LeftOr(lastStep, proofP)
      thenHave((preconditionsSet + x ∈ app(h, successor(a)) + (a < N) + ih) |- P(x)) by Substitution.ApplyRules(heightSuccessor)
      have((preconditionsSet + x ∈ app(h, successor(a)) + ordinal(N) + (a < successor(a)) + (successor(a) < N) + ih) |- P(x)) by Cut(ordinalTransitive of (b := successor(a), c := N), lastStep)
      have((preconditionsSet + x ∈ app(h, successor(a)) + ordinal(N) + (successor(a) < N) + ih + hIsTheHeightFunction) |- P(x)) by Cut(inSuccessor, lastStep)
      thenHave((preconditionsSet + (n === successor(a)) + x ∈ app(h, n) + ordinal(N) + (n < N) + ∀(m, (m < n) ==> inductionFormula(m)) + hIsTheHeightFunction) |- P(x)) by Substitution.ApplyRules(n === successor(a))
      thenHave((preconditionsSet + ∃(a, n === successor(a)) + x ∈ app(h, n) + ordinal(N) + (n < N) + ∀(m, (m < n) ==> inductionFormula(m)) + hIsTheHeightFunction) |- P(x)) by LeftExists
      thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(n) /\ ∃(a, n === successor(a)), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) by Weakening
      thenHave((structuralInductionPreconditions, hIsTheHeightFunction, successorOrdinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) by Substitution.ApplyRules(successorOrdinal.definition)
    }

    // STEP 3: Prove the limit case
    val limitCase = have((hIsTheHeightFunction, limitOrdinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) subproof {
      have(∀(m, (m < n) ==> inductionFormula(m)) |- ∀(m, (m < n) ==> inductionFormula(m))) by Hypothesis
      thenHave((m < n, ∀(m, (m < n) ==> inductionFormula(m))) |- inductionFormula(m)) by InstantiateForall(m)
      thenHave(((m < n) /\ x ∈ app(h, m), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by InstantiateForall(x)
      thenHave((ordinal(N), n < N, (m < (N ∩ n)) /\ x ∈ app(h, m), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by Substitution.ApplyRules(intersectionInOrdinal of (a := N, b := n))
      thenHave((hIsTheHeightFunction, ordinal(N), n < N, (m < (dom(h) ∩ n)) /\ x ∈ app(h, m), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by Substitution.ApplyRules(heightFunctionDomain) 
      thenHave((hIsTheHeightFunction, ordinal(N), n < N, ∃(m, (m < (dom(h) ∩ n)) /\ x ∈ app(h, m)), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by LeftExists 
      have((hIsTheHeightFunction, ordinal(N), n < N, functional(h), x ∈ uran(h ↾ n), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by Cut(unionRangeRestrElim of (f := h, d := n, z := x), lastStep)
      have((hIsTheHeightFunction, ordinal(N), n < N, functionalOver(h, N), x ∈ uran(h ↾ n), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by Cut(functionalOverIsFunctional of (f := h, x := N), lastStep)
      thenHave((hIsTheHeightFunction, ordinal(N), n < N, limitOrdinal(n), functionalOver(h, N), x ∈ app(h, n), ∀(m, (m < n) ==> inductionFormula(m))) |- P(x)) by Substitution.ApplyRules(heightLimit)
    }

    have((structuralInductionPreconditions, hIsTheHeightFunction, limitOrdinal(n) \/ successorOrdinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) by LeftOr(succCase, limitCase)
    have((structuralInductionPreconditions, hIsTheHeightFunction, (n === ∅) \/ limitOrdinal(n) \/ successorOrdinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) by LeftOr(zeroCase, lastStep)
    have((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- x ∈ app(h, n) ==> P(x)) by Cut(successorOrNonsuccessorOrdinal of (a := n), lastStep)
    thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(n), ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- inductionFormula(n)) by RightForall
    have((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N), n < N, ∀(m, (m < n) ==> inductionFormula(m))) |- inductionFormula(n)) by Cut(elementsOfOrdinalsAreOrdinals of (b := n, a := N), lastStep)
    thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N), n < N) |- ∀(m, (m < n) ==> inductionFormula(m)) ==> inductionFormula(n)) by RightImplies
    
    thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N)) |- (n < N) ==> (∀(m, (m < n) ==> inductionFormula(m)) ==> inductionFormula(n))) by RightImplies
    thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N)) |- ∀(n, (n < N) ==> (∀(m, (m < n) ==> inductionFormula(m)) ==> inductionFormula(n)))) by RightForall
    have((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N)) |- ∀(n, (n < N) ==> inductionFormula(n))) by Cut(lastStep, transfiniteInductionOnOrdinal of (x := N, P := lambda(n, inductionFormula(n))))
    thenHave((structuralInductionPreconditions, hIsTheHeightFunction, ordinal(N), n < N) |- inductionFormula(n)) by InstantiateForall(n)
    sorry
  })

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
) extends lisa.Main {
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
    private val uniqueness = Axiom(∃!(c, untypedDefinition))

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
      have(∀(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
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
      have(∀(c, (term === c) <=> untypedDefinition)) by Exact(classFunction.definition)
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
        Lemma(vars1WellTyped ++ vars2WellTyped |- simplify((appliedTerm1 === appliedTerm2) <=> (variables1 ===+ variables2))) {

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

          thenHave(thesis) by Substitution.ApplyRules(underlying.injectivity)
        }

    
    /**
     * Case generated by this constructor when performing a proof by induction
     */
    lazy val inductiveCase: Formula =
      syntacticSignature.foldRight[Formula](P(appliedTerm1))
        ((el, fc) =>
          val (v, typ) = el
          typ match
            case Self => ∀(v, v :: adt.term ==> (P(v) ==> fc))
            case GroundType(t) => ∀(v, v :: t ==> fc)
            case f: FunctionType => ∀(v, v :: f.getOrElse(adt.term) ==> (forallSeq(f.variables, f.wellTypedDomains ==> P(appSeq(v)(f.variables))) ==> fc))
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
    ) extends lisa.Main {

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

        have(c1.structuralTerm1 === c2.structuralTerm2 |- ()) by Restate.from(underlying.injectivity(c1.underlying, c2.underlying))
        have((vars1WellTyped ++ vars2WellTyped) + (c1.appliedTerm1 === c2.appliedTerm2) |- ()) by Cut(defUnfolding, lastStep)
      }

    /**
     * Theorem --- Structural induction principle for this ADT.
     *
     *    `base cases => inductive cases => ∀x ∈ ADT. P(x)`
     */
    lazy val induction = Lemma(constructors.foldRight[Formula](∀(x, x :: term ==> P(x)))((c, f) => c.inductiveCase ==> f)) { sp ?=>
      constructors.foldRight[(Formula, Formula, sp.Fact)] {
        val prop = ∀(x, x :: term ==> P(x))
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
                  have(wellTypedVars |- (P(v) ==> fc1) <=> (P(v) ==> fc2)) by Cut(lastStep, leftImpliesEquivalenceWeak of (p := P(v), p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- wellTypedV ==> ((P(v) ==> fc1) <=> (P(v) ==> fc2))) by RightImplies
                  have(wellTypedVars.init |- (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2))) by Cut(
                    lastStep,
                    leftImpliesEquivalenceStrong of (p := wellTypedV, p1 := P(v) ==> fc1, p2 := P(v) ==> fc2)
                  )
                  thenHave(wellTypedVars.init |- ∀(v, (wellTypedV ==> (P(v) ==> fc1)) <=> (wellTypedV ==> (P(v) ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- ∀(v, (wellTypedV ==> (P(v) ==> fc1))) <=> ∀(v, (wellTypedV ==> (P(v) ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, wellTypedV ==> (P(v) ==> fc1)), Q := lambda(v, wellTypedV ==> (P(v) ==> fc2)))
                  )
                  (∀(v, wellTypedV ==> (P(v) ==> fc1)), ∀(v, wellTypedV ==> (P(v) ==> fc2)), wellTypedVars.init)
                case GroundType(t) =>
                  thenHave(wellTypedVars.init |- v :: t ==> (fc1 <=> fc2)) by RightImplies
                  have(wellTypedVars.init |- (v ∈ t ==> fc1) <=> (v :: t ==> fc2)) by Cut(lastStep, leftImpliesEquivalenceStrong of (p := v ∈ t, p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- ∀(v, (v ∈ t ==> fc1) <=> (v :: t ==> fc2))) by RightForall
                  have(wellTypedVars.init |- ∀(v, (v ∈ t ==> fc1)) <=> ∀(v, (v :: t ==> fc2))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, v ∈ t ==> fc1), Q := lambda(v, v :: t ==> fc2))
                  )
                  (∀(v, (v ∈ t ==> fc1)), ∀(v, (v :: t ==> fc2)), wellTypedVars.init)
                case f: FunctionType =>
                  val indHypothesis: Formula = forallSeq(f.variables, f.wellTypedDomains ==> P(appSeq(v)(f.variables)))
                  val wellTypedV: Formula = v :: f.getOrElse(term)
                  have(wellTypedVars |- (indHypothesis ==> fc1) <=> (indHypothesis ==> fc2)) by Cut(lastStep, leftImpliesEquivalenceWeak of (p := indHypothesis, p1 := fc1, p2 := fc2))
                  thenHave(wellTypedVars.init |- wellTypedV ==> ((indHypothesis ==> fc1) <=> (indHypothesis ==> fc2))) by RightImplies
                  have(wellTypedVars.init |- (wellTypedV ==> (indHypothesis ==> fc1)) <=> (wellTypedV ==> (indHypothesis ==> fc2))) by Cut(
                    lastStep,
                    leftImpliesEquivalenceStrong of (p := wellTypedV, p1 := indHypothesis ==> fc1, p2 := indHypothesis ==> fc2)
                  )
                  thenHave(wellTypedVars.init |- ∀(v, (wellTypedV ==> (indHypothesis ==> fc1)) <=> (wellTypedV ==> (indHypothesis ==> fc2)))) by RightForall
                  have(wellTypedVars.init |- ∀(v, (wellTypedV ==> (indHypothesis ==> fc1))) <=> ∀(v, (wellTypedV ==> (indHypothesis ==> fc2)))) by Cut(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(v, wellTypedV ==> (indHypothesis ==> fc1)), Q := lambda(v, wellTypedV ==> (indHypothesis ==> fc2)))
                  )
                  (∀(v, wellTypedV ==> (indHypothesis ==> fc1)), ∀(v, wellTypedV ==> (indHypothesis ==> fc2)), wellTypedVars.init)
            )
        }
        (newBefore, newAfter, have(newBefore <=> newAfter) by Apply(impliesEquivalence).on(lastStep, fact))
      )
      have(underlying.induction.statement.right.head |- thesis.right.head) by Cut(
        lastStep,
        equivalenceApply of (
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
      \/+(constructors.map(c => isConstructorMap(c)))

    /**
     * Theorem --- Pattern matching principle (also known as elimination rule) for this ADT.
     *
     *    `x ∈ ADT |- x = c * x1 * ... * xn for some constructor c and xi, ..., xj ∈ ADT`
     */
    lazy val elim = Lemma(x :: term |- simplify(isConstructor)) {

      // Induction preconditions with P(z) = z != x
      val inductionPreconditionIneq = constructors.map(c => c -> c.inductiveCase.substitute((P -> lambda(z, !(x === z))))).toMap
      val inductionPreconditionsIneq = /\+(inductionPreconditionIneq.map(_._2))

      // Weakening of the negation of the induction preconditions
      val weakNegInductionPreconditionIneq: Map[SemanticConstructor[N], Formula] = constructors
        .map(c =>
          c ->
            c.semanticSignature
              .foldRight[Formula](x === c.appliedTerm)((el, fc) =>
                val (v, t) = el
                ∃(v, (v :: t) /\ fc)
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
                        thenHave((x =/= v) /\ left |- right) by Weakening
                      case _ => ()

                    val weakr = thenHave(v ∈ ty.getOrElse(term) /\ left |- right) by Weakening
                    val weakl = have(v ∈ ty.getOrElse(term) /\ left |- v ∈ ty.getOrElse(term)) by Restate

                    have((v :: ty.getOrElse(term)) /\ left |- (v :: ty.getOrElse(term)) /\ right) by RightAnd(weakl, weakr)
                    thenHave((v :: ty.getOrElse(term)) /\ left |- ∃(v, (v :: ty.getOrElse(term)) /\ right)) by RightExists
                    thenHave(∃(v, (v :: ty.getOrElse(term)) /\ left) |- ∃(v, (v :: ty.getOrElse(term)) /\ right)) by LeftExists
                  )

              }

              // STEP 1.1.2: Conclude
              // TODO: Change to a more efficient way of proving this
              have(weakNegInductionPreconditionIneq(c) |- isConstructorMap(c)) by Tableau
              have(!inductionPreconditionIneq(c) |- isConstructorMap(c)) by Cut(conditionStrenghtening, lastStep)
              thenHave(!inductionPreconditionIneq(c) |- isConstructor) by Weakening

          have(thesis) by LeftOr(negInductionPreconditionsOrSequence*)
      }

      // STEP 2: Conclude
      have(inductionPreconditionsIneq |- ∀(z, z :: term ==> !(x === z))) by Restate.from(induction of (P := lambda(z, !(x === z))))
      val ind = thenHave(x :: term |- !inductionPreconditionsIneq) by InstantiateForall(x)
      have(x :: term |- isConstructor) by Cut(lastStep, strengtheningOfInductionPreconditions)
    }
  }






