import lisa.prooflib.OutputManager
object ADTExample extends lisa.Main {

  // importing the adt package
  import lisa.maths.settheory.types.adt.{*, given}
  import lisa.maths.settheory.SetTheory.*


  // variable declarations
  val a = variable
  val b = variable
  val gen = variable

  val n = variable
  val l = variable
  val x = variable
  val y = variable

  val x0 = variable
  val x1 = variable
  val y0 = variable
  val y1 = variable

  // ***********************
  // * 1 : Examples of ADT *
  // ***********************

  // Boolean
  val define(bool: ADT[0], constructors(tru, fals)) = () | ()

  // Nat
  val define(nat: ADT[0], constructors(zero, succ)) = () | nat

  // Option
  val define(option: ADT[1], constructors(none, some)) = gen --> () | nat

  // List
  val define(list: ADT[1], constructors(nil, cons)) = gen --> () | (gen, list)

  // Infinite Trees
  val define(tree: ADT[1], constructors(leaf, node)) = gen --> gen | (gen, nat |=> tree)

  // Nothing
  val define(nothing, constructors()) = |

  // ****************
  // * 2 : Theorems *
  // ****************

  summon[OutputManager].output("2: Theorems")

  // Injectivity
  show(nil.injectivity)
  show(cons.injectivity)
  show(list.injectivity(nil, cons))

  // Introduction rules
  show(nil.intro)
  show(cons.intro)

  // Typechecking
  val listTypecheck = Theorem(cons(nat) * (succ * zero) * nil(nat) :: list(nat)){
    have(thesis) by TypeChecker.prove
  } 

  // Induction
  show(list.induction)

  // Pattern matching
  show(list.elim)

  // *****************
  // * 3 : Functions *
  // *****************

  summon[OutputManager].output("3: Functions")

  // Negation
  val not = fun(bool, bool) {
    Case(tru) { fals }
    Case(fals) { tru }
  }

  // Predecessor
  val pred = fun(nat, option(nat)):
    Case(zero): 
      none(nat) 
    Case(succ, n): 
      some(nat) * n

  show(pred.intro)
  show(pred.elim(succ))

  // ************************
  // * 4 : Induction Tactic *
  // ************************

  summon[OutputManager].output("4: Induction")

  /**
    * Theorem --- Double negation
    * 
    *   `x :: bool |- not (not x) = x`
    */
  Theorem(x :: bool |- not * (not * x) === x) {
    have(thesis) by Induction() {
      Case(tru) subproof {
        val notFals = have(not * fals === tru) by Restate.from((not.elim(fals)))
        have(fals === not * tru) by Restate.from(not.elim(tru))
        have(not * (not * tru) === tru) by Substitution.ApplyRules(lastStep)(notFals)
      }
      Case(fals) subproof {
        val notTrue = have(not * tru === fals) by Restate.from((not.elim(tru)))
        have(tru === not * fals) by Restate.from(not.elim(fals))
        have(not * (not * fals) === fals) by Substitution.ApplyRules(lastStep)(notTrue)
      }
    }
  }

  // ****************************
  // * 5: Everything together *
  // ****************************

  summon[OutputManager].output("5: Everything together")

  /**
    * Theorem --- Every natural number is different from its successor
    * 
    *   `n :: nat |- n != n + 1`
    */
  val succInj = Theorem(n :: nat |- n =/= succ * n) {
    
    val boolean = unorderedPair(∅, singleton(∅))
    val f = variable
    have((b :: boolean, f :: (boolean |=> boolean)) |- f * b :: boolean) by TypeChecker.prove
    have(thesis) by Induction() {
      Case(zero) subproof {
        have(zero :: nat) by TypeChecker.prove
        have(zero =/= succ * zero) by (Apply(nat.injectivity(zero, succ) of (y0 := zero)) on lastStep)
      }
      
      Case(succ, n) subproof {
        have((n :: nat) |- succ * n :: nat) by TypeChecker.prove
        have((n =/= succ * n, n :: nat) |- !(succ * n === succ * (succ * n))) by 
          Tautology.from(succ.injectivity of (x0 := n, y0 := succ * n), lastStep)
      }
    }
  }

  /**
    * Theorem --- Every list is different from its tail
    * 
    *   `l :: list(gen), x :: gen |- l != cons(gen) x l`
    */
  val consInj = Theorem((l :: list(gen), x :: gen) |- !(l === cons(gen) * x * l)) {

    val typeNil = have(nil(gen) :: list(gen)) by TypeChecker.prove
    val typeCons = have((y :: gen, l :: list(gen)) |- cons(gen) * y * l :: list(gen)) by TypeChecker.prove

    have(l :: list(gen) |- forall(x, x :: gen ==> !(l === cons(gen) * x * l))) by Induction(){
      Case(nil) subproof {
        have(x :: gen ==> !(nil(gen) === cons(gen) * x * nil(gen))) by Tautology.from(list.injectivity(nil, cons) of (y0 := x, y1 := nil(gen)), typeNil)
        thenHave(forall(x, x :: gen ==> !(nil(gen) === cons(gen) * x * nil(gen)))) by RightForall
      }
      Case(cons, y, l) subproof {
        have((y :: gen ==> !(l === cons(gen) * y * l), y :: gen, l :: list(gen)) |- x :: gen ==> !(cons(gen) * y * l === cons(gen) * x * (cons(gen) * y * l))) by Tautology.from(
             cons.injectivity of (x0 := y, x1 := l, y0 := x, y1 := cons(gen) * y * l),
             typeCons
           )
        thenHave((y :: gen ==> !(l === cons(gen) * y * l), y :: gen, l :: list(gen)) |- forall(x, x :: gen ==> !(cons(gen) * y * l === cons(gen) * x * (cons(gen) * y * l)))) by RightForall
        thenHave((forall(x, x :: gen ==> !(l === cons(gen) * x * l)), y :: gen, l :: list(gen)) |- forall(x, x :: gen ==> !(cons(gen) * y * l === cons(gen) * x * (cons(gen) * y * l)))) by LeftForall
      }
    }

    thenHave(l :: list(gen) |- x :: gen ==> !(l === cons(gen) * x * l)) by InstantiateForall(x)
  }

  summon[OutputManager].output("Thank you for running this example!", Console.MAGENTA)

}