import lisa.maths.settheory.SetTheory.singleton
import lisa.utils.parsing.SynonymInfo.empty
object ADTExample extends lisa.Main {
  import lisa.maths.settheory.types.adt.{*, given}

  // variable declarations
  val a = variable
  val b = variable

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
  val define(option: ADT[1], constructors(none, some)) = a --> () | nat

  // List
  val define(list: ADT[1], constructors(nil, cons)) = a --> () | (a, list)

  //Binary Trees
  val define(tree: ADT[1], constructors(leaf, node)) = a --> a | (a, nat |=> tree)

  // Nothing
  val define(nothing, constructors()) = |

  // ****************
  // * 2 : Theorems *
  // ****************

  // Injectivity
  show(nil.injectivity)
  show(cons.injectivity)
  show(list.injectivity(nil, cons))
  show(tree.induction)

  // Introduction rules
  show(nil.intro)
  show(cons.intro)

  Lemma(nil(a) :: list(a)){
    have(thesis) by TypeChecker.prove
  } 
  Lemma(cons(nat) * (succ * zero) * nil(nat) :: list(nat)){
    have(thesis) by TypeChecker.prove
  } 

  // Induction
  show(list.induction)

  // Pattern matching
  show(list.elim)

  // *****************
  // * 3 : Functions *
  // *****************

  val not = fun(bool, bool) {
    Case(tru) { fals }
    Case(fals) { tru }
  }

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
  // * 5: All features together *
  // ****************************

  val succInj = Theorem(n :: nat |- !(n === succ * n)) {
    
    val boolean = unorderedPair(emptySet, singleton(emptySet))
    val f = variable
    have((b :: boolean, f :: (boolean |=> boolean)) |- f * b :: boolean) by TypeChecker.prove
    have(thesis) by Induction() {
      Case(zero) subproof {
        have(zero :: nat) by TypeChecker.prove
        have(!(zero === succ * zero)) by 
          Tautology.from(nat.injectivity(zero, succ) of (y0 := zero), lastStep)
      }
      
      Case(succ, n) subproof {
        have((n :: nat) |- succ * n :: nat) by TypeChecker.prove
        have((!(n === succ * n), n :: nat) |- !(succ * n === succ * (succ * n))) by 
          Tautology.from(succ.injectivity of (x0 := n, y0 := succ * n), lastStep)
      }
    }
  }

  val consInj = Theorem((l :: list(a), x :: a) |- !(l === cons(a) * x * l)) {

    val typeNil = have(nil(a) :: list(a)) by TypeChecker.prove
    val typeCons = have((y :: a, l :: list(a)) |- cons(a) * y * l :: list(a)) by TypeChecker.prove

    have(l :: list(a) |- forall(x, x :: a ==> !(l === cons(a) * x * l))) by Induction(){
      Case(nil) subproof {
        have(x :: a ==> !(nil(a) === cons(a) * x * nil(a))) by Tautology.from(list.injectivity(nil, cons) of (y0 := x, y1 := nil(a)), typeNil)
        thenHave(forall(x, x :: a ==> !(nil(a) === cons(a) * x * nil(a)))) by RightForall
      }
      Case(cons, y, l) subproof {
        have((y :: a ==> !(l === cons(a) * y * l), y :: a, l :: list(a)) |- x :: a ==> !(cons(a) * y * l === cons(a) * x * (cons(a) * y * l))) by Tautology.from(
             cons.injectivity of (x0 := y, x1 := l, y0 := x, y1 := cons(a) * y * l),
             typeCons
           )
        thenHave((y :: a ==> !(l === cons(a) * y * l), y :: a, l :: list(a)) |- forall(x, x :: a ==> !(cons(a) * y * l === cons(a) * x * (cons(a) * y * l)))) by RightForall
        thenHave((forall(x, x :: a ==> !(l === cons(a) * x * l)), y :: a, l :: list(a)) |- forall(x, x :: a ==> !(cons(a) * y * l === cons(a) * x * (cons(a) * y * l)))) by LeftForall
      }
    }

    thenHave(l :: list(a) |- x :: a ==> !(l === cons(a) * x * l)) by InstantiateForall(x)
    thenHave(thesis) by Tautology
  }

}