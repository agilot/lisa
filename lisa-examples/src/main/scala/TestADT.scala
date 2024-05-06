object ADTTest extends lisa.Main {
  import lisa.maths.settheory.types.adt.{*, given}

  // // variable declarations
  val A = variable

  // // Nothing
  // val define(nothing, constructors()) = |
  // nothing.induction

  // println("---------------")

  // // Nat
  val define(nat: ADT[0], constructors(zero, succ)) = () | nat
  // show(nat.induction)

  // println("---------------")

  // //Binary Trees
  // val define(tree: ADT[1], constructors(leaf, node)) = A --> A | (A, nat |=> tree)
  // show(tree.induction)


}