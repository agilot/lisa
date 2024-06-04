package lisa.maths.settheory.orderings

import lisa.maths.settheory.orderings.PartialOrders.*
import lisa.maths.settheory.SetTheory.*
import lisa.automation.settheory.SetTheoryTactics.*

object Bounds extends lisa.Main {

  val a = variable
  val b = variable
  val r = variable
  val t = variable
  val x = variable
  val y = variable
  val z = variable

  /**
   * Definition --- Subset Maximal Element in a Strict Partial Order
   * 
   * `a` is a maximal element of `y ⊆ x` with respect to a strict partial order `(r, x)` if 
   *
   *    `∀ b ∈ y. (a, b) ∉ r`
   */
  val maximalElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ ∀(b, in(b, y) ==> (!in(pair(a, b), r)))


  /**
   * Definition --- Subset Minimal Element in a Strict Partial Order
   * 
   * `a` is a minimal element of `y ⊆ x` with respect to a strict partial order `(r, x)` if 
   *
   *    `∀ b ∈ y. (b, a) ∉ r`
   */
  val minimalElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ ∀(b, in(b, y) ==> (!in(pair(b, a), r)))

  /**
   * Greatest Element --- `a` is the greatest element of `y` with respect to
   * `r`, where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   */
  val greatestElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ ∀(b, in(b, y) ==> (in(pair(b, a), r) \/ (a === b)))

  /**
   * Least Element --- `a` is the least element of `y` with respect to `r`,
   * where `p = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   */

  val leastElement = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ in(a, y) /\ ∀(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))

  /**
   * Upper Bound --- `a` is an upper bound on `y` with respect to `r`, where `p
   * = (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. b r a ⋁ b = a`
   *
   * Note that as opposed to the greatest element, `a` is not enforced to be an
   * element of `y`.
   */
  val upperBound = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ ∀(b, in(b, y) ==> (in(pair(b, a), r) \/ (a === b)))

  /**
   * Lower Bound --- `a` is a lower bound on `y` with respect to `r`, where `p =
   * (r, x)` is a partial order on `x`, and `y ⊆ x`.
   *
   *    `∀ b ∈ y. a r b ⋁ b = a`
   *
   * Note that as opposed to the least element, `a` is not enforced to be an
   * element of `y`
   */
  val lowerBound = DEF(a, y, r, x) --> strictPartialOrder(r, x) /\ subset(y, x) /\ ∀(b, in(b, y) ==> (in(pair(a, b), r) \/ (a === b)))

  val setOfUpperBoundsUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ upperBound(t, y, r, x))))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(t, upperBound(t, y, r, x)))
  }

  /**
   * The set of all upper bounds of a set `y` under a partial order `p`. Used to define [[leastUpperBound]]
   */
  val setOfUpperBounds = DEF(y, r, x) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ upperBound(t, y, r, x))))(setOfUpperBoundsUniqueness)

  /**
   * Least Upper Bound --- `a` is the least upper bound on `y ⊆ x` under
   * a partial order `p = (r, x)` if it is the least element in the
   * [[setOfUpperBounds]] of `y` under `p`.
   */
  val greatestUpperBound = DEF(a, y, r, x) --> leastElement(a, setOfUpperBounds(y, r, x), r, x)

  /**
   * Alias for [[greatestUpperBound]]
   */
  val supremum = greatestUpperBound

  val setOfLowerBoundsUniqueness = Lemma(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, x) /\ lowerBound(t, y, r, x))))
  ) {
    have(thesis) by UniqueComprehension(x, lambda(t, lowerBound(t, y, r, x)))
  }

  /**
   * The set of all lower bounds of a set `y` under a partial order `p`. Used to define [[greatestLowerBound]]
   */
  val setOfLowerBounds = DEF(y, r, x) --> The(z, ∀(t, in(t, z) <=> (in(t, x) /\ lowerBound(t, y, r, x))))(setOfLowerBoundsUniqueness)



  /**
   * Greatest Lower Bound --- `a` is the greatest lower bound on `y ⊆ x`
   * under a partial order `p = (r, x)` if it is the greatest element in the
   * [[setOfLowerBounds]] of `y` under `p`.
   */
  val greatestLowerBound = DEF(a, y, r, x) --> greatestElement(a, setOfLowerBounds(y, r, x), r, x)

  /**
   * Alias for [[greatestLowerBound]]
   */
  val infimum = greatestLowerBound

}