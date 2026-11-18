/-
Copyright (c) 2026 Formal Verification Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Verification Authors

! This file was extracted as a self-contained candidate for Mathlib.
-/

/-!
# Zero-Sum Block Variance and Rational Cubic Collar Polynomial Bounds

This module provides self-contained, unconditional algebraic and rational theorems:
1. Exact zero-sum two-point variance identity relating squared differences to sum of squares.
2. Self-contained positive rational pairs with decidable strict inequality.
3. Rational cubic polynomial collar upper bounds at evaluation point delta = 1/5.
-/

namespace MathlibPR.LinearAlgebra

/--
Theorem: For two integer variables x1, x2 satisfying zero sum x1 + x2 = 0,
the squared difference equals twice the sum of squares:
  (x1 - x2)^2 = 2 * (x1^2 + x2^2).
-/
theorem two_point_zero_sum_sq_diff_eq (x1 x2 : Int) (h : x1 + x2 = 0) :
    (x1 - x2) * (x1 - x2) = 2 * (x1 * x1 + x2 * x2) := by
  have h2 : x2 = -x1 := by omega
  subst h2
  have hdiff : x1 - -x1 = 2 * x1 := by omega
  rw [hdiff]
  have hsq : 2 * x1 * (2 * x1) = 4 * (x1 * x1) := by
    rw [Int.mul_assoc, Int.mul_left_comm x1 2 x1, ← Int.mul_assoc]
    rfl
  rw [hsq]
  have hneg : -x1 * -x1 = x1 * x1 := by
    rw [Int.neg_mul_neg]
  rw [hneg]
  have hadd : x1 * x1 + x1 * x1 = 2 * (x1 * x1) := by
    rw [Int.two_mul]
  rw [hadd]
  have hright : 2 * (2 * (x1 * x1)) = 4 * (x1 * x1) := by
    rw [← Int.mul_assoc]
    rfl
  rw [hright]

end MathlibPR.LinearAlgebra

namespace MathlibPR.CubicCollar

/-- Exact non-negative rational pair with positive denominator. -/
structure RatPair where
  num : Nat
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace RatPair

def ofNat (n : Nat) : RatPair := ⟨n, 1, by omega⟩

def mul (a b : RatPair) : RatPair :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def lt (a b : RatPair) : Prop := a.num * b.den < b.num * a.den

instance (a b : RatPair) : Decidable (lt a b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

end RatPair

/-- Evaluated cubic collar constant c = 452 / 1065. -/
def cubicCollarCoeff : RatPair := ⟨452, 1065, by omega⟩

/-- Cubic evaluation parameter delta^3 = 1 / 125 at delta = 1/5. -/
def cubicCollarDeltaCube : RatPair := ⟨1, 125, by omega⟩

/-- Resulting cubic collar value 452 / 133125. -/
def cubicCollarEval : RatPair := ⟨452, 133125, by omega⟩

/-- Target comparison reference threshold
    356398551099682824675502937 / 19979987798223270175317603840. -/
def collarReferenceMargin : RatPair :=
  ⟨356398551099682824675502937, 19979987798223270175317603840, by omega⟩

/-- Theorem: Product of cubic collar coefficient and delta^3 equals exact evaluated pair. -/
theorem cubic_collar_eval_eq :
    RatPair.mul cubicCollarCoeff cubicCollarDeltaCube = cubicCollarEval := by
  rfl

/-- Theorem: Evaluated cubic collar is strictly less than the target margin. -/
theorem cubic_collar_eval_lt_target_margin :
    RatPair.lt cubicCollarEval collarReferenceMargin := by
  decide

/-- Theorem: Evaluated cubic collar is bounded by decimal upper bound 18 / 1000. -/
theorem cubic_collar_eval_lt_decimal_bound :
    RatPair.lt cubicCollarEval ⟨18, 1000, by omega⟩ := by
  decide

end MathlibPR.CubicCollar
