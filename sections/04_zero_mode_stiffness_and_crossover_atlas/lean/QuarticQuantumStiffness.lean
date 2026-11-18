/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Variational Lower Bounds for Inverse-Linear plus Quadratic Variance Functionals

This file establishes the exact algebraic lower bound for the convex functional
`variationalEnergy b x₀ x = (2 * b * x₀ ^ 3) / x + b * x ^ 2` for `x > 0` over any
linearly ordered field. Via the cubic identity
`2 * x₀ ^ 3 + x ^ 3 - 3 * x₀ ^ 2 * x = (x - x₀) ^ 2 * (x + 2 * x₀)`,
the functional is bounded below globally on `(0, ∞)` by `3 * b * x₀ ^ 2`.

## Main results

* `QuarticQuantumStiffness.cubic_defect_factorization`: exact identity
  `2 * x₀ ^ 3 + x ^ 3 - 3 * x₀ ^ 2 * x = (x - x₀) ^ 2 * (x + 2 * x₀)`.
* `QuarticQuantumStiffness.variationalEnergy_sub_min_eq`: remainder formula above `3 * b * x₀ ^ 2`.
* `QuarticQuantumStiffness.three_mul_sq_le_variationalEnergy`: global lower bound
  `3 * b * x₀ ^ 2 ≤ variationalEnergy b x₀ x` for `x > 0`, `x₀ ≥ 0`, `b ≥ 0`.
* `QuarticQuantumStiffness.variationalEnergy_pos`: strict positivity for `b > 0`, `x₀ > 0`, `x > 0`.
-/

@[expose] public section

namespace QuarticQuantumStiffness

section

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Scaled inverse-linear plus quadratic variance functional
`(2 * b * x₀ ^ 3) / x + b * x ^ 2`. -/
def variationalEnergy (b x₀ x : F) : F :=
  (2 * b * x₀ ^ 3) / x + b * x ^ 2

/-- Algebraic factorization of the three-term cubic AM-GM polynomial defect. -/
theorem cubic_defect_factorization {R : Type*} [CommRing R] (x₀ x : R) :
    2 * x₀ ^ 3 + x ^ 3 - 3 * x₀ ^ 2 * x = (x - x₀) ^ 2 * (x + 2 * x₀) := by
  ring

/-- For `x ≠ 0`, the excess of `variationalEnergy b x₀ x` above `3 * b * x₀ ^ 2` equals
`(b * (x - x₀) ^ 2 * (x + 2 * x₀)) / x`. -/
theorem variationalEnergy_sub_min_eq {b x₀ x : F} (hx : x ≠ 0) :
    variationalEnergy b x₀ x - 3 * b * x₀ ^ 2 =
      (b * (x - x₀) ^ 2 * (x + 2 * x₀)) / x := by
  unfold variationalEnergy
  field_simp [hx]
  ring

/-- Global variational lower bound: for `0 ≤ b`, `0 ≤ x₀`, and `0 < x`,
`3 * b * x₀ ^ 2 ≤ variationalEnergy b x₀ x`. -/
theorem three_mul_sq_le_variationalEnergy {b x₀ x : F}
    (hb : 0 ≤ b) (hx₀ : 0 ≤ x₀) (hx : 0 < x) :
    3 * b * x₀ ^ 2 ≤ variationalEnergy b x₀ x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_diff := variationalEnergy_sub_min_eq (b := b) (x₀ := x₀) hx_ne
  have h_nonneg : 0 ≤ (b * (x - x₀) ^ 2 * (x + 2 * x₀)) / x := by
    positivity
  linarith

/-- Strict positivity of the global minimum when `0 < b`, `0 < x₀`, and `0 < x`. -/
theorem variationalEnergy_pos {b x₀ x : F}
    (hb : 0 < b) (hx₀ : 0 < x₀) (hx : 0 < x) :
    0 < variationalEnergy b x₀ x := by
  have h_min_pos : 0 < 3 * b * x₀ ^ 2 := by positivity
  have h_le := three_mul_sq_le_variationalEnergy (le_of_lt hb) (le_of_lt hx₀) hx
  exact lt_of_lt_of_le h_min_pos h_le

end

end QuarticQuantumStiffness
