/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Unimodular Crystallographic Cartan Quadratic Forms of Rank 2 and Rank 4

This file studies the symmetrized quadratic forms and Cartan determinants associated with
the unimodular crystallographic root systems of rank 2 (`g2CartanForm`) and rank 4
(`f4CartanForm`). Both forms have Cartan determinant equal to `1` and admit exact
integer-scaled sum-of-squares decompositions.

## Main results

* `CartanCoxeterRigidity.g2CartanDet_eq_one`: `2 * 2 - (-1) * (-3) = 1`.
* `CartanCoxeterRigidity.two_mul_g2CartanForm_eq`:
  `2 * g2CartanForm x y = (2 * x - 3 * y) ^ 2 + 3 * y ^ 2`.
* `CartanCoxeterRigidity.g2CartanForm_eq_zero_iff`: positive-definite elimination on `G₂`.
* `CartanCoxeterRigidity.six_mul_f4CartanForm_eq`: 4-square decomposition of `6 * f4CartanForm`.
* `CartanCoxeterRigidity.f4CartanForm_eq_zero_iff`: positive-definite elimination on `F₄`.
-/

@[expose] public section

namespace CartanCoxeterRigidity

variable {R : Type*} [CommRing R]

/-- Symmetrized rank-2 Cartan quadratic form `2 x² - 6 x y + 6 y²` of type `G₂`. -/
def g2CartanForm (x y : R) : R :=
  2 * x ^ 2 - 6 * x * y + 6 * y ^ 2

/-- Symmetrized rank-4 Cartan quadratic form of type `F₄`. -/
def f4CartanForm (x₁ x₂ x₃ x₄ : R) : R :=
  4 * x₁ ^ 2 - 4 * x₁ * x₂ + 4 * x₂ ^ 2 - 4 * x₂ * x₃ +
    2 * x₃ ^ 2 - 2 * x₃ * x₄ + 2 * x₄ ^ 2

/-- The determinant of the `2 × 2` Cartan matrix `[[2, -1], [-3, 2]]` of `G₂` equals `1`. -/
theorem g2CartanDet_eq_one : (2 : ℤ) * 2 - (-1) * (-3) = 1 := by
  ring

/-- Exact integer-scaled completion of squares for `g2CartanForm`. -/
theorem two_mul_g2CartanForm_eq (x y : R) :
    2 * g2CartanForm x y = (2 * x - 3 * y) ^ 2 + 3 * y ^ 2 := by
  unfold g2CartanForm
  ring

/-- Exact integer-scaled completion of squares for `f4CartanForm`. -/
theorem six_mul_f4CartanForm_eq (x₁ x₂ x₃ x₄ : R) :
    6 * f4CartanForm x₁ x₂ x₃ x₄ =
      6 * (2 * x₁ - x₂) ^ 2 + 2 * (3 * x₂ - 2 * x₃) ^ 2 +
      (2 * x₃ - 3 * x₄) ^ 2 + 3 * x₄ ^ 2 := by
  unfold f4CartanForm
  ring

/-- Over any linearly ordered commutative ring, `g2CartanForm x y` vanishes if and only if
`x = 0 ∧ y = 0`. -/
theorem g2CartanForm_eq_zero_iff {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] (x y : F) :
    g2CartanForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h2 : (2 * x - 3 * y) ^ 2 + 3 * y ^ 2 = 0 := by
      rw [← two_mul_g2CartanForm_eq, h, mul_zero]
    have s1 := sq_nonneg (2 * x - 3 * y)
    have s2 := sq_nonneg y
    have hy2 : y ^ 2 = 0 := by nlinarith
    have hy : y = 0 := sq_eq_zero_iff.mp hy2
    have hx2 : (2 * x - 3 * y) ^ 2 = 0 := by nlinarith
    have hx_lin : 2 * x - 3 * y = 0 := sq_eq_zero_iff.mp hx2
    have hx : x = 0 := by linarith
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    unfold g2CartanForm
    ring

/-- Over any linearly ordered commutative ring, `f4CartanForm x₁ x₂ x₃ x₄` vanishes if and
only if all four coordinates are zero. -/
theorem f4CartanForm_eq_zero_iff {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] (x₁ x₂ x₃ x₄ : F) :
    f4CartanForm x₁ x₂ x₃ x₄ = 0 ↔ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 := by
  constructor
  · intro h
    have h6 : 6 * (2 * x₁ - x₂) ^ 2 + 2 * (3 * x₂ - 2 * x₃) ^ 2 +
        (2 * x₃ - 3 * x₄) ^ 2 + 3 * x₄ ^ 2 = 0 := by
      rw [← six_mul_f4CartanForm_eq, h, mul_zero]
    have s1 := sq_nonneg (2 * x₁ - x₂)
    have s2 := sq_nonneg (3 * x₂ - 2 * x₃)
    have s3 := sq_nonneg (2 * x₃ - 3 * x₄)
    have s4 := sq_nonneg x₄
    have hx4_sq : x₄ ^ 2 = 0 := by nlinarith
    have hx4 : x₄ = 0 := sq_eq_zero_iff.mp hx4_sq
    have h_s3 : (2 * x₃ - 3 * x₄) ^ 2 = 0 := by nlinarith
    have hx3_lin : 2 * x₃ - 3 * x₄ = 0 := sq_eq_zero_iff.mp h_s3
    have hx3 : x₃ = 0 := by linarith
    have h_s2 : (3 * x₂ - 2 * x₃) ^ 2 = 0 := by nlinarith
    have hx2_lin : 3 * x₂ - 2 * x₃ = 0 := sq_eq_zero_iff.mp h_s2
    have hx2 : x₂ = 0 := by linarith
    have h_s1 : (2 * x₁ - x₂) ^ 2 = 0 := by nlinarith
    have hx1_lin : 2 * x₁ - x₂ = 0 := sq_eq_zero_iff.mp h_s1
    have hx1 : x₁ = 0 := by linarith
    exact ⟨hx1, hx2, hx3, hx4⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    unfold f4CartanForm
    ring

end CartanCoxeterRigidity
