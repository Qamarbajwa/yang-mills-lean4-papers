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
# Unimodular Rank-8 `E₈` Cartan Quadratic Form and Positive-Definite Elimination

This module defines the rank-8 `E₈` Cartan quadratic form `e8CartanForm` over any commutative
ring `R` and proves an exact integer-scaled 8-square decomposition `840 * e8CartanForm = ...`,
establishing positive-definite zero-mode elimination over any linearly ordered commutative ring.

## Main results

* `ExceptionalE8Cartan.e8CartanForm`: rank-8 Cartan quadratic form.
* `ExceptionalE8Cartan.e8_sum_of_squares_eq`: exact `840`-scaled completion of squares.
* `ExceptionalE8Cartan.e8CartanForm_nonneg`: non-negativity over ordered commutative rings.
* `ExceptionalE8Cartan.e8CartanForm_eq_zero_iff`: `e8CartanForm x = 0 ↔ x = (0, ..., 0)`.
-/

@[expose] public section

namespace ExceptionalE8Cartan

variable {R : Type*} [CommRing R]

/-- Rank-8 `E₈` Cartan quadratic form with Dynkin chain `0-1-2-3-4-5-6` and branch `4-7`. -/
def e8CartanForm (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : R) : R :=
  2 * x₀ ^ 2 - 2 * x₀ * x₁ +
  2 * x₁ ^ 2 - 2 * x₁ * x₂ +
  2 * x₂ ^ 2 - 2 * x₂ * x₃ +
  2 * x₃ ^ 2 - 2 * x₃ * x₄ +
  2 * x₄ ^ 2 - 2 * x₄ * x₅ - 2 * x₄ * x₇ +
  2 * x₅ ^ 2 - 2 * x₅ * x₆ +
  2 * x₆ ^ 2 +
  2 * x₇ ^ 2

/-- Exact `840`-scaled Cholesky completion of squares for the rank-8 `E₈` Cartan form. -/
theorem e8_sum_of_squares_eq (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : R) :
    840 * e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ =
      420 * (2 * x₀ - x₁) ^ 2 +
      140 * (3 * x₁ - 2 * x₂) ^ 2 +
      70 * (4 * x₂ - 3 * x₃) ^ 2 +
      42 * (5 * x₃ - 4 * x₄) ^ 2 +
      28 * (6 * x₄ - 5 * x₅ - 5 * x₇) ^ 2 +
      20 * (7 * x₅ - 6 * x₆ - 5 * x₇) ^ 2 +
      15 * (8 * x₆ - 5 * x₇) ^ 2 +
      105 * x₇ ^ 2 := by
  unfold e8CartanForm
  ring

section Ordered

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Non-negativity of `e8CartanForm` over any linearly ordered commutative ring. -/
theorem e8CartanForm_nonneg (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : F) :
    0 ≤ e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ := by
  have p0 : 0 ≤ 420 * (2 * x₀ - x₁) ^ 2 := by positivity
  have p1 : 0 ≤ 140 * (3 * x₁ - 2 * x₂) ^ 2 := by positivity
  have p2 : 0 ≤ 70 * (4 * x₂ - 3 * x₃) ^ 2 := by positivity
  have p3 : 0 ≤ 42 * (5 * x₃ - 4 * x₄) ^ 2 := by positivity
  have p4 : 0 ≤ 28 * (6 * x₄ - 5 * x₅ - 5 * x₇) ^ 2 := by positivity
  have p5 : 0 ≤ 20 * (7 * x₅ - 6 * x₆ - 5 * x₇) ^ 2 := by positivity
  have p6 : 0 ≤ 15 * (8 * x₆ - 5 * x₇) ^ 2 := by positivity
  have p7 : 0 ≤ 105 * x₇ ^ 2 := by positivity
  have h840 : 0 ≤ 840 * e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ := by
    rw [e8_sum_of_squares_eq]
    linarith
  by_contra hlt
  push Not at hlt
  have hneg : 840 * e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hlt
  linarith

/-- Positive-definite elimination: `e8CartanForm` vanishes if and only if all 8 coordinates
are identically zero. -/
theorem e8CartanForm_eq_zero_iff (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : F) :
    e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ = 0 ↔
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧
      x₄ = 0 ∧ x₅ = 0 ∧ x₆ = 0 ∧ x₇ = 0 := by
  constructor
  · intro h
    have h840 :
        420 * (2 * x₀ - x₁) ^ 2 + 140 * (3 * x₁ - 2 * x₂) ^ 2 +
        70 * (4 * x₂ - 3 * x₃) ^ 2 + 42 * (5 * x₃ - 4 * x₄) ^ 2 +
        28 * (6 * x₄ - 5 * x₅ - 5 * x₇) ^ 2 +
        20 * (7 * x₅ - 6 * x₆ - 5 * x₇) ^ 2 +
        15 * (8 * x₆ - 5 * x₇) ^ 2 + 105 * x₇ ^ 2 = 0 := by
      rw [← e8_sum_of_squares_eq, h, mul_zero]
    have p0 : 0 ≤ 420 * (2 * x₀ - x₁) ^ 2 := by positivity
    have p1 : 0 ≤ 140 * (3 * x₁ - 2 * x₂) ^ 2 := by positivity
    have p2 : 0 ≤ 70 * (4 * x₂ - 3 * x₃) ^ 2 := by positivity
    have p3 : 0 ≤ 42 * (5 * x₃ - 4 * x₄) ^ 2 := by positivity
    have p4 : 0 ≤ 28 * (6 * x₄ - 5 * x₅ - 5 * x₇) ^ 2 := by positivity
    have p5 : 0 ≤ 20 * (7 * x₅ - 6 * x₆ - 5 * x₇) ^ 2 := by positivity
    have p6 : 0 ≤ 15 * (8 * x₆ - 5 * x₇) ^ 2 := by positivity
    have p7 : 0 ≤ 105 * x₇ ^ 2 := by positivity
    have z7 : x₇ ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (105 : F) * x₇ ^ 2 = 0)).resolve_left (by positivity)
    have hx7 : x₇ = 0 := sq_eq_zero_iff.mp z7
    have z6 : (8 * x₆ - 5 * x₇) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (15 : F) * _ = 0)).resolve_left (by positivity)
    have hx6_lin : 8 * x₆ - 5 * x₇ = 0 := sq_eq_zero_iff.mp z6
    have hx6 : x₆ = 0 :=
      (mul_eq_zero.mp (by linarith : (8 : F) * x₆ = 0)).resolve_left (by positivity)
    have z5 : (7 * x₅ - 6 * x₆ - 5 * x₇) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (20 : F) * _ = 0)).resolve_left (by positivity)
    have hx5_lin : 7 * x₅ - 6 * x₆ - 5 * x₇ = 0 := sq_eq_zero_iff.mp z5
    have hx5 : x₅ = 0 :=
      (mul_eq_zero.mp (by linarith : (7 : F) * x₅ = 0)).resolve_left (by positivity)
    have z4 : (6 * x₄ - 5 * x₅ - 5 * x₇) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (28 : F) * _ = 0)).resolve_left (by positivity)
    have hx4_lin : 6 * x₄ - 5 * x₅ - 5 * x₇ = 0 := sq_eq_zero_iff.mp z4
    have hx4 : x₄ = 0 :=
      (mul_eq_zero.mp (by linarith : (6 : F) * x₄ = 0)).resolve_left (by positivity)
    have z3 : (5 * x₃ - 4 * x₄) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (42 : F) * _ = 0)).resolve_left (by positivity)
    have hx3_lin : 5 * x₃ - 4 * x₄ = 0 := sq_eq_zero_iff.mp z3
    have hx3 : x₃ = 0 :=
      (mul_eq_zero.mp (by linarith : (5 : F) * x₃ = 0)).resolve_left (by positivity)
    have z2 : (4 * x₂ - 3 * x₃) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (70 : F) * _ = 0)).resolve_left (by positivity)
    have hx2_lin : 4 * x₂ - 3 * x₃ = 0 := sq_eq_zero_iff.mp z2
    have hx2 : x₂ = 0 :=
      (mul_eq_zero.mp (by linarith : (4 : F) * x₂ = 0)).resolve_left (by positivity)
    have z1 : (3 * x₁ - 2 * x₂) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (140 : F) * _ = 0)).resolve_left (by positivity)
    have hx1_lin : 3 * x₁ - 2 * x₂ = 0 := sq_eq_zero_iff.mp z1
    have hx1 : x₁ = 0 :=
      (mul_eq_zero.mp (by linarith : (3 : F) * x₁ = 0)).resolve_left (by positivity)
    have z0 : (2 * x₀ - x₁) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (420 : F) * _ = 0)).resolve_left (by positivity)
    have hx0_lin : 2 * x₀ - x₁ = 0 := sq_eq_zero_iff.mp z0
    have hx0 : x₀ = 0 :=
      (mul_eq_zero.mp (by linarith : (2 : F) * x₀ = 0)).resolve_left (by positivity)
    exact ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    unfold e8CartanForm
    ring

end Ordered

end ExceptionalE8Cartan
