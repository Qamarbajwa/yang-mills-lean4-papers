/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cyclic Shift Matrices, Eisenstein Norms, and Concavity Trigonometric Bounds

This module defines the `3 × 3` cyclic shift and diagonal clock matrices, proves the
commutation relation `clock3 ω * shift3 = ω • (shift3 * clock3 ω)` for `ω ^ 3 = 1`,
formalizes the Eisenstein norm quadratic form, and proves Jordan, secant, and pentagonal
spectral lower bounds directly on `Real.sin`.

## Main results

- `ClockShiftMatrices.shift3`, `ClockShiftMatrices.clock3`: `3 × 3` shift and clock matrices.
- `ClockShiftMatrices.clock3_mul_shift3_eq`: Weyl commutation for `ω ^ 3 = 1`.
- `ClockShiftMatrices.eisensteinNormSq`: quadratic form `a ^ 2 - a * b + b ^ 2`.
- `ClockShiftMatrices.chord_normSq_eq_four_mul_sin_sq`: unit-circle chord identity.
- `ClockShiftMatrices.mul_le_sin_of_mem_Icc`: general concavity secant bound on `[0, π]`.
- `ClockShiftMatrices.jordan_spectral_gap_le_four_mul_sin_sq`: `16 / N^2 ≤ 4 sin²(π / N)`.
- `ClockShiftMatrices.secant_spectral_gap_le_four_mul_sin_sq`: `36 / N^2 ≤ 4 sin²(π / N)`.
- `ClockShiftMatrices.four_mul_sin_pi_div_five_sq_gt`: `199 / 144 < 4 sin²(π / 5)`.
-/

@[expose] public section

namespace ClockShiftMatrices

/-- Cyclic shift permutation on `Fin 3`. -/
def shift3Perm (i : Fin 3) : Fin 3 :=
  i + 1

/-- Applying `shift3Perm` three times yields the identity on `Fin 3`. -/
theorem shift3Perm_cube (i : Fin 3) : shift3Perm (shift3Perm (shift3Perm i)) = i := by
  revert i
  decide

/-- Cyclic shift matrix on `Fin 3 × Fin 3` sending basis vector `j` to `j + 1`. -/
def shift3 {R : Type*} [Zero R] [One R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of (fun i j => if j + 1 = i then 1 else 0)

/-- Diagonal clock matrix on `Fin 3 × Fin 3` with entries `ω ^ i`. -/
def clock3 {R : Type*} [CommRing R] (ω : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal (fun i => ω ^ (i : ℕ))

/-- Sylvester clock-and-shift commutation relation for cube roots of unity `ω ^ 3 = 1`. -/
theorem clock3_mul_shift3_eq {R : Type*} [CommRing R] (ω : R) (hω : ω ^ 3 = 1) :
    clock3 ω * shift3 = ω • (shift3 * clock3 ω) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, clock3, shift3,
    Matrix.diagonal_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp
  · calc
      (1 : R) = ω ^ 3 := hω.symm
      _ = ω * ω ^ 2 := by ring
  · ring

/-- Eisenstein integer norm quadratic form `a ^ 2 - a * b + b ^ 2`. -/
def eisensteinNormSq {R : Type*} [Ring R] (a b : R) : R :=
  a ^ 2 - a * b + b ^ 2

/-- First primitive cube-root chord evaluation: `eisensteinNormSq 1 (-1) = 3`. -/
theorem eisenstein_chord_normSq_one {R : Type*} [CommRing R] :
    eisensteinNormSq (1 : R) (-1) = 3 := by
  unfold eisensteinNormSq
  ring

/-- Second primitive cube-root chord evaluation: `eisensteinNormSq 2 1 = 3`. -/
theorem eisenstein_chord_normSq_two {R : Type*} [CommRing R] :
    eisensteinNormSq (2 : R) 1 = 3 := by
  unfold eisensteinNormSq
  ring

/-- Non-negativity of the Eisenstein norm form over any linearly ordered commutative ring. -/
theorem eisensteinNormSq_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (a b : R) :
    0 ≤ eisensteinNormSq a b := by
  unfold eisensteinNormSq
  have hsq : 0 ≤ (2 * a - b) ^ 2 + 3 * b ^ 2 := by positivity
  have hid : 4 * (a ^ 2 - a * b + b ^ 2) = (2 * a - b) ^ 2 + 3 * b ^ 2 := by ring
  linarith

/-- Unit-circle chord identity: `(1 - cos(2α))² + sin(2α)² = 4 sin²(α)`. -/
theorem chord_normSq_eq_four_mul_sin_sq (α : ℝ) :
    (1 - Real.cos (2 * α)) ^ 2 + Real.sin (2 * α) ^ 2 = 4 * Real.sin α ^ 2 := by
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have hsc : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq α]
  calc
    (1 - (2 * Real.cos α ^ 2 - 1)) ^ 2 + (2 * Real.sin α * Real.cos α) ^ 2
        = (2 * (1 - Real.cos α ^ 2)) ^ 2 + 4 * Real.sin α ^ 2 * Real.cos α ^ 2 := by ring
    _ = (2 * Real.sin α ^ 2) ^ 2 + 4 * Real.sin α ^ 2 * Real.cos α ^ 2 := by rw [hsc]
    _ = 4 * Real.sin α ^ 2 * (Real.sin α ^ 2 + Real.cos α ^ 2) := by ring
    _ = 4 * Real.sin α ^ 2 := by rw [add_comm, Real.cos_sq_add_sin_sq α, mul_one]

/-- General concavity secant lower bound for `Real.sin` on `[0, a] ⊆ [0, π]`. -/
theorem mul_le_sin_of_mem_Icc {a x : ℝ} (ha : a ∈ Set.Ioc 0 Real.pi)
    (hx : x ∈ Set.Icc 0 a) :
    (Real.sin a / a) * x ≤ Real.sin x := by
  have ha0 : 0 < a := ha.1
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have ha_mem : a ∈ Set.Icc 0 Real.pi := ⟨ha0.le, ha.2⟩
  have ht1 : 0 ≤ x / a := div_nonneg hx.1 ha0.le
  have ht0 : 0 ≤ 1 - x / a := sub_nonneg.mpr ((div_le_one ha0).mpr hx.2)
  have hsum : (1 - x / a) + x / a = 1 := by ring
  have hcomb : (1 - x / a) • (0 : ℝ) + (x / a) • a = x := by
    simp [smul_eq_mul]
    field_simp [ha0.ne']
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2 h0_mem ha_mem ht0 ht1 hsum
  rw [hcomb, smul_eq_mul, smul_eq_mul, Real.sin_zero, mul_zero, zero_add] at hconc
  linarith [show (x / a) * Real.sin a = (Real.sin a / a) * x by ring]

/-- Jordan's inequality `(2 / π) * x ≤ sin x` on `[0, π / 2]`. -/
theorem jordan_sin_le_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 2)) :
    (2 / Real.pi) * x ≤ Real.sin x := by
  have hpi : Real.pi / 2 ∈ Set.Ioc 0 Real.pi := by
    refine ⟨by positivity, ?_⟩
    linarith [Real.pi_pos]
  have h := mul_le_sin_of_mem_Icc hpi hx
  rw [Real.sin_pi_div_two] at h
  linarith [show (1 : ℝ) / (Real.pi / 2) * x = (2 / Real.pi) * x by ring]

/-- Universal Jordan spectral gap lower bound `16 / N² ≤ 4 sin²(π / N)` for all `N ≥ 2`. -/
theorem jordan_spectral_gap_le_four_mul_sin_sq {N : ℕ} (hN : 2 ≤ N) :
    16 / (N : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNge : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : Real.pi / N ∈ Set.Icc 0 (Real.pi / 2) := by
    refine ⟨div_nonneg Real.pi_pos.le hNpos.le, ?_⟩
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hNge
  have hj := jordan_sin_le_of_mem_Icc hx
  have hleft : (2 / Real.pi) * (Real.pi / N) = 2 / (N : ℝ) := by
    field_simp [Real.pi_ne_zero]
  rw [hleft] at hj
  have h2N : (0 : ℝ) ≤ 2 / N := by positivity
  have hsq : (2 / (N : ℝ)) ^ 2 ≤ Real.sin (Real.pi / N) ^ 2 := by nlinarith
  linarith [show 4 * (2 / (N : ℝ)) ^ 2 = 16 / (N : ℝ) ^ 2 by ring]

/-- Secant chord inequality `(3 / π) * x ≤ sin x` on `[0, π / 6]`. -/
theorem secant_pi_div_six_sin_le_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 6)) :
    (3 / Real.pi) * x ≤ Real.sin x := by
  have hpi : Real.pi / 6 ∈ Set.Ioc 0 Real.pi := by
    refine ⟨by positivity, ?_⟩
    linarith [Real.pi_pos]
  have h := mul_le_sin_of_mem_Icc hpi hx
  rw [Real.sin_pi_div_six] at h
  linarith [show ((1 / 2 : ℝ) / (Real.pi / 6)) * x = (3 / Real.pi) * x by ring]

/-- Asymptotic secant spectral gap bound `36 / N² ≤ 4 sin²(π / N)` for all `N ≥ 6`. -/
theorem secant_spectral_gap_le_four_mul_sin_sq {N : ℕ} (hN : 6 ≤ N) :
    36 / (N : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNge : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : Real.pi / N ∈ Set.Icc 0 (Real.pi / 6) := by
    refine ⟨div_nonneg Real.pi_pos.le hNpos.le, ?_⟩
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hNge
  have hs := secant_pi_div_six_sin_le_of_mem_Icc hx
  have hleft : (3 / Real.pi) * (Real.pi / N) = 3 / (N : ℝ) := by
    field_simp [Real.pi_ne_zero]
  rw [hleft] at hs
  have h3N : (0 : ℝ) ≤ 3 / N := by positivity
  have hsq : (3 / (N : ℝ)) ^ 2 ≤ Real.sin (Real.pi / N) ^ 2 := by nlinarith
  linarith [show 4 * (3 / (N : ℝ)) ^ 2 = 36 / (N : ℝ) ^ 2 by ring]

/-- Exact cosine of `π / 5`: `cos(π / 5) = (1 + √5) / 4`. -/
theorem cos_pi_div_five_eq : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
  have hpos_sin : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h23 : Real.sin (2 * (Real.pi / 5)) = Real.sin (3 * (Real.pi / 5)) := by
    have heq : 2 * (Real.pi / 5) = Real.pi - 3 * (Real.pi / 5) := by ring
    rw [heq, Real.sin_pi_sub]
  rw [Real.sin_two_mul, Real.sin_three_mul] at h23
  have hsin_sq : Real.sin (Real.pi / 5) ^ 2 = 1 - Real.cos (Real.pi / 5) ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq (Real.pi / 5)]
  have hpoly : Real.sin (Real.pi / 5) *
      (4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1) = 0 := by
    have hsub : 3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 -
        2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) = 0 := by linarith
    have hfac : 3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 -
        2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) =
        Real.sin (Real.pi / 5) *
          (3 - 4 * Real.sin (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5)) := by ring
    rw [hfac, hsin_sq] at hsub
    linarith
  have hquad : 4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 :=
    (mul_eq_zero.mp hpoly).resolve_left hpos_sin.ne'
  have hsq5 : (4 * Real.cos (Real.pi / 5) - 1) ^ 2 = 5 := by linarith
  have hcos_gt : 1 / 2 < Real.cos (Real.pi / 5) := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by linarith [Real.pi_pos])
  have hnonneg : 0 ≤ 4 * Real.cos (Real.pi / 5) - 1 := by linarith
  have hsqrt : Real.sqrt 5 = 4 * Real.cos (Real.pi / 5) - 1 := by
    calc
      Real.sqrt 5 = Real.sqrt ((4 * Real.cos (Real.pi / 5) - 1) ^ 2) := by rw [hsq5]
      _ = 4 * Real.cos (Real.pi / 5) - 1 := Real.sqrt_sq hnonneg
  linarith

/-- Exact spectral gap for `N = 5`: `4 sin²(π / 5) = (5 - √5) / 2`. -/
theorem four_mul_sin_pi_div_five_sq_eq :
    4 * Real.sin (Real.pi / 5) ^ 2 = (5 - Real.sqrt 5) / 2 := by
  have hsin_sq : Real.sin (Real.pi / 5) ^ 2 = 1 - Real.cos (Real.pi / 5) ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq (Real.pi / 5)]
  rw [hsin_sq, cos_pi_div_five_eq]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- Rational Archimedean lower bound on `N = 5`: `199 / 144 < 4 sin²(π / 5)`. -/
theorem four_mul_sin_pi_div_five_sq_gt :
    (199 / 144 : ℝ) < 4 * Real.sin (Real.pi / 5) ^ 2 := by
  rw [four_mul_sin_pi_div_five_sq_eq]
  have hsqrt : Real.sqrt 5 < 161 / 72 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

end ClockShiftMatrices
