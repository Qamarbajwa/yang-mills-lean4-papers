/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Symmetric Four-Plane Shear Bijections and Quadratic-Rank Spectral Scaling

This module studies unimodular `2 × 2` shear twists `(m₁, m₂) ↦ (m₁, k * m₁ + m₂)` over
`ZMod N × ZMod N` together with quadratic-rank trigonometric lower bounds `16 / N ≤ 4 sin²(π / L)`
when `N = L ^ 2` (`2 ≤ L`).

## Main results

* `TEKFourPlaneLattice.shearMap`: unimodular integer shear on `ZMod N × ZMod N`.
* `TEKFourPlaneLattice.shearMap_bijective`: bijectivity for any `N` and `k`.
* `TEKFourPlaneLattice.shearMap_eq_zero_iff`: triviality of the kernel.
* `TEKFourPlaneLattice.quadratic_rank_gap_le_four_mul_sin_sq`:
  `16 / (N : ℝ) ≤ 4 * Real.sin (Real.pi / L) ^ 2` whenever `N = L ^ 2` and `2 ≤ L`.
* `TEKFourPlaneLattice.four_plane_additive_gap_le`:
  `64 / (N : ℝ) ≤ 4 * (4 * Real.sin (Real.pi / L) ^ 2)` across four orthogonal planes.
-/

@[expose] public section

namespace TEKFourPlaneLattice

section ModularShear

/-- Unimodular modular shear map on `ZMod N × ZMod N`. -/
def shearMap (N : ℕ) (k : ℕ) (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (p.1, (k : ZMod N) * p.1 + p.2)

/-- Explicit two-sided inverse equivalence for `shearMap N k`. -/
def shearEquiv (N k : ℕ) : (ZMod N × ZMod N) ≃ (ZMod N × ZMod N) where
  toFun := shearMap N k
  invFun q := (q.1, q.2 - (k : ZMod N) * q.1)
  left_inv p := by
    ext <;> simp [shearMap]
  right_inv q := by
    ext <;> simp [shearMap]

/-- `shearMap N k` is bijective for every modulus `N` and shift parameter `k`. -/
theorem shearMap_bijective (N k : ℕ) : Function.Bijective (shearMap N k) :=
  (shearEquiv N k).bijective

/-- Trivial kernel: `shearMap N k p = (0, 0) ↔ p = (0, 0)`. -/
theorem shearMap_eq_zero_iff (N k : ℕ) (p : ZMod N × ZMod N) :
    shearMap N k p = (0, 0) ↔ p = (0, 0) := by
  constructor
  · intro h
    have hp1 : p.1 = 0 := congrArg Prod.fst h
    have hp2 : (k : ZMod N) * p.1 + p.2 = 0 := congrArg Prod.snd h
    rw [hp1, mul_zero, zero_add] at hp2
    exact Prod.ext hp1 hp2
  · intro h
    subst h
    simp [shearMap]

end ModularShear

section QuadraticRankGap

/-- Concavity Jordan bound `(2 / π) * x ≤ sin x` for `0 ≤ x ≤ π / 2`. -/
theorem two_div_pi_mul_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    (2 / Real.pi) * x ≤ Real.sin x := by
  have hpi : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hx_mem : x ∈ Set.Icc 0 (Real.pi / 2) := ⟨hx0, hxpi⟩
  have ha0 : 0 < Real.pi / 2 := by positivity
  have ht1 : 0 ≤ x / (Real.pi / 2) := div_nonneg hx0 ha0.le
  have ht0 : 0 ≤ 1 - x / (Real.pi / 2) := sub_nonneg.mpr ((div_le_one ha0).mpr hxpi)
  have hsum : (1 - x / (Real.pi / 2)) + x / (Real.pi / 2) = 1 := by ring
  have hcomb : (1 - x / (Real.pi / 2)) • (0 : ℝ) + (x / (Real.pi / 2)) • (Real.pi / 2) = x := by
    simp [smul_eq_mul, ha0.ne']
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2 h0 hpi ht0 ht1 hsum
  rw [hcomb, smul_eq_mul, smul_eq_mul, Real.sin_zero, Real.sin_pi_div_two,
    mul_zero, zero_add] at hconc
  linarith [show (x / (Real.pi / 2)) * 1 = (2 / Real.pi) * x by ring]

/-- Under quadratic rank scaling `N = L ^ 2` with `2 ≤ L`, the single-plane spectral gap
is bounded below by `16 / N` (rather than `16 / N ^ 2`). -/
theorem quadratic_rank_gap_le_four_mul_sin_sq {L N : ℕ} (hL : 2 ≤ L) (hN : N = L ^ 2) :
    16 / (N : ℝ) ≤ 4 * Real.sin (Real.pi / L) ^ 2 := by
  have hL_real : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL_pos : (0 : ℝ) < (L : ℝ) := by linarith
  have hx0 : 0 ≤ Real.pi / L := div_nonneg Real.pi_pos.le hL_pos.le
  have hxpi : Real.pi / L ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hL_real
  have hj := two_div_pi_mul_le_sin hx0 hxpi
  have hsimp : (2 / Real.pi) * (Real.pi / L) = 2 / L := by
    field_simp [Real.pi_ne_zero, hL_pos.ne']
  rw [hsimp] at hj
  have hsq : (2 / (L : ℝ)) ^ 2 ≤ Real.sin (Real.pi / L) ^ 2 :=
    sq_le_sq' (by linarith [show (0 : ℝ) ≤ 2 / (L : ℝ) by positivity]) hj
  have hN_cast : (N : ℝ) = (L : ℝ) ^ 2 := by exact_mod_cast hN
  rw [hN_cast]
  linarith [show 4 * (2 / (L : ℝ)) ^ 2 = 16 / (L : ℝ) ^ 2 by ring]

/-- Four-plane symmetric additive spectral lower bound `64 / N`. -/
theorem four_plane_additive_gap_le {L N : ℕ} (hL : 2 ≤ L) (hN : N = L ^ 2) :
    64 / (N : ℝ) ≤ 4 * (4 * Real.sin (Real.pi / L) ^ 2) := by
  have h := quadratic_rank_gap_le_four_mul_sin_sq hL hN
  linarith [show 4 * (16 / (N : ℝ)) = 64 / (N : ℝ) by ring]

end QuadraticRankGap

end TEKFourPlaneLattice
