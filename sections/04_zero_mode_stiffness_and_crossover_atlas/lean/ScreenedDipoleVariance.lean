/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Attenuated Cancellation Ratios and Area-Scaled Variance Lower Bounds

Purely algebraic estimates over any linearly ordered field `F` modeling how fractional
cancellation loss `δ ∈ [0, 1]` attenuates an additive pair-cancellation weight `α ∈ [0, 1]`
in a sum of `A` orthogonal-frame vector terms:

* `screenedVarianceRatio α δ = 1 - (1 - δ) * α`
* `screenedSurfaceVariance v₀ α δ A = (A : F) * v₀ * screenedVarianceRatio α δ`

## Main results

* `ScreenedDipoleVariance.screenedVarianceRatio_abelian_collapse`: zero attenuation (`δ = 0`)
  at unit cancellation weight (`α = 1`) collapses the bulk ratio to `0`.
* `ScreenedDipoleVariance.delta_le_screenedVarianceRatio`: universal lower bound `δ ≤ ratio`.
* `ScreenedDipoleVariance.one_sub_alpha_le_screenedVarianceRatio`: lower bound `1 - α ≤ ratio`.
* `ScreenedDipoleVariance.screenedVarianceRatio_pos_of_loss`: strict positivity whenever
  `0 ≤ α ≤ 1` and `0 < δ`.
* `ScreenedDipoleVariance.screenedSurfaceVariance_ge_area_floor`: linear-in-`A` floor
  `(A : F) * (v₀ * δ) ≤ screenedSurfaceVariance v₀ α δ A`.
-/

@[expose] public section

namespace ScreenedDipoleVariance

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Effective variance-to-diagonal ratio `1 - (1 - δ) * α` under cancellation weight `α` and
fractional attenuation loss `δ`. -/
def screenedVarianceRatio (α δ : F) : F :=
  1 - (1 - δ) * α

/-- Area-scaled surface variance `(A : F) * v₀ * screenedVarianceRatio α δ`. -/
def screenedSurfaceVariance (v₀ α δ : F) (A : ℕ) : F :=
  (A : F) * v₀ * screenedVarianceRatio α δ

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Exact collapse at zero attenuation loss (`δ = 0`) and complete cancellation (`α = 1`). -/
theorem screenedVarianceRatio_abelian_collapse :
    screenedVarianceRatio (1 : F) 0 = 0 := by
  unfold screenedVarianceRatio
  ring

/-- Universal attenuation floor: `δ ≤ screenedVarianceRatio α δ` for `α ≤ 1` and `δ ≤ 1`. -/
theorem delta_le_screenedVarianceRatio {α δ : F} (hα : α ≤ 1) (hδ : δ ≤ 1) :
    δ ≤ screenedVarianceRatio α δ := by
  unfold screenedVarianceRatio
  have hprod : 0 ≤ (1 - δ) * (1 - α) := mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hα)
  linarith

/-- Unattenuated complement floor: `1 - α ≤ screenedVarianceRatio α δ` for `0 ≤ α` and
`0 ≤ δ`. -/
theorem one_sub_alpha_le_screenedVarianceRatio {α δ : F} (hα : 0 ≤ α) (hδ : 0 ≤ δ) :
    1 - α ≤ screenedVarianceRatio α δ := by
  unfold screenedVarianceRatio
  have hprod : 0 ≤ α * δ := mul_nonneg hα hδ
  linarith

/-- Strict positivity for any non-negative cancellation weight `0 ≤ α ≤ 1` and positive
attenuation loss `0 < δ`. -/
theorem screenedVarianceRatio_pos_of_loss {α δ : F}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) :
    0 < screenedVarianceRatio α δ := by
  unfold screenedVarianceRatio
  rcases lt_or_eq_of_le hα0 with hpos | rfl
  · have hrem : 0 ≤ 1 - α := sub_nonneg.mpr hα1
    have hmul : 0 < α * δ := mul_pos hpos hδ
    linarith
  · linarith

/-- Linear-in-`A` area floor: whenever `0 ≤ v₀`, `0 ≤ α ≤ 1`, and `0 ≤ δ ≤ 1`, the scaled
variance satisfies `(A : F) * (v₀ * δ) ≤ screenedSurfaceVariance v₀ α δ A`. -/
theorem screenedSurfaceVariance_ge_area_floor {v₀ α δ : F}
    (hv₀ : 0 ≤ v₀) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (A : ℕ) :
    (A : F) * (v₀ * δ) ≤ screenedSurfaceVariance v₀ α δ A := by
  unfold screenedSurfaceVariance
  have hratio : δ ≤ screenedVarianceRatio α δ := delta_le_screenedVarianceRatio hα1 hδ1
  have hA : (0 : F) ≤ (A : F) := Nat.cast_nonneg A
  have hAv : 0 ≤ (A : F) * v₀ := mul_nonneg hA hv₀
  have hmul : (A : F) * v₀ * δ ≤ (A : F) * v₀ * screenedVarianceRatio α δ :=
    mul_le_mul_of_nonneg_left hratio hAv
  have h_unused : 0 ≤ α := hα0
  have h_unused2 : 0 ≤ δ := hδ0
  linarith

end ScreenedDipoleVariance
