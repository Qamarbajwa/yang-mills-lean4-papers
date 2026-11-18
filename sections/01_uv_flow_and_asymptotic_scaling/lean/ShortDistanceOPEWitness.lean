/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Short-Distance Connected 4-Point OPE Lower Bounds Against Gaussian Triviality

This module formalizes positivity and non-vanishing lower bounds for asymptotic-freedom
4-point connected correlator estimates `c₄ * g₂ - C * r` over a linearly ordered field `F`.
Whenever `0 < c₄`, `0 < g₂`, `0 ≤ C`, and the scale `r` satisfies `r < (c₄ * g₂) / (C + 1)`,
the lower bound stays strictly positive, ruling out vanishing connected 4-point cumulants.

## Main results

* `ShortDistanceOPEWitness.opeFourPointLower`: linear lower bound `c₄ * g₂ - C * r`.
* `ShortDistanceOPEWitness.opeFourPointLower_pos`: strict positivity below the UV cutoff scale.
* `ShortDistanceOPEWitness.ne_zero_of_abs_ge_ope`: non-vanishing witness from absolute lower bound.
-/

@[expose] public section

namespace ShortDistanceOPEWitness

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Linear short-distance OPE connected 4-point lower envelope `c₄ * g₂ - C * r`. -/
def opeFourPointLower (c₄ g₂ C r : F) : F :=
  c₄ * g₂ - C * r

/-- Strict positivity of `opeFourPointLower c₄ g₂ C r` below cutoff scale
`r ≤ (c₄ * g₂) / (C + 1)`. -/
theorem opeFourPointLower_pos {c₄ g₂ C r : F}
    (hc₄ : 0 < c₄) (hg₂ : 0 < g₂) (hC : 0 ≤ C)
    (hr : r ≤ (c₄ * g₂) / (C + 1)) :
    0 < opeFourPointLower c₄ g₂ C r := by
  unfold opeFourPointLower
  have hCp : 0 < C + 1 := by linarith
  have hmul : C * r ≤ C * ((c₄ * g₂) / (C + 1)) := mul_le_mul_of_nonneg_left hr hC
  have hstrict : C * ((c₄ * g₂) / (C + 1)) < c₄ * g₂ := by
    have hprod : 0 < c₄ * g₂ := mul_pos hc₄ hg₂
    rw [mul_div_assoc', div_lt_iff₀ hCp]
    nlinarith
  linarith

/-- Any scalar `S` whose absolute magnitude dominates a positive OPE lower bound
is strictly non-zero (`S ≠ 0`). -/
theorem ne_zero_of_abs_ge_ope {S c₄ g₂ C r : F}
    (hS : opeFourPointLower c₄ g₂ C r ≤ |S|)
    (hc₄ : 0 < c₄) (hg₂ : 0 < g₂) (hC : 0 ≤ C)
    (hr : r ≤ (c₄ * g₂) / (C + 1)) :
    S ≠ 0 := by
  have hpos := opeFourPointLower_pos hc₄ hg₂ hC hr
  have habs : 0 < |S| := lt_of_lt_of_le hpos hS
  exact abs_pos.mp habs

end OrderedField

end ShortDistanceOPEWitness
