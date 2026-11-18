/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CubicSinBounds
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-!
# YM-102: Weyl Cubic Collar Rational and Real Integral Certificate

This module evaluates `CubicSinBounds.cubicCollarWeight` at `δ = 1 / 5` and connects it to
the genuine real Weyl Haar integral `(4 / π) * ∫ θ in 0..(1/5), sin θ ^ 2 < 1 / 57`
via `Real.pi_gt_d6`.
-/

namespace YangMillsBlueprint.Certificates

open CubicSinBounds

/-- Exact rational evaluation of the cubic collar weight at `p = 355 / 113` and `δ = 1 / 5`. -/
theorem weyl_collar_rational_eval :
    cubicCollarWeight (355 / 113 : ℚ) (1 / 5) = 452 / 133125 := by
  unfold cubicCollarWeight
  norm_num

/-- The evaluated Weyl collar weight `452 / 133125` is strictly below `1 / 57`. -/
theorem weyl_collar_lt_margin :
    cubicCollarWeight (355 / 113 : ℚ) (1 / 5) < 1 / 57 := by
  rw [weyl_collar_rational_eval]
  norm_num

/-- For any real constant `p ≥ 333 / 106` (which includes `π > 333 / 106`), the cubic collar
weight at `δ = 1 / 5` is strictly below `1 / 57`. -/
theorem weyl_collar_strict_upper_bound_lt_margin {p : ℝ} (hp : (333 / 106 : ℝ) ≤ p) :
    cubicCollarWeight p (1 / 5) < 1 / 57 := by
  have hanti : cubicCollarWeight p (1 / 5) ≤ cubicCollarWeight (333 / 106 : ℝ) (1 / 5) :=
    cubicCollarWeight_anti_left (by norm_num) hp (by norm_num)
  have hnum : cubicCollarWeight (333 / 106 : ℝ) (1 / 5) < 1 / 57 := by
    unfold cubicCollarWeight
    norm_num
  exact lt_of_le_of_lt hanti hnum

/-- End-to-end real calculus certificate: the normalized SU(2) Weyl Haar collar integral
at `δ = 1 / 5` is unconditionally bounded below the all-orders contraction margin `1 / 57`. -/
theorem su2_real_weyl_collar_integral_lt_margin :
    (4 / Real.pi) * (∫ θ in (0 : ℝ)..(1 / 5 : ℝ), Real.sin θ ^ 2) < 1 / 57 := by
  have hpi : (333 / 106 : ℝ) ≤ Real.pi := by
    have h6 := Real.pi_gt_d6
    linarith
  have hint := normalized_sin_sq_integral_le_cubicCollarWeight (δ := (1 / 5 : ℝ)) (by norm_num)
  have hmargin := weyl_collar_strict_upper_bound_lt_margin hpi
  exact lt_of_le_of_lt hint hmargin

end YangMillsBlueprint.Certificates
