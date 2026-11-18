/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Gauge-Invariant Sign-Magnitude Factorization and Creutz Ratio Additivity

For any real normalized loop trace `w ∈ [-1, 1]`, splitting `w = centerSign w * |w|` decouples
coset modulus fluctuations `cosetMagDefect w = 1 - |w|` from gauge-invariant center-sign flips
`centerFlipDefect w`. Across rectangle scales, multiplicative expectation factorization
`w = s * a * r` induces exact additivity of the logarithmic Creutz ratio without gauge fixing.

## Main results

* `CosetSignMagnitudeCreutz.centerSign_mul_abs`: pointwise sign-magnitude identity.
* `CosetSignMagnitudeCreutz.coset_energy_decomposition`: non-negative defect splitting.
* `CosetSignMagnitudeCreutz.creutzRatio_factorization`: exact 3-factor Creutz additivity.
* `CosetSignMagnitudeCreutz.creutzRatio_pos_of_sign_dominance`: positive full Creutz ratio
  whenever sign-projected Creutz tension dominates modulus and covariance defects.
-/

@[expose] public section

namespace CosetSignMagnitudeCreutz

/-- Gauge-invariant center sign `±1` for a real normalized loop trace `w`. -/
noncomputable def centerSign (w : ℝ) : ℝ :=
  if 0 ≤ w then 1 else -1

/-- Continuous coset modulus defect `1 - |w|`. -/
noncomputable def cosetMagDefect (w : ℝ) : ℝ :=
  1 - |w|

/-- Center-flip topological defect `2 * |w|` when `w < 0`, else `0`. -/
noncomputable def centerFlipDefect (w : ℝ) : ℝ :=
  if w < 0 then 2 * |w| else 0

/-- Logarithmic Creutz ratio `-Real.log (wRR * w11 / w12 ^ 2)`. -/
noncomputable def creutzRatio (wRR w11 w12 : ℝ) : ℝ :=
  -Real.log (wRR * w11 / w12 ^ 2)

/-- Exact sign-magnitude identity `centerSign w * |w| = w`. -/
theorem centerSign_mul_abs (w : ℝ) : centerSign w * |w| = w := by
  unfold centerSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · have hlt : w < 0 := lt_of_not_ge h
    simp [abs_of_neg hlt]

/-- Pointwise non-negative energy splitting `1 - w = cosetMagDefect w + centerFlipDefect w`. -/
theorem coset_energy_decomposition (w : ℝ) :
    1 - w = cosetMagDefect w + centerFlipDefect w := by
  unfold cosetMagDefect centerFlipDefect
  split_ifs with h
  · rw [abs_of_neg h]
    ring
  · have hge : 0 ≤ w := not_lt.mp h
    rw [abs_of_nonneg hge]
    ring

/-- Both coset modulus and center-flip defects are non-negative when `|w| ≤ 1`. -/
theorem coset_defects_nonneg {w : ℝ} (hw : |w| ≤ 1) :
    0 ≤ cosetMagDefect w ∧ 0 ≤ centerFlipDefect w := by
  unfold cosetMagDefect centerFlipDefect
  constructor
  · linarith
  · split_ifs <;> positivity

/-- Exact additivity of the Creutz ratio under three-factor loop decomposition `w = s * a * r`. -/
theorem creutzRatio_factorization
    {sRR s11 s12 aRR a11 a12 rRR r11 r12 : ℝ}
    (hsRR : 0 < sRR) (hs11 : 0 < s11) (hs12 : 0 < s12)
    (haRR : 0 < aRR) (ha11 : 0 < a11) (ha12 : 0 < a12)
    (hrRR : 0 < rRR) (hr11 : 0 < r11) (hr12 : 0 < r12) :
    creutzRatio (sRR * aRR * rRR) (s11 * a11 * r11) (s12 * a12 * r12) =
      creutzRatio sRR s11 s12 + creutzRatio aRR a11 a12 + creutzRatio rRR r11 r12 := by
  unfold creutzRatio
  have hS : 0 < sRR * s11 / s12 ^ 2 := by positivity
  have hA : 0 < aRR * a11 / a12 ^ 2 := by positivity
  have hR : 0 < rRR * r11 / r12 ^ 2 := by positivity
  have hprod :
      (sRR * aRR * rRR) * (s11 * a11 * r11) / (s12 * a12 * r12) ^ 2 =
        (sRR * s11 / s12 ^ 2) * (aRR * a11 / a12 ^ 2) * (rRR * r11 / r12 ^ 2) := by
    field_simp
  rw [hprod, Real.log_mul (mul_pos hS hA).ne' hR.ne', Real.log_mul hS.ne' hA.ne']
  ring

/-- Positivity of the full Creutz ratio whenever sign tension exceeds modulus and covariance
defects. -/
theorem creutzRatio_pos_of_sign_dominance
    {sRR s11 s12 aRR a11 a12 rRR r11 r12 εA εC : ℝ}
    (hsRR : 0 < sRR) (hs11 : 0 < s11) (hs12 : 0 < s12)
    (haRR : 0 < aRR) (ha11 : 0 < a11) (ha12 : 0 < a12)
    (hrRR : 0 < rRR) (hr11 : 0 < r11) (hr12 : 0 < r12)
    (hA : -εA ≤ creutzRatio aRR a11 a12)
    (hR : -εC ≤ creutzRatio rRR r11 r12)
    (hdom : εA + εC < creutzRatio sRR s11 s12) :
    0 < creutzRatio (sRR * aRR * rRR) (s11 * a11 * r11) (s12 * a12 * r12) := by
  rw [creutzRatio_factorization hsRR hs11 hs12 haRR ha11 ha12 hrRR hr11 hr12]
  linarith

end CosetSignMagnitudeCreutz
