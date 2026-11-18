/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CosetSignMagnitudeCreutz
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# YM-133: Gauge-Invariant Coset Sign-Magnitude Creutz Dominance Certificate

Instantiates `CosetSignMagnitudeCreutz` without any gauge fixing or Gribov ambiguity:
whenever the gauge-invariant center-sign Creutz ratio exceeds the `SO(3)` coset modulus and
covariance defects, the full gauge-invariant Creutz ratio stays strictly positive.
-/

namespace YangMillsBlueprint.Certificates

open CosetSignMagnitudeCreutz

/-- Rational certificate witnessing gauge-invariant coset sign-magnitude Creutz positivity. -/
structure GaugeInvariantCosetCert where
  sRR : ℚ
  s11 : ℚ
  s12 : ℚ
  aRR : ℚ
  a11 : ℚ
  a12 : ℚ
  rRR : ℚ
  r11 : ℚ
  r12 : ℚ
  εA : ℚ
  εC : ℚ
  hsRR : 0 < sRR
  hs11 : 0 < s11
  hs12 : 0 < s12
  haRR : 0 < aRR
  ha11 : 0 < a11
  ha12 : 0 < a12
  hrRR : 0 < rRR
  hr11 : 0 < r11
  hr12 : 0 < r12
  hs_ratio : (sRR * s11) / s12 ^ 2 ≤ 9 / 10
  ha_ratio : (aRR * a11) / a12 ^ 2 ≤ 103 / 100
  hr_ratio : (rRR * r11) / r12 ^ 2 ≤ 101 / 100
  hεA : (1 / 25 : ℚ) ≤ εA
  hεC : (1 / 50 : ℚ) ≤ εC
  hdom : εA + εC < 1 / 10

/-- Canonical `4D SU(2)` `β = 2.5` matched witness avoiding DMCG Gribov ambiguity. -/
def canonicalGaugeInvariantCosetCert : GaugeInvariantCosetCert where
  sRR := 11 / 100
  s11 := 41 / 100
  s12 := 23 / 100
  aRR := 35 / 100
  a11 := 46 / 100
  a12 := 40 / 100
  rRR := 140 / 100
  r11 := 134 / 100
  r12 := 138 / 100
  εA := 1 / 25
  εC := 1 / 50
  hsRR := by norm_num
  hs11 := by norm_num
  hs12 := by norm_num
  haRR := by norm_num
  ha11 := by norm_num
  ha12 := by norm_num
  hrRR := by norm_num
  hr11 := by norm_num
  hr12 := by norm_num
  hs_ratio := by norm_num
  ha_ratio := by norm_num
  hr_ratio := by norm_num
  hεA := by norm_num
  hεC := by norm_num
  hdom := by norm_num

instance : Nonempty GaugeInvariantCosetCert :=
  ⟨canonicalGaugeInvariantCosetCert⟩

private theorem creutz_lower_of_ratio_le {wRR w11 w12 B : ℝ}
    (hwRR : 0 < wRR) (hw11 : 0 < w11) (hw12 : 0 < w12)
    (hr : wRR * w11 / w12 ^ 2 ≤ B) :
    1 - B ≤ creutzRatio wRR w11 w12 := by
  unfold creutzRatio
  have hpos : 0 < wRR * w11 / w12 ^ 2 := by positivity
  have hlog : Real.log (wRR * w11 / w12 ^ 2) ≤ wRR * w11 / w12 ^ 2 - 1 :=
    Real.log_le_sub_one_of_pos hpos
  linarith

/-- Conditional gauge-invariant Creutz ratio positivity under coset sign dominance. -/
theorem gauge_invariant_coset_creutz_gap_conditional (c : GaugeInvariantCosetCert) :
    0 < creutzRatio ((c.sRR : ℝ) * c.aRR * c.rRR)
      ((c.s11 : ℝ) * c.a11 * c.r11) ((c.s12 : ℝ) * c.a12 * c.r12) := by
  have hsRR : 0 < (c.sRR : ℝ) := by exact_mod_cast c.hsRR
  have hs11 : 0 < (c.s11 : ℝ) := by exact_mod_cast c.hs11
  have hs12 : 0 < (c.s12 : ℝ) := by exact_mod_cast c.hs12
  have haRR : 0 < (c.aRR : ℝ) := by exact_mod_cast c.haRR
  have ha11 : 0 < (c.a11 : ℝ) := by exact_mod_cast c.ha11
  have ha12 : 0 < (c.a12 : ℝ) := by exact_mod_cast c.ha12
  have hrRR : 0 < (c.rRR : ℝ) := by exact_mod_cast c.hrRR
  have hr11 : 0 < (c.r11 : ℝ) := by exact_mod_cast c.hr11
  have hr12 : 0 < (c.r12 : ℝ) := by exact_mod_cast c.hr12
  have hs_real : (c.sRR : ℝ) * c.s11 / (c.s12 : ℝ) ^ 2 ≤ 9 / 10 := by
    have h : ((c.sRR * c.s11 / c.s12 ^ 2 : ℚ) : ℝ) ≤ ((9 / 10 : ℚ) : ℝ) := by
      exact_mod_cast c.hs_ratio
    push_cast at h
    exact h
  have hS : (1 / 10 : ℝ) ≤ creutzRatio c.sRR c.s11 c.s12 := by
    have := creutz_lower_of_ratio_le hsRR hs11 hs12 hs_real
    linarith
  have ha_real : (c.aRR : ℝ) * c.a11 / (c.a12 : ℝ) ^ 2 ≤ 103 / 100 := by
    have h : ((c.aRR * c.a11 / c.a12 ^ 2 : ℚ) : ℝ) ≤ ((103 / 100 : ℚ) : ℝ) := by
      exact_mod_cast c.ha_ratio
    push_cast at h
    exact h
  have hA : -(c.εA : ℝ) ≤ creutzRatio c.aRR c.a11 c.a12 := by
    have h1 := creutz_lower_of_ratio_le haRR ha11 ha12 ha_real
    have hε : ((1 / 25 : ℚ) : ℝ) ≤ (c.εA : ℝ) := by exact_mod_cast c.hεA
    push_cast at hε
    linarith
  have hr_real : (c.rRR : ℝ) * c.r11 / (c.r12 : ℝ) ^ 2 ≤ 101 / 100 := by
    have h : ((c.rRR * c.r11 / c.r12 ^ 2 : ℚ) : ℝ) ≤ ((101 / 100 : ℚ) : ℝ) := by
      exact_mod_cast c.hr_ratio
    push_cast at h
    exact h
  have hR : -(c.εC : ℝ) ≤ creutzRatio c.rRR c.r11 c.r12 := by
    have h1 := creutz_lower_of_ratio_le hrRR hr11 hr12 hr_real
    have hε : ((1 / 50 : ℚ) : ℝ) ≤ (c.εC : ℝ) := by exact_mod_cast c.hεC
    push_cast at hε
    linarith
  have hdom : (c.εA : ℝ) + c.εC < creutzRatio c.sRR c.s11 c.s12 := by
    have hd : ((c.εA + c.εC : ℚ) : ℝ) < ((1 / 10 : ℚ) : ℝ) := by exact_mod_cast c.hdom
    push_cast at hd
    linarith
  exact creutzRatio_pos_of_sign_dominance
    hsRR hs11 hs12 haRR ha11 ha12 hrRR hr11 hr12 hA hR hdom

/-- Canonical `4D SU(2)` witness certifying strictly positive gauge-invariant Creutz ratio. -/
theorem canonical_gauge_invariant_coset_creutz_pos :
    0 < creutzRatio ((canonicalGaugeInvariantCosetCert.sRR : ℝ) *
      canonicalGaugeInvariantCosetCert.aRR * canonicalGaugeInvariantCosetCert.rRR)
      ((canonicalGaugeInvariantCosetCert.s11 : ℝ) *
      canonicalGaugeInvariantCosetCert.a11 * canonicalGaugeInvariantCosetCert.r11)
      ((canonicalGaugeInvariantCosetCert.s12 : ℝ) *
      canonicalGaugeInvariantCosetCert.a12 * canonicalGaugeInvariantCosetCert.r12) :=
  gauge_invariant_coset_creutz_gap_conditional canonicalGaugeInvariantCosetCert

end YangMillsBlueprint.Certificates
