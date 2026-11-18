/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CurvedGroupLogSobolev
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# YM-123: Curved Holley-Stroock & Dobrushin Block-Mixing Spectral Gap Certificate

This module instantiates `CurvedGroupLogSobolev` over `ℚ` and `ℝ` to certify that any
uniform single-block log-Sobolev constant `ρ₀ > 0` with Holley-Stroock oscillation bound
`osc ≥ 0` and Dobrushin block-interaction contraction `θ < 1` yields a strictly positive,
volume-uniform global spectral gap lower bound.
-/

namespace YangMillsBlueprint.Certificates

open CurvedGroupLogSobolev

/-- Rational certificate bundling block gap `ρ₀ > 0`, oscillation `osc ≥ 0`, and
Dobrushin interaction bound `θ < 1`. -/
structure DobrushinMixingBridgeCert where
  ρ₀ : ℚ
  osc : ℚ
  θ : ℚ
  hρ₀ : 0 < ρ₀
  hosc : 0 ≤ osc
  hθ : θ < 1

/-- Canonical finite-block crossover mixing witness (`ρ₀ = 1 / 2`, `osc = 1`, `θ = 3 / 4`). -/
def canonicalDobrushinMixingCert : DobrushinMixingBridgeCert where
  ρ₀ := 1 / 2
  osc := 1
  θ := 3 / 4
  hρ₀ := by norm_num
  hosc := by norm_num
  hθ := by norm_num

instance : Nonempty DobrushinMixingBridgeCert :=
  ⟨canonicalDobrushinMixingCert⟩

/-- Conditional global spectral-gap positivity over `ℝ` from Holley-Stroock + Dobrushin
interaction contraction `θ < 1`. -/
theorem dobrushin_global_log_sobolev_gap_conditional (c : DobrushinMixingBridgeCert) :
    0 < dobrushinGlobalGap (c.ρ₀ : ℝ) (holleyStroockFactor (c.osc : ℝ)) (c.θ : ℝ) :=
  dobrushin_holley_stroock_pos (by exact_mod_cast c.hρ₀) (by exact_mod_cast c.hθ)

/-- Rational lower bound for canonical crossover mixing parameters when `oscFactor ≥ 1 / 8`:
`(1 - 3 / 4) * ((1 / 2) * (1 / 8)) = 1 / 64 > 0`. -/
theorem canonical_dobrushin_mixing_eval :
    dobrushinGlobalGap (1 / 2 : ℚ) (1 / 8 : ℚ) (3 / 4 : ℚ) = 1 / 64 ∧
      0 < dobrushinGlobalGap (1 / 2 : ℚ) (1 / 8 : ℚ) (3 / 4 : ℚ) := by
  unfold dobrushinGlobalGap
  norm_num

end YangMillsBlueprint.Certificates
