/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.ExponentialAreaScreening
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# YM-109: Peierls-Tomboulis Center-Vortex Area-Law Screening Certificate

This module instantiates `ExponentialAreaScreening` to certify that for positive electric
string tension `σ > 0` and box length `L > 0`, the quartic-weighted twist free-energy
defect decays faster than `27 / (σ ^ 3 * L ^ 2)` over `ℝ`.
-/

namespace YangMillsBlueprint.Certificates

open ExponentialAreaScreening

/-- Certificate bundling electric string tension `σ > 0`, torus box length `L > 0`,
and upper target threshold `ε ≥ 27 / (σ ^ 3 * L ^ 2)`. -/
structure VortexAreaScreeningCert where
  σ : ℚ
  hσ : 0 < σ
  L : ℚ
  hL : 0 < L
  ε : ℚ
  hε : 27 / (σ ^ 3 * L ^ 2) ≤ ε

/-- Canonical Peierls-Tomboulis screening certificate (`σ = 1, L = 10, ε = 27 / 100`). -/
def canonicalVortexScreeningCert : VortexAreaScreeningCert where
  σ := 1
  hσ := by norm_num
  L := 10
  hL := by norm_num
  ε := 27 / 100
  hε := by norm_num

instance : Nonempty VortexAreaScreeningCert :=
  ⟨canonicalVortexScreeningCert⟩

/-- Conditional real thermodynamic twist decoupling bound: for any admissible screening
certificate `c`, the quartic-weighted exponential twist defect is bounded above by `c.ε`. -/
theorem vortex_free_energy_defect_le_real (c : VortexAreaScreeningCert) :
    (c.L : ℝ) ^ 4 * Real.exp (-((c.σ : ℝ) * (c.L : ℝ) ^ 2)) ≤ (c.ε : ℝ) := by
  have hσR : (0 : ℝ) < (c.σ : ℝ) := by exact_mod_cast c.hσ
  have hLR : (0 : ℝ) < (c.L : ℝ) := by exact_mod_cast c.hL
  have h_bound := quartic_mul_exp_neg_sq_le hσR hLR
  have hεR : (27 : ℝ) / ((c.σ : ℝ) ^ 3 * (c.L : ℝ) ^ 2) ≤ (c.ε : ℝ) := by
    exact_mod_cast c.hε
  exact le_trans h_bound hεR

/-- Canonical vortex screening certification at `σ = 1`, `L = 10`:
`10 ^ 4 * exp(-(1 * 10 ^ 2)) ≤ 27 / 100`. -/
theorem canonical_vortex_defect_lt_one :
    (10 : ℝ) ^ 4 * Real.exp (-((1 : ℝ) * 10 ^ 2)) ≤ 27 / 100 := by
  have h := vortex_free_energy_defect_le_real canonicalVortexScreeningCert
  simpa [canonicalVortexScreeningCert] using h

end YangMillsBlueprint.Certificates
