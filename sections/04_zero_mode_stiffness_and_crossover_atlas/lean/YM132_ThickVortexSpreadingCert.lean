/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.VortexSpreadingBound
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# YM-132: Thick-Vortex Action Spreading & RG Stopping Scale Certificate

This module instantiates `VortexSpreadingBound` over `ℝ` at `β = 4`, `Φ = 3.15` (`> π`), and
`W = 16`, certifying that spreading a single quantum of magnetic flux uniformly across `16 ^ 2`
fine plaquettes reduces the classical action cost strictly below `1 / 10` (`< 1 / 6`), proving
that weak-coupling spreading cannot be ruled out without re-blocking into `g(W a) ^ 2 ~ 1`.
-/

namespace YangMillsBlueprint.Certificates

open VortexSpreadingBound

/-- Certificate bundling bare coupling `β ≥ 0`, flux bound `Φ`, thickness `W > 0`, and
dilution threshold `ε` satisfying `β * Φ ^ 2 < 2 * ε * W ^ 2`. -/
structure ThickVortexSpreadingCert where
  β : ℚ
  Φ : ℚ
  ε : ℚ
  W : ℕ
  hβ : 0 ≤ β
  hW : 0 < W
  hcut : β * Φ ^ 2 < 2 * ε * (W : ℚ) ^ 2

/-- Canonical spreading witness (`β = 4`, `Φ = 315 / 100`, `ε = 1 / 10`, `W = 16`). -/
def canonicalThickVortexSpreadingCert : ThickVortexSpreadingCert where
  β := 4
  Φ := 315 / 100
  ε := 1 / 10
  W := 16
  hβ := by norm_num
  hW := by decide
  hcut := by norm_num

instance : Nonempty ThickVortexSpreadingCert :=
  ⟨canonicalThickVortexSpreadingCert⟩

/-- Conditional real trigonometric spreading bound over `ℝ`. -/
theorem thick_vortex_spread_cost_lt_conditional (c : ThickVortexSpreadingCert) :
    spreadTrigCost (c.β : ℝ) (c.Φ : ℝ) c.W < (c.ε : ℝ) :=
  spreadTrigCost_lt_of_cutoff (by exact_mod_cast c.hβ) c.hW (by exact_mod_cast c.hcut)

/-- Canonical witness: spreading `Φ = 3.15` over `16 ^ 2 = 256` plaquettes at `β = 4`
reduces total classical action cost strictly below `1 / 10`. -/
theorem canonical_thick_vortex_w16_lt_tenth :
    spreadTrigCost (4 : ℝ) ((315 / 100 : ℚ) : ℝ) 16 < (1 / 10 : ℝ) := by
  simpa [canonicalThickVortexSpreadingCert] using
    thick_vortex_spread_cost_lt_conditional canonicalThickVortexSpreadingCert

end YangMillsBlueprint.Certificates
