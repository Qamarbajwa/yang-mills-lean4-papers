/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.NonAbelianCommutatorStiffness
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-105: Non-Abelian Zero-Mode Commutator Stiffness Certificate

This module instantiates `NonAbelianCommutatorStiffness` at the crossover coupling
`g_k5² = 24 / 41` with three mutually orthogonal `su(2)` color vectors, proving quartic
restoring energy positivity at zero momentum.
-/

namespace YangMillsBlueprint.Certificates

open NonAbelianCommutatorStiffness

/-- Certificate bundling the step-`k=5` coupling `g_sq_k5 = 24 / 41`, amplitude threshold
`a > 0`, and three mutually orthogonal zero-momentum `su(2)` color vectors. -/
structure ZeroModeStiffnessCert where
  g_sq_k5 : ℚ
  h_g_sq_k5 : g_sq_k5 = 24 / 41
  a : ℚ
  ha : 0 < a
  u : Vec3 ℚ
  v : Vec3 ℚ
  w : Vec3 ℚ
  huv : dot u v = 0
  hvw : dot v w = 0
  hwu : dot w u = 0
  hu : a ≤ normSq u
  hv : a ≤ normSq v
  hw : a ≤ normSq w

/-- Canonical zero-mode stiffness certificate with standard orthonormal basis vectors in `ℚ³`. -/
def canonicalZeroModeCert : ZeroModeStiffnessCert where
  g_sq_k5 := 24 / 41
  h_g_sq_k5 := rfl
  a := 1
  ha := by norm_num
  u := ⟨1, 0, 0⟩
  v := ⟨0, 1, 0⟩
  w := ⟨0, 0, 1⟩
  huv := by unfold dot; norm_num
  hvw := by unfold dot; norm_num
  hwu := by unfold dot; norm_num
  hu := by unfold normSq dot; norm_num
  hv := by unfold normSq dot; norm_num
  hw := by unfold normSq dot; norm_num

instance : Nonempty ZeroModeStiffnessCert :=
  ⟨canonicalZeroModeCert⟩

/-- Conditional quartic stiffness positivity: for any admissible orthogonal triad of amplitude
at least `a > 0`, the quartic commutator energy is bounded below by `3 * a ^ 2` and is
strictly positive. -/
theorem su2_zero_mode_quartic_stiffness_pos_conditional (cert : ZeroModeStiffnessCert) :
    3 * cert.a ^ 2 ≤ triadQuarticEnergy cert.u cert.v cert.w ∧
      0 < triadQuarticEnergy cert.u cert.v cert.w := by
  have hge := triadQuarticEnergy_ge_three_mul_sq cert.ha.le
    cert.huv cert.hvw cert.hwu cert.hu cert.hv cert.hw
  have ha_sq : 0 < 3 * cert.a ^ 2 := by
    have := mul_pos cert.ha cert.ha
    linarith
  exact ⟨hge, lt_of_lt_of_le ha_sq hge⟩

/-- Exact evaluation of the canonical zero-mode quartic triad energy to `3`. -/
theorem canonical_zero_mode_energy_eq_three :
    triadQuarticEnergy canonicalZeroModeCert.u canonicalZeroModeCert.v
      canonicalZeroModeCert.w = 3 := by
  unfold canonicalZeroModeCert triadQuarticEnergy normSq cross dot
  norm_num

end YangMillsBlueprint.Certificates
