/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Vortex Flux-Spreading Action Decay and Critical Blocking Thresholds

This module formalizes the `1 / W ^ 2` classical action dilution of distributing a fixed
angular flux `Φ` evenly across `W ^ 2` cells (`W ^ 2 * β * (1 - Real.cos (Φ / W ^ 2))`),
showing that fixed-coupling spreading drives the action per unit cross-section below any `ε > 0`
for `W ^ 2 > β * Φ ^ 2 / (2 * ε)` unless effective coupling grows along scale decimation.

## Main results

* `VortexSpreadingBound.spreadTrigCost`: `W ^ 2 * (β * (1 - Real.cos (Φ / W ^ 2)))`.
* `VortexSpreadingBound.one_sub_cos_le_sq_div_two`: `1 - Real.cos x ≤ x ^ 2 / 2`.
* `VortexSpreadingBound.spreadTrigCost_le`: exact upper bound `(β * Φ ^ 2) / (2 * W ^ 2)`.
* `VortexSpreadingBound.spreadTrigCost_lt_of_cutoff`: strict threshold dilution `< ε`.
-/

@[expose] public section

namespace VortexSpreadingBound

/-- Elementary cosine bound: `1 - Real.cos x ≤ x ^ 2 / 2` via `Real.sin_sq_le_sq`. -/
theorem one_sub_cos_le_sq_div_two (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hcos : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (x / 2)
    have h2 : 2 * (x / 2) = x := by ring
    have h3 := Real.sin_sq_add_cos_sq (x / 2)
    rw [h2] at h1
    linarith
  have hsin : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := Real.sin_sq_le_sq (x := x / 2)
  rw [hcos]
  nlinarith

/-- Classical cosine action summed across `W ^ 2` plaquettes carrying equal flux `Φ / W ^ 2`. -/
noncomputable def spreadTrigCost (β Φ : ℝ) (W : ℕ) : ℝ :=
  (W : ℝ) ^ 2 * (β * (1 - Real.cos (Φ / (W : ℝ) ^ 2)))

/-- Exact inverse-square upper bound: `spreadTrigCost β Φ W ≤ (β * Φ ^ 2) / (2 * W ^ 2)`
for `0 ≤ β` and `0 < W`. -/
theorem spreadTrigCost_le {β Φ : ℝ} {W : ℕ} (hβ : 0 ≤ β) (hW : 0 < W) :
    spreadTrigCost β Φ W ≤ (β * Φ ^ 2) / (2 * (W : ℝ) ^ 2) := by
  unfold spreadTrigCost
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hWne : (W : ℝ) ≠ 0 := ne_of_gt hWpos
  have hcos := one_sub_cos_le_sq_div_two (Φ / (W : ℝ) ^ 2)
  have h1 : (W : ℝ) ^ 2 * (β * (1 - Real.cos (Φ / (W : ℝ) ^ 2))) ≤
      (W : ℝ) ^ 2 * (β * ((Φ / (W : ℝ) ^ 2) ^ 2 / 2)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hcos hβ
  have h2 : (W : ℝ) ^ 2 * (β * ((Φ / (W : ℝ) ^ 2) ^ 2 / 2)) =
      (β * Φ ^ 2) / (2 * (W : ℝ) ^ 2) := by
    field_simp
  linarith

/-- Spreading dilution threshold: whenever `2 * ε * W ^ 2 > β * Φ ^ 2`, the total spread
classical cost drops strictly below `ε`. -/
theorem spreadTrigCost_lt_of_cutoff {β Φ ε : ℝ} {W : ℕ}
    (hβ : 0 ≤ β) (hW : 0 < W) (hcut : β * Φ ^ 2 < 2 * ε * (W : ℝ) ^ 2) :
    spreadTrigCost β Φ W < ε := by
  have hle := spreadTrigCost_le (Φ := Φ) hβ hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hden : (0 : ℝ) < 2 * (W : ℝ) ^ 2 := by positivity
  have hdiv : (β * Φ ^ 2) / (2 * (W : ℝ) ^ 2) < ε := by
    rw [div_lt_iff₀ hden]
    linarith
  exact lt_of_le_of_lt hle hdiv

end VortexSpreadingBound
