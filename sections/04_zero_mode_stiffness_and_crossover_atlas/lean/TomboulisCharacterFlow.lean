/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Quartic Character-Weight Contraction and Inductive Threshold Amplification

This file analyzes the nonlinear discrete recurrence `w ↦ μ * w ^ 4` modeling multi-plaquette
character-ratio decimation against an entropy factor `μ ≥ 0`. Whenever the initial weight
satisfies `0 ≤ w₀ ≤ r` with `μ * r ^ 3 ≤ η ≤ 1`, the sequence contracts geometrically as
`w k ≤ η ^ k * w₀` for all `k : ℕ`, despite `μ > 1`.

## Main results

* `TomboulisCharacterFlow.characterWeightStep`: quartic decimation map `μ * w ^ 4`.
* `TomboulisCharacterFlow.characterWeightStep_le_mul`: one-step contraction `≤ η * w`.
* `TomboulisCharacterFlow.characterTrajectory_le_geom`: inductive contraction `w k ≤ η ^ k * w 0`.
-/

@[expose] public section

namespace TomboulisCharacterFlow

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Quartic character-ratio decimation step `μ * w ^ 4`. -/
def characterWeightStep (μ w : F) : F :=
  μ * w ^ 4

/-- One-step dominance: if `0 ≤ μ`, `0 ≤ w ≤ r`, and `μ * r ^ 3 ≤ η`, then
`μ * w ^ 4 ≤ η * w`. -/
theorem characterWeightStep_le_mul {μ w r η : F}
    (hμ : 0 ≤ μ) (hw0 : 0 ≤ w) (hwr : w ≤ r) (hη : μ * r ^ 3 ≤ η) :
    characterWeightStep μ w ≤ η * w := by
  unfold characterWeightStep
  have hw3 : w ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hw0 hwr 3
  have h1 : μ * w ^ 3 ≤ μ * r ^ 3 := mul_le_mul_of_nonneg_left hw3 hμ
  have h2 : μ * w ^ 3 ≤ η := le_trans h1 hη
  have h3 : (μ * w ^ 3) * w ≤ η * w := mul_le_mul_of_nonneg_right h2 hw0
  have h4 : μ * w ^ 4 = (μ * w ^ 3) * w := by ring
  rw [h4]
  exact h3

/-- Inductive geometric decay across all scales `k : ℕ`: if `0 ≤ w k`,
`w (k + 1) ≤ μ * (w k) ^ 4`, `0 ≤ w 0 ≤ r`, and `μ * r ^ 3 ≤ η ≤ 1`, then
`w k ≤ η ^ k * w 0` for every `k : ℕ`. -/
theorem characterTrajectory_le_geom {μ r η : F} {w : ℕ → F}
    (hμ : 0 ≤ μ) (hr : w 0 ≤ r)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hcrit : μ * r ^ 3 ≤ η)
    (hw0 : ∀ k : ℕ, 0 ≤ w k)
    (hstep : ∀ k : ℕ, w (k + 1) ≤ characterWeightStep μ (w k)) :
    ∀ k : ℕ, w k ≤ η ^ k * w 0 := by
  intro k
  induction k with
  | zero =>
    simp
  | succ m hm =>
    have hηpow : 0 ≤ η ^ m := pow_nonneg hη0 m
    have hηm1 : η ^ m ≤ 1 := pow_le_one₀ hη0 hη1
    have hwm_r : w m ≤ r := by
      have h1 : η ^ m * w 0 ≤ 1 * w 0 := mul_le_mul_of_nonneg_right hηm1 (hw0 0)
      linarith
    have hstep_m := characterWeightStep_le_mul hμ (hw0 m) hwm_r hcrit
    have hdec : w (m + 1) ≤ η * w m := le_trans (hstep m) hstep_m
    have hmul : η * w m ≤ η * (η ^ m * w 0) := mul_le_mul_of_nonneg_left hm hη0
    have hpow : η * (η ^ m * w 0) = η ^ (m + 1) * w 0 := by
      rw [pow_succ']
      ring
    linarith

end OrderedField

end TomboulisCharacterFlow
