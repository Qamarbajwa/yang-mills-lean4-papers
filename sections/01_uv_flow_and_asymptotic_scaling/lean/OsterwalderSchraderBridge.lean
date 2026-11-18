/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Additive Exponential Decay Envelopes and Volume-Scaling Limit Extraction

This file proves non-negativity, separate parameter monotonicity in time and scale, and
asymptotic envelope extraction for additive exponential decay functions
`finiteVolumeCorrelatorBound A Δ t C σ L = A * Real.exp (-(Δ * t)) + C * Real.exp (-(σ * L ^ 2))`.

## Main results

* `OsterwalderSchraderBridge.finiteVolumeCorrelatorBound`: additive exponential envelope.
* `OsterwalderSchraderBridge.finiteVolumeCorrelatorBound_nonneg`: non-negativity.
* `OsterwalderSchraderBridge.finiteVolumeCorrelatorBound_anti_time`: antitone in `t`.
* `OsterwalderSchraderBridge.finiteVolumeCorrelatorBound_anti_volume`: antitone in `0 ≤ L`.
* `OsterwalderSchraderBridge.clustering_extraction_le`: residual `ε` extraction bound.
-/

@[expose] public section

namespace OsterwalderSchraderBridge

/-- Two-term exponential decay envelope combining temporal and Gaussian scale terms. -/
noncomputable def finiteVolumeCorrelatorBound (A Δ t C σ L : ℝ) : ℝ :=
  A * Real.exp (-(Δ * t)) + C * Real.exp (-(σ * L ^ 2))

/-- Non-negativity whenever both amplitude prefactors are non-negative. -/
theorem finiteVolumeCorrelatorBound_nonneg {A Δ t C σ L : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    0 ≤ finiteVolumeCorrelatorBound A Δ t C σ L := by
  unfold finiteVolumeCorrelatorBound
  positivity

/-- Antitone monotonicity in the temporal separation variable `t` for `0 ≤ A` and `0 ≤ Δ`. -/
theorem finiteVolumeCorrelatorBound_anti_time {A Δ t₁ t₂ C σ L : ℝ}
    (hA : 0 ≤ A) (hΔ : 0 ≤ Δ) (ht : t₁ ≤ t₂) :
    finiteVolumeCorrelatorBound A Δ t₂ C σ L ≤
      finiteVolumeCorrelatorBound A Δ t₁ C σ L := by
  unfold finiteVolumeCorrelatorBound
  have hexp : Real.exp (-(Δ * t₂)) ≤ Real.exp (-(Δ * t₁)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  nlinarith

/-- Antitone monotonicity in the scale variable `L ≥ 0` for `0 ≤ C` and `0 ≤ σ`. -/
theorem finiteVolumeCorrelatorBound_anti_volume {A Δ t C σ L₁ L₂ : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) :
    finiteVolumeCorrelatorBound A Δ t C σ L₂ ≤
      finiteVolumeCorrelatorBound A Δ t C σ L₁ := by
  unfold finiteVolumeCorrelatorBound
  have hsq : L₁ ^ 2 ≤ L₂ ^ 2 := by nlinarith
  have hexp : Real.exp (-(σ * L₂ ^ 2)) ≤ Real.exp (-(σ * L₁ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  nlinarith

/-- Residual extraction bound when the Gaussian scale term is bounded above by `ε`. -/
theorem clustering_extraction_le {A Δ t C σ L ε : ℝ}
    (hε : C * Real.exp (-(σ * L ^ 2)) ≤ ε) :
    finiteVolumeCorrelatorBound A Δ t C σ L ≤ A * Real.exp (-(Δ * t)) + ε := by
  unfold finiteVolumeCorrelatorBound
  linarith

end OsterwalderSchraderBridge
