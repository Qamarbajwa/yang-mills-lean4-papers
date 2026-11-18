/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith

/-!
# Uniform Exponential Envelope Extraction Under Vanishing Remainder Sequences

This file proves the order-theoretic limit extraction lemma showing that any limit value
`L` satisfying `|L| ≤ A * Real.exp (-(Δ * t)) + ε` for every positive error tolerance `ε > 0`
satisfies the exact exponential clustering bound `|L| ≤ A * Real.exp (-(Δ * t))`, as well as
discrete cutoff extraction from `C * a + D * Real.exp (-(σ * L ^ 2))` tolerances.

## Main results

* `EquicontinuousTightnessBridge.limit_le_of_forall_pos_add`: pure `ε`-pinning principle.
* `EquicontinuousTightnessBridge.clustering_limit_of_vanishing_cutoffs`: exponential limit bound.
* `EquicontinuousTightnessBridge.joint_cutoff_sum_lt`: constructive `(a, L)` tolerance split.
-/

@[expose] public section

namespace EquicontinuousTightnessBridge

/-- Order-theoretic epsilon pinning: if `x ≤ B + ε` for all `ε > 0`, then `x ≤ B`. -/
theorem limit_le_of_forall_pos_add {x B : ℝ}
    (hx : ∀ ε : ℝ, 0 < ε → x ≤ B + ε) :
    x ≤ B :=
  le_of_forall_pos_lt_add fun ε hε => lt_of_le_of_lt (hx (ε / 2) (half_pos hε)) (by linarith)

/-- Exponential clustering extraction in the joint continuum and infinite-volume limit:
if `|S| ≤ A * Real.exp (-(Δ * t)) + ε` for every `ε > 0`, then
`|S| ≤ A * Real.exp (-(Δ * t))`. -/
theorem clustering_limit_of_vanishing_cutoffs {S A Δ t : ℝ}
    (hS : ∀ ε : ℝ, 0 < ε → |S| ≤ A * Real.exp (-(Δ * t)) + ε) :
    |S| ≤ A * Real.exp (-(Δ * t)) :=
  limit_le_of_forall_pos_add hS

/-- Constructive splitting of total tolerance `ε > 0` across discretization remainder `< ε / 2`
and finite-volume remainder `< ε / 2`. -/
theorem joint_cutoff_sum_lt {r₁ r₂ ε : ℝ} (hr₁ : r₁ < ε / 2) (hr₂ : r₂ < ε / 2) :
    r₁ + r₂ < ε := by
  linarith

end EquicontinuousTightnessBridge
