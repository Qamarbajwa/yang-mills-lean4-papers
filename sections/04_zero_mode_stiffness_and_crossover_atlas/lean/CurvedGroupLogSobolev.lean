/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Perturbed Convexity Margins and Block-Interaction Spectral Gap Bounds

This file formalizes elementary positivity and antitone perturbation bounds for global spectral
gap parameters of the form `(1 - θ) * (ρ₀ * oscFactor)` under multiplicative oscillation
factors `holleyStroockFactor osc = Real.exp (-(2 * osc))` and interaction contraction `θ < 1`.

## Main results

* `CurvedGroupLogSobolev.dobrushinGlobalGap`: `(1 - θ) * (ρ₀ * oscFactor)`.
* `CurvedGroupLogSobolev.dobrushinGlobalGap_pos`: strict positivity when `0 < ρ₀`, `0 < oscFactor`,
  and `θ < 1`.
* `CurvedGroupLogSobolev.dobrushinGlobalGap_ge_of_bounds`: volume-uniform lower bound.
* `CurvedGroupLogSobolev.holleyStroockFactor`: `Real.exp (-(2 * osc))`.
* `CurvedGroupLogSobolev.dobrushin_holley_stroock_pos`: positivity over `ℝ`.
-/

@[expose] public section

namespace CurvedGroupLogSobolev

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Global spectral gap lower bound under multiplicative oscillation and contraction `1 - θ`. -/
def dobrushinGlobalGap (ρ₀ oscFactor θ : F) : F :=
  (1 - θ) * (ρ₀ * oscFactor)

/-- Positivity of `dobrushinGlobalGap` when local gap and oscillation factor are positive
and the block-interaction contraction satisfies `θ < 1`. -/
theorem dobrushinGlobalGap_pos {ρ₀ oscFactor θ : F}
    (hρ : 0 < ρ₀) (hosc : 0 < oscFactor) (hθ : θ < 1) :
    0 < dobrushinGlobalGap ρ₀ oscFactor θ := by
  unfold dobrushinGlobalGap
  exact mul_pos (sub_pos.mpr hθ) (mul_pos hρ hosc)

/-- Monotonicity lower bound from uniform bounds `ρmin ≤ ρ₀`, `oscMin ≤ oscFactor`, `θ ≤ θMax`. -/
theorem dobrushinGlobalGap_ge_of_bounds {ρmin ρ₀ oscMin oscFactor θ θMax : F}
    (hρmin : 0 ≤ ρmin) (hρ : ρmin ≤ ρ₀)
    (hoscMin : 0 ≤ oscMin) (hosc : oscMin ≤ oscFactor)
    (hθMax : θMax ≤ 1) (hθ : θ ≤ θMax) :
    dobrushinGlobalGap ρmin oscMin θMax ≤ dobrushinGlobalGap ρ₀ oscFactor θ := by
  unfold dobrushinGlobalGap
  have h1 : 0 ≤ 1 - θMax := sub_nonneg.mpr hθMax
  have h2 : 1 - θMax ≤ 1 - θ := by linarith
  have h3 : ρmin * oscMin ≤ ρ₀ * oscFactor :=
    mul_le_mul hρ hosc hoscMin (le_trans hρmin hρ)
  exact mul_le_mul h2 h3 (mul_nonneg hρmin hoscMin) (sub_nonneg.mpr (le_trans hθ hθMax))

end OrderedField

section RealHolleyStroock

/-- Exponential oscillation factor `exp (-(2 * osc))`. -/
noncomputable def holleyStroockFactor (osc : ℝ) : ℝ :=
  Real.exp (-(2 * osc))

/-- Strict positivity of `holleyStroockFactor`. -/
theorem holleyStroockFactor_pos (osc : ℝ) :
    0 < holleyStroockFactor osc := by
  unfold holleyStroockFactor
  exact Real.exp_pos _

/-- Antitone monotonicity of `holleyStroockFactor` with respect to oscillation bound `osc`. -/
theorem holleyStroockFactor_anti {osc₁ osc₂ : ℝ} (h : osc₁ ≤ osc₂) :
    holleyStroockFactor osc₂ ≤ holleyStroockFactor osc₁ := by
  unfold holleyStroockFactor
  apply Real.exp_le_exp.mpr
  linarith

/-- Strict positivity over `ℝ` combining Holley-Stroock oscillation and `θ < 1`. -/
theorem dobrushin_holley_stroock_pos {ρ₀ osc θ : ℝ}
    (hρ : 0 < ρ₀) (hθ : θ < 1) :
    0 < dobrushinGlobalGap ρ₀ (holleyStroockFactor osc) θ :=
  dobrushinGlobalGap_pos hρ (holleyStroockFactor_pos osc) hθ

end RealHolleyStroock

end CurvedGroupLogSobolev
