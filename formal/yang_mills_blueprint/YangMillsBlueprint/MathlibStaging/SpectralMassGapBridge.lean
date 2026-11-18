/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Hilbert-Space Spectral Gap Coercivity and Exponential Clustering Bounds

This module provides elementary real inner-product-space lemmas connecting orthogonal
operator coercivity (`Δ * ‖ψ‖ ^ 2 ≤ ⟪ψ, T ψ⟫_ℝ`) to orthogonal projection residuals
and exponential clustering monotonicity `Real.exp (-Δ * t) ≤ Real.exp (-Δ₀ * t)`.

## Main results

* `SpectralMassGapBridge.HasOrthogonalCoercivity`: positive quadratic form gap on `Ωᗮ`.
* `SpectralMassGapBridge.coercivity_orthogonal_decomp`: lower bound after projecting out `Ω`.
* `SpectralMassGapBridge.exp_neg_mul_anti`: monotonicity of exponential decay in the gap rate.
* `SpectralMassGapBridge.exp_decay_product_le`: product bound for two-point decay envelopes.
-/

@[expose] public section

namespace SpectralMassGapBridge

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Positive quadratic coercivity on the orthogonal complement of a unit vector `Ω`. -/
structure HasOrthogonalCoercivity (T : H →ₗ[ℝ] H) (Ω : H) (Δ : ℝ) : Prop where
  gap_pos : 0 < Δ
  norm_vacuum : ‖Ω‖ = 1
  annihilates : T Ω = 0
  symmetric_on_vacuum : ∀ ψ : H, inner ℝ ψ (T Ω) = inner ℝ (T ψ) Ω
  coercive : ∀ ψ : H, inner ℝ Ω ψ = 0 → Δ * ‖ψ‖ ^ 2 ≤ inner ℝ ψ (T ψ)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Exponential decay rates are antitone with respect to the spectral gap parameter. -/
theorem exp_neg_mul_anti {Δ₀ Δ t : ℝ} (hΔ : Δ₀ ≤ Δ) (ht : 0 ≤ t) :
    Real.exp (-(Δ * t)) ≤ Real.exp (-(Δ₀ * t)) := by
  apply Real.exp_le_exp.mpr
  nlinarith

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Product of two exponential clustering envelopes with non-negative prefactors. -/
theorem exp_decay_product_le {C₁ C₂ Δ₁ Δ₂ t : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    (C₁ * Real.exp (-(Δ₁ * t))) * (C₂ * Real.exp (-(Δ₂ * t))) =
      (C₁ * C₂) * Real.exp (-((Δ₁ + Δ₂) * t)) := by
  have _ : 0 ≤ C₁ * C₂ := mul_nonneg hC₁ hC₂
  have hexp : Real.exp (-(Δ₁ * t)) * Real.exp (-(Δ₂ * t)) =
      Real.exp (-((Δ₁ + Δ₂) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (C₁ * Real.exp (-(Δ₁ * t))) * (C₂ * Real.exp (-(Δ₂ * t)))
        = (C₁ * C₂) * (Real.exp (-(Δ₁ * t)) * Real.exp (-(Δ₂ * t))) := by ring
    _ = (C₁ * C₂) * Real.exp (-((Δ₁ + Δ₂) * t)) := by rw [hexp]

/-- Orthogonal decomposition lower bound: any vector `φ = c • Ω + ψ` with `⟪Ω, ψ⟫ = 0`
satisfies `Δ * ‖ψ‖ ^ 2 ≤ ⟪φ, T φ⟫_ℝ`. -/
theorem coercivity_orthogonal_decomp {T : H →ₗ[ℝ] H} {Ω : H} {Δ : ℝ}
    (hT : HasOrthogonalCoercivity T Ω Δ) (c : ℝ) {ψ : H}
    (h_perp : inner ℝ Ω ψ = 0) :
    Δ * ‖ψ‖ ^ 2 ≤ inner ℝ (c • Ω + ψ) (T (c • Ω + ψ)) := by
  have hTΩ : T (c • Ω + ψ) = T ψ := by
    rw [map_add, map_smul, hT.annihilates, smul_zero, zero_add]
  have h_left : inner ℝ (c • Ω) (T ψ) = 0 := by
    rw [real_inner_smul_left]
    have hcomm : inner ℝ Ω (T ψ) = inner ℝ (T ψ) Ω := real_inner_comm _ _
    have hsym := hT.symmetric_on_vacuum ψ
    rw [hT.annihilates, inner_zero_right] at hsym
    rw [hcomm, ← hsym, mul_zero]
  rw [hTΩ, inner_add_left, h_left, zero_add]
  exact hT.coercive ψ h_perp

/-- Strict positivity of the quadratic expectation on any vector whose orthogonal
component `ψ` is nonzero. -/
theorem coercivity_pos_of_perp_ne_zero {T : H →ₗ[ℝ] H} {Ω : H} {Δ : ℝ}
    (hT : HasOrthogonalCoercivity T Ω Δ) (c : ℝ) {ψ : H}
    (h_perp : inner ℝ Ω ψ = 0) (hne : ψ ≠ 0) :
    0 < inner ℝ (c • Ω + ψ) (T (c • Ω + ψ)) := by
  have h_bound := coercivity_orthogonal_decomp hT c h_perp
  have hnorm : 0 < ‖ψ‖ := norm_pos_iff.mpr hne
  have hprod : 0 < Δ * ‖ψ‖ ^ 2 := mul_pos hT.gap_pos (pow_pos hnorm 2)
  linarith

end InnerProduct

end SpectralMassGapBridge
