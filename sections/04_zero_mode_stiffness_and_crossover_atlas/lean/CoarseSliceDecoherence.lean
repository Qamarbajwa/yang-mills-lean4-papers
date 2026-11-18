/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

/-!
# Geometric Sequence Decay Below Contraction Thresholds

Purely algebraic monotonicity and threshold-discharge lemmas over any linearly ordered ring `F`
for geometric coupling envelopes `coarseSliceCoupling M₀ r k = M₀ * r ^ k`:

* `coarseSliceCoupling_zero`: initial value `M₀` at step `0`.
* `coarseSliceCoupling_anti_step`: antitone decay along non-negative contraction ratios `0 ≤ r ≤ 1`.
* `coarseSliceCoupling_le_margin`: discharges uniform `≤ 1 - η` threshold once `M₀ * r ^ k ≤ 1 - η`.
-/

@[expose] public section

namespace CoarseSliceDecoherence

/-- Geometric envelope `M₀ * r ^ k` after `k` coarse blocking steps. -/
def coarseSliceCoupling {F : Type*} [Mul F] [Pow F ℕ] (M₀ r : F) (k : ℕ) : F :=
  M₀ * r ^ k

/-- Initial envelope equality at step `k = 0`. -/
theorem coarseSliceCoupling_zero {F : Type*} [Monoid F] (M₀ r : F) :
    coarseSliceCoupling M₀ r 0 = M₀ := by
  unfold coarseSliceCoupling
  rw [pow_zero, mul_one]

/-- Antitone step decay: for `0 ≤ M₀` and `0 ≤ r ≤ 1`, `k₁ ≤ k₂` implies
`coarseSliceCoupling M₀ r k₂ ≤ coarseSliceCoupling M₀ r k₁`. -/
theorem coarseSliceCoupling_anti_step {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {M₀ r : F} (hM₀ : 0 ≤ M₀) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    coarseSliceCoupling M₀ r k₂ ≤ coarseSliceCoupling M₀ r k₁ := by
  unfold coarseSliceCoupling
  have hpow : r ^ k₂ ≤ r ^ k₁ := pow_le_pow_of_le_one hr0 hr1 hk
  exact mul_le_mul_of_nonneg_left hpow hM₀

/-- Persistence below threshold: once `M₀ * r ^ k₀ ≤ 1 - η` holds at stride `k₀` with
`0 ≤ M₀` and `0 ≤ r ≤ 1`, then `coarseSliceCoupling M₀ r k ≤ 1 - η` for all `k₀ ≤ k`. -/
theorem coarseSliceCoupling_le_margin {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {M₀ r η : F} {k₀ k : ℕ} (hM₀ : 0 ≤ M₀) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hk : k₀ ≤ k) (hbound : M₀ * r ^ k₀ ≤ 1 - η) :
    coarseSliceCoupling M₀ r k ≤ 1 - η :=
  (coarseSliceCoupling_anti_step hM₀ hr0 hr1 hk).trans hbound

end CoarseSliceDecoherence
