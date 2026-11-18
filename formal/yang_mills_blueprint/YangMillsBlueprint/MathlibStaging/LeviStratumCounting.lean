/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Partition Stratum Dimension Accounting and Scaling Exponent Identities

This module formalizes mode-dimension conservation across flat, conjugation, quadratic, and
quartic blocks indexed by integer partitions `(n₁, ..., n_k)` of `N` with `S = ∑ n_r ^ 2`,
and proves exact algebraic comparison formulas for the rational scaling exponent `alphaHarm`.

## Main results

* `LeviStratumCounting.stratum_dimension_conservation`:
  `d * (k - 1) + (N^2 - S) + (d - 1) * (N^2 - S) + d * (S - k) = d * (N^2 - 1)`.
* `LeviStratumCounting.alphaHarm`, `LeviStratumCounting.alphaReg`: rational exponents.
* `LeviStratumCounting.four_mul_alphaReg_sub_alphaHarm_eq`:
  exact defect `4 * (alphaReg - alphaHarm) = (d - 2) * (S - N) + d * (k - N)`.
* `LeviStratumCounting.alphaHarm_central_le_alphaReg`:
  central stratum exponent never exceeds regular stratum exponent for `4 ≤ d` and `2 ≤ N`.
-/

@[expose] public section

namespace LeviStratumCounting

/-- Natural-number dimension conservation across the four mode subspaces. -/
theorem stratum_dimension_conservation (d N S k : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hkS : k ≤ S) (hSN : S ≤ N ^ 2) :
    d * (k - 1) + (N ^ 2 - S) + (d - 1) * (N ^ 2 - S) + d * (S - k) = d * (N ^ 2 - 1) := by
  have hk1 : 1 ≤ N ^ 2 := le_trans hk (le_trans hkS hSN)
  zify [hd, hk, hkS, hSN, hk1]
  ring

section ScalingExponent

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Harmonic scaling exponent `((d - 1) / 2) * (N^2 - S) + (d / 4) * (S - k)`. -/
def alphaHarm (d N S k : F) : F :=
  ((d - 1) / 2) * (N ^ 2 - S) + (d / 4) * (S - k)

/-- Regular stratum exponent `((d - 1) / 2) * (N^2 - N)` corresponding to `S = N, k = N`. -/
def alphaReg (d N : F) : F :=
  ((d - 1) / 2) * (N ^ 2 - N)

/-- Exact `4`-scaled algebraic identity for `alphaReg - alphaHarm`. -/
theorem four_mul_alphaReg_sub_alphaHarm_eq (d N S k : F) :
    4 * (alphaReg d N - alphaHarm d N S k) =
      (d - 2) * (S - N) + d * (k - N) := by
  unfold alphaReg alphaHarm
  ring

/-- Regular specialization: when `S = N` and `k = N`, `alphaHarm = alphaReg`. -/
theorem alphaHarm_self_eq_alphaReg (d N : F) :
    alphaHarm d N N N = alphaReg d N := by
  unfold alphaHarm alphaReg
  ring

/-- Central stratum suppression: when `S = N ^ 2`, `k = 1`, `4 ≤ d`, and `2 ≤ N`,
`alphaHarm d N (N ^ 2) 1 ≤ alphaReg d N`, with strict inequality when `3 ≤ N`. -/
theorem alphaHarm_central_le_alphaReg {d N : F} (hd : 4 ≤ d) (hN : 2 ≤ N) :
    alphaHarm d N (N ^ 2) 1 ≤ alphaReg d N := by
  have hdiff : 4 * (alphaReg d N - alphaHarm d N (N ^ 2) 1) =
      (N - 1) * ((d - 2) * (N - 1) - 2) := by
    rw [four_mul_alphaReg_sub_alphaHarm_eq]
    ring
  have hNm1 : 0 ≤ N - 1 := by linarith
  have hd2 : 2 ≤ d - 2 := by linarith
  have hN1 : 1 ≤ N - 1 := by linarith
  have hprod : 2 ≤ (d - 2) * (N - 1) := by nlinarith
  have hfactor : 0 ≤ (d - 2) * (N - 1) - 2 := by linarith
  have hnonneg : 0 ≤ (N - 1) * ((d - 2) * (N - 1) - 2) := mul_nonneg hNm1 hfactor
  linarith

end ScalingExponent

end LeviStratumCounting
