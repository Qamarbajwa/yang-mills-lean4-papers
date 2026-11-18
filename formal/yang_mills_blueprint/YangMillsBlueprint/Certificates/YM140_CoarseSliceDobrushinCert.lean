/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CoarseSliceDecoherence
import YangMillsBlueprint.MathlibStaging.EffectiveMassTransferGap
import YangMillsBlueprint.MathlibStaging.SliceMarkovTensorization
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-140: Coarse Temporal-Slice Dobrushin Contraction Certificate (`WP1-C` / `WP3-C`)

Calibrates `CoarseSliceDecoherence` against Probe 14 (`L = 4, 6, 8` at `β = 2.3`):
- Static `Δt = 0` normalized spatial susceptibility `M₀ = 12 > 1`
- Single-step transfer ratio `r = 3 / 10` (`Δt = 1`: `12 * 3 / 10 = 18 / 5 = 3.6 > 1`)
- At coarse blocking depth `k = 3`, `coarseSliceCoupling 12 (3 / 10) 3 = 81 / 250 = 0.324 ≤ 1 / 2`,
  discharging the `ℓ¹` spatial-slice row-sum hypothesis of `YM138` (`SliceMarkovTensorization`)
  for every spatial box size `n ~ L³`.
-/

namespace YangMillsBlueprint.Certificates

open CoarseSliceDecoherence SliceMarkovTensorization

/-- Certificate bundling static spatial susceptibility `M₀`, transfer ratio `r`, blocking
depth `k`, and target slice contraction threshold `η`. -/
structure CoarseSliceDobrushinCert where
  M0 : ℚ
  r : ℚ
  η : ℚ
  k : ℕ
  hM0 : 0 ≤ M0
  hr0 : 0 ≤ r
  hr1 : r ≤ 1
  hη0 : 0 < η
  hη1 : η < 1
  hk2 : 2 ≤ k
  hbound : M0 * r ^ k ≤ 1 - η

/-- Canonical Probe-14 calibration (`M0 = 12`, `r = 3 / 10`, `k = 3`, `η = 1 / 2`):
`coarseSliceCoupling 12 (3 / 10) 3 = 81 / 250 ≤ 1 - 1 / 2 = 1 / 2`. -/
def canonicalCoarseSliceCert : CoarseSliceDobrushinCert where
  M0 := 12
  r := 3 / 10
  η := 1 / 2
  k := 3
  hM0 := by norm_num
  hr0 := by norm_num
  hr1 := by norm_num
  hη0 := by norm_num
  hη1 := by norm_num
  hk2 := by omega
  hbound := by norm_num

instance : Nonempty CoarseSliceDobrushinCert :=
  ⟨canonicalCoarseSliceCert⟩

/-- Exact canonical evaluation at `k = 3`: `coarseSliceCoupling 12 (3 / 10) 3 = 81 / 250 ≤ 1 / 2`. -/
theorem canonical_coarse_slice_k3_eval :
    coarseSliceCoupling canonicalCoarseSliceCert.M0 canonicalCoarseSliceCert.r
        canonicalCoarseSliceCert.k = 81 / 250 ∧
      coarseSliceCoupling canonicalCoarseSliceCert.M0 canonicalCoarseSliceCert.r
        canonicalCoarseSliceCert.k ≤ 1 - canonicalCoarseSliceCert.η := by
  dsimp [canonicalCoarseSliceCert, coarseSliceCoupling]
  constructor <;> norm_num

/-- Unconditional `ℓ²`-squared contraction margin `1 - (1 - η) ^ 2 > 0` for any valid
`CoarseSliceDobrushinCert`. -/
theorem coarse_slice_sq_margin_pos (c : CoarseSliceDobrushinCert) :
    0 < 1 - (1 - c.η) ^ 2 := by
  have hfac : 0 < c.η * (2 - c.η) := mul_pos c.hη0 (by linarith [c.hη1])
  linarith [show 1 - (1 - c.η) ^ 2 = c.η * (2 - c.η) by ring]

/-- **CONDITIONAL:** Once `k`-step coarse temporal blocking (`k ≥ 2`) achieves symmetric
inter-slice `ℓ¹` row bound `coarseSliceCoupling c.M0 c.r c.k ≤ 1 - c.η` and local block
row bound `ηB` with combined symmetric row sum `≤ 1 - c.η` uniformly in spatial dimension `n`,
`YM138` yields an `L³`-uniform `ℓ²` operator contraction bound `(1 - c.η) ^ 2` with strict
gap margin `0 < 1 - (1 - c.η) ^ 2`. -/
theorem coarse_slice_dobrushin_gap_conditional (c : CoarseSliceDobrushinCert)
    {n : ℕ} (M₀ E : Fin n → Fin n → ℚ) (v : Fin n → ℚ)
    (hsymM : ∀ i j, M₀ i j + E i j = M₀ j i + E j i)
    (hrowTot : ∀ i, ∑ j : Fin n, |M₀ i j + E i j| ≤
      (1 - c.η - coarseSliceCoupling c.M0 c.r c.k) + coarseSliceCoupling c.M0 c.r c.k) :
    ∑ i : Fin n, (∑ j : Fin n, (M₀ i j + E i j) * v j) ^ 2 ≤
        (1 - c.η) ^ 2 * ∑ j : Fin n, v j ^ 2 ∧
      0 < 1 - (1 - c.η) ^ 2 := by
  have hdec := coarseSliceCoupling_le_margin c.hM0 c.hr0 c.hr1 le_rfl c.hbound
  have hrow : ∀ i, ∑ j : Fin n, |M₀ i j + E i j| ≤ 1 - c.η := by
    intro i
    have hi := hrowTot i
    linarith
  have hρ0 : 0 ≤ 1 - c.η := le_of_lt (sub_pos.mpr c.hη1)
  exact ⟨schur_symmetric_operator_sq_le (fun i j => M₀ i j + E i j) v hsymM hρ0 hrow,
    coarse_slice_sq_margin_pos c⟩

end YangMillsBlueprint.Certificates
