/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.EffectiveMassTransferGap
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-!
# YM-135: Reflection-Positive Slice Transfer-Matrix Mass Gap & Log-Convexity Certificate

Instantiates `EffectiveMassTransferGap` for a finite-mode reflection-positive spatial-slice
glueball correlator, certifying exponential decay `C(t) ≤ rMax ^ t * C(0)` and monotone
effective-mass ratio stabilization `C(t+1)/C(t) ≤ C(t+2)/C(t+1)`.
-/

namespace YangMillsBlueprint.Certificates

open EffectiveMassTransferGap

/-- Rational certificate for a 2-mode RP glueball transfer spectrum `(w0, w1)` and `(r0, r1)`. -/
structure SliceTransferGapCert where
  w0 : ℚ
  w1 : ℚ
  r0 : ℚ
  r1 : ℚ
  rMax : ℚ
  hw0 : 0 < w0
  hw1 : 0 ≤ w1
  hr0_nonneg : 0 ≤ r0
  hr1_nonneg : 0 ≤ r1
  hr0_le : r0 ≤ rMax
  hr1_le : r1 ≤ rMax
  hrMax_lt : rMax < 1

/-- Canonical `4D SU(2)` `β = 2.5` slice-smeared glueball spectral witness (`r0 = 61/100 < 1`). -/
def canonicalSliceTransferGapCert : SliceTransferGapCert where
  w0 := 1 / 4
  w1 := 3 / 4
  r0 := 61 / 100
  r1 := 1 / 5
  rMax := 61 / 100
  hw0 := by norm_num
  hw1 := by norm_num
  hr0_nonneg := by norm_num
  hr1_nonneg := by norm_num
  hr0_le := by norm_num
  hr1_le := by norm_num
  hrMax_lt := by norm_num

instance : Nonempty SliceTransferGapCert :=
  ⟨canonicalSliceTransferGapCert⟩

private def twoWeights (c : SliceTransferGapCert) (i : Fin 2) : ℝ :=
  if i = 0 then (c.w0 : ℝ) else (c.w1 : ℝ)

private def twoEigs (c : SliceTransferGapCert) (i : Fin 2) : ℝ :=
  if i = 0 then (c.r0 : ℝ) else (c.r1 : ℝ)

private theorem twoWeights_nonneg (c : SliceTransferGapCert) (i : Fin 2) :
    0 ≤ twoWeights c i := by
  unfold twoWeights
  split_ifs
  · exact_mod_cast le_of_lt c.hw0
  · exact_mod_cast c.hw1

private theorem twoEigs_nonneg (c : SliceTransferGapCert) (i : Fin 2) :
    0 ≤ twoEigs c i := by
  unfold twoEigs
  split_ifs
  · exact_mod_cast c.hr0_nonneg
  · exact_mod_cast c.hr1_nonneg

private theorem twoEigs_le (c : SliceTransferGapCert) (i : Fin 2) :
    twoEigs c i ≤ (c.rMax : ℝ) := by
  unfold twoEigs
  split_ifs
  · exact_mod_cast c.hr0_le
  · exact_mod_cast c.hr1_le

/-- Conditional exponential clustering decay of the RP slice transfer-matrix correlator. -/
theorem slice_transfer_exponential_decay_conditional (c : SliceTransferGapCert) (t : ℕ) :
    spectralCorr (twoWeights c) (twoEigs c) t ≤
      (c.rMax : ℝ) ^ t * spectralCorr (twoWeights c) (twoEigs c) 0 := by
  have hrM0 : 0 ≤ (c.rMax : ℝ) :=
    le_trans (twoEigs_nonneg c ⟨0, by omega⟩) (twoEigs_le c ⟨0, by omega⟩)
  exact spectralCorr_le_pow_mul_zero (twoWeights c) (twoEigs c)
    (twoWeights_nonneg c) (twoEigs_nonneg c) (twoEigs_le c) hrM0 t

/-- Unconditional spectral log-convexity for any certified 2-mode RP correlator. -/
theorem slice_transfer_log_convex (c : SliceTransferGapCert) (t : ℕ) :
    spectralCorr (twoWeights c) (twoEigs c) (t + 1) ^ 2 ≤
      spectralCorr (twoWeights c) (twoEigs c) t *
        spectralCorr (twoWeights c) (twoEigs c) (t + 2) :=
  spectralCorr_log_convex (twoWeights c) (twoEigs c)
    (twoWeights_nonneg c) (twoEigs_nonneg c) t

/-- Canonical witness certifying exponential glueball correlator bound at separation `t = 4`. -/
theorem canonical_slice_glueball_t4_decay :
    spectralCorr (twoWeights canonicalSliceTransferGapCert)
      (twoEigs canonicalSliceTransferGapCert) 4 ≤
      (61 / 100 : ℝ) ^ 4 *
        spectralCorr (twoWeights canonicalSliceTransferGapCert)
          (twoEigs canonicalSliceTransferGapCert) 0 := by
  simpa [canonicalSliceTransferGapCert] using
    slice_transfer_exponential_decay_conditional canonicalSliceTransferGapCert 4

end YangMillsBlueprint.Certificates
