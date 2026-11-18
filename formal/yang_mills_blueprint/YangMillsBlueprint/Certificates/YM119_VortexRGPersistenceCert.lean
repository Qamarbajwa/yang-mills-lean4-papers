/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.PeierlsRGContourFlow
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-119: Super-Critical Peierls RG Surface Tension Persistence Certificate

This module instantiates `PeierlsRGContourFlow` at decimation scale factor `s = 4`,
entropy penalty `c = 3 / 2`, and bare string tension `σ₀ = 1`, certifying
`criticalTension = 1 / 2 < σ₀` and strict RG amplification `rgTensionStep = 5 / 2 > σ₀`.
-/

namespace YangMillsBlueprint.Certificates

open PeierlsRGContourFlow

/-- Rational certificate for a super-critical Peierls contour decimation step. -/
structure VortexRGPersistenceCert where
  s : ℚ
  c : ℚ
  σ₀ : ℚ
  hs : 1 < s
  hσ₀ : criticalTension s c < σ₀

/-- Canonical super-critical Peierls RG witness (`s = 4, c = 3 / 2, σ₀ = 1`). -/
def canonicalVortexRGPersistenceCert : VortexRGPersistenceCert where
  s := 4
  c := 3 / 2
  σ₀ := 1
  hs := by norm_num
  hσ₀ := by
    unfold criticalTension
    norm_num

instance : Nonempty VortexRGPersistenceCert :=
  ⟨canonicalVortexRGPersistenceCert⟩

/-- Conditional RG amplification and preservation above critical tension. -/
theorem peierls_rg_tension_amplifies_conditional (cert : VortexRGPersistenceCert) :
    cert.σ₀ < rgTensionStep cert.s cert.c cert.σ₀ ∧
      criticalTension cert.s cert.c < rgTensionStep cert.s cert.c cert.σ₀ :=
  ⟨lt_rgTensionStep_of_gt_critical cert.hs cert.hσ₀,
    criticalTension_lt_rgTensionStep cert.hs cert.hσ₀⟩

/-- Canonical evaluation at `s = 4, c = 3 / 2, σ₀ = 1`:
`criticalTension = 1 / 2 < 1` and `rgTensionStep = 5 / 2 > 1`. -/
theorem canonical_vortex_rg_persistence_eval :
    criticalTension (4 : ℚ) (3 / 2) = 1 / 2 ∧
      rgTensionStep (4 : ℚ) (3 / 2) 1 = 5 / 2 ∧
      (1 : ℚ) < rgTensionStep (4 : ℚ) (3 / 2) 1 := by
  unfold criticalTension rgTensionStep
  norm_num

end YangMillsBlueprint.Certificates
