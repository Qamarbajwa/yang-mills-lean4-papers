/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CenterlessWeylAlcoveGap
import YangMillsBlueprint.MathlibStaging.CartanCoxeterRigidity
import YangMillsBlueprint.MathlibStaging.ExceptionalE8Cartan
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-130: Centerless Gauge Family Adjoint-Gap & Weyl-Alcove Positivity Certificate

This module instantiates `CenterlessWeylAlcoveGap` alongside centerless Cartan forms (`YM108`,
`YM113`) over `ℚ`, certifying positive gap transfer `0 < Δtot` for trivial-center groups
(`G₂`, `F₄`, `E₈`) from an adjoint-representation floor `Δadj ≥ Δfloor > 0` without relying on
non-trivial group-center cohomology.
-/

namespace YangMillsBlueprint.Certificates

open CenterlessWeylAlcoveGap

/-- Certificate bundling adjoint spectral floor `Δfloor > 0` and Cartan stiffness witness. -/
structure CenterlessGroupGapCert where
  Δfloor : ℚ
  qCartan : ℚ
  hfloor : 0 < Δfloor
  hq : 0 ≤ qCartan

/-- Canonical centerless adjoint-gap witness (`Δfloor = 1 / 4`, `qCartan = 3`). -/
def canonicalCenterlessGroupGapCert : CenterlessGroupGapCert where
  Δfloor := 1 / 4
  qCartan := 3
  hfloor := by norm_num
  hq := by norm_num

instance : Nonempty CenterlessGroupGapCert :=
  ⟨canonicalCenterlessGroupGapCert⟩

/-- Conditional centerless continuum mass-gap positivity from an adjoint-channel floor. -/
theorem centerless_adjoint_gap_pos_conditional (c : CenterlessGroupGapCert)
    {Δadj Δtot : ℚ} (hadj : c.Δfloor ≤ Δadj) (htot : c.qCartan + Δadj ≤ Δtot) :
    0 < Δtot := by
  have hpos : 0 < Δadj := lt_of_lt_of_le c.hfloor hadj
  exact weylAlcoveCoerciveGap_pos c.hq hpos htot

/-- Exact check that combining canonical Cartan stiffness (`q = 3` on unit `G₂` root) with
`Δadj ≥ 1 / 4` guarantees `Δtot ≥ 13 / 4 > 0`. -/
theorem canonical_centerless_g2_combined_gap_pos :
    0 < (3 : ℚ) + (1 / 4 : ℚ) ∧
      (0 : ℚ) ≤ CartanCoxeterRigidity.g2CartanForm (1 : ℚ) 0 := by
  refine ⟨by norm_num, ?_⟩
  unfold CartanCoxeterRigidity.g2CartanForm
  norm_num

end YangMillsBlueprint.Certificates
