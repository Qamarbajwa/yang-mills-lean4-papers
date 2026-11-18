/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CartanCoxeterRigidity
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-108: Centerless Exceptional Lie Group Cartan-Coxeter Rigidity Certificate

This module instantiates `CartanCoxeterRigidity` over `ℚ` for the rank-2 `G₂` and rank-4 `F₄`
unimodular Cartan quadratic forms, certifying zero-mode elimination and unit root stiffness.
-/

namespace YangMillsBlueprint.Certificates

open CartanCoxeterRigidity

/-- Certificate bundling Cartan coordinates for the rank-2 `G₂` and rank-4 `F₄` forms. -/
structure CenterlessGroupRigidityCert where
  x : ℚ
  y : ℚ
  x₁ : ℚ
  x₂ : ℚ
  x₃ : ℚ
  x₄ : ℚ

/-- Canonical centerless Cartan coordinate certificate at unit simple roots. -/
def canonicalCenterlessCert : CenterlessGroupRigidityCert where
  x := 1
  y := 0
  x₁ := 1
  x₂ := 0
  x₃ := 0
  x₄ := 0

instance : Nonempty CenterlessGroupRigidityCert :=
  ⟨canonicalCenterlessCert⟩

/-- Positive-definite zero-mode elimination for the `G₂` Cartan quadratic form over `ℚ`. -/
theorem g2_coxeter_cartan_zero_mode_eliminated (x y : ℚ) :
    g2CartanForm x y = 0 → x = 0 ∧ y = 0 :=
  (g2CartanForm_eq_zero_iff x y).mp

/-- Positive-definite zero-mode elimination for the `F₄` Cartan quadratic form over `ℚ`. -/
theorem f4_coxeter_cartan_zero_mode_eliminated (x₁ x₂ x₃ x₄ : ℚ) :
    f4CartanForm x₁ x₂ x₃ x₄ = 0 → x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 :=
  (f4CartanForm_eq_zero_iff x₁ x₂ x₃ x₄).mp

/-- Minimum lattice root-vector stiffness evaluations on `G₂`:
`g2CartanForm 1 0 = 2` and `g2CartanForm 0 1 = 6`. -/
theorem g2_unit_root_stiffness :
    g2CartanForm (1 : ℚ) 0 = 2 ∧ g2CartanForm (0 : ℚ) 1 = 6 := by
  unfold g2CartanForm
  norm_num

end YangMillsBlueprint.Certificates
