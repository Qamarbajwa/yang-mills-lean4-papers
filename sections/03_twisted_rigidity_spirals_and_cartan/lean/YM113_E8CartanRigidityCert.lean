/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.ExceptionalE8Cartan
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-113: Exceptional Rank-8 `E₈` Unimodular Cartan Rigidity Certificate

This module instantiates `ExceptionalE8Cartan` over `ℚ` to certify zero-mode elimination
and unit simple-root stiffness (`e8CartanForm = 2`) for the rank-8 centerless Lie algebra `E₈`.
-/

namespace YangMillsBlueprint.Certificates

open ExceptionalE8Cartan

/-- Certificate bundling rank-8 Cartan coordinates for `E₈`. -/
structure ExceptionalE8RigidityCert where
  x₀ : ℚ
  x₁ : ℚ
  x₂ : ℚ
  x₃ : ℚ
  x₄ : ℚ
  x₅ : ℚ
  x₆ : ℚ
  x₇ : ℚ

/-- Canonical rank-8 certificate evaluated at the first simple root. -/
def canonicalE8Cert : ExceptionalE8RigidityCert where
  x₀ := 1
  x₁ := 0
  x₂ := 0
  x₃ := 0
  x₄ := 0
  x₅ := 0
  x₆ := 0
  x₇ := 0

instance : Nonempty ExceptionalE8RigidityCert :=
  ⟨canonicalE8Cert⟩

/-- Positive-definite zero-mode elimination for `E₈` over `ℚ`. -/
theorem e8_coxeter_cartan_zero_mode_eliminated (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℚ) :
    e8CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ = 0 →
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧
      x₄ = 0 ∧ x₅ = 0 ∧ x₆ = 0 ∧ x₇ = 0 :=
  (e8CartanForm_eq_zero_iff x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇).mp

/-- Uniform non-negativity of the `E₈` Cartan energy form over `ℚ`. -/
theorem e8_cartan_form_nonneg (c : ExceptionalE8RigidityCert) :
    0 ≤ e8CartanForm c.x₀ c.x₁ c.x₂ c.x₃ c.x₄ c.x₅ c.x₆ c.x₇ :=
  e8CartanForm_nonneg c.x₀ c.x₁ c.x₂ c.x₃ c.x₄ c.x₅ c.x₆ c.x₇

/-- Simple-root evaluation: canonical unit simple root gives strictly positive stiffness `2`. -/
theorem e8_unit_simple_root_stiffness :
    e8CartanForm canonicalE8Cert.x₀ canonicalE8Cert.x₁ canonicalE8Cert.x₂ canonicalE8Cert.x₃
      canonicalE8Cert.x₄ canonicalE8Cert.x₅ canonicalE8Cert.x₆ canonicalE8Cert.x₇ = 2 := by
  unfold canonicalE8Cert e8CartanForm
  norm_num

end YangMillsBlueprint.Certificates
