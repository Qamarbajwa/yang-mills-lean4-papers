/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.UrsellCumulantNonGaussian
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-121: Non-Gaussian 4-Point Ursell Cumulant Non-Triviality Witness Certificate

This module instantiates `UrsellCumulantNonGaussian` over `ℚ` at `m₂ = 1`, `γ = 24 / 41`,
and `m₄ = 99 / 41`, certifying strict negativity `ursellFour = -24 / 41 < 0` and
non-Gaussian interaction witness `ursellFour ≠ 0`.
-/

namespace YangMillsBlueprint.Certificates

open UrsellCumulantNonGaussian

/-- Rational certificate encoding a strict sub-Gaussian fourth-moment deficit `γ > 0`. -/
structure NonTrivialityWitnessCert where
  m₂ : ℚ
  γ : ℚ
  m₄ : ℚ
  hm₂ : 0 < m₂
  hγ : 0 < γ
  hsub : m₄ ≤ (3 - γ) * m₂ ^ 2

/-- Canonical non-triviality witness (`m₂ = 1, γ = 24 / 41, m₄ = 99 / 41`). -/
def canonicalNonTrivialityWitnessCert : NonTrivialityWitnessCert where
  m₂ := 1
  γ := 24 / 41
  m₄ := 99 / 41
  hm₂ := by norm_num
  hγ := by norm_num
  hsub := by norm_num

instance : Nonempty NonTrivialityWitnessCert :=
  ⟨canonicalNonTrivialityWitnessCert⟩

/-- Conditional strict negativity and non-vanishing of the 4-point Ursell cumulant. -/
theorem subgaussian_ursell_nontrivial_conditional (c : NonTrivialityWitnessCert) :
    ursellFour c.m₄ c.m₂ < 0 ∧ ursellFour c.m₄ c.m₂ ≠ 0 :=
  ⟨ursellFour_neg_of_subgaussian c.hsub c.hγ c.hm₂,
    ursellFour_ne_zero_of_subgaussian c.hsub c.hγ c.hm₂⟩

/-- Canonical numeric evaluation: `ursellFour (99 / 41) 1 = -24 / 41 ≠ 0`. -/
theorem canonical_ursell_four_eval :
    ursellFour (99 / 41 : ℚ) 1 = -24 / 41 ∧
      ursellFour (99 / 41 : ℚ) 1 ≠ 0 := by
  unfold ursellFour
  norm_num

end YangMillsBlueprint.Certificates
