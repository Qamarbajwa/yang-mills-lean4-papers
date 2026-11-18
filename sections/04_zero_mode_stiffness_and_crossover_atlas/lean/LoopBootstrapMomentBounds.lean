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
# Schur-Complement Moment Matrix Positivity and Quadratic Bootstrap Envelopes

This module formalizes exact `2 × 2` positive-semidefinite moment inequalities (`w² ≤ M₁₁`),
completion-of-squares quadratic loop-equation bounds `(2 * β * w - 3)^2 ≤ 9 + 20 * β^2`,
and normalized trace reflection positivity bounds (`2 * w^2 - 1 ≤ w_domino`).

## Main results

* `LoopBootstrapMomentBounds.sq_le_moment_of_schur`: `w ^ 2 ≤ M₁₁` from `0 ≤ M₁₁ - w ^ 2`.
* `LoopBootstrapMomentBounds.loop_eq_level4_quadratic_le`: `β * w ^ 2 - 3 * w - 5 * β ≤ 0`.
* `LoopBootstrapMomentBounds.loop_eq_level4_completed_square_le`:
  `(2 * β * w - 3) ^ 2 ≤ 9 + 20 * β ^ 2`.
* `LoopBootstrapMomentBounds.domino_reflection_positivity_bound`:
  `0 ≤ w₂ - (2 * w₁ ^ 2 - 1) → 2 * w₁ ^ 2 - 1 ≤ w₂`.
-/

@[expose] public section

namespace LoopBootstrapMomentBounds

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- From positive-semidefinite Schur complement `0 ≤ M₁₁ - w ^ 2`, conclude `w ^ 2 ≤ M₁₁`. -/
theorem sq_le_moment_of_schur {w M₁₁ : F} (hschur : 0 ≤ M₁₁ - w ^ 2) :
    w ^ 2 ≤ M₁₁ := by
  linarith

/-- Level-4 loop equation quadratic bound: if `3 * w = β * M₁₁ + (β / 2) * Δ`, `w ^ 2 ≤ M₁₁`,
and `-10 ≤ Δ`, with `0 ≤ β`, then `β * w ^ 2 - 3 * w - 5 * β ≤ 0`. -/
theorem loop_eq_level4_quadratic_le {β w M₁₁ Δ : F}
    (hβ : 0 ≤ β)
    (hmom : w ^ 2 ≤ M₁₁)
    (hΔ : -10 ≤ Δ)
    (heq : 3 * w = β * M₁₁ + (β / 2) * Δ) :
    β * w ^ 2 - 3 * w - 5 * β ≤ 0 := by
  have h1 : β * w ^ 2 ≤ β * M₁₁ := mul_le_mul_of_nonneg_left hmom hβ
  have h2 : -(5 * β) ≤ (β / 2) * Δ := by
    have hhalf : 0 ≤ β / 2 := div_nonneg hβ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hΔ hhalf
    linarith [show (β / 2) * (-10) = -(5 * β) by ring]
  linarith

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Completed square identity for the Level-4 quadratic envelope. -/
theorem completed_square_identity (β w : F) :
    (2 * β * w - 3) ^ 2 - (9 + 20 * β ^ 2) = 4 * β * (β * w ^ 2 - 3 * w - 5 * β) := by
  ring

/-- Completed-square window bound `(2 * β * w - 3) ^ 2 ≤ 9 + 20 * β ^ 2` for `0 ≤ β`. -/
theorem loop_eq_level4_completed_square_le {β w M₁₁ Δ : F}
    (hβ : 0 ≤ β)
    (hmom : w ^ 2 ≤ M₁₁)
    (hΔ : -10 ≤ Δ)
    (heq : 3 * w = β * M₁₁ + (β / 2) * Δ) :
    (2 * β * w - 3) ^ 2 ≤ 9 + 20 * β ^ 2 := by
  have hquad := loop_eq_level4_quadratic_le hβ hmom hΔ heq
  have h4β : 0 ≤ 4 * β := by linarith
  have hmul : 4 * β * (β * w ^ 2 - 3 * w - 5 * β) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h4β hquad
  rw [← completed_square_identity] at hmul
  linarith

/-- Reflection positivity inequality tying planar domino loops to squared plaquettes. -/
theorem domino_reflection_positivity_bound {w₁ w₂ : F} (h : 0 ≤ w₂ - (2 * w₁ ^ 2 - 1)) :
    2 * w₁ ^ 2 - 1 ≤ w₂ := by
  linarith

end OrderedField

end LoopBootstrapMomentBounds
