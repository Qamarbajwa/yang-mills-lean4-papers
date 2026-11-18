/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Symmetric Fourth-Order Cumulant Defects and Sub-Gaussian Moment Strict Negativity

This file defines the fourth-order symmetric cumulant functional `m₄ - 3 * m₂ ^ 2` (`ursellFour`)
over a linearly ordered field `F`, characterizes its vanishing locus (`m₄ = 3 * m₂ ^ 2`), and
proves strict negativity and non-vanishing under a strict sub-Gaussian fourth-moment deficit
`m₄ ≤ (3 - γ) * m₂ ^ 2` with `0 < γ` and `0 < m₂`.

## Main results

* `UrsellCumulantNonGaussian.ursellFour`: fourth cumulant `m₄ - 3 * m₂ ^ 2`.
* `UrsellCumulantNonGaussian.ursellFour_eq_zero_iff`: `ursellFour m₄ m₂ = 0 ↔ m₄ = 3 * m₂ ^ 2`.
* `UrsellCumulantNonGaussian.ursellFour_neg_of_subgaussian`: negativity under deficit `γ > 0`.
* `UrsellCumulantNonGaussian.ursellFour_ne_zero_of_subgaussian`: non-vanishing for `γ > 0`.
-/

@[expose] public section

namespace UrsellCumulantNonGaussian

section RingOps

variable {F : Type*} [CommRing F]

/-- Fourth-order cumulant functional `m₄ - 3 * m₂ ^ 2`. -/
def ursellFour (m₄ m₂ : F) : F :=
  m₄ - 3 * m₂ ^ 2

/-- Characterization of the Gaussian vanishing locus of `ursellFour`. -/
theorem ursellFour_eq_zero_iff (m₄ m₂ : F) :
    ursellFour m₄ m₂ = 0 ↔ m₄ = 3 * m₂ ^ 2 := by
  unfold ursellFour
  exact sub_eq_zero

end RingOps

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Strict negativity of `ursellFour` under a strict sub-Gaussian deficit `γ > 0`
and positive second moment `m₂ > 0`. -/
theorem ursellFour_neg_of_subgaussian {m₄ m₂ γ : F}
    (hsub : m₄ ≤ (3 - γ) * m₂ ^ 2) (hγ : 0 < γ) (hm₂ : 0 < m₂) :
    ursellFour m₄ m₂ < 0 := by
  unfold ursellFour
  have hm₂sq : 0 < m₂ ^ 2 := sq_pos_of_pos hm₂
  have hγm : 0 < γ * m₂ ^ 2 := mul_pos hγ hm₂sq
  linarith

/-- Non-vanishing of `ursellFour` under a strict sub-Gaussian deficit `γ > 0`
and positive second moment `m₂ > 0`. -/
theorem ursellFour_ne_zero_of_subgaussian {m₄ m₂ γ : F}
    (hsub : m₄ ≤ (3 - γ) * m₂ ^ 2) (hγ : 0 < γ) (hm₂ : 0 < m₂) :
    ursellFour m₄ m₂ ≠ 0 :=
  ne_of_lt (ursellFour_neg_of_subgaussian hsub hγ hm₂)

end OrderedField

end UrsellCumulantNonGaussian
