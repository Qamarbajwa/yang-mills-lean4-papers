/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

/-!
# Adjoint Representation Mass Gap Bounds Without Central Group Cohomology

This module formalizes elementary lower-bound transfers for spectral gaps in centerless or
adjoint-projected systems: whenever the adjoint representation gap `Δadj` satisfies
`0 < Δfloor ≤ Δadj` and `Δadj ≤ Δtot`, any auxiliary centerless decomposition preserves
strict positivity `0 < Δtot` independently of center-group invariants.

## Main results

* `CenterlessWeylAlcoveGap.adjointGapFloor_pos`: positivity transfer `0 < Δtot`.
* `CenterlessWeylAlcoveGap.weylAlcoveCoerciveGap_pos`: additive Cartan + adjoint floor positivity.
-/

@[expose] public section

namespace CenterlessWeylAlcoveGap

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Positivity transfer from an adjoint gap floor `0 < Δfloor ≤ Δadj ≤ Δtot`. -/
theorem adjointGapFloor_pos {Δfloor Δadj Δtot : F}
    (hfloor : 0 < Δfloor) (hadj : Δfloor ≤ Δadj) (htot : Δadj ≤ Δtot) :
    0 < Δtot :=
  lt_of_lt_of_le hfloor (le_trans hadj htot)

/-- Combined spectral lower bound from a non-negative Cartan quadratic form floor `q ≥ 0`
and a strictly positive adjoint gap `Δadj > 0`. -/
theorem weylAlcoveCoerciveGap_pos {q Δadj Δtot : F}
    (hq : 0 ≤ q) (hadj : 0 < Δadj) (htot : q + Δadj ≤ Δtot) :
    0 < Δtot := by
  linarith

end CenterlessWeylAlcoveGap
