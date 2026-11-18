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
# Spanning-Tree Degree Counting and Stiffness Margin Variance Bounds

This file proves natural-number edge-degree conservation `(V - 1) + ((d - 1) * V + 1) = d * V`
for a maximal spanning tree on a regular graph of degree `2 * d` over `V` vertices, and gives
elementary variance upper bounds `1 / (m - κ)` from positive stiffness margins over a linearly
ordered field `F`.

## Main results

* `CurvedBrascampLiebDefect.tree_gauge_dof_conservation`: spanning-tree degree identity.
* `CurvedBrascampLiebDefect.effectiveStiffness`: difference `m - κ`.
* `CurvedBrascampLiebDefect.curvedVarianceBound`: reciprocal variance bound `1 / (m - κ)`.
* `CurvedBrascampLiebDefect.effectiveStiffness_pos`: positivity for `κ < m`.
* `CurvedBrascampLiebDefect.curvedVarianceBound_pos`: positivity of `1 / (m - κ)`.
* `CurvedBrascampLiebDefect.curvedVarianceBound_le_of_margin`: upper bound `1 / (m - κ) ≤ 1 / δ`.
-/

@[expose] public section

namespace CurvedBrascampLiebDefect

/-- Spanning-tree degree-of-freedom conservation on `V` vertices in `d` coordinate axes. -/
theorem tree_gauge_dof_conservation (d V : ℕ) (hd : 1 ≤ d) (hV : 1 ≤ V) :
    (V - 1) + ((d - 1) * V + 1) = d * V := by
  have hdV : 1 ≤ d * V := Nat.mul_pos hd hV
  zify [hd, hV, hdV]
  ring

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Net positive stiffness margin `m - κ`. -/
def effectiveStiffness (m κ : F) : F :=
  m - κ

/-- Reciprocal variance bound `1 / (m - κ)`. -/
def curvedVarianceBound (m κ : F) : F :=
  1 / (m - κ)

/-- Positivity of `effectiveStiffness m κ` when `κ < m`. -/
theorem effectiveStiffness_pos {m κ : F} (h : κ < m) :
    0 < effectiveStiffness m κ := by
  unfold effectiveStiffness
  linarith

/-- Positivity of `curvedVarianceBound m κ` when `κ < m`. -/
theorem curvedVarianceBound_pos {m κ : F} (h : κ < m) :
    0 < curvedVarianceBound m κ := by
  unfold curvedVarianceBound
  exact one_div_pos.mpr (sub_pos.mpr h)

/-- Variance upper bound from any strictly positive lower margin `δ ≤ effectiveStiffness m κ`. -/
theorem curvedVarianceBound_le_of_margin {m κ δ : F} (hδ : 0 < δ)
    (hm : δ ≤ effectiveStiffness m κ) :
    curvedVarianceBound m κ ≤ 1 / δ := by
  unfold curvedVarianceBound
  exact one_div_le_one_div_of_le hδ hm

end OrderedField

end CurvedBrascampLiebDefect
