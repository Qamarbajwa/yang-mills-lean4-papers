/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith

/-!
# Polydisk Majorant Inequalities and Infinite Geometric Tail Bounds

This module proves elementary majorant and geometric tail bounds over an arbitrary
linearly ordered field, together with infinite geometric series `tsum` bounds over `ℝ`.

## Main results

- `PolydiskMajorant.total_weight_lt_one`: bounds a sum of leading and tail weights below `1`.
- `PolydiskMajorant.one_sub_weight_pos`: positivity of the unit complement `1 - w`.
- `PolydiskMajorant.geometric_defect_le`: rational majorant bound for `c * r / (1 - r)`.
- `PolydiskMajorant.summable_geometric_tail`: summability of `n ↦ w ^ (n + 1)` for `0 ≤ w < 1`.
- `PolydiskMajorant.tsum_geometric_tail_eq`: exact evaluation `∑' n, w ^ (n + 1) = w / (1 - w)`.
- `PolydiskMajorant.tsum_geometric_tail_le`: margin bound `∑' n, w ^ (n + 1) ≤ (1 - m) / m`.
-/

@[expose] public section

namespace PolydiskMajorant

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Total majorant weight combining a leading contribution and a tail contribution. -/
def totalWeight (wLeading wTail : F) : F :=
  wLeading + wTail

/-- If the tail is bounded above by `wBound` and `wLeading + wBound < 1`, then the total
weight is strictly less than `1`. -/
theorem total_weight_lt_one {wLeading wTail wBound : F}
    (hTail : wTail ≤ wBound) (hSum : wLeading + wBound < 1) :
    totalWeight wLeading wTail < 1 := by
  unfold totalWeight
  linarith

/-- Positivity of the contraction margin `1 - w` whenever `w < 1`. -/
theorem one_sub_weight_pos {w : F} (hw : w < 1) : 0 < 1 - w :=
  sub_pos.mpr hw

/-- Upper bound on a geometric tail `c * r / (1 - r)` for `r < 1`. -/
theorem geometric_defect_le {c r bound : F}
    (hr₁ : r < 1) (hbound : c * r ≤ bound * (1 - r)) :
    c * r / (1 - r) ≤ bound :=
  (div_le_iff₀ (sub_pos.mpr hr₁)).mpr hbound

end OrderedField

section RealSeries

/-- Summability of the shifted geometric series `n ↦ w ^ (n + 1)` for `0 ≤ w < 1`. -/
theorem summable_geometric_tail {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w < 1) :
    Summable (fun n : ℕ => w ^ (n + 1)) := by
  have h := (summable_geometric_of_lt_one hw₀ hw₁).mul_left w
  simpa [pow_succ'] using h

/-- Exact value of the shifted geometric series `∑' n, w ^ (n + 1) = w / (1 - w)`. -/
theorem tsum_geometric_tail_eq {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w < 1) :
    (∑' n : ℕ, w ^ (n + 1)) = w / (1 - w) := by
  have hsum : (fun n : ℕ => w ^ (n + 1)) = (fun n : ℕ => w * w ^ n) := by
    ext n
    rw [pow_succ']
  rw [hsum, tsum_mul_left, tsum_geometric_of_lt_one hw₀ hw₁, div_eq_mul_inv]

/-- Infinite geometric tail bound: if `0 ≤ w`, `0 < m`, and `w + m ≤ 1`, then the shifted
geometric series is summable, equals `w / (1 - w)`, and is bounded above by `(1 - m) / m`. -/
theorem tsum_geometric_tail_le {w m : ℝ}
    (hw₀ : 0 ≤ w) (hm₀ : 0 < m) (hwm : w + m ≤ 1) :
    Summable (fun n : ℕ => w ^ (n + 1)) ∧
      (∑' n : ℕ, w ^ (n + 1)) = w / (1 - w) ∧
      (∑' n : ℕ, w ^ (n + 1)) ≤ (1 - m) / m := by
  have hw₁ : w < 1 := by linarith
  refine ⟨summable_geometric_tail hw₀ hw₁, tsum_geometric_tail_eq hw₀ hw₁, ?_⟩
  rw [tsum_geometric_tail_eq hw₀ hw₁]
  have h1w : 0 < 1 - w := sub_pos.mpr hw₁
  rw [div_le_div_iff₀ h1w hm₀]
  nlinarith

end RealSeries

end PolydiskMajorant
