/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Chessboard Power Extraction and Cluster Suppression Bounds

This module formalizes the elementary algebraic extraction step in chessboard reflection
positivity estimates: if a non-negative defect weight `p` satisfies `p ^ m ≤ r ^ m` for a
non-negative upper threshold `r` and positive block tiling multiplicity `m ≠ 0`, then
`p ≤ r`, and any `k`-fold product satisfies exponential cluster suppression `p ^ k ≤ r ^ k`.

## Main results

* `ChessboardHolderBound.chessboard_defect_le_of_pow`: root extraction `p ^ m ≤ r ^ m → p ≤ r`.
* `ChessboardHolderBound.chessboard_cluster_suppression`: `k`-cell bound `p ^ k ≤ r ^ k`.
* `ChessboardHolderBound.chessboard_strict_threshold_lt`: `r < η → p ^ k ≤ η ^ k`.
-/

@[expose] public section

namespace ChessboardHolderBound

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Chessboard root extraction: from `0 ≤ p`, `0 ≤ r`, `m ≠ 0`, and `p ^ m ≤ r ^ m`,
deduce `p ≤ r`. -/
theorem chessboard_defect_le_of_pow {p r : F} {m : ℕ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hm : m ≠ 0) (hpow : p ^ m ≤ r ^ m) :
    p ≤ r :=
  (pow_le_pow_iff_left₀ hp hr hm).mp hpow

/-- Area/multiplicity suppression: `p ^ k ≤ r ^ k` for all `k : ℕ`. -/
theorem chessboard_cluster_suppression {p r : F}
    (hp : 0 ≤ p) (hr : 0 ≤ r) {m : ℕ} (hm : m ≠ 0) (hpow : p ^ m ≤ r ^ m) (k : ℕ) :
    p ^ k ≤ r ^ k := by
  have hpr : p ≤ r := chessboard_defect_le_of_pow hp hr hm hpow
  exact pow_le_pow_left₀ hp hpr k

/-- Strict sub-threshold decay relative to any `η` with `r < η`. -/
theorem chessboard_strict_threshold_lt {p r η : F}
    (hp : 0 ≤ p) (hr : 0 ≤ r) {m : ℕ} (hm : m ≠ 0) (hpow : p ^ m ≤ r ^ m)
    (hη : r ≤ η) (k : ℕ) :
    p ^ k ≤ η ^ k :=
  le_trans (chessboard_cluster_suppression hp hr hm hpow k) (pow_le_pow_left₀ hr hη k)

end ChessboardHolderBound
