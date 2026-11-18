/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Symanzik Discretization Error Envelopes and Continuum Limit Extraction

This file studies the logarithmic scaling envelope
`symanzikBound C a = C * a ^ 2 * (1 - Real.log a)` over `0 < a ≤ 1`. Using
`-Real.log a = Real.log (1 / a) ≤ 1 / a - 1`, we prove `symanzikBound C a ≤ C * a`, giving an
explicit constructive cutoff `a ≤ min 1 (ε / (C + 1))` below which discretization errors fall
strictly below any tolerance `ε > 0`.

## Main results

* `SymanzikRotationalBound.symanzikBound`: envelope `C * a ^ 2 * (1 - Real.log a)`.
* `SymanzikRotationalBound.symanzikBound_nonneg`: non-negativity for `0 ≤ C` and `0 < a ≤ 1`.
* `SymanzikRotationalBound.symanzikBound_le_linear`: linear dominating bound `≤ C * a`.
* `SymanzikRotationalBound.symanzikBound_lt_of_le`: constructive `ε`-cutoff extraction.
-/

@[expose] public section

namespace SymanzikRotationalBound

/-- Symanzik discretization envelope `C * a ^ 2 * (1 - Real.log a)`. -/
noncomputable def symanzikBound (C a : ℝ) : ℝ :=
  C * a ^ 2 * (1 - Real.log a)

/-- Non-negativity of `symanzikBound C a` for `0 ≤ C` and `0 < a ≤ 1`. -/
theorem symanzikBound_nonneg {C a : ℝ} (hC : 0 ≤ C) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    0 ≤ symanzikBound C a := by
  unfold symanzikBound
  have hlog : Real.log a ≤ 0 := Real.log_nonpos (le_of_lt ha0) ha1
  have hfac : 0 ≤ 1 - Real.log a := by linarith
  positivity

/-- Linear dominating upper bound: for `0 ≤ C` and `0 < a ≤ 1`,
`C * a ^ 2 * (1 - Real.log a) ≤ C * a`. -/
theorem symanzikBound_le_linear {C a : ℝ} (hC : 0 ≤ C) (ha0 : 0 < a) :
    symanzikBound C a ≤ C * a := by
  unfold symanzikBound
  have hlog : -Real.log a ≤ 1 / a - 1 := by
    rw [← Real.log_inv]
    simpa [one_div] using Real.log_le_sub_one_of_pos (one_div_pos.mpr ha0)
  have hfac : 1 - Real.log a ≤ 1 / a := by linarith
  have h1 : a ^ 2 * (1 - Real.log a) ≤ a ^ 2 * (1 / a) :=
    mul_le_mul_of_nonneg_left hfac (sq_nonneg a)
  have h2 : a ^ 2 * (1 / a) = a := by
    field_simp
  have h3 : C * a ^ 2 * (1 - Real.log a) = C * (a ^ 2 * (1 - Real.log a)) := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (le_trans h1 (le_of_eq h2)) hC

/-- Constructive tolerance bound: for any `ε > 0` and `C ≥ 0`, choosing
`0 < a ≤ min 1 (ε / (C + 1))` guarantees `symanzikBound C a < ε`. -/
theorem symanzikBound_lt_of_cutoff {C a ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (ha0 : 0 < a) (ha : a ≤ ε / (C + 1)) :
    symanzikBound C a < ε := by
  have hlin := symanzikBound_le_linear hC ha0
  have hCp : 0 < C + 1 := by linarith
  have haε : C * a ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left ha hC
  have hlt : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hCp]
    nlinarith
  exact lt_of_le_of_lt (le_trans hlin haε) hlt

end SymanzikRotationalBound
