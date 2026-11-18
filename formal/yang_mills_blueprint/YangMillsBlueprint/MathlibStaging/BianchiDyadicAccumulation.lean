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
# Dyadic Accumulation Recurrence for Orthogonal Alignment Loss

Purely algebraic recurrence over any linearly ordered field `F` modeling doubly-exponential
saturation under independent orthogonal composition steps on normalized loss `δ ∈ [0, 1]`:

* `dyadicLossStep δ = 2 * δ - δ ^ 2`
* `iteratedDyadicLoss δ₀ k`: `k`-step dyadic iterate starting from `δ₀`

## Main results

* `BianchiDyadicAccumulation.one_sub_dyadicLossStep`: `1 - dyadicLossStep δ = (1 - δ) ^ 2`.
* `BianchiDyadicAccumulation.one_sub_iteratedDyadicLoss_eq`: closed form `(1 - δ₀) ^ (2 ^ k)`.
* `BianchiDyadicAccumulation.lt_dyadicLossStep_of_pos_of_lt_one`: strict growth `δ < step δ`.
* `BianchiDyadicAccumulation.dyadicLossStep_lt_one`: strict upper bound `step δ < 1`.
* `BianchiDyadicAccumulation.iteratedDyadicLoss_zero`: exact `0` fixed point across all `k`.
-/

@[expose] public section

namespace BianchiDyadicAccumulation

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Single orthogonal composition step `2 * δ - δ ^ 2 = 1 - (1 - δ) ^ 2`. -/
def dyadicLossStep (δ : F) : F :=
  2 * δ - δ ^ 2

/-- Recursive `k`-scale dyadic accumulation starting from microscopic loss `δ₀`. -/
def iteratedDyadicLoss (δ₀ : F) : ℕ → F
  | 0 => δ₀
  | k + 1 => dyadicLossStep (iteratedDyadicLoss δ₀ k)

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Exact complement squaring identity `1 - dyadicLossStep δ = (1 - δ) ^ 2`. -/
theorem one_sub_dyadicLossStep (δ : F) :
    1 - dyadicLossStep δ = (1 - δ) ^ 2 := by
  unfold dyadicLossStep
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Closed-form doubly-exponential complement law:
`1 - iteratedDyadicLoss δ₀ k = (1 - δ₀) ^ (2 ^ k)`. -/
theorem one_sub_iteratedDyadicLoss_eq (δ₀ : F) (k : ℕ) :
    1 - iteratedDyadicLoss δ₀ k = (1 - δ₀) ^ (2 ^ k) := by
  induction k with
  | zero =>
      simp [iteratedDyadicLoss]
  | succ k ih =>
      calc
        1 - iteratedDyadicLoss δ₀ (k + 1)
            = (1 - iteratedDyadicLoss δ₀ k) ^ 2 := one_sub_dyadicLossStep _
        _ = ((1 - δ₀) ^ (2 ^ k)) ^ 2 := by rw [ih]
        _ = (1 - δ₀) ^ (2 ^ k * 2) := by rw [← pow_mul]
        _ = (1 - δ₀) ^ (2 ^ (k + 1)) := by rw [Nat.pow_succ]

/-- Strict single-step amplification `δ < dyadicLossStep δ` for `0 < δ < 1`. -/
theorem lt_dyadicLossStep_of_pos_of_lt_one {δ : F} (h0 : 0 < δ) (h1 : δ < 1) :
    δ < dyadicLossStep δ := by
  have hdiff : 0 < δ * (1 - δ) := mul_pos h0 (sub_pos.mpr h1)
  unfold dyadicLossStep
  linarith [show 2 * δ - δ ^ 2 - δ = δ * (1 - δ) by ring]

/-- Strict upper invariance `dyadicLossStep δ < 1` whenever `δ < 1`. -/
theorem dyadicLossStep_lt_one {δ : F} (h1 : δ < 1) :
    dyadicLossStep δ < 1 := by
  have hsq : 0 < (1 - δ) ^ 2 := sq_pos_of_pos (sub_pos.mpr h1)
  linarith [one_sub_dyadicLossStep δ]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Exact fixed point at zero: `iteratedDyadicLoss 0 k = 0` for all `k`. -/
theorem iteratedDyadicLoss_zero (k : ℕ) :
    iteratedDyadicLoss (0 : F) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change dyadicLossStep (iteratedDyadicLoss (0 : F) k) = 0
      rw [ih]
      unfold dyadicLossStep
      ring

/-- Preservation of `(0, 1)` bounds across arbitrary dyadic depth `k : ℕ`. -/
theorem iteratedDyadicLoss_mem_Ioo {δ₀ : F} (h0 : 0 < δ₀) (h1 : δ₀ < 1) (k : ℕ) :
    0 < iteratedDyadicLoss δ₀ k ∧ iteratedDyadicLoss δ₀ k < 1 := by
  induction k with
  | zero => exact ⟨h0, h1⟩
  | succ k ih =>
      rcases ih with ⟨ih0, ih1⟩
      exact ⟨lt_trans ih0 (lt_dyadicLossStep_of_pos_of_lt_one ih0 ih1),
        dyadicLossStep_lt_one ih1⟩

end BianchiDyadicAccumulation
