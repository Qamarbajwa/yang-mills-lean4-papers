/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Inverse-Linear Recurrence Flows and Telescoping Defect Bounds

This file analyzes the one-parameter rational recurrence flow
`runningCoupling g₀ b k = g₀ / (1 + k * b * g₀)` over a linearly ordered field `F`. When
`g₀ > 0` and `b > 0`, the inverse of `runningCoupling g₀ b k` grows linearly as
`1 / g₀ + k * b`, bounding `runningCoupling g₀ b k ≤ 1 / (k * b)` and ensuring that
consecutive quadratic defect terms telescope cleanly.

## Main results

* `AsymptoticFreedomFlow.inv_runningCoupling_eq`: `1 / runningCoupling g₀ b k = 1 / g₀ + k * b`.
* `AsymptoticFreedomFlow.runningCoupling_le_inv_mul`: `runningCoupling g₀ b k ≤ 1 / (k * b)`.
* `AsymptoticFreedomFlow.telescoping_step_eq`: `1 / (k * (k + 1)) = 1 / k - 1 / (k + 1)`.
-/

@[expose] public section

namespace AsymptoticFreedomFlow

section

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Rational inverse-linear flow `g₀ / (1 + k * b * g₀)`. -/
def runningCoupling (g₀ b k : F) : F :=
  g₀ / (1 + k * b * g₀)

/-- Exact linear growth of the inverse coupling for `g₀ ≠ 0`. -/
theorem inv_runningCoupling_eq {g₀ b k : F} (hg₀ : g₀ ≠ 0) :
    1 / runningCoupling g₀ b k = 1 / g₀ + k * b := by
  unfold runningCoupling
  rw [one_div_div, add_div, mul_div_cancel_right₀ _ hg₀]

/-- Positivity of `runningCoupling g₀ b k` for `0 < g₀`, `0 ≤ b`, and `0 ≤ k`. -/
theorem runningCoupling_pos {g₀ b k : F} (hg₀ : 0 < g₀) (hb : 0 ≤ b) (hk : 0 ≤ k) :
    0 < runningCoupling g₀ b k := by
  unfold runningCoupling
  have h_denom : 0 < 1 + k * b * g₀ := by positivity
  exact div_pos hg₀ h_denom

/-- Upper bound `runningCoupling g₀ b k ≤ 1 / (k * b)` for `0 < g₀`, `0 < b`, and `0 < k`. -/
theorem runningCoupling_le_inv_mul {g₀ b k : F}
    (hg₀ : 0 < g₀) (hb : 0 < b) (hk : 0 < k) :
    runningCoupling g₀ b k ≤ 1 / (k * b) := by
  unfold runningCoupling
  have h_denom : 0 < 1 + k * b * g₀ := by positivity
  have h_kb : 0 < k * b := by positivity
  rw [div_le_div_iff₀ h_denom h_kb]
  linarith

/-- Telescoping partial-fraction identity for consecutive scale indices `k ≠ 0` and
`k + 1 ≠ 0`. -/
theorem telescoping_step_eq {k : F} (hk : k ≠ 0) (hk1 : k + 1 ≠ 0) :
    1 / (k * (k + 1)) = 1 / k - 1 / (k + 1) := by
  field_simp [hk, hk1]
  ring

/-- For `0 ≤ K`, the telescoped cumulative weight `1 - 1 / (K + 1)` is strictly less than
`1`. -/
theorem telescoped_sum_lt_one {K : F} (hK : 0 ≤ K) :
    1 - 1 / (K + 1) < 1 := by
  have h_pos : 0 < 1 / (K + 1) := by positivity
  linarith

end

end AsymptoticFreedomFlow
