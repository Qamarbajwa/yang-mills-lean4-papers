/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Inductive Super-Critical Affine Recurrence Floor Preservation

This module extends one-step affine recurrence amplification `x ↦ s * x - c` to arbitrary
discrete trajectories `σ : ℕ → F` with varying penalties `c : ℕ → F` bounded above by `cMax`.
Whenever `1 < s` and a floor `σFloor` satisfies `cMax / (s - 1) ≤ σFloor ≤ σ 0`, the entire
infinite sequence remains bounded below by `σFloor` for all `k : ℕ`.

## Main results

* `InductivePeierlsRGBridge.rgStepMap`: affine step `s * x - c`.
* `InductivePeierlsRGBridge.floor_le_rgStep_of_le`: single-step floor preservation.
* `InductivePeierlsRGBridge.rgTrajectory_ge_floor`: inductive bound `∀ k, σFloor ≤ σ k`.
* `InductivePeierlsRGBridge.rgTrajectory_ge_of_strict`: strict survival above critical threshold.
-/

@[expose] public section

namespace InductivePeierlsRGBridge

section FieldOps

variable {F : Type*} [Field F]

/-- Linear affine step `s * x - c`. -/
def rgStepMap (s c x : F) : F :=
  s * x - c

end FieldOps

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Single-step preservation: if `1 < s`, `cMax / (s - 1) ≤ σFloor ≤ x`, and `c ≤ cMax`,
then `σFloor ≤ s * x - c`. -/
theorem floor_le_rgStep_of_le {s c cMax σFloor x : F}
    (hs : 1 < s) (hcrit : cMax / (s - 1) ≤ σFloor) (hc : c ≤ cMax) (hx : σFloor ≤ x) :
    σFloor ≤ rgStepMap s c x := by
  unfold rgStepMap
  have hspos : 0 < s - 1 := sub_pos.mpr hs
  have hcmax : cMax ≤ σFloor * (s - 1) := (div_le_iff₀ hspos).mp hcrit
  have h1 : (s - 1) * σFloor ≤ (s - 1) * x :=
    mul_le_mul_of_nonneg_left hx (le_of_lt hspos)
  linarith

/-- Inductive trajectory floor: if every step satisfies `s * σ k - c k ≤ σ (k + 1)` with
uniform penalty cap `c k ≤ cMax`, then `σFloor ≤ σ k` holds for all `k : ℕ`. -/
theorem rgTrajectory_ge_floor {s cMax σFloor : F} {σ c : ℕ → F}
    (hs : 1 < s) (hcrit : cMax / (s - 1) ≤ σFloor) (h0 : σFloor ≤ σ 0)
    (hc : ∀ k : ℕ, c k ≤ cMax)
    (hstep : ∀ k : ℕ, rgStepMap s (c k) (σ k) ≤ σ (k + 1)) :
    ∀ k : ℕ, σFloor ≤ σ k := by
  intro k
  induction k with
  | zero => exact h0
  | succ m hm =>
    exact le_trans (floor_le_rgStep_of_le hs hcrit (hc m) hm) (hstep m)

/-- Strict super-critical trajectory persistence relative to `cMax / (s - 1)`. -/
theorem rgTrajectory_strict_above_critical {s cMax : F} {σ c : ℕ → F}
    (hs : 1 < s) (h0 : cMax / (s - 1) < σ 0)
    (hc : ∀ k : ℕ, c k ≤ cMax)
    (hstep : ∀ k : ℕ, rgStepMap s (c k) (σ k) ≤ σ (k + 1)) :
    ∀ k : ℕ, σ 0 ≤ σ k :=
  rgTrajectory_ge_floor hs (le_of_lt h0) (le_refl (σ 0)) hc hstep

end OrderedField

end InductivePeierlsRGBridge
