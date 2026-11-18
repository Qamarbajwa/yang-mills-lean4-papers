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
# Linear Affine Recurrence Steps and Super-Critical Fixed-Point Amplification

This file analyzes the affine recurrence `rgTensionStep s c σ = s * σ - c` relative to its
unique fixed point `criticalTension s c = c / (s - 1)` for slope `s ≠ 1` over a linearly
ordered field `F`. Whenever `1 < s` and `criticalTension s c < σ`, the recurrence expands
strictly away from the fixed point.

## Main results

* `PeierlsRGContourFlow.rgTensionStep`: affine step `s * σ - c`.
* `PeierlsRGContourFlow.criticalTension`: unstable fixed point `c / (s - 1)`.
* `PeierlsRGContourFlow.rgTensionStep_sub_critical`: exact expansion factor `s`.
* `PeierlsRGContourFlow.criticalTension_lt_rgTensionStep`: preservation above critical value.
* `PeierlsRGContourFlow.lt_rgTensionStep_of_gt_critical`: strict monotone amplification.
-/

@[expose] public section

namespace PeierlsRGContourFlow

section FieldOps

variable {F : Type*} [Field F]

/-- Linear affine step `s * σ - c`. -/
def rgTensionStep (s c σ : F) : F :=
  s * σ - c

/-- Fixed point `c / (s - 1)` of `σ ↦ s * σ - c`. -/
def criticalTension (s c : F) : F :=
  c / (s - 1)

/-- Exact residual expansion identity around `criticalTension s c` for `s ≠ 1`. -/
theorem rgTensionStep_sub_critical {s c σ : F} (hs : s ≠ 1) :
    rgTensionStep s c σ - criticalTension s c = s * (σ - criticalTension s c) := by
  unfold rgTensionStep criticalTension
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

end FieldOps

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Any input strictly above `criticalTension s c` remains strictly above after a step. -/
theorem criticalTension_lt_rgTensionStep {s c σ : F} (hs : 1 < s)
    (hσ : criticalTension s c < σ) :
    criticalTension s c < rgTensionStep s c σ := by
  have hsne : s ≠ 1 := ne_of_gt hs
  have hid := rgTensionStep_sub_critical (c := c) (σ := σ) hsne
  have hpos : 0 < s * (σ - criticalTension s c) :=
    mul_pos (by linarith) (sub_pos.mpr hσ)
  linarith

/-- Strict amplification `σ < rgTensionStep s c σ` above `criticalTension s c` when `1 < s`. -/
theorem lt_rgTensionStep_of_gt_critical {s c σ : F} (hs : 1 < s)
    (hσ : criticalTension s c < σ) :
    σ < rgTensionStep s c σ := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  have hdiff : rgTensionStep s c σ - σ = (s - 1) * (σ - criticalTension s c) := by
    unfold rgTensionStep criticalTension
    field_simp
    ring
  have hpos : 0 < (s - 1) * (σ - criticalTension s c) :=
    mul_pos (sub_pos.mpr hs) (sub_pos.mpr hσ)
  linarith

end OrderedField

end PeierlsRGContourFlow
