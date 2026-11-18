/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Orthogonal Quaternion Centralizer Quadratic Form on ℝ³

This module defines three-dimensional vectors `Vec3`, their squared Euclidean norm `normSq`,
and the orthogonal commutator quadratic form `adjointTwistQuadraticForm`, proving exact
proportionality to `4 * normSq` and lower bounds on non-zero vectors.

## Main results

- `QuaternionCentralizer.Vec3`: three-component real vector structure.
- `QuaternionCentralizer.normSq`: squared Euclidean norm on `Vec3`.
- `QuaternionCentralizer.adjointTwistQuadraticForm`: orthogonal commutator quadratic form.
- `QuaternionCentralizer.adjointTwistQuadraticForm_eq`: exact identity `= 4 * normSq v`.
- `QuaternionCentralizer.adjointTwistQuadraticForm_ge_three`: lower bound `3 ≤` for `1 ≤ normSq v`.
-/

@[expose] public section

namespace QuaternionCentralizer

/-- Three-dimensional vector over `ℝ`. -/
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Squared Euclidean norm on `Vec3`. -/
def normSq (v : Vec3) : ℝ :=
  v.x ^ 2 + v.y ^ 2 + v.z ^ 2

/-- Orthogonal commutator quadratic form on `Vec3`. -/
def adjointTwistQuadraticForm (v : Vec3) : ℝ :=
  (2 * v.x) ^ 2 + (2 * v.y) ^ 2 + (2 * v.z) ^ 2

/-- Exact proportionality of `adjointTwistQuadraticForm` to `4 * normSq`. -/
theorem adjointTwistQuadraticForm_eq (v : Vec3) :
    adjointTwistQuadraticForm v = 4 * normSq v := by
  unfold adjointTwistQuadraticForm normSq
  ring

/-- On any vector with `1 ≤ normSq v`, the quadratic form is at least `3`. -/
theorem adjointTwistQuadraticForm_ge_three {v : Vec3} (hv : 1 ≤ normSq v) :
    3 ≤ adjointTwistQuadraticForm v := by
  rw [adjointTwistQuadraticForm_eq]
  linarith

end QuaternionCentralizer
