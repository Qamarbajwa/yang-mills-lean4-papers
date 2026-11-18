/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.QuaternionCentralizer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# YM-103: SU(2) Orthogonal Twist-Eater Rigidity Certificate

This module specializes `QuaternionCentralizer` to SU(2) twisted
boundary conditions, certifying the exact discrete adjoint Laplacian eigenvalue `λ_min(SU(2)) = 4`,
the lower bound `≥ 3`, and complete elimination of flat abelian toron zero-modes.
-/

namespace YangMillsBlueprint.Certificates

open QuaternionCentralizer

/-- On any unit adjoint vector `v` (`normSq v = 1`), the SU(2) twisted adjoint Laplacian
quadratic form evaluates to `4`. -/
theorem su2_twisted_laplacian_exact {v : Vec3} (hv : normSq v = 1) :
    adjointTwistQuadraticForm v = 4 := by
  rw [adjointTwistQuadraticForm_eq, hv]
  ring

/-- On any adjoint vector with `1 ≤ normSq v`, the SU(2) twisted Laplacian gap is at least `3`. -/
theorem su2_twisted_laplacian_gap_ge_three {v : Vec3} (hv : 1 ≤ normSq v) :
    3 ≤ adjointTwistQuadraticForm v :=
  adjointTwistQuadraticForm_ge_three hv

/-- Complete elimination of flat abelian toron zero-modes under SU(2) orthogonal twist:
if `adjointTwistQuadraticForm v = 0`, then `v` is the zero vector. -/
theorem su2_toron_zero_mode_eliminated {v : Vec3}
    (hv : adjointTwistQuadraticForm v = 0) :
    v.x = 0 ∧ v.y = 0 ∧ v.z = 0 := by
  rw [adjointTwistQuadraticForm_eq] at hv
  have hns : normSq v = 0 := by linarith
  unfold normSq at hns
  have hx : v.x ^ 2 = 0 := by
    have hy : 0 ≤ v.y ^ 2 := by positivity
    have hz : 0 ≤ v.z ^ 2 := by positivity
    have hx0 : 0 ≤ v.x ^ 2 := by positivity
    linarith
  have hy : v.y ^ 2 = 0 := by
    have hz : 0 ≤ v.z ^ 2 := by positivity
    have hy0 : 0 ≤ v.y ^ 2 := by positivity
    linarith
  have hz : v.z ^ 2 = 0 := by linarith
  exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy, sq_eq_zero_iff.mp hz⟩

end YangMillsBlueprint.Certificates
