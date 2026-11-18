/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Linarith

/-!
# Finite Positive-Semidefinite Reflected Slice Bilinear Kernels

This file formalizes non-negativity of weighted squared reflection pairings
`rpKernelForm w v = ∑ i : Fin n, w i * v i ^ 2` and closure under non-negative addition and
convex combinations over an ordered commutative ring `R`.

## Main results

* `SpatialBlockRP.rpKernelForm`: reflected weighted quadratic form `∑ i, w i * v i ^ 2`.
* `SpatialBlockRP.rpKernelForm_nonneg`: non-negativity under pointwise non-negative weights.
* `SpatialBlockRP.rpKernelForm_add_nonneg`: closure under non-negative sum of kernels.
* `SpatialBlockRP.rpKernelForm_convex_comb_nonneg`: closure under convex interpolation.
-/

@[expose] public section

namespace SpatialBlockRP

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Weighted reflected slice quadratic form `∑ i : Fin n, w i * v i ^ 2`. -/
def rpKernelForm {n : ℕ} (w v : Fin n → R) : R :=
  ∑ i : Fin n, w i * v i ^ 2

/-- Non-negativity of `rpKernelForm w v` when every spectral weight `w i` is non-negative. -/
theorem rpKernelForm_nonneg {n : ℕ} {w v : Fin n → R} (hw : ∀ i : Fin n, 0 ≤ w i) :
    0 ≤ rpKernelForm w v := by
  unfold rpKernelForm
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_nonneg (hw i) (sq_nonneg (v i))

/-- Non-negativity of sums of two reflected slice quadratic forms. -/
theorem rpKernelForm_add_nonneg {n : ℕ} {w₁ w₂ v₁ v₂ : Fin n → R}
    (hw₁ : ∀ i : Fin n, 0 ≤ w₁ i) (hw₂ : ∀ i : Fin n, 0 ≤ w₂ i) :
    0 ≤ rpKernelForm w₁ v₁ + rpKernelForm w₂ v₂ :=
  add_nonneg (rpKernelForm_nonneg hw₁) (rpKernelForm_nonneg hw₂)

/-- Convex interpolation closure: for `0 ≤ α ≤ 1`, convex combinations preserve RP ≥ 0. -/
theorem rpKernelForm_convex_comb_nonneg {n : ℕ} {w₁ w₂ v₁ v₂ : Fin n → R} {α : R}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hw₁ : ∀ i : Fin n, 0 ≤ w₁ i) (hw₂ : ∀ i : Fin n, 0 ≤ w₂ i) :
    0 ≤ (1 - α) * rpKernelForm w₁ v₁ + α * rpKernelForm w₂ v₂ := by
  have h1 : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  exact add_nonneg
    (mul_nonneg h1 (rpKernelForm_nonneg hw₁))
    (mul_nonneg hα0 (rpKernelForm_nonneg hw₂))

end SpatialBlockRP
