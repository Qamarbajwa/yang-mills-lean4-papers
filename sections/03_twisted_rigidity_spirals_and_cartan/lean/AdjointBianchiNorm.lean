/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Positivity

/-!
# General Compact Lie-Group Adjoint Transport Chord Identity

For any square orthogonal transformation `U : Matrix (Fin n) (Fin n) R` (`U * Uᵀ = 1` and
`Uᵀ * U = 1`, including adjoint representations of centerless exceptional groups `G₂`, `F₄`,
and `E₈`) and any element `X : Matrix (Fin n) (Fin n) R`, we prove the exact Frobenius
chording identity equating the parallel-transport Bianchi defect norm squared to the matrix
commutator norm squared:
`frobSq (adjAction U X - X) = frobSq (comm U X)`.

## Main results

* `AdjointBianchiNorm.frobSq_nonneg`: non-negativity of `frobSq M = (M * Mᵀ).trace`.
* `AdjointBianchiNorm.frobSq_adjAction`: orthogonal adjoint isometry `frobSq (adjAction U X)`.
* `AdjointBianchiNorm.adjAction_sub_eq`: transport factorization `(comm U X) * Uᵀ`.
* `AdjointBianchiNorm.frobSq_adjAction_sub_eq`: `frobSq (adjAction U X - X) = frobSq (comm U X)`.
-/

@[expose] public section

namespace AdjointBianchiNorm

open Matrix

/-- Squared Frobenius / Killing-Hilbert-Schmidt norm `(M * Mᵀ).trace` on `n × n` matrices. -/
def frobSq {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) : R :=
  (M * Mᵀ).trace

/-- Orthogonal adjoint conjugation `U * X * Uᵀ`. -/
def adjAction {n : ℕ} {R : Type*} [CommRing R] (U X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  U * X * Uᵀ

/-- Matrix commutator `[U, X] = U * X - X * U`. -/
def matrixComm {n : ℕ} {R : Type*} [CommRing R] (U X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  U * X - X * U

/-- Non-negativity of `frobSq M` over any linearly ordered commutative ring. -/
theorem frobSq_nonneg {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    0 ≤ frobSq M := by
  unfold frobSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  rw [← sq]
  exact sq_nonneg (M i j)

/-- Right multiplication by orthogonal `V` (`V * Vᵀ = 1`) preserves `frobSq`. -/
theorem frobSq_mul_right_orth {n : ℕ} {R : Type*} [CommRing R]
    (M V : Matrix (Fin n) (Fin n) R) (hV : V * Vᵀ = 1) :
    frobSq (M * V) = frobSq M := by
  unfold frobSq
  calc
    ((M * V) * (M * V)ᵀ).trace = (M * V * (Vᵀ * Mᵀ)).trace := by
      rw [Matrix.transpose_mul]
    _ = (M * (V * Vᵀ) * Mᵀ).trace := by
      simp only [Matrix.mul_assoc]
    _ = (M * Mᵀ).trace := by
      rw [hV, Matrix.mul_one]

/-- Left multiplication by orthogonal `U` (`Uᵀ * U = 1`) preserves `frobSq`. -/
theorem frobSq_mul_left_orth {n : ℕ} {R : Type*} [CommRing R]
    (U M : Matrix (Fin n) (Fin n) R) (hU : Uᵀ * U = 1) :
    frobSq (U * M) = frobSq M := by
  unfold frobSq
  calc
    ((U * M) * (U * M)ᵀ).trace = ((U * (M * Mᵀ)) * Uᵀ).trace := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = (Uᵀ * (U * (M * Mᵀ))).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((Uᵀ * U) * (M * Mᵀ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (M * Mᵀ).trace := by
      rw [hU, Matrix.one_mul]

/-- Orthogonal adjoint conjugation preserves `frobSq`. -/
theorem frobSq_adjAction {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU2 : Uᵀ * U = 1) :
    frobSq (adjAction U X) = frobSq X := by
  unfold adjAction
  rw [frobSq_mul_right_orth (U * X) Uᵀ (by simpa [Matrix.transpose_transpose] using hU2)]
  exact frobSq_mul_left_orth U X hU2

/-- Exact factorization `adjAction U X - X = matrixComm U X * Uᵀ` for `U * Uᵀ = 1`. -/
theorem adjAction_sub_eq {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU1 : U * Uᵀ = 1) :
    adjAction U X - X = matrixComm U X * Uᵀ := by
  unfold adjAction matrixComm
  calc
    U * X * Uᵀ - X = U * X * Uᵀ - X * (U * Uᵀ) := by rw [hU1, Matrix.mul_one]
    _ = (U * X - X * U) * Uᵀ := by
      simp only [Matrix.sub_mul, Matrix.mul_assoc]

/-- Exact general-rank adjoint Bianchi chord identity:
`frobSq (adjAction U X - X) = frobSq (matrixComm U X)` for any orthogonal `U`. -/
theorem frobSq_adjAction_sub_eq {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) :
    frobSq (adjAction U X - X) = frobSq (matrixComm U X) := by
  rw [adjAction_sub_eq U X hU1]
  exact frobSq_mul_right_orth (matrixComm U X) Uᵀ
    (by simpa [Matrix.transpose_transpose] using hU2)

/-- Abelian Cartan vanishing: if `U * X = X * U`, the adjoint Bianchi defect is zero. -/
theorem frobSq_adjAction_sub_zero_of_comm {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1)
    (hc : U * X = X * U) :
    frobSq (adjAction U X - X) = 0 := by
  rw [frobSq_adjAction_sub_eq U X hU1 hU2]
  unfold matrixComm frobSq
  simp [hc]

end AdjointBianchiNorm
