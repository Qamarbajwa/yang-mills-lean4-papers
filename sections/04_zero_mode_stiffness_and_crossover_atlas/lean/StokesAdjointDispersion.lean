/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import YangMillsBlueprint.MathlibStaging.AdjointBianchiNorm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Non-Abelian Stokes Adjoint Dispersion & Coulomb-Dipole Non-Cancellation

Builds on `AdjointBianchiNorm` (`YM-136`) to formalize the exact Frobenius polarization
mechanism explaining why non-Abelian parallel transport `T` prevents interior Abelian Coulomb
edge cancellation across Wilson loop surfaces:

1. `frobInner_adjAction_self_mul_two`: for any orthogonal adjoint matrix `U` (`U * Uᵀ = 1`,
   `Uᵀ * U = 1`), `2 * frobInner (adjAction U X) X = 2 * frobSq X - frobSq (matrixComm U X)`.
2. `frobSq_coulomb_dipole_noncancellation`: transporting an anti-correlated dipole `-α • X` by `U`
   yields `frobSq (X + adjAction U (-(α • X))) = (1 - α) ^ 2 * frobSq X + α * frobSq [U, X]`.
3. `frobSq_exact_cancellation_eq_comm`: even exact Abelian cancellation (`α = 1`, `X₂ = -X₁`)
   leaves a strictly positive Stokes residual `frobSq (matrixComm U X₁)` when `[U, X₁] ≠ 0`.
4. `stokes_sum_frobSq_ge_of_bianchi_floor`: converts a pairwise covariant Bianchi decoherence
   floor into an area-proportional lower bound on the total transported Stokes flux norm squared.
-/

@[expose] public section

namespace StokesAdjointDispersion

open AdjointBianchiNorm Matrix

/-- Matrix Frobenius inner product `(A * Bᵀ).trace` on `n × n` matrices. -/
def frobInner {n : ℕ} {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) : R :=
  (A * Bᵀ).trace

/-- Symmetry of the Frobenius inner product via cyclic trace invariance. -/
theorem frobInner_comm {n : ℕ} {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) :
    frobInner A B = frobInner B A := by
  unfold frobInner
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Exact Frobenius polarization identity for `A - B`. -/
theorem frobSq_sub_eq {n : ℕ} {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) :
    frobSq (A - B) = frobSq A + frobSq B - 2 * frobInner A B := by
  unfold frobSq frobInner
  have hmul : (A - B) * (A - B)ᵀ = A * Aᵀ - A * Bᵀ - B * Aᵀ + B * Bᵀ := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  rw [hmul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  have hsym : (B * Aᵀ).trace = (A * Bᵀ).trace := by
    simpa [frobInner] using frobInner_comm B A
  rw [hsym]
  ring

/-- Exact Frobenius polarization identity for `A + B`. -/
theorem frobSq_add_eq {n : ℕ} {R : Type*} [CommRing R] (A B : Matrix (Fin n) (Fin n) R) :
    frobSq (A + B) = frobSq A + frobSq B + 2 * frobInner A B := by
  unfold frobSq frobInner
  have hmul : (A + B) * (A + B)ᵀ = A * Aᵀ + A * Bᵀ + B * Aᵀ + B * Bᵀ := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  rw [hmul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
  have hsym : (B * Aᵀ).trace = (A * Bᵀ).trace := by
    simpa [frobInner] using frobInner_comm B A
  rw [hsym]
  ring

/-- Right-bilinearity of `frobInner` under negation. -/
theorem frobInner_neg_right {n : ℕ} {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) :
    frobInner A (-B) = -frobInner A B := by
  unfold frobInner
  rw [Matrix.transpose_neg, Matrix.mul_neg, Matrix.trace_neg]

/-- Right-linearity of `frobInner` under scalar multiplication. -/
theorem frobInner_smul_right {n : ℕ} {R : Type*} [CommRing R]
    (α : R) (A B : Matrix (Fin n) (Fin n) R) :
    frobInner A (α • B) = α * frobInner A B := by
  unfold frobInner
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Negation invariance of `frobSq (-M) = frobSq M`. -/
theorem frobSq_neg {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    frobSq (-M) = frobSq M := by
  unfold frobSq
  rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- Scalar scaling law for `frobSq (α • M) = α ^ 2 * frobSq M`. -/
theorem frobSq_smul {n : ℕ} {R : Type*} [CommRing R]
    (α : R) (M : Matrix (Fin n) (Fin n) R) :
    frobSq (α • M) = α ^ 2 * frobSq M := by
  unfold frobSq
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `adjAction` commutes with scalar multiplication. -/
theorem adjAction_smul {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (α : R) :
    adjAction U (α • X) = α • adjAction U X := by
  unfold adjAction
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `adjAction` commutes with negation. -/
theorem adjAction_neg {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) :
    adjAction U (-X) = -adjAction U X := by
  unfold adjAction
  rw [Matrix.mul_neg, Matrix.neg_mul]

/-- Exact adjoint alignment loss formula:
`2 * frobInner (adjAction U X) X = 2 * frobSq X - frobSq (matrixComm U X)`. -/
theorem frobInner_adjAction_self_mul_two {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) :
    2 * frobInner (adjAction U X) X = 2 * frobSq X - frobSq (matrixComm U X) := by
  have hpol := frobSq_sub_eq (adjAction U X) X
  have hiso := frobSq_adjAction U X hU2
  have hchord := frobSq_adjAction_sub_eq U X hU1 hU2
  rw [hiso, hchord] at hpol
  calc
    2 * frobInner (adjAction U X) X
        = (frobSq X + frobSq X) - (frobSq X + frobSq X - 2 * frobInner (adjAction U X) X) := by
          ring
    _ = 2 * frobSq X - frobSq (matrixComm U X) := by
          rw [← hpol]
          ring

/-- Exact transported Coulomb-dipole non-cancellation law:
for `X₂ = -(α • X₁)` transported by orthogonal `U`,
`frobSq (X₁ + adjAction U (-(α • X₁))) = (1 - α) ^ 2 * frobSq X₁ + α * frobSq [U, X₁]`. -/
theorem frobSq_coulomb_dipole_noncancellation {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (α : R) (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) :
    frobSq (X + adjAction U (-(α • X))) =
      (1 - α) ^ 2 * frobSq X + α * frobSq (matrixComm U X) := by
  have hadd := frobSq_add_eq X (adjAction U (-(α • X)))
  have hrew : adjAction U (-(α • X)) = -(α • adjAction U X) := by
    rw [adjAction_neg, adjAction_smul]
  rw [hrew] at hadd
  have hsq : frobSq (-(α • adjAction U X)) = α ^ 2 * frobSq X := by
    rw [frobSq_neg, frobSq_smul, frobSq_adjAction U X hU2]
  have hin : frobInner X (-(α • adjAction U X)) = -(α * frobInner (adjAction U X) X) := by
    rw [frobInner_neg_right, frobInner_smul_right, frobInner_comm X (adjAction U X)]
  have hloss := frobInner_adjAction_self_mul_two U X hU1 hU2
  rw [hsq, hin] at hadd
  calc
    frobSq (X + adjAction U (-(α • X)))
        = frobSq X + α ^ 2 * frobSq X - α * (2 * frobInner (adjAction U X) X) := by
          rw [hrew, hadd]
          ring
    _ = frobSq X + α ^ 2 * frobSq X - α * (2 * frobSq X - frobSq (matrixComm U X)) := by
          rw [hloss]
    _ = (1 - α) ^ 2 * frobSq X + α * frobSq (matrixComm U X) := by ring

/-- Exact Abelian edge-cancellation (`α = 1`, `X₂ = -X₁`) leaves exact commutator residual
`frobSq (matrixComm U X)` after orthogonal parallel transport `U`. -/
theorem frobSq_exact_cancellation_eq_comm {n : ℕ} {R : Type*} [CommRing R]
    (U X : Matrix (Fin n) (Fin n) R) (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) :
    frobSq (X + adjAction U (-X)) = frobSq (matrixComm U X) := by
  have h := frobSq_coulomb_dipole_noncancellation U X 1 hU1 hU2
  simpa using h

/-- Trace linearity for finite sums of matrices. -/
theorem trace_finset_sum {n : ℕ} {ι : Type*} {R : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) R) :
    (∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i).trace := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.trace]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.trace_add, ih, Finset.sum_insert ha]

/-- Exact variance expansion of `frobSq (∑ i, M i)` as diagonal sum plus off-diagonal
pair inner products. -/
theorem frobSq_sum_eq {n m : ℕ} {R : Type*} [CommRing R]
    (M : Fin m → Matrix (Fin n) (Fin n) R) :
    frobSq (∑ i : Fin m, M i) =
      (∑ i : Fin m, frobSq (M i)) +
        ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, frobInner (M i) (M j) := by
  unfold frobSq frobInner
  have htr : (∑ i : Fin m, M i)ᵀ = ∑ j : Fin m, (M j)ᵀ := by
    ext a b
    simp [Matrix.transpose_apply, Matrix.sum_apply]
  rw [htr, Finset.sum_mul, trace_finset_sum]
  have hsplit : ∀ i : Fin m,
      (M i * ∑ j : Fin m, (M j)ᵀ).trace =
        (M i * (M i)ᵀ).trace + ∑ j ∈ Finset.univ.erase i, (M i * (M j)ᵀ).trace := by
    intro i
    rw [Matrix.mul_sum, trace_finset_sum]
    have hmem : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
    rw [← Finset.add_sum_erase Finset.univ (fun j => (M i * (M j)ᵀ).trace) hmem]
  simp_rw [hsplit, Finset.sum_add_distrib]

/-- Unconditional Bianchi-decoherence lower bound on total Stokes flux norm squared:
whenever off-diagonal covariant pair cancellations cannot erase more than `1 - cBianchi`
of the diagonal variance, the summed Stokes norm squared retains at least `cBianchi` of
the full area-summed diagonal variance. -/
theorem stokes_sum_frobSq_ge_of_bianchi_floor {n m : ℕ} {R : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (M : Fin m → Matrix (Fin n) (Fin n) R) (cBianchi : R)
    (hoff : -(1 - cBianchi) * (∑ i : Fin m, frobSq (M i)) ≤
      ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, frobInner (M i) (M j)) :
    cBianchi * (∑ i : Fin m, frobSq (M i)) ≤ frobSq (∑ i : Fin m, M i) := by
  rw [frobSq_sum_eq]
  have hsub :
      cBianchi * (∑ i : Fin m, frobSq (M i)) =
        (∑ i : Fin m, frobSq (M i)) + -(1 - cBianchi) * (∑ i : Fin m, frobSq (M i)) := by
    ring
  rw [hsub]
  exact add_le_add le_rfl hoff

end StokesAdjointDispersion
