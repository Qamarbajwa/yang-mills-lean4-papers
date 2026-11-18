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
public import Mathlib.Tactic.Ring

/-!
# Arbitrary-Rank `Aₙ` and Exceptional `E₆`, `E₇` Cartan Quadratic Forms

This module establishes positive-definite sum-of-squares decompositions and zero-mode
elimination for arbitrary-rank `A_{n+1}` Cartan quadratic forms (`aCartanForm`) via exact
adjacent-difference telescoping over `Fin (n + 1)`, together with rank-6 `E₆` (`60`-scaled)
and rank-7 `E₇` (`420`-scaled) Cholesky factorizations.

## Main results

* `ClassicalAndExceptionalCartan.aCartanForm`: rank `n + 1` tridiagonal Cartan form.
* `ClassicalAndExceptionalCartan.aCartanForm_eq_sum_sq`: exact `Fin` sum-of-squares identity.
* `ClassicalAndExceptionalCartan.aCartanForm_eq_zero_iff`: universal positive definiteness.
* `ClassicalAndExceptionalCartan.e6_sum_of_squares_eq`, `e6CartanForm_eq_zero_iff`.
* `ClassicalAndExceptionalCartan.e7_sum_of_squares_eq`, `e7CartanForm_eq_zero_iff`.
-/

@[expose] public section

namespace ClassicalAndExceptionalCartan

section TypeAN

variable {R : Type*} [CommRing R]

/-- Tridiagonal Cartan quadratic form of type `A_{n+1}` on `Fin (n + 1) → R`. -/
def aCartanForm (n : ℕ) (x : Fin (n + 1) → R) : R :=
  (∑ i : Fin (n + 1), 2 * x i ^ 2) - ∑ i : Fin n, 2 * x i.castSucc * x i.succ

/-- Sum-of-squares decomposition of `aCartanForm n x`. -/
def aCartanSqSum (n : ℕ) (x : Fin (n + 1) → R) : R :=
  x 0 ^ 2 + (∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2) + x (Fin.last n) ^ 2

private theorem sum_castSucc_add_succ {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin (n + 1) → R) :
    (∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2)) + x 0 ^ 2 + x (Fin.last n) ^ 2 =
      ∑ i : Fin (n + 1), 2 * x i ^ 2 := by
  have h1 : (∑ i : Fin n, x i.castSucc ^ 2) + x (Fin.last n) ^ 2 =
      ∑ i : Fin (n + 1), x i ^ 2 := by
    rw [Fin.sum_univ_castSucc]
  have h2 : x 0 ^ 2 + ∑ i : Fin n, x i.succ ^ 2 =
      ∑ i : Fin (n + 1), x i ^ 2 := by
    rw [Fin.sum_univ_succ]
  have hsplit : ∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2) =
      (∑ i : Fin n, x i.castSucc ^ 2) + ∑ i : Fin n, x i.succ ^ 2 := Finset.sum_add_distrib
  have hdouble : ∑ i : Fin (n + 1), 2 * x i ^ 2 =
      (∑ i : Fin (n + 1), x i ^ 2) + ∑ i : Fin (n + 1), x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext i
    ring
  calc
    (∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2)) + x 0 ^ 2 + x (Fin.last n) ^ 2
        = ((∑ i : Fin n, x i.castSucc ^ 2) + x (Fin.last n) ^ 2) +
            (x 0 ^ 2 + ∑ i : Fin n, x i.succ ^ 2) := by
          rw [hsplit]
          ring
    _ = (∑ i : Fin (n + 1), x i ^ 2) + ∑ i : Fin (n + 1), x i ^ 2 := by rw [h1, h2]
    _ = ∑ i : Fin (n + 1), 2 * x i ^ 2 := hdouble.symm

/-- Exact algebraic equality between the tridiagonal `A_{n+1}` Cartan form and its
positive-definite sum-of-squares representation for every rank `n`. -/
theorem aCartanForm_eq_sum_sq (n : ℕ) (x : Fin (n + 1) → R) :
    aCartanForm n x = aCartanSqSum n x := by
  unfold aCartanForm aCartanSqSum
  have hdiff : ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 =
      (∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2)) -
        ∑ i : Fin n, 2 * x i.castSucc * x i.succ := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext i
    ring
  rw [hdiff, ← sum_castSucc_add_succ n x]
  ring

theorem aCartanForm_nonneg {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : ℕ) (x : Fin (n + 1) → F) :
    0 ≤ aCartanForm n x := by
  rw [aCartanForm_eq_sum_sq]
  unfold aCartanSqSum
  have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hlast : 0 ≤ x (Fin.last n) ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- Positive-definite elimination for `A_{n+1}` at any rank `n`:
`aCartanForm n x = 0 ↔ ∀ i, x i = 0`. -/
theorem aCartanForm_eq_zero_iff {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] (n : ℕ) (x : Fin (n + 1) → F) :
    aCartanForm n x = 0 ↔ ∀ i : Fin (n + 1), x i = 0 := by
  constructor
  · intro h
    rw [aCartanForm_eq_sum_sq] at h
    unfold aCartanSqSum at h
    have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
    have hlast : 0 ≤ x (Fin.last n) ^ 2 := sq_nonneg _
    have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hx0_sq : x 0 ^ 2 = 0 := by linarith
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp hx0_sq
    have hsum_zero : ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 = 0 := by linarith
    have hadj : ∀ i : Fin n, x i.castSucc = x i.succ := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsum_zero
        i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hrec : ∀ k : ℕ, (hk : k < n + 1) → x ⟨k, hk⟩ = 0 := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact hx0
      | succ m ih =>
        intro hk
        have hm : m < n := Nat.lt_of_succ_lt_succ hk
        have hstep := hadj ⟨m, hm⟩
        have ih_m := ih (Nat.lt_trans hm (Nat.lt_succ_self n))
        exact hstep.symm.trans ih_m
    intro i
    exact hrec i.val i.isLt
  · intro h
    rw [aCartanForm_eq_sum_sq]
    unfold aCartanSqSum
    simp [h]

end TypeAN

section ExceptionalE6E7

variable {R : Type*} [CommRing R]

/-- Rank-6 `E₆` Cartan quadratic form (`0-1-2-3-4` with `5` attached to `2`). -/
def e6CartanForm (x₀ x₁ x₂ x₃ x₄ x₅ : R) : R :=
  2 * x₀ ^ 2 - 2 * x₀ * x₁ + 2 * x₁ ^ 2 - 2 * x₁ * x₂ +
  2 * x₂ ^ 2 - 2 * x₂ * x₃ - 2 * x₂ * x₅ +
  2 * x₃ ^ 2 - 2 * x₃ * x₄ + 2 * x₄ ^ 2 + 2 * x₅ ^ 2

/-- Rank-7 `E₇` Cartan quadratic form (`0-1-2-3-4-5` with `6` attached to `3`). -/
def e7CartanForm (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : R) : R :=
  2 * x₀ ^ 2 - 2 * x₀ * x₁ + 2 * x₁ ^ 2 - 2 * x₁ * x₂ +
  2 * x₂ ^ 2 - 2 * x₂ * x₃ + 2 * x₃ ^ 2 - 2 * x₃ * x₄ - 2 * x₃ * x₆ +
  2 * x₄ ^ 2 - 2 * x₄ * x₅ + 2 * x₅ ^ 2 + 2 * x₆ ^ 2

/-- Exact `60`-scaled Cholesky sum-of-squares factorization for `E₆`. -/
theorem e6_sum_of_squares_eq (x₀ x₁ x₂ x₃ x₄ x₅ : R) :
    60 * e6CartanForm x₀ x₁ x₂ x₃ x₄ x₅ =
      30 * (2 * x₀ - x₁) ^ 2 + 10 * (3 * x₁ - 2 * x₂) ^ 2 +
      5 * (4 * x₂ - 3 * x₃ - 3 * x₅) ^ 2 +
      3 * (5 * x₃ - 4 * x₄ - 3 * x₅) ^ 2 +
      18 * (2 * x₄ - x₅) ^ 2 + 30 * x₅ ^ 2 := by
  unfold e6CartanForm
  ring

/-- Exact `420`-scaled Cholesky sum-of-squares factorization for `E₇`. -/
theorem e7_sum_of_squares_eq (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : R) :
    420 * e7CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ =
      210 * (2 * x₀ - x₁) ^ 2 + 70 * (3 * x₁ - 2 * x₂) ^ 2 +
      35 * (4 * x₂ - 3 * x₃) ^ 2 + 21 * (5 * x₃ - 4 * x₄ - 4 * x₆) ^ 2 +
      14 * (6 * x₄ - 5 * x₅ - 4 * x₆) ^ 2 +
      10 * (7 * x₅ - 4 * x₆) ^ 2 + 120 * x₆ ^ 2 := by
  unfold e7CartanForm
  ring

section OrderedE6E7

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Positive-definite zero-mode elimination for `E₆`. -/
theorem e6CartanForm_eq_zero_iff (x₀ x₁ x₂ x₃ x₄ x₅ : F) :
    e6CartanForm x₀ x₁ x₂ x₃ x₄ x₅ = 0 ↔
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0 := by
  constructor
  · intro h
    have h60 :
        30 * (2 * x₀ - x₁) ^ 2 + 10 * (3 * x₁ - 2 * x₂) ^ 2 +
        5 * (4 * x₂ - 3 * x₃ - 3 * x₅) ^ 2 +
        3 * (5 * x₃ - 4 * x₄ - 3 * x₅) ^ 2 +
        18 * (2 * x₄ - x₅) ^ 2 + 30 * x₅ ^ 2 = 0 := by
      rw [← e6_sum_of_squares_eq, h, mul_zero]
    have p0 : 0 ≤ 30 * (2 * x₀ - x₁) ^ 2 := by positivity
    have p1 : 0 ≤ 10 * (3 * x₁ - 2 * x₂) ^ 2 := by positivity
    have p2 : 0 ≤ 5 * (4 * x₂ - 3 * x₃ - 3 * x₅) ^ 2 := by positivity
    have p3 : 0 ≤ 3 * (5 * x₃ - 4 * x₄ - 3 * x₅) ^ 2 := by positivity
    have p4 : 0 ≤ 18 * (2 * x₄ - x₅) ^ 2 := by positivity
    have p5 : 0 ≤ 30 * x₅ ^ 2 := by positivity
    have z5 : x₅ ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (30 : F) * x₅ ^ 2 = 0)).resolve_left (by positivity)
    have hx5 : x₅ = 0 := sq_eq_zero_iff.mp z5
    have z4 : (2 * x₄ - x₅) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (18 : F) * _ = 0)).resolve_left (by positivity)
    have hx4_lin : 2 * x₄ - x₅ = 0 := sq_eq_zero_iff.mp z4
    have hx4 : x₄ = 0 :=
      (mul_eq_zero.mp (by linarith : (2 : F) * x₄ = 0)).resolve_left (by positivity)
    have z3 : (5 * x₃ - 4 * x₄ - 3 * x₅) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (3 : F) * _ = 0)).resolve_left (by positivity)
    have hx3_lin : 5 * x₃ - 4 * x₄ - 3 * x₅ = 0 := sq_eq_zero_iff.mp z3
    have hx3 : x₃ = 0 :=
      (mul_eq_zero.mp (by linarith : (5 : F) * x₃ = 0)).resolve_left (by positivity)
    have z2 : (4 * x₂ - 3 * x₃ - 3 * x₅) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (5 : F) * _ = 0)).resolve_left (by positivity)
    have hx2_lin : 4 * x₂ - 3 * x₃ - 3 * x₅ = 0 := sq_eq_zero_iff.mp z2
    have hx2 : x₂ = 0 :=
      (mul_eq_zero.mp (by linarith : (4 : F) * x₂ = 0)).resolve_left (by positivity)
    have z1 : (3 * x₁ - 2 * x₂) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (10 : F) * _ = 0)).resolve_left (by positivity)
    have hx1_lin : 3 * x₁ - 2 * x₂ = 0 := sq_eq_zero_iff.mp z1
    have hx1 : x₁ = 0 :=
      (mul_eq_zero.mp (by linarith : (3 : F) * x₁ = 0)).resolve_left (by positivity)
    have z0 : (2 * x₀ - x₁) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (30 : F) * _ = 0)).resolve_left (by positivity)
    have hx0_lin : 2 * x₀ - x₁ = 0 := sq_eq_zero_iff.mp z0
    have hx0 : x₀ = 0 :=
      (mul_eq_zero.mp (by linarith : (2 : F) * x₀ = 0)).resolve_left (by positivity)
    exact ⟨hx0, hx1, hx2, hx3, hx4, hx5⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    unfold e6CartanForm
    ring

/-- Positive-definite zero-mode elimination for `E₇`. -/
theorem e7CartanForm_eq_zero_iff (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : F) :
    e7CartanForm x₀ x₁ x₂ x₃ x₄ x₅ x₆ = 0 ↔
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₅ = 0 ∧ x₆ = 0 := by
  constructor
  · intro h
    have h420 :
        210 * (2 * x₀ - x₁) ^ 2 + 70 * (3 * x₁ - 2 * x₂) ^ 2 +
        35 * (4 * x₂ - 3 * x₃) ^ 2 + 21 * (5 * x₃ - 4 * x₄ - 4 * x₆) ^ 2 +
        14 * (6 * x₄ - 5 * x₅ - 4 * x₆) ^ 2 +
        10 * (7 * x₅ - 4 * x₆) ^ 2 + 120 * x₆ ^ 2 = 0 := by
      rw [← e7_sum_of_squares_eq, h, mul_zero]
    have p0 : 0 ≤ 210 * (2 * x₀ - x₁) ^ 2 := by positivity
    have p1 : 0 ≤ 70 * (3 * x₁ - 2 * x₂) ^ 2 := by positivity
    have p2 : 0 ≤ 35 * (4 * x₂ - 3 * x₃) ^ 2 := by positivity
    have p3 : 0 ≤ 21 * (5 * x₃ - 4 * x₄ - 4 * x₆) ^ 2 := by positivity
    have p4 : 0 ≤ 14 * (6 * x₄ - 5 * x₅ - 4 * x₆) ^ 2 := by positivity
    have p5 : 0 ≤ 10 * (7 * x₅ - 4 * x₆) ^ 2 := by positivity
    have p6 : 0 ≤ 120 * x₆ ^ 2 := by positivity
    have z6 : x₆ ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (120 : F) * x₆ ^ 2 = 0)).resolve_left (by positivity)
    have hx6 : x₆ = 0 := sq_eq_zero_iff.mp z6
    have z5 : (7 * x₅ - 4 * x₆) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (10 : F) * _ = 0)).resolve_left (by positivity)
    have hx5_lin : 7 * x₅ - 4 * x₆ = 0 := sq_eq_zero_iff.mp z5
    have hx5 : x₅ = 0 :=
      (mul_eq_zero.mp (by linarith : (7 : F) * x₅ = 0)).resolve_left (by positivity)
    have z4 : (6 * x₄ - 5 * x₅ - 4 * x₆) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (14 : F) * _ = 0)).resolve_left (by positivity)
    have hx4_lin : 6 * x₄ - 5 * x₅ - 4 * x₆ = 0 := sq_eq_zero_iff.mp z4
    have hx4 : x₄ = 0 :=
      (mul_eq_zero.mp (by linarith : (6 : F) * x₄ = 0)).resolve_left (by positivity)
    have z3 : (5 * x₃ - 4 * x₄ - 4 * x₆) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (21 : F) * _ = 0)).resolve_left (by positivity)
    have hx3_lin : 5 * x₃ - 4 * x₄ - 4 * x₆ = 0 := sq_eq_zero_iff.mp z3
    have hx3 : x₃ = 0 :=
      (mul_eq_zero.mp (by linarith : (5 : F) * x₃ = 0)).resolve_left (by positivity)
    have z2 : (4 * x₂ - 3 * x₃) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (35 : F) * _ = 0)).resolve_left (by positivity)
    have hx2_lin : 4 * x₂ - 3 * x₃ = 0 := sq_eq_zero_iff.mp z2
    have hx2 : x₂ = 0 :=
      (mul_eq_zero.mp (by linarith : (4 : F) * x₂ = 0)).resolve_left (by positivity)
    have z1 : (3 * x₁ - 2 * x₂) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (70 : F) * _ = 0)).resolve_left (by positivity)
    have hx1_lin : 3 * x₁ - 2 * x₂ = 0 := sq_eq_zero_iff.mp z1
    have hx1 : x₁ = 0 :=
      (mul_eq_zero.mp (by linarith : (3 : F) * x₁ = 0)).resolve_left (by positivity)
    have z0 : (2 * x₀ - x₁) ^ 2 = 0 :=
      (mul_eq_zero.mp (by linarith : (210 : F) * _ = 0)).resolve_left (by positivity)
    have hx0_lin : 2 * x₀ - x₁ = 0 := sq_eq_zero_iff.mp z0
    have hx0 : x₀ = 0 :=
      (mul_eq_zero.mp (by linarith : (2 : F) * x₀ = 0)).resolve_left (by positivity)
    exact ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    unfold e7CartanForm
    ring

end OrderedE6E7

end ExceptionalE6E7

end ClassicalAndExceptionalCartan
