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
# Arbitrary-Rank Classical Type `B`, `C`, and `D` Cartan Quadratic Forms

This module formalizes the symmetrized Cartan quadratic forms for arbitrary-rank classical root
systems of type `B_{n+1}`, `C_{n+2}`, and `D_{n+3}` (including rank-4 `d4CartanForm`), proving
exact sum-of-squares telescoping identities, non-negativity, and positive-definite elimination
over every linearly ordered commutative ring.

## Main results

* `BCDClassicalCartan.bCartanForm_eq_sum_sq`, `bCartanForm_nonneg`, `bCartanForm_eq_zero_iff`.
* `BCDClassicalCartan.cCartanForm_eq_sum_sq`, `cCartanForm_nonneg`, `cCartanForm_eq_zero_iff`.
* `BCDClassicalCartan.dCartanForm_eq_sum_sq`, `dCartanForm_nonneg`, `dCartanForm_eq_zero_iff`.
* `BCDClassicalCartan.d4CartanForm`, `d4CartanForm_eq_zero_iff`.
-/

@[expose] public section

namespace BCDClassicalCartan

section RingForms

variable {R : Type*} [CommRing R]

private theorem sum_castSucc_add_succ {R : Type*} [CommRing R] (n : ℕ)
    (x : Fin (n + 1) → R) :
    (∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2)) + x 0 ^ 2 - x (Fin.last n) ^ 2 =
      ∑ i : Fin n, 2 * x i.castSucc ^ 2 := by
  have h1 : (∑ i : Fin n, x i.castSucc ^ 2) + x (Fin.last n) ^ 2 =
      ∑ i : Fin (n + 1), x i ^ 2 := by
    rw [Fin.sum_univ_castSucc]
  have h2 : x 0 ^ 2 + ∑ i : Fin n, x i.succ ^ 2 =
      ∑ i : Fin (n + 1), x i ^ 2 := by
    rw [Fin.sum_univ_succ]
  have hsplit : ∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2) =
      (∑ i : Fin n, x i.castSucc ^ 2) + ∑ i : Fin n, x i.succ ^ 2 := Finset.sum_add_distrib
  have hdouble : ∑ i : Fin n, 2 * x i.castSucc ^ 2 =
      (∑ i : Fin n, x i.castSucc ^ 2) + ∑ i : Fin n, x i.castSucc ^ 2 := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext i
    ring
  rw [hsplit]
  calc
    (∑ i : Fin n, x i.castSucc ^ 2) + (∑ i : Fin n, x i.succ ^ 2) + x 0 ^ 2 -
        x (Fin.last n) ^ 2 =
      ((∑ i : Fin n, x i.castSucc ^ 2) + (x 0 ^ 2 + ∑ i : Fin n, x i.succ ^ 2)) -
        x (Fin.last n) ^ 2 := by ring
    _ = ((∑ i : Fin n, x i.castSucc ^ 2) +
          ((∑ i : Fin n, x i.castSucc ^ 2) + x (Fin.last n) ^ 2)) -
        x (Fin.last n) ^ 2 := by rw [h2, ← h1]
    _ = ∑ i : Fin n, 2 * x i.castSucc ^ 2 := by rw [hdouble]; ring

/-- Symmetrized type `B_{n+1}` Cartan quadratic form on `Fin (n + 1) → R`. -/
def bCartanForm (n : ℕ) (x : Fin (n + 1) → R) : R :=
  (∑ i : Fin n, 2 * x i.castSucc ^ 2) + x (Fin.last n) ^ 2 -
    ∑ i : Fin n, 2 * x i.castSucc * x i.succ

/-- Sum-of-squares form for `bCartanForm n x`. -/
def bCartanSqSum (n : ℕ) (x : Fin (n + 1) → R) : R :=
  x 0 ^ 2 + ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2

/-- Exact algebraic sum-of-squares identity for arbitrary-rank type `B_{n+1}`. -/
theorem bCartanForm_eq_sum_sq (n : ℕ) (x : Fin (n + 1) → R) :
    bCartanForm n x = bCartanSqSum n x := by
  unfold bCartanForm bCartanSqSum
  have hdiff : ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 =
      (∑ i : Fin n, (x i.castSucc ^ 2 + x i.succ ^ 2)) -
        ∑ i : Fin n, 2 * x i.castSucc * x i.succ := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext i
    ring
  rw [hdiff, ← sum_castSucc_add_succ n x]
  ring

/-- Symmetrized type `C_{n+2}` Cartan quadratic form on `Fin (n + 2) → R`. -/
def cCartanForm (n : ℕ) (x : Fin (n + 2) → R) : R :=
  (∑ i : Fin n, 2 * x i.castSucc.castSucc ^ 2) +
    2 * x (Fin.last n).castSucc ^ 2 + 4 * x (Fin.last (n + 1)) ^ 2 -
    (∑ i : Fin n, 2 * x i.castSucc.castSucc * x i.succ.castSucc) -
    4 * x (Fin.last n).castSucc * x (Fin.last (n + 1))

/-- Sum-of-squares form for `cCartanForm n x`. -/
def cCartanSqSum (n : ℕ) (x : Fin (n + 2) → R) : R :=
  x 0 ^ 2 +
    (∑ i : Fin n, (x i.castSucc.castSucc - x i.succ.castSucc) ^ 2) +
    (x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1))) ^ 2

/-- Exact algebraic sum-of-squares identity for arbitrary-rank type `C_{n+2}`. -/
theorem cCartanForm_eq_sum_sq (n : ℕ) (x : Fin (n + 2) → R) :
    cCartanForm n x = cCartanSqSum n x := by
  let y : Fin (n + 1) → R := fun i => x i.castSucc
  have hb := bCartanForm_eq_sum_sq n y
  have hy_tail :
      4 * x (Fin.last (n + 1)) ^ 2 -
          4 * x (Fin.last n).castSucc * x (Fin.last (n + 1)) +
          y (Fin.last n) ^ 2 =
        (x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1))) ^ 2 := by
    dsimp [y]
    ring
  have hy_form :
      bCartanForm n y +
          (4 * x (Fin.last (n + 1)) ^ 2 -
            4 * x (Fin.last n).castSucc * x (Fin.last (n + 1)) +
            y (Fin.last n) ^ 2) =
        cCartanForm n x := by
    unfold bCartanForm cCartanForm
    dsimp [y]
    ring
  have hy_sq :
      bCartanSqSum n y +
          (x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1))) ^ 2 =
        cCartanSqSum n x := by
    unfold bCartanSqSum cCartanSqSum
    dsimp [y]
  rw [← hy_form, hb, hy_tail, hy_sq]

/-- Symmetrized type `D_{n+3}` Cartan quadratic form on `Fin (n + 3) → R` with chain
`0..n` and symmetric fork leaves `n + 1` and `n + 2` attached at vertex `n`. -/
def dCartanForm (n : ℕ) (x : Fin (n + 3) → R) : R :=
  (∑ i : Fin n, 2 * x i.castSucc.castSucc.castSucc ^ 2) +
    2 * x (Fin.last n).castSucc.castSucc ^ 2 +
    2 * x (Fin.last (n + 1)).castSucc ^ 2 +
    2 * x (Fin.last (n + 2)) ^ 2 -
    (∑ i : Fin n,
      2 * x i.castSucc.castSucc.castSucc * x i.succ.castSucc.castSucc) -
    2 * x (Fin.last n).castSucc.castSucc *
      (x (Fin.last (n + 1)).castSucc + x (Fin.last (n + 2)))

/-- Sum-of-squares form for `dCartanForm n x`. -/
def dCartanSqSum (n : ℕ) (x : Fin (n + 3) → R) : R :=
  x 0 ^ 2 +
    (∑ i : Fin n,
      (x i.castSucc.castSucc.castSucc - x i.succ.castSucc.castSucc) ^ 2) +
    (x (Fin.last n).castSucc.castSucc -
      x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 +
    (x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2

/-- Exact algebraic sum-of-squares identity for arbitrary-rank type `D_{n+3}`. -/
theorem dCartanForm_eq_sum_sq (n : ℕ) (x : Fin (n + 3) → R) :
    dCartanForm n x = dCartanSqSum n x := by
  let y : Fin (n + 1) → R := fun i => x i.castSucc.castSucc
  have hb := bCartanForm_eq_sum_sq n y
  have hy_tail :
      (x (Fin.last n).castSucc.castSucc -
          x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 +
        (x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 =
        y (Fin.last n) ^ 2 +
          2 * x (Fin.last (n + 1)).castSucc ^ 2 +
          2 * x (Fin.last (n + 2)) ^ 2 -
          2 * x (Fin.last n).castSucc.castSucc *
            (x (Fin.last (n + 1)).castSucc + x (Fin.last (n + 2))) := by
    dsimp [y]
    ring
  have hy_form :
      bCartanForm n y +
          (y (Fin.last n) ^ 2 +
            2 * x (Fin.last (n + 1)).castSucc ^ 2 +
            2 * x (Fin.last (n + 2)) ^ 2 -
            2 * x (Fin.last n).castSucc.castSucc *
              (x (Fin.last (n + 1)).castSucc + x (Fin.last (n + 2)))) =
        dCartanForm n x := by
    unfold bCartanForm dCartanForm
    dsimp [y]
    ring
  have hy_sq :
      bCartanSqSum n y +
          ((x (Fin.last n).castSucc.castSucc -
              x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 +
            (x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2) =
        dCartanSqSum n x := by
    unfold bCartanSqSum dCartanSqSum
    dsimp [y]
    ring
  rw [← hy_form, hb, ← hy_tail, hy_sq]

/-- Rank-4 specialization `d4CartanForm` (`n = 1`). -/
abbrev d4CartanForm (x : Fin 4 → R) : R :=
  dCartanForm 1 x

end RingForms

section OrderedForms

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Non-negativity of `bCartanForm n x`. -/
theorem bCartanForm_nonneg (n : ℕ) (x : Fin (n + 1) → F) :
    0 ≤ bCartanForm n x := by
  rw [bCartanForm_eq_sum_sq]
  unfold bCartanSqSum
  have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- Positive-definite elimination for arbitrary-rank type `B_{n+1}`. -/
theorem bCartanForm_eq_zero_iff (n : ℕ) (x : Fin (n + 1) → F) :
    bCartanForm n x = 0 ↔ ∀ i : Fin (n + 1), x i = 0 := by
  constructor
  · intro h
    rw [bCartanForm_eq_sum_sq] at h
    unfold bCartanSqSum at h
    have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
    have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp (by linarith)
    have hsum0 : ∑ i : Fin n, (x i.castSucc - x i.succ) ^ 2 = 0 := by linarith
    have hadj : ∀ i : Fin n, x i.castSucc = x i.succ := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsum0
        i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hrec : ∀ k : ℕ, (hk : k < n + 1) → x ⟨k, hk⟩ = 0 := by
      intro k
      induction k with
      | zero => intro _; exact hx0
      | succ m ih =>
        intro hk
        have hm : m < n := Nat.lt_of_succ_lt_succ hk
        exact (hadj ⟨m, hm⟩).symm.trans (ih (Nat.lt_trans hm (Nat.lt_succ_self n)))
    intro i
    exact hrec i.val i.isLt
  · intro h
    rw [bCartanForm_eq_sum_sq]
    unfold bCartanSqSum
    simp [h]

/-- Non-negativity of `cCartanForm n x`. -/
theorem cCartanForm_nonneg (n : ℕ) (x : Fin (n + 2) → F) :
    0 ≤ cCartanForm n x := by
  rw [cCartanForm_eq_sum_sq]
  unfold cCartanSqSum
  have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc.castSucc - x i.succ.castSucc) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have htail : 0 ≤ (x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1))) ^ 2 := sq_nonneg _
  linarith

/-- Positive-definite elimination for arbitrary-rank type `C_{n+2}`. -/
theorem cCartanForm_eq_zero_iff (n : ℕ) (x : Fin (n + 2) → F) :
    cCartanForm n x = 0 ↔ ∀ i : Fin (n + 2), x i = 0 := by
  constructor
  · intro h
    rw [cCartanForm_eq_sum_sq] at h
    unfold cCartanSqSum at h
    have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
    have hsum : 0 ≤ ∑ i : Fin n, (x i.castSucc.castSucc - x i.succ.castSucc) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have htail : 0 ≤ (x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1))) ^ 2 := sq_nonneg _
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp (by linarith)
    have hsum0 : ∑ i : Fin n, (x i.castSucc.castSucc - x i.succ.castSucc) ^ 2 = 0 := by
      linarith
    have htail_lin : x (Fin.last n).castSucc - 2 * x (Fin.last (n + 1)) = 0 :=
      sq_eq_zero_iff.mp (by linarith)
    have hadj : ∀ i : Fin n, x i.castSucc.castSucc = x i.succ.castSucc := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsum0
        i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hprefix : ∀ k : ℕ, (hk : k < n + 1) → x ⟨k, Nat.lt_succ_of_lt hk⟩ = 0 := by
      intro k
      induction k with
      | zero => intro _; exact hx0
      | succ m ih =>
        intro hk
        have hm : m < n := Nat.lt_of_succ_lt_succ hk
        exact (hadj ⟨m, hm⟩).symm.trans (ih (Nat.lt_trans hm (Nat.lt_succ_self n)))
    have hlast_n : x (Fin.last n).castSucc = 0 := by
      simpa [Fin.last] using hprefix n (Nat.lt_succ_self n)
    have htwo : 2 * x (Fin.last (n + 1)) = 0 := by linarith
    have hxlast : x (Fin.last (n + 1)) = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by positivity)
    intro i
    by_cases hi : i.val < n + 1
    · exact hprefix i.val hi
    · have heq : i.val = n + 1 := by omega
      have hfin : i = Fin.last (n + 1) := Fin.ext heq
      rw [hfin]
      exact hxlast
  · intro h
    rw [cCartanForm_eq_sum_sq]
    unfold cCartanSqSum
    simp [h]

/-- Non-negativity of `dCartanForm n x`. -/
theorem dCartanForm_nonneg (n : ℕ) (x : Fin (n + 3) → F) :
    0 ≤ dCartanForm n x := by
  rw [dCartanForm_eq_sum_sq]
  unfold dCartanSqSum
  have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin n,
      (x i.castSucc.castSucc.castSucc - x i.succ.castSucc.castSucc) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht1 : 0 ≤ (x (Fin.last n).castSucc.castSucc -
      x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 := sq_nonneg _
  have ht2 : 0 ≤ (x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 := sq_nonneg _
  linarith

/-- Positive-definite elimination for arbitrary-rank type `D_{n+3}`. -/
theorem dCartanForm_eq_zero_iff (n : ℕ) (x : Fin (n + 3) → F) :
    dCartanForm n x = 0 ↔ ∀ i : Fin (n + 3), x i = 0 := by
  constructor
  · intro h
    rw [dCartanForm_eq_sum_sq] at h
    unfold dCartanSqSum at h
    have h0 : 0 ≤ x 0 ^ 2 := sq_nonneg _
    have hsum : 0 ≤ ∑ i : Fin n,
        (x i.castSucc.castSucc.castSucc - x i.succ.castSucc.castSucc) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have ht1 : 0 ≤ (x (Fin.last n).castSucc.castSucc -
        x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 := sq_nonneg _
    have ht2 : 0 ≤ (x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2))) ^ 2 := sq_nonneg _
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp (by linarith)
    have hsum0 : ∑ i : Fin n,
        (x i.castSucc.castSucc.castSucc - x i.succ.castSucc.castSucc) ^ 2 = 0 := by
      linarith
    have ht1_lin : x (Fin.last n).castSucc.castSucc -
        x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2)) = 0 :=
      sq_eq_zero_iff.mp (by linarith)
    have ht2_lin : x (Fin.last (n + 1)).castSucc - x (Fin.last (n + 2)) = 0 :=
      sq_eq_zero_iff.mp (by linarith)
    have hadj : ∀ i : Fin n,
        x i.castSucc.castSucc.castSucc = x i.succ.castSucc.castSucc := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsum0
        i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hprefix : ∀ k : ℕ, (hk : k < n + 1) →
        x ⟨k, Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hk)⟩ = 0 := by
      intro k
      induction k with
      | zero => intro _; exact hx0
      | succ m ih =>
        intro hk
        have hm : m < n := Nat.lt_of_succ_lt_succ hk
        exact (hadj ⟨m, hm⟩).symm.trans (ih (Nat.lt_trans hm (Nat.lt_succ_self n)))
    have hlast_n : x (Fin.last n).castSucc.castSucc = 0 := by
      simpa [Fin.last] using hprefix n (Nat.lt_succ_self n)
    have htwo : 2 * x (Fin.last (n + 2)) = 0 := by linarith
    have hxleaf2 : x (Fin.last (n + 2)) = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by positivity)
    have hxleaf1 : x (Fin.last (n + 1)).castSucc = 0 := by linarith
    intro i
    by_cases h1 : i.val < n + 1
    · exact hprefix i.val h1
    · by_cases h2 : i.val = n + 1
      · have hfin : i = (Fin.last (n + 1)).castSucc := Fin.ext h2
        rw [hfin]
        exact hxleaf1
      · have h3 : i.val = n + 2 := by omega
        have hfin : i = Fin.last (n + 2) := Fin.ext h3
        rw [hfin]
        exact hxleaf2
  · intro h
    rw [dCartanForm_eq_sum_sq]
    unfold dCartanSqSum
    simp [h]

/-- Rank-4 specialization `d4CartanForm_eq_zero_iff`. -/
theorem d4CartanForm_eq_zero_iff (x : Fin 4 → F) :
    d4CartanForm x = 0 ↔ ∀ i : Fin 4, x i = 0 :=
  dCartanForm_eq_zero_iff 1 x

end OrderedForms

end BCDClassicalCartan
