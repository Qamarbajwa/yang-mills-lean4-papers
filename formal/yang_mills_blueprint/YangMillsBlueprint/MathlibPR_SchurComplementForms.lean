/-
Copyright (c) 2026 Formal Verification Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Verification Authors

! This file was extracted as a self-contained candidate for Mathlib.
-/

/-!
# Schur Complement Quadratic Identities and Exact Rational Bounds

This module provides self-contained, unconditional algebraic identities:
1. The exact completion-of-the-square identity for 2x2 block quadratic forms.
2. Strict block coercivity from positive pivots and positive Schur determinant.
3. Decidable exact positive rational arithmetic pairs and geometric tail bounds.
-/

namespace MathlibPR.LinearAlgebra

/-- Evaluates the quadratic form Q(z_b, z_c) = a_cc*z_c^2 - 2*a_cb*z_c*z_b + a_bb*z_b^2. -/
def twoBlockQuadForm (a_bb a_cb a_cc z_b z_c : Int) : Int :=
  a_cc * (z_c * z_c) - 2 * a_cb * z_c * z_b + a_bb * (z_b * z_b)

/-- Scalar determinant of the Schur complement block: delta = a_cc * a_bb - a_cb^2. -/
def twoBlockSchurDet (a_bb a_cb a_cc : Int) : Int :=
  a_cc * a_bb - a_cb * a_cb

/--
Theorem: Multiplied by the pivot `a_bb`, the 2x2 block quadratic form decomposes
into the Schur complement determinant term plus a non-negative squared residual:
  delta * z_c^2 + (a_bb * z_b - a_cb * z_c)^2 = a_bb * Q(z_b, z_c).
-/
theorem schur_complement_quadratic_identity (a_bb a_cb a_cc z_b z_c : Int) :
    twoBlockSchurDet a_bb a_cb a_cc * (z_c * z_c) +
        (a_bb * z_b - a_cb * z_c) * (a_bb * z_b - a_cb * z_c) =
      a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
  unfold twoBlockSchurDet twoBlockQuadForm
  have h1 : a_cc * a_bb * (z_c * z_c) = a_bb * (a_cc * (z_c * z_c)) := by
    rw [Int.mul_comm a_cc a_bb, Int.mul_assoc]
  have hcross1 : a_bb * z_b * (a_cb * z_c) = a_bb * a_cb * z_c * z_b := by
    rw [Int.mul_assoc a_bb z_b (a_cb * z_c), Int.mul_left_comm z_b a_cb z_c,
        Int.mul_comm z_b z_c, ← Int.mul_assoc, ← Int.mul_assoc]
  have hcross2 : a_cb * z_c * (a_bb * z_b) = a_bb * a_cb * z_c * z_b := by
    rw [Int.mul_comm (a_cb * z_c) (a_bb * z_b)]
    exact hcross1
  have hsqb : a_bb * z_b * (a_bb * z_b) = a_bb * (a_bb * (z_b * z_b)) := by
    rw [Int.mul_assoc, Int.mul_left_comm z_b a_bb z_b, ← Int.mul_assoc]
  have hsqc : a_cb * z_c * (a_cb * z_c) = a_cb * a_cb * (z_c * z_c) := by
    rw [Int.mul_assoc, Int.mul_left_comm z_c a_cb z_c, ← Int.mul_assoc]
  have h2rhs : a_bb * (2 * a_cb * z_c * z_b) = 2 * (a_bb * a_cb * z_c * z_b) := by
    rw [← Int.mul_assoc a_bb (2 * a_cb * z_c) z_b,
        ← Int.mul_assoc a_bb (2 * a_cb) z_c,
        ← Int.mul_assoc a_bb 2 a_cb,
        Int.mul_comm a_bb 2,
        Int.mul_assoc 2 a_bb a_cb,
        Int.mul_assoc 2 (a_bb * a_cb) z_c,
        Int.mul_assoc 2 (a_bb * a_cb * z_c) z_b]
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add]
  rw [h1, hcross1, hcross2, hsqb, hsqc, h2rhs]
  omega

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with hx | hx
  · exact Int.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by omega
    have hsq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    rw [← hsq]
    exact Int.mul_nonneg hnx hnx

private theorem int_sq_pos_of_ne_zero {x : Int} (hne : x ≠ 0) : 0 < x * x := by
  have hnn : 0 ≤ x * x := int_sq_nonneg x
  rcases Int.lt_trichotomy x 0 with hlt | heq | hgt
  · have hnx : 0 < -x := by omega
    have hsq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    rw [← hsq]
    exact Int.mul_pos hnx hnx
  · exact absurd heq hne
  · exact Int.mul_pos hgt hgt

/--
Theorem: If the pivot `0 < a_bb` and Schur determinant `0 < twoBlockSchurDet a_bb a_cb a_cc`,
then for every non-zero vector (z_b, z_c) the quadratic form is strictly positive.
-/
theorem schur_coercivity_from_block_pivots
    (a_bb a_cb a_cc z_b z_c : Int)
    (hbb : 0 < a_bb)
    (hschur : 0 < twoBlockSchurDet a_bb a_cb a_cc)
    (hnz : z_b ≠ 0 ∨ z_c ≠ 0) :
    0 < twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
  have hid := schur_complement_quadratic_identity a_bb a_cb a_cc z_b z_c
  have hr_nn : 0 ≤ (a_bb * z_b - a_cb * z_c) * (a_bb * z_b - a_cb * z_c) :=
    int_sq_nonneg (a_bb * z_b - a_cb * z_c)
  have hprod_pos : 0 < a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
    rw [← hid]
    by_cases hzc : z_c = 0
    · subst hzc
      have hzb : z_b ≠ 0 := by
        cases hnz with
        | inl h => exact h
        | inr h => exact absurd rfl h
      have hbb_ne : a_bb ≠ 0 := by omega
      have hzb_ne : a_bb * z_b ≠ 0 := Int.mul_ne_zero hbb_ne hzb
      have hr_pos : 0 < (a_bb * z_b - a_cb * 0) * (a_bb * z_b - a_cb * 0) := by
        simp only [Int.mul_zero, Int.sub_zero]
        exact int_sq_pos_of_ne_zero hzb_ne
      have h0 : twoBlockSchurDet a_bb a_cb a_cc * (0 * 0) = 0 := by
        simp only [Int.mul_zero]
      rw [h0]
      omega
    · have hz_pos : 0 < z_c * z_c := int_sq_pos_of_ne_zero hzc
      have ht1 : 0 < twoBlockSchurDet a_bb a_cb a_cc * (z_c * z_c) :=
        Int.mul_pos hschur hz_pos
      omega
  by_cases hgt : 0 < twoBlockQuadForm a_bb a_cb a_cc z_b z_c
  · exact hgt
  · have hle : twoBlockQuadForm a_bb a_cb a_cc z_b z_c ≤ 0 := by omega
    have hnp : a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle
    omega

end MathlibPR.LinearAlgebra

namespace MathlibPR.Data.RationalPairs

/-- Exact non-negative rational pair with positive denominator. -/
structure RatPair where
  num : Nat
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace RatPair

def ofNat (n : Nat) : RatPair := ⟨n, 1, by omega⟩

def add (a b : RatPair) : RatPair :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def mul (a b : RatPair) : RatPair :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def pow4 (a : RatPair) : RatPair :=
  mul (mul a a) (mul a a)

def eqv (a b : RatPair) : Prop := a.num * b.den = b.num * a.den

def lt (a b : RatPair) : Prop := a.num * b.den < b.num * a.den

def le (a b : RatPair) : Prop := a.num * b.den ≤ b.num * a.den

instance (a b : RatPair) : Decidable (lt a b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

instance (a b : RatPair) : Decidable (le a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

instance (a b : RatPair) : Decidable (eqv a b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

end RatPair

open RatPair

/-- Reduced exact total geometric cluster weight. -/
def totalGeometricClusterWeight : RatPair :=
  ⟨19623589247123587350642100903, 19979987798223270175317603840, by omega⟩

/-- Exact positive contraction margin 1 - totalGeometricClusterWeight. -/
def geometricContractionMargin : RatPair :=
  ⟨356398551099682824675502937, 19979987798223270175317603840, by omega⟩

/-- Theorem: Total geometric cluster weight is strictly less than 1. -/
theorem geometric_cluster_weight_lt_one :
    RatPair.lt totalGeometricClusterWeight (RatPair.ofNat 1) := by
  decide

/-- Theorem: Contraction margin strictly exceeds 1 / 57. -/
theorem geometric_contraction_margin_gt_one_57th :
    RatPair.lt ⟨1, 57, by omega⟩ geometricContractionMargin := by
  decide

/-- Theorem: Exact conservation: totalGeometricClusterWeight + margin = 1. -/
theorem geometric_margin_conservation :
    totalGeometricClusterWeight.num + geometricContractionMargin.num =
      totalGeometricClusterWeight.den := by
  decide

end MathlibPR.Data.RationalPairs
