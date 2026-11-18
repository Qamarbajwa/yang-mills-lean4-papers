/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Spatial-Slice Markov Tensorization & Dimension-Uniform Schur Spectral Contraction

Non-Hessian spectral-gap route for `WP1-B` / `WP3-C`, replacing static tree-gauge cotree
Hessian inversion (falsified by `O(L²)` ratio blowup) with finite-range spatial-slice
transfer bounds independent of spatial lattice volume `n ~ (L / b)³`:

1. `weighted_cs_sq_le`: algebraic weighted Cauchy–Schwarz over any linearly ordered field `K`.
2. `schur_symmetric_operator_sq_le`: for symmetric `M : Fin n → Fin n → K` with `ℓ¹` slice row
   bound `∑ j, |M i j| ≤ ρ`, `∑ i, (∑ j, M i j * v j) ^ 2 ≤ ρ ^ 2 * ∑ j, v j ^ 2`.
3. `rayleigh_abs_le_of_schur`: symmetric Rayleigh bound
   `|∑ i, v i * (∑ j, M i j * v j)| ≤ ρ * ‖v‖²`.
4. `slice_tensor_contraction_le`: perturbative slice-block tensorization `|⟨v, (M₀ + E) v⟩| ≤
   (η + ρE) * ‖v‖²` uniformly in spatial grid dimension `n`.
-/

@[expose] public section

namespace SliceMarkovTensorization

/-- Algebraic weighted Cauchy–Schwarz inequality for non-negative weights `w i ≥ 0` over any
linearly ordered field `K`: `(∑ i, w i * a i) ^ 2 ≤ (∑ i, w i) * (∑ i, w i * a i ^ 2)`. -/
theorem weighted_cs_sq_le {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (w a : Fin n → K) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Fin n, w i * a i) ^ 2 ≤ (∑ i : Fin n, w i) * (∑ i : Fin n, w i * a i ^ 2) := by
  have hnonneg : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, w i * w j * (a i - a j) ^ 2 := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg (a i - a j))
  have hexpand :
      (∑ i : Fin n, ∑ j : Fin n, w i * w j * (a i - a j) ^ 2) =
        2 * (∑ i : Fin n, w i) * (∑ i : Fin n, w i * a i ^ 2) -
          2 * (∑ i : Fin n, w i * a i) ^ 2 := by
    have hterm : ∀ i j : Fin n,
        w i * w j * (a i - a j) ^ 2 =
          (w i * a i ^ 2) * w j + w i * (w j * a j ^ 2) - 2 * ((w i * a i) * (w j * a j)) := by
      intro i j
      ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

/-- Symmetric `ℓ²` operator-norm bound via Schur's test: if `M` is symmetric (`M i j = M j i`)
and every spatial slice row has `ℓ¹` influence sum `∑ j, |M i j| ≤ ρ`, then the `ℓ²` operator
norm squared is bounded by `ρ ^ 2` independently of the spatial dimension `n`. -/
theorem schur_symmetric_operator_sq_le {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : Fin n → Fin n → K) (v : Fin n → K) {ρ : K}
    (hsym : ∀ i j, M i j = M j i)
    (hρ0 : 0 ≤ ρ)
    (hrow : ∀ i, ∑ j : Fin n, |M i j| ≤ ρ) :
    ∑ i : Fin n, (∑ j : Fin n, M i j * v j) ^ 2 ≤ ρ ^ 2 * ∑ j : Fin n, v j ^ 2 := by
  have hpoint : ∀ i : Fin n,
      (∑ j : Fin n, M i j * v j) ^ 2 ≤ ρ * ∑ j : Fin n, |M i j| * v j ^ 2 := by
    intro i
    have habs : |∑ j : Fin n, M i j * v j| ≤ ∑ j : Fin n, |M i j| * |v j| := by
      calc
        |∑ j : Fin n, M i j * v j| ≤ ∑ j : Fin n, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |M i j| * |v j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact abs_mul (M i j) (v j)
    have hsq1 : (∑ j : Fin n, M i j * v j) ^ 2 ≤ (∑ j : Fin n, |M i j| * |v j|) ^ 2 := by
      rw [← sq_abs (∑ j : Fin n, M i j * v j)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hcs := weighted_cs_sq_le (fun j => |M i j|) (fun j => |v j|) (fun j => abs_nonneg _)
    have hsqabs : (fun j => |M i j| * |v j| ^ 2) = fun j => |M i j| * v j ^ 2 := by
      funext j
      rw [sq_abs]
    rw [hsqabs] at hcs
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, |M i j| * v j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hrow_mul : (∑ j : Fin n, |M i j|) * (∑ j : Fin n, |M i j| * v j ^ 2) ≤
        ρ * ∑ j : Fin n, |M i j| * v j ^ 2 :=
      mul_le_mul_of_nonneg_right (hrow i) hsum_nonneg
    exact hsq1.trans (hcs.trans hrow_mul)
  have hsum_i :
      ∑ i : Fin n, (∑ j : Fin n, M i j * v j) ^ 2 ≤
        ρ * ∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2 := by
    calc
      ∑ i : Fin n, (∑ j : Fin n, M i j * v j) ^ 2
          ≤ ∑ i : Fin n, ρ * ∑ j : Fin n, |M i j| * v j ^ 2 :=
            Finset.sum_le_sum fun i _ => hpoint i
      _ = ρ * ∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2 := by
            rw [← Finset.mul_sum]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2) =
        ∑ j : Fin n, v j ^ 2 * ∑ i : Fin n, |M j i| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsym i j, mul_comm]
  have hcol :
      ∑ j : Fin n, v j ^ 2 * ∑ i : Fin n, |M j i| ≤ ρ * ∑ j : Fin n, v j ^ 2 := by
    calc
      ∑ j : Fin n, v j ^ 2 * ∑ i : Fin n, |M j i|
          ≤ ∑ j : Fin n, v j ^ 2 * ρ := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg _)
      _ = ρ * ∑ j : Fin n, v j ^ 2 := by
            rw [← Finset.sum_mul, mul_comm]
  calc
    ∑ i : Fin n, (∑ j : Fin n, M i j * v j) ^ 2
        ≤ ρ * ∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2 := hsum_i
    _ = ρ * ∑ j : Fin n, v j ^ 2 * ∑ i : Fin n, |M j i| := by rw [hswap]
    _ ≤ ρ * (ρ * ∑ j : Fin n, v j ^ 2) := mul_le_mul_of_nonneg_left hcol hρ0
    _ = ρ ^ 2 * ∑ j : Fin n, v j ^ 2 := by ring

/-- Symmetric Rayleigh quotient bound from `ℓ¹` slice influence row sums:
`|∑ i, v i * (∑ j, M i j * v j)| ≤ ρ * ∑ j, v j ^ 2`. -/
theorem rayleigh_abs_le_of_schur {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : Fin n → Fin n → K) (v : Fin n → K) {ρ : K}
    (hsym : ∀ i j, M i j = M j i)
    (hrow : ∀ i, ∑ j : Fin n, |M i j| ≤ ρ) :
    |∑ i : Fin n, v i * ∑ j : Fin n, M i j * v j| ≤ ρ * ∑ j : Fin n, v j ^ 2 := by
  have hstep1 :
      |∑ i : Fin n, v i * ∑ j : Fin n, M i j * v j| ≤
        ∑ i : Fin n, ∑ j : Fin n, |M i j| * |v i * v j| := by
    have hrew :
        (∑ i : Fin n, v i * ∑ j : Fin n, M i j * v j) =
          ∑ i : Fin n, ∑ j : Fin n, M i j * (v i * v j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hrew]
    calc
      |∑ i : Fin n, ∑ j : Fin n, M i j * (v i * v j)|
          ≤ ∑ i : Fin n, |∑ j : Fin n, M i j * (v i * v j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |M i j| * |v i * v j| := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc
              |∑ j : Fin n, M i j * (v i * v j)|
                  ≤ ∑ j : Fin n, |M i j * (v i * v j)| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j : Fin n, |M i j| * |v i * v j| := by
                    refine Finset.sum_congr rfl fun j _ => abs_mul _ _
  have hstep2 :
      2 * (∑ i : Fin n, ∑ j : Fin n, |M i j| * |v i * v j|) ≤
        2 * (ρ * ∑ i : Fin n, v i ^ 2) := by
    have hpair : ∀ i j : Fin n,
        2 * (|M i j| * |v i * v j|) ≤ |M i j| * v i ^ 2 + |M i j| * v j ^ 2 := by
      intro i j
      have hsq : 0 ≤ (|v i| - |v j|) ^ 2 := sq_nonneg _
      have hamgm : 2 * |v i * v j| ≤ v i ^ 2 + v j ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_abs (v i), sq_abs (v j)]
      calc
        2 * (|M i j| * |v i * v j|) = |M i j| * (2 * |v i * v j|) := by ring
        _ ≤ |M i j| * (v i ^ 2 + v j ^ 2) := mul_le_mul_of_nonneg_left hamgm (abs_nonneg _)
        _ = |M i j| * v i ^ 2 + |M i j| * v j ^ 2 := by ring
    have hsum2 :
        2 * (∑ i : Fin n, ∑ j : Fin n, |M i j| * |v i * v j|) ≤
          (∑ i : Fin n, ∑ j : Fin n, |M i j| * v i ^ 2) +
            (∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => hpair i j
    have hleft : ∑ i : Fin n, ∑ j : Fin n, |M i j| * v i ^ 2 ≤ ρ * ∑ i : Fin n, v i ^ 2 := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, |M i j| * v i ^ 2
            = ∑ i : Fin n, (∑ j : Fin n, |M i j|) * v i ^ 2 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_mul]
        _ ≤ ∑ i : Fin n, ρ * v i ^ 2 := by
              refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
        _ = ρ * ∑ i : Fin n, v i ^ 2 := by rw [← Finset.mul_sum]
    have hright : ∑ i : Fin n, ∑ j : Fin n, |M i j| * v j ^ 2 ≤ ρ * ∑ j : Fin n, v j ^ 2 := by
      rw [Finset.sum_comm]
      calc
        ∑ j : Fin n, ∑ i : Fin n, |M i j| * v j ^ 2
            = ∑ j : Fin n, (∑ i : Fin n, |M j i|) * v j ^ 2 := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← Finset.sum_mul]
              congr 1
              exact Finset.sum_congr rfl fun i _ => by rw [hsym i j]
        _ ≤ ∑ j : Fin n, ρ * v j ^ 2 := by
              refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hrow j) (sq_nonneg _)
        _ = ρ * ∑ j : Fin n, v j ^ 2 := by rw [← Finset.mul_sum]
    linarith
  linarith

/-- Dimension-uniform perturbative slice-tensorization contraction: if single-block transfer `M₀`
satisfies `|⟨v, M₀ v⟩| ≤ η * ‖v‖²` and symmetric inter-slice coupling `E` has `ℓ¹` row-sum
bound `ρE`, then `|⟨v, (M₀ + E) v⟩| ≤ (η + ρE) * ‖v‖²` for every spatial grid size `n`. -/
theorem slice_tensor_contraction_le {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M₀ E : Fin n → Fin n → K) (v : Fin n → K) {η ρE : K}
    (hM₀ : |∑ i : Fin n, v i * ∑ j : Fin n, M₀ i j * v j| ≤ η * ∑ j : Fin n, v j ^ 2)
    (hsymE : ∀ i j, E i j = E j i)
    (hrowE : ∀ i, ∑ j : Fin n, |E i j| ≤ ρE) :
    |∑ i : Fin n, v i * ∑ j : Fin n, (M₀ i j + E i j) * v j| ≤
      (η + ρE) * ∑ j : Fin n, v j ^ 2 := by
  have hsplit :
      (∑ i : Fin n, v i * ∑ j : Fin n, (M₀ i j + E i j) * v j) =
        (∑ i : Fin n, v i * ∑ j : Fin n, M₀ i j * v j) +
          (∑ i : Fin n, v i * ∑ j : Fin n, E i j * v j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  have hE := rayleigh_abs_le_of_schur E v hsymE hrowE
  have htri := abs_add_le
    (∑ i : Fin n, v i * ∑ j : Fin n, M₀ i j * v j)
    (∑ i : Fin n, v i * ∑ j : Fin n, E i j * v j)
  linarith

end SliceMarkovTensorization
