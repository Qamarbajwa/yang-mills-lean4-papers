/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Transfer-Matrix Spectral Correlator Log-Convexity and Effective-Mass Monotonicity

For a finite-mode reflection-positive slice transfer correlator
`spectralCorr w r t = ∑ i : Fin k, w i * r i ^ t` with non-negative weights `w i ≥ 0` and
transfer eigenvalues `0 ≤ r i ≤ rMax`, we prove:
1. Single-step spectral contraction `spectralCorr w r (t + 1) ≤ rMax * spectralCorr w r t`,
2. Exponential clustering decay `spectralCorr w r t ≤ rMax ^ t * spectralCorr w r 0`, and
3. Cauchy–Schwarz log-convexity `(spectralCorr w r (t + 1)) ^ 2 ≤ ...`, which implies that
   effective-mass ratios increase monotonically with Euclidean separation `t`.

## Main results

* `EffectiveMassTransferGap.spectralCorr_nonneg`: positivity from RP spectral weights.
* `EffectiveMassTransferGap.spectralCorr_le_pow_mul_zero`: exponential decay at rate `rMax`.
* `EffectiveMassTransferGap.spectralCorr_log_convex`: Cauchy–Schwarz spectral log-convexity.
* `EffectiveMassTransferGap.effectiveMassRatio_mono`: non-decreasing transfer ratios
  (equivalently non-increasing finite-`t` effective masses converging from above to the gap).
-/

@[expose] public section

namespace EffectiveMassTransferGap

/-- Finite-mode reflection-positive Euclidean slice correlator `∑ i, w i * r i ^ t`. -/
noncomputable def spectralCorr {k : ℕ} (w r : Fin k → ℝ) (t : ℕ) : ℝ :=
  ∑ i : Fin k, w i * r i ^ t

/-- Non-negativity of the spectral correlator for non-negative weights and eigenvalues. -/
theorem spectralCorr_nonneg {k : ℕ} (w r : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (t : ℕ) :
    0 ≤ spectralCorr w r t := by
  unfold spectralCorr
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (pow_nonneg (hr i) t)

/-- One-step transfer contraction bounded by maximum eigenvalue `rMax`. -/
theorem spectralCorr_succ_le {k : ℕ} (w r : Fin k → ℝ) {rMax : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hr0 : ∀ i, 0 ≤ r i) (hrMax : ∀ i, r i ≤ rMax) (t : ℕ) :
    spectralCorr w r (t + 1) ≤ rMax * spectralCorr w r t := by
  unfold spectralCorr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hterm : w i * r i ^ (t + 1) = r i * (w i * r i ^ t) := by
    rw [pow_succ']
    ring
  rw [hterm]
  exact mul_le_mul_of_nonneg_right (hrMax i) (mul_nonneg (hw i) (pow_nonneg (hr0 i) t))

/-- Exponential decay `C(t) ≤ rMax ^ t * C(0)` for all Euclidean time separations `t`. -/
theorem spectralCorr_le_pow_mul_zero {k : ℕ} (w r : Fin k → ℝ) {rMax : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hr0 : ∀ i, 0 ≤ r i) (hrMax : ∀ i, r i ≤ rMax) (hrM0 : 0 ≤ rMax) :
    ∀ t : ℕ, spectralCorr w r t ≤ rMax ^ t * spectralCorr w r 0
  | 0 => by simp
  | t + 1 => by
    have hstep := spectralCorr_succ_le w r hw hr0 hrMax t
    have hind := spectralCorr_le_pow_mul_zero w r hw hr0 hrMax hrM0 t
    have hmul : rMax * spectralCorr w r t ≤ rMax * (rMax ^ t * spectralCorr w r 0) :=
      mul_le_mul_of_nonneg_left hind hrM0
    calc
      spectralCorr w r (t + 1) ≤ rMax * spectralCorr w r t := hstep
      _ ≤ rMax * (rMax ^ t * spectralCorr w r 0) := hmul
      _ = rMax ^ (t + 1) * spectralCorr w r 0 := by rw [pow_succ']; ring

/-- Spectral log-convexity `(C(t + 1))^2 ≤ C(t) * C(t + 2)` via Cauchy–Schwarz. -/
theorem spectralCorr_log_convex {k : ℕ} (w r : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (t : ℕ) :
    spectralCorr w r (t + 1) ^ 2 ≤ spectralCorr w r t * spectralCorr w r (t + 2) := by
  let a : Fin k → ℝ := fun i => Real.sqrt (w i * r i ^ t)
  let b : Fin k → ℝ := fun i => Real.sqrt (w i * r i ^ (t + 2))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) a b
  have ha2 : (∑ i : Fin k, a i ^ 2) = spectralCorr w r t := by
    unfold spectralCorr
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.sq_sqrt (mul_nonneg (hw i) (pow_nonneg (hr i) t))
  have hb2 : (∑ i : Fin k, b i ^ 2) = spectralCorr w r (t + 2) := by
    unfold spectralCorr
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.sq_sqrt (mul_nonneg (hw i) (pow_nonneg (hr i) (t + 2)))
  have hab : (∑ i : Fin k, a i * b i) = spectralCorr w r (t + 1) := by
    unfold spectralCorr
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow : (w i * r i ^ t) * (w i * r i ^ (t + 2)) = (w i * r i ^ (t + 1)) ^ 2 := by
      have : r i ^ t * r i ^ (t + 2) = (r i ^ (t + 1)) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      calc
        (w i * r i ^ t) * (w i * r i ^ (t + 2)) = w i ^ 2 * (r i ^ t * r i ^ (t + 2)) := by ring
        _ = w i ^ 2 * (r i ^ (t + 1)) ^ 2 := by rw [this]
        _ = (w i * r i ^ (t + 1)) ^ 2 := by ring
    dsimp [a, b]
    rw [← Real.sqrt_mul (mul_nonneg (hw i) (pow_nonneg (hr i) t)), hpow]
    exact Real.sqrt_sq (mul_nonneg (hw i) (pow_nonneg (hr i) (t + 1)))
  rw [hab, ha2, hb2] at hcs
  exact hcs

/-- Monotonicity of consecutive transfer ratios `C(t + 1) / C(t) ≤ C(t + 2) / C(t + 1)`. -/
theorem effectiveMassRatio_mono {k : ℕ} (w r : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (t : ℕ)
    (ht0 : 0 < spectralCorr w r t) (ht1 : 0 < spectralCorr w r (t + 1)) :
    spectralCorr w r (t + 1) / spectralCorr w r t ≤
      spectralCorr w r (t + 2) / spectralCorr w r (t + 1) := by
  rw [div_le_div_iff₀ ht0 ht1]
  have hlc := spectralCorr_log_convex w r hw hr t
  linarith [sq (spectralCorr w r (t + 1))]

end EffectiveMassTransferGap
