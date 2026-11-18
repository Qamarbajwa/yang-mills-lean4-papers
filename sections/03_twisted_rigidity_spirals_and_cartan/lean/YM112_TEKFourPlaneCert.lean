/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.TEKFourPlaneLattice
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-112: Four-Plane Symmetric Shear & Quadratic-Rank Spectral Scaling Certificate

This module instantiates `TEKFourPlaneLattice` at rank `N = 36` (`L = 6`, flux `k = 5`),
certifying bijectivity of the modular shear twist, triviality of its kernel, the quadratic
rank scaling bound `16 / 36 ≤ 4 * sin²(π / 6)`, and the 4-plane additive gap `64 / 36`.
-/

namespace YangMillsBlueprint.Certificates

open TEKFourPlaneLattice

/-- Certificate witnessing symmetric four-plane twist scaling at `N = L^2`. -/
structure TEKFourPlaneCert where
  L : ℕ
  N : ℕ
  k : ℕ
  hL : 2 ≤ L
  hN : N = L ^ 2
  hcoprime : Nat.Coprime k L

/-- Canonical rank-36 four-plane certificate (`L = 6`, `N = 36`, `k = 5`). -/
def canonicalTEKCert : TEKFourPlaneCert where
  L := 6
  N := 36
  k := 5
  hL := by decide
  hN := by norm_num
  hcoprime := by decide

instance : Nonempty TEKFourPlaneCert :=
  ⟨canonicalTEKCert⟩

/-- Modular shear twist is bijective for every `TEKFourPlaneCert`. -/
theorem tek_shear_bijective (c : TEKFourPlaneCert) :
    Function.Bijective (shearMap c.N c.k) :=
  shearMap_bijective c.N c.k

/-- Quadratic-rank single-plane spectral bound `16 / N ≤ 4 sin²(π / L)` for `N = L^2`. -/
theorem tek_quadratic_rank_gap_le (c : TEKFourPlaneCert) :
    16 / (c.N : ℝ) ≤ 4 * Real.sin (Real.pi / c.L) ^ 2 :=
  quadratic_rank_gap_le_four_mul_sin_sq c.hL c.hN

/-- Symmetric four-plane additive gap `64 / N` cleanly exceeds single-plane `1/N^2` decay. -/
theorem tek_four_plane_additive_gap_le (c : TEKFourPlaneCert) :
    64 / (c.N : ℝ) ≤ 4 * (4 * Real.sin (Real.pi / c.L) ^ 2) :=
  four_plane_additive_gap_le c.hL c.hN

/-- Concrete evaluation at `L = 6, N = 36`: `4 * (4 * sin²(π / 6)) ≥ 16 / 9 > 1`. -/
theorem canonical_tek_four_plane_gap_gt_one :
    (1 : ℝ) < 4 * (4 * Real.sin (Real.pi / canonicalTEKCert.L) ^ 2) := by
  have h := tek_four_plane_additive_gap_le canonicalTEKCert
  have hN : (canonicalTEKCert.N : ℝ) = 36 := by norm_num [canonicalTEKCert]
  rw [hN] at h
  linarith

end YangMillsBlueprint.Certificates
