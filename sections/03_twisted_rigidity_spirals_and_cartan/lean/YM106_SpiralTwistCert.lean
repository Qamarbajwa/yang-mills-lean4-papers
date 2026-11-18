/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.CoprimeSpiralTwist
import YangMillsBlueprint.MathlibStaging.ClockShiftMatrices
import Mathlib.Tactic.Linarith

/-!
# YM-106: SU(N) Coprime Spiral Twist Certificate

This module instantiates `CoprimeSpiralTwist` alongside `ClockShiftMatrices` to establish
simultaneous two-plane non-vanishing for coprime twists and prove the additive two-plane
Jordan spectral lower bound `32 / N² ≤ 4 sin²(π / N) + 4 sin²(π / N)`.
-/

namespace YangMillsBlueprint.Certificates

open CoprimeSpiralTwist
open ClockShiftMatrices

/-- Certificate bundling an SU(N) color rank `N ≥ 2` and a coprime spiral twist parameter `k`. -/
structure SpiralTwistCert where
  N : ℕ
  k : ℕ
  hN : 2 ≤ N
  hCoprime : Nat.Coprime k N

/-- Canonical coprime spiral twist certificate for `N = 5`, `k = 2`. -/
def canonicalSpiralTwistCert : SpiralTwistCert where
  N := 5
  k := 2
  hN := by decide
  hCoprime := by decide

instance : Nonempty SpiralTwistCert :=
  ⟨canonicalSpiralTwistCert⟩

/-- Under any coprime spiral twist certificate, every non-zero mode `m ≠ 0` has non-zero
coordinates in both twisted planes. -/
theorem spiral_twist_both_planes_nonzero (cert : SpiralTwistCert)
    {m : ZMod cert.N} (hm : m ≠ 0) :
    m ≠ 0 ∧ spiralMap cert.N cert.k m ≠ 0 :=
  spiral_both_coords_ne_zero cert.hCoprime hm

/-- For all `N ≥ 2`, the two-plane coprime spiral fundamental chord sum satisfies the additive
Jordan spectral gap lower bound `32 / N² ≤ 4 sin²(π / N) + 4 sin²(π / N)`. -/
theorem sun_coprime_spiral_two_plane_gap_le {N : ℕ} (hN : 2 ≤ N) :
    32 / (N : ℝ) ^ 2 ≤ 4 * Real.sin (Real.pi / N) ^ 2 + 4 * Real.sin (Real.pi / N) ^ 2 := by
  have hj := jordan_spectral_gap_le_four_mul_sin_sq hN
  have h2 := two_plane_gap_lower_bound hj hj
  linarith [show 2 * (16 / (N : ℝ) ^ 2) = 32 / (N : ℝ) ^ 2 by ring]

end YangMillsBlueprint.Certificates
