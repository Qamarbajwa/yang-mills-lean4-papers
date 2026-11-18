/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.ScreenedDipoleVariance
import YangMillsBlueprint.MathlibStaging.StokesAdjointDispersion
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-139: Bianchi-Screened Dipole Variance Certificate (`WP2-C`)

Calibrates `ScreenedDipoleVariance` against Probes 12–13 on 4D `SU(2)` at `β = 2.3` vs. `U(1)`
Coulomb (`β_U(1) = 1.30`):
- Bare Coulomb dipole cancellation weight `α = 4 / 7` (from `U(1)` `sum/diag = 0.4281`).
- Nearest-neighbor Landau-gauge Bianchi adjoint loss `δ_nn = 2 / 5` (`≈ 0.3922`), yielding
  `screenedVarianceRatio (4 / 7) (2 / 5) = 23 / 35 ≥ 2 / 5 > 0`.
- Full `R = 4` Bianchi decoherence `δ_full = 4 / 5`, yielding
  `screenedVarianceRatio (4 / 7) (4 / 5) = 31 / 35` (`≈ 0.8857`), matching the `0.9006` area plateau.
-/

namespace YangMillsBlueprint.Certificates

open AdjointBianchiNorm ScreenedDipoleVariance StokesAdjointDispersion Matrix

/-- Certificate bundling Bianchi-screened Coulomb cancellation and surface variance floor. -/
structure BianchiScreenedVarianceCert where
  v0 : ℚ
  α : ℚ
  δnn : ℚ
  δfull : ℚ
  hv0 : 0 < v0
  hα0 : 0 ≤ α
  hα1 : α ≤ 1
  hδnn0 : 0 < δnn
  hδnn1 : δnn ≤ 1
  hδf0 : 0 < δfull
  hδf1 : δfull ≤ 1

/-- Canonical `β = 2.3` 4D `SU(2)` Bianchi-screened variance witness (`α = 4 / 7`, `δnn = 2 / 5`,
`δfull = 4 / 5`, `v0 = 9 / 10`). -/
def canonicalBianchiScreenedCert : BianchiScreenedVarianceCert where
  v0 := 9 / 10
  α := 4 / 7
  δnn := 2 / 5
  δfull := 4 / 5
  hv0 := by norm_num
  hα0 := by norm_num
  hα1 := by norm_num
  hδnn0 := by norm_num
  hδnn1 := by norm_num
  hδf0 := by norm_num
  hδf1 := by norm_num

instance : Nonempty BianchiScreenedVarianceCert :=
  ⟨canonicalBianchiScreenedCert⟩

/-- Canonical nearest-neighbor evaluation: `screenedVarianceRatio (4 / 7) (2 / 5) = 23 / 35`. -/
theorem canonical_screened_ratio_nn_eq :
    screenedVarianceRatio canonicalBianchiScreenedCert.α canonicalBianchiScreenedCert.δnn =
      23 / 35 := by
  dsimp [canonicalBianchiScreenedCert, screenedVarianceRatio]
  norm_num

/-- Canonical full-decoherence evaluation: `screenedVarianceRatio (4 / 7) (4 / 5) = 31 / 35`. -/
theorem canonical_screened_ratio_full_eq :
    screenedVarianceRatio canonicalBianchiScreenedCert.α canonicalBianchiScreenedCert.δfull =
      31 / 35 := by
  dsimp [canonicalBianchiScreenedCert, screenedVarianceRatio]
  norm_num

/-- Unconditional positivity of both `δnn` and the screened area-law variance ratio. -/
theorem screened_ratio_pos_of_cert (c : BianchiScreenedVarianceCert) :
    c.δnn ≤ screenedVarianceRatio c.α c.δnn ∧ 0 < screenedVarianceRatio c.α c.δnn := by
  exact ⟨delta_le_screenedVarianceRatio c.hα1 c.hδnn1,
    screenedVarianceRatio_pos_of_loss c.hα0 c.hα1 c.hδnn0⟩

/-- **CONDITIONAL:** Chaining `YM137` (`stokes_sum_frobSq_ge_of_bianchi_floor`) with
`ScreenedDipoleVariance` (`screenedSurfaceVariance_ge_area_floor`): once the Gibbs measure on
`R × R` surfaces realizes single-plaquette floor `v0` and covariant Bianchi attenuation
`cBianchi = screenedVarianceRatio c.α c.δfull`, total transported Stokes flux variance grows at
least proportionally to `(R * R : ℚ) * (c.v0 * c.δfull)`. -/
theorem bianchi_screened_area_law_variance_conditional (c : BianchiScreenedVarianceCert)
    {n R : ℕ} (M : Fin (R * R) → Matrix (Fin n) (Fin n) ℚ)
    (hoff : -(1 - screenedVarianceRatio c.α c.δfull) * (∑ i : Fin (R * R), frobSq (M i)) ≤
      ∑ i : Fin (R * R), ∑ j ∈ Finset.univ.erase i, frobInner (M i) (M j))
    (hdiag : (R * R : ℚ) * c.v0 ≤ ∑ i : Fin (R * R), frobSq (M i)) :
    (R * R : ℚ) * (c.v0 * c.δfull) ≤ frobSq (∑ i : Fin (R * R), M i) := by
  have hstokes := stokes_sum_frobSq_ge_of_bianchi_floor M (screenedVarianceRatio c.α c.δfull) hoff
  have hpos : 0 < screenedVarianceRatio c.α c.δfull :=
    screenedVarianceRatio_pos_of_loss c.hα0 c.hα1 c.hδf0
  have hmul :
      screenedSurfaceVariance c.v0 c.α c.δfull (R * R) ≤
        screenedVarianceRatio c.α c.δfull * ∑ i : Fin (R * R), frobSq (M i) := by
    unfold screenedSurfaceVariance
    have hcalc : ((R * R : ℕ) : ℚ) * c.v0 * screenedVarianceRatio c.α c.δfull =
        screenedVarianceRatio c.α c.δfull * ((R * R : ℚ) * c.v0) := by
      push_cast
      ring
    rw [hcalc]
    exact mul_le_mul_of_nonneg_left hdiag (le_of_lt hpos)
  have harea : ((R * R : ℕ) : ℚ) * (c.v0 * c.δfull) ≤
      screenedSurfaceVariance c.v0 c.α c.δfull (R * R) :=
    screenedSurfaceVariance_ge_area_floor (le_of_lt c.hv0) c.hα0 c.hα1
      (le_of_lt c.hδf0) c.hδf1 (R * R)
  have hcast : ((R * R : ℕ) : ℚ) = (R * R : ℚ) := by push_cast; ring
  rw [hcast] at harea
  exact harea.trans (hmul.trans hstokes)

end YangMillsBlueprint.Certificates
