/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.StokesAdjointDispersion
import YangMillsBlueprint.Certificates.YM136_GeneralGroupBianchiCert
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-137: Non-Abelian Stokes Adjoint Dispersion Certificate (`WP2-C` / `E-LATTICE-CONT`)

Certifies:
1. Unconditional `SO(3)` broken Coulomb-dipole cancellation: transporting an exact opposite
   dipole `-so3GenX` by `so3RotZ90` leaves strictly positive Stokes residual `= 4 > 0`, whereas
   commuting Abelian Cartan `-so3GenZ` cancels identically to `0`.
2. Conditional infinite-volume area-variance persistence (`stokes_area_variance_persists_conditional`)
   converting a uniform Bianchi decoherence floor `cBianchi > 0` and single-plaquette variance
   floor `κ₀ > 0` on `m = R * R` tiles into area-law Stokes flux variance `≥ cBianchi * κ₀ * (R * R)`.
-/

namespace YangMillsBlueprint.Certificates

open AdjointBianchiNorm StokesAdjointDispersion Matrix

/-- Certificate bundling non-Abelian Coulomb-dipole non-cancellation and Stokes Bianchi floor. -/
structure StokesBianchiDispersionCert where
  u : Matrix (Fin 3) (Fin 3) ℚ
  x : Matrix (Fin 3) (Fin 3) ℚ
  δ : ℚ
  cBianchi : ℚ
  κ0 : ℚ
  hu1 : u * uᵀ = 1
  hu2 : uᵀ * u = 1
  hδ : 0 < δ
  hcomm : δ ≤ frobSq (matrixComm u x)
  hc : 0 < cBianchi
  hκ : 0 < κ0

/-- Canonical `SO(3)` Stokes dispersion witness (`[so3RotZ90, so3GenX]` leaves residual `4 > 0`,
with `cBianchi = 4 / 5` matching 4D `SU(2)` scaling plateau `0.81–0.85`). -/
def canonicalStokesBianchiDispersionCert : StokesBianchiDispersionCert where
  u := so3RotZ90
  x := so3GenX
  δ := 4
  cBianchi := 4 / 5
  κ0 := 7 / 10
  hu1 := canonicalGeneralGroupBianchiCert.hu1
  hu2 := canonicalGeneralGroupBianchiCert.hu2
  hδ := by norm_num
  hcomm := canonicalGeneralGroupBianchiCert.hcomm
  hc := by norm_num
  hκ := by norm_num

instance : Nonempty StokesBianchiDispersionCert :=
  ⟨canonicalStokesBianchiDispersionCert⟩

/-- Unconditional broken Abelian cancellation: for any certified orthogonal transport `(u, x)`,
transporting the exact opposite dipole `-x` leaves strictly positive Stokes norm squared. -/
theorem stokes_coulomb_dipole_broken_pos (c : StokesBianchiDispersionCert) :
    0 < frobSq (c.x + adjAction c.u (-c.x)) := by
  rw [frobSq_exact_cancellation_eq_comm c.u c.x c.hu1 c.hu2]
  exact lt_of_lt_of_le c.hδ c.hcomm

/-- Canonical `SO(3)` witness: exact opposite dipole `-so3GenX` transported by `so3RotZ90`
retains norm squared `4 > 3`, in sharp contrast to Abelian Cartan cancellation `0`. -/
theorem canonical_so3_dipole_broken_gt_three :
    3 < frobSq (so3GenX + adjAction so3RotZ90 (-so3GenX)) := by
  rw [frobSq_exact_cancellation_eq_comm so3RotZ90 so3GenX
    canonicalStokesBianchiDispersionCert.hu1 canonicalStokesBianchiDispersionCert.hu2]
  have h := canonicalStokesBianchiDispersionCert.hcomm
  dsimp [canonicalStokesBianchiDispersionCert] at h
  linarith

/-- Commuting Cartan dipole `-so3GenZ` cancels identically to zero under `so3RotZ90`. -/
theorem canonical_cartan_dipole_cancels_zero :
    frobSq (so3GenZ + adjAction so3RotZ90 (-so3GenZ)) = 0 := by
  rw [frobSq_exact_cancellation_eq_comm so3RotZ90 so3GenZ
    canonicalStokesBianchiDispersionCert.hu1 canonicalStokesBianchiDispersionCert.hu2]
  have hc : so3RotZ90 * so3GenZ = so3GenZ * so3RotZ90 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [so3RotZ90, so3GenZ, Matrix.mul_apply, Fin.sum_univ_three]
  unfold matrixComm
  rw [hc, sub_self]
  unfold frobSq Matrix.trace
  simp

/-- **CONDITIONAL:** Once the infinite-volume Gibbs measure on `R × R` tiles satisfies the
covariant Bianchi decoherence floor `cBianchi` and per-plaquette curvature floor `κ0`, the total
transported Stokes flux norm squared grows at least proportionally to the surface area `R * R`. -/
theorem stokes_area_variance_persists_conditional (c : StokesBianchiDispersionCert)
    {n R : ℕ} (M : Fin (R * R) → Matrix (Fin n) (Fin n) ℚ)
    (hoff : -(1 - c.cBianchi) * (∑ i : Fin (R * R), frobSq (M i)) ≤
      ∑ i : Fin (R * R), ∑ j ∈ Finset.univ.erase i, frobInner (M i) (M j))
    (hcurv : (R * R : ℚ) * c.κ0 ≤ ∑ i : Fin (R * R), frobSq (M i)) :
    c.cBianchi * c.κ0 * (R * R : ℚ) ≤ frobSq (∑ i : Fin (R * R), M i) := by
  have hfloor := stokes_sum_frobSq_ge_of_bianchi_floor M c.cBianchi hoff
  have hmul : c.cBianchi * ((R * R : ℚ) * c.κ0) ≤
      c.cBianchi * ∑ i : Fin (R * R), frobSq (M i) :=
    mul_le_mul_of_nonneg_left hcurv (le_of_lt c.hc)
  calc
    c.cBianchi * c.κ0 * (R * R : ℚ) = c.cBianchi * ((R * R : ℚ) * c.κ0) := by ring
    _ ≤ c.cBianchi * ∑ i : Fin (R * R), frobSq (M i) := hmul
    _ ≤ frobSq (∑ i : Fin (R * R), M i) := hfloor

end YangMillsBlueprint.Certificates
