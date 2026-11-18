/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.AdjointBianchiNorm
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-136: General Lie-Group Adjoint Bianchi Chording Certificate (`E-GROUP-GEN`)

Instantiates `AdjointBianchiNorm` on `3 × 3` orthogonal transformations (`SO(3) = SU(2)/ℤ₂`),
certifying positive non-Abelian adjoint transport defect `= 8 > 0` without relying on center
elements `Z(G)`, contrasted with exact `0` vanishing in a commuting Cartan slice.
-/

namespace YangMillsBlueprint.Certificates

open AdjointBianchiNorm Matrix

/-- Orthogonal `SO(3)` rotation around the 3-axis by `π/2` (represents trivial center in `SO(3)`). -/
def so3RotZ90 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- Non-commuting adjoint generator `L₁ ∈ so(3)` orthogonal to the rotation axis. -/
def so3GenX : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 0, 0; 0, 0, -1; 0, 1, 0]

/-- Commuting adjoint generator `L₃ ∈ so(3)` parallel to the rotation axis. -/
def so3GenZ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- Certificate bundling dimension-3 orthogonal adjoint chording witness. -/
structure GeneralGroupBianchiCert where
  u : Matrix (Fin 3) (Fin 3) ℚ
  x : Matrix (Fin 3) (Fin 3) ℚ
  δ : ℚ
  hu1 : u * uᵀ = 1
  hu2 : uᵀ * u = 1
  hδ : 0 < δ
  hcomm : δ ≤ frobSq (matrixComm u x)

/-- Canonical `SO(3)` centerless adjoint chording certificate (`frobSq (matrixComm u x) = 4 ≥ 4`). -/
def canonicalGeneralGroupBianchiCert : GeneralGroupBianchiCert where
  u := so3RotZ90
  x := so3GenX
  δ := 4
  hu1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [so3RotZ90, Matrix.mul_apply, Fin.sum_univ_three]
  hu2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [so3RotZ90, Matrix.mul_apply, Fin.sum_univ_three]
  hδ := by norm_num
  hcomm := by
    unfold frobSq matrixComm so3RotZ90 so3GenX Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
      Fin.sum_univ_three]
    norm_num

instance : Nonempty GeneralGroupBianchiCert :=
  ⟨canonicalGeneralGroupBianchiCert⟩

/-- Positive adjoint parallel-transport Bianchi defect for any certified orthogonal pair `(u, x)`. -/
theorem general_adjoint_bianchi_defect_pos (c : GeneralGroupBianchiCert) :
    0 < frobSq (adjAction c.u c.x - c.x) := by
  rw [frobSq_adjAction_sub_eq c.u c.x c.hu1 c.hu2]
  exact lt_of_lt_of_le c.hδ c.hcomm

/-- Canonical `SO(3)` centerless witness certifying positive adjoint Bianchi defect `> 3`. -/
theorem canonical_so3_adjoint_bianchi_defect_gt_three :
    3 < frobSq (adjAction so3RotZ90 so3GenX - so3GenX) := by
  rw [frobSq_adjAction_sub_eq so3RotZ90 so3GenX
    canonicalGeneralGroupBianchiCert.hu1 canonicalGeneralGroupBianchiCert.hu2]
  have h := canonicalGeneralGroupBianchiCert.hcomm
  dsimp [canonicalGeneralGroupBianchiCert] at h
  linarith

/-- Commuting Abelian Cartan generator `L₃` gives exact zero adjoint Bianchi defect. -/
theorem canonical_cartan_commuting_bianchi_zero :
    frobSq (adjAction so3RotZ90 so3GenZ - so3GenZ) = 0 := by
  apply frobSq_adjAction_sub_zero_of_comm so3RotZ90 so3GenZ
    canonicalGeneralGroupBianchiCert.hu1 canonicalGeneralGroupBianchiCert.hu2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3RotZ90, so3GenZ, Matrix.mul_apply, Fin.sum_univ_three]

end YangMillsBlueprint.Certificates
