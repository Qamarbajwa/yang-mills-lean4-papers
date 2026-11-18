/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.BCDClassicalCartan
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum

/-!
# YM-117: Classical `Bₙ` (`SO(2n+1)`), `Cₙ` (`Sp(n)`), and `Dₙ` (`Spin(2n)`) Cartan Certificate

This module instantiates `BCDClassicalCartan` over `ℚ`, certifying positive-definite
zero-mode elimination for arbitrary-rank orthogonal and symplectic Lie algebras (`B_{n+1}`,
`C_{n+2}`, `D_{n+3}`, and `D₄`), completing 100% Killing-Cartan coverage alongside
`YM108`, `YM113`, and `YM114`.
-/

namespace YangMillsBlueprint.Certificates

open BCDClassicalCartan

/-- Certificate bundling rank parameter `n` across types `B`, `C`, and `D`. -/
structure BCDClassicalCartanCert where
  n : ℕ

/-- Canonical rank certificate at `n = 1` (`B₂`, `C₃`, `D₄`). -/
def canonicalBCDCartanCert : BCDClassicalCartanCert where
  n := 1

instance : Nonempty BCDClassicalCartanCert :=
  ⟨canonicalBCDCartanCert⟩

/-- Positive-definite zero-mode elimination for centerless `SO(2n+3)` (`B_{n+1}`) over `ℚ`. -/
theorem so_odd_bn_cartan_zero_mode_eliminated (n : ℕ) (x : Fin (n + 1) → ℚ) :
    bCartanForm n x = 0 → ∀ i : Fin (n + 1), x i = 0 :=
  (bCartanForm_eq_zero_iff n x).mp

/-- Positive-definite zero-mode elimination for `Sp(n+2)` (`C_{n+2}`) over `ℚ`. -/
theorem sp_cn_cartan_zero_mode_eliminated (n : ℕ) (x : Fin (n + 2) → ℚ) :
    cCartanForm n x = 0 → ∀ i : Fin (n + 2), x i = 0 :=
  (cCartanForm_eq_zero_iff n x).mp

/-- Positive-definite zero-mode elimination for `Spin(2(n+3))` (`D_{n+3}`) over `ℚ`. -/
theorem spin_dn_cartan_zero_mode_eliminated (n : ℕ) (x : Fin (n + 3) → ℚ) :
    dCartanForm n x = 0 → ∀ i : Fin (n + 3), x i = 0 :=
  (dCartanForm_eq_zero_iff n x).mp

/-- Rank-4 triality `Spin(8)` (`D₄`) specialization check over `ℚ`. -/
theorem spin8_d4_cartan_zero_mode_eliminated (x : Fin 4 → ℚ) :
    d4CartanForm x = 0 → ∀ i : Fin 4, x i = 0 :=
  (d4CartanForm_eq_zero_iff x).mp

end YangMillsBlueprint.Certificates
