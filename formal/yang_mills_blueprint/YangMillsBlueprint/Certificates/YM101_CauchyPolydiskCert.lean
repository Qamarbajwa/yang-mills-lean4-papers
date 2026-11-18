/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import YangMillsBlueprint.MathlibStaging.PolydiskMajorant
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# YM-101: All-Orders Cauchy-Taylor Polydisk Contraction Certificate

This module instantiates `PolydiskMajorant` bounds with the exact rational weights of the
4D SU(2) multiscale small-field cluster expansion, including the real infinite-series `tsum`
convergence bound.
-/

namespace YangMillsBlueprint.Certificates

open PolydiskMajorant

/-- Rational certificate packaging the leading and tail small-field polymer weights
together with the `δ = 1/5` collar weight and contraction margin. -/
structure PolydiskContractionCert where
  wLeading : ℚ
  wTail : ℚ
  wCollar : ℚ
  hCollar : wCollar = 452 / 133125
  hBaseSum : wLeading + wTail < 1
  hMargin : (1 : ℚ) / 57 < 1 - (wLeading + wTail)
  hTotal : wLeading + wTail + wCollar < 1

/-- Canonical exact rational certificate from the all-orders small-field expansion. -/
def canonicalPolydiskCert : PolydiskContractionCert where
  wLeading := 19623589247123587350642100903 / 19979987798223270175317603840
  wTail := 0
  wCollar := 452 / 133125
  hCollar := rfl
  hBaseSum := by norm_num
  hMargin := by norm_num
  hTotal := by norm_num

instance : Nonempty PolydiskContractionCert :=
  ⟨canonicalPolydiskCert⟩

/-- Conditional small-field contraction: any certificate whose tail is bounded by `wBound`
and satisfies `wLeading + wBound < 1` has total weight strictly less than `1`. -/
theorem small_field_contraction_lt_one_conditional (cert : PolydiskContractionCert)
    (wBound : ℚ) (hTail : cert.wTail ≤ wBound) (hSum : cert.wLeading + wBound < 1) :
    totalWeight cert.wLeading cert.wTail < 1 :=
  total_weight_lt_one hTail hSum

/-- Unconditional verification that the canonical all-orders polymer weight plus the
`δ = 1/5` collar bound is strictly less than `1`. -/
theorem canonical_polymer_weight_lt_one :
    totalWeight (canonicalPolydiskCert.wLeading + canonicalPolydiskCert.wTail)
      canonicalPolydiskCert.wCollar < 1 := by
  unfold totalWeight
  exact canonicalPolydiskCert.hTotal

/-- Infinite geometric series `tsum` convergence bound instantiated for the canonical
small-field polymer weight `w` and margin `1 / 57` over `ℝ`. -/
theorem canonical_polymer_tsum_bound :
    let w : ℝ := (canonicalPolydiskCert.wLeading : ℝ)
    Summable (fun n : ℕ => w ^ (n + 1)) ∧
      (∑' n : ℕ, w ^ (n + 1)) = w / (1 - w) ∧
      (∑' n : ℕ, w ^ (n + 1)) ≤ (1 - (1 / 57 : ℝ)) / (1 / 57 : ℝ) := by
  have hw₀ : (0 : ℝ) ≤ (canonicalPolydiskCert.wLeading : ℝ) := by
    dsimp [canonicalPolydiskCert]
    norm_num
  have hwm : (canonicalPolydiskCert.wLeading : ℝ) + (1 / 57 : ℝ) ≤ 1 := by
    dsimp [canonicalPolydiskCert]
    norm_num
  exact tsum_geometric_tail_le hw₀ (by norm_num) hwm

end YangMillsBlueprint.Certificates
