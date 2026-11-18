/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Lean
import YangMillsBlueprint.MathlibPR_SchurComplementForms
import YangMillsBlueprint.MathlibPR_CubicCollarBounds
import YangMillsBlueprint.MathlibPR_QuaternionTwistRigidity
import YangMillsBlueprint.MathlibPR_ClockShiftRigidity
import YangMillsBlueprint.MathlibStaging.PolydiskMajorant
import YangMillsBlueprint.MathlibStaging.CubicSinBounds
import YangMillsBlueprint.MathlibStaging.QuaternionCentralizer
import YangMillsBlueprint.MathlibStaging.ClockShiftMatrices
import YangMillsBlueprint.MathlibStaging.NonAbelianCommutatorStiffness
import YangMillsBlueprint.MathlibStaging.CoprimeSpiralTwist
import YangMillsBlueprint.MathlibStaging.QuarticQuantumStiffness
import YangMillsBlueprint.MathlibStaging.CartanCoxeterRigidity
import YangMillsBlueprint.MathlibStaging.ExponentialAreaScreening
import YangMillsBlueprint.MathlibStaging.AsymptoticFreedomFlow
import YangMillsBlueprint.MathlibStaging.SpectralMassGapBridge
import YangMillsBlueprint.MathlibStaging.TEKFourPlaneLattice
import YangMillsBlueprint.MathlibStaging.ExceptionalE8Cartan
import YangMillsBlueprint.MathlibStaging.ClassicalAndExceptionalCartan
import YangMillsBlueprint.MathlibStaging.LeviStratumCounting
import YangMillsBlueprint.MathlibStaging.LoopBootstrapMomentBounds
import YangMillsBlueprint.Certificates.YM101_CauchyPolydiskCert
import YangMillsBlueprint.Certificates.YM102_WeylCollarCert
import YangMillsBlueprint.Certificates.YM103_SU2TwistRigidityCert
import YangMillsBlueprint.Certificates.YM104_SU3ClockShiftCert
import YangMillsBlueprint.Certificates.YM105_ZeroModeStiffnessCert
import YangMillsBlueprint.Certificates.YM106_SpiralTwistCert
import YangMillsBlueprint.Certificates.YM107_LuscherQuantumGapCert
import YangMillsBlueprint.Certificates.YM108_CenterlessGroupCert
import YangMillsBlueprint.Certificates.YM109_VortexAreaScreeningCert
import YangMillsBlueprint.Certificates.YM110_AsymptoticFreedomCert
import YangMillsBlueprint.Certificates.YM111_ClayTargetSpecCert
import YangMillsBlueprint.Certificates.YM112_TEKFourPlaneCert
import YangMillsBlueprint.Certificates.YM113_E8CartanRigidityCert
import YangMillsBlueprint.Certificates.YM114_ClassicalExceptionalCartanCert
import YangMillsBlueprint.Certificates.YM115_LeviStratumCert
import YangMillsBlueprint.Certificates.YM116_CrossoverBootstrapCert

/-!
# Hardened Metaprogramming AST & Axiom Auditor (`VerifyNoTraps`)

This module performs compile-time `Lean.Meta` verification that every declaration in
`auditedTheorems`:
1. Exists in the environment and is not `opaque` or an `axiom`.
2. Uses strictly a subset of `[propext, Classical.choice, Quot.sound]`.
3. Contains zero `sorryAx`, `Lean.ofReduceBool`, or `Lean.ofReduceNat` in its proof AST.
4. Has a conclusion whose `whnf` is not definitionally `True`.
5. Has a conclusion not `isDefEq` to any single hypothesis in its `forallTelescopeReducing`
   context (blocking projection tautologies).
6. Verifies `Nonempty` instances for all conditional certificate structures.
-/

namespace YangMillsBlueprint.VerifyNoTraps

open Lean Meta Elab Command

private def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

private def forbiddenConsts : List Name :=
  [`sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat]

private def auditedTheorems : List Name :=
  [ ``PolydiskMajorant.total_weight_lt_one
  , ``PolydiskMajorant.one_sub_weight_pos
  , ``PolydiskMajorant.geometric_defect_le
  , ``PolydiskMajorant.summable_geometric_tail
  , ``PolydiskMajorant.tsum_geometric_tail_eq
  , ``PolydiskMajorant.tsum_geometric_tail_le
  , ``CubicSinBounds.cubicCollarWeight_nonneg
  , ``CubicSinBounds.cubicCollarWeight_anti_left
  , ``CubicSinBounds.sin_sq_le_sq
  , ``CubicSinBounds.integral_sin_sq_le_cubic
  , ``CubicSinBounds.normalized_sin_sq_integral_le_cubicCollarWeight
  , ``QuaternionCentralizer.adjointTwistQuadraticForm_eq
  , ``QuaternionCentralizer.adjointTwistQuadraticForm_ge_three
  , ``ClockShiftMatrices.shift3Perm_cube
  , ``ClockShiftMatrices.clock3_mul_shift3_eq
  , ``ClockShiftMatrices.eisenstein_chord_normSq_one
  , ``ClockShiftMatrices.eisenstein_chord_normSq_two
  , ``ClockShiftMatrices.eisensteinNormSq_nonneg
  , ``ClockShiftMatrices.chord_normSq_eq_four_mul_sin_sq
  , ``ClockShiftMatrices.mul_le_sin_of_mem_Icc
  , ``ClockShiftMatrices.jordan_sin_le_of_mem_Icc
  , ``ClockShiftMatrices.jordan_spectral_gap_le_four_mul_sin_sq
  , ``ClockShiftMatrices.secant_pi_div_six_sin_le_of_mem_Icc
  , ``ClockShiftMatrices.secant_spectral_gap_le_four_mul_sin_sq
  , ``ClockShiftMatrices.cos_pi_div_five_eq
  , ``ClockShiftMatrices.four_mul_sin_pi_div_five_sq_eq
  , ``ClockShiftMatrices.four_mul_sin_pi_div_five_sq_gt
  , ``NonAbelianCommutatorStiffness.lagrange_identity
  , ``NonAbelianCommutatorStiffness.cross_normSq_eq_of_ortho
  , ``NonAbelianCommutatorStiffness.triadQuarticEnergy_eq_of_ortho
  , ``NonAbelianCommutatorStiffness.triadQuarticEnergy_ge_three_mul_sq
  , ``CoprimeSpiralTwist.isUnit_coe_of_coprime
  , ``CoprimeSpiralTwist.spiralMap_eq_zero_iff
  , ``CoprimeSpiralTwist.spiralMap_ne_zero_of_ne_zero
  , ``CoprimeSpiralTwist.spiral_both_coords_ne_zero
  , ``CoprimeSpiralTwist.spiralMap_bijective
  , ``CoprimeSpiralTwist.two_plane_gap_lower_bound
  , ``QuarticQuantumStiffness.cubic_defect_factorization
  , ``QuarticQuantumStiffness.variationalEnergy_sub_min_eq
  , ``QuarticQuantumStiffness.three_mul_sq_le_variationalEnergy
  , ``QuarticQuantumStiffness.variationalEnergy_pos
  , ``CartanCoxeterRigidity.g2CartanDet_eq_one
  , ``CartanCoxeterRigidity.two_mul_g2CartanForm_eq
  , ``CartanCoxeterRigidity.six_mul_f4CartanForm_eq
  , ``CartanCoxeterRigidity.g2CartanForm_eq_zero_iff
  , ``CartanCoxeterRigidity.f4CartanForm_eq_zero_iff
  , ``ExponentialAreaScreening.exp_div_three_cubed
  , ``ExponentialAreaScreening.one_add_div_three_cubed_le_exp
  , ``ExponentialAreaScreening.cubic_div_twenty_seven_le_exp
  , ``ExponentialAreaScreening.quartic_mul_exp_neg_sq_le
  , ``AsymptoticFreedomFlow.inv_runningCoupling_eq
  , ``AsymptoticFreedomFlow.runningCoupling_pos
  , ``AsymptoticFreedomFlow.runningCoupling_le_inv_mul
  , ``AsymptoticFreedomFlow.telescoping_step_eq
  , ``AsymptoticFreedomFlow.telescoped_sum_lt_one
  , ``YangMillsBlueprint.Certificates.small_field_contraction_lt_one_conditional
  , ``YangMillsBlueprint.Certificates.canonical_polymer_weight_lt_one
  , ``YangMillsBlueprint.Certificates.canonical_polymer_tsum_bound
  , ``YangMillsBlueprint.Certificates.weyl_collar_rational_eval
  , ``YangMillsBlueprint.Certificates.weyl_collar_lt_margin
  , ``YangMillsBlueprint.Certificates.weyl_collar_strict_upper_bound_lt_margin
  , ``YangMillsBlueprint.Certificates.su2_real_weyl_collar_integral_lt_margin
  , ``YangMillsBlueprint.Certificates.su2_twisted_laplacian_exact
  , ``YangMillsBlueprint.Certificates.su2_twisted_laplacian_gap_ge_three
  , ``YangMillsBlueprint.Certificates.su2_toron_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.su3_clock_shift_spectral_gap_eq_three
  , ``YangMillsBlueprint.Certificates.su3_clock_shift_second_chord_eq_three
  , ``YangMillsBlueprint.Certificates.su3_clock_shift_commutation
  , ``YangMillsBlueprint.Certificates.su5_real_spectral_gap_gt
  , ``YangMillsBlueprint.Certificates.sun_real_jordan_gap_le
  , ``YangMillsBlueprint.Certificates.sun_real_secant_gap_le
  , ``YangMillsBlueprint.Certificates.su2_zero_mode_quartic_stiffness_pos_conditional
  , ``YangMillsBlueprint.Certificates.canonical_zero_mode_energy_eq_three
  , ``YangMillsBlueprint.Certificates.spiral_twist_both_planes_nonzero
  , ``YangMillsBlueprint.Certificates.sun_coprime_spiral_two_plane_gap_le
  , ``YangMillsBlueprint.Certificates.luscher_zero_mode_quantum_gap_ge_conditional
  , ``YangMillsBlueprint.Certificates.canonical_luscher_quantum_gap_pos
  , ``YangMillsBlueprint.Certificates.g2_coxeter_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.f4_coxeter_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.g2_unit_root_stiffness
  , ``YangMillsBlueprint.Certificates.vortex_free_energy_defect_le_real
  , ``YangMillsBlueprint.Certificates.canonical_vortex_defect_lt_one
  , ``YangMillsBlueprint.Certificates.uv_running_coupling_contraction_conditional
  , ``YangMillsBlueprint.Certificates.canonical_uv_coupling_lt_one
  , ``MathlibPR.LinearAlgebra.schur_complement_quadratic_identity
  , ``MathlibPR.LinearAlgebra.schur_coercivity_from_block_pivots
  , ``MathlibPR.LinearAlgebra.two_point_zero_sum_sq_diff_eq
  , ``MathlibPR.Data.RationalPairs.geometric_cluster_weight_lt_one
  , ``MathlibPR.CubicCollar.cubic_collar_eval_lt_target_margin
  , ``MathlibPR.QuaternionAlgebra.quat_imag_comm_i_j_trivial
  , ``MathlibPR.QuaternionAlgebra.quat_imag_ad_spectral_gap
  , ``MathlibPR.ClockShiftAlgebra.mode_pair_norm_sq_pos
  , ``MathlibPR.ClockShiftAlgebra.su3_twisted_eigenvalue_table_min
  , ``MathlibPR.ClockShiftAlgebra.jordan_spectral_gap_pos
  , ``MathlibPR.ClockShiftAlgebra.secant_asymptotic_gap_pos
  , ``MathlibPR.ClockShiftAlgebra.secant_asymptotic_gap_six_eval
  , ``MathlibPR.ClockShiftAlgebra.su5_rational_gap_witness
  , ``MathlibPR.ClockShiftAlgebra.su5_gap_gt_jordan
  , ``SpectralMassGapBridge.exp_neg_mul_anti
  , ``SpectralMassGapBridge.exp_decay_product_le
  , ``SpectralMassGapBridge.coercivity_orthogonal_decomp
  , ``SpectralMassGapBridge.coercivity_pos_of_perp_ne_zero
  , ``TEKFourPlaneLattice.shearMap_bijective
  , ``TEKFourPlaneLattice.shearMap_eq_zero_iff
  , ``TEKFourPlaneLattice.quadratic_rank_gap_le_four_mul_sin_sq
  , ``TEKFourPlaneLattice.four_plane_additive_gap_le
  , ``ExceptionalE8Cartan.e8_sum_of_squares_eq
  , ``ExceptionalE8Cartan.e8CartanForm_nonneg
  , ``ExceptionalE8Cartan.e8CartanForm_eq_zero_iff
  , ``YangMillsBlueprint.Certificates.real_mass_gap_spec_excited_pos
  , ``YangMillsBlueprint.Certificates.canonical_clustering_decay_le
  , ``YangMillsBlueprint.Certificates.tek_shear_bijective
  , ``YangMillsBlueprint.Certificates.tek_quadratic_rank_gap_le
  , ``YangMillsBlueprint.Certificates.tek_four_plane_additive_gap_le
  , ``YangMillsBlueprint.Certificates.canonical_tek_four_plane_gap_gt_one
  , ``YangMillsBlueprint.Certificates.e8_coxeter_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.e8_cartan_form_nonneg
  , ``YangMillsBlueprint.Certificates.e8_unit_simple_root_stiffness
  , ``ClassicalAndExceptionalCartan.aCartanForm_eq_sum_sq
  , ``ClassicalAndExceptionalCartan.aCartanForm_nonneg
  , ``ClassicalAndExceptionalCartan.aCartanForm_eq_zero_iff
  , ``ClassicalAndExceptionalCartan.e6_sum_of_squares_eq
  , ``ClassicalAndExceptionalCartan.e6CartanForm_eq_zero_iff
  , ``ClassicalAndExceptionalCartan.e7_sum_of_squares_eq
  , ``ClassicalAndExceptionalCartan.e7CartanForm_eq_zero_iff
  , ``LeviStratumCounting.stratum_dimension_conservation
  , ``LeviStratumCounting.four_mul_alphaReg_sub_alphaHarm_eq
  , ``LeviStratumCounting.alphaHarm_central_le_alphaReg
  , ``LoopBootstrapMomentBounds.sq_le_moment_of_schur
  , ``LoopBootstrapMomentBounds.loop_eq_level4_quadratic_le
  , ``LoopBootstrapMomentBounds.completed_square_identity
  , ``LoopBootstrapMomentBounds.loop_eq_level4_completed_square_le
  , ``LoopBootstrapMomentBounds.domino_reflection_positivity_bound
  , ``YangMillsBlueprint.Certificates.su_an_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.su_an_cartan_form_nonneg
  , ``YangMillsBlueprint.Certificates.e6_coxeter_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.e7_coxeter_cartan_zero_mode_eliminated
  , ``YangMillsBlueprint.Certificates.e6_e7_unit_simple_root_stiffness
  , ``YangMillsBlueprint.Certificates.su_n_levi_stratum_mode_balance
  , ``YangMillsBlueprint.Certificates.central_toron_harmonic_exponent_le_regular
  , ``YangMillsBlueprint.Certificates.su3_central_vs_regular_exponent_eval
  , ``YangMillsBlueprint.Certificates.crossover_level4_bootstrap_window
  , ``YangMillsBlueprint.Certificates.canonical_crossover_rhs_eval
  , ``YangMillsBlueprint.Certificates.crossover_level4_domino_coupling_conditional
  ]

private def requiredNonemptyStructs : List Name :=
  [ ``YangMillsBlueprint.Certificates.PolydiskContractionCert
  , ``YangMillsBlueprint.Certificates.SU3AdjointModeVec
  , ``YangMillsBlueprint.Certificates.ZeroModeStiffnessCert
  , ``YangMillsBlueprint.Certificates.SpiralTwistCert
  , ``YangMillsBlueprint.Certificates.LuscherQuantumGapCert
  , ``YangMillsBlueprint.Certificates.CenterlessGroupRigidityCert
  , ``YangMillsBlueprint.Certificates.VortexAreaScreeningCert
  , ``YangMillsBlueprint.Certificates.AsymptoticFreedomCert
  , ``YangMillsBlueprint.Certificates.RealMassGapSpecCert
  , ``YangMillsBlueprint.Certificates.TEKFourPlaneCert
  , ``YangMillsBlueprint.Certificates.ExceptionalE8RigidityCert
  , ``YangMillsBlueprint.Certificates.ClassicalExceptionalCartanCert
  , ``YangMillsBlueprint.Certificates.LeviStratumCert
  , ``YangMillsBlueprint.Certificates.CrossoverBootstrapCert
  ]

private def auditSingleTheorem (declName : Name) : MetaM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "VerifyNoTraps: missing declaration `{declName}`"
  match info with
  | .opaqueInfo _ =>
    throwError "VerifyNoTraps: `{declName}` is marked opaque"
  | .axiomInfo _ =>
    throwError "VerifyNoTraps: `{declName}` is a raw axiom"
  | _ => pure ()
  let usedAxioms ← collectAxioms declName
  for ax in usedAxioms do
    unless allowedAxioms.contains ax do
      throwError "VerifyNoTraps: `{declName}` uses forbidden axiom `{ax}`"
  if let some val := info.value? then
    let foundForbidden := val.foldConsts ([] : List Name) fun c acc =>
      if forbiddenConsts.contains c && !acc.contains c then c :: acc else acc
    unless foundForbidden.isEmpty do
      throwError "VerifyNoTraps: `{declName}` contains forbidden constants {foundForbidden}"
  forallTelescopeReducing info.type fun xs body => do
    let bodyWhnf ← whnf body
    if bodyWhnf.isConstOf ``True then
      throwError "VerifyNoTraps: `{declName}` conclusion reduces to `True`"
    for x in xs do
      let xType ← inferType x
      if ← isDefEq xType body then
        throwError "VerifyNoTraps: `{declName}` conclusion is defeq to hypothesis (tautology)"

private def auditNonemptyInstance (structName : Name) : MetaM Unit := do
  let target ← mkAppM ``Nonempty #[mkConst structName]
  let _ ← synthInstance target

#eval show CommandElabM Unit from liftTermElabM do
  for declName in auditedTheorems do
    auditSingleTheorem declName
  for structName in requiredNonemptyStructs do
    auditNonemptyInstance structName

-- Backward-compatible unconditional type bindings for regression test suite
theorem check_schur_identity_unconditional :
    (∀ a_bb a_cb a_cc z_b z_c : Int,
      MathlibPR.LinearAlgebra.twoBlockSchurDet a_bb a_cb a_cc * (z_c * z_c) +
          (a_bb * z_b - a_cb * z_c) * (a_bb * z_b - a_cb * z_c) =
        a_bb * MathlibPR.LinearAlgebra.twoBlockQuadForm a_bb a_cb a_cc z_b z_c) :=
  MathlibPR.LinearAlgebra.schur_complement_quadratic_identity

theorem check_schur_coercivity_unconditional :
    (∀ a_bb a_cb a_cc z_b z_c : Int,
      0 < a_bb →
      0 < MathlibPR.LinearAlgebra.twoBlockSchurDet a_bb a_cb a_cc →
      (z_b ≠ 0 ∨ z_c ≠ 0) →
      0 < MathlibPR.LinearAlgebra.twoBlockQuadForm a_bb a_cb a_cc z_b z_c) :=
  MathlibPR.LinearAlgebra.schur_coercivity_from_block_pivots

theorem check_poincare_block_identity_unconditional :
    (∀ x1 x2 : Int, x1 + x2 = 0 → (x1 - x2) * (x1 - x2) = 2 * (x1 * x1 + x2 * x2)) :=
  MathlibPR.LinearAlgebra.two_point_zero_sum_sq_diff_eq

theorem check_geometric_cluster_weight_unconditional :
    MathlibPR.Data.RationalPairs.RatPair.lt
      MathlibPR.Data.RationalPairs.totalGeometricClusterWeight
      (MathlibPR.Data.RationalPairs.RatPair.ofNat 1) :=
  MathlibPR.Data.RationalPairs.geometric_cluster_weight_lt_one

theorem check_geometric_margin_unconditional :
    MathlibPR.Data.RationalPairs.RatPair.lt
      ⟨1, 57, by omega⟩
      MathlibPR.Data.RationalPairs.geometricContractionMargin :=
  MathlibPR.Data.RationalPairs.geometric_contraction_margin_gt_one_57th

theorem check_cubic_collar_bound_unconditional :
    MathlibPR.CubicCollar.RatPair.lt
      MathlibPR.CubicCollar.cubicCollarEval
      MathlibPR.CubicCollar.collarReferenceMargin :=
  MathlibPR.CubicCollar.cubic_collar_eval_lt_target_margin

theorem check_quat_centralizer_rigidity_unconditional :
    (∀ b c d : Int,
      -2 * d = 0 → 2 * c = 0 → 2 * d = 0 → -2 * b = 0 →
      b = 0 ∧ c = 0 ∧ d = 0) :=
  MathlibPR.QuaternionAlgebra.quat_imag_comm_i_j_trivial

theorem check_quat_adjoint_spectral_gap_unconditional :
    (∀ b c d : Int,
      4 * (b * b + c * c + d * d) ≤
        -2 * d * (-2 * d) + 2 * c * (2 * c) + 2 * d * (2 * d) + -2 * b * (-2 * b)) :=
  MathlibPR.QuaternionAlgebra.quat_imag_ad_spectral_gap

theorem check_mode_pair_norm_sq_unconditional :
    (∀ m1 m2 : Int, m1 ≠ 0 ∨ m2 ≠ 0 → 1 ≤ m1 * m1 + m2 * m2) :=
  MathlibPR.ClockShiftAlgebra.mode_pair_norm_sq_pos

theorem check_su3_twisted_eigenvalue_table_min_unconditional :
    (∀ m1 m2 : Int, m1 ≠ 0 ∨ m2 ≠ 0 → 3 ≤ 3 * (m1 * m1) + 3 * (m2 * m2)) :=
  MathlibPR.ClockShiftAlgebra.su3_twisted_eigenvalue_table_min

theorem check_su3_cyclotomic_norm_sq_eval_unconditional :
    MathlibPR.ClockShiftAlgebra.RatPair.eqv
      (MathlibPR.ClockShiftAlgebra.RatPair.add
        MathlibPR.ClockShiftAlgebra.cyclotomicOrder3RealSq
        MathlibPR.ClockShiftAlgebra.cyclotomicOrder3ImagSq)
      MathlibPR.ClockShiftAlgebra.cyclotomicOrder3NormSq :=
  MathlibPR.ClockShiftAlgebra.su3_cyclotomic_norm_sq_eval

theorem check_jordan_spectral_gap_pos_unconditional :
    (∀ (N : Nat) (hN : 2 ≤ N),
      MathlibPR.ClockShiftAlgebra.RatPair.lt
        (MathlibPR.ClockShiftAlgebra.RatPair.ofNat 0)
        (MathlibPR.ClockShiftAlgebra.jordanBoundPair N hN)) :=
  MathlibPR.ClockShiftAlgebra.jordan_spectral_gap_pos

theorem check_secant_asymptotic_gap_pos_unconditional :
    (∀ (N : Nat) (hN : 6 ≤ N),
      MathlibPR.ClockShiftAlgebra.RatPair.lt
        (MathlibPR.ClockShiftAlgebra.RatPair.ofNat 0)
        (MathlibPR.ClockShiftAlgebra.secantBoundPair N hN)) :=
  MathlibPR.ClockShiftAlgebra.secant_asymptotic_gap_pos

theorem check_secant_asymptotic_gap_six_eval_unconditional :
    MathlibPR.ClockShiftAlgebra.RatPair.eqv
      (MathlibPR.ClockShiftAlgebra.secantBoundPair 6 (by omega))
      (MathlibPR.ClockShiftAlgebra.RatPair.ofNat 1) :=
  MathlibPR.ClockShiftAlgebra.secant_asymptotic_gap_six_eval

theorem check_su5_rational_gap_witness_unconditional :
    (5 : Nat) * (72 * 72) < 161 * 161 ∧ 5 * 72 - 161 = 199 :=
  MathlibPR.ClockShiftAlgebra.su5_rational_gap_witness

theorem check_su5_gap_gt_jordan_unconditional :
    MathlibPR.ClockShiftAlgebra.RatPair.lt
      (MathlibPR.ClockShiftAlgebra.jordanBoundPair 5 (by omega))
      MathlibPR.ClockShiftAlgebra.su5LowerBoundPair :=
  MathlibPR.ClockShiftAlgebra.su5_gap_gt_jordan

-- Verbatim kernel axiom footprints for real-analysis, calculus, matrix, and certificate theorems
#print axioms PolydiskMajorant.tsum_geometric_tail_le
#print axioms CubicSinBounds.sin_sq_le_sq
#print axioms CubicSinBounds.integral_sin_sq_le_cubic
#print axioms CubicSinBounds.normalized_sin_sq_integral_le_cubicCollarWeight
#print axioms QuaternionCentralizer.adjointTwistQuadraticForm_eq
#print axioms QuaternionCentralizer.adjointTwistQuadraticForm_ge_three
#print axioms ClockShiftMatrices.clock3_mul_shift3_eq
#print axioms ClockShiftMatrices.chord_normSq_eq_four_mul_sin_sq
#print axioms ClockShiftMatrices.mul_le_sin_of_mem_Icc
#print axioms ClockShiftMatrices.jordan_spectral_gap_le_four_mul_sin_sq
#print axioms ClockShiftMatrices.secant_spectral_gap_le_four_mul_sin_sq
#print axioms ClockShiftMatrices.four_mul_sin_pi_div_five_sq_eq
#print axioms ClockShiftMatrices.four_mul_sin_pi_div_five_sq_gt
#print axioms YangMillsBlueprint.Certificates.canonical_polymer_tsum_bound
#print axioms YangMillsBlueprint.Certificates.su2_real_weyl_collar_integral_lt_margin
#print axioms YangMillsBlueprint.Certificates.su3_clock_shift_commutation
#print axioms YangMillsBlueprint.Certificates.su5_real_spectral_gap_gt
#print axioms YangMillsBlueprint.Certificates.sun_real_jordan_gap_le
#print axioms YangMillsBlueprint.Certificates.sun_real_secant_gap_le
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.ZeroModeStiffnessCert)
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.SpiralTwistCert)
#print axioms NonAbelianCommutatorStiffness.lagrange_identity
#print axioms NonAbelianCommutatorStiffness.cross_normSq_eq_of_ortho
#print axioms NonAbelianCommutatorStiffness.triadQuarticEnergy_ge_three_mul_sq
#print axioms CoprimeSpiralTwist.spiralMap_eq_zero_iff
#print axioms CoprimeSpiralTwist.spiral_both_coords_ne_zero
#print axioms CoprimeSpiralTwist.spiralMap_bijective
#print axioms CoprimeSpiralTwist.two_plane_gap_lower_bound
#print axioms YangMillsBlueprint.Certificates.su2_zero_mode_quartic_stiffness_pos_conditional
#print axioms YangMillsBlueprint.Certificates.canonical_zero_mode_energy_eq_three
#print axioms YangMillsBlueprint.Certificates.spiral_twist_both_planes_nonzero
#print axioms YangMillsBlueprint.Certificates.sun_coprime_spiral_two_plane_gap_le
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.LuscherQuantumGapCert)
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.CenterlessGroupRigidityCert)
#print axioms QuarticQuantumStiffness.cubic_defect_factorization
#print axioms QuarticQuantumStiffness.variationalEnergy_sub_min_eq
#print axioms QuarticQuantumStiffness.three_mul_sq_le_variationalEnergy
#print axioms QuarticQuantumStiffness.variationalEnergy_pos
#print axioms CartanCoxeterRigidity.g2CartanDet_eq_one
#print axioms CartanCoxeterRigidity.two_mul_g2CartanForm_eq
#print axioms CartanCoxeterRigidity.six_mul_f4CartanForm_eq
#print axioms CartanCoxeterRigidity.g2CartanForm_eq_zero_iff
#print axioms CartanCoxeterRigidity.f4CartanForm_eq_zero_iff
#print axioms YangMillsBlueprint.Certificates.luscher_zero_mode_quantum_gap_ge_conditional
#print axioms YangMillsBlueprint.Certificates.canonical_luscher_quantum_gap_pos
#print axioms YangMillsBlueprint.Certificates.g2_coxeter_cartan_zero_mode_eliminated
#print axioms YangMillsBlueprint.Certificates.f4_coxeter_cartan_zero_mode_eliminated
#print axioms YangMillsBlueprint.Certificates.g2_unit_root_stiffness
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.VortexAreaScreeningCert)
#check (inferInstance : Nonempty YangMillsBlueprint.Certificates.AsymptoticFreedomCert)
#print axioms ExponentialAreaScreening.cubic_div_twenty_seven_le_exp
#print axioms ExponentialAreaScreening.quartic_mul_exp_neg_sq_le
#print axioms AsymptoticFreedomFlow.inv_runningCoupling_eq
#print axioms AsymptoticFreedomFlow.runningCoupling_le_inv_mul
#print axioms AsymptoticFreedomFlow.telescoping_step_eq
#print axioms AsymptoticFreedomFlow.telescoped_sum_lt_one
#print axioms YangMillsBlueprint.Certificates.vortex_free_energy_defect_le_real
#print axioms YangMillsBlueprint.Certificates.canonical_vortex_defect_lt_one
#print axioms YangMillsBlueprint.Certificates.uv_running_coupling_contraction_conditional
#print axioms YangMillsBlueprint.Certificates.canonical_uv_coupling_lt_one

end YangMillsBlueprint.VerifyNoTraps
