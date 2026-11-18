/-
  YangMillsBlueprint.MissingBridgeInterfaces
  ==========================================
  Specification checklist of open analytic obligations separating Part I
  from continuum constructive Yang-Mills closure:
  - Edge E-CROSSOVER (YM-059F, YM-060F, YM-101F): Non-perturbative toron zero-mode projection.
  - Edge E-LATTICE-CONT: Uniform non-perturbative RG continuum step (a -> 0).
  - Edge E-THERMO: Uniform thermodynamic limit (L -> infinity) at fixed spectral gap.
  - Edges E-CONT-SCHWINGER & OS0..OS4: Temperedness, Euclidean symmetry, reflection positivity, clustering.
  - Edge E-NONTRIV-WITNESS: Non-trivial scattering / non-Gaussianity witness.
  - Edge E-GROUP-GEN: Extension across all compact simple Lie groups.

  NOTE: This file defines a typed specification checklist and internal
  dependency-completeness check. It is NOT a mathematical proof of the Clay problem.
-/
import YangMillsBlueprint.BasicTypes

namespace YangMillsBlueprint.Interfaces

/-- Epistemic status of a bridge edge matching `literature/OPEN_EDGE_REGISTER.md`. -/
inductive BridgeEdgeStatus where
  | closed
  | regulatedOnly
  | conditional
  | openUnproved
  deriving Repr, DecidableEq

/-- Canonical open bridge edge identifier in the YM-003 missing-bridge DAG. -/
structure OpenBridgeEdge where
  edgeId : String
  srcRank : Nat
  dstRank : Nat
  status : BridgeEdgeStatus
  deriving Repr

/--
  Typed specification checklist isolating every open analytic obligation
  separating finite/algebraic theorems from continuum constructive QFT.
-/
structure ContinuumTransferObligations where
  /-- Edge E-CROSSOVER (YM-059F, YM-060F, YM-101F): Uniform IR toron projection below 17838/1000000 margin. -/
  e_crossover_toron_projection : Prop
  /-- Edge E-LATTICE-CONT: Uniform non-perturbative RG step across crossover to continuum limit a -> 0. -/
  e_lattice_cont_rg_step : Prop
  /-- Edge E-THERMO: Uniform infinite-volume thermodynamic limit L -> infinity at fixed gap. -/
  e_thermo_infinite_volume : Prop
  /-- Edge E-CONT-SCHWINGER: Convergence of lattice expectations to tempered Schwinger distributions. -/
  e_cont_schwinger_distributions : Prop
  /-- Edge E-SCHWINGER-OS0: Analyticity / temperedness growth axiom OS0. -/
  e_schwinger_os0_tempered : Prop
  /-- Edge E-SCHWINGER-OS1: Full Euclidean SO(4) rotation + translation invariance OS1. -/
  e_schwinger_os1_euclidean : Prop
  /-- Edge E-SCHWINGER-OS2: Permutation symmetry OS2 (currently CONDITIONAL on continuum convergence). -/
  e_schwinger_os2_symmetry : Prop
  /-- Edge E-SCHWINGER-OS3: Non-perturbative reflection positivity OS3 in continuum limit. -/
  e_schwinger_os3_reflection_positivity : Prop
  /-- Edge E-SCHWINGER-OS4: Exponential cluster decomposition OS4 uniformly at finite Delta > 0. -/
  e_schwinger_os4_cluster_gap : Prop
  /-- Edge E-NONTRIV-WITNESS: Non-trivial interacting scattering / non-Gaussianity witness. -/
  e_nontriv_witness : Prop
  /-- Edge E-GROUP-GEN: Full extension across all compact simple Lie groups G. -/
  e_group_gen_sun : Prop
  /-- Target Clay Millennium existence + nonzero mass gap statement. -/
  clay_existence_and_mass_gap : Prop
  /-- Verified Osterwalder-Schrader reconstruction implication schema (if all OS0-OS4 + nontriviality hold, Clay holds). -/
  os_reconstruction_implies_clay :
    e_crossover_toron_projection →
    e_lattice_cont_rg_step →
    e_thermo_infinite_volume →
    e_cont_schwinger_distributions →
    e_schwinger_os0_tempered →
    e_schwinger_os1_euclidean →
    e_schwinger_os2_symmetry →
    e_schwinger_os3_reflection_positivity →
    e_schwinger_os4_cluster_gap →
    e_nontriv_witness →
    e_group_gen_sun →
    clay_existence_and_mass_gap

/-- Backwards-compatible alias for specification interface. -/
abbrev ClassicalYangMillsBridgeInterface := ContinuumTransferObligations

/-- Explicit witness bundle packing proofs of all fields of `ContinuumTransferObligations`. -/
structure BridgeAssumptions (I : ContinuumTransferObligations) : Prop where
  h_cross : I.e_crossover_toron_projection
  h_cont : I.e_lattice_cont_rg_step
  h_thermo : I.e_thermo_infinite_volume
  h_dist : I.e_cont_schwinger_distributions
  h_os0 : I.e_schwinger_os0_tempered
  h_os1 : I.e_schwinger_os1_euclidean
  h_os2 : I.e_schwinger_os2_symmetry
  h_os3 : I.e_schwinger_os3_reflection_positivity
  h_os4 : I.e_schwinger_os4_cluster_gap
  h_nontriv : I.e_nontriv_witness
  h_group : I.e_group_gen_sun

/--
  Internal dependency-completeness check:
  Purely constructive, zero custom axioms (`axioms: []`), checking that the
  target continuum properties follow IF all explicit transfer obligations in
  `BridgeAssumptions I` are satisfied.
  This is an internal specification check, NOT an independent mathematical proof.
-/
theorem check_continuum_obligations_deduction
    (I : ContinuumTransferObligations)
    (h : BridgeAssumptions I) :
    I.clay_existence_and_mass_gap :=
  I.os_reconstruction_implies_clay
    h.h_cross h.h_cont h.h_thermo h.h_dist
    h.h_os0 h.h_os1 h.h_os2 h.h_os3 h.h_os4
    h.h_nontriv h.h_group

/-- Backwards-compatible alias for the dependency-completeness check. -/
abbrev conditional_clay_mass_gap_of_bridges := @check_continuum_obligations_deduction

/-- Canonical remaining open edges tracked from `literature/OPEN_EDGE_REGISTER.md`. -/
def openClayBridgeEdges : List OpenBridgeEdge :=
  [ ⟨"E-UV-RG",            0, 1, .regulatedOnly⟩
  , ⟨"E-CROSSOVER",        1, 2, .openUnproved⟩
  , ⟨"E-LATTICE-GAP",      1, 2, .regulatedOnly⟩
  , ⟨"E-LATTICE-CONT",     2, 3, .openUnproved⟩
  , ⟨"E-THERMO",           2, 3, .openUnproved⟩
  , ⟨"E-CONT-SCHWINGER",   3, 4, .openUnproved⟩
  , ⟨"E-SCHWINGER-OS0",    4, 5, .openUnproved⟩
  , ⟨"E-SCHWINGER-OS1",    4, 5, .openUnproved⟩
  , ⟨"E-SCHWINGER-OS2",    4, 5, .conditional⟩
  , ⟨"E-SCHWINGER-OS3",    4, 5, .openUnproved⟩
  , ⟨"E-SCHWINGER-OS4",    4, 5, .openUnproved⟩
  , ⟨"E-NONTRIV-WITNESS",  5, 6, .openUnproved⟩
  , ⟨"E-GROUP-GEN",        5, 6, .openUnproved⟩
  ]

/-- Theorem (Part I): Every open bridge edge strictly advances topological rank (acyclic DAG). -/
theorem bridge_dag_acyclic_rank :
    openClayBridgeEdges.all (fun e => decide (e.srcRank < e.dstRank)) = true := by
  decide

end YangMillsBlueprint.Interfaces
