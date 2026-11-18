# Four-Dimensional Lattice Yang–Mills Theory: Modular Micro-Papers & Lean 4 Verification (`YM101`–`YM136`, v1.2.0)

**Author:** Qamar Munawer  
**Affiliation:** Brandenburg University of Technology Cottbus–Senftenberg (BTU Cottbus–Senftenberg), Cottbus, Germany  
**Epistemic Status:** `clay_problem: OPEN_AND_UNSOLVED` | `goal_complete: false`  
**Standalone Lean Reservoir Package:** https://github.com/Qamarbajwa/yang-mills-lean4  
**Kernel Axioms:** Strictly subsets of `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`)

---

## Sub-Sections

| Section | Focus | Micro-Paper | Lean Certificates |
|---|---|---|---|
| [01 — UV Flow, OS Clustering & Ursell Cumulants](sections/01_uv_flow_and_asymptotic_scaling/) | Gradient flow smoothing, UV running coupling, Hilbert gap coercivity, Symanzik bounds, OPE non-triviality, OS clustering, continuum tightness, transfer-matrix log-convexity, Ursell $u_4 \neq 0$ | [Paper 1 (PDF)](sections/01_uv_flow_and_asymptotic_scaling/paper_1_uv_flowed_construction.pdf) | `YM110`, `YM111`, `YM120`, `YM121`, `YM126`, `YM127`, `YM129`, `YM135` |
| [02 — Polymer Contraction & Weyl Collar](sections/02_polymer_contraction_and_weyl_collar/) | Infinite geometric `tsum` convergence & Lebesgue $\frac{4}{\pi}\int_0^{1/5}\sin^2\theta\,d\theta < \frac{1}{57}$ | [Paper 2 (PDF)](sections/02_polymer_contraction_and_weyl_collar/paper_2_polymer_collar_lean.pdf) | `YM101`, `YM102` |
| [03 — Twisted Rigidity, Spirals & Cartan](sections/03_twisted_rigidity_spirals_and_cartan/) | Quaternion / Sylvester twists, 2D/4D `ZMod N` spirals, complete Killing–Cartan ($A_n,B_n,C_n,D_n,G_2,F_4,E_6,E_7,E_8$), centerless alcove & general adjoint Bianchi bounds | [Paper 3 (PDF)](sections/03_twisted_rigidity_spirals_and_cartan/paper_3_twisted_rigidity_lean.pdf) | `YM103`, `YM104`, `YM106`, `YM108`, `YM112`, `YM113`, `YM114`, `YM117`, `YM130`, `YM136` |
| [04 — Zero-Mode Stiffness & Crossover Atlas](sections/04_zero_mode_stiffness_and_crossover_atlas/) | Triad stiffness, Lüscher gap, Levi strata, loop bootstrap, Brascamp–Lieb & Dobrushin bridges, inductive Peierls RG, spatial RP, Tomboulis flow, FILS chessboard, thick vortices, GI coset Creutz & 3-cube Bianchi defects | [Paper 4 (PDF)](sections/04_zero_mode_stiffness_and_crossover_atlas/paper_4_crossover_obstruction_atlas.pdf) | `YM105`, `YM107`, `YM109`, `YM115`, `YM116`, `YM118`, `YM119`, `YM122`, `YM123`, `YM124`, `YM125`, `YM128`, `YM131`, `YM132`, `YM133`, `YM134` |

Full kernel `#print axioms` verification output (`YM101`–`YM136`) is archived in [`VERIFY_LOG.txt`](VERIFY_LOG.txt).
