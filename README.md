# Four-Dimensional Lattice Yang–Mills Theory: Modular Micro-Papers & Lean 4 Verification (`YM101`–`YM117`, v0.7.0)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24327877.svg)](https://doi.org/10.5281/zenodo.24327877)

**Author:** Qamar Munawer  
**Affiliation:** Brandenburg University of Technology Cottbus–Senftenberg (BTU Cottbus–Senftenberg), Cottbus, Germany  
**Epistemic Status:** `clay_problem: OPEN_AND_UNSOLVED` | `goal_complete: false`  
**Kernel Axioms:** Strictly subsets of `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`)

---

## Overview

This repository packages four concise, study-friendly research micro-papers together with a unified, axiom-audited Lean 4 formalization (`formal/yang_mills_blueprint/`) spanning `YM101` through `YM117` (34 modular Lean 4 files: 17 Mathlib-ready foundational modules and 17 domain certificates, completing 100% Killing–Cartan coverage across $A_n, B_n, C_n, D_n, G_2, F_4, E_6, E_7, E_8$). Each theorem is machine-checked inside Lean 4 (`VerifyNoTraps.lean`), while explicitly separating verified finite-volume and algebraic bounds from the open Clay Millennium infinite-volume continuum mass gap problem ($\Delta > 0$).

## Sub-Sections

| Section | Focus | Micro-Paper | Lean Certificates |
|---|---|---|---|
| [01 — UV Flow & Asymptotic Scaling](sections/01_uv_flow_and_asymptotic_scaling/) | Gradient flow half-space smoothing, inverse coupling flow, Hilbert gap coercivity | [Paper 1 (PDF)](sections/01_uv_flow_and_asymptotic_scaling/paper_1_uv_flowed_construction.pdf) | `YM110`, `YM111` |
| [02 — Polymer Contraction & Weyl Collar](sections/02_polymer_contraction_and_weyl_collar/) | Infinite geometric `tsum` convergence & Lebesgue $\frac{4}{\pi}\int_0^{1/5}\sin^2\theta\,d\theta < \frac{1}{57}$ | [Paper 2 (PDF)](sections/02_polymer_contraction_and_weyl_collar/paper_2_polymer_collar_lean.pdf) | `YM101`, `YM102` |
| [03 — Twisted Rigidity, Spirals & Cartan](sections/03_twisted_rigidity_spirals_and_cartan/) | Quaternion / Sylvester twists, 2D/4D `ZMod N` spirals, complete Killing–Cartan ($A_n,B_n,C_n,D_n,G_2,F_4,E_6,E_7,E_8$) | [Paper 3 (PDF)](sections/03_twisted_rigidity_spirals_and_cartan/paper_3_twisted_rigidity_lean.pdf) | `YM103`, `YM104`, `YM106`, `YM108`, `YM112`, `YM113`, `YM114`, `YM117` |
| [04 — Zero-Mode Stiffness & Crossover Atlas](sections/04_zero_mode_stiffness_and_crossover_atlas/) | Triad commutator stiffness, Lüscher gap $3bx_0^2$, Levi strata, loop bootstrap & vortex screening | [Paper 4 (PDF)](sections/04_zero_mode_stiffness_and_crossover_atlas/paper_4_crossover_obstruction_atlas.pdf) | `YM105`, `YM107`, `YM109`, `YM115`, `YM116` |

## Reproduce Verification Locally

```bash
cd formal/yang_mills_blueprint
lake build
lake env lean YangMillsBlueprint/VerifyNoTraps.lean
```

Full kernel `#print axioms` verification output for `YM101`–`YM117` is archived in [`VERIFY_LOG.txt`](VERIFY_LOG.txt) and Zenodo archive metadata in [`.zenodo.json`](.zenodo.json).
