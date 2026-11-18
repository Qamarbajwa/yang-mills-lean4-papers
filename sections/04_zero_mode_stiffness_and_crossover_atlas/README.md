# Section 04 — Zero-Mode Stiffness, Levi Strata, Bootstrap Bounds & Crossover Atlas

## Physical Intuition

Even when Gaussian small-field bounds break down at renormalization scale $k = 5$ ($g_5^2 = 24/41 > 1/2$), non-Abelian gluons retain geometric stiffness: constant triad potentials pay quartic commutator energy $\|u \times v\|^2 + \|v \times w\|^2 + \|w \times u\|^2 \ge 3a^2$ ("Energy of Zero"), and transverse quantum uncertainty raises Lüscher's Rayleigh–Ritz energy $(2 b x_0^3)/x + b x^2$ strictly above the variational floor $3 b x_0^2$ via an exact cubic defect factorization. On periodic strata, Levi-stratum mode conservation confirms that central zero-mode strata reduce harmonic $1/\beta$ exponents relative to regular torons ($\alpha_{\mathrm{harm}} \le \alpha_{\mathrm{reg}}$), Schur-complement positivity pins Level-4 Makeenko–Migdal loop bootstrap envelopes inside $(2\beta w - 3)^2 \le 9 + 20\beta^2$, and Peierls–Tomboulis center-vortex screening proves $L^4 e^{-\sigma L^2} \le 27 / (\sigma^3 L^2)$ from $u^3 / 27 \le e^u$. Infinite-volume closure across $g_k^2 \sim 1$ and $L \to \infty$ remains open.

## Included Files

- Manuscript: [`paper_4_crossover_obstruction_atlas.pdf`](paper_4_crossover_obstruction_atlas.pdf) ([LaTeX source](paper_4_crossover_obstruction_atlas.tex))
- Lean 4 modules (`lean/`):
  - Foundational: `NonAbelianCommutatorStiffness.lean`, `QuarticQuantumStiffness.lean`, `ExponentialAreaScreening.lean`, `LeviStratumCounting.lean`, `LoopBootstrapMomentBounds.lean`
  - Certificates: `YM105`, `YM107`, `YM109`, `YM115`, `YM116`

## Lean 4 Verification Ledger

| Declaration | Role | Kernel Axiom Footprint |
|---|---|---|
| `NonAbelianCommutatorStiffness.lagrange_identity` | Algebraic cross-product identity over any commutative ring | `[propext, Quot.sound]` |
| `Certificates.canonical_zero_mode_energy_eq_three` | $\mathrm{SU}(2)$ triad energy at $g_5^2 = 24/41$ | `[propext, Classical.choice, Quot.sound]` |
| `QuarticQuantumStiffness.cubic_defect_factorization` | Exact defect identity $(b/x)(x-x_0)^2(x+2x_0)$ | `[propext, Quot.sound]` |
| `Certificates.canonical_luscher_quantum_gap_pos` | Lüscher variational floor $3 b x_0^2 > 0$ at $b = 24/41$ | `[propext, Classical.choice, Quot.sound]` |
| `ExponentialAreaScreening.quartic_mul_exp_neg_sq_le` | Vortex screening $L^4 e^{-\sigma L^2} \le 27 / (\sigma^3 L^2)$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.canonical_vortex_defect_lt_one` | Screening witness $< 27/100 < 1$ at $\sigma=1, L=10$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.su_n_levi_stratum_mode_balance` | Exact 4D Levi mode-dimension conservation | `[propext, Quot.sound]` |
| `Certificates.su3_central_vs_regular_exponent_eval` | $\mathrm{SU}(3)$ central exponent $8 \le 9$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.crossover_level4_bootstrap_window` | Schur + Level-4 loop equation completed square | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.crossover_level4_domino_coupling_conditional` | Conditional Level-4/Level-6 conjunction at `E-CROSSOVER` | `[propext, Classical.choice, Quot.sound]` |
