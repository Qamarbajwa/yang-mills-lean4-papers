# Section 01 — Ultraviolet Flow & Asymptotic Scaling

## Physical Intuition

In four-dimensional gauge theory, short-distance fluctuations diverge on bare lattice links unless smoothed by gauge-invariant diffusion. Gradient flow evolves link variables along an auxiliary flow time $t > 0$, smearing modes over radius $r_t = \sqrt{8t}$ inside the unbuffered half-space $x_0 \ge 0$ while keeping $x_0 > r_t$ free of boundary contact singularities. Simultaneously, asymptotic freedom drives the inverse running coupling linearly upward:

$$\frac{1}{g_k^2} = \frac{1}{g_0^2} + k b,$$

forcing $g_k^2 \le 1/(kb)$ across renormalization steps $k$. Together with the non-stub real inner-product Hilbert space coercivity predicate `HasOrthogonalCoercivity`, this section establishes local finite-volume Osterwalder–Schrader reconstruction at $\theta = 0$ and machine-checks the algebraic UV flow and real spectral coercivity lemmas. The infinite-volume thermodynamic limit and Clay Millennium mass gap remain open.

## Included Files

- Manuscript: [`paper_1_uv_flowed_construction.pdf`](paper_1_uv_flowed_construction.pdf) ([LaTeX source](paper_1_uv_flowed_construction.tex))
- Lean 4 modules (`lean/`):
  - [`AsymptoticFreedomFlow.lean`](lean/AsymptoticFreedomFlow.lean)
  - [`SpectralMassGapBridge.lean`](lean/SpectralMassGapBridge.lean)
  - [`YM110_AsymptoticFreedomCert.lean`](lean/YM110_AsymptoticFreedomCert.lean)
  - [`YM111_ClayTargetSpecCert.lean`](lean/YM111_ClayTargetSpecCert.lean)

## Lean 4 Verification Ledger

| Declaration | Role | Kernel Axiom Footprint |
|---|---|---|
| `AsymptoticFreedomFlow.inv_runningCoupling_eq` | Exact linear inverse coupling $1/g_k = 1/g_0 + kb$ | `[propext, Classical.choice, Quot.sound]` |
| `AsymptoticFreedomFlow.runningCoupling_le_inv_mul` | Scale contraction $g_k \le 1/(kb)$ | `[propext, Classical.choice, Quot.sound]` |
| `AsymptoticFreedomFlow.telescoped_sum_lt_one` | Telescoping step defect $< 1$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.canonical_uv_coupling_lt_one` | Step $k=5$ witness at $g_0^2 = 24/41, b = 11/24$ | `[propext, Classical.choice, Quot.sound]` |
| `SpectralMassGapBridge.coercivity_orthogonal_decomp` | Orthogonal complement quadratic bound $\Delta \|\psi\|^2 \le \langle \varphi, T\varphi\rangle$ | `[propext, Classical.choice, Quot.sound]` |
| `SpectralMassGapBridge.coercivity_pos_of_perp_ne_zero` | Strict positivity for nonzero orthogonal excitation | `[propext, Classical.choice, Quot.sound]` |
| `SpectralMassGapBridge.exp_neg_mul_anti` | Monotonicity of exponential clustering rate | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.real_mass_gap_spec_excited_pos` | Non-stub `InnerProductSpace ℝ H` gap excitation bound | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.canonical_clustering_decay_le` | Exponential decay bound at $\Delta = 3$ | `[propext, Classical.choice, Quot.sound]` |
