# Section 02 — All-Orders Polymer Contraction & Weyl Collar Integral Bounds

## Physical Intuition

Near the two central elements $\pm I \in Z(\mathrm{SU}(2))$ ($\theta = 0, \pi$), classical plaquette action gradients vanish. Quantum integration over the compact gauge group rescues small-field control through the reduced Haar measure $\frac{2}{\pi}\sin^2\theta\,d\theta$, which vanishes quadratically at both poles and repels configurations from flat collars. Paired with an all-orders geometric `tsum` polydisk tail bound leaving margin $m = 1/57$, Lean 4 proves via genuine Lebesgue interval integration that at collar radius $\delta = 1/5$:

$$\frac{4}{\pi}\int_0^{1/5} \sin^2\theta\,d\theta < \frac{1}{57}.$$

## Included Files

- Manuscript: [`paper_2_polymer_collar_lean.pdf`](paper_2_polymer_collar_lean.pdf) ([LaTeX source](paper_2_polymer_collar_lean.tex))
- Lean 4 modules (`lean/`):
  - [`PolydiskMajorant.lean`](lean/PolydiskMajorant.lean)
  - [`CubicSinBounds.lean`](lean/CubicSinBounds.lean)
  - [`YM101_CauchyPolydiskCert.lean`](lean/YM101_CauchyPolydiskCert.lean)
  - [`YM102_WeylCollarCert.lean`](lean/YM102_WeylCollarCert.lean)

## Lean 4 Verification Ledger

| Declaration | Role | Kernel Axiom Footprint |
|---|---|---|
| `PolydiskMajorant.total_weight_lt_one` | Leading + tail contraction $< 1$ over ordered fields | `[propext, Classical.choice, Quot.sound]` |
| `PolydiskMajorant.summable_geometric_tail` | Summability of shifted series $n \mapsto w^{n+1}$ | `[propext, Classical.choice, Quot.sound]` |
| `PolydiskMajorant.tsum_geometric_tail_le` | Infinite `tsum` bound $\le (1 - m)/m$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.canonical_polymer_tsum_bound` | Exact rational convergence at $m = 1/57$ | `[propext, Classical.choice, Quot.sound]` |
| `CubicSinBounds.sin_sq_le_sq` | Pointwise bound $\sin^2\theta \le \theta^2$ | `[propext, Classical.choice, Quot.sound]` |
| `CubicSinBounds.integral_sin_sq_le_cubic` | Lebesgue integral $\int_0^\delta \sin^2\theta\,d\theta \le \delta^3/3$ | `[propext, Classical.choice, Quot.sound]` |
| `CubicSinBounds.normalized_sin_sq_integral_le_cubicCollarWeight` | Antitone rational $\pi$ proxy bridge | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.su2_real_weyl_collar_integral_lt_margin` | Certified real collar integral $< 1/57$ at $\delta = 1/5$ | `[propext, Classical.choice, Quot.sound]` |
