# Section 03 — Orthogonal Twist Rigidity, Coprime Spirals & Positive-Definite Cartan Forms

## Physical Intuition

On a periodic spatial torus $T^3$, commuting constant holonomies sweep out flat zero-action toron valleys. Imposing orthogonal 't Hooft magnetic boundary twists forces holonomy matrices to satisfy Weyl–Heisenberg commutation $P Q = \omega Q P$, collapsing the centralizer kernel to zero: quaternions give $\lambda_{\min}(\mathrm{SU}(2)) = 4$, $3 \times 3$ Sylvester clock-and-shift matrices give $\lambda_{\min}(\mathrm{SU}(3)) = 3$, and strict concavity of `Real.sin` proves Jordan ($16/N^2$) and secant ($36/N^2$) spectral bounds across $\mathrm{SU}(N)$. For large rank $N$, 2D coprime spirals $m \mapsto (m, km \bmod N)$ on `ZMod N` and 4-plane symmetric shear scaling ($N = L^2$, yielding $16/N$ single-plane and $64/N$ four-plane gaps) prevent coordinate-axis degeneration. For arbitrary-rank $A_n$ and exceptional groups $G_2, F_4, E_6, E_7, E_8$ (covering the centerless systems $G_2, F_4, E_8$), exact integer-scaled Cholesky sum-of-squares factorizations prove unconditional positive-definite Cartan elimination.

## Included Files

- Manuscript: [`paper_3_twisted_rigidity_lean.pdf`](paper_3_twisted_rigidity_lean.pdf) ([LaTeX source](paper_3_twisted_rigidity_lean.tex))
- Lean 4 modules (`lean/`):
  - Foundational: `QuaternionCentralizer.lean`, `ClockShiftMatrices.lean`, `CoprimeSpiralTwist.lean`, `TEKFourPlaneLattice.lean`, `CartanCoxeterRigidity.lean`, `ExceptionalE8Cartan.lean`, `ClassicalAndExceptionalCartan.lean`
  - Certificates: `YM103`, `YM104`, `YM106`, `YM108`, `YM112`, `YM113`, `YM114`

## Lean 4 Verification Ledger

| Declaration | Role | Kernel Axiom Footprint |
|---|---|---|
| `Certificates.su2_toron_zero_mode_eliminated` | $\mathrm{SU}(2)$ quaternion twist gap $= 4$, ker $= 0$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.su3_clock_shift_spectral_gap_eq_three` | $\mathrm{SU}(3)$ Sylvester gap $= 3$ | `[propext, Classical.choice, Quot.sound]` |
| `ClockShiftMatrices.jordan_spectral_gap_le_four_mul_sin_sq` | Real Jordan bound $16/N^2 \le 4\sin^2(\pi/N)$ | `[propext, Classical.choice, Quot.sound]` |
| `ClockShiftMatrices.four_mul_sin_pi_div_five_sq_gt` | Exact $\mathrm{SU}(5)$ bound $> 199/144$ | `[propext, Classical.choice, Quot.sound]` |
| `CoprimeSpiralTwist.spiral_both_coords_ne_zero` | Simultaneous non-vanishing on $(\mathbb{Z}/N\mathbb{Z})^2$ | `[propext, Quot.sound]` |
| `TEKFourPlaneLattice.shearMap_bijective` | Unimodular 2D/4D shear bijection | `[propext, Quot.sound]` |
| `Certificates.canonical_tek_four_plane_gap_gt_one` | Rank $N=36$ four-plane gap $> 1$ | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.g2_coxeter_cartan_zero_mode_eliminated` | Rank-2 $G_2$ Cartan rigidity ($\det = 1$) | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.f4_coxeter_cartan_zero_mode_eliminated` | Rank-4 $F_4$ Cartan rigidity ($\det = 1$) | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.e6_coxeter_cartan_zero_mode_eliminated` | Rank-6 $E_6$ Cholesky sum-of-squares elimination | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.e7_coxeter_cartan_zero_mode_eliminated` | Rank-7 $E_7$ Cholesky sum-of-squares elimination | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.e8_coxeter_cartan_zero_mode_eliminated` | Rank-8 $E_8$ `840`-scaled 8-square elimination | `[propext, Classical.choice, Quot.sound]` |
| `Certificates.su_an_cartan_zero_mode_eliminated` | Universal arbitrary-rank $A_{n+1}$ Cartan elimination | `[propext, Classical.choice, Quot.sound]` |
