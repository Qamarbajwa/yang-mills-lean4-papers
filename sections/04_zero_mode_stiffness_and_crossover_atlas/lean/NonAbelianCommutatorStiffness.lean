/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Three-Space Cross-Product Stiffness and Quartic Triad Coercivity

This file establishes Lagrange's polynomial identity `‖u × v‖² + ⟨u, v⟩² = ‖u‖² ‖v‖²` on a
three-dimensional module `R³` and proves that any mutually orthogonal triad `(u, v, w)` with
component squared norms bounded below by `a ≥ 0` satisfies the quartic coercivity bound
`3 * a ^ 2 ≤ ‖u × v‖² + ‖v × w‖² + ‖w × u‖²`.

## Main results

* `NonAbelianCommutatorStiffness.lagrange_identity`:
  `normSq (cross u v) + (dot u v) ^ 2 = normSq u * normSq v`.
* `NonAbelianCommutatorStiffness.cross_normSq_eq_of_ortho`:
  transverse coercivity when `dot u v = 0`.
* `NonAbelianCommutatorStiffness.triadQuarticEnergy_ge_three_mul_sq`:
  lower bound `3 * a ^ 2` for mutually orthogonal triads.
-/

@[expose] public section

namespace NonAbelianCommutatorStiffness

variable {R : Type*} [CommRing R]

/-- A vector in three-space `R³`. -/
structure Vec3 (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq

/-- Standard bilinear dot product on `R³`. -/
def dot (u v : Vec3 R) : R :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Squared Euclidean norm `⟨u, u⟩`. -/
def normSq (u : Vec3 R) : R :=
  dot u u

/-- Standard alternating cross product `u × v` on `R³`. -/
def cross (u v : Vec3 R) : Vec3 R where
  x := u.y * v.z - u.z * v.y
  y := u.z * v.x - u.x * v.z
  z := u.x * v.y - u.y * v.x

/-- Quartic commutator triad energy `‖u × v‖² + ‖v × w‖² + ‖w × u‖²`. -/
def triadQuarticEnergy (u v w : Vec3 R) : R :=
  normSq (cross u v) + normSq (cross v w) + normSq (cross w u)

/-- Lagrange's polynomial identity: `‖u × v‖² + ⟨u, v⟩² = ‖u‖² ‖v‖²`. -/
theorem lagrange_identity (u v : Vec3 R) :
    normSq (cross u v) + (dot u v) ^ 2 = normSq u * normSq v := by
  unfold normSq cross dot
  ring

/-- Transverse coercivity: if `u` and `v` are orthogonal (`dot u v = 0`), the squared norm of
their cross product equals the product of their squared norms. -/
theorem cross_normSq_eq_of_ortho {u v : Vec3 R} (h_ortho : dot u v = 0) :
    normSq (cross u v) = normSq u * normSq v := by
  have h := lagrange_identity u v
  rw [h_ortho] at h
  simpa using h

/-- For any mutually orthogonal triad `(u, v, w)`, the quartic triad energy equals the
symmetric quadratic elementary polynomial in `normSq u`, `normSq v`, and `normSq w`. -/
theorem triadQuarticEnergy_eq_of_ortho {u v w : Vec3 R}
    (huv : dot u v = 0) (hvw : dot v w = 0) (hwu : dot w u = 0) :
    triadQuarticEnergy u v w =
      normSq u * normSq v + normSq v * normSq w + normSq w * normSq u := by
  unfold triadQuarticEnergy
  rw [cross_normSq_eq_of_ortho huv, cross_normSq_eq_of_ortho hvw,
    cross_normSq_eq_of_ortho hwu]

/-- Over a linearly ordered commutative ring, if `(u, v, w)` are mutually orthogonal and each
mode has squared norm at least `a ≥ 0`, then `3 * a ^ 2 ≤ triadQuarticEnergy u v w`. -/
theorem triadQuarticEnergy_ge_three_mul_sq {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] {u v w : Vec3 F} {a : F} (ha : 0 ≤ a)
    (huv : dot u v = 0) (hvw : dot v w = 0) (hwu : dot w u = 0)
    (hu : a ≤ normSq u) (hv : a ≤ normSq v) (hw : a ≤ normSq w) :
    3 * a ^ 2 ≤ triadQuarticEnergy u v w := by
  rw [triadQuarticEnergy_eq_of_ortho huv hvw hwu]
  have hnu : 0 ≤ normSq u := le_trans ha hu
  have hnv : 0 ≤ normSq v := le_trans ha hv
  have hnw : 0 ≤ normSq w := le_trans ha hw
  have h1 : a * a ≤ normSq u * normSq v := mul_le_mul hu hv ha hnu
  have h2 : a * a ≤ normSq v * normSq w := mul_le_mul hv hw ha hnv
  have h3 : a * a ≤ normSq w * normSq u := mul_le_mul hw hu ha hnw
  nlinarith

end NonAbelianCommutatorStiffness
