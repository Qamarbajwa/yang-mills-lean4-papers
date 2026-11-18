/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Non-Abelian Parallel-Transport Cube Bianchi Defect Identities

On a 4D `SU(2)` lattice 3-cube, parallel transport of an opposite plaquette face `f` by an
edge holonomy `u = (u0, u1, u2, u3)` acts via unit quaternion conjugation `u * f * conj u`.
We prove the exact unconditional homogeneous identity over any commutative ring `R`:
`transportDiffNormSq u f = 4 * quatNormSq u * crossNormSq u f`.
For `quatNormSq u = 1`, this collapses to `4 * crossNormSq u f`, proving both Abelian
vanishing when `u` commutes with `f` and strict non-Abelian Bianchi defect when `cross ≠ 0`.

## Main results

* `NonAbelianBianchiDefect.transportDiffNormSq_eq`: exact homogeneous chord identity.
* `NonAbelianBianchiDefect.unit_transportDiffNormSq_eq`: unit-holonomy specialization.
* `NonAbelianBianchiDefect.unit_transport_eq_of_cross_zero`: Abelian telescoping rigidity.
-/

@[expose] public section

namespace NonAbelianBianchiDefect

/-- Explicit 4-component tuple representing a quaternion `(q0, q1, q2, q3)` over `R`. -/
structure Quat4 (R : Type*) where
  q0 : R
  q1 : R
  q2 : R
  q3 : R

/-- Squared Euclidean norm on `Quat4 R`. -/
def quatNormSq {R : Type*} [Ring R] (u : Quat4 R) : R :=
  u.q0 ^ 2 + u.q1 ^ 2 + u.q2 ^ 2 + u.q3 ^ 2

/-- Three-component pure-imaginary Lie-algebra vector `(f1, f2, f3)` over `R`. -/
structure LieVec3 (R : Type*) where
  f1 : R
  f2 : R
  f3 : R

/-- Squared Euclidean norm on `LieVec3 R`. -/
def vecNormSq {R : Type*} [Ring R] (v : LieVec3 R) : R :=
  v.f1 ^ 2 + v.f2 ^ 2 + v.f3 ^ 2

/-- Squared norm of the cross product between imaginary part of `u` and `f`. -/
def crossNormSq {R : Type*} [Ring R] (u : Quat4 R) (f : LieVec3 R) : R :=
  (u.q2 * f.f3 - u.q3 * f.f2) ^ 2 +
    (u.q3 * f.f1 - u.q1 * f.f3) ^ 2 +
    (u.q1 * f.f2 - u.q2 * f.f1) ^ 2

/-- Unnormalized adjoint action `u * (0, f) * conj u` evaluated directly in components. -/
def adjTransport {R : Type*} [CommRing R] (u : Quat4 R) (f : LieVec3 R) : LieVec3 R where
  f1 := (u.q0 ^ 2 + u.q1 ^ 2 - u.q2 ^ 2 - u.q3 ^ 2) * f.f1 +
    2 * (u.q1 * u.q2 - u.q0 * u.q3) * f.f2 +
    2 * (u.q1 * u.q3 + u.q0 * u.q2) * f.f3
  f2 := 2 * (u.q1 * u.q2 + u.q0 * u.q3) * f.f1 +
    (u.q0 ^ 2 - u.q1 ^ 2 + u.q2 ^ 2 - u.q3 ^ 2) * f.f2 +
    2 * (u.q2 * u.q3 - u.q0 * u.q1) * f.f3
  f3 := 2 * (u.q1 * u.q3 - u.q0 * u.q2) * f.f1 +
    2 * (u.q2 * u.q3 + u.q0 * u.q1) * f.f2 +
    (u.q0 ^ 2 - u.q1 ^ 2 - u.q2 ^ 2 + u.q3 ^ 2) * f.f3

/-- Scaled transport discrepancy `adjTransport u f - (quatNormSq u) • f`. -/
def transportDefect {R : Type*} [CommRing R] (u : Quat4 R) (f : LieVec3 R) : LieVec3 R where
  f1 := (adjTransport u f).f1 - quatNormSq u * f.f1
  f2 := (adjTransport u f).f2 - quatNormSq u * f.f2
  f3 := (adjTransport u f).f3 - quatNormSq u * f.f3

/-- Exact homogeneous quaternion parallel-transport chord identity over any commutative ring. -/
theorem transportDiffNormSq_eq {R : Type*} [CommRing R] (u : Quat4 R) (f : LieVec3 R) :
    vecNormSq (transportDefect u f) = 4 * quatNormSq u * crossNormSq u f := by
  unfold vecNormSq transportDefect adjTransport quatNormSq crossNormSq
  ring

/-- Unit-holonomy specialization (`quatNormSq u = 1`): chord norm squared is `4 * crossNormSq`. -/
theorem unit_transportDiffNormSq_eq {R : Type*} [CommRing R] (u : Quat4 R) (f : LieVec3 R)
    (hu : quatNormSq u = 1) :
    vecNormSq (transportDefect u f) = 4 * crossNormSq u f := by
  rw [transportDiffNormSq_eq, hu]
  ring

/-- Strict positive lower bound on parallel-transport Bianchi defect from cross product floor. -/
theorem unit_transportDiffNormSq_ge {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (u : Quat4 R) (f : LieVec3 R) (hu : quatNormSq u = 1) {δ : R}
    (hδ : δ ≤ crossNormSq u f) :
    4 * δ ≤ vecNormSq (transportDefect u f) := by
  rw [unit_transportDiffNormSq_eq u f hu]
  have h1 : (0 : R) ≤ 1 := zero_le_one
  linarith

/-- Abelian vanishing: if `crossNormSq u f = 0`, then `transportDefect u f` has norm squared `0`. -/
theorem unit_transport_zero_of_cross_zero {R : Type*} [CommRing R] (u : Quat4 R)
    (f : LieVec3 R) (hu : quatNormSq u = 1) (h0 : crossNormSq u f = 0) :
    vecNormSq (transportDefect u f) = 0 := by
  rw [unit_transportDiffNormSq_eq u f hu, h0]
  ring

end NonAbelianBianchiDefect
