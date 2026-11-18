/-
  YangMillsBlueprint.BasicTypes
  =============================
  Pure constructive Lean 4.35 (axioms: [], zero Mathlib/sorry) foundations for:
  1. Exact positive/non-negative rational pairs QPair (cross-multiplied, GCD-free).
  2. SU(N) Levi-stratum mode conservation on T^d (toron + unbroken + broken = d*(N^2 - 1)).
  3. Exact Quadratic-Residual Schur Congruence identity & strict block coercivity in Int.
-/

namespace YangMillsBlueprint

/-- Exact non-negative rational numerator/denominator pair with positive denominator. -/
structure QPair where
  num : Nat
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace QPair

def ofNat (n : Nat) : QPair := ⟨n, 1, by omega⟩

def mkPos (n d : Nat) (h : 0 < d) : QPair := ⟨n, d, h⟩

def add (a b : QPair) : QPair :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def mul (a b : QPair) : QPair :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def pow4 (a : QPair) : QPair :=
  mul (mul a a) (mul a a)

def eqv (a b : QPair) : Prop := a.num * b.den = b.num * a.den

def lt (a b : QPair) : Prop := a.num * b.den < b.num * a.den

def le (a b : QPair) : Prop := a.num * b.den ≤ b.num * a.den

/-- Cross-multiplied strict gap: a < b ↔ a.num * b.den < b.num * a.den. -/
instance (a b : QPair) : Decidable (lt a b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

instance (a b : QPair) : Decidable (le a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

instance (a b : QPair) : Decidable (eqv a b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

/-- Safe subtraction `b - a` returning exact difference whenever `a ≤ b`. -/
def subLe (b a : QPair) : QPair :=
  ⟨b.num * a.den - a.num * b.den, b.den * a.den, Nat.mul_pos b.den_pos a.den_pos⟩

end QPair

/-- Lie algebra dimension dim su(N) = N^2 - 1. -/
def suDim (N : Nat) : Nat := N * N - 1

/-- Flat commuting toron moduli zero-modes: d * (k - 1). -/
def toronModuliModes (d k : Nat) : Nat := d * (k - 1)

/-- Unbroken transverse + temporal gluon modes in Levi stratum (N^2 - S) + (d - 1)*(N^2 - S). -/
def leviUnbrokenBulkModes (d N S : Nat) : Nat :=
  (N * N - S) + (d - 1) * (N * N - S)

/-- Broken off-diagonal Levi roots with nonzero commutator gaps: d * (S - k). -/
def leviBrokenModes (d S k : Nat) : Nat := d * (S - k)

/-- Theorem: Mode count partition identity for block decompositions on T^d. -/
theorem block_mode_dimension_additivity
    (d N S k : Nat)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hkS : k ≤ S) (hSN : S ≤ N * N) :
    toronModuliModes d k + leviUnbrokenBulkModes d N S + leviBrokenModes d S k =
      d * suDim N := by
  unfold toronModuliModes leviUnbrokenBulkModes leviBrokenModes suDim
  have h1 : 1 + (d - 1) = d := by omega
  have hbulk : (N * N - S) + (d - 1) * (N * N - S) = d * (N * N - S) := by
    calc
      (N * N - S) + (d - 1) * (N * N - S)
          = 1 * (N * N - S) + (d - 1) * (N * N - S) := by rw [Nat.one_mul]
      _ = (1 + (d - 1)) * (N * N - S) := by rw [Nat.add_mul]
      _ = d * (N * N - S) := by rw [h1]
  rw [hbulk]
  have hpart : (k - 1) + (N * N - S) + (S - k) = N * N - 1 := by omega
  calc
    d * (k - 1) + d * (N * N - S) + d * (S - k)
        = d * ((k - 1) + (N * N - S)) + d * (S - k) := by rw [← Nat.mul_add]
    _ = d * ((k - 1) + (N * N - S) + (S - k)) := by rw [← Nat.mul_add]
    _ = d * (N * N - 1) := by rw [hpart]

/-- Backwards-compatible alias for the block mode dimension additivity theorem. -/
abbrev levi_stratum_mode_conservation := @block_mode_dimension_additivity

/-- Two-block quadratic form Q(z_b, z_c) = a_cc * z_c^2 - 2 * a_cb * z_c * z_b + a_bb * z_b^2. -/
def twoBlockQuadForm (a_bb a_cb a_cc z_b z_c : Int) : Int :=
  a_cc * (z_c * z_c) - 2 * a_cb * z_c * z_b + a_bb * (z_b * z_b)

/-- Schur complement scalar determinant delta = a_cc * a_bb - a_cb^2. -/
def twoBlockSchurDet (a_bb a_cb a_cc : Int) : Int :=
  a_cc * a_bb - a_cb * a_cb

/--
  Theorem (Schur Complement Quadratic Identity):
  Exact algebraic completion of the square for 2x2 block forms:
  multiplied by the pivot `a_bb`, the form splits into the Schur-complement
  energy plus a squared off-diagonal residual:
    delta * z_c^2 + (a_bb * z_b - a_cb * z_c)^2 = a_bb * Q(z_b, z_c).
-/
theorem schur_complement_quadratic_identity (a_bb a_cb a_cc z_b z_c : Int) :
    twoBlockSchurDet a_bb a_cb a_cc * (z_c * z_c) +
        (a_bb * z_b - a_cb * z_c) * (a_bb * z_b - a_cb * z_c) =
      a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
  unfold twoBlockSchurDet twoBlockQuadForm
  have h1 : a_cc * a_bb * (z_c * z_c) = a_bb * (a_cc * (z_c * z_c)) := by
    rw [Int.mul_comm a_cc a_bb, Int.mul_assoc]
  have hcross1 : a_bb * z_b * (a_cb * z_c) = a_bb * a_cb * z_c * z_b := by
    rw [Int.mul_assoc a_bb z_b (a_cb * z_c), Int.mul_left_comm z_b a_cb z_c,
        Int.mul_comm z_b z_c, ← Int.mul_assoc, ← Int.mul_assoc]
  have hcross2 : a_cb * z_c * (a_bb * z_b) = a_bb * a_cb * z_c * z_b := by
    rw [Int.mul_comm (a_cb * z_c) (a_bb * z_b)]
    exact hcross1
  have hsqb : a_bb * z_b * (a_bb * z_b) = a_bb * (a_bb * (z_b * z_b)) := by
    rw [Int.mul_assoc, Int.mul_left_comm z_b a_bb z_b, ← Int.mul_assoc]
  have hsqc : a_cb * z_c * (a_cb * z_c) = a_cb * a_cb * (z_c * z_c) := by
    rw [Int.mul_assoc, Int.mul_left_comm z_c a_cb z_c, ← Int.mul_assoc]
  have h2rhs : a_bb * (2 * a_cb * z_c * z_b) = 2 * (a_bb * a_cb * z_c * z_b) := by
    rw [← Int.mul_assoc a_bb (2 * a_cb * z_c) z_b,
        ← Int.mul_assoc a_bb (2 * a_cb) z_c,
        ← Int.mul_assoc a_bb 2 a_cb,
        Int.mul_comm a_bb 2,
        Int.mul_assoc 2 a_bb a_cb,
        Int.mul_assoc 2 (a_bb * a_cb) z_c,
        Int.mul_assoc 2 (a_bb * a_cb * z_c) z_b]
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add]
  rw [h1, hcross1, hcross2, hsqb, hsqc, h2rhs]
  omega

/-- Backwards-compatible alias for the Schur complement quadratic identity. -/
abbrev schur_quadratic_residual_identity := @schur_complement_quadratic_identity

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with hx | hx
  · exact Int.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by omega
    have hsq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    rw [← hsq]
    exact Int.mul_nonneg hnx hnx

private theorem int_sq_pos_of_ne_zero {x : Int} (hne : x ≠ 0) : 0 < x * x := by
  have hnn : 0 ≤ x * x := int_sq_nonneg x
  rcases Int.lt_trichotomy x 0 with hlt | heq | hgt
  · have hnx : 0 < -x := by omega
    have hsq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    rw [← hsq]
    exact Int.mul_pos hnx hnx
  · exact absurd heq hne
  · exact Int.mul_pos hgt hgt

/--
  Theorem (Certified Block Coercivity via Schur Congruence, Part I):
  If bulk pivot `0 < a_bb` and Schur complement `0 < twoBlockSchurDet a_bb a_cb a_cc`,
  then for every nonzero vector `(z_b, z_c)`, `twoBlockQuadForm a_bb a_cb a_cc z_b z_c > 0`.
-/
theorem schur_coercivity_from_block_pivots
    (a_bb a_cb a_cc z_b z_c : Int)
    (hbb : 0 < a_bb)
    (hschur : 0 < twoBlockSchurDet a_bb a_cb a_cc)
    (hnz : z_b ≠ 0 ∨ z_c ≠ 0) :
    0 < twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
  have hid := schur_quadratic_residual_identity a_bb a_cb a_cc z_b z_c
  have hr_nn : 0 ≤ (a_bb * z_b - a_cb * z_c) * (a_bb * z_b - a_cb * z_c) :=
    int_sq_nonneg (a_bb * z_b - a_cb * z_c)
  have hprod_pos : 0 < a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c := by
    rw [← hid]
    by_cases hzc : z_c = 0
    · subst hzc
      have hzb : z_b ≠ 0 := by
        cases hnz with
        | inl h => exact h
        | inr h => exact absurd rfl h
      have hbb_ne : a_bb ≠ 0 := by omega
      have hzb_ne : a_bb * z_b ≠ 0 := Int.mul_ne_zero hbb_ne hzb
      have hr_pos : 0 < (a_bb * z_b - a_cb * 0) * (a_bb * z_b - a_cb * 0) := by
        simp only [Int.mul_zero, Int.sub_zero]
        exact int_sq_pos_of_ne_zero hzb_ne
      have h0 : twoBlockSchurDet a_bb a_cb a_cc * (0 * 0) = 0 := by
        simp only [Int.mul_zero]
      rw [h0]
      omega
    · have hz_pos : 0 < z_c * z_c := int_sq_pos_of_ne_zero hzc
      have ht1 : 0 < twoBlockSchurDet a_bb a_cb a_cc * (z_c * z_c) :=
        Int.mul_pos hschur hz_pos
      omega
  by_cases hgt : 0 < twoBlockQuadForm a_bb a_cb a_cc z_b z_c
  · exact hgt
  · have hle : twoBlockQuadForm a_bb a_cb a_cc z_b z_c ≤ 0 := by omega
    have hnp : a_bb * twoBlockQuadForm a_bb a_cb a_cc z_b z_c ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle
    omega

end YangMillsBlueprint
