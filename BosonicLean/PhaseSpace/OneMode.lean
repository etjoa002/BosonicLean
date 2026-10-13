/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# One-mode matrices

Identities for `2 × 2` matrices indexed by BosonicLean's one-mode cell `Gaussian.PhaseIndex 1`
(position first, then momentum), over any commutative ring. They are the algebra behind the
nearest-neighbour classification of QCALean: with the one-mode symplectic matrix
`Ω = [[0,1],[-1,0]]`,

* `Aᵀ Ω B = Ω adj(A) B` (`transpose_mul_omega_mul`), in particular `Aᵀ Ω A = det(A) Ω`;
* the adjugate is additive, and `det(A + B) = det A + det B + tr(adj(A) B)`;
* `adj K = K` exactly when `K` is a multiple of the identity.

The adjugate `adj2` and determinant `det2` are written out by entries; `det2_eq_det` identifies
`det2` with Mathlib's determinant.
-/

open Matrix

namespace Gaussian

variable {R : Type*} [CommRing R]

/-- The one-mode cell, position first. -/
abbrev Cell := Gaussian.PhaseIndex 1

/-- The position index. -/
abbrev qIdx : Cell := Sum.inl 0
/-- The momentum index. -/
abbrev pIdx : Cell := Sum.inr 0

/-- The one-mode symplectic matrix `[[0,1],[-1,0]]` over any commutative ring. -/
def omega : Matrix Cell Cell R := -Matrix.J (Fin 1) R

/-- Over `ℝ` it is BosonicLean's `symplecticForm 1`. -/
theorem omega_real : (omega : Matrix Cell Cell ℝ) = Gaussian.symplecticForm 1 := rfl

/-- The determinant of a one-mode matrix, by entries. -/
def det2 (A : Matrix Cell Cell R) : R := A qIdx qIdx * A pIdx pIdx - A qIdx pIdx * A pIdx qIdx

/-- The adjugate of a one-mode matrix, by entries. -/
def adj2 (A : Matrix Cell Cell R) : Matrix Cell Cell R :=
  Matrix.of fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => A pIdx pIdx
    | Sum.inl _, Sum.inr _ => -A qIdx pIdx
    | Sum.inr _, Sum.inl _ => -A pIdx qIdx
    | Sum.inr _, Sum.inr _ => A qIdx qIdx

omit [CommRing R] in
/-- Split a statement about all indices of the cell into its four entries. -/
theorem cell_ext {A B : Matrix Cell Cell R}
    (h1 : A qIdx qIdx = B qIdx qIdx) (h2 : A qIdx pIdx = B qIdx pIdx)
    (h3 : A pIdx qIdx = B pIdx qIdx)
    (h4 : A pIdx pIdx = B pIdx pIdx) : A = B := by
  ext i j
  rcases i with ⟨i⟩ | ⟨i⟩ <;> rcases j with ⟨j⟩ | ⟨j⟩ <;> fin_cases i <;> fin_cases j <;>
    assumption

@[simp] theorem mul_qq (A B : Matrix Cell Cell R) :
    (A * B) qIdx qIdx = A qIdx qIdx * B qIdx qIdx + A qIdx pIdx * B pIdx qIdx := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]
@[simp] theorem mul_qp (A B : Matrix Cell Cell R) :
    (A * B) qIdx pIdx = A qIdx qIdx * B qIdx pIdx + A qIdx pIdx * B pIdx pIdx := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]
@[simp] theorem mul_pq (A B : Matrix Cell Cell R) :
    (A * B) pIdx qIdx = A pIdx qIdx * B qIdx qIdx + A pIdx pIdx * B pIdx qIdx := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]
@[simp] theorem mul_pp (A B : Matrix Cell Cell R) :
    (A * B) pIdx pIdx = A pIdx qIdx * B qIdx pIdx + A pIdx pIdx * B pIdx pIdx := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

@[simp] theorem omega_qq : (omega : Matrix Cell Cell R) qIdx qIdx = 0 := by simp [omega, Matrix.J]
@[simp] theorem omega_qp : (omega : Matrix Cell Cell R) qIdx pIdx = 1 := by simp [omega, Matrix.J]
@[simp] theorem omega_pq : (omega : Matrix Cell Cell R) pIdx qIdx = -1 := by simp [omega, Matrix.J]
@[simp] theorem omega_pp : (omega : Matrix Cell Cell R) pIdx pIdx = 0 := by simp [omega, Matrix.J]

@[simp] theorem adj2_qq (A : Matrix Cell Cell R) : adj2 A qIdx qIdx = A pIdx pIdx := rfl
@[simp] theorem adj2_qp (A : Matrix Cell Cell R) : adj2 A qIdx pIdx = -A qIdx pIdx := rfl
@[simp] theorem adj2_pq (A : Matrix Cell Cell R) : adj2 A pIdx qIdx = -A pIdx qIdx := rfl
@[simp] theorem adj2_pp (A : Matrix Cell Cell R) : adj2 A pIdx pIdx = A qIdx qIdx := rfl

@[simp] theorem one_qq : (1 : Matrix Cell Cell R) qIdx qIdx = 1 := rfl
@[simp] theorem one_qp : (1 : Matrix Cell Cell R) qIdx pIdx = 0 := rfl
@[simp] theorem one_pq : (1 : Matrix Cell Cell R) pIdx qIdx = 0 := rfl
@[simp] theorem one_pp : (1 : Matrix Cell Cell R) pIdx pIdx = 1 := rfl

theorem mul_adj2 (A : Matrix Cell Cell R) : A * adj2 A = det2 A • 1 := by
  apply cell_ext <;> simp [det2] <;> ring

theorem adj2_mul (A : Matrix Cell Cell R) : adj2 A * A = det2 A • 1 := by
  apply cell_ext <;> simp [det2] <;> ring

/-- `Aᵀ Ω B = Ω adj(A) B`. (QCALean notes: `lem:qca-2x2`) -/
theorem transpose_mul_omega_mul (A B : Matrix Cell Cell R) :
    Aᵀ * omega * B = omega * adj2 A * B := by
  apply cell_ext <;> simp

/-- `Aᵀ Ω A = det(A) Ω`. (QCALean notes: `lem:qca-2x2`) -/
theorem transpose_mul_omega_mul_self (A : Matrix Cell Cell R) :
    Aᵀ * omega * A = det2 A • omega := by
  apply cell_ext <;> simp [det2] <;> ring

/-- (QCALean notes: `lem:qca-2x2`) -/
theorem adj2_add (A B : Matrix Cell Cell R) : adj2 (A + B) = adj2 A + adj2 B := by
  apply cell_ext <;> simp <;> ring

theorem adj2_sub (A B : Matrix Cell Cell R) : adj2 (A - B) = adj2 A - adj2 B := by
  apply cell_ext <;> simp <;> ring

/-- (QCALean notes: `lem:qca-2x2`) -/
theorem det2_add (A B : Matrix Cell Cell R) :
    det2 (A + B) = det2 A + det2 B + ((adj2 A * B) qIdx qIdx + (adj2 A * B) pIdx pIdx) := by
  simp [det2]
  ring

theorem det2_smul (c : R) (A : Matrix Cell Cell R) : det2 (c • A) = c ^ 2 * det2 A := by
  simp [det2]; ring

theorem det2_one : det2 (1 : Matrix Cell Cell R) = 1 := by simp [det2]

/-- A one-mode matrix equal to its adjugate is a multiple of the identity, when `2 ≠ 0` in a
domain (over `ZMod 2` every symmetric pattern of off-diagonal entries is allowed).
(QCALean notes: `lem:qca-2x2`) -/
theorem eq_smul_one_of_adj2_eq [IsDomain R] (two : (2 : R) ≠ 0) {K : Matrix Cell Cell R}
    (h : adj2 K = K) : K = K qIdx qIdx • 1 := by
  have h2 := congrFun (congrFun h qIdx) pIdx
  have h3 := congrFun (congrFun h pIdx) qIdx
  have h4 := congrFun (congrFun h pIdx) pIdx
  simp only [adj2_qp, adj2_pq, adj2_pp] at h2 h3 h4
  have e2 : K qIdx pIdx = 0 := by
    have : (2 : R) * K qIdx pIdx = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two
  have e3 : K pIdx qIdx = 0 := by
    have : (2 : R) * K pIdx qIdx = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 this).resolve_left two
  apply cell_ext <;> simp [e2, e3, h4]

/-- (QCALean notes: `lem:qca-2x2`) -/
theorem adj2_mul_rev (A B : Matrix Cell Cell R) : adj2 (A * B) = adj2 B * adj2 A := by
  apply cell_ext <;> simp <;> ring

/-- (QCALean notes: `lem:qca-2x2`) -/
theorem adj2_adj2 (A : Matrix Cell Cell R) : adj2 (adj2 A) = A := by
  apply cell_ext <;> simp

theorem adj2_neg (A : Matrix Cell Cell R) : adj2 (-A) = -adj2 A := by
  apply cell_ext <;> simp

theorem det2_neg (A : Matrix Cell Cell R) : det2 (-A) = det2 A := by
  simp [det2]

theorem omega_mul_omega : (omega : Matrix Cell Cell R) * omega = -1 := by
  apply cell_ext <;> simp

/-- Cancel `Ω` on the left. -/
theorem omega_mul_cancel {A B : Matrix Cell Cell R} (h : omega * A = omega * B) : A = B := by
  have := congrArg (fun X => omega * X) h
  simpa [← Matrix.mul_assoc, omega_mul_omega] using this

/-- If `det2 A` is a unit and `adj2 A * B = 0`, then `B = 0`. -/
theorem eq_zero_of_adj2_mul_eq_zero {A B : Matrix Cell Cell R} (hA : IsUnit (det2 A))
    (h : adj2 A * B = 0) : B = 0 := by
  have h' : A * adj2 A * B = 0 := by rw [Matrix.mul_assoc, h, Matrix.mul_zero]
  rw [mul_adj2, Matrix.smul_mul, Matrix.one_mul] at h'
  have := congrArg (fun X => ((hA.unit⁻¹ : Rˣ) : R) • X) h'
  simpa [smul_smul] using this

/-- `det2` is Mathlib's determinant. -/
theorem det2_eq_det (A : Matrix Cell Cell R) : det2 A = A.det := by
  rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
  simp [det2, finSumFinEquiv]
  rfl

/-! ### General one-mode facts -/

section General

/-- The trace of a one-mode matrix, by entries. -/
theorem trace_cell {R : Type*} [CommRing R] (A : Matrix Cell Cell R) :
    A.trace = A qIdx qIdx + A pIdx pIdx := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Cayley–Hamilton for a one-mode matrix, `A² = (tr A) A − (det A) 1`. -/
theorem sq_eq_trace_smul_sub {R : Type*} [CommRing R] (A : Matrix Cell Cell R) :
    A * A = A.trace • A - det2 A • 1 := by
  rw [trace_cell]
  apply cell_ext <;> simp [det2] <;> ring

/-- A real symmetric one-mode matrix with positive `(1,1)` entry and positive determinant is
positive definite. -/
theorem posDef_of_cell {E : Matrix Cell Cell ℝ} (hs : Eᵀ = E) (h1 : 0 < E qIdx qIdx)
    (hd : 0 < det2 E) : E.PosDef := by
  have hsym : E pIdx qIdx = E qIdx pIdx := by
    have := congrFun (congrFun hs qIdx) pIdx
    rwa [Matrix.transpose_apply] at this
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hs],
    fun x hx => ?_⟩
  have hQ : star x ⬝ᵥ (E *ᵥ x) = E qIdx qIdx * x qIdx ^ 2 + 2 * E qIdx pIdx * x qIdx * x pIdx +
      E pIdx pIdx * x pIdx ^ 2 := by
    simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, hsym]
    ring
  rw [hQ]
  unfold det2 at hd
  rw [hsym] at hd
  have key : E qIdx qIdx * (E qIdx qIdx * x qIdx ^ 2 + 2 * E qIdx pIdx * x qIdx * x pIdx +
      E pIdx pIdx * x pIdx ^ 2) = (E qIdx qIdx * x qIdx + E qIdx pIdx * x pIdx) ^ 2 +
        (E qIdx qIdx * E pIdx pIdx - E qIdx pIdx * E qIdx pIdx) * x pIdx ^ 2 := by ring
  by_cases hp : x pIdx = 0
  · have hq : x qIdx ≠ 0 := by
      intro hq
      apply hx
      funext i
      rcases i with ⟨i⟩ | ⟨i⟩ <;> fin_cases i
      exacts [hq, hp]
    rw [hp]
    simpa using mul_pos h1 (pow_pos (abs_pos.2 hq) 2 |>.trans_eq (sq_abs _))
  · have hp2 : 0 < x pIdx ^ 2 := pow_pos (abs_pos.2 hp) 2 |>.trans_eq (sq_abs _)
    have hprod : 0 < E qIdx qIdx * (E qIdx qIdx * x qIdx ^ 2 +
        2 * E qIdx pIdx * x qIdx * x pIdx + E pIdx pIdx * x pIdx ^ 2) := by
      rw [key]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hd hp2)
    exact pos_of_mul_pos_right hprod h1.le

/-- A one-mode matrix commuting with a matrix `A` that is not a multiple of the identity is a
polynomial `p 1 + q A` in `A`. (QCALean notes: `lem:es-commutant`) -/
theorem exists_eq_smul_one_add_smul_of_commute {A X : Matrix Cell Cell ℝ} (hA : ∀ c : ℝ, A ≠ c • 1)
    (h : Commute X A) : ∃ p q : ℝ, X = p • 1 + q • A := by
  have h : X * A = A * X := h.eq
  have e1 := congrFun (congrFun h qIdx) qIdx
  have e2 := congrFun (congrFun h qIdx) pIdx
  have e3 := congrFun (congrFun h pIdx) qIdx
  simp only [mul_qq, mul_qp, mul_pq] at e1 e2 e3
  set a := A qIdx qIdx - A pIdx pIdx
  set x := X qIdx qIdx - X pIdx pIdx
  have hxb : x * A qIdx pIdx = X qIdx pIdx * a := by simp only [x, a]; linarith
  have hza : X pIdx qIdx * a = x * A pIdx qIdx := by simp only [x, a]; linarith
  have hyc : X qIdx pIdx * A pIdx qIdx = A qIdx pIdx * X pIdx qIdx := by linarith
  have ex : ∀ q : ℝ, x = q * a → X qIdx pIdx = q * A qIdx pIdx → X pIdx qIdx = q * A pIdx qIdx →
      X = (X qIdx qIdx - q * A qIdx qIdx) • 1 + q • A := by
    intro q h1 h2 h3
    apply cell_ext <;> simp [h2, h3]
    simp only [x, a] at h1
    linarith
  by_cases ha : a = 0
  · by_cases hb : A qIdx pIdx = 0
    · by_cases hc : A pIdx qIdx = 0
      · exfalso
        apply hA (A qIdx qIdx)
        apply cell_ext <;> simp [hb, hc]
        simp only [a] at ha
        linarith
      · refine ⟨_, X pIdx qIdx / A pIdx qIdx, ex _ ?_ ?_ ?_⟩
        · rw [ha, mul_zero]
          have : x * A pIdx qIdx = 0 := by rw [← hza, ha, mul_zero]
          exact (mul_eq_zero.1 this).resolve_right hc
        · rw [hb, mul_zero]
          have : X qIdx pIdx * A pIdx qIdx = 0 := by rw [hyc, hb, zero_mul]
          exact (mul_eq_zero.1 this).resolve_right hc
        · field_simp
    · refine ⟨_, X qIdx pIdx / A qIdx pIdx, ex _ ?_ ?_ ?_⟩
      · field_simp; linarith [hxb]
      · field_simp
      · field_simp; linarith [hyc]
  · refine ⟨_, x / a, ex _ ?_ ?_ ?_⟩
    · field_simp
    · field_simp; linarith [hxb]
    · field_simp; linarith [hza]

/-- The invariant symmetric forms of a one-mode matrix `A` of determinant one that is not a
multiple of the identity are the multiples of `Ω (A − ½ tr A)`. (QCALean notes:
`prop:es-invariant`) -/
theorem eq_smul_of_invariant_sym {A S : Matrix Cell Cell ℝ} (hd : det2 A = 1)
    (hA : ∀ c : ℝ, A ≠ c • 1) (hS : Sᵀ = S) (hSA : Aᵀ * S * A = S) :
    ∃ q : ℝ, S = q • (omega * (A - (A.trace / 2) • 1)) := by
  -- `Ω Aᵀ = adj(A) Ω`
  have h1 : Aᵀ * omega = omega * adj2 A := by simpa using transpose_mul_omega_mul A 1
  have h2 : omega * Aᵀ = adj2 A * omega := by
    have := congrArg (fun Y => omega * Y * omega) h1
    simp only [Matrix.mul_assoc, omega_mul_omega, Matrix.mul_neg, Matrix.mul_one] at this
    simp only [← Matrix.mul_assoc, omega_mul_omega, Matrix.neg_mul, Matrix.one_mul] at this
    exact neg_injective this
  set X := omega * S
  have hX : adj2 A * X * A = X := by
    simp only [X]
    rw [← Matrix.mul_assoc (adj2 A), ← h2, Matrix.mul_assoc omega Aᵀ S,
      Matrix.mul_assoc omega (Aᵀ * S) A, hSA]
  have hcomm : X * A = A * X := by
    have hAadj : A * adj2 A = 1 := by rw [mul_adj2, hd, one_smul]
    calc X * A = A * adj2 A * X * A := by rw [hAadj, Matrix.one_mul]
      _ = A * (adj2 A * X * A) := by simp only [Matrix.mul_assoc]
      _ = A * X := by rw [hX]
  obtain ⟨p, q, hpq⟩ := exists_eq_smul_one_add_smul_of_commute hA hcomm
  have hSx : S = -(omega * X) := by
    simp only [X, ← Matrix.mul_assoc, omega_mul_omega, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hsym := congrFun (congrFun hS qIdx) pIdx
  rw [Matrix.transpose_apply, hSx, hpq] at hsym
  simp at hsym
  refine ⟨-q, ?_⟩
  rw [hSx, hpq, trace_cell]
  apply cell_ext <;> simp <;> linarith

/-- The complexification of a real symmetric one-mode matrix is Hermitian. -/
theorem isHermitian_map_ofReal {E : Matrix Cell Cell ℝ} (hs : Eᵀ = E) :
    (E.map Complex.ofReal).IsHermitian := by
  ext i j
  have := congrFun (congrFun hs j) i
  simp only [Matrix.transpose_apply] at this
  simp [Matrix.conjTranspose_apply, this]

end General

end Gaussian
