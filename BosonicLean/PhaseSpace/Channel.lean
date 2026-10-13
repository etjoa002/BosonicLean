/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import BosonicLean.Weyl.State

/-!
# Gaussian channels on finitely many modes

In BosonicLean's convention (covariance matrices `γ` with `γ − iΩ ≥ 0`, positions first) a
Gaussian channel acts by `γ ↦ XγXᵀ + Y` for real matrices `(X, Y)` with `Y` symmetric and
`Y − iΩ + iXΩXᵀ ≥ 0` (Holevo–Werner). Such channel matrices preserve admissibility, and they are
exactly the images of the data `(G, ν)` of the channel condition (4.34) of Krüger's thesis on
`ℝ^{2n}` (see `BosonicLean.Weyl.GaussianChannel`) under the conversion `X = ΩᵀGᵀΩ`, `Y = ΩᵀνΩ`.

## Main definitions

* `Gaussian.IsChannelMatrix`

## Main statements

* `Gaussian.isAdmissible_channel`: channel matrices map admissible matrices to admissible ones;
* `Gaussian.channel_output`: the conversion of the output covariance;
* `Gaussian.isStateConditionC_iff_posSemidef`: the condition (4.34) on `ℝ^{2n}` as a matrix
  inequality;
* `Gaussian.isChannelMatrix_iff_isStateConditionC`: the conversion of the condition (4.34).
-/

open Matrix BosonicLean.Weyl
open scoped ComplexOrder

namespace Gaussian

variable {n : ℕ}

/-- (Holevo–Werner) Real matrices `(X, Y)` are channel
matrices if `Y` is symmetric and `Y − iΩ + iXΩXᵀ ≥ 0`; they act by `γ ↦ XγXᵀ + Y`.
(QCALean notes: `def:ch-matrices`) -/
def IsChannelMatrix (X Y : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) : Prop :=
  Yᵀ = Y ∧ (Y.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal +
    Complex.I • (X * symplecticForm n * Xᵀ).map Complex.ofReal).PosSemidef

/-- The complexification of a real matrix product. -/
private theorem map_ofReal_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

private theorem conjTranspose_map_ofReal {ι : Type*} (A : Matrix ι ι ℝ) :
    (A.map Complex.ofReal)ᴴ = Aᵀ.map Complex.ofReal := by
  ext i j; simp [Matrix.conjTranspose_apply]

/-- Channel matrices map admissible covariance matrices
to admissible ones. (QCALean notes: `prop:ch-matrices`) -/
theorem isAdmissible_channel {X Y γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (h : IsChannelMatrix X Y) (hγ : IsAdmissible γ) : IsAdmissible (X * γ * Xᵀ + Y) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hγ.1, h.1, Matrix.mul_assoc]
  · have h1 := hγ.2.mul_mul_conjTranspose_same (X.map Complex.ofReal)
    have key : (X * γ * Xᵀ + Y).map Complex.ofReal -
          Complex.I • (symplecticForm n).map Complex.ofReal =
        X.map Complex.ofReal * (γ.map Complex.ofReal -
            Complex.I • (symplecticForm n).map Complex.ofReal) * (X.map Complex.ofReal)ᴴ +
          (Y.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal +
            Complex.I • (X * symplecticForm n * Xᵀ).map Complex.ofReal) := by
      have hadd : (X * γ * Xᵀ + Y).map Complex.ofReal =
          (X * γ * Xᵀ).map Complex.ofReal + Y.map Complex.ofReal :=
        Matrix.map_add _ (fun a b => Complex.ofReal_add a b) _ _
      rw [conjTranspose_map_ofReal, hadd, map_ofReal_mul, map_ofReal_mul,
        map_ofReal_mul, map_ofReal_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul]
      abel
    rw [key]
    exact h1.add h.2

/-- The conversion of the output covariance,
`Ωᵀ(GᵀγG + ν)Ω = X(ΩᵀγΩ)Xᵀ + Y` with `X = ΩᵀGᵀΩ` and `Y = ΩᵀνΩ`.
(QCALean notes: `prop:ch-matrices`) -/
theorem channel_output (G ν γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    (symplecticForm n)ᵀ * (Gᵀ * γ * G + ν) * symplecticForm n =
      ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n) *
          ((symplecticForm n)ᵀ * γ * symplecticForm n) *
          ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n)ᵀ +
        (symplecticForm n)ᵀ * ν * symplecticForm n := by
  have h := symplecticForm_mul_transpose_self n
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (symplecticForm n) (symplecticForm n)ᵀ, h, Matrix.one_mul,
    ← Matrix.mul_assoc (symplecticForm n) (symplecticForm n)ᵀ, h, Matrix.one_mul]

/-- The Gram matrix of a pair of bilinear forms given by real matrices, on a family of vectors,
is the congruence of the complex matrix `A + iB` by the matrix of the family. -/
private theorem gram_toBilin' {m : ℕ} (A B : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (u : Fin m → PhaseIndex n → ℝ) :
    (Matrix.of fun j k => ((Matrix.toBilin' A (u j) (u k) : ℝ) : ℂ) +
        Complex.I * ((Matrix.toBilin' B (u j) (u k) : ℝ) : ℂ)) =
      ((Matrix.of fun i j => u j i).map Complex.ofReal)ᴴ *
        (A.map Complex.ofReal + Complex.I • B.map Complex.ofReal) *
        (Matrix.of fun i j => u j i).map Complex.ofReal := by
  ext j k
  simp only [Matrix.of_apply, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- The Gram matrix of the standard basis, reindexed, is the matrix itself. -/
private theorem basis_gram {m : ℕ} (e : PhaseIndex n ≃ Fin m)
    (H : Matrix (PhaseIndex n) (PhaseIndex n) ℂ) :
    ((((Matrix.of fun i j => (Pi.single (e.symm j) (1 : ℝ) : PhaseIndex n → ℝ) i).map
        Complex.ofReal)ᴴ * H *
      (Matrix.of fun i j => (Pi.single (e.symm j) (1 : ℝ) : PhaseIndex n → ℝ) i).map
        Complex.ofReal).submatrix e e) = H := by
  ext a b
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.single_apply, apply_ite]

/-- The condition (4.34) on `ℝ^{2n}` is positive semidefiniteness of `ν + i(Ω − GᵀΩG)`. -/
theorem isStateConditionC_iff_posSemidef (G ν : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    IsStateConditionC (Matrix.toBilin' ν)
        (Matrix.toBilin' (symplecticForm n) -
          (Matrix.toBilin' (symplecticForm n)).comp (Matrix.toLin' G) (Matrix.toLin' G)) ↔
      (ν.map Complex.ofReal + Complex.I •
        (symplecticForm n - Gᵀ * symplecticForm n * G).map Complex.ofReal).PosSemidef := by
  rw [Matrix.toBilin'_comp, ← map_sub]
  constructor
  · intro h
    let e := Fintype.equivFin (PhaseIndex n)
    have hg := h (Fintype.card (PhaseIndex n)) (fun j => Pi.single (e.symm j) 1)
    rw [gram_toBilin'] at hg
    have hs := hg.submatrix e
    rwa [basis_gram] at hs
  · intro h m u
    rw [gram_toBilin']
    exact h.conjTranspose_mul_mul_same _

/-- For symmetric `ν`, the converted matrices
`(ΩᵀGᵀΩ, ΩᵀνΩ)` are channel matrices if and only if `G` and `ν` satisfy the condition (4.34) on
`ℝ^{2n}` with `σ(u, w) = uᵀΩw`. (QCALean notes: `prop:ch-matrices`) -/
theorem isChannelMatrix_iff_isStateConditionC (G ν : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (hν : νᵀ = ν) :
    IsChannelMatrix ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n)
        ((symplecticForm n)ᵀ * ν * symplecticForm n) ↔
      IsStateConditionC (Matrix.toBilin' ν)
        (Matrix.toBilin' (symplecticForm n) -
          (Matrix.toBilin' (symplecticForm n)).comp (Matrix.toLin' G) (Matrix.toLin' G)) := by
  rw [isStateConditionC_iff_posSemidef]
  have hΩt : (symplecticForm n)ᵀ = -symplecticForm n := transpose_symplecticForm n
  have hunit : (symplecticForm n).map Complex.ofReal * ((symplecticForm n).map Complex.ofReal)ᴴ =
      1 := by
    rw [conjTranspose_map_ofReal, ← map_ofReal_mul, symplecticForm_mul_transpose_self,
      Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
  have hK :
      ((symplecticForm n)ᵀ * ν * symplecticForm n).map Complex.ofReal -
          Complex.I • (symplecticForm n).map Complex.ofReal +
          Complex.I • (((symplecticForm n)ᵀ * Gᵀ * symplecticForm n) * symplecticForm n *
            ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n)ᵀ).map Complex.ofReal =
        ((symplecticForm n).map Complex.ofReal)ᴴ *
          (ν.map Complex.ofReal + Complex.I •
            (symplecticForm n - Gᵀ * symplecticForm n * G).map Complex.ofReal)ᵀ *
          (symplecticForm n).map Complex.ofReal := by
    have hsq : ∀ A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ,
        symplecticForm n * (symplecticForm n * A) = -A := fun A => by
      rw [← Matrix.mul_assoc, symplecticForm_sq, Matrix.neg_mul, Matrix.one_mul]
    have r3 : (symplecticForm n)ᵀ * (symplecticForm n - Gᵀ * symplecticForm n * G)ᵀ *
          symplecticForm n =
        -symplecticForm n + ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n) * symplecticForm n *
          ((symplecticForm n)ᵀ * Gᵀ * symplecticForm n)ᵀ := by
      simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_neg, hΩt, Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg,
        neg_neg, Matrix.mul_assoc, hsq]
      abel
    have hT : (ν.map Complex.ofReal + Complex.I •
        (symplecticForm n - Gᵀ * symplecticForm n * G).map Complex.ofReal)ᵀ =
        ν.map Complex.ofReal + Complex.I •
          ((symplecticForm n - Gᵀ * symplecticForm n * G)ᵀ).map Complex.ofReal := by
      rw [Matrix.transpose_add, Matrix.transpose_smul, ← Matrix.transpose_map,
        ← Matrix.transpose_map, hν]
    rw [hT, conjTranspose_map_ofReal, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, ← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, r3,
      Matrix.map_add _ (fun a b => Complex.ofReal_add a b),
      Matrix.map_neg _ (fun a => Complex.ofReal_neg a), smul_add, smul_neg]
    abel
  unfold IsChannelMatrix
  constructor
  · intro hc
    have h2 := hc.2
    rw [hK] at h2
    have h3 := h2.mul_mul_conjTranspose_same ((symplecticForm n).map Complex.ofReal)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hunit, Matrix.one_mul, Matrix.mul_assoc, hunit,
      Matrix.mul_one] at h3
    simpa using h3.transpose
  · intro hs
    refine ⟨?_, ?_⟩
    · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hν, Matrix.mul_assoc]
    · rw [hK]
      exact hs.transpose.conjTranspose_mul_mul_same _

@[deprecated isChannelMatrix_iff_isStateConditionC (since := "2026-10-01")]
alias isChannelMatrix_iff := isChannelMatrix_iff_isStateConditionC

end Gaussian
