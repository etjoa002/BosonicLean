/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Kronecker
import BosonicLean.Analysis.PowerBound

/-!
# Kronecker products and the `ℓ^∞` operator norm

The `ℓ^∞` operator norm of a matrix is its largest absolute row sum (Mathlib's
`Matrix.linftyOpNormedRing`, a local instance). For it,
`‖X ⊗ₖ Y‖ ≤ ‖X‖ ‖Y‖` (row sums multiply), `‖1‖ ≤ 1` (with equality unless the index type is
empty), and entrywise complex conjugation preserves the norm. The maps `X ↦ X ⊗ₖ 1` and
`X ↦ 1 ⊗ₖ X` are algebra homomorphisms. These facts reduce the transfer matrix of a bosonic MPS
to a series in one Banach algebra.

## Main definitions

* `BosonicLean.kroneckerRightOne`: `X ↦ X ⊗ₖ 1` as an algebra homomorphism.
* `BosonicLean.kroneckerLeftOne`: `X ↦ 1 ⊗ₖ X` as an algebra homomorphism.

## Main results

* `BosonicLean.linfty_opNorm_kronecker_le`: `‖X ⊗ₖ Y‖ ≤ ‖X‖ ‖Y‖`.
* `BosonicLean.linfty_opNorm_one_le`: `‖1‖ ≤ 1`.
* `BosonicLean.linfty_opNorm_map_conj`: `‖X̄‖ = ‖X‖` for the entrywise conjugate.
* `BosonicLean.kronecker_pow`: `(X ⊗ₖ Y)ᵏ = Xᵏ ⊗ₖ Yᵏ`.
* `BosonicLean.list_ofFn_prod_kronecker`: the mixed-product rule for ordered products.
-/

open Matrix
open scoped Kronecker NNReal

namespace BosonicLean

section Norm

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup

variable {l m n p α : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- **Row sums multiply.** `‖X ⊗ₖ Y‖ ≤ ‖X‖ ‖Y‖` in the `ℓ^∞` operator norm. -/
theorem linfty_opNNNorm_kronecker_le [NonUnitalSeminormedRing α] (X : Matrix l m α)
    (Y : Matrix n p α) : ‖X ⊗ₖ Y‖₊ ≤ ‖X‖₊ * ‖Y‖₊ := by
  rw [linfty_opNNNorm_def, linfty_opNNNorm_def X, linfty_opNNNorm_def Y]
  refine Finset.sup_le fun i _ => ?_
  calc ∑ j : m × p, ‖(X ⊗ₖ Y) i j‖₊
      ≤ ∑ j : m × p, ‖X i.1 j.1‖₊ * ‖Y i.2 j.2‖₊ :=
        Finset.sum_le_sum fun j _ => nnnorm_mul_le _ _
    _ = (∑ j : m, ‖X i.1 j‖₊) * ∑ j : p, ‖Y i.2 j‖₊ := by
        rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
    _ ≤ (Finset.univ.sup fun i : l => ∑ j : m, ‖X i j‖₊) *
          Finset.univ.sup fun i : n => ∑ j : p, ‖Y i j‖₊ :=
        mul_le_mul' (Finset.le_sup (f := fun i : l => ∑ j : m, ‖X i j‖₊) (Finset.mem_univ _))
          (Finset.le_sup (f := fun i : n => ∑ j : p, ‖Y i j‖₊) (Finset.mem_univ _))

/-- **Row sums multiply.** `‖X ⊗ₖ Y‖ ≤ ‖X‖ ‖Y‖` in the `ℓ^∞` operator norm. -/
theorem linfty_opNorm_kronecker_le [NonUnitalSeminormedRing α] (X : Matrix l m α)
    (Y : Matrix n p α) : ‖X ⊗ₖ Y‖ ≤ ‖X‖ * ‖Y‖ :=
  linfty_opNNNorm_kronecker_le X Y

/-- `‖1‖ ≤ 1` in the `ℓ^∞` operator norm; the norm is `0` when the index type is empty. -/
theorem linfty_opNorm_one_le [SeminormedRing α] [NormOneClass α] [DecidableEq n] :
    ‖(1 : Matrix n n α)‖ ≤ 1 := by
  rw [← diagonal_one, linfty_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => norm_one.le

/-- Entrywise complex conjugation preserves the `ℓ^∞` operator norm. -/
theorem linfty_opNorm_map_conj (X : Matrix m n ℂ) : ‖X.map (starRingEnd ℂ)‖ = ‖X‖ := by
  simp [linfty_opNorm_def]

end Norm

section AlgHom

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

/-- `X ↦ X ⊗ₖ 1` as an algebra homomorphism. -/
def kroneckerRightOne : Matrix m m R →ₐ[R] Matrix (m × n) (m × n) R where
  toFun X := X ⊗ₖ (1 : Matrix n n R)
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := zero_kronecker _
  map_add' X Y := add_kronecker _ _ _
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one, smul_kronecker]

/-- `X ↦ 1 ⊗ₖ X` as an algebra homomorphism. -/
def kroneckerLeftOne : Matrix n n R →ₐ[R] Matrix (m × n) (m × n) R where
  toFun X := (1 : Matrix m m R) ⊗ₖ X
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := kronecker_zero _
  map_add' X Y := kronecker_add _ _ _
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one, kronecker_smul]

@[simp]
theorem kroneckerRightOne_apply (X : Matrix m m R) :
    (kroneckerRightOne : Matrix m m R →ₐ[R] Matrix (m × n) (m × n) R) X = X ⊗ₖ 1 :=
  rfl

@[simp]
theorem kroneckerLeftOne_apply (X : Matrix n n R) :
    (kroneckerLeftOne : Matrix n n R →ₐ[R] Matrix (m × n) (m × n) R) X = 1 ⊗ₖ X :=
  rfl

/-- `X ⊗ₖ Y = (X ⊗ₖ 1)(1 ⊗ₖ Y)`. -/
theorem kronecker_eq_mul (X : Matrix m m R) (Y : Matrix n n R) :
    X ⊗ₖ Y = (X ⊗ₖ (1 : Matrix n n R)) * ((1 : Matrix m m R) ⊗ₖ Y) := by
  rw [← mul_kronecker_mul, mul_one, one_mul]

/-- `(X ⊗ₖ Y)ᵏ = Xᵏ ⊗ₖ Yᵏ`. -/
theorem kronecker_pow (X : Matrix m m R) (Y : Matrix n n R) (k : ℕ) :
    (X ⊗ₖ Y) ^ k = (X ^ k) ⊗ₖ (Y ^ k) := by
  induction k with
  | zero => simp only [pow_zero, one_kronecker_one]
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- The mixed-product rule for ordered products:
`(X₁ ⋯ X_M) ⊗ₖ (Y₁ ⋯ Y_M) = (X₁ ⊗ₖ Y₁) ⋯ (X_M ⊗ₖ Y_M)`. -/
theorem list_ofFn_prod_kronecker :
    ∀ {M : ℕ} (X : Fin M → Matrix m m R) (Y : Fin M → Matrix n n R),
      (List.ofFn X).prod ⊗ₖ (List.ofFn Y).prod = (List.ofFn fun j => X j ⊗ₖ Y j).prod
  | 0, _, _ => by simp only [List.ofFn_zero, List.prod_nil, one_kronecker_one]
  | M + 1, X, Y => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, mul_kronecker_mul, list_ofFn_prod_kronecker]

end AlgHom

/-- Entrywise conjugation of an ordered product of matrices. -/
theorem list_ofFn_prod_map_conj {m : Type*} [Fintype m] [DecidableEq m] {M : ℕ}
    (X : Fin M → Matrix m m ℂ) :
    (List.ofFn X).prod.map (starRingEnd ℂ) = (List.ofFn fun j => (X j).map (starRingEnd ℂ)).prod :=
  by rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_ofFn]; rfl

section PowerBound

attribute [local instance] Matrix.linftyOpNormedRing

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- `K̄ ⊗ₖ 1` inherits the power bound `(C, r)` of `K` (`ℓ^∞` operator norm). -/
theorem HasPowerBound.map_conj_kronecker_one {K : Matrix β β ℂ} {C r : ℝ}
    (hK : HasPowerBound K C r) :
    HasPowerBound (K.map (starRingEnd ℂ) ⊗ₖ (1 : Matrix β β ℂ)) C r := fun m => by
  have hpow : (K.map (starRingEnd ℂ)) ^ m = (K ^ m).map (starRingEnd ℂ) :=
    (map_pow (starRingEnd ℂ).mapMatrix K m).symm
  rw [kronecker_pow, one_pow, hpow]
  calc ‖(K ^ m).map (starRingEnd ℂ) ⊗ₖ (1 : Matrix β β ℂ)‖
      ≤ ‖(K ^ m).map (starRingEnd ℂ)‖ * ‖(1 : Matrix β β ℂ)‖ := linfty_opNorm_kronecker_le _ _
    _ ≤ ‖K ^ m‖ * 1 := by
        rw [linfty_opNorm_map_conj]
        exact mul_le_mul_of_nonneg_left linfty_opNorm_one_le (norm_nonneg _)
    _ ≤ C * r ^ m := by rw [mul_one]; exact hK m

/-- `1 ⊗ₖ K` inherits the power bound `(C, r)` of `K` (`ℓ^∞` operator norm). -/
theorem HasPowerBound.one_kronecker {K : Matrix β β ℂ} {C r : ℝ} (hK : HasPowerBound K C r) :
    HasPowerBound ((1 : Matrix β β ℂ) ⊗ₖ K) C r := fun m => by
  rw [kronecker_pow, one_pow]
  calc ‖(1 : Matrix β β ℂ) ⊗ₖ (K ^ m)‖ ≤ ‖(1 : Matrix β β ℂ)‖ * ‖K ^ m‖ :=
        linfty_opNorm_kronecker_le _ _
    _ ≤ 1 * ‖K ^ m‖ := mul_le_mul_of_nonneg_right linfty_opNorm_one_le (norm_nonneg _)
    _ ≤ C * r ^ m := by rw [one_mul]; exact hK m

/-- `K̄ ⊗ₖ K` has the power bound `(C², r²)` if `K` has the power bound `(C, r)`
(`ℓ^∞` operator norm). -/
theorem HasPowerBound.map_conj_kronecker_self {K : Matrix β β ℂ} {C r : ℝ}
    (hK : HasPowerBound K C r) :
    HasPowerBound (K.map (starRingEnd ℂ) ⊗ₖ K) (C * C) (r * r) := fun m => by
  have hpow : (K.map (starRingEnd ℂ)) ^ m = (K ^ m).map (starRingEnd ℂ) :=
    (map_pow (starRingEnd ℂ).mapMatrix K m).symm
  rw [kronecker_pow, hpow]
  calc ‖(K ^ m).map (starRingEnd ℂ) ⊗ₖ (K ^ m)‖
      ≤ ‖(K ^ m).map (starRingEnd ℂ)‖ * ‖K ^ m‖ := linfty_opNorm_kronecker_le _ _
    _ ≤ (C * r ^ m) * (C * r ^ m) := by
        rw [linfty_opNorm_map_conj]
        exact mul_le_mul (hK m) (hK m) (norm_nonneg _) ((norm_nonneg _).trans (hK m))
    _ = C * C * (r * r) ^ m := by ring

end PowerBound

end BosonicLean
