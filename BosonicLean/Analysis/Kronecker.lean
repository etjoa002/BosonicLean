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
* `BosonicLean.hasSum_kronecker_left`: `X ⊗ₖ ·` preserves sums.
* `BosonicLean.list_ofFn_prod_sum`: an ordered product of sums is the sum of ordered products.
* `BosonicLean.trace_kronecker_mul_list_ofFn_sum`: the trace of a product of rank-one Kronecker
  sums factorizes into a trace and a product of bilinear pairings.
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

/-! ### Sums -/

section Sum

variable {ι l m n p α : Type*} [NonUnitalNonAssocSemiring α] [TopologicalSpace α]
  [IsTopologicalSemiring α]

/-- `X ⊗ₖ ·` preserves sums: if `Σᵢ fᵢ = S`, then `Σᵢ X ⊗ₖ fᵢ = X ⊗ₖ S`. -/
theorem hasSum_kronecker_left {f : ι → Matrix n p α} {S : Matrix n p α} (h : HasSum f S)
    (X : Matrix l m α) : HasSum (fun i => X ⊗ₖ f i) (X ⊗ₖ S) :=
  Pi.hasSum.2 fun ij => Pi.hasSum.2 fun kl => by
    simpa only [kroneckerMap_apply] using
      ((Pi.hasSum.1 (Pi.hasSum.1 h ij.2) kl.2).mul_left (X ij.1 kl.1))

end Sum

/-! ### Products of rank-one Kronecker factors -/

section RankOne

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The ordered product of sums is the sum of ordered products. -/
theorem list_ofFn_prod_sum {R : Type*} [Ring R] :
    ∀ {M : ℕ} (x : Fin M → ι → R),
      (List.ofFn fun j => ∑ I, x j I).prod = ∑ I : Fin M → ι, (List.ofFn fun j => x j (I j)).prod
  | 0, x => by simp
  | M + 1, x => by
    rw [List.ofFn_succ, List.prod_cons, list_ofFn_prod_sum fun j => x j.succ, sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (M + 1) => ι).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun I _ => sum_congr rfl fun J _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

/-- `Tr(uvᵀ · u w₁ᵀ ⋯ u w_Mᵀ) = (v⬝u)(w₁⬝u) ⋯ (w_M⬝u)`. -/
theorem trace_vecMulVec_mul_list_prod (u : κ → ℂ) :
    ∀ (l : List (κ → ℂ)) (v : κ → ℂ),
      trace (vecMulVec u v * (l.map (vecMulVec u)).prod) = (v ⬝ᵥ u) * (l.map (· ⬝ᵥ u)).prod
  | [], v => by rw [List.map_nil, List.prod_nil, Matrix.mul_one, trace_vecMulVec,
      dotProduct_comm, List.map_nil, List.prod_nil, mul_one]
  | w :: l, v => by
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, vecMulVec_mul_vecMulVec, vecMulVec_smul,
      Matrix.smul_mul, trace_smul, trace_vecMulVec_mul_list_prod u l w, List.map_cons,
      List.prod_cons, smul_eq_mul]

/-- For `M ≥ 1`, `Tr(u w₁ᵀ ⋯ u w_Mᵀ) = ∏ⱼ (wⱼ⬝u)`. -/
theorem trace_list_ofFn_vecMulVec {M : ℕ} (hM : 1 ≤ M) (u : κ → ℂ) (w : Fin M → κ → ℂ) :
    trace (List.ofFn fun j => vecMulVec u (w j)).prod = ∏ j, (w j ⬝ᵥ u) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hl : (List.ofFn fun i : Fin M => vecMulVec u (w i.succ)) =
      (List.ofFn fun i : Fin M => w i.succ).map (vecMulVec u) := by
    rw [List.map_ofFn]
    rfl
  have hr : (List.ofFn fun i : Fin M => w i.succ).map (· ⬝ᵥ u) =
      List.ofFn fun i : Fin M => w i.succ ⬝ᵥ u := by
    rw [List.map_ofFn]
    rfl
  rw [List.ofFn_succ, List.prod_cons, hl, trace_vecMulVec_mul_list_prod, hr, List.prod_ofFn,
    Fin.prod_univ_succ]

/-- **Trace of a product of rank-one Kronecker sums.** For `M ≥ 1` sites, matrices `fⱼ(I)`,
vectors `gⱼ(I)` and `u`:
`Tr((B ⊗ 1) ∏ⱼ Σ_I fⱼ(I) ⊗ u gⱼ(I)ᵀ) = Σ_{I₁,…,I_M} Tr(B f₁(I₁) ⋯ f_M(I_M)) ∏ⱼ (gⱼ(Iⱼ)⬝u)`. -/
theorem trace_kronecker_mul_list_ofFn_sum {D M : ℕ} (hM : 1 ≤ M) (B : Matrix (Fin D) (Fin D) ℂ)
    (f : Fin M → ι → Matrix (Fin D) (Fin D) ℂ) (g : Fin M → ι → κ → ℂ) (u : κ → ℂ) :
    trace ((B ⊗ₖ (1 : Matrix κ κ ℂ)) *
        (List.ofFn fun j => ∑ I, f j I ⊗ₖ vecMulVec u (g j I)).prod) =
      ∑ I : Fin M → ι, trace (B * (List.ofFn fun j => f j (I j)).prod) *
        ∏ j, (g j (I j) ⬝ᵥ u) := by
  rw [list_ofFn_prod_sum, Matrix.mul_sum, trace_sum]
  refine sum_congr rfl fun I _ => ?_
  rw [← list_ofFn_prod_kronecker, ← mul_kronecker_mul, Matrix.one_mul, trace_kronecker,
    trace_list_ofFn_vecMulVec hM]

end RankOne

end BosonicLean
