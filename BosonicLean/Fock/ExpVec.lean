/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.SecondQuantization
import BosonicLean.Fock.OneMode
import BosonicLean.Fock.TensorNorm
import BosonicLean.Analysis.Mehler
import BosonicLean.Analysis.ProductSeries
import BosonicLean.Analysis.GramIsometry
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.PSeries

/-!
# Exponential vectors and the operators of the Gaussian unitaries

For `z ∈ ℂ^ι` the **exponential vector** `ε(z) = e^{z·a†}∣0⟩` has coefficients
`ε(z)(n) = zⁿ/√(n!)`; it lies in `Γ_s(ι)` with `⟨ε(w), ε(z)⟩ = e^{⟨w, z⟩}`, depends continuously on
`z`, and is an eigenvector of every `aⱼ` (Lemma 2). The exponential vectors are total in `Γ_s`
(Theorem 4): the coefficients of `ψ` are the Taylor coefficients of the entire function
`t ↦ ⟨ε(t w), ψ⟩` (Lemma 3).

The file then sets up the operators of the normal-ordered forms of the displacement and squeezing
operators: the Gaussian raising operators `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)` and their exponentials, which act
on product vectors factor by factor, and the lowering operators `-ᾱ·a` and `½ Σⱼ τ̄ⱼ aⱼ²`, whose
exponentials converge coefficient by coefficient on `Γ_s` and are represented by inner products
with explicit vectors (Lemma 5). A linear map from `Γ_s` to the formal Fock space with continuous
coefficients that preserves the inner products of exponential vectors is an isometry of `Γ_s`
(Lemma 6). Finally, an ℓ¹ estimate for the creation operators gives the derivative at `t = 0` of
`t ↦ e^{Σⱼ (κⱼ(t) aⱼ†² + ℓⱼ(t) aⱼ†)} ∣m⟩`, used for the generators of Theorems 10(c) and 17(c).

## Main definitions

* `BosonicLean.Fock.FormalFock.expVecFormal z`, `BosonicLean.Fock.FockSpace.expVec z`: `ε(z)`.
* `BosonicLean.Fock.FockSpace.vacuum`: the vacuum `∣0⟩ ∈ Γ_s`.
* `BosonicLean.Fock.FormalFock.gaussRaise κ ℓ`: `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)`; `raiseDisp`,
  `raiseSqueeze`, `lowerDisp`, `lowerSqueeze`: the operators of the ordered forms.
* `BosonicLean.Fock.FormalFock.l1Norm`, `VanishesAbove`: the auxiliary ℓ¹ norm and the particle
  bound used for the derivatives.

## Main results

* `FockSpace.inner_expVec`, `continuous_expVec`, `FormalFock.annihilate_expVecFormal`: Lemma 2.
* `FockSpace.eq_zero_of_hasSum_pow`, `hasSum_inner_expVec_smul`: Lemma 3.
* `FockSpace.dense_span_expVec`: Theorem 4, totality.
* `FockSpace.summable_coeffExp_lowerDisp`, `coeff_coeffExp_lowerSqueeze`,
  `not_memℓp_raiseSqueeze`: Lemma 5.
* `FockSpace.exists_linearIsometry_of_expVec`, `eq_of_eqOn_expVec`: Lemma 6.
* `FockSpace.hasDerivAt_gaussRaise_exp`: the derivative of a raising exponential on a number state.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), (5), (C17).
* K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser (1992), §19.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open Finset

namespace BosonicLean.Fock

namespace FormalFock

variable {ι : Type*}

/-! ### The Gaussian raising operators on many modes -/

section Gauss

variable [Fintype ι]

/-- The operator `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)`, which raises the particle number. -/
noncomputable def gaussRaise (κ ℓ : ι → ℂ) : NumberRaisingOp ι ℂ :=
  ⟨∑ j, ((gen (κ j) j 2 (by norm_num)).op + (gen (ℓ j) j 1 le_rfl).op),
    RaisesParticleNumber.sum _ fun j _ =>
      (gen (κ j) j 2 _).raisesParticleNumber.add (gen (ℓ j) j 1 le_rfl).raisesParticleNumber⟩

/-- `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)` as an operator. -/
theorem gaussRaise_op (κ ℓ : ι → ℂ) :
    (gaussRaise κ ℓ).op = ∑ j, (κ j • create j ^ 2 + ℓ j • create j) := by
  simp only [gaussRaise, gen_op_eq_smul, pow_one]

/-- The partial sums `Σ_{j ∈ s} (κⱼ aⱼ†² + ℓⱼ aⱼ†)`. -/
private noncomputable def gaussRaisePartial (κ ℓ : ι → ℂ) (s : Finset ι) :
    NumberRaisingOp ι ℂ :=
  ⟨∑ j ∈ s, ((gen (κ j) j 2 (by norm_num)).op + (gen (ℓ j) j 1 le_rfl).op),
    RaisesParticleNumber.sum _ fun j _ =>
      (gen (κ j) j 2 _).raisesParticleNumber.add (gen (ℓ j) j 1 le_rfl).raisesParticleNumber⟩

omit [Fintype ι] in
private theorem commute_gen_add_gen (κ ℓ κ' ℓ' : ℂ) (i j : ι) :
    Commute ((gen κ i 2 (by norm_num) : NumberRaisingOp ι ℂ).op + (gen ℓ i 1 le_rfl).op)
      ((gen κ' j 2 (by norm_num)).op + (gen ℓ' j 1 le_rfl).op) :=
  ((commute_gen_gen _ _ _ _ _ _).add_right (commute_gen_gen _ _ _ _ _ _)).add_left
    ((commute_gen_gen _ _ _ _ _ _).add_right (commute_gen_gen _ _ _ _ _ _))

private theorem gaussRaisePartial_exp_tensorVec [DecidableEq ι] (κ ℓ : ι → ℂ) (s : Finset ι)
    (φ : ι → FormalFock Unit ℂ) :
    (gaussRaisePartial κ ℓ s).exp (tensorVec φ) =
      tensorVec fun j => if j ∈ s then gaussExp (κ j) (ℓ j) (φ j) else φ j := by
  induction s using Finset.induction_on with
  | empty =>
    rw [NumberRaisingOp.exp_of_op_eq_zero (by simp [gaussRaisePartial])]
    simp
  | insert a s ha ih =>
    set G : NumberRaisingOp ι ℂ := gen (κ a) a 2 (by norm_num) + gen (ℓ a) a 1 le_rfl
    have hop : (gaussRaisePartial κ ℓ (insert a s)).op = (G + gaussRaisePartial κ ℓ s).op := by
      simp only [gaussRaisePartial, NumberRaisingOp.add_op, G, sum_insert ha]
    have hc : Commute G.op (gaussRaisePartial κ ℓ s).op :=
      Commute.sum_right _ _ _ fun j _ => commute_gen_add_gen _ _ _ _ a j
    have hG : G.exp = onMode a (gaussExp (κ a) (ℓ a)) := by
      refine (onMode_exp a _ G ?_).symm
      simp only [NumberRaisingOp.add_op, G, onMode_add, onMode_gen_op]
    rw [NumberRaisingOp.exp_congr hop, NumberRaisingOp.exp_add _ _ hc, Module.End.mul_apply, ih,
      hG, onMode_tensorVec]
    congr 1
    funext j
    by_cases hj : j = a
    · subst hj
      simp [ha]
    · rw [Function.update_of_ne hj]
      simp [hj]

/-- **Gaussian operators on many modes act on product vectors factor by factor:**
`e^{Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)} (⊗ⱼ φⱼ) = ⊗ⱼ e^{κⱼ a†² + ℓⱼ a†} φⱼ`. -/
theorem gaussRaise_exp_tensorVec (κ ℓ : ι → ℂ) (φ : ι → FormalFock Unit ℂ) :
    (gaussRaise κ ℓ).exp (tensorVec φ) = tensorVec fun j => gaussExp (κ j) (ℓ j) (φ j) := by
  classical
  have h : gaussRaise κ ℓ = gaussRaisePartial κ ℓ univ := rfl
  rw [h, gaussRaisePartial_exp_tensorVec]
  simp

/-- On the vacuum, `e^{Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)} ∣0⟩ = ⊗ⱼ e^{κⱼ a†² + ℓⱼ a†} ∣0⟩`. -/
theorem gaussRaise_exp_vacuum [DecidableEq ι] (κ ℓ : ι → ℂ) :
    (gaussRaise κ ℓ).exp (single 0 1) = tensorVec fun j => gaussVec (κ j) (ℓ j) := by
  rw [← tensorVec_vacuum, gaussRaise_exp_tensorVec]
  simp only [gaussExp_vacuum]

end Gauss

/-! ### The coefficients of a single-mode Gaussian vector -/

/-- **The coefficients of `e^{κ a†² + ℓ a†} ∣0⟩`**: `√(m!) Cₘ(κ, ℓ)` at `∣m⟩`. -/
theorem coeff_gaussVec (κ ℓ : ℂ) (m : ℕ) :
    (gaussVec κ ℓ).coeff (Finsupp.single () m) = sqrtC m.factorial * cMatrix κ ℓ m := by
  have hB : PowerSeries.coeff m (bargmann (gaussVec κ ℓ)) = cMatrix κ ℓ m := by
    rw [bargmann_apply, toBargmann_photonAdded, pow_zero, one_mul]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, cMatrix]
    simp only [coeff_expSeries_unit κ (by norm_num : 1 ≤ 2), coeff_expSeries_unit ℓ le_rfl,
      Nat.div_one, one_dvd, ↓reduceIte]
    have himg : Set.InjOn (fun t : ℕ => 2 * t) (range (m / 2 + 1)) := fun a _ b _ h => by
      simp only at h; omega
    rw [← sum_subset (s₁ := (range (m / 2 + 1)).image fun t => 2 * t)]
    · rw [sum_image himg]
      refine sum_congr rfl fun t ht => ?_
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left t two_pos, smul_eq_mul]
      push_cast
      ring
    · intro i hi
      simp only [mem_image, mem_range] at hi ⊢
      obtain ⟨t, ht, rfl⟩ := hi
      omega
    · intro i _ hi
      split_ifs with h2
      · exfalso
        apply hi
        obtain ⟨t, rfl⟩ := h2
        simp only [mem_image, mem_range]
        refine ⟨t, ?_, rfl⟩
        simp only [mem_range] at *
        omega
      · rw [zero_mul]
  have hc := hB
  rw [bargmann_apply] at hc
  change MvPowerSeries.coeff (Finsupp.single () m) (toBargmann (gaussVec κ ℓ)) = _ at hc
  rw [coeff_toBargmann, sqrtFactorial, factorial_single, smul_eq_mul] at hc
  rw [← hc, ← mul_assoc, mul_inv_cancel₀ (sqrtC_ne_zero (Nat.factorial_pos m)), one_mul]

/-! ### Exponential vectors -/

section ExpVec

variable [Fintype ι]

/-- **Definition 1.** The **exponential vector** `ε(z) = e^{z·a†}∣0⟩` as a formal vector, with
coefficients `ε(z)(n) = zⁿ/√(n!)`, where `zⁿ = ∏ⱼ zⱼ^{nⱼ}` (`expVecFormal_eq_exp`). -/
noncomputable def expVecFormal (z : ι → ℂ) : FormalFock ι ℂ :=
  ⟨fun n => (∏ j, z j ^ n j) / sqrtFactorial n⟩

/-- The coefficients `ε(z)(n) = zⁿ/√(n!)` of the exponential vector. -/
theorem coeff_expVecFormal (z : ι → ℂ) (n : ι →₀ ℕ) :
    (expVecFormal z).coeff n = (∏ j, z j ^ n j) / sqrtFactorial n :=
  rfl

/-- The single-mode exponential vector is the Gaussian vector with `κ = 0`. -/
theorem gaussVec_zero_left (w : ℂ) : gaussVec 0 w = expVecFormal fun _ : Unit => w := by
  ext n
  obtain ⟨m, rfl⟩ : ∃ m, n = Finsupp.single () m := ⟨n (), Finsupp.unique_single n⟩
  rw [coeff_gaussVec, cMatrix_zero_left, coeff_expVecFormal, sqrtFactorial, factorial_single]
  simp only [Finsupp.single_eq_same, Finset.univ_unique, Finset.prod_singleton, smul_eq_mul]
  have h := sqrtC_mul_self m.factorial
  have h0 := sqrtC_ne_zero (Nat.factorial_pos m)
  rw [eq_div_iff h0, ← h]
  field_simp

/-- **Lemma 2(c).** `ε(z) = ⊗ⱼ ε(zⱼ)`, a product vector. -/
theorem expVecFormal_eq_tensorVec (z : ι → ℂ) :
    expVecFormal z = tensorVec fun j => expVecFormal fun _ : Unit => z j := by
  ext n
  rw [coeff_expVecFormal, coeff_tensorVec, sqrtFactorial_eq_prod, ← prod_div_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [coeff_expVecFormal, sqrtFactorial, factorial_single]
  simp

variable [DecidableEq ι]

/-- `α·a† = Σⱼ αⱼ aⱼ†`, which raises the particle number. -/
noncomputable def raiseDisp (α : ι → ℂ) : NumberRaisingOp ι ℂ := gaussRaise 0 α

omit [DecidableEq ι] in
/-- `α·a† = Σⱼ αⱼ aⱼ†` as an operator. -/
theorem raiseDisp_op (α : ι → ℂ) : (raiseDisp α).op = ∑ j, α j • create j := by
  simp [raiseDisp, gaussRaise_op]

/-- **Definition 1.** `ε(z) = e^{z·a†}∣0⟩`. -/
theorem expVecFormal_eq_exp (z : ι → ℂ) : expVecFormal z = (raiseDisp z).exp (single 0 1) := by
  rw [raiseDisp, gaussRaise_exp_vacuum, expVecFormal_eq_tensorVec]
  simp only [Pi.zero_apply, gaussVec_zero_left]

/-- `ε(0) = ∣0⟩`. -/
theorem expVecFormal_zero : expVecFormal (0 : ι → ℂ) = single 0 1 := by
  ext n
  rw [coeff_expVecFormal, coeff_single]
  by_cases hn : n = 0
  · subst hn
    simp [sqrtFactorial, sqrtC]
  · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hn
    simp only [hn, ↓reduceIte]
    rw [prod_eq_zero (mem_univ j) (by rw [Pi.zero_apply, zero_pow (by simpa using hj)]),
      zero_div]

omit [DecidableEq ι] in
/-- **Lemma 2(b).** `aⱼ ε(z) = zⱼ ε(z)`: exponential vectors are eigenvectors of the annihilation
operators. -/
theorem annihilate_expVecFormal (z : ι → ℂ) (j : ι) :
    annihilate j (expVecFormal z) = z j • expVecFormal z := by
  ext n
  rw [coeff_annihilate, coeff_expVecFormal, coeff_smul, coeff_expVecFormal,
    sqrtFactorial_add_single, smul_eq_mul, smul_eq_mul]
  have hp : ∏ k, z k ^ (n + Finsupp.single j 1 : ι →₀ ℕ) k = z j * ∏ k, z k ^ n k := by
    simp only [Finsupp.add_apply, pow_add, prod_mul_distrib]
    rw [mul_comm, prod_eq_single j (fun k _ hk => by simp [Finsupp.single_eq_of_ne hk])
      (by simp)]
    simp
  have h0 := sqrtC_ne_zero (Nat.succ_pos (n j))
  have h1 := sqrtFactorial_ne_zero n
  rw [hp]
  field_simp

omit [DecidableEq ι] in
/-- `Γ(g)` intertwines exponentials of operators that raise the particle number: if
`Γ(g) T = T' Γ(g)`, then `Γ(g) e^T = e^{T'} Γ(g)`. -/
theorem secondQuant_mul_exp_of_mul_eq (g : Matrix ι ι ℂ) {T T' : NumberRaisingOp ι ℂ}
    (h : secondQuant g * T.op = T'.op * secondQuant g) :
    secondQuant g * T.exp = T'.exp * secondQuant g := by
  classical
  have hk : ∀ k : ℕ, secondQuant g * T.op ^ k = T'.op ^ k * secondQuant g := fun k =>
    (SemiconjBy.pow_right (a := secondQuant g) h k)
  refine LinearMap.ext fun ψ => ?_
  ext m
  rw [Module.End.mul_apply, Module.End.mul_apply, coeff_secondQuant, NumberRaisingOp.coeff_exp]
  have hsum : ∀ n ∈ finsuppAntidiag (univ : Finset ι) m.degree,
      matrixCoeff g m n * (T.exp ψ).coeff n =
        ∑ k ∈ range (m.degree + 1),
          ((k.factorial : ℂ)⁻¹) * (matrixCoeff g m n * ((T.op ^ k) ψ).coeff n) := by
    intro n hn
    rw [mem_finsuppAntidiag_univ] at hn
    rw [NumberRaisingOp.coeff_exp_eq_sum T ψ hn.le, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul]
    ring
  rw [sum_congr rfl hsum, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_sum, ← coeff_secondQuant, ← Module.End.mul_apply, hk, Module.End.mul_apply,
    smul_eq_mul]

omit [DecidableEq ι] in
/-- `Γ(g) (z·a†) = ((g z)·a†) Γ(g)`. -/
theorem secondQuant_mul_raiseDisp (g : Matrix ι ι ℂ) (z : ι → ℂ) :
    secondQuant g * (raiseDisp z).op = (raiseDisp (g.mulVec z)).op * secondQuant g := by
  rw [raiseDisp_op, raiseDisp_op, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, secondQuant_mul_create, Finset.sum_mul, Finset.smul_sum, smul_mul_assoc,
    smul_smul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_comm]

omit [DecidableEq ι] in
/-- **Lemma 2(b).** `Γ(g) ε(z) = ε(g z)` for every matrix `g`. -/
theorem secondQuant_expVecFormal (g : Matrix ι ι ℂ) (z : ι → ℂ) :
    secondQuant g (expVecFormal z) = expVecFormal (g.mulVec z) := by
  classical
  rw [expVecFormal_eq_exp, expVecFormal_eq_exp, ← Module.End.mul_apply,
    secondQuant_mul_exp_of_mul_eq g (secondQuant_mul_raiseDisp g z), Module.End.mul_apply,
    secondQuant_vacuum]

omit [DecidableEq ι] in
/-- `e^{α·a†} ε(z) = ε(z + α)`, the exponential law for the raising exponentials. -/
theorem raiseDisp_exp_expVecFormal (α z : ι → ℂ) :
    (raiseDisp α).exp (expVecFormal z) = expVecFormal (z + α) := by
  classical
  rw [expVecFormal_eq_tensorVec, raiseDisp, gaussRaise_exp_tensorVec, expVecFormal_eq_tensorVec]
  congr 1
  funext j
  rw [Pi.zero_apply, ← gaussVec_zero_left, ← gaussVec_zero_left, ← gaussExp_vacuum,
    ← Module.End.mul_apply, gaussExp_mul_gaussExp, gaussExp_vacuum, add_zero, Pi.add_apply,
    add_comm]

end ExpVec

/-! ### Overlaps of product vectors -/

section Overlap

/-- `‖conj a * b‖ ≤ (‖a‖² + ‖b‖²)/2`. -/
private theorem norm_conj_mul_le (a b : ℂ) : ‖conj a * b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The overlap series of two square-summable families converges absolutely. -/
theorem summable_norm_conj_mul {α : Type*} {a b : α → ℂ} (ha : Summable fun i => ‖a i‖ ^ 2)
    (hb : Summable fun i => ‖b i‖ ^ 2) : Summable fun i => ‖conj (a i) * b i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_conj_mul_le (a i) (b i))
    ((ha.add hb).div_const 2)

variable [Fintype ι]

/-- **The overlap of product vectors** with square-summable factors:
`Σₙ conj((⊗φ)(n)) (⊗ψ)(n) = ∏ⱼ Σₘ conj(φⱼ(m)) ψⱼ(m)`, the series converging absolutely. -/
theorem hasSum_conj_mul_tensorVec {φ ψ : ι → FormalFock Unit ℂ}
    (hφ : ∀ j, Summable fun m : ℕ => ‖(φ j).coeff (Finsupp.single () m)‖ ^ 2)
    (hψ : ∀ j, Summable fun m : ℕ => ‖(ψ j).coeff (Finsupp.single () m)‖ ^ 2) :
    HasSum (fun n => conj ((tensorVec φ).coeff n) * (tensorVec ψ).coeff n)
      (∏ j, ∑' m : ℕ, conj ((φ j).coeff (Finsupp.single () m)) *
        (ψ j).coeff (Finsupp.single () m)) := by
  obtain ⟨-, h⟩ := hasSum_prod_apply_of_summable_norm (R := ℂ)
    (g := fun j m => conj ((φ j).coeff (Finsupp.single () m)) * (ψ j).coeff (Finsupp.single () m))
    fun j => summable_norm_conj_mul (hφ j) (hψ j)
  rw [← (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).hasSum_iff] at h
  convert h using 2 with n
  simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply, coeff_tensorVec, map_prod,
    prod_mul_distrib]

/-- The one-mode exponential vector at `∣m⟩`: `wᵐ/√(m!)`. -/
theorem coeff_expVecFormal_unit (w : ℂ) (m : ℕ) :
    (expVecFormal fun _ : Unit => w).coeff (Finsupp.single () m) = w ^ m / sqrtC m.factorial := by
  rw [coeff_expVecFormal, sqrtFactorial, factorial_single]
  simp

/-- The one-mode exponential vector is square-summable: `Σₘ |w|^{2m}/m! = e^{|w|²}`. -/
theorem summable_sq_coeff_expVecFormal_unit (w : ℂ) :
    Summable fun m : ℕ => ‖(expVecFormal fun _ : Unit => w).coeff (Finsupp.single () m)‖ ^ 2 := by
  refine (Real.summable_pow_div_factorial (‖w‖ ^ 2)).congr fun m => ?_
  rw [coeff_expVecFormal_unit, norm_div, norm_pow, div_pow, ← pow_mul, sqrtC,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), mul_comm]
  rw [pow_mul]

/-- The one-mode overlap `Σₘ conj(ε(w)(m)) ε(z)(m) = e^{w̄ z}`. -/
private theorem hasSum_conj_mul_expVecFormal_unit (w z : ℂ) :
    HasSum (fun m : ℕ => conj ((expVecFormal fun _ : Unit => w).coeff (Finsupp.single () m)) *
      (expVecFormal fun _ : Unit => z).coeff (Finsupp.single () m)) (Complex.exp (conj w * z)) := by
  rw [Complex.exp_eq_exp_ℂ]
  refine (NormedSpace.expSeries_div_hasSum_exp (conj w * z)).congr_fun fun m => ?_
  rw [coeff_expVecFormal_unit, coeff_expVecFormal_unit, map_div₀, map_pow, sqrtC,
    Complex.conj_ofReal, ← sqrtC, mul_pow, div_mul_div_comm, sqrtC_mul_self]

/-- **Lemma 2(a), as a series.** `Σₙ conj(ε(w)(n)) ε(z)(n) = e^{⟨w, z⟩}`, absolutely convergent,
with `⟨w, z⟩ = Σⱼ w̄ⱼ zⱼ`. -/
theorem hasSum_conj_mul_expVecFormal (w z : ι → ℂ) :
    HasSum (fun n => conj ((expVecFormal w).coeff n) * (expVecFormal z).coeff n)
      (Complex.exp (∑ j, conj (w j) * z j)) := by
  rw [expVecFormal_eq_tensorVec w, expVecFormal_eq_tensorVec z, Complex.exp_sum]
  convert hasSum_conj_mul_tensorVec (fun j => summable_sq_coeff_expVecFormal_unit (w j))
    (fun j => summable_sq_coeff_expVecFormal_unit (z j)) using 2 with j
  exact (hasSum_conj_mul_expVecFormal_unit (w j) (z j)).tsum_eq.symm

/-- The exponential vectors are square-summable. -/
theorem memℓp_expVecFormal (z : ι → ℂ) : Memℓp (expVecFormal z).coeff 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have h := (hasSum_conj_mul_expVecFormal z z).summable
  have h' : Summable fun n => ((‖(expVecFormal z).coeff n‖ ^ 2 : ℝ) : ℂ) := by
    refine h.congr fun n => ?_
    rw [Complex.conj_mul', Complex.ofReal_pow]
  simpa using Complex.summable_ofReal.1 h'

end Overlap

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Exponential vectors in the Fock space -/

/-- The vacuum `∣0⟩` of `Γ_s(ι)`. -/
noncomputable def vacuum : FockSpace ι := lp.single 2 0 1

omit [Fintype ι] in
/-- The vacuum of `Γ_s` is the formal vacuum `∣0⟩`. -/
theorem toFormal_vacuum : toFormal (vacuum : FockSpace ι) = single 0 1 :=
  toFormal_lpSingle 0

/-- **Definition 1.** The exponential vector `ε(z) = e^{z·a†}∣0⟩` as a vector of `Γ_s(ι)`. -/
noncomputable def expVec (z : ι → ℂ) : FockSpace ι := ⟨(expVecFormal z).coeff, memℓp_expVecFormal z⟩

omit [DecidableEq ι] in
/-- The exponential vector of `Γ_s` has the coefficients of `ε(z)`. -/
theorem toFormal_expVec (z : ι → ℂ) : toFormal (expVec z) = expVecFormal z := rfl

omit [DecidableEq ι] in
/-- The coefficients `ε(z)(n) = zⁿ/√(n!)` of the exponential vector of `Γ_s`. -/
theorem expVec_apply (z : ι → ℂ) (n : ι →₀ ℕ) :
    expVec z n = (∏ j, z j ^ n j) / sqrtFactorial n := rfl

omit [DecidableEq ι] in
/-- **Lemma 2(a).** `⟨ε(w), ε(z)⟩ = e^{⟨w, z⟩}` with `⟨w, z⟩ = Σⱼ w̄ⱼ zⱼ`. -/
theorem inner_expVec (w z : ι → ℂ) :
    ⟪expVec w, expVec z⟫_ℂ = Complex.exp (∑ j, conj (w j) * z j) := by
  classical
  refine (lp.hasSum_inner (expVec w) (expVec z)).unique ?_
  convert hasSum_conj_mul_expVecFormal w z using 2 with n
  rw [RCLike.inner_apply']
  rfl

omit [DecidableEq ι] in
/-- `‖ε(z)‖² = e^{|z|²}`. -/
theorem norm_expVec_sq (z : ι → ℂ) : ‖expVec z‖ ^ 2 = Real.exp (∑ j, ‖z j‖ ^ 2) := by
  classical
  have h := inner_expVec z z
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∑ j, conj (z j) * z j = ((∑ j, ‖z j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact sum_congr rfl fun j _ => Complex.conj_mul' (z j)
  rw [h2] at h
  have h3 := congrArg Complex.re h
  simp only [Complex.exp_ofReal_re] at h3
  rw [← h3]
  norm_cast

omit [DecidableEq ι] in
/-- **Lemma 2(a).** `z ↦ ε(z)` is continuous into `Γ_s`. -/
theorem continuous_expVec : Continuous (expVec (ι := ι)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro z₀
  have hF : Continuous fun z : ι → ℂ => ‖expVec z - expVec z₀‖ ^ 2 := by
    have he : (fun z : ι → ℂ => ‖expVec z - expVec z₀‖ ^ 2) = fun z =>
        Real.exp (∑ j, ‖z j‖ ^ 2) -
          2 * (Complex.exp (∑ j, conj (z j) * z₀ j)).re + Real.exp (∑ j, ‖z₀ j‖ ^ 2) := by
      funext z
      rw [@norm_sub_sq ℂ, norm_expVec_sq, norm_expVec_sq, inner_expVec]
      rfl
    rw [he]
    fun_prop
  have h0 : Filter.Tendsto (fun z : ι → ℂ => ‖expVec z - expVec z₀‖ ^ 2) (nhds z₀) (nhds 0) := by
    have := hF.tendsto z₀
    simpa using this
  have h1 : Filter.Tendsto (fun z : ι → ℂ => ‖expVec z - expVec z₀‖) (nhds z₀) (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_iff_norm_sub_tendsto_zero.2 h1

/-- `ε(0) = ∣0⟩`. -/
theorem expVec_zero : expVec (0 : ι → ℂ) = vacuum :=
  toFormal_injective (by rw [toFormal_expVec, toFormal_vacuum, expVecFormal_zero])

open scoped Matrix in
/-- `Γ(𝒰) ε(z) = ε(𝒰 z)`. -/
theorem secondQuantRep_expVec (U : Matrix.unitaryGroup ι ℂ) (z : ι → ℂ) :
    (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) (expVec z) =
      expVec ((U : Matrix ι ι ℂ) *ᵥ z) :=
  toFormal_injective (by
    rw [secondQuantRep_apply, toFormal_secondQuantUnitary, toFormal_expVec, toFormal_expVec,
      secondQuant_expVecFormal])

/-- `Γ(𝒰) ∣0⟩ = ∣0⟩`. -/
theorem secondQuantRep_vacuum (U : Matrix.unitaryGroup ι ℂ) :
    (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) vacuum = vacuum := by
  rw [← expVec_zero, secondQuantRep_expVec, Matrix.mulVec_zero]

/-! ### Lemma 3 and Theorem 4: a series in `z̄` equal to a series in `z`; totality -/

/-- **Lemma 3, claim (i).** A real power series that converges and vanishes on all of `ℝ` has
zero coefficients. -/
theorem eq_zero_of_hasSum_pow (c : ℕ → ℂ) (h : ∀ t : ℝ, HasSum (fun p => c p * (t : ℂ) ^ p) 0) :
    c = 0 := by
  -- absolute convergence of `Σ c_p`, from the convergence at `t = 2`
  have habs : Summable fun p => ‖c p‖ := by
    have h2 : Filter.Tendsto (fun p => ‖c p * ((2 : ℝ) : ℂ) ^ p‖) Filter.atTop (nhds 0) := by
      simpa using (h 2).summable.tendsto_atTop_zero.norm
    refine Summable.of_norm_bounded_eventually_nat (g := fun p : ℕ => (1 / 2 : ℝ) ^ p)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
    filter_upwards [h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with p hp
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at hp
    rw [norm_norm, div_pow, one_pow, le_div_iff₀ (by positivity)]
    exact hp.le
  by_contra hc
  have hex : ∃ k, c k ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hc (funext hne)
  classical
  set k := Nat.find hex
  have hk : c k ≠ 0 := Nat.find_spec hex
  have hlt : ∀ p < k, c p = 0 := fun p hp => by
    by_contra h'
    exact Nat.find_min hex hp h'
  set M := ∑' p, ‖c p‖
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  -- for `0 < t ≤ 1`: `‖c_k‖ ≤ t M`
  have hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖c k‖ ≤ t * M := by
    intro t ht0 ht1
    have hs := h t
    have hsplit := hs.summable.sum_add_tsum_nat_add (k + 1)
    rw [hs.tsum_eq, sum_range_succ,
      sum_eq_zero fun i hi => by rw [hlt i (mem_range.1 hi), zero_mul], zero_add] at hsplit
    have htail_s : Summable fun i => ‖c (i + (k + 1))‖ :=
      (summable_nat_add_iff (k + 1)).2 habs
    have htail : ‖∑' i, c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1))‖ ≤ t ^ (k + 1) * M := by
      have hle : ∀ i, ‖c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1))‖ ≤
          t ^ (k + 1) * ‖c (i + (k + 1))‖ := fun i => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le, mul_comm, pow_add]
        gcongr
        calc t ^ i * t ^ (k + 1) ≤ 1 * t ^ (k + 1) := by
              gcongr
              exact pow_le_one₀ ht0.le ht1
          _ = t ^ (k + 1) := one_mul _
      have hs' : Summable fun i => ‖c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1))‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (htail_s.mul_left _)
      calc ‖∑' i, c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1))‖
          ≤ ∑' i, ‖c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1))‖ := norm_tsum_le_tsum_norm hs'
        _ ≤ ∑' i, t ^ (k + 1) * ‖c (i + (k + 1))‖ :=
            hs'.tsum_le_tsum hle (htail_s.mul_left _)
        _ = t ^ (k + 1) * ∑' i, ‖c (i + (k + 1))‖ := tsum_mul_left
        _ ≤ t ^ (k + 1) * M := by
            gcongr
            exact (le_add_of_nonneg_left (sum_nonneg fun _ _ => norm_nonneg _)).trans
              (habs.sum_add_tsum_nat_add (k + 1)).le
    have heq : c k * (t : ℂ) ^ k = -∑' i, c (i + (k + 1)) * (t : ℂ) ^ (i + (k + 1)) :=
      eq_neg_of_add_eq_zero_left hsplit
    have h1 : ‖c k‖ * t ^ k ≤ t ^ (k + 1) * M := by
      have := congrArg norm heq
      rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le] at this
      rw [this]
      exact htail
    have htk : 0 < t ^ k := pow_pos ht0 k
    rw [pow_succ, mul_assoc] at h1
    exact le_of_mul_le_mul_right (by linarith) htk
  have hck : 0 < ‖c k‖ := norm_pos_iff.2 hk
  set t := min 1 (‖c k‖ / (2 * (M + 1)))
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have h1 := hbound t ht0 ht1
  have h2 : t * M < ‖c k‖ := by
    calc t * M ≤ ‖c k‖ / (2 * (M + 1)) * M := by gcongr; exact min_le_right _ _
      _ < ‖c k‖ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  linarith

/-- **Lemma 3, claim (ii).** For `ψ ∈ Γ_s` and real `t`, `⟨ε(t w), ψ⟩ = Σₚ tᵖ Pₚ(w)` with the
sectors summed separately, `Pₚ(w) = Σ_{|n| = p} w̄ⁿ ψ(n)/√(n!)`. -/
theorem hasSum_inner_expVec_smul (ψ : FockSpace ι) (w : ι → ℂ) (t : ℝ) :
    HasSum (fun p : ℕ => (t : ℂ) ^ p * ∑ n ∈ finsuppAntidiag univ p,
      (∏ j, conj (w j) ^ n j) * ψ n / sqrtFactorial n) ⟪expVec ((t : ℂ) • w), ψ⟫_ℂ := by
  set g : (ι →₀ ℕ) → ℂ := fun n => (∏ j, conj (w j) ^ n j) * ψ n / sqrtFactorial n
  have hterm : ∀ n : ι →₀ ℕ, ⟪expVec ((t : ℂ) • w) n, ψ n⟫_ℂ = (t : ℂ) ^ n.degree * g n := by
    intro n
    rw [RCLike.inner_apply', expVec_apply, map_div₀, map_prod, sqrtFactorial, sqrtC,
      Complex.conj_ofReal, ← sqrtC, ← sqrtFactorial, Finsupp.degree_eq_sum]
    simp only [g, Pi.smul_apply, smul_eq_mul, map_pow, map_mul, Complex.conj_ofReal, mul_pow,
      prod_mul_distrib, prod_pow_eq_pow_sum]
    ring
  have hS : HasSum (fun n => (t : ℂ) ^ n.degree * g n) ⟪expVec ((t : ℂ) • w), ψ⟫_ℂ := by
    have := lp.hasSum_inner (𝕜 := ℂ) (expVec ((t : ℂ) • w)) ψ
    simp only [hterm] at this
    exact this
  have hF := hS.tsum_fiberwise Finsupp.degree
  refine hF.congr_fun fun p => ?_
  have hset : (Finsupp.degree ⁻¹' {p} : Set (ι →₀ ℕ)) =
      ↑(finsuppAntidiag (univ : Finset ι) p) := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_finsuppAntidiag_univ]
  rw [tsum_congr_set_coe (fun n => (t : ℂ) ^ n.degree * g n) hset,
    Finset.tsum_subtype' (finsuppAntidiag univ p) (fun n => (t : ℂ) ^ n.degree * g n), mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_finsuppAntidiag_univ.1 hn]

/-- The polynomial `Σ_{|n| = p} aₙ Xⁿ` vanishes at every point only if `aₙ = 0` for `|n| = p`. -/
private theorem coeff_eq_zero_of_forall_sum_eq_zero {p : ℕ} (a : (ι →₀ ℕ) → ℂ)
    (h : ∀ x : ι → ℂ, ∑ n ∈ finsuppAntidiag univ p, a n * ∏ j, x j ^ n j = 0) {n : ι →₀ ℕ}
    (hn : n.degree = p) : a n = 0 := by
  set P : MvPolynomial ι ℂ := ∑ m ∈ finsuppAntidiag univ p, MvPolynomial.monomial m (a m)
  have hP : P = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_zero, map_sum, ← h x]
    refine sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun j => pow_zero _]
  have hc := congrArg (fun Q : MvPolynomial ι ℂ => Q.coeff n) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
  rw [sum_ite_eq', ite_eq_left (mem_finsuppAntidiag_univ.2 hn)] at hc
  simpa using hc

/-- The sector sums `Pₚ(w) = Σ_{|n| = p} w̄ⁿ ψ(n)/√(n!)` of the series in `z̄` (Lemma 3). -/
private noncomputable def sectorSum (ψ : FockSpace ι) (p : ℕ) (w : ι → ℂ) : ℂ :=
  ∑ n ∈ finsuppAntidiag univ p, (∏ j, conj (w j) ^ n j) * ψ n / sqrtFactorial n

/-- The core of Lemma 3: the sector sums of `ψ` are the conjugates of those of `φ`. -/
private theorem sectorSum_eq_conj {ψ φ : FockSpace ι}
    (h : ∀ z, ⟪expVec z, ψ⟫_ℂ = ⟪φ, expVec z⟫_ℂ) (p : ℕ) (w : ι → ℂ) :
    sectorSum ψ p w = conj (sectorSum φ p w) := by
  have hc : (fun q => sectorSum ψ q w - conj (sectorSum φ q w)) = 0 := by
    refine eq_zero_of_hasSum_pow _ fun t => ?_
    have h1 := hasSum_inner_expVec_smul ψ w t
    have h2 := Complex.hasSum_conj'.2 (hasSum_inner_expVec_smul φ w t)
    rw [inner_conj_symm, ← h] at h2
    convert h1.sub h2 using 1
    · funext q
      simp only [sectorSum, map_mul, map_pow, Complex.conj_ofReal]
      ring
    · rw [sub_self]
  exact sub_eq_zero.1 (congrFun hc p)

/-- Lemma 3 in the sectors `p ≥ 1`: both sector sums vanish. -/
private theorem sectorSum_eq_zero {ψ φ : FockSpace ι}
    (h : ∀ z, ⟪expVec z, ψ⟫_ℂ = ⟪φ, expVec z⟫_ℂ) {p : ℕ} (hp : 0 < p) (w : ι → ℂ) :
    sectorSum ψ p w = 0 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq Complex.I hp
  have hrot : ∀ χ : FockSpace ι, sectorSum χ p (u • w) = conj u ^ p * sectorSum χ p w := by
    intro χ
    rw [sectorSum, sectorSum, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hdeg := mem_finsuppAntidiag_univ.1 hn
    rw [← hdeg, Finsupp.degree_eq_sum, ← prod_pow_eq_pow_sum]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_pow, prod_mul_distrib]
    ring
  have e1 := sectorSum_eq_conj h p (u • w)
  rw [hrot, hrot, map_mul, map_pow, Complex.conj_conj, ← sectorSum_eq_conj h p w, hu,
    ← map_pow, hu, Complex.conj_I] at e1
  have : (2 * Complex.I) * sectorSum ψ p w = 0 := by linear_combination -e1
  exact (mul_eq_zero.1 this).resolve_left (by simp [Complex.I_ne_zero])

/-- If all sector sums of `χ` in the sector `p` vanish, then `χ(n) = 0` for `|n| = p`. -/
private theorem coeff_eq_zero_of_sectorSum_eq_zero (χ : FockSpace ι) {p : ℕ}
    (h : ∀ w, sectorSum χ p w = 0) {n : ι →₀ ℕ} (hn : n.degree = p) : χ n = 0 := by
  have hχ := coeff_eq_zero_of_forall_sum_eq_zero (p := p)
    (fun m => χ m / sqrtFactorial m) (fun x => ?_) hn
  · simpa [sqrtFactorial_ne_zero n] using hχ
  have := h fun j => conj (x j)
  rw [sectorSum] at this
  rw [← this]
  refine sum_congr rfl fun m _ => ?_
  simp only [Complex.conj_conj]
  ring

omit [DecidableEq ι] in
/-- **Lemma 3.** If `⟨ε(z), ψ⟩ = ⟨φ, ε(z)⟩` for every `z` (a series in `z̄` equal to a series in
`z`), then `ψ(n) = φ(n) = 0` for `n ≠ 0`. -/
theorem coeff_eq_zero_of_inner_expVec_eq {ψ φ : FockSpace ι}
    (h : ∀ z, ⟪expVec z, ψ⟫_ℂ = ⟪φ, expVec z⟫_ℂ) {n : ι →₀ ℕ} (hn : n ≠ 0) :
    ψ n = 0 ∧ φ n = 0 := by
  classical
  have hp : 0 < n.degree := by
    rw [Nat.pos_iff_ne_zero, Ne, Finsupp.degree_eq_zero_iff]
    exact hn
  refine ⟨coeff_eq_zero_of_sectorSum_eq_zero ψ (fun w => sectorSum_eq_zero h hp w) rfl,
    coeff_eq_zero_of_sectorSum_eq_zero φ (fun w => ?_) rfl⟩
  have h0 := (sectorSum_eq_conj h n.degree w).symm.trans (sectorSum_eq_zero h hp w)
  exact (map_eq_zero _).1 h0

omit [DecidableEq ι] in
/-- **Lemma 3.** Under the same hypothesis, `ψ(0) = conj(φ(0))`. -/
theorem coeff_zero_of_inner_expVec_eq {ψ φ : FockSpace ι}
    (h : ∀ z, ⟪expVec z, ψ⟫_ℂ = ⟪φ, expVec z⟫_ℂ) : ψ 0 = conj (φ 0) := by
  classical
  have h0 := sectorSum_eq_conj h 0 0
  simp only [sectorSum, finsuppAntidiag_zero, sum_singleton, Finsupp.coe_zero, Pi.zero_apply,
    pow_zero, prod_const_one, one_mul, sqrtFactorial, factorial_zero, sqrtC, Nat.cast_one,
    Real.sqrt_one, Complex.ofReal_one, div_one] at h0
  exact h0

omit [DecidableEq ι] in
/-- **Theorem 4 (totality).** The exponential vectors span a dense subspace of `Γ_s(ι)`. -/
theorem dense_span_expVec :
    Dense (Submodule.span ℂ (Set.range (expVec (ι := ι))) : Set (FockSpace ι)) := by
  classical
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro ψ hψ
  have h : ∀ z, ⟪expVec z, ψ⟫_ℂ = ⟪(0 : FockSpace ι), expVec z⟫_ℂ := fun z => by
    rw [inner_zero_left]
    exact (Submodule.mem_orthogonal _ _).1 hψ _ (Submodule.subset_span ⟨z, rfl⟩)
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [coeff_zero_of_inner_expVec_eq h]
    simp
  · rw [(coeff_eq_zero_of_inner_expVec_eq h hn).1]
    simp

end FockSpace

/-! ### Lemma 5: lowering exponentials on `Γ_s` -/

namespace FormalFock

variable {ι : Type*}

/-! #### The pairing with finitely supported vectors -/

section Pairing

/-- The pairing with a vector supported in a finite set `s` is the finite sum over `s`. -/
theorem pairing_eq_sum {φ : FormalFock ι ℂ} {s : Finset (ι →₀ ℕ)}
    (hs : Function.support φ.coeff ⊆ s) (ψ : FormalFock ι ℂ) :
    pairing φ ψ = ∑ n ∈ s, conj (φ.coeff n) * ψ.coeff n := by
  rw [pairing]
  exact finsum_eq_sum_of_support_subset _ fun n hn => hs (Function.mem_support.2 fun h =>
    (Function.mem_support.1 hn) (by rw [h, map_zero, zero_mul]))

/-- `⟨∣m⟩, ψ⟩ = ψ(m)`. -/
theorem pairing_single_one [DecidableEq ι] (m : ι →₀ ℕ) (ψ : FormalFock ι ℂ) :
    pairing (single m 1) ψ = ψ.coeff m := by
  rw [pairing_eq_sum (s := {m}) fun n hn => by
    rw [Function.mem_support, coeff_single] at hn
    simp only [coe_singleton, Set.mem_singleton_iff]
    by_contra h
    exact hn (ite_eq_right h)]
  simp

/-- Finitely supported formal vectors are closed under addition. -/
theorem finite_support_add {φ ψ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite)
    (hψ : (Function.support ψ.coeff).Finite) : (Function.support (φ + ψ).coeff).Finite :=
  (hφ.union hψ).subset (Function.support_add _ _)

/-- Finitely supported formal vectors are closed under scalar multiples. -/
theorem finite_support_smul (c : ℂ) {φ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite) :
    (Function.support (c • φ).coeff).Finite :=
  hφ.subset (Function.support_const_smul_subset c _)

/-- Finitely supported formal vectors are closed under finite sums. -/
theorem finite_support_sum {κ : Type*} (s : Finset κ) {φ : κ → FormalFock ι ℂ}
    (h : ∀ k ∈ s, (Function.support (φ k).coeff).Finite) :
    (Function.support (∑ k ∈ s, φ k).coeff).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty]
    exact Set.finite_empty.subset fun n hn => absurd (coeff_zero n) hn
  | insert k s hk ih =>
    rw [sum_insert hk]
    exact finite_support_add (h k (mem_insert_self k s))
      (ih fun k' hk' => h k' (mem_insert_of_mem hk'))

/-- `aⱼ†` maps finitely supported formal vectors to finitely supported ones. -/
theorem finite_support_create (j : ι) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) : (Function.support (create j φ).coeff).Finite := by
  classical
  refine (hφ.image (· + Finsupp.single j 1)).subset fun n hn => ?_
  rw [Function.mem_support, coeff_create] at hn
  split_ifs at hn with h
  · exact ⟨n - Finsupp.single j 1, right_ne_zero_of_mul hn, sub_single_add_single h⟩
  · exact absurd rfl hn

/-- `aⱼ†^p` maps finitely supported formal vectors to finitely supported ones. -/
theorem finite_support_create_pow (j : ι) (p : ℕ) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) :
    (Function.support (((create j : Module.End ℂ (FormalFock ι ℂ)) ^ p) φ).coeff).Finite := by
  classical
  induction p with
  | zero => simpa using hφ
  | succ p ih => rw [pow_succ', Module.End.mul_apply]; exact finite_support_create j ih

/-- The pairing is additive in its first argument, for finitely supported vectors. -/
theorem pairing_add_left {φ₁ φ₂ : FormalFock ι ℂ} (h₁ : (Function.support φ₁.coeff).Finite)
    (h₂ : (Function.support φ₂.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing (φ₁ + φ₂) ψ = pairing φ₁ ψ + pairing φ₂ ψ := by
  classical
  set s := h₁.toFinset ∪ h₂.toFinset
  have hs₁ : Function.support φ₁.coeff ⊆ s := fun n hn => by simp [s, hn]
  have hs₂ : Function.support φ₂.coeff ⊆ s := fun n hn => by simp [s, hn]
  rw [pairing_eq_sum ((Function.support_add _ _).trans (Set.union_subset hs₁ hs₂)),
    pairing_eq_sum hs₁, pairing_eq_sum hs₂, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [coeff_add, map_add, add_mul]

/-- The pairing is conjugate-linear in its first argument. -/
theorem pairing_smul_left (c : ℂ) {φ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite)
    (ψ : FormalFock ι ℂ) : pairing (c • φ) ψ = conj c * pairing φ ψ := by
  classical
  have hs : Function.support φ.coeff ⊆ hφ.toFinset := by simp
  have hs' : Function.support (c • φ).coeff ⊆ hφ.toFinset := fun n hn =>
    hs (Function.mem_support.2 fun h => (Function.mem_support.1 hn) (by rw [coeff_smul, h,
      smul_zero]))
  rw [pairing_eq_sum hs', pairing_eq_sum hs, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [coeff_smul, smul_eq_mul, map_mul, mul_assoc]

/-- The pairing is additive in its finitely supported first argument. -/
theorem pairing_sum_left {κ : Type*} (s : Finset κ) {φ : κ → FormalFock ι ℂ}
    (h : ∀ k ∈ s, (Function.support (φ k).coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing (∑ k ∈ s, φ k) ψ = ∑ k ∈ s, pairing (φ k) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, sum_empty, pairing_eq_sum (s := ∅) fun n hn => absurd (coeff_zero n) hn]
    simp
  | insert k s hk ih =>
    rw [sum_insert hk, sum_insert hk, pairing_add_left (h k (mem_insert_self k s))
      (finite_support_sum s fun k' hk' => h k' (mem_insert_of_mem hk')),
      ih fun k' hk' => h k' (mem_insert_of_mem hk')]

/-- For a finitely supported `φ`, the pairing `⟨φ, ·⟩` is linear. -/
theorem pairing_add_right {φ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite)
    (ψ₁ ψ₂ : FormalFock ι ℂ) : pairing φ (ψ₁ + ψ₂) = pairing φ ψ₁ + pairing φ ψ₂ := by
  classical
  have hs : Function.support φ.coeff ⊆ hφ.toFinset := by simp
  rw [pairing_eq_sum hs, pairing_eq_sum hs, pairing_eq_sum hs, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [coeff_add, mul_add]

/-- The pairing is linear in its second argument. -/
theorem pairing_smul_right {φ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite) (c : ℂ)
    (ψ : FormalFock ι ℂ) : pairing φ (c • ψ) = c * pairing φ ψ := by
  classical
  have hs : Function.support φ.coeff ⊆ hφ.toFinset := by simp
  rw [pairing_eq_sum hs, pairing_eq_sum hs, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

/-- The pairing is additive in its second argument. -/
theorem pairing_sum_right {κ : Type*} {φ : FormalFock ι ℂ} (hφ : (Function.support φ.coeff).Finite)
    (s : Finset κ) (ψ : κ → FormalFock ι ℂ) :
    pairing φ (∑ k ∈ s, ψ k) = ∑ k ∈ s, pairing φ (ψ k) := by
  classical
  have hs : Function.support φ.coeff ⊆ hφ.toFinset := by simp
  rw [pairing_eq_sum hs]
  simp_rw [pairing_eq_sum hs, coeff_sum, mul_sum]
  exact sum_comm

/-- **The adjointness of `aⱼ†` and `aⱼ`** for the pairing: `⟨aⱼ† φ, ψ⟩ = ⟨φ, aⱼ ψ⟩` for every
finitely supported `φ` and every `ψ`. -/
theorem pairing_create (j : ι) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing (create j φ) ψ = pairing φ (annihilate j ψ) := by
  classical
  classical
  set s := hφ.toFinset
  have hs : Function.support φ.coeff ⊆ s := by simp [s]
  have hs' : Function.support (create j φ).coeff ⊆ s.image (· + Finsupp.single j 1) := by
    intro n hn
    rw [Function.mem_support, coeff_create] at hn
    split_ifs at hn with h
    · exact mem_image.2 ⟨n - Finsupp.single j 1, hs (right_ne_zero_of_mul hn),
        sub_single_add_single h⟩
    · exact absurd rfl hn
  rw [pairing_eq_sum hs', pairing_eq_sum hs, sum_image fun a _ b _ h => add_right_cancel h]
  refine sum_congr rfl fun m _ => ?_
  have hpos : 0 < (m + Finsupp.single j 1 : ι →₀ ℕ) j := by simp
  rw [coeff_create]
  simp only [hpos, ↓reduceIte]
  rw [add_single_sub_single, coeff_annihilate]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, smul_eq_mul, map_mul]
  rw [sqrtC, Complex.conj_ofReal, ← sqrtC]
  ring

/-- `⟨aⱼ†^p φ, ψ⟩ = ⟨φ, aⱼ^p ψ⟩` for finitely supported `φ`. -/
theorem pairing_create_pow (j : ι) (p : ℕ) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing (((create j : Module.End ℂ (FormalFock ι ℂ)) ^ p) φ) ψ =
      pairing φ (((annihilate j : Module.End ℂ (FormalFock ι ℂ)) ^ p) ψ) := by
  classical
  induction p generalizing ψ with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, pairing_create j (finite_support_create_pow j p hφ), ih,
      pow_succ, Module.End.mul_apply]

end Pairing

/-! #### Particle-number sectors

`φ` lies in the sector of `d` particles when `sector d φ = φ` (B5.1's `sector`). -/

section Sector

private theorem coeff_eq_zero_of_sector_eq {d : ℕ} {φ : FormalFock ι ℂ} (h : sector d φ = φ)
    (m : ι →₀ ℕ) (hm : m.degree ≠ d) : φ.coeff m = 0 := by
  rw [← h, coeff_sector]
  simp [hm]

private theorem sector_single [DecidableEq ι] (n : ι →₀ ℕ) :
    sector n.degree (single n (1 : ℂ)) = single n 1 := by
  ext m
  rw [coeff_sector, coeff_single]
  by_cases h : m = n
  · subst h
    simp
  · simp [h]

private theorem sector_create {d : ℕ} {φ : FormalFock ι ℂ} (h : sector d φ = φ) (j : ι) :
    sector (d + 1) (create j φ) = create j φ := by
  ext m
  rw [coeff_sector]
  split_ifs with hm
  · rfl
  · symm
    rw [coeff_create]
    split_ifs with hj
    · rw [coeff_eq_zero_of_sector_eq h _ fun h' => hm (by rw [← degree_sub_single_add_one hj, h']),
        smul_zero]
    · rfl

private theorem sector_create_pow {d : ℕ} {φ : FormalFock ι ℂ} (h : sector d φ = φ) (j : ι)
    (p : ℕ) : sector (d + p) (((create j : Module.End ℂ (FormalFock ι ℂ)) ^ p) φ) =
      ((create j : Module.End ℂ (FormalFock ι ℂ)) ^ p) φ := by
  induction p with
  | zero => simpa using h
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact sector_create ih j

end Sector

/-! #### Lowering operators and their adjoints -/

section Lower

variable [Fintype ι] [DecidableEq ι]

/-- `Σⱼ cⱼ aⱼ†^p` (`p ≥ 1`), raising the particle number. -/
private noncomputable def raiseOp (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) : NumberRaisingOp ι ℂ :=
  ⟨∑ j, (gen (c j) j p hp).op,
    RaisesParticleNumber.sum _ fun j _ => (gen (c j) j p hp).raisesParticleNumber⟩

/-- `Σⱼ c̄ⱼ aⱼ^p`, the adjoint of `Σⱼ cⱼ aⱼ†^p` for the pairing. -/
private noncomputable def lowerOp (c : ι → ℂ) (p : ℕ) : Module.End ℂ (FormalFock ι ℂ) :=
  ∑ j, conj (c j) • (annihilate j : Module.End ℂ (FormalFock ι ℂ)) ^ p

omit [DecidableEq ι] in
private theorem raiseOp_op (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) :
    (raiseOp c hp).op = ∑ j, c j • (create j : Module.End ℂ (FormalFock ι ℂ)) ^ p := by
  classical
  simp only [raiseOp, gen_op_eq_smul]

private theorem sector_raiseOp_pow (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) (r : ℕ)
    (n : ι →₀ ℕ) :
    sector (n.degree + p * r) (((raiseOp c hp).op ^ r) (single n 1)) =
      ((raiseOp c hp).op ^ r) (single n 1) := by
  induction r with
  | zero => simpa using sector_single n
  | succ r ih =>
    rw [raiseOp_op] at ih
    rw [pow_succ', Module.End.mul_apply, raiseOp_op, LinearMap.sum_apply,
      show n.degree + p * (r + 1) = n.degree + p * r + p by ring, map_sum]
    exact sum_congr rfl fun j _ => by
      rw [LinearMap.smul_apply, map_smul, sector_create_pow ih j p]

omit [DecidableEq ι] in
/-- The pairing adjointness `⟨(Σⱼ cⱼ aⱼ†^p) φ, ψ⟩ = ⟨φ, (Σⱼ c̄ⱼ aⱼ^p) ψ⟩`. -/
private theorem pairing_raiseOp (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing ((raiseOp c hp).op φ) ψ = pairing φ (lowerOp c p ψ) := by
  classical
  simp only [raiseOp_op, lowerOp, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [pairing_sum_left _ fun j _ => finite_support_smul _ (finite_support_create_pow j p hφ),
    pairing_sum_right hφ]
  refine sum_congr rfl fun j _ => ?_
  rw [pairing_smul_left _ (finite_support_create_pow j p hφ), pairing_create_pow j p hφ,
    pairing_smul_right hφ]

/-- `((Σⱼ c̄ⱼ aⱼ^p)^r ψ)(n) = ⟨(Σⱼ cⱼ aⱼ†^p)^r ∣n⟩, ψ⟩`. -/
private theorem coeff_lowerOp_pow (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) (r : ℕ) (n : ι →₀ ℕ)
    (ψ : FormalFock ι ℂ) :
    ((lowerOp c p ^ r) ψ).coeff n = pairing (((raiseOp c hp).op ^ r) (single n 1)) ψ := by
  induction r generalizing ψ with
  | zero => simp [pairing_single_one]
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
      pairing_raiseOp c hp (by
        rw [← sector_raiseOp_pow c hp r n]
        exact finite_support_sector _ _)]

/-- The coefficients of `e^{Σⱼ cⱼ aⱼ†^p} ∣n⟩` in the sector `|n| + p r`. -/
private theorem coeff_raiseOp_exp (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) (n : ι →₀ ℕ) (r : ℕ)
    {m : ι →₀ ℕ} (hm : m.degree = n.degree + p * r) :
    ((raiseOp c hp).exp (single n 1)).coeff m =
      ((r.factorial : ℂ)⁻¹) * (((raiseOp c hp).op ^ r) (single n 1)).coeff m := by
  rw [NumberRaisingOp.coeff_exp, sum_eq_single r]
  · rw [smul_eq_mul]
  · intro k _ hk
    rw [coeff_eq_zero_of_sector_eq (sector_raiseOp_pow c hp k n) m fun h => hk (by
      rw [hm] at h; exact (Nat.eq_of_mul_eq_mul_left hp (by omega)).symm), smul_zero]
  · intro hr
    exfalso
    apply hr
    rw [mem_range]
    nlinarith

/-- `e^{Σⱼ cⱼ aⱼ†^p} ∣n⟩` vanishes outside the sectors `|n| + p r`. -/
private theorem coeff_raiseOp_exp_eq_zero (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) (n : ι →₀ ℕ)
    {m : ι →₀ ℕ} (hm : ∀ r, m.degree ≠ n.degree + p * r) :
    ((raiseOp c hp).exp (single n 1)).coeff m = 0 := by
  rw [NumberRaisingOp.coeff_exp]
  exact sum_eq_zero fun k _ => by
    rw [coeff_eq_zero_of_sector_eq (sector_raiseOp_pow c hp k n) m (hm k), smul_zero]

end Lower

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Grouping an absolutely convergent series over multi-indices by the particle number. -/
private theorem hasSum_sum_finsuppAntidiag {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {a : (ι →₀ ℕ) → E} {s : E} (h : HasSum a s) :
    HasSum (fun q : ℕ => ∑ m ∈ finsuppAntidiag univ q, a m) s := by
  refine (h.tsum_fiberwise Finsupp.degree).congr_fun fun q => ?_
  have hset : (Finsupp.degree ⁻¹' {q} : Set (ι →₀ ℕ)) =
      ↑(finsuppAntidiag (univ : Finset ι) q) := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_finsuppAntidiag_univ]
  rw [tsum_congr_set_coe a hset, Finset.tsum_subtype' (finsuppAntidiag univ q) a]

/-- The inner product grouped by sectors: `⟨f, ψ⟩ = Σ_q Σ_{|m| = q} conj(f(m)) ψ(m)`, the outer
series converging absolutely. -/
private theorem hasSum_sector_inner (f ψ : FockSpace ι) :
    HasSum (fun q : ℕ => ∑ m ∈ finsuppAntidiag univ q, conj (f m) * ψ m) ⟪f, ψ⟫_ℂ ∧
      Summable fun q : ℕ => ‖∑ m ∈ finsuppAntidiag univ q, conj (f m) * ψ m‖ := by
  have ha : HasSum (fun m => conj (f m) * ψ m) ⟪f, ψ⟫_ℂ := by
    simpa only [RCLike.inner_apply'] using lp.hasSum_inner (𝕜 := ℂ) f ψ
  have hn : Summable fun m => ‖conj (f m) * ψ m‖ :=
    summable_norm_conj_mul (summable_sq f) (summable_sq ψ)
  refine ⟨hasSum_sum_finsuppAntidiag ha, ?_⟩
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_sum_le _ _)
    (hasSum_sum_finsuppAntidiag hn.hasSum).summable

/-- The general form of Lemma 5: on `ψ ∈ Γ_s`, the series of `e^{Σⱼ c̄ⱼ aⱼ^p} ψ` converges
absolutely at `n`, to `⟨f, ψ⟩` where `f = e^{Σⱼ cⱼ aⱼ†^p} ∣n⟩` is square-summable. -/
private theorem hasSum_coeff_lowerOp (c : ι → ℂ) {p : ℕ} (hp : 1 ≤ p) (n : ι →₀ ℕ)
    {f : FockSpace ι} (hf : toFormal f = (raiseOp c hp).exp (single n 1)) (ψ : FockSpace ι) :
    (Summable fun r : ℕ =>
      ‖((r.factorial : ℂ)⁻¹) * ((lowerOp c p ^ r) (toFormal ψ)).coeff n‖) ∧
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) * ((lowerOp c p ^ r) (toFormal ψ)).coeff n)
      ⟪f, ψ⟫_ℂ := by
  obtain ⟨hS, hN⟩ := hasSum_sector_inner f ψ
  have hfm : ∀ m, f m = ((raiseOp c hp).exp (single n 1)).coeff m := fun m => by
    rw [← hf]
    rfl
  set F : ℕ → ℂ := fun q => ∑ m ∈ finsuppAntidiag univ q, conj (f m) * ψ m
  set g : ℕ → ℕ := fun r => n.degree + p * r
  have hg : Function.Injective g := fun a b h => by
    simp only [g] at h
    exact Nat.eq_of_mul_eq_mul_left hp (by omega)
  have hF0 : ∀ q ∉ Set.range g, F q = 0 := by
    intro q hq
    refine sum_eq_zero fun m hm => ?_
    rw [mem_finsuppAntidiag_univ] at hm
    have : f m = 0 := by
      rw [hfm]
      exact coeff_raiseOp_exp_eq_zero c hp n fun r hr => hq ⟨r, by rw [← hm, hr]⟩
    rw [this, map_zero, zero_mul]
  have hterm : ∀ r : ℕ, ((r.factorial : ℂ)⁻¹) * ((lowerOp c p ^ r) (toFormal ψ)).coeff n =
      F (g r) := by
    intro r
    have hs := coeff_eq_zero_of_sector_eq (sector_raiseOp_pow c hp r n)
    rw [coeff_lowerOp_pow c hp r n, pairing_eq_sum (s := finsuppAntidiag univ (g r)) (fun m hm =>
      by rw [Finset.mem_coe, mem_finsuppAntidiag_univ]; by_contra h; exact hm (hs m h)), mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [mem_finsuppAntidiag_univ] at hm
    rw [hfm, coeff_raiseOp_exp c hp n r hm, map_mul, map_inv₀, map_natCast, coeff_toFormal]
    ring
  have h1 : (fun r : ℕ => ((r.factorial : ℂ)⁻¹) * ((lowerOp c p ^ r) (toFormal ψ)).coeff n) =
      F ∘ g := funext hterm
  have h2 : (fun r : ℕ => ‖((r.factorial : ℂ)⁻¹) * ((lowerOp c p ^ r) (toFormal ψ)).coeff n‖) =
      (fun q => ‖F q‖) ∘ g := funext fun r => congrArg norm (hterm r)
  rw [h1, h2]
  exact ⟨(hg.summable_iff fun q hq => by rw [hF0 q hq, norm_zero]).2 hN,
    (hg.hasSum_iff hF0).2 hS⟩

end FockSpace

/-! #### Square-summability of `e^{Σⱼ cⱼ aⱼ†^p} ∣n⟩` -/

namespace FormalFock

variable {ι : Type*}

/-- A formal vector lies in `Γ_s` exactly when its coefficients are square-summable, that is, when
its squared norm is finite. -/
theorem memℓp_coeff_iff_sqNorm_lt_top (ψ : FormalFock ι ℂ) :
    Memℓp ψ.coeff 2 ↔ sqNorm ψ < ∞ := by
  rw [sqNorm_lt_top_iff, memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp

/-- The coefficients of `e^{κ a†² + ℓ a†} ∣m⟩`: `√(k!/m!) C_{k-m}(κ, ℓ)` at `∣k⟩` for `k ≥ m`, and
`0` below `m`. -/
theorem coeff_gaussExp_numberState (κ ℓ : ℂ) (m k : ℕ) :
    (gaussExp κ ℓ (numberState m)).coeff (Finsupp.single () k) =
      if m ≤ k then sqrtC k.factorial * cMatrix κ ℓ (k - m) / sqrtC m.factorial else 0 := by
  have hB := bargmann_gaussExp κ ℓ (numberState m)
  have hv : bargmann (numberState m) =
      MvPowerSeries.monomial (Finsupp.single () m) ((sqrtC m.factorial)⁻¹) := by
    rw [bargmann_apply, numberState, toBargmann_single, mul_one, sqrtFactorial, factorial_single]
  have hG : ∀ j : ℕ, MvPowerSeries.coeff (Finsupp.single () j) (bargmann (gaussVec κ ℓ)) =
      cMatrix κ ℓ j := fun j => by
    rw [bargmann_apply, coeff_toBargmann, coeff_gaussVec, sqrtFactorial, factorial_single,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (sqrtC_ne_zero (Nat.factorial_pos j)), one_mul]
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single () k)) hB
  rw [hv, MvPowerSeries.coeff_mul_monomial, bargmann_apply, coeff_toBargmann, sqrtFactorial,
    factorial_single, smul_eq_mul] at hc
  have h0 := sqrtC_ne_zero (Nat.factorial_pos k)
  simp only [Finsupp.single_le_single] at hc
  split_ifs at hc ⊢ with h1
  · rw [← Finsupp.single_tsub, hG] at hc
    calc (gaussExp κ ℓ (numberState m)).coeff (Finsupp.single () k)
        = sqrtC k.factorial * ((sqrtC k.factorial)⁻¹ *
          (gaussExp κ ℓ (numberState m)).coeff (Finsupp.single () k)) := by field_simp
      _ = _ := by rw [hc]; ring
  · rwa [mul_eq_zero, or_iff_right (inv_ne_zero h0)] at hc

/-- `Cⱼ(s² κ, s ℓ) = sʲ Cⱼ(κ, ℓ)`, the case `R = ℂ` of `BosonicLean.cMatrix_smul_sq_smul`. -/
@[deprecated BosonicLean.cMatrix_smul_sq_smul +typeChanged (since := "2026-10-30")]
theorem cMatrix_mul_sq_mul (s κ ℓ : ℂ) (j : ℕ) :
    cMatrix (s ^ 2 * κ) (s * ℓ) j = s ^ j * cMatrix κ ℓ j := by
  simpa only [smul_eq_mul] using cMatrix_smul_sq_smul s κ ℓ j

/-- **Square-summability of `e^{κ a†² + ℓ a†} ∣m⟩` for `|κ| < 1/2`.** -/
private theorem sqNorm_gaussExp_numberState_lt_top {κ : ℂ} (hκ : ‖κ‖ < 1 / 2) (ℓ : ℂ) (m : ℕ) :
    sqNorm (gaussExp κ ℓ (numberState m)) < ∞ := by
  rw [sqNorm_lt_top_iff, ← (Finsupp.uniqueEquiv ()).symm.summable_iff]
  set b : ℕ → ℝ := fun k => ‖(gaussExp κ ℓ (numberState m)).coeff (Finsupp.single () k)‖ ^ 2
  change Summable b
  rw [← summable_nat_add_iff m]
  -- the scaled parameters `κ' = κ/ρ`, `ℓ' = ℓ/√ρ` with `ρ = (1 + 2|κ|)/2 < 1`
  set ρ : ℝ := (1 + 2 * ‖κ‖) / 2
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  set s : ℂ := (Real.sqrt ρ : ℂ)
  have hs0 : s ≠ 0 := by simp [s, Real.sqrt_eq_zero', hρ0.not_ge]
  have hs2 : s ^ 2 = (ρ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hρ0.le]
  set κ' : ℂ := κ / s ^ 2
  set ℓ' : ℂ := ℓ / s
  have hκ' : ‖κ'‖ < 1 / 2 := by
    rw [norm_div, hs2, Complex.norm_real, Real.norm_of_nonneg hρ0.le, div_lt_iff₀ hρ0]
    simp only [ρ]
    linarith
  have hscale : ∀ j, ‖cMatrix κ ℓ j‖ ^ 2 = ρ ^ j * ‖cMatrix κ' ℓ' j‖ ^ 2 := fun j => by
    have h : cMatrix (s ^ 2 * κ') (s * ℓ') j = s ^ j * cMatrix κ' ℓ' j := by
      simpa only [smul_eq_mul] using cMatrix_smul_sq_smul s κ' ℓ' j
    have e1 : s ^ 2 * κ' = κ := by
      rw [show κ' = κ / s ^ 2 from rfl]
      field_simp
    have e2 : s * ℓ' = ℓ := by
      rw [show ℓ' = ℓ / s from rfl]
      field_simp
    have e3 : ‖s‖ = Real.sqrt ρ := by
      rw [show s = (Real.sqrt ρ : ℂ) from rfl, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [e1, e2] at h
    rw [h, norm_mul, norm_pow, mul_pow, ← pow_mul, e3, mul_comm j 2, pow_mul,
      Real.sq_sqrt hρ0.le]
  -- `(j + m)^m ρ^j` is bounded
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ j : ℕ, ((j + m : ℕ) : ℝ) ^ m * ρ ^ j ≤ B := by
    have hsum := summable_pow_mul_geometric_of_norm_lt_one m
      (by rw [Real.norm_of_nonneg hρ0.le]; exact hρ1)
    refine ⟨(ρ ^ m)⁻¹ * ∑' N : ℕ, (N : ℝ) ^ m * ρ ^ N, fun j => ?_⟩
    have hle := hsum.le_tsum (j + m) fun N _ => by positivity
    rw [le_inv_mul_iff₀ (pow_pos hρ0 m)]
    calc ρ ^ m * (((j + m : ℕ) : ℝ) ^ m * ρ ^ j) = ((j + m : ℕ) : ℝ) ^ m * ρ ^ (j + m) := by
          rw [pow_add]; ring
      _ ≤ _ := hle
  have hM := (hasSum_factorial_mul_normSq_cMatrix κ' ℓ' hκ').summable
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) (hM.mul_left B)
  simp only [b]
  rw [coeff_gaussExp_numberState, ite_eq_left (by omega), Nat.add_sub_cancel]
  rw [norm_div, norm_mul, div_pow, mul_pow]
  have hsq : ∀ k : ℕ, ‖sqrtC k.factorial‖ ^ 2 = (k.factorial : ℝ) := fun k => by
    rw [sqrtC, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq, hsq, hscale, Complex.normSq_eq_norm_sq]
  -- `(j + m)!/m! ≤ j! (j + m)^m`
  have hfac : ((j + m).factorial : ℝ) / m.factorial ≤ j.factorial * ((j + m : ℕ) : ℝ) ^ m := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (j + m).factorial = j.factorial * (j + 1).ascFactorial m :=
      (Nat.factorial_mul_ascFactorial j m).symm
    have h2 := Nat.ascFactorial_le_pow_add j m
    have h3 : (1 : ℝ) ≤ m.factorial := Nat.one_le_cast.2 (Nat.factorial_pos m)
    rw [h1, Nat.cast_mul]
    calc (j.factorial : ℝ) * ((j + 1).ascFactorial m : ℝ)
        ≤ j.factorial * ((j + m : ℕ) : ℝ) ^ m := by
          gcongr
          exact_mod_cast h2
      _ ≤ j.factorial * ((j + m : ℕ) : ℝ) ^ m * m.factorial := le_mul_of_one_le_right
          (by positivity) h3
  calc ((j + m).factorial : ℝ) * (ρ ^ j * ‖cMatrix κ' ℓ' j‖ ^ 2) / m.factorial
      = (j + m).factorial / (m.factorial : ℝ) * (ρ ^ j * ‖cMatrix κ' ℓ' j‖ ^ 2) := by ring
    _ ≤ j.factorial * ((j + m : ℕ) : ℝ) ^ m * (ρ ^ j * ‖cMatrix κ' ℓ' j‖ ^ 2) := by
        gcongr
    _ = (((j + m : ℕ) : ℝ) ^ m * ρ ^ j) * (j.factorial * ‖cMatrix κ' ℓ' j‖ ^ 2) := by ring
    _ ≤ B * (j.factorial * ‖cMatrix κ' ℓ' j‖ ^ 2) := by
        gcongr
        exact hB j

end FormalFock

/-! #### The lowering exponentials of the displacement and squeezing operators -/

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `-ᾱ·a = -Σⱼ ᾱⱼ aⱼ`, which lowers the particle number. -/
noncomputable def lowerDisp (α : ι → ℂ) : Module.End ℂ (FormalFock ι ℂ) :=
  -∑ j, conj (α j) • annihilate j

/-- `½ Σⱼ τ̄ⱼ aⱼ²`, which lowers the particle number. -/
noncomputable def lowerSqueeze (τ : ι → ℂ) : Module.End ℂ (FormalFock ι ℂ) :=
  ∑ j, (conj (τ j) / 2) • annihilate j ^ 2

/-- `-½ Σⱼ τⱼ aⱼ†²`, which raises the particle number. -/
noncomputable def raiseSqueeze (τ : ι → ℂ) : NumberRaisingOp ι ℂ :=
  gaussRaise (fun j => -τ j / 2) 0

omit [DecidableEq ι] in
/-- `-½ Σⱼ τⱼ aⱼ†²` as an operator. -/
theorem raiseSqueeze_op (τ : ι → ℂ) :
    (raiseSqueeze τ).op = ∑ j, (-τ j / 2) • create j ^ 2 := by
  simp [raiseSqueeze, gaussRaise_op]

omit [DecidableEq ι] in
private theorem lowerDisp_eq_lowerOp (α : ι → ℂ) : lowerDisp α = lowerOp (-α) 1 := by
  simp [lowerDisp, lowerOp, ← sum_neg_distrib, neg_smul]

omit [DecidableEq ι] in
private theorem lowerSqueeze_eq_lowerOp (τ : ι → ℂ) :
    lowerSqueeze τ = lowerOp (fun j => τ j / 2) 2 := by
  simp [lowerSqueeze, lowerOp, map_div₀, map_ofNat]

omit [DecidableEq ι] in
private theorem raiseDisp_exp_eq (α : ι → ℂ) : (raiseDisp α).exp = (raiseOp α le_rfl).exp :=
  NumberRaisingOp.exp_congr (by rw [raiseDisp_op, raiseOp_op]; simp)

omit [DecidableEq ι] in
private theorem raiseSqueeze_neg_exp_eq (τ : ι → ℂ) :
    (raiseSqueeze (-τ)).exp = (raiseOp (fun j => τ j / 2) (by norm_num : 1 ≤ 2)).exp :=
  NumberRaisingOp.exp_congr (by rw [raiseSqueeze_op, raiseOp_op]; simp)

/-- A number state is a product of one-mode number states. -/
private theorem single_one_eq_tensorVec (n : ι →₀ ℕ) :
    single n (1 : ℂ) = tensorVec fun j => numberState (n j) := by
  rw [tensorVec_numberState, Finsupp.equivFunOnFinite_symm_coe]

/-- `e^{-ᾱ·a†}` and its relatives on a number state: `e^{Σⱼ ℓⱼ aⱼ†} ∣n⟩ = ⊗ⱼ e^{ℓⱼ a†} ∣nⱼ⟩`. -/
theorem raiseDisp_exp_single (α : ι → ℂ) (n : ι →₀ ℕ) :
    (raiseDisp α).exp (single n 1) = tensorVec fun j => gaussExp 0 (α j) (numberState (n j)) := by
  rw [raiseDisp, single_one_eq_tensorVec, gaussRaise_exp_tensorVec]
  rfl

/-- `e^{-½ Σⱼ τⱼ aⱼ†²} ∣n⟩ = ⊗ⱼ e^{-τⱼ a†²/2} ∣nⱼ⟩`. -/
theorem raiseSqueeze_exp_single (τ : ι → ℂ) (n : ι →₀ ℕ) :
    (raiseSqueeze τ).exp (single n 1) =
      tensorVec fun j => gaussExp (-τ j / 2) 0 (numberState (n j)) := by
  rw [raiseSqueeze, single_one_eq_tensorVec, gaussRaise_exp_tensorVec]
  rfl

/-- `e^{α·a†} ∣n⟩` is square-summable. -/
theorem sqNorm_raiseDisp_exp_lt_top (α : ι → ℂ) (n : ι →₀ ℕ) :
    sqNorm ((raiseDisp α).exp (single n 1)) < ∞ := by
  rw [raiseDisp_exp_single]
  exact sqNorm_tensorVec_lt_top fun j =>
    sqNorm_gaussExp_numberState_lt_top (by norm_num) (α j) (n j)

/-- For `|τⱼ| < 1`, `e^{-½ Σⱼ τⱼ aⱼ†²} ∣n⟩` is square-summable. -/
theorem sqNorm_raiseSqueeze_exp_lt_top {τ : ι → ℂ} (hτ : ∀ j, ‖τ j‖ < 1) (n : ι →₀ ℕ) :
    sqNorm ((raiseSqueeze τ).exp (single n 1)) < ∞ := by
  rw [raiseSqueeze_exp_single]
  refine sqNorm_tensorVec_lt_top fun j => sqNorm_gaussExp_numberState_lt_top ?_ 0 (n j)
  rw [norm_div, norm_neg, Complex.norm_ofNat]
  linarith [hτ j]

/-- **Lemma 5(b), sharpness.** For `|τ| ≥ 1`, `e^{τ a†²/2} ∣0⟩` is not square-summable. -/
theorem sqNorm_gaussVec_eq_top {κ : ℂ} (hκ : 1 / 2 ≤ ‖κ‖) : sqNorm (gaussVec κ 0) = ∞ := by
  by_contra hne
  have hs := (sqNorm_lt_top_iff _).1 (lt_top_iff_ne_top.2 hne)
  have hs2 : Summable fun k : ℕ => ‖(gaussVec κ 0).coeff (Finsupp.single () (2 * k))‖ ^ 2 :=
    hs.comp_injective fun a b h => by
      have := congrArg (fun f : Unit →₀ ℕ => f ()) h
      simp only [Finsupp.single_eq_same] at this
      omega
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 ?_)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hs2.comp_injective (add_left_injective 1)).mul_left 2)
  simp only [Function.comp_apply]
  set N := k + 1
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  -- `‖g(κ, 0)(2N)‖² = C(2N, N) |κ|^{2N}`
  have hcb : (N.centralBinom : ℝ) * (N.factorial : ℝ) ^ 2 = ((2 * N).factorial : ℝ) := by
    rw [Nat.centralBinom_eq_two_mul_choose, sq, ← mul_assoc]
    have := Nat.choose_mul_factorial_mul_factorial (by omega : N ≤ 2 * N)
    rw [show 2 * N - N = N by omega] at this
    exact_mod_cast this
  have key : ‖(gaussVec κ 0).coeff (Finsupp.single () (2 * N))‖ ^ 2 =
      N.centralBinom * ‖κ‖ ^ (2 * N) := by
    rw [coeff_gaussVec, cMatrix_zero_right_even, smul_eq_mul, norm_mul, norm_mul, norm_inv,
      norm_pow, Complex.norm_natCast, mul_pow, mul_pow, sqrtC, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), ← hcb, ← pow_mul,
      mul_comm N 2]
    have hf : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [key]
  have h4 : (4 : ℝ) ^ N ≤ 2 * N * N.centralBinom := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom N (Nat.succ_pos k)
  have hκ2 : (1 / 4 : ℝ) ^ N ≤ ‖κ‖ ^ (2 * N) := by
    rw [pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_mul,
      mul_comm 2 N]
    exact pow_le_pow_left₀ (by norm_num) hκ _
  calc 1 / (N : ℝ) = (4 ^ N * (1 / 4) ^ N) / N := by rw [← mul_pow]; norm_num
    _ ≤ (2 * N * N.centralBinom * ‖κ‖ ^ (2 * N)) / N := by gcongr
    _ = 2 * (N.centralBinom * ‖κ‖ ^ (2 * N)) := by field_simp

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Lemma 5(a).** For `ψ ∈ Γ_s`, the series of `e^{-ᾱ·a} ψ` converges absolutely at every
coefficient. -/
theorem summable_coeffExp_lowerDisp (α : ι → ℂ) (ψ : FockSpace ι) (n : ι →₀ ℕ) :
    Summable fun r : ℕ =>
      ‖((r.factorial : ℂ)⁻¹) * ((lowerDisp α ^ r) (toFormal ψ)).coeff n‖ := by
  classical
  obtain ⟨f, hf⟩ := (mem_range_toFormal_iff _).2 (sqNorm_raiseDisp_exp_lt_top (-α) n)
  rw [raiseDisp_exp_eq] at hf
  simpa only [lowerDisp_eq_lowerOp] using (hasSum_coeff_lowerOp (-α) le_rfl n hf ψ).1

/-- **Lemma 5(a).** The coefficient of `e^{-ᾱ·a} ψ` at `n` is `⟨fₙ, ψ⟩` with
`fₙ = e^{-α·a†} ∣n⟩ ∈ Γ_s`. -/
theorem coeff_coeffExp_lowerDisp (α : ι → ℂ) (n : ι →₀ ℕ) :
    ∃ χ : FockSpace ι, toFormal χ = (raiseDisp (-α)).exp (single n 1) ∧
      ∀ ψ : FockSpace ι, (coeffExp (lowerDisp α) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ := by
  obtain ⟨f, hf⟩ := (mem_range_toFormal_iff _).2 (sqNorm_raiseDisp_exp_lt_top (-α) n)
  refine ⟨f, hf, fun ψ => ?_⟩
  rw [raiseDisp_exp_eq] at hf
  rw [coeff_coeffExp, lowerDisp_eq_lowerOp]
  exact (hasSum_coeff_lowerOp (-α) le_rfl n hf ψ).2.tsum_eq

omit [DecidableEq ι] in
/-- **Lemma 5(b).** For `|τⱼ| < 1`, the series of `e^{½ Σⱼ τ̄ⱼ aⱼ²} ψ` converges absolutely at
every coefficient. -/
theorem summable_coeffExp_lowerSqueeze {τ : ι → ℂ} (hτ : ∀ j, ‖τ j‖ < 1) (ψ : FockSpace ι)
    (n : ι →₀ ℕ) :
    Summable fun r : ℕ =>
      ‖((r.factorial : ℂ)⁻¹) * ((lowerSqueeze τ ^ r) (toFormal ψ)).coeff n‖ := by
  classical
  obtain ⟨f, hf⟩ := (mem_range_toFormal_iff _).2
    (sqNorm_raiseSqueeze_exp_lt_top (τ := -τ) (by simpa using hτ) n)
  rw [raiseSqueeze_neg_exp_eq] at hf
  simpa only [lowerSqueeze_eq_lowerOp] using (hasSum_coeff_lowerOp _ _ n hf ψ).1

/-- **Lemma 5(b).** For `|τⱼ| < 1`, the coefficient of `e^{½ Σⱼ τ̄ⱼ aⱼ²} ψ` at `n` is `⟨fₙ, ψ⟩`
with `fₙ = e^{½ Σⱼ τⱼ aⱼ†²} ∣n⟩ ∈ Γ_s`. -/
theorem coeff_coeffExp_lowerSqueeze {τ : ι → ℂ} (hτ : ∀ j, ‖τ j‖ < 1) (n : ι →₀ ℕ) :
    ∃ χ : FockSpace ι, toFormal χ = (raiseSqueeze (-τ)).exp (single n 1) ∧
      ∀ ψ : FockSpace ι, (coeffExp (lowerSqueeze τ) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ := by
  obtain ⟨f, hf⟩ := (mem_range_toFormal_iff _).2
    (sqNorm_raiseSqueeze_exp_lt_top (τ := -τ) (by simpa using hτ) n)
  refine ⟨f, hf, fun ψ => ?_⟩
  rw [raiseSqueeze_neg_exp_eq] at hf
  rw [coeff_coeffExp, lowerSqueeze_eq_lowerOp]
  exact (hasSum_coeff_lowerOp _ _ n hf ψ).2.tsum_eq

/-- **Lemma 5(b), sharpness.** If `|τⱼ| ≥ 1` for some `j`, then `e^{½ Σⱼ τⱼ aⱼ†²} ∣0⟩` is not
square-summable. -/
theorem not_memℓp_raiseSqueeze {τ : ι → ℂ} (hτ : ∃ j, 1 ≤ ‖τ j‖) :
    ¬ Memℓp ((raiseSqueeze (-τ)).exp (single 0 1)).coeff 2 := by
  obtain ⟨j, hj⟩ := hτ
  rw [memℓp_coeff_iff_sqNorm_lt_top, raiseSqueeze_exp_single, sqNorm_tensorVec, not_lt,
    top_le_iff]
  refine WithTop.prod_eq_top (mem_univ j) ?_ fun i _ => ?_
  · simp only [Finsupp.coe_zero, Pi.zero_apply, Pi.neg_apply, neg_neg, gaussExp_vacuum]
    refine sqNorm_gaussVec_eq_top ?_
    rw [norm_div, Complex.norm_ofNat]
    linarith
  · simp only [Finsupp.coe_zero, Pi.zero_apply, gaussExp_vacuum]
    intro h0
    have := congrArg (fun φ : FormalFock Unit ℂ => φ.coeff 0) ((sqNorm_eq_zero_iff _).1 h0)
    simp only [coeff_zero] at this
    rw [← Finsupp.single_zero (), coeff_gaussVec, cMatrix_zero] at this
    simp [sqrtC] at this

omit [DecidableEq ι] in
/-- **Lemma 5(c).** `ψ ↦ (e^{-ᾱ·a} ψ)(n)` is a continuous linear functional on `Γ_s`. -/
theorem continuous_coeff_coeffExp_lowerDisp (α : ι → ℂ) (n : ι →₀ ℕ) :
    Continuous fun ψ : FockSpace ι => (coeffExp (lowerDisp α) (toFormal ψ)).coeff n := by
  classical
  obtain ⟨χ, -, hχ⟩ := coeff_coeffExp_lowerDisp α n
  simp_rw [hχ]
  exact continuous_const.inner continuous_id

omit [DecidableEq ι] in
/-- **Lemma 5(c).** For `|τⱼ| < 1`, `ψ ↦ (e^{½ Σⱼ τ̄ⱼ aⱼ²} ψ)(n)` is a continuous linear
functional on `Γ_s`. -/
theorem continuous_coeff_coeffExp_lowerSqueeze {τ : ι → ℂ} (hτ : ∀ j, ‖τ j‖ < 1)
    (n : ι →₀ ℕ) :
    Continuous fun ψ : FockSpace ι => (coeffExp (lowerSqueeze τ) (toFormal ψ)).coeff n := by
  classical
  obtain ⟨χ, -, hχ⟩ := coeff_coeffExp_lowerSqueeze hτ n
  simp_rw [hχ]
  exact continuous_const.inner continuous_id

end FockSpace

/-! ### Lemma 6: isometric extension from the exponential vectors -/

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Lemma 6(b).** Two linear maps `Γ_s → 𝓕` with continuous coefficients that agree on the
exponential vectors agree. -/
theorem eq_of_eqOn_expVec (T T' : FockSpace ι →ₗ[ℂ] FormalFock ι ℂ)
    (hT : ∀ n, Continuous fun ψ => (T ψ).coeff n) (hT' : ∀ n, Continuous fun ψ => (T' ψ).coeff n)
    (h : ∀ z, T (expVec z) = T' (expVec z)) : T = T' := by
  classical
  refine LinearMap.ext fun ψ => ?_
  ext n
  have hEq : Set.EqOn (fun ψ => (T ψ).coeff n) (fun ψ => (T' ψ).coeff n)
      (Submodule.span ℂ (Set.range (expVec (ι := ι)))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp only [h z]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, coeff_add] at hx hy ⊢; rw [hx, hy]
    | smul c x _ hx => simp only [map_smul, coeff_smul] at hx ⊢; rw [hx]
  exact congrFun (Continuous.ext_on dense_span_expVec (hT n) (hT' n) hEq) ψ

omit [DecidableEq ι] in
/-- **Lemma 6(a).** A linear map `T : Γ_s → 𝓕` with continuous coefficients that maps the
exponential vectors to vectors of `Γ_s` with their inner products maps `Γ_s` isometrically into
`Γ_s`: the extension of a Gram-preserving map (`exists_unique_linearIsometry_of_inner_eq`)
followed by Lemma 6(b). -/
theorem exists_linearIsometry_of_expVec (T : FockSpace ι →ₗ[ℂ] FormalFock ι ℂ)
    (hT : ∀ n, Continuous fun ψ => (T ψ).coeff n) (V : (ι → ℂ) → FockSpace ι)
    (hV : ∀ z, T (expVec z) = toFormal (V z))
    (hVV : ∀ w z, ⟪V w, V z⟫_ℂ = ⟪expVec w, expVec z⟫_ℂ) :
    ∃ L : FockSpace ι →ₗᵢ[ℂ] FockSpace ι, ∀ ψ, toFormal (L ψ) = T ψ := by
  obtain ⟨L, hL, -⟩ := exists_unique_linearIsometry_of_inner_eq (expVec (ι := ι)) V
    (fun w z => (hVV w z).symm) dense_span_expVec
  refine ⟨L, fun ψ => LinearMap.congr_fun (eq_of_eqOn_expVec (toFormal ∘ₗ L.toLinearMap) T
    (fun n => (lp.lipschitzWith_one_eval 2 n).continuous.comp L.continuous) hT
    fun z => ?_) ψ⟩
  rw [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, hL, hV]

end FockSpace

/-! ### Linear maps built from lowering exponentials -/

namespace FormalFock

/-- The coefficientwise exponential is homogeneous: `e^T (c ψ) = c e^T ψ`. -/
theorem coeffExp_smul {ι : Type*} (T : Module.End ℂ (FormalFock ι ℂ)) (c : ℂ)
    (ψ : FormalFock ι ℂ) : coeffExp T (c • ψ) = c • coeffExp T ψ := by
  ext n
  rw [coeff_smul, coeff_coeffExp, coeff_coeffExp, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  rw [map_smul, coeff_smul, smul_eq_mul]
  ring

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- If every coefficient of `e^T ψ` is an inner product `⟨χₙ, ψ⟩`, then `ψ ↦ e^T ψ` is additive
on `Γ_s`. -/
theorem coeffExp_toFormal_add {T : Module.End ℂ (FormalFock ι ℂ)}
    (hT : ∀ n, ∃ χ : FockSpace ι, ∀ ψ : FockSpace ι, (coeffExp T (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ)
    (ψ φ : FockSpace ι) :
    coeffExp T (toFormal (ψ + φ)) = coeffExp T (toFormal ψ) + coeffExp T (toFormal φ) := by
  classical
  ext n
  obtain ⟨χ, hχ⟩ := hT n
  rw [coeff_add, hχ, hχ, hχ, inner_add_right]

omit [DecidableEq ι] in
/-- Two continuous linear maps out of `Γ_s` that agree on the exponential vectors are equal
(Theorem 4). -/
theorem ext_expVec {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommGroup E] [Module ℂ E]
    {f g : FockSpace ι →L[ℂ] E} (h : ∀ z, f (expVec z) = g (expVec z)) : f = g :=
  ContinuousLinearMap.ext_on dense_span_expVec fun _ ⟨z, hz⟩ => hz ▸ h z

omit [DecidableEq ι] in
/-- Theorem 4 in inner-product form: two vectors with the same inner products with every
exponential vector are equal. -/
theorem ext_inner_expVec {x y : FockSpace ι} (h : ∀ w, ⟪expVec w, x⟫_ℂ = ⟪expVec w, y⟫_ℂ) :
    x = y := by
  have hxy := ext_expVec (f := innerSL ℂ x) (g := innerSL ℂ y) fun z => by
    rw [innerSL_apply_apply, innerSL_apply_apply, ← inner_conj_symm, h, inner_conj_symm]
  exact ext_inner_right ℂ fun v => by
    simpa only [innerSL_apply_apply] using congrArg (fun f => f v) hxy

end FockSpace

/-! ### Derivatives of raising exponentials

On vectors with at most `e` particles the creation operator `aⱼ†` is bounded by `√(e + 1)` for the
ℓ¹ norm `Σₙ |ψ(n)|`, which majorizes the norm of `Γ_s`. Summing the exponential series with these
bounds gives the derivative at `t = 0` of `t ↦ e^{Σⱼ (κⱼ(t) aⱼ†² + ℓⱼ(t) aⱼ†)} ∣m⟩` in `Γ_s`,
used for the derivatives of Theorems 10(c) and 17(c). -/

namespace FormalFock

open scoped NNReal

variable {ι : Type*}

/-- `ψ` has no component with more than `e` particles. -/
def VanishesAbove (e : ℕ) (ψ : FormalFock ι ℂ) : Prop :=
  ∀ n : ι →₀ ℕ, e < n.degree → ψ.coeff n = 0

/-- A particle bound can be raised. -/
theorem VanishesAbove.mono {e e' : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ)
    (he : e ≤ e') : VanishesAbove e' ψ :=
  fun n hn => h n (by omega)

/-- A particle bound is preserved by addition. -/
theorem VanishesAbove.add {e : ℕ} {ψ φ : FormalFock ι ℂ} (hψ : VanishesAbove e ψ)
    (hφ : VanishesAbove e φ) : VanishesAbove e (ψ + φ) :=
  fun n hn => by rw [coeff_add, hψ n hn, hφ n hn, add_zero]

/-- A particle bound is preserved by scalar multiples. -/
theorem VanishesAbove.smul {e : ℕ} {ψ : FormalFock ι ℂ} (hψ : VanishesAbove e ψ) (c : ℂ) :
    VanishesAbove e (c • ψ) :=
  fun n hn => by rw [coeff_smul, hψ n hn, smul_zero]

/-- A particle bound is preserved by finite sums. -/
theorem vanishesAbove_sum {κ : Type*} {e : ℕ} (s : Finset κ) {ψ : κ → FormalFock ι ℂ}
    (h : ∀ i ∈ s, VanishesAbove e (ψ i)) : VanishesAbove e (∑ i ∈ s, ψ i) := by
  intro n hn
  rw [coeff_sum]
  exact sum_eq_zero fun i hi => h i hi n hn

/-- The number state `c∣m⟩` has at most `|m|` particles. -/
theorem vanishesAbove_single [DecidableEq ι] (m : ι →₀ ℕ) (c : ℂ) :
    VanishesAbove m.degree (single m c) := fun n hn => by
  rw [coeff_single, ite_eq_right]
  rintro rfl
  omega

/-- `aⱼ†` raises a particle bound by one. -/
theorem VanishesAbove.create {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) (j : ι) : VanishesAbove (e + 1) (create j ψ) := by
  classical
  intro n hn
  rw [coeff_create]
  split_ifs with hj
  · rw [h _ (by have := degree_sub_single_add_one hj; omega), smul_zero]
  · rfl

/-- A vector with at most `e` particles is finitely supported. -/
theorem VanishesAbove.finite_support [Finite ι] {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) : (Function.support ψ.coeff).Finite := by
  have := Fintype.ofFinite ι
  classical
  refine ((range (e + 1)).biUnion fun d => finsuppAntidiag (univ : Finset ι) d).finite_toSet.subset
    fun m hm => ?_
  rw [Finset.mem_coe, mem_biUnion]
  refine ⟨m.degree, mem_range.2 ?_, mem_finsuppAntidiag_univ.2 rfl⟩
  by_contra hle
  exact hm (h m (by omega))

/-- `Γ(g)` preserves particle bounds. -/
theorem VanishesAbove.secondQuant [Fintype ι] {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) (g : Matrix ι ι ℂ) : VanishesAbove e (secondQuant g ψ) :=
  fun m hm => by
  classical
  rw [coeff_secondQuant]
  refine sum_eq_zero fun k hk => ?_
  rw [h k (by rw [mem_finsuppAntidiag] at hk; rw [Finsupp.degree_eq_sum, hk.1]; exact hm),
    mul_zero]

/-- The ℓ¹ norm `Σₙ |ψ(n)|` of a formal vector, in `[0, ∞]`. -/
private noncomputable def l1Norm (ψ : FormalFock ι ℂ) : ℝ≥0∞ :=
  ∑' n, (‖ψ.coeff n‖₊ : ℝ≥0∞)

/-- The triangle inequality for the ℓ¹ norm. -/
private theorem l1Norm_add_le (ψ φ : FormalFock ι ℂ) : l1Norm (ψ + φ) ≤ l1Norm ψ + l1Norm φ := by
  rw [l1Norm, l1Norm, l1Norm, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [coeff_add, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact nnnorm_add_le _ _

/-- The ℓ¹ norm is absolutely homogeneous. -/
private theorem l1Norm_smul (c : ℂ) (ψ : FormalFock ι ℂ) : l1Norm (c • ψ) = ‖c‖₊ * l1Norm ψ := by
  rw [l1Norm, l1Norm, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [coeff_smul, nnnorm_smul, ENNReal.coe_mul]

/-- The ℓ¹ norm of `0` is `0`. -/
private theorem l1Norm_zero : l1Norm (0 : FormalFock ι ℂ) = 0 := by
  simp [l1Norm, coeff_zero]

/-- The triangle inequality for finite sums in the ℓ¹ norm. -/
private theorem l1Norm_sum_le {κ : Type*} (s : Finset κ) (ψ : κ → FormalFock ι ℂ) :
    l1Norm (∑ i ∈ s, ψ i) ≤ ∑ i ∈ s, l1Norm (ψ i) :=
  Finset.le_sum_of_subadditive l1Norm l1Norm_zero.le l1Norm_add_le s ψ

/-- The ℓ¹ norm of `c∣m⟩` is `|c|`. -/
private theorem l1Norm_single [DecidableEq ι] (m : ι →₀ ℕ) (c : ℂ) :
    l1Norm (single m c) = ‖c‖₊ := by
  rw [l1Norm, tsum_eq_single m fun n hn => by simp [coeff_single, hn]]
  simp [coeff_single]

/-- The ℓ¹ norm majorizes the norm: `Σₙ |ψ(n)|² ≤ (Σₙ |ψ(n)|)²`. -/
private theorem sqNorm_le_l1Norm_sq (ψ : FormalFock ι ℂ) : sqNorm ψ ≤ l1Norm ψ ^ 2 := by
  rw [sqNorm, l1Norm, sq, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [sq]
  exact mul_le_mul_right (ENNReal.le_tsum (f := fun n => (‖ψ.coeff n‖₊ : ℝ≥0∞)) n) _

/-- `|√k| = √k` for the complex square root of a natural number. -/
private theorem nnnorm_sqrtC (k : ℕ) : ‖sqrtC k‖₊ = NNReal.sqrt k := by
  ext
  rw [coe_nnnorm, sqrtC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.coe_sqrt, NNReal.coe_natCast]

/-- On vectors with at most `e` particles, `‖aⱼ† ψ‖₁ ≤ √(e + 1) ‖ψ‖₁`. -/
private theorem l1Norm_create_le {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ)
    (j : ι) : l1Norm (create j ψ) ≤ (NNReal.sqrt (e + 1) : ℝ≥0∞) * l1Norm ψ := by
  classical
  have hinj : Function.Injective fun m : ι →₀ ℕ => m + Finsupp.single j 1 :=
    fun a b hab => add_right_cancel hab
  have hsupp : Function.support (fun n => (‖(create j ψ).coeff n‖₊ : ℝ≥0∞)) ⊆
      Set.range fun m : ι →₀ ℕ => m + Finsupp.single j 1 := by
    intro n hn
    have h0 : 0 < n j := by
      by_contra h0
      exact hn (by simp [coeff_create, h0])
    refine ⟨n - Finsupp.single j 1, ?_⟩
    ext k
    by_cases hk : k = j
    · subst hk
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same]
      omega
    · simp [Ne.symm hk]
  rw [l1Norm, ← hinj.tsum_eq hsupp, l1Norm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [coeff_create, ite_eq_left (by simp), add_tsub_cancel_right, nnnorm_smul, ENNReal.coe_mul,
    nnnorm_sqrtC]
  by_cases hm : ψ.coeff m = 0
  · simp [hm]
  · refine mul_le_mul_left (ENNReal.coe_le_coe.2 (NNReal.sqrt_le_sqrt.2 ?_)) _
    have hdeg : m.degree ≤ e := not_lt.1 fun hlt => hm (h m hlt)
    have := Finsupp.le_degree j m
    have hle : (m + Finsupp.single j 1 : ι →₀ ℕ) j ≤ e + 1 := by
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    exact_mod_cast hle

/-- `‖aⱼ† ψ‖₁ ≤ (e + 1) ‖ψ‖₁` on vectors with at most `e` particles. -/
private theorem l1Norm_create_le' {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ)
    (j : ι) : l1Norm (create j ψ) ≤ ((e : ℝ≥0∞) + 1) * l1Norm ψ := by
  classical
  refine (l1Norm_create_le h j).trans (mul_le_mul_left ?_ _)
  have : NNReal.sqrt (e + 1) ≤ (e : ℝ≥0) + 1 := by
    rw [NNReal.sqrt_le_iff_le_sq]
    have h1 : (1 : ℝ≥0) ≤ e + 1 := le_add_of_nonneg_left ((zero_le : (0 : ℝ≥0) ≤ e))
    calc (e : ℝ≥0) + 1 = (e + 1) * 1 := (mul_one _).symm
      _ ≤ (e + 1) * (e + 1) := mul_le_mul_right h1 _
      _ = (e + 1) ^ 2 := (sq _).symm
  exact_mod_cast this

/-- `‖aⱼ†² ψ‖₁ ≤ 2 (e + 1) ‖ψ‖₁` on vectors with at most `e` particles. -/
private theorem l1Norm_create_sq_le {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ)
    (j : ι) : l1Norm ((create j ^ 2) ψ) ≤ 2 * ((e : ℝ≥0∞) + 1) * l1Norm ψ := by
  classical
  rw [sq, Module.End.mul_apply]
  have h1 := l1Norm_create_le (h.create j) j
  have h2 := l1Norm_create_le h j
  push_cast at h1
  refine h1.trans ((mul_le_mul_right h2 _).trans ?_)
  rw [← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.coe_mul, ← NNReal.sqrt_mul]
  have : NNReal.sqrt ((e + 1 + 1) * (e + 1)) ≤ 2 * ((e : ℝ≥0) + 1) := by
    rw [NNReal.sqrt_le_iff_le_sq]
    have h0 : (0 : ℝ≥0) ≤ e := (zero_le : (0 : ℝ≥0) ≤ e)
    calc ((e : ℝ≥0) + 1 + 1) * (e + 1) ≤ (2 * (e + 1)) * (e + 1) := by
          gcongr
          calc (e : ℝ≥0) + 1 + 1 ≤ (e + 1) + (e + 1) := by gcongr; exact le_add_of_nonneg_left h0
            _ = 2 * (e + 1) := (two_mul _).symm
      _ ≤ (2 * (e + 1)) * (2 * (e + 1)) := by
          gcongr
          calc (e : ℝ≥0) + 1 = 1 * (e + 1) := (one_mul _).symm
            _ ≤ 2 * (e + 1) := by gcongr; norm_num
      _ = (2 * (e + 1)) ^ 2 := (sq _).symm
  exact_mod_cast this

/-- `(e + 1)(e + 2) ⋯ (e + k) ≤ 2^{e + k} k!`. -/
private theorem ascFactorial_le_two_pow_mul_factorial (e k : ℕ) :
    (e + 1).ascFactorial k ≤ 2 ^ (e + k) * k.factorial := by
  have h1 := Nat.factorial_mul_ascFactorial e k
  have h2 := Nat.add_choose_mul_factorial_mul_factorial e k
  have h3 := Nat.choose_le_two_pow (e + k) k
  have he := Nat.factorial_pos e
  have : (e + 1).ascFactorial k = (e + k).choose k * k.factorial := by
    refine Nat.eq_of_mul_eq_mul_left he ?_
    rw [h1, ← h2]
    ring
  rw [this]
  exact Nat.mul_le_mul_right _ h3

end FormalFock

namespace FormalFock

open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)` raises a particle bound by two. -/
theorem VanishesAbove.gaussRaise_op {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ)
    (κ ℓ : ι → ℂ) : VanishesAbove (e + 2) ((gaussRaise κ ℓ).op ψ) := by
  rw [FormalFock.gaussRaise_op, LinearMap.sum_apply]
  refine vanishesAbove_sum _ fun j _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  have h2 : VanishesAbove (e + 2) ((FormalFock.create j ^ 2) ψ) := by
    rw [sq, Module.End.mul_apply]
    exact (h.create j).create j
  exact (h2.smul _).add (((h.create j).mono (by omega)).smul _)

omit [DecidableEq ι] in
/-- On vectors with at most `e` particles, `Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)` adds at most two particles and
`‖Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†) ψ‖₁ ≤ B (e + 1) ‖ψ‖₁` with `B = Σⱼ (2|κⱼ| + |ℓⱼ|)`. -/
private theorem gaussRaise_op_l1Norm_le (κ ℓ : ι → ℂ) {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) :
    VanishesAbove (e + 2) ((gaussRaise κ ℓ).op ψ) ∧
      l1Norm ((gaussRaise κ ℓ).op ψ) ≤
        ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) * ((e : ℝ≥0∞) + 1) * l1Norm ψ := by
  classical
  refine ⟨h.gaussRaise_op κ ℓ, ?_⟩
  rw [gaussRaise_op, LinearMap.sum_apply]
  · refine (l1Norm_sum_le _ _).trans ?_
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    refine (l1Norm_add_le _ _).trans ?_
    rw [l1Norm_smul, l1Norm_smul]
    calc (‖κ j‖₊ : ℝ≥0∞) * l1Norm ((create j ^ 2) ψ) + ‖ℓ j‖₊ * l1Norm (create j ψ)
        ≤ ‖κ j‖₊ * (2 * ((e : ℝ≥0∞) + 1) * l1Norm ψ) + ‖ℓ j‖₊ * (((e : ℝ≥0∞) + 1) * l1Norm ψ) :=
          add_le_add (mul_le_mul_right (l1Norm_create_sq_le h j) _)
            (mul_le_mul_right (l1Norm_create_le' h j) _)
      _ = ((2 * ‖κ j‖₊ + ‖ℓ j‖₊ : ℝ≥0) : ℝ≥0∞) * ((e : ℝ≥0∞) + 1) * l1Norm ψ := by
          push_cast
          ring

omit [DecidableEq ι] in
/-- The powers: `‖(Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†))ᵏ ψ‖₁ ≤ (2B)ᵏ (e + 1)(e + 2) ⋯ (e + k) ‖ψ‖₁`. -/
private theorem gaussRaise_op_pow_l1Norm_le (κ ℓ : ι → ℂ) (k : ℕ) {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) :
    VanishesAbove (e + 2 * k) (((gaussRaise κ ℓ).op ^ k) ψ) ∧
      l1Norm (((gaussRaise κ ℓ).op ^ k) ψ) ≤
        (2 * ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞)) ^ k *
          ((e + 1).ascFactorial k : ℝ≥0∞) * l1Norm ψ := by
  classical
  induction k with
  | zero => simp [h]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := gaussRaise_op_l1Norm_le κ ℓ h1
    rw [pow_succ', Module.End.mul_apply]
    refine ⟨h3.mono (by omega), h4.trans ?_⟩
    rw [Nat.ascFactorial_succ]
    have hc : ((e + 2 * k : ℕ) : ℝ≥0∞) + 1 ≤ 2 * ((e + 1 + k : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by omega : e + 2 * k + 1 ≤ 2 * (e + 1 + k))
    calc ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) * (((e + 2 * k : ℕ) : ℝ≥0∞) + 1) *
          l1Norm (((gaussRaise κ ℓ).op ^ k) ψ)
        ≤ ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) * (2 * ((e + 1 + k : ℕ) : ℝ≥0∞)) *
          ((2 * ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞)) ^ k *
            ((e + 1).ascFactorial k : ℝ≥0∞) * l1Norm ψ) := by
          gcongr
      _ = _ := by
          push_cast
          ring

omit [Fintype ι] [DecidableEq ι] in
/-- The remainder of the exponential series: `‖e^T ψ - ψ - T ψ‖₁ ≤ Σₖ ‖T^{k+2} ψ‖₁/(k + 2)!`. -/
private theorem l1Norm_exp_sub_le (T : NumberRaisingOp ι ℂ) (ψ : FormalFock ι ℂ) :
    l1Norm (T.exp ψ - ψ - T.op ψ) ≤
      ∑' k : ℕ, (((k + 2).factorial : ℝ≥0∞))⁻¹ * l1Norm ((T.op ^ (k + 2)) ψ) := by
  have hc : ∀ n, (T.exp ψ - ψ - T.op ψ).coeff n = ∑ k ∈ range n.degree,
      (((k + 2).factorial : ℂ))⁻¹ • ((T.op ^ (k + 2)) ψ).coeff n := by
    intro n
    rw [coeff_sub, coeff_sub, NumberRaisingOp.coeff_exp_eq_sum T ψ (M := n.degree + 1) (by omega),
      sum_range_succ', sum_range_succ']
    simp only [pow_zero, pow_one, Module.End.one_apply, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, inv_one, one_smul, zero_add]
    abel
  have hterm : ∀ (k : ℕ) (n : ι →₀ ℕ),
      ((‖(((k + 2).factorial : ℂ))⁻¹ • ((T.op ^ (k + 2)) ψ).coeff n‖₊ : ℝ≥0) : ℝ≥0∞) =
        (((k + 2).factorial : ℝ≥0∞))⁻¹ * ‖((T.op ^ (k + 2)) ψ).coeff n‖₊ := fun k n => by
    rw [nnnorm_smul, nnnorm_inv, Complex.nnnorm_natCast, ENNReal.coe_mul,
      ENNReal.coe_inv (by exact_mod_cast (Nat.factorial_pos _).ne'), ENNReal.coe_natCast]
  rw [l1Norm]
  calc ∑' n, (‖(T.exp ψ - ψ - T.op ψ).coeff n‖₊ : ℝ≥0∞)
      ≤ ∑' n, ∑' k : ℕ, (((k + 2).factorial : ℝ≥0∞))⁻¹ *
          ‖((T.op ^ (k + 2)) ψ).coeff n‖₊ := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [hc n]
        refine (ENNReal.coe_le_coe.2 (nnnorm_sum_le _ _)).trans ?_
        rw [ENNReal.ofNNReal_finsetSum]
        refine (Finset.sum_le_sum fun k _ => (hterm k n).le).trans (ENNReal.sum_le_tsum _)
    _ = ∑' k : ℕ, ∑' n, (((k + 2).factorial : ℝ≥0∞))⁻¹ *
          ‖((T.op ^ (k + 2)) ψ).coeff n‖₊ := ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr fun k => ?_
        rw [ENNReal.tsum_mul_left, l1Norm]

omit [DecidableEq ι] in
/-- **The exponential remainder.** If `ψ` has at most `e` particles and `4B ≤ 1/2`,
`B = Σⱼ (2|κⱼ| + |ℓⱼ|)`, then `‖e^T ψ - ψ - T ψ‖₁ ≤ 2^{e+5} B² ‖ψ‖₁` for
`T = Σⱼ (κⱼ aⱼ†² + ℓⱼ aⱼ†)`. -/
private theorem l1Norm_gaussRaise_exp_sub_le (κ ℓ : ι → ℂ) {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ)
    (hB : 4 * ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) ≤ 2⁻¹) :
    l1Norm ((gaussRaise κ ℓ).exp ψ - ψ - (gaussRaise κ ℓ).op ψ) ≤
      2 ^ (e + 5) * ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) ^ 2 * l1Norm ψ := by
  classical
  set B : ℝ≥0∞ := ((∑ j, (2 * ‖κ j‖₊ + ‖ℓ j‖₊) : ℝ≥0) : ℝ≥0∞) with hBdef
  refine (l1Norm_exp_sub_le _ ψ).trans ?_
  calc ∑' k : ℕ, (((k + 2).factorial : ℝ≥0∞))⁻¹ * l1Norm (((gaussRaise κ ℓ).op ^ (k + 2)) ψ)
      ≤ ∑' k : ℕ, 2 ^ e * (2 * (2 * B)) ^ 2 * l1Norm ψ * (2 * (2 * B)) ^ k := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        have h1 := (gaussRaise_op_pow_l1Norm_le κ ℓ (k + 2) h).2
        have h2 : ((e + 1).ascFactorial (k + 2) : ℝ≥0∞) ≤
            2 ^ (e + (k + 2)) * ((k + 2).factorial : ℝ≥0∞) := by
          exact_mod_cast ascFactorial_le_two_pow_mul_factorial e (k + 2)
        have hf : (((k + 2).factorial : ℝ≥0∞))⁻¹ * ((k + 2).factorial : ℝ≥0∞) = 1 :=
          ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos _).ne')
            (ENNReal.natCast_ne_top _)
        calc (((k + 2).factorial : ℝ≥0∞))⁻¹ * l1Norm (((gaussRaise κ ℓ).op ^ (k + 2)) ψ)
            ≤ (((k + 2).factorial : ℝ≥0∞))⁻¹ * ((2 * B) ^ (k + 2) *
                (2 ^ (e + (k + 2)) * ((k + 2).factorial : ℝ≥0∞)) * l1Norm ψ) := by
              gcongr
              exact h1.trans (by gcongr)
          _ = (((k + 2).factorial : ℝ≥0∞))⁻¹ * ((k + 2).factorial : ℝ≥0∞) *
                (2 ^ e * (2 * (2 * B)) ^ 2 * l1Norm ψ * (2 * (2 * B)) ^ k) := by
              have hC : (2 * B) ^ (k + 2) * 2 ^ (k + 2) =
                  (2 * (2 * B)) ^ k * (2 * (2 * B)) ^ 2 := by
                rw [← mul_pow, mul_comm (2 * B) 2, ← pow_add]
              rw [pow_add 2 e (k + 2)]
              calc _ = (((k + 2).factorial : ℝ≥0∞))⁻¹ * ((k + 2).factorial : ℝ≥0∞) *
                    (2 ^ e * ((2 * B) ^ (k + 2) * 2 ^ (k + 2)) * l1Norm ψ) := by ring
                _ = _ := by rw [hC]; ring
          _ = _ := by rw [hf, one_mul]
    _ = 2 ^ e * (2 * (2 * B)) ^ 2 * l1Norm ψ * ∑' k : ℕ, (2 * (2 * B)) ^ k :=
        ENNReal.tsum_mul_left
    _ ≤ 2 ^ e * (2 * (2 * B)) ^ 2 * l1Norm ψ * 2 := by
        have h4 : 2 * (2 * B) ≤ 2⁻¹ := by
          rw [← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num]
          exact hB
        gcongr
        calc ∑' k : ℕ, (2 * (2 * B)) ^ k ≤ ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k :=
              ENNReal.tsum_le_tsum fun k => by gcongr
          _ = 2 := ENNReal.tsum_geometric_two
    _ = 2 ^ (e + 5) * B ^ 2 * l1Norm ψ := by
        rw [pow_add]
        ring

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*}

/-- The ℓ¹ norm majorizes the norm of `Γ_s`. -/
private theorem ofReal_norm_le_l1Norm (ψ : FockSpace ι) :
    ENNReal.ofReal ‖ψ‖ ≤ l1Norm (toFormal ψ) := by
  have h := sqNorm_le_l1Norm_sq (toFormal ψ)
  rw [sqNorm_toFormal, ENNReal.ofReal_pow (norm_nonneg _)] at h
  exact le_of_not_gt fun hlt => ((ENNReal.pow_lt_pow_left_iff two_ne_zero).2 hlt).not_ge h

/-- A formal vector with finite ℓ¹ norm is in `Γ_s`. -/
private theorem exists_toFormal_eq_of_l1Norm_ne_top {ψ : FormalFock ι ℂ} (h : l1Norm ψ ≠ ⊤) :
    ∃ φ : FockSpace ι, toFormal φ = ψ :=
  (mem_range_toFormal_iff ψ).2 ((sqNorm_le_l1Norm_sq ψ).trans_lt
    (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 h)))

/-- A formal vector with at most `e` particles is in `Γ_s`. -/
theorem exists_toFormal_eq_of_vanishesAbove [Finite ι] {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) : ∃ φ : FockSpace ι, toFormal φ = ψ :=
  exists_toFormal_eq_of_l1Norm_ne_top (by
    unfold l1Norm
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (summable_of_hasFiniteSupport (h.finite_support.subset fun n hn h0 => hn (by simp [h0]))))

/-- A finitely supported vector has at most `e` particles for some `e`. -/
theorem exists_vanishesAbove_of_finite {ψ : FockSpace ι} (h : (Function.support ψ).Finite) :
    ∃ e, VanishesAbove e (toFormal ψ) :=
  ⟨h.toFinset.sup Finsupp.degree, fun p hp => by
    rw [coeff_toFormal]
    by_contra hne
    exact absurd (Finset.le_sup (f := Finsupp.degree) (h.mem_toFinset.2 hne)) (by omega)⟩

end FockSpace

namespace FockSpace

open FormalFock Asymptotics Filter
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Derivative of a raising exponential on a number state.** If `κ(t)` and `ℓ(t)` vanish at
`t = 0` and are differentiable there with derivatives `κ'`, `ℓ'`, then
`t ↦ e^{Σⱼ (κⱼ(t) aⱼ†² + ℓⱼ(t) aⱼ†)} ∣m⟩` (taken in `Γ_s`) has derivative
`Σⱼ (κ'ⱼ aⱼ†² + ℓ'ⱼ aⱼ†) ∣m⟩` at `t = 0`. -/
theorem hasDerivAt_gaussRaise_exp {κ ℓ : ℝ → ι → ℂ} {κ' ℓ' : ι → ℂ}
    (hκ : ∀ j, HasDerivAt (fun t => κ t j) (κ' j) 0)
    (hℓ : ∀ j, HasDerivAt (fun t => ℓ t j) (ℓ' j) 0) (hκ0 : κ 0 = 0) (hℓ0 : ℓ 0 = 0)
    (m : ι →₀ ℕ) {W : ℝ → FockSpace ι}
    (hW : ∀ t, toFormal (W t) = (gaussRaise (κ t) (ℓ t)).exp (single m 1)) {G : FockSpace ι}
    (hG : toFormal G = (gaussRaise κ' ℓ').op (single m 1)) :
    HasDerivAt W G 0 := by
  have hm : VanishesAbove m.degree (single m (1 : ℂ)) := vanishesAbove_single m 1
  have hl1 : l1Norm (single m (1 : ℂ)) = 1 := by
    rw [l1Norm_single, nnnorm_one, ENNReal.coe_one]
  have hfin2 : ∀ j, l1Norm ((create j ^ 2) (single m (1 : ℂ))) ≠ ⊤ := fun j =>
    ((l1Norm_create_sq_le hm j).trans_lt (by
      rw [hl1, mul_one]
      exact ENNReal.mul_lt_top (by simp) (by simp))).ne
  have hfin1 : ∀ j, l1Norm (create j (single m (1 : ℂ))) ≠ ⊤ := fun j =>
    ((l1Norm_create_le hm j).trans_lt (by
      rw [hl1, mul_one]
      simp)).ne
  choose v2 hv2 using fun j => exists_toFormal_eq_of_l1Norm_ne_top (hfin2 j)
  choose v1 hv1 using fun j => exists_toFormal_eq_of_l1Norm_ne_top (hfin1 j)
  have hy : toFormal (lp.single 2 m (1 : ℂ) : FockSpace ι) = single m 1 := toFormal_lpSingle m
  have hZ : ∀ (a b : ι → ℂ), toFormal (∑ j, (a j • v2 j + b j • v1 j)) =
      (gaussRaise a b).op (single m 1) := fun a b => by
    simp only [map_sum, map_add, map_smul, hv1, hv2, gaussRaise_op, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.smul_apply]
  have hGZ : G = ∑ j, (κ' j • v2 j + ℓ' j • v1 j) := toFormal_injective (by rw [hG, hZ])
  have hZd : HasDerivAt (fun t => ∑ j, (κ t j • v2 j + ℓ t j • v1 j)) G 0 := by
    rw [hGZ]
    exact HasDerivAt.fun_sum fun j _ =>
      ((hκ j).smul_const (v2 j)).fun_add ((hℓ j).smul_const (v1 j))
  -- the remainder `r(t) = W(t) - ∣m⟩ - Σⱼ (κⱼ(t) aⱼ†² + ℓⱼ(t) aⱼ†)∣m⟩`
  set r : ℝ → FockSpace ι := fun t =>
    W t - lp.single 2 m (1 : ℂ) - ∑ j, (κ t j • v2 j + ℓ t j • v1 j) with hrdef
  have hr : ∀ t, toFormal (r t) = (gaussRaise (κ t) (ℓ t)).exp (single m 1) - single m 1 -
      (gaussRaise (κ t) (ℓ t)).op (single m 1) := fun t => by
    rw [hrdef, map_sub, map_sub, hW, hy, hZ]
  -- `B(t) = Σⱼ (2|κⱼ(t)| + |ℓⱼ(t)|) = O(t)`
  set B : ℝ → ℝ := fun t => ∑ j, (2 * ‖κ t j‖ + ‖ℓ t j‖) with hBdef
  have hBO : B =O[𝓝 0] fun t => t := by
    refine IsBigO.fun_sum fun j _ => ((((hκ j).isBigO_sub).norm_left.const_mul_left 2).add
      ((hℓ j).isBigO_sub).norm_left).congr (fun t => ?_) (fun t => sub_zero t)
    simp [hκ0, hℓ0]
  have hBt : Tendsto B (𝓝 0) (𝓝 0) := hBO.trans_tendsto tendsto_id
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), B t < 8⁻¹ := (tendsto_order.1 hBt).2 _ (by norm_num)
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), ‖r t‖ ≤ 2 ^ (m.degree + 5) * ‖B t ^ 2‖ := by
    filter_upwards [hev] with t ht
    have hB0 : 0 ≤ B t := sum_nonneg fun j _ => by positivity
    have hBn : ((∑ j, (2 * ‖κ t j‖₊ + ‖ℓ t j‖₊) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B t) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [hBdef]
    have h4 : 4 * ((∑ j, (2 * ‖κ t j‖₊ + ‖ℓ t j‖₊) : ℝ≥0) : ℝ≥0∞) ≤ 2⁻¹ := by
      have h5 : ENNReal.ofReal (4 * B t) ≤ ENNReal.ofReal 2⁻¹ :=
        ENNReal.ofReal_le_ofReal (by linarith)
      rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, ← hBn] at h5
    have h1 := l1Norm_gaussRaise_exp_sub_le (κ t) (ℓ t) hm h4
    rw [← hr] at h1
    have h := (ofReal_norm_le_l1Norm (r t)).trans h1
    have hR : (2 : ℝ≥0∞) ^ (m.degree + 5) * ENNReal.ofReal (B t) ^ 2 =
        ENNReal.ofReal (2 ^ (m.degree + 5) * B t ^ 2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow hB0, ENNReal.ofReal_ofNat]
    rw [hl1, mul_one, hBn, hR] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hro : r =o[𝓝 0] fun t => t :=
    (IsBigO.of_bound _ hbound).trans_isLittleO
      ((hBO.pow 2).trans_isLittleO (isLittleO_pow_id (by norm_num : 1 < 2)))
  have hr0 : r 0 = 0 := toFormal_injective (by
    rw [hr, map_zero, hκ0, hℓ0, NumberRaisingOp.exp_of_op_eq_zero (by simp [gaussRaise_op])]
    simp [gaussRaise_op])
  have hrd : HasDerivAt r 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simpa [hr0] using hro
  have hW' : W = fun t => lp.single 2 m (1 : ℂ) + ∑ j, (κ t j • v2 j + ℓ t j • v1 j) + r t := by
    funext t
    simp [hrdef]
  rw [hW']
  have := ((hasDerivAt_const (0 : ℝ) (lp.single 2 m (1 : ℂ) : FockSpace ι)).fun_add hZd).fun_add hrd
  rwa [zero_add, add_zero] at this

end FockSpace

end BosonicLean.Fock
