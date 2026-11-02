/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Bargmann
import BosonicLean.Fock.FockSpace
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Second quantization of a matrix

For a complex matrix `g` on the one-particle space `ℂ^ι`, the second quantization `Γ(g)` acts on the
formal Fock space, in the Bargmann picture, by the linear change of variables
`(Γ(g) f)(z) = f(gᵀ z)`. It is defined for every matrix and needs no analysis: substitution of
linear forms preserves degrees, so each coefficient of `Γ(g)ψ` is a finite sum over one
particle-number sector, with matrix elements `Γ(g)_{mn} = √(m!/n!) [z^m] (gᵀz)^n`, polynomials in
the entries of `g`. The map `g ↦ Γ(g)` is multiplicative, intertwines the ladder operators,
`Γ(g) aⱼ† = (Σ_k g_kj a_k†) Γ(g)` and `aⱼ Γ(g) = Γ(g) (Σ_k g_jk a_k)`, and has `Γ(g*)` as its
adjoint on finitely supported vectors. For a unitary matrix `𝒰`, `Γ(𝒰)` preserves the squared norm
of every formal vector, and its restriction `𝖴_𝒰` to the Fock space `Γ_s` is a unitary
representation of `U(ι)`, strongly continuous (`FockSpace.continuous_secondQuantRep_apply`). The
generator `dΓ(h) = Σ_{jk} h_jk aⱼ† a_k` acts in the Bargmann picture as `Σ_{jk} h_jk zⱼ ∂_k`, a
derivation of `ℂ[[z]]`, and `Γ(e^h) = e^{dΓ(h)}` for every matrix `h`, the exponential taken
coefficient by coefficient.

The convention is that of Tjoa and Cirac, (29) and Appendix A, (A26), which agree:
`Γ(𝒰)⁻¹ aⱼ Γ(𝒰) = Σ_k 𝒰_jk a_k` (`secondQuant_conjTranspose_mul_annihilate_mul`). The inverse
conjugation `Γ(𝒰) aⱼ† Γ(𝒰)⁻¹ = Σ_k 𝒰_kj a_k†` (`secondQuant_mul_create_mul_conjTranspose`) is a
consequence and does not appear in the paper.

## Main definitions

* `BosonicLean.Fock.FormalFock.sector p`: the component `[ψ]_p` in the sector of `p` particles.
* `BosonicLean.Fock.FormalFock.secondQuant g`: the second quantization `Γ(g)`.
* `BosonicLean.Fock.FormalFock.matrixCoeff g m n`: the matrix element `Γ(g)_{mn}`.
* `BosonicLean.Fock.FormalFock.totalNumber`: the total number operator `n_tot = Σ_j aⱼ† aⱼ`.
* `BosonicLean.Fock.FormalFock.pairing φ ψ`: `⟨φ, ψ⟩ = Σₙ conj(φ(n)) ψ(n)`.
* `BosonicLean.Fock.FockSpace.secondQuantUnitary 𝒰`: the unitary `𝖴_𝒰` of `Γ_s`.
* `BosonicLean.Fock.FockSpace.secondQuantRep`: the homomorphism `𝒰 ↦ 𝖴_𝒰` into the unitary group of
  `Γ_s`; with `continuous_secondQuantRep_apply`, a unitary representation.
* `BosonicLean.Fock.FormalFock.dSecondQuant h`: the generator `dΓ(h)`.
* `BosonicLean.Fock.FormalFock.coeffExp T`: the coefficientwise exponential `e^T`.

## Main results

* `coeff_secondQuant`, `exists_mvPolynomial_matrixCoeff`, `secondQuant_sector`,
  `commute_secondQuant_totalNumber`, `secondQuant_vacuum`, `secondQuant_single_one`,
  `finite_support_secondQuant`: coefficients and sectors.
* `secondQuant_one`, `secondQuant_mul`: the representation property.
* `secondQuant_mul_create`, `annihilate_mul_secondQuant`: intertwining, through the chain rule
  `pderiv_subst_linearForms`.
* `matrixCoeff_conjTranspose`, `pairing_secondQuant`: the adjoint.
* `sqNorm_secondQuant`, `FockSpace.secondQuantRep`, `FockSpace.continuous_secondQuantRep_apply`,
  `secondQuant_conjTranspose_mul_annihilate_mul`, `mem_map_secondQuant_iff`: unitarity.
* `Derivation.iterate_apply_mul`: the general Leibniz rule.
* `toBargmann_dSecondQuant`: `𝔅 dΓ(h) ψ = Σ_{jk} h_jk zⱼ ∂_k 𝔅ψ`.
* `norm_coeff_toBargmann_dSecondQuant_pow_le`, `summable_norm_coeff_dSecondQuant_pow`: the bound.
* `hasSum_coeff_dSecondQuant_pow`, `secondQuant_exp`: `Γ(e^h) = e^{dΓ(h)}`.
* `secondQuant_conjTranspose_mul_lift_mul`, `FockSpace.inner_maxRealization_conj`: conjugation of
  operators by `Γ(𝒰)`.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), (12), (29), (A20)–(A26).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, revised ed. (1980), §VIII.10.
* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform.
  Part I*, Comm. Pure Appl. Math. 14 (1961) 187–214.
-/

open MvPowerSeries
open scoped Matrix

namespace BosonicLean.Fock.FormalFock

/-! ### Particle-number sectors -/

section Sector

variable {ι R : Type*} [AddCommGroup R] [Module ℂ R]

/-- The component `[ψ]_p` of `ψ` in the **particle-number sector** of `p` particles: the
coefficients at the `n` with `∣n∣ = p`, and `0` elsewhere. -/
def sector (p : ℕ) : FormalFock ι R →ₗ[ℂ] FormalFock ι R where
  toFun ψ := ⟨fun n => if n.degree = p then ψ.coeff n else 0⟩
  map_add' ψ φ := by
    ext n
    simp only [coeff_add]
    split_ifs <;> simp
  map_smul' c ψ := by
    ext n
    simp only [coeff_smul, RingHom.id_apply]
    split_ifs <;> simp

/-- The coefficients of `[ψ]_p`. -/
theorem coeff_sector (p : ℕ) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (sector p ψ).coeff n = if n.degree = p then ψ.coeff n else 0 := rfl

end Sector

/-- Under the Bargmann map, the component `[ψ]_p` is the homogeneous component of degree `p`. -/
theorem toBargmann_sector {ι : Type*} (p : ℕ) (ψ : FormalFock ι ℂ) :
    toBargmann (sector p ψ) = homogeneousComponent p (toBargmann ψ) := by
  ext n
  rw [coeff_homogeneousComponent, coeff_toBargmann, coeff_toBargmann, coeff_sector]
  split_ifs <;> simp

variable {ι : Type*} [Fintype ι]

/-- The multi-indices of total particle number `p`. -/
theorem mem_finsuppAntidiag_univ [DecidableEq ι] {p : ℕ} {n : ι →₀ ℕ} :
    n ∈ Finset.finsuppAntidiag Finset.univ p ↔ n.degree = p := by
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

/-! ### Definition: the second quantization of a matrix -/

/-- The linear forms `(gᵀ z)_j = Σ_k g_kj z_k` that the second quantization of `g` substitutes
for the variables `z_j`. -/
noncomputable def linearForms (g : Matrix ι ι ℂ) (j : ι) : MvPowerSeries ι ℂ :=
  ∑ k, g k j • X k

/-- The coefficients of the linear form `(gᵀ z)_j`. -/
theorem coeff_linearForms [DecidableEq ι] (g : Matrix ι ι ℂ) (j : ι) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (linearForms g j) =
      ∑ k, if n = Finsupp.single k 1 then g k j else 0 := by
  simp [linearForms, MvPowerSeries.coeff_X]

/-- The linear forms have no constant term. -/
theorem constantCoeff_linearForms (g : Matrix ι ι ℂ) (j : ι) :
    constantCoeff (linearForms g j) = 0 := by
  simp [linearForms]

/-- The linear forms can be substituted into power series. -/
theorem hasSubst_linearForms (g : Matrix ι ι ℂ) : HasSubst (linearForms g) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_linearForms g)

/-- The **second quantization** `Γ(g)` of a complex matrix `g`: in the Bargmann picture it is the
substitution `f(z) ↦ f(gᵀ z)`, so `𝔅 Γ(g) = Γ̃(g) 𝔅`. It is defined on the whole formal Fock
space, for every matrix. -/
noncomputable def secondQuant (g : Matrix ι ι ℂ) : Module.End ℂ (FormalFock ι ℂ) :=
  toBargmann.symm.toLinearMap ∘ₗ (substAlgHom (hasSubst_linearForms g)).toLinearMap ∘ₗ
    toBargmann.toLinearMap

/-- `𝔅 Γ(g) ψ = (𝔅ψ)(gᵀ z)`. -/
theorem toBargmann_secondQuant (g : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) :
    toBargmann (secondQuant g ψ) = subst (linearForms g) (toBargmann ψ) := by
  simp [secondQuant]

/-! ### Homogeneity of the substitution -/

omit [Fintype ι] in
private theorem isHomogeneous_one : (1 : MvPowerSeries ι ℂ).IsHomogeneous 0 := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_one] at hd
  split_ifs at hd with h
  · simp [h]
  · exact absurd rfl hd

omit [Fintype ι] in
private theorem isHomogeneous_pow {f : MvPowerSeries ι ℂ} {p : ℕ} (hf : f.IsHomogeneous p)
    (e : ℕ) : (f ^ e).IsHomogeneous (p * e) := by
  classical
  induction e with
  | zero =>
    rw [pow_zero, mul_zero]
    exact fun {_} hd => isHomogeneous_one hd
  | succ e ih => rw [pow_succ, mul_add, mul_one]; exact IsHomogeneous.mul ih hf

/-- The linear form `(gᵀ z)_j` is homogeneous of degree `1`. -/
theorem isHomogeneous_linearForms (g : Matrix ι ι ℂ) (j : ι) :
    (linearForms g j).IsHomogeneous 1 := by
  classical
  intro d hd
  rw [coeff_linearForms] at hd
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  split_ifs at hk with h
  · subst h
    simp [Finsupp.weight_apply]
  · exact absurd rfl hk

/-- The product `(gᵀ z)^n = ∏_j (gᵀ z)_j^{n_j}` is homogeneous of degree `∣n∣`. -/
theorem isHomogeneous_prod_linearForms (g : Matrix ι ι ℂ) (n : ι →₀ ℕ) :
    (n.prod fun j e => linearForms g j ^ e).IsHomogeneous n.degree := by
  classical
  have key : ∀ s : Finset ι,
      (∏ j ∈ s, linearForms g j ^ n j).IsHomogeneous (∑ j ∈ s, n j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact fun {_} hd => isHomogeneous_one hd
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 : (linearForms g a ^ n a).IsHomogeneous (1 * n a) :=
        isHomogeneous_pow (isHomogeneous_linearForms g a) (n a)
      have h2 : (linearForms g a ^ n a * ∏ j ∈ s, linearForms g j ^ n j).IsHomogeneous
          (1 * n a + ∑ j ∈ s, n j) := IsHomogeneous.mul h1 ih
      rwa [one_mul] at h2
  exact fun {_} hd => key n.support hd

/-- `(gᵀz)^n` has no coefficient outside degree `∣n∣`. -/
theorem coeff_prod_linearForms_eq_zero (g : Matrix ι ι ℂ) {m n : ι →₀ ℕ}
    (h : m.degree ≠ n.degree) :
    MvPowerSeries.coeff m (n.prod fun j e => linearForms g j ^ e) = 0 :=
  IsHomogeneous.coeff_eq_zero (fun {_} hd => isHomogeneous_prod_linearForms g n hd) h

/-- The coefficient at `m` of the substitution involves only the coefficients of degree `∣m∣`. -/
theorem coeff_subst_linearForms [DecidableEq ι] (g : Matrix ι ι ℂ) (f : MvPowerSeries ι ℂ)
    (m : ι →₀ ℕ) :
    MvPowerSeries.coeff m (subst (linearForms g) f) =
      ∑ d ∈ Finset.finsuppAntidiag Finset.univ m.degree, MvPowerSeries.coeff d f *
        MvPowerSeries.coeff m (d.prod fun j e => linearForms g j ^ e) := by
  rw [coeff_subst (hasSubst_linearForms g)]
  refine finsum_eq_sum_of_support_subset _ fun d hd => ?_
  rw [Finset.mem_coe, mem_finsuppAntidiag_univ]
  by_contra hne
  exact hd (by simp only [coeff_prod_linearForms_eq_zero g (Ne.symm hne), smul_zero])

/-! ### Coefficients and particle-number sectors -/

omit [Fintype ι] in
/-- The coefficients of the inverse Bargmann map: `ψ(n) = √(n!) [zⁿ] 𝔅ψ`. -/
theorem coeff_toBargmann_symm (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) :
    (toBargmann.symm f : FormalFock ι ℂ).coeff n = sqrtFactorial n * MvPowerSeries.coeff n f :=
  rfl

omit [Fintype ι] in
/-- The Bargmann image of `c∣n⟩` is the monomial `c zⁿ / √(n!)`. -/
theorem toBargmann_single [DecidableEq ι] (n : ι →₀ ℕ) (c : ℂ) :
    toBargmann (single n c) = monomial n ((sqrtFactorial n)⁻¹ * c) := by
  ext m
  rw [coeff_toBargmann, coeff_single, coeff_monomial]
  split_ifs with h
  · subst h; rfl
  · exact smul_zero _

omit [Fintype ι] in
/-- The Bargmann image of the one-particle state `∣eⱼ⟩` is the variable `zⱼ`. -/
theorem toBargmann_single_one [DecidableEq ι] (j : ι) :
    toBargmann (single (Finsupp.single j 1) (1 : ℂ)) = X j := by
  rw [toBargmann_single, sqrtFactorial, factorial, Finsupp.prod_single_index (by simp)]
  simp [sqrtC, X]

/-- The Bargmann image of `Γ(g)∣n⟩` is `(gᵀz)^n / √(n!)`. -/
theorem toBargmann_secondQuant_single [DecidableEq ι] (g : Matrix ι ι ℂ) (n : ι →₀ ℕ) :
    toBargmann (secondQuant g (single n 1)) =
      (sqrtFactorial n)⁻¹ • n.prod fun j e => linearForms g j ^ e := by
  rw [toBargmann_secondQuant, toBargmann_single, subst_monomial (hasSubst_linearForms g),
    mul_one, Algebra.smul_def]

/-- The matrix element `Γ(g)_{mn} = (Γ(g)∣n⟩)(m)`. -/
noncomputable def matrixCoeff [DecidableEq ι] (g : Matrix ι ι ℂ) (m n : ι →₀ ℕ) : ℂ :=
  (secondQuant g (single n 1)).coeff m

/-- `Γ(g)_{mn} = √(m!/n!) [z^m] (gᵀz)^n`, a polynomial in the entries of `g`. -/
theorem matrixCoeff_eq [DecidableEq ι] (g : Matrix ι ι ℂ) (m n : ι →₀ ℕ) :
    matrixCoeff g m n = sqrtFactorial m * (sqrtFactorial n)⁻¹ *
      MvPowerSeries.coeff m (n.prod fun j e => linearForms g j ^ e) := by
  rw [matrixCoeff, ← toBargmann.symm_apply_apply (secondQuant g (single n 1)),
    toBargmann_secondQuant_single, coeff_toBargmann_symm, MvPowerSeries.coeff_smul, ← mul_assoc]

/-- `Γ(g)_{mn} = 0` unless `∣m∣ = ∣n∣`. -/
theorem matrixCoeff_eq_zero_of_degree_ne [DecidableEq ι] (g : Matrix ι ι ℂ) {m n : ι →₀ ℕ}
    (h : m.degree ≠ n.degree) : matrixCoeff g m n = 0 := by
  rw [matrixCoeff_eq, coeff_prod_linearForms_eq_zero g h, mul_zero]

omit [Fintype ι] in
private theorem exists_mvPolynomial_coeff_mul {F G : Matrix ι ι ℂ → MvPowerSeries ι ℂ}
    (hF : ∀ d, ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g,
      MvPowerSeries.coeff d (F g) = MvPolynomial.eval (fun ij => g ij.1 ij.2) P)
    (hG : ∀ d, ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g,
      MvPowerSeries.coeff d (G g) = MvPolynomial.eval (fun ij => g ij.1 ij.2) P)
    (d : ι →₀ ℕ) : ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g,
      MvPowerSeries.coeff d (F g * G g) = MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
  classical
  choose P hP using hF
  choose Q hQ using hG
  refine ⟨∑ x ∈ Finset.antidiagonal d, P x.1 * Q x.2, fun g => ?_⟩
  simp only [MvPowerSeries.coeff_mul, map_sum, map_mul, hP, hQ]

omit [Fintype ι] in
private theorem exists_mvPolynomial_coeff_one (d : ι →₀ ℕ) :
    ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      MvPowerSeries.coeff d (1 : MvPowerSeries ι ℂ) =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
  ⟨MvPolynomial.C (MvPowerSeries.coeff d 1), fun _ => (MvPolynomial.eval_C _).symm⟩

private theorem exists_mvPolynomial_coeff_prod_linearForms (n d : ι →₀ ℕ) :
    ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      MvPowerSeries.coeff d (n.prod fun j e => linearForms g j ^ e) =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
  classical
  have hlf : ∀ j d, ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      MvPowerSeries.coeff d (linearForms g j) = MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun j d => ⟨∑ k, if d = Finsupp.single k 1 then MvPolynomial.X (k, j) else 0, fun g => by
      simp only [coeff_linearForms, map_sum, apply_ite (MvPolynomial.eval _),
        MvPolynomial.eval_X, map_zero]⟩
  have hpow : ∀ j e d, ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      MvPowerSeries.coeff d (linearForms g j ^ e) =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
    intro j e
    induction e with
    | zero => simpa using exists_mvPolynomial_coeff_one
    | succ e ih => simpa only [pow_succ] using exists_mvPolynomial_coeff_mul ih (hlf j)
  have key : ∀ s : Finset ι, ∀ d, ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      MvPowerSeries.coeff d (∏ j ∈ s, linearForms g j ^ n j) =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using exists_mvPolynomial_coeff_one
    | insert a s ha ih =>
      simpa only [Finset.prod_insert ha] using exists_mvPolynomial_coeff_mul (hpow a (n a)) ih
  exact key n.support d

/-- **Lemma 2(a).** The matrix element `Γ(g)_{mn}` is a polynomial in the entries of `g`. -/
theorem exists_mvPolynomial_matrixCoeff [DecidableEq ι] (m n : ι →₀ ℕ) :
    ∃ P : MvPolynomial (ι × ι) ℂ, ∀ g : Matrix ι ι ℂ,
      matrixCoeff g m n = MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_coeff_prod_linearForms n m
  refine ⟨MvPolynomial.C (sqrtFactorial m * (sqrtFactorial n)⁻¹) * P, fun g => ?_⟩
  rw [matrixCoeff_eq, hP, map_mul, MvPolynomial.eval_C]

/-- **Lemma 2(a).** The coefficient of `Γ(g)ψ` at `m` is the finite sum
`Σ_{∣n∣ = ∣m∣} Γ(g)_{mn} ψ(n)`. -/
theorem coeff_secondQuant [DecidableEq ι] (g : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) (m : ι →₀ ℕ) :
    (secondQuant g ψ).coeff m =
      ∑ n ∈ Finset.finsuppAntidiag Finset.univ m.degree, matrixCoeff g m n * ψ.coeff n := by
  rw [← toBargmann.symm_apply_apply (secondQuant g ψ), toBargmann_secondQuant,
    coeff_toBargmann_symm, coeff_subst_linearForms, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matrixCoeff_eq, coeff_toBargmann, smul_eq_mul]
  ring

/-- **Lemma 2(a).** `Γ(g)` preserves the particle-number sectors: `[Γ(g)ψ]_p = Γ(g)[ψ]_p`. -/
theorem secondQuant_sector (g : Matrix ι ι ℂ) (p : ℕ) (ψ : FormalFock ι ℂ) :
    secondQuant g (sector p ψ) = sector p (secondQuant g ψ) := by
  classical
  ext m
  rw [coeff_secondQuant, coeff_sector, coeff_secondQuant]
  split_ifs with hm
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [mem_finsuppAntidiag_univ] at hn
    simp [coeff_sector, hn.trans hm]
  · refine Finset.sum_eq_zero fun n hn => ?_
    rw [mem_finsuppAntidiag_univ] at hn
    simp [coeff_sector, hn, hm]

/-- The total number operator `n_tot = Σ_j aⱼ† aⱼ`. -/
noncomputable def totalNumber : Module.End ℂ (FormalFock ι ℂ) :=
  ∑ j, create j * annihilate j

omit [Fintype ι] in
/-- `aⱼ† aⱼ` multiplies the coefficient at `n` by `nⱼ`. -/
theorem coeff_create_mul_annihilate (j : ι) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    ((create j * annihilate j : Module.End ℂ (FormalFock ι ℂ)) ψ).coeff n =
      (n j : ℂ) * ψ.coeff n := by
  rw [Module.End.mul_apply, coeff_create]
  split_ifs with h
  · rw [coeff_annihilate, sub_single_add_single h, smul_smul, smul_eq_mul]
    have hn : (n - Finsupp.single j 1 : ι →₀ ℕ) j + 1 = n j := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    rw [hn, sqrtC_mul_self]
  · have h0 : n j = 0 := by omega
    simp [h0]

/-- `n_tot` multiplies the coefficient at `n` by `∣n∣`. -/
theorem coeff_totalNumber (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    (totalNumber ψ).coeff n = (n.degree : ℂ) * ψ.coeff n := by
  rw [totalNumber, LinearMap.sum_apply, coeff_sum]
  simp only [coeff_create_mul_annihilate, ← Finset.sum_mul, Finsupp.degree_eq_sum, Nat.cast_sum]

/-- **Lemma 2(a).** `Γ(g)` commutes with the total number operator. -/
theorem commute_secondQuant_totalNumber (g : Matrix ι ι ℂ) :
    Commute (secondQuant g) (totalNumber (ι := ι)) := by
  classical
  refine LinearMap.ext fun ψ => ?_
  ext m
  rw [Module.End.mul_apply, Module.End.mul_apply, coeff_secondQuant, coeff_totalNumber,
    coeff_secondQuant, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_finsuppAntidiag_univ] at hn
  rw [coeff_totalNumber, hn]
  ring

/-- **Lemma 2(b).** `Γ(g)∣0⟩ = ∣0⟩`. -/
theorem secondQuant_vacuum [DecidableEq ι] (g : Matrix ι ι ℂ) (c : ℂ) :
    secondQuant g (single 0 c) = single 0 c := by
  apply toBargmann.injective
  rw [toBargmann_secondQuant, toBargmann_vacuum, subst_C]

/-- **Lemma 2(b).** On the one-particle sector `Γ(g)` is `g`: `Γ(g)∣eⱼ⟩ = Σ_k g_kj ∣e_k⟩`. -/
theorem secondQuant_single_one [DecidableEq ι] (g : Matrix ι ι ℂ) (j : ι) :
    secondQuant g (single (Finsupp.single j 1) 1) =
      ∑ k, g k j • single (Finsupp.single k 1) (1 : ℂ) := by
  apply toBargmann.injective
  rw [toBargmann_secondQuant, toBargmann_single_one, subst_X (hasSubst_linearForms g), map_sum]
  simp only [map_smul, toBargmann_single_one, linearForms]

/-- **Lemma 2(a).** `Γ(g)` is coefficient-finite. -/
theorem isCoeffFinite_secondQuant (g : Matrix ι ι ℂ) : IsCoeffFinite (secondQuant g) := by
  classical
  intro m
  refine ⟨Finset.finsuppAntidiag Finset.univ m.degree, fun ψ φ h => ?_⟩
  rw [coeff_secondQuant, coeff_secondQuant]
  exact Finset.sum_congr rfl fun n hn => by rw [h n hn]

/-- **Lemma 2(c).** `Γ(g)` maps finitely supported vectors to finitely supported vectors. -/
theorem finite_support_secondQuant (g : Matrix ι ι ℂ) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) :
    (Function.support (secondQuant g φ).coeff).Finite := by
  classical
  refine (hφ.biUnion fun n _ =>
    (Finset.finsuppAntidiag Finset.univ n.degree).finite_toSet).subset fun m hm => ?_
  rw [Function.mem_support, coeff_secondQuant] at hm
  obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [mem_finsuppAntidiag_univ] at hn
  exact Set.mem_iUnion₂.2 ⟨n, right_ne_zero_of_mul hne, by
    rw [Finset.mem_coe, mem_finsuppAntidiag_univ, hn]⟩

/-! ### Theorem 3: the representation property -/

/-- For `g = 1` the linear forms are the variables. -/
theorem linearForms_one [DecidableEq ι] : linearForms (1 : Matrix ι ι ℂ) = X := by
  funext j
  simp [linearForms, Matrix.one_apply]

/-- Substituting `(gᵀ z)` into `(g'ᵀ z)_j` gives `((g g')ᵀ z)_j`. -/
theorem subst_linearForms (g g' : Matrix ι ι ℂ) (j : ι) :
    subst (linearForms g) (linearForms g' j) = linearForms (g * g') j := by
  rw [← coe_substAlgHom (hasSubst_linearForms g)]
  simp only [linearForms, map_sum, map_smul, substAlgHom_X, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- **Theorem 3.** `Γ(1) = 1`. -/
theorem secondQuant_one [DecidableEq ι] : secondQuant (1 : Matrix ι ι ℂ) = 1 := by
  refine LinearMap.ext fun ψ => toBargmann.injective ?_
  rw [toBargmann_secondQuant, linearForms_one, subst_self]
  rfl

/-- **Theorem 3.** `Γ(g g') = Γ(g) Γ(g')`. -/
theorem secondQuant_mul (g g' : Matrix ι ι ℂ) :
    secondQuant (g * g') = secondQuant g * secondQuant g' := by
  refine LinearMap.ext fun ψ => toBargmann.injective ?_
  rw [Module.End.mul_apply, toBargmann_secondQuant, toBargmann_secondQuant,
    toBargmann_secondQuant, subst_comp_subst_apply (hasSubst_linearForms g')
      (hasSubst_linearForms g)]
  congr 1
  funext j
  rw [subst_linearForms]

/-- **Theorem 3.** `g ↦ Γ(g)` as a monoid homomorphism. -/
noncomputable def secondQuantHom [DecidableEq ι] :
    Matrix ι ι ℂ →* Module.End ℂ (FormalFock ι ℂ) where
  toFun := secondQuant
  map_one' := secondQuant_one
  map_mul' := secondQuant_mul

/-- The monoid homomorphism `g ↦ Γ(g)` applied to `g` is `Γ(g)`. -/
theorem secondQuantHom_apply [DecidableEq ι] (g : Matrix ι ι ℂ) :
    secondQuantHom g = secondQuant g := rfl

/-- **Theorem 3.** For invertible `g`, `Γ(g⁻¹) Γ(g) = 1`. -/
theorem secondQuant_inv_mul [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : IsUnit g) :
    secondQuant g⁻¹ * secondQuant g = 1 := by
  rw [← secondQuant_mul, Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hg),
    secondQuant_one]

/-- **Theorem 3.** For invertible `g`, `Γ(g) Γ(g⁻¹) = 1`. -/
theorem secondQuant_mul_inv [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : IsUnit g) :
    secondQuant g * secondQuant g⁻¹ = 1 := by
  rw [← secondQuant_mul, Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).1 hg),
    secondQuant_one]

/-! ### Theorem 4: intertwining with the ladder operators -/

/-- **Theorem 4.** `Γ(g) aⱼ† = (Σ_k g_kj a_k†) Γ(g)` on the whole formal Fock space. -/
theorem secondQuant_mul_create (g : Matrix ι ι ℂ) (j : ι) :
    secondQuant g * create j = (∑ k, g k j • create k) * secondQuant g := by
  classical
  refine LinearMap.ext fun ψ => toBargmann.injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, toBargmann_secondQuant, toBargmann_create,
    subst_mul (hasSubst_linearForms g), subst_X (hasSubst_linearForms g), LinearMap.sum_apply,
    map_sum, ← toBargmann_secondQuant, linearForms, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, map_smul, toBargmann_create, smul_mul_assoc]

/-- `∂ⱼ (gᵀ z)ᵢ = g_ji`. -/
theorem pderiv_linearForms (g : Matrix ι ι ℂ) (i j : ι) :
    pderiv j (linearForms g i) = g j i • (1 : MvPowerSeries ι ℂ) := by
  classical
  simp [linearForms, map_sum, pderiv_X, Pi.single_apply]

/-- The chain rule for the substitution `f(z) ↦ f(gᵀz)`, on polynomials. -/
private theorem pderiv_subst_linearForms_coe (g : Matrix ι ι ℂ) (j : ι) (p : MvPolynomial ι ℂ) :
    pderiv j (subst (linearForms g) (p : MvPowerSeries ι ℂ)) =
      ∑ k, g j k • subst (linearForms g) (pderiv k (p : MvPowerSeries ι ℂ)) := by
  classical
  rw [← coe_substAlgHom (hasSubst_linearForms g)]
  set S := substAlgHom (R := ℂ) (hasSubst_linearForms g)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hSC : S (MvPowerSeries.C a) = MvPowerSeries.C a := by
      simp only [S, coe_substAlgHom, subst_C]
    simp [MvPolynomial.coe_C, hSC]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
    have hSX : S (X i) = linearForms g i := substAlgHom_X _ i
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hSX, Derivation.leibniz, ih,
      pderiv_linearForms]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, map_mul, hSX, pderiv_X, Pi.single_apply,
      apply_ite S, map_zero, mul_ite, mul_one, mul_zero, Finset.mul_sum]
    simp only [smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mul_smul_comm, mul_one]

/-- Power series that agree in degree `∣m∣` have substitutions with the same coefficient at `m`. -/
theorem coeff_subst_linearForms_congr (g : Matrix ι ι ℂ) {f f' : MvPowerSeries ι ℂ}
    {m : ι →₀ ℕ} (h : ∀ d : ι →₀ ℕ, d.degree = m.degree →
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d f') :
    MvPowerSeries.coeff m (subst (linearForms g) f) =
      MvPowerSeries.coeff m (subst (linearForms g) f') := by
  classical
  rw [coeff_subst_linearForms, coeff_subst_linearForms]
  exact Finset.sum_congr rfl fun d hd => by rw [h d (mem_finsuppAntidiag_univ.1 hd)]

omit [Fintype ι] in
private theorem degree_add_single (m : ι →₀ ℕ) (j : ι) :
    (m + Finsupp.single j 1).degree = m.degree + 1 := by
  rw [map_add, Finsupp.degree_single]

/-- **The chain rule** for the substitution `f(z) ↦ f(gᵀz)`:
`∂ⱼ [f(gᵀz)] = Σ_k g_jk (∂_k f)(gᵀz)`. -/
theorem pderiv_subst_linearForms (g : Matrix ι ι ℂ) (j : ι) (f : MvPowerSeries ι ℂ) :
    pderiv j (subst (linearForms g) f) = ∑ k, g j k • subst (linearForms g) (pderiv k f) := by
  classical
  ext m
  have hP : ∀ d : ι →₀ ℕ, d.degree < m.degree + 2 → MvPowerSeries.coeff d f =
      MvPowerSeries.coeff d (truncTotal (m.degree + 2) f : MvPowerSeries ι ℂ) := fun d hd => by
    rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]
  have h1 : MvPowerSeries.coeff m (pderiv j (subst (linearForms g) f)) =
      MvPowerSeries.coeff m (pderiv j (subst (linearForms g)
        (truncTotal (m.degree + 2) f : MvPowerSeries ι ℂ))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_subst_linearForms_congr g fun d hd => hP d (by
      rw [hd, degree_add_single]; omega)]
  have h2 : ∀ k, MvPowerSeries.coeff m (subst (linearForms g) (pderiv k f)) =
      MvPowerSeries.coeff m (subst (linearForms g)
        (pderiv k (truncTotal (m.degree + 2) f : MvPowerSeries ι ℂ))) := fun k =>
    coeff_subst_linearForms_congr g fun d hd => by
      rw [coeff_pderiv, coeff_pderiv, hP _ (by rw [degree_add_single, hd]; omega)]
  rw [h1, pderiv_subst_linearForms_coe, map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [MvPowerSeries.coeff_smul,
    MvPowerSeries.coeff_smul, h2]

/-- **Theorem 4.** `aⱼ Γ(g) = Γ(g) (Σ_k g_jk a_k)` on the whole formal Fock space. -/
theorem annihilate_mul_secondQuant (g : Matrix ι ι ℂ) (j : ι) :
    annihilate j * secondQuant g = secondQuant g * ∑ k, g j k • annihilate k := by
  classical
  refine LinearMap.ext fun ψ => toBargmann.injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, toBargmann_annihilate_complex,
    toBargmann_secondQuant, pderiv_subst_linearForms, toBargmann_secondQuant, LinearMap.sum_apply,
    map_sum, ← coe_substAlgHom (hasSubst_linearForms g), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, map_smul, map_smul, toBargmann_annihilate_complex]

/-! ### Theorem 5: the adjoint -/

omit [Fintype ι] in
/-- `a_k† ∣m⟩ = √(m_k + 1) ∣m + e_k⟩`. -/
theorem create_single [DecidableEq ι] (k : ι) (m : ι →₀ ℕ) :
    create k (single m (1 : ℂ)) = sqrtC (m k + 1) • single (m + Finsupp.single k 1) 1 := by
  ext p
  simp only [coeff_create, coeff_smul, coeff_single]
  by_cases hp : p = m + Finsupp.single k 1
  · subst hp
    simp
  · rw [ite_eq_right hp, smul_zero]
    split_ifs with h h'
    · exact absurd (by rw [← h', sub_single_add_single h]) hp
    · exact smul_zero _
    · rfl

omit [Fintype ι] in
/-- `a_k ∣n⟩ = √(n_k) ∣n - e_k⟩`, and `0` if `n_k = 0`. -/
theorem annihilate_single [DecidableEq ι] (k : ι) (n : ι →₀ ℕ) :
    annihilate k (single n (1 : ℂ)) =
      if 0 < n k then sqrtC (n k) • single (n - Finsupp.single k 1) 1 else 0 := by
  ext p
  rw [coeff_annihilate, coeff_single]
  split_ifs with h1 h2 h2
  · subst h1
    simp
  · exfalso
    apply h2
    rw [← h1]
    simp
  · rw [smul_zero, coeff_smul, coeff_single, ite_eq_right fun h => h1 (by
      rw [h, sub_single_add_single h2]), smul_zero]
  · rw [smul_zero, coeff_zero]

/-- `(Γ(g) c∣n⟩)(m) = Γ(g)_{mn} c`. -/
theorem coeff_secondQuant_single [DecidableEq ι] (g : Matrix ι ι ℂ) (n m : ι →₀ ℕ) (c : ℂ) :
    (secondQuant g (single n c)).coeff m = matrixCoeff g m n * c := by
  have : single n c = c • single n (1 : ℂ) := by
    ext p
    simp [coeff_single]
  rw [this, map_smul, coeff_smul, smul_eq_mul, mul_comm, matrixCoeff]

/-- `(Γ(g)∣n⟩)(m) = Γ(g)_{mn}`. -/
theorem coeff_secondQuant_single_one [DecidableEq ι] (g : Matrix ι ι ℂ) (n m : ι →₀ ℕ) :
    (secondQuant g (single n 1)).coeff m = matrixCoeff g m n := rfl

/-- The recursion of the matrix elements given by Theorem 4 for the annihilation operators. -/
private theorem matrixCoeff_add_single [DecidableEq ι] (g : Matrix ι ι ℂ) (m n : ι →₀ ℕ) (i : ι) :
    sqrtC (m i + 1) * matrixCoeff g (m + Finsupp.single i 1) n =
      ∑ k, g i k * if 0 < n k then sqrtC (n k) * matrixCoeff g m (n - Finsupp.single k 1)
        else 0 := by
  have h := congrArg (fun T : Module.End ℂ (FormalFock ι ℂ) => (T (single n 1)).coeff m)
    (annihilate_mul_secondQuant g i)
  simp only [Module.End.mul_apply, coeff_annihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, coeff_sum, coeff_smul, annihilate_single, smul_eq_mul,
    coeff_secondQuant_single_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [map_smul, coeff_smul, smul_eq_mul, coeff_secondQuant_single_one]
  · rw [map_zero, coeff_zero]

/-- The recursion of the matrix elements given by Theorem 4 for the creation operators. -/
private theorem matrixCoeff_add_single' [DecidableEq ι] (g : Matrix ι ι ℂ) (m n : ι →₀ ℕ) (i : ι) :
    sqrtC (m i + 1) * matrixCoeff g n (m + Finsupp.single i 1) =
      ∑ k, g k i * if 0 < n k then sqrtC (n k) * matrixCoeff g (n - Finsupp.single k 1) m
        else 0 := by
  have h := congrArg (fun T : Module.End ℂ (FormalFock ι ℂ) => (T (single m 1)).coeff n)
    (secondQuant_mul_create g i)
  simp only [Module.End.mul_apply, create_single, map_smul, coeff_smul, smul_eq_mul,
    LinearMap.sum_apply, LinearMap.smul_apply, coeff_sum, coeff_create,
    coeff_secondQuant_single_one] at h
  exact h

open ComplexConjugate in
/-- **Theorem 5**, matrix form: `Γ(g*)_{nm} = conj(Γ(g)_{mn})`. -/
theorem matrixCoeff_conjTranspose [DecidableEq ι] (g : Matrix ι ι ℂ) (m n : ι →₀ ℕ) :
    matrixCoeff gᴴ n m = conj (matrixCoeff g m n) := by
  induction hd : m.degree generalizing m n with
  | zero =>
    rw [Finsupp.degree_eq_zero_iff] at hd
    subst hd
    rw [matrixCoeff, secondQuant_vacuum, coeff_single]
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left rfl, matrixCoeff, secondQuant_vacuum, coeff_single, ite_eq_left rfl, map_one]
    · rw [ite_eq_right hn, matrixCoeff_eq_zero_of_degree_ne, map_zero]
      rw [map_zero]
      exact fun h => hn ((Finsupp.degree_eq_zero_iff n).1 h.symm)
  | succ d ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm
    have hi' : 0 < m i := Nat.pos_of_ne_zero hi
    set m' := m - Finsupp.single i 1 with hm'
    have hmm : m = m' + Finsupp.single i 1 := (sub_single_add_single hi').symm
    have hd' : m'.degree = d := by
      rw [hmm, degree_add_single] at hd
      omega
    have h1 := matrixCoeff_add_single g m' n i
    have h2 := matrixCoeff_add_single' gᴴ m' n i
    rw [← hmm] at h1 h2
    have hs : sqrtC (m' i + 1) ≠ 0 := sqrtC_ne_zero (Nat.succ_pos _)
    have hc : conj (sqrtC (m' i + 1)) = sqrtC (m' i + 1) := Complex.conj_ofReal _
    apply mul_left_cancel₀ hs
    rw [h2, ← hc, ← map_mul, h1, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, map_mul, apply_ite conj, map_mul, map_zero, ih m' _ hd']
    simp only [RCLike.star_def, Complex.conj_ofReal, sqrtC]

omit [Fintype ι] in
/-- A vector supported in a finite set `s` is the finite sum `Σ_{m ∈ s} ψ(m) ∣m⟩`. -/
theorem eq_sum_single_of_support_subset [DecidableEq ι] {ψ : FormalFock ι ℂ} {s : Finset (ι →₀ ℕ)}
    (hs : Function.support ψ.coeff ⊆ s) : ψ = ∑ m ∈ s, ψ.coeff m • single m 1 := by
  ext n
  rw [coeff_sum]
  simp only [coeff_smul, coeff_single, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · by_contra h
    exact hn (hs (Function.mem_support.2 h))

/-- On a vector supported in a finite set `s`, `(Γ(g)φ)(n) = Σ_{m ∈ s} Γ(g)_{nm} φ(m)`. -/
theorem coeff_secondQuant_of_support_subset [DecidableEq ι] (g : Matrix ι ι ℂ) {φ : FormalFock ι ℂ}
    {s : Finset (ι →₀ ℕ)} (hs : Function.support φ.coeff ⊆ s) (n : ι →₀ ℕ) :
    (secondQuant g φ).coeff n = ∑ m ∈ s, matrixCoeff g n m * φ.coeff m := by
  conv_lhs => rw [eq_sum_single_of_support_subset hs]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, coeff_smul, smul_eq_mul, coeff_secondQuant_single_one, mul_comm]

open ComplexConjugate in
/-- The pairing `⟨φ, ψ⟩ = Σₙ conj(φ(n)) ψ(n)`, as Mathlib's `finsum` (`0` when the summand has
infinite support). It is used only for finitely supported `φ`; then it is a finite sum, and for
square-summable `ψ` it equals the inner product of `Γ_s`. -/
noncomputable def pairing {ι : Type*} (φ ψ : FormalFock ι ℂ) : ℂ :=
  ∑ᶠ n, conj (φ.coeff n) * ψ.coeff n

open ComplexConjugate in
/-- **Theorem 5.** For finitely supported `φ` and every `ψ`, `⟨φ, Γ(g)ψ⟩ = ⟨Γ(g*)φ, ψ⟩`. -/
theorem pairing_secondQuant (g : Matrix ι ι ℂ) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing φ (secondQuant g ψ) = pairing (secondQuant gᴴ φ) ψ := by
  classical
  set s := hφ.toFinset
  have hs : Function.support φ.coeff ⊆ s := by simp [s]
  set T := s.biUnion fun m : ι →₀ ℕ => Finset.finsuppAntidiag (Finset.univ : Finset ι) m.degree
  have hAT : ∀ m ∈ s, Finset.finsuppAntidiag Finset.univ m.degree ⊆ T := fun m hm =>
    Finset.subset_biUnion_of_mem
      (fun m : ι →₀ ℕ => Finset.finsuppAntidiag (Finset.univ : Finset ι) m.degree) hm
  -- the left side
  have hL : pairing φ (secondQuant g ψ) =
      ∑ m ∈ s, ∑ n ∈ T, conj (φ.coeff m) * (matrixCoeff g m n * ψ.coeff n) := by
    rw [pairing, finsum_eq_sum_of_support_subset _ fun m hm => hs (Function.mem_support.2
      fun h => (Function.mem_support.1 hm) (by rw [h, map_zero, zero_mul]))]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_secondQuant, Finset.mul_sum]
    refine Finset.sum_subset (hAT m hm) fun n _ hn => ?_
    rw [mem_finsuppAntidiag_univ] at hn
    rw [matrixCoeff_eq_zero_of_degree_ne g (Ne.symm hn), zero_mul, mul_zero]
  -- the right side
  have hR : pairing (secondQuant gᴴ φ) ψ =
      ∑ n ∈ T, ∑ m ∈ s, conj (φ.coeff m) * (matrixCoeff g m n * ψ.coeff n) := by
    have hsupp : Function.support (fun n => conj ((secondQuant gᴴ φ).coeff n) * ψ.coeff n) ⊆ T := by
      intro n hn
      rw [Function.mem_support, coeff_secondQuant_of_support_subset gᴴ hs] at hn
      obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        ((map_ne_zero (starRingEnd ℂ)).1 (left_ne_zero_of_mul hn))
      have hdeg : n.degree = m.degree := by
        by_contra hd
        exact left_ne_zero_of_mul hne (matrixCoeff_eq_zero_of_degree_ne _ hd)
      exact Finset.mem_coe.2 (hAT m hm (mem_finsuppAntidiag_univ.2 hdeg))
    rw [pairing, finsum_eq_sum_of_support_subset _ hsupp]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coeff_secondQuant_of_support_subset gᴴ hs, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, matrixCoeff_conjTranspose, Complex.conj_conj]
    ring
  rw [hL, hR, Finset.sum_comm]

/-! ### Theorem 6: unitarity -/

omit [Fintype ι] in
/-- On finitely many modes, a particle-number sector is finitely supported. -/
theorem finite_support_sector [Finite ι] (p : ℕ) (ψ : FormalFock ι ℂ) :
    (Function.support (sector p ψ).coeff).Finite := by
  classical
  have := Fintype.ofFinite ι
  refine (Finset.finsuppAntidiag (Finset.univ : Finset ι) p).finite_toSet.subset fun n hn => ?_
  rw [Function.mem_support, coeff_sector] at hn
  rw [Finset.mem_coe, mem_finsuppAntidiag_univ]
  by_contra h
  exact hn (by rw [ite_eq_right h])

omit [Fintype ι] in
/-- The squared norm regrouped by particle number: `‖ψ‖² = Σ_p ‖[ψ]_p‖²` in `[0, ∞]`. -/
theorem sqNorm_eq_tsum_sqNorm_sector (ψ : FormalFock ι ℂ) :
    sqNorm ψ = ∑' p, sqNorm (sector p ψ) := by
  simp only [sqNorm, coeff_sector]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun n => ?_
  rw [tsum_eq_single n.degree fun p hp => by rw [ite_eq_right (Ne.symm hp)]; simp,
    ite_eq_left rfl]

open ComplexConjugate in
omit [Fintype ι] in
/-- For a finitely supported vector, `‖φ‖² = ⟨φ, φ⟩`. -/
theorem sqNorm_eq_ofReal_re_pairing {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) :
    sqNorm φ = ENNReal.ofReal (pairing φ φ).re := by
  have hs : Function.support φ.coeff ⊆ hφ.toFinset := by simp
  have hsupp : Function.support (fun n => conj (φ.coeff n) * φ.coeff n) ⊆ hφ.toFinset :=
    fun n hn => hs (Function.mem_support.2 fun h => (Function.mem_support.1 hn) (by
      rw [h, mul_zero]))
  rw [pairing, finsum_eq_sum_of_support_subset _ hsupp, sqNorm,
    tsum_eq_sum (s := hφ.toFinset) fun n hn => by
      rw [Function.notMem_support.1 fun h => hn (hs h)]; simp, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg fun n _ => by
      rw [Complex.conj_mul']; norm_cast; positivity]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, ENNReal.ofReal_pow
    (norm_nonneg _), ofReal_norm]
  rfl

/-- `Γ(𝒰*) Γ(𝒰) = 1` for a unitary matrix `𝒰`. -/
theorem secondQuant_conjTranspose_mul_self [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * secondQuant (U : Matrix ι ι ℂ) = 1 := by
  rw [← secondQuant_mul, ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self,
    secondQuant_one]

/-- `Γ(𝒰) Γ(𝒰*) = 1` for a unitary matrix `𝒰`. -/
theorem secondQuant_mul_conjTranspose_self [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    secondQuant (U : Matrix ι ι ℂ) * secondQuant (U : Matrix ι ι ℂ)ᴴ = 1 := by
  rw [← secondQuant_mul, ← Matrix.star_eq_conjTranspose, Unitary.mul_star_self_of_mem U.2,
    secondQuant_one]

/-- For a unitary matrix `𝒰`, `φ ∈ Γ(𝒰) M` if and only if `Γ(𝒰*) φ ∈ M`. -/
theorem mem_map_secondQuant_iff [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (M : Submodule ℂ (FormalFock ι ℂ)) (φ : FormalFock ι ℂ) :
    φ ∈ M.map (secondQuant (U : Matrix ι ι ℂ)) ↔
      secondQuant ((star U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) φ ∈ M := by
  rw [Unitary.coe_star, Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    rwa [← Module.End.mul_apply, secondQuant_conjTranspose_mul_self, Module.End.one_apply]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← Module.End.mul_apply, secondQuant_mul_conjTranspose_self, Module.End.one_apply]

/-- **Theorem 6(a).** `Γ(𝒰)` preserves the squared norm of every formal vector, in `[0, ∞]`. -/
theorem sqNorm_secondQuant [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (ψ : FormalFock ι ℂ) :
    sqNorm (secondQuant (U : Matrix ι ι ℂ) ψ) = sqNorm ψ := by
  rw [sqNorm_eq_tsum_sqNorm_sector, sqNorm_eq_tsum_sqNorm_sector ψ]
  refine tsum_congr fun p => ?_
  have hχ := finite_support_sector p ψ
  have hΓχ := finite_support_secondQuant (U : Matrix ι ι ℂ) hχ
  rw [← secondQuant_sector, sqNorm_eq_ofReal_re_pairing hΓχ, sqNorm_eq_ofReal_re_pairing hχ,
    pairing_secondQuant _ hΓχ, ← Module.End.mul_apply, secondQuant_conjTranspose_mul_self,
    Module.End.one_apply]

end BosonicLean.Fock.FormalFock

namespace BosonicLean.Fock.FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι]

/-- `Γ(𝒰)` maps a vector of `Γ_s` to a square-summable vector. -/
theorem memlp_secondQuant [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (ψ : FockSpace ι) :
    Memℓp (secondQuant (U : Matrix ι ι ℂ) (toFormal ψ)).coeff 2 := by
  obtain ⟨φ, hφ⟩ := (mem_range_toFormal_iff _).2
    ((sqNorm_secondQuant U (toFormal ψ)).symm ▸ (mem_range_toFormal_iff _).1 ⟨ψ, rfl⟩)
  rw [← hφ]
  exact lp.memℓp φ

/-- **Theorem 6(b).** The unitary `𝖴_𝒰` of the Fock space `Γ_s`: the restriction of `Γ(𝒰)`. -/
noncomputable def secondQuantUnitary [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    FockSpace ι ≃ₗᵢ[ℂ] FockSpace ι where
  toFun ψ := ⟨(secondQuant (U : Matrix ι ι ℂ) (toFormal ψ)).coeff, memlp_secondQuant U ψ⟩
  invFun ψ := ⟨(secondQuant ((star U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
    (toFormal ψ)).coeff, memlp_secondQuant (star U) ψ⟩
  map_add' ψ φ := by
    ext n
    simp [map_add]
    rfl
  map_smul' c ψ := by
    ext n
    simp [map_smul]
  left_inv ψ := by
    refine toFormal_injective ?_
    change secondQuant _ (secondQuant _ (toFormal ψ)) = toFormal ψ
    rw [← Module.End.mul_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      secondQuant_conjTranspose_mul_self, Module.End.one_apply]
  right_inv ψ := by
    refine toFormal_injective ?_
    change secondQuant _ (secondQuant _ (toFormal ψ)) = toFormal ψ
    rw [← Module.End.mul_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      secondQuant_mul_conjTranspose_self, Module.End.one_apply]
  norm_map' ψ := by
    let x : FockSpace ι :=
      ⟨(secondQuant (U : Matrix ι ι ℂ) (toFormal ψ)).coeff, memlp_secondQuant U ψ⟩
    change ‖x‖ = ‖ψ‖
    have h := sqNorm_secondQuant U (toFormal ψ)
    rw [show secondQuant (U : Matrix ι ι ℂ) (toFormal ψ) = toFormal x from rfl, sqNorm_toFormal,
      sqNorm_toFormal, ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Theorem 6(b).** `𝖴_𝒰` is the restriction of `Γ(𝒰)` to `Γ_s`. -/
theorem toFormal_secondQuantUnitary [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (ψ : FockSpace ι) :
    toFormal (secondQuantUnitary U ψ) = secondQuant (U : Matrix ι ι ℂ) (toFormal ψ) := rfl

/-- **Theorem 6(b).** `Γ(𝒰)` maps `Γ_s` onto `Γ_s`. -/
theorem map_secondQuant_range_toFormal [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (LinearMap.range (toFormal (ι := ι))).map (secondQuant (U : Matrix ι ι ℂ)) =
      LinearMap.range toFormal := by
  ext φ
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨secondQuantUnitary U ψ, rfl⟩
  · rintro ⟨ψ, rfl⟩
    refine ⟨toFormal ((secondQuantUnitary U).symm ψ), ⟨_, rfl⟩, ?_⟩
    rw [← toFormal_secondQuantUnitary, LinearIsometryEquiv.apply_symm_apply]

/-- **Theorem 6(b).** `𝖴_𝒰⁻¹ = 𝖴_{𝒰*}`. -/
theorem secondQuantUnitary_symm [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (secondQuantUnitary U).symm = secondQuantUnitary (star U) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- `𝖴_1 = 1`. -/
theorem secondQuantUnitary_one [DecidableEq ι] : secondQuantUnitary (1 : Matrix.unitaryGroup ι ℂ) =
    LinearIsometryEquiv.refl ℂ (FockSpace ι) := by
  ext ψ : 1
  refine toFormal_injective ?_
  rw [toFormal_secondQuantUnitary, Matrix.UnitaryGroup.one_val, secondQuant_one]
  rfl

/-- **Theorem 6(b).** `𝖴_{𝒰𝒱} = 𝖴_𝒰 𝖴_𝒱`. -/
theorem secondQuantUnitary_mul [DecidableEq ι] (U V : Matrix.unitaryGroup ι ℂ) :
    secondQuantUnitary (U * V) = (secondQuantUnitary V).trans (secondQuantUnitary U) := by
  ext ψ : 1
  refine toFormal_injective ?_
  rw [toFormal_secondQuantUnitary, Matrix.UnitaryGroup.mul_val, secondQuant_mul]
  rfl

/-- **Theorem 6(b).** The group homomorphism `𝒰 ↦ 𝖴_𝒰` from `U(ι)` to the unitary group of `Γ_s`.
It is strongly continuous (`continuous_secondQuantRep_apply`, Theorem 6(d)), hence a unitary
representation. -/
noncomputable def secondQuantRep [DecidableEq ι] :
    Matrix.unitaryGroup ι ℂ →* unitary (FockSpace ι →L[ℂ] FockSpace ι) where
  toFun U := Unitary.linearIsometryEquiv.symm (secondQuantUnitary U)
  map_one' := by
    rw [secondQuantUnitary_one]
    exact map_one Unitary.linearIsometryEquiv.symm
  map_mul' U V := by
    rw [secondQuantUnitary_mul, ← map_mul]
    rfl

/-- The representation acts by `𝖴_𝒰`. -/
theorem secondQuantRep_apply [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (ψ : FockSpace ι) :
    (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ = secondQuantUnitary U ψ := rfl

/-- **Theorem 6(b).** The adjoint of `𝖴_𝒰` is `𝖴_{𝒰*}`. -/
theorem star_secondQuantRep [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    star (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) = secondQuantRep (star U) := by
  rw [← Unitary.coe_star, Unitary.star_eq_inv, Unitary.star_eq_inv, map_inv]

/-! #### Theorem 6(d): strong continuity -/

/-- The matrix element `Γ(g)_{mn}` is a continuous function of `g`. -/
theorem continuous_matrixCoeff [DecidableEq ι] (m n : ι →₀ ℕ) :
    Continuous fun g : Matrix ι ι ℂ => matrixCoeff g m n := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_matrixCoeff m n
  simp only [hP]
  exact (MvPolynomial.continuous_eval P).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

omit [Fintype ι] in
/-- The basis vector `∣m⟩` of `Γ_s` is the number state `∣m⟩`. -/
theorem toFormal_lpSingle [DecidableEq ι] (m : ι →₀ ℕ) :
    toFormal (lp.single 2 m (1 : ℂ) : FockSpace ι) = single m 1 := by
  classical
  ext n
  rw [coeff_toFormal, lp.single_apply, coeff_single, Pi.single_apply]

/-- On a number state, `𝖴_𝒰 ∣m⟩ = Σ_{∣n∣ = ∣m∣} Γ(𝒰)_{nm} ∣n⟩`. -/
theorem secondQuantUnitary_lpSingle [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (m : ι →₀ ℕ) :
    secondQuantUnitary U (lp.single 2 m 1) =
      ∑ n ∈ Finset.finsuppAntidiag Finset.univ m.degree,
        matrixCoeff (U : Matrix ι ι ℂ) n m • lp.single 2 n (1 : ℂ) := by
  refine toFormal_injective ?_
  ext n'
  rw [toFormal_secondQuantUnitary, toFormal_lpSingle, coeff_secondQuant_single_one, map_sum,
    coeff_sum]
  simp only [map_smul, FormalFock.coeff_smul, toFormal_lpSingle, coeff_single, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_finsuppAntidiag_univ] at h
    exact matrixCoeff_eq_zero_of_degree_ne _ h

/-- **Theorem 6(d).** The representation is strongly continuous: for every `ψ ∈ Γ_s`,
`𝒰 ↦ 𝖴_𝒰 ψ` is continuous. -/
theorem continuous_secondQuantRep_apply [DecidableEq ι] (ψ : FockSpace ι) :
    Continuous fun U : Matrix.unitaryGroup ι ℂ =>
      (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ := by
  simp only [secondQuantRep_apply]
  set D := Submodule.span ℂ (Set.range fun m : ι →₀ ℕ => lp.single 2 m (1 : ℂ))
  have hD : ∀ χ ∈ D, Continuous fun U : Matrix.unitaryGroup ι ℂ => secondQuantUnitary U χ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      simp only [secondQuantUnitary_lpSingle]
      exact continuous_finsetSum _ fun n _ =>
        ((continuous_matrixCoeff n m).comp continuous_subtype_val).smul continuous_const
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul]; exact hx.const_smul c
  have hequi : Equicontinuous fun U : Matrix.unitaryGroup ι ℂ => ⇑(secondQuantUnitary U) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun U =>
      (secondQuantUnitary U).lipschitzWith).equicontinuous
  refine continuous_iff_continuousAt.2 fun U₀ => ?_
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := nhds U₀)
    (secondQuantUnitary U₀).continuous
  have hsub : closure (D : Set (FockSpace ι)) ⊆ _ :=
    hclosed.closure_subset_iff.2 fun χ hχ => (hD χ hχ).continuousAt
  exact hsub ((dense_span_single (ι := ι)).closure_eq ▸ Set.mem_univ ψ)

end BosonicLean.Fock.FockSpace

namespace BosonicLean.Fock.FormalFock

open ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-! ### Theorem 6(c): conjugation of the ladder and number operators -/

/-- **Theorem 6(c)**, the paper's (29) and (A26), which agree: `Γ(𝒰*) aⱼ Γ(𝒰) = Σ_k 𝒰_jk a_k`. -/
theorem secondQuant_conjTranspose_mul_annihilate_mul [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * annihilate j * secondQuant (U : Matrix ι ι ℂ) =
      ∑ k, (U : Matrix ι ι ℂ) j k • annihilate k := by
  rw [mul_assoc, annihilate_mul_secondQuant, ← mul_assoc, secondQuant_conjTranspose_mul_self,
    one_mul]

/-- **Theorem 6(c).** `Γ(𝒰*) aⱼ† Γ(𝒰) = Σ_k conj(𝒰_jk) a_k†`. -/
theorem secondQuant_conjTranspose_mul_create_mul [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (j : ι) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * create j * secondQuant (U : Matrix ι ι ℂ) =
      ∑ k, conj ((U : Matrix ι ι ℂ) j k) • create k := by
  rw [secondQuant_mul_create, mul_assoc, secondQuant_conjTranspose_mul_self, mul_one]
  rfl

/-- **Theorem 6(c)**, the inverse conjugation: `Γ(𝒰) aⱼ† Γ(𝒰*) = Σ_k 𝒰_kj a_k†`. It follows
from the paper's (29) = (A26) (`secondQuant_conjTranspose_mul_annihilate_mul`) and is not in the
paper. -/
theorem secondQuant_mul_create_mul_conjTranspose [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (j : ι) :
    secondQuant (U : Matrix ι ι ℂ) * create j * secondQuant (U : Matrix ι ι ℂ)ᴴ =
      ∑ k, (U : Matrix ι ι ℂ) k j • create k := by
  rw [secondQuant_mul_create, mul_assoc, secondQuant_mul_conjTranspose_self, mul_one]

/-- **Theorem 6(c).** `Γ(𝒰) n_tot Γ(𝒰*) = n_tot`. -/
theorem secondQuant_mul_totalNumber_mul_conjTranspose [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    secondQuant (U : Matrix ι ι ℂ) * totalNumber * secondQuant (U : Matrix ι ι ℂ)ᴴ =
      totalNumber := by
  rw [(commute_secondQuant_totalNumber _).eq, mul_assoc, secondQuant_mul_conjTranspose_self,
    mul_one]

end BosonicLean.Fock.FormalFock

/-! ### The general Leibniz rule -/

/-- **The general Leibniz rule** for a derivation of a commutative algebra:
`Dⁿ (a b) = Σ_{i+j=n} C(n, i) Dⁱ a Dʲ b` (Lemma 8(b); the Lie version is
`LieDerivation.iterate_apply_lie`). -/
theorem Derivation.iterate_apply_mul {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (D : Derivation R A A) (n : ℕ) (a b : A) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 • ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := A)
      (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, smul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm, mul_comm]

namespace BosonicLean.Fock.FormalFock

open ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-! ### Definition 7: the generator `dΓ(h)` and the coefficientwise exponential -/

/-- The **generator** `dΓ(h) = Σ_{jk} h_jk aⱼ† a_k` of the second quantization. -/
noncomputable def dSecondQuant (h : Matrix ι ι ℂ) : Module.End ℂ (FormalFock ι ℂ) :=
  ∑ j, ∑ k, h j k • (create j * annihilate k)

/-- The **coefficientwise exponential** of a linear map `T` of the formal Fock space:
`(e^T ψ)(n) = Σ_r (T^r ψ)(n) / r!` where this series converges absolutely, and `0` otherwise (the
value of Mathlib's `tsum` on a non-summable series). Every statement in this library applies it
where the coefficient series converge absolutely: to `T = dΓ(h)` (or `i dΓ(M) = dΓ(iM)`,
`dSecondQuant_smul`; Lemma 8(c), `summable_norm_coeff_dSecondQuant_pow`), and, on vectors of `Γ_s`,
to the lowering operators `-ᾱ·a` and `½ Σⱼ τ̄ⱼ aⱼ²` (`|τⱼ| < 1`) in the normal-ordered forms of the
displacement and squeezing operators (`FockSpace.summable_coeffExp_lowerDisp`,
`FockSpace.summable_coeffExp_lowerSqueeze`). -/
noncomputable def coeffExp (T : Module.End ℂ (FormalFock ι ℂ)) (ψ : FormalFock ι ℂ) :
    FormalFock ι ℂ :=
  ⟨fun n => ∑' r : ℕ, ((r.factorial : ℂ)⁻¹) * ((T ^ r) ψ).coeff n⟩

omit [Fintype ι] in
/-- The coefficients of the coefficientwise exponential. -/
theorem coeff_coeffExp (T : Module.End ℂ (FormalFock ι ℂ)) (ψ : FormalFock ι ℂ)
    (n : ι →₀ ℕ) :
    (coeffExp T ψ).coeff n = ∑' r : ℕ, ((r.factorial : ℂ)⁻¹) * ((T ^ r) ψ).coeff n := rfl

/-! ### Lemma 8: the generator in the Bargmann picture -/

/-- Auxiliary for Lemma 8 and Theorem 9: the derivation `δ_h = Σ_{jk} h_jk zⱼ ∂_k` of `ℂ[[z]]`,
the Bargmann image of `dΓ(h)` (`toBargmann_dSecondQuant`), used for the Leibniz rule. -/
private noncomputable def bargmannDeriv (h : Matrix ι ι ℂ) :
    Derivation ℂ (MvPowerSeries ι ℂ) (MvPowerSeries ι ℂ) :=
  ∑ j, ∑ k, h j k • (X j : MvPowerSeries ι ℂ) • pderiv k

/-- `δ_h f = Σ_{jk} h_jk zⱼ ∂_k f`. -/
private theorem bargmannDeriv_apply (h : Matrix ι ι ℂ) (f : MvPowerSeries ι ℂ) :
    bargmannDeriv h f = ∑ j, ∑ k, h j k • (X j * pderiv k f) := by
  classical
  simp [bargmannDeriv]

/-- **Lemma 8(a).** In the Bargmann picture `dΓ(h)` is `Σ_{jk} h_jk zⱼ ∂_k`:
`𝔅 dΓ(h) ψ = Σ_{jk} h_jk zⱼ ∂_k 𝔅ψ`. -/
theorem toBargmann_dSecondQuant (h : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) :
    toBargmann (dSecondQuant h ψ) =
      ∑ j, ∑ k, h j k • ((X j : MvPowerSeries ι ℂ) * pderiv k (toBargmann ψ)) := by
  classical
  rw [dSecondQuant, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, map_smul, Module.End.mul_apply, toBargmann_create,
    toBargmann_annihilate_complex]

/-- `𝔅 dΓ(h) = δ_h 𝔅`. -/
private theorem toBargmann_dSecondQuant_eq_bargmannDeriv (h : Matrix ι ι ℂ)
    (ψ : FormalFock ι ℂ) :
    toBargmann (dSecondQuant h ψ) = bargmannDeriv h (toBargmann ψ) := by
  rw [toBargmann_dSecondQuant, bargmannDeriv_apply]

/-- `δ_h zₗ = (hᵀ z)ₗ`. -/
private theorem bargmannDeriv_X (h : Matrix ι ι ℂ) (l : ι) :
    bargmannDeriv h (X l) = linearForms h l := by
  classical
  rw [bargmannDeriv_apply, linearForms]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [pderiv_X, Pi.single_apply]

/-- The coefficients of `δ_h f`. -/
private theorem coeff_bargmannDeriv (h : Matrix ι ι ℂ) (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (bargmannDeriv h f) = ∑ j, ∑ k, h j k *
      if 0 < n j then MvPowerSeries.coeff (n - Finsupp.single j 1 + Finsupp.single k 1) f *
        (((n - Finsupp.single j 1 : ι →₀ ℕ) k : ℂ) + 1) else 0 := by
  classical
  rw [bargmannDeriv_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPowerSeries.coeff_smul, coeff_X_mul_eq]
  split_ifs
  · rw [coeff_pderiv]
  · rfl

omit [Fintype ι] in
private theorem degree_sub_single_add_single {n : ι →₀ ℕ} {j : ι} (hj : 0 < n j) (k : ι) :
    (n - Finsupp.single j 1 + Finsupp.single k 1).degree = n.degree := by
  rw [map_add, Finsupp.degree_single, degree_sub_single_add_one hj]

/-- `δ_h` preserves degrees: the coefficients of `δ_h f` in degree `p` depend only on those of `f`
in degree `p`. -/
private theorem coeff_bargmannDeriv_congr (h : Matrix ι ι ℂ) {f f' : MvPowerSeries ι ℂ} {p : ℕ}
    (hf : ∀ m : ι →₀ ℕ, m.degree = p → MvPowerSeries.coeff m f = MvPowerSeries.coeff m f')
    {n : ι →₀ ℕ} (hn : n.degree = p) :
    MvPowerSeries.coeff n (bargmannDeriv h f) = MvPowerSeries.coeff n (bargmannDeriv h f') := by
  classical
  rw [coeff_bargmannDeriv, coeff_bargmannDeriv]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hj
  · rw [hf _ (by rw [degree_sub_single_add_single hj, hn])]
  · rfl

/-- The powers of `δ_h` preserve degrees. -/
private theorem coeff_bargmannDeriv_iterate_congr (h : Matrix ι ι ℂ) {f f' : MvPowerSeries ι ℂ}
    {p : ℕ}
    (hf : ∀ m : ι →₀ ℕ, m.degree = p → MvPowerSeries.coeff m f = MvPowerSeries.coeff m f')
    (r : ℕ) {n : ι →₀ ℕ} (hn : n.degree = p) :
    MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f) =
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f') := by
  classical
  induction r generalizing n with
  | zero => exact hf n hn
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact coeff_bargmannDeriv_congr h (fun _ hm => ih hm) hn

/-- `δ_h` commutes with taking homogeneous components. -/
private theorem bargmannDeriv_homogeneousComponent (h : Matrix ι ι ℂ) (p : ℕ)
    (f : MvPowerSeries ι ℂ) :
    bargmannDeriv h (homogeneousComponent p f) = homogeneousComponent p (bargmannDeriv h f) := by
  classical
  ext n
  rw [coeff_homogeneousComponent]
  split_ifs with hn
  · exact coeff_bargmannDeriv_congr h (fun m hm => by
      rw [coeff_homogeneousComponent, ite_eq_left hm]) hn
  · rw [coeff_bargmannDeriv]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hj
    · have hd : (n - Finsupp.single j 1 + Finsupp.single k 1).degree ≠ p := by
        rw [degree_sub_single_add_single hj]
        exact hn
      rw [coeff_homogeneousComponent, ite_eq_right hd, zero_mul, mul_zero]
    · rw [mul_zero]

/-- **Lemma 8(a).** `dΓ(h)` maps every sector into itself. -/
theorem dSecondQuant_sector (h : Matrix ι ι ℂ) (p : ℕ) (ψ : FormalFock ι ℂ) :
    dSecondQuant h (sector p ψ) = sector p (dSecondQuant h ψ) := by
  classical
  apply toBargmann.injective
  rw [toBargmann_dSecondQuant_eq_bargmannDeriv, toBargmann_sector, toBargmann_sector,
    toBargmann_dSecondQuant_eq_bargmannDeriv,
    bargmannDeriv_homogeneousComponent]

/-- **Lemma 8(a).** On the one-particle sector `dΓ(h)` is `h`: `dΓ(h)∣eⱼ⟩ = Σ_k h_kj ∣e_k⟩`. -/
theorem dSecondQuant_single_one [DecidableEq ι] (h : Matrix ι ι ℂ) (j : ι) :
    dSecondQuant h (single (Finsupp.single j 1) 1) =
      ∑ k, h k j • single (Finsupp.single k 1) (1 : ℂ) := by
  apply toBargmann.injective
  rw [toBargmann_dSecondQuant_eq_bargmannDeriv, toBargmann_single_one, bargmannDeriv_X, map_sum]
  simp only [map_smul, toBargmann_single_one, linearForms]

/-- **Lemma 8(a).** `δ_h zₗ = (hᵀ z)ₗ`, in the Bargmann picture: `𝔅 dΓ(h)∣eₗ⟩ = (hᵀ z)ₗ`. -/
theorem toBargmann_dSecondQuant_single_one [DecidableEq ι] (h : Matrix ι ι ℂ) (l : ι) :
    toBargmann (dSecondQuant h (single (Finsupp.single l 1) 1)) = linearForms h l := by
  rw [toBargmann_dSecondQuant_eq_bargmannDeriv, toBargmann_single_one, bargmannDeriv_X]

end BosonicLean.Fock.FormalFock

namespace BosonicLean.Fock.FormalFock

variable {ι : Type*} [Fintype ι]

/-! ### Lemma 8(c): the bound and absolute convergence -/

omit [Fintype ι] in
private theorem apply_sub_single_add_one_le {n : ι →₀ ℕ} {j : ι} (hj : 0 < n j) (k : ι) :
    (n - Finsupp.single j 1 : ι →₀ ℕ) k + 1 ≤ n.degree := by
  have h := Finsupp.le_degree k (n - Finsupp.single j 1 + Finsupp.single k 1)
  rw [degree_sub_single_add_single hj, Finsupp.add_apply, Finsupp.single_eq_same] at h
  exact h

private theorem norm_coeff_bargmannDeriv_le (h : Matrix ι ι ℂ) {g : MvPowerSeries ι ℂ} {p : ℕ}
    {B : ℝ} (hg : ∀ m : ι →₀ ℕ, m.degree = p → ‖MvPowerSeries.coeff m g‖ ≤ B)
    {n : ι →₀ ℕ} (hn : n.degree = p) :
    ‖MvPowerSeries.coeff n (bargmannDeriv h g)‖ ≤ (p * ∑ j, ∑ k, ‖h j k‖) * B := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg n hn)
  rw [coeff_bargmannDeriv]
  calc _ ≤ ∑ j, ∑ k, ‖h j k‖ * (p * B) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        split_ifs with hj
        · have h1 := hg (n - Finsupp.single j 1 + Finsupp.single k 1)
            (by rw [degree_sub_single_add_single hj k, hn])
          have h3 := apply_sub_single_add_one_le hj k
          have h2 : ‖(((n - Finsupp.single j 1 : ι →₀ ℕ) k : ℂ) + 1)‖ ≤ p := by
            rw [← hn, show (((n - Finsupp.single j 1 : ι →₀ ℕ) k : ℂ) + 1) =
              (((n - Finsupp.single j 1 : ι →₀ ℕ) k + 1 : ℕ) : ℂ) by push_cast; ring,
              Complex.norm_natCast]
            exact_mod_cast h3
          rw [norm_mul, mul_comm (p : ℝ)]
          exact mul_le_mul h1 h2 (norm_nonneg _) hB
        · rw [norm_zero]
          positivity
    _ = (p * ∑ j, ∑ k, ‖h j k‖) * B := by
        simp only [← Finset.sum_mul]
        ring

/-- If `|[z^m] f| ≤ C` for all `m` of degree `p`, then `|[z^n] δ_h^r f| ≤ (p ‖h‖₁)^r C` for every
`n` of degree `p`. -/
private theorem norm_coeff_bargmannDeriv_iterate_le (h : Matrix ι ι ℂ) {f : MvPowerSeries ι ℂ}
    {p : ℕ}
    {C : ℝ} (hf : ∀ m : ι →₀ ℕ, m.degree = p → ‖MvPowerSeries.coeff m f‖ ≤ C) (r : ℕ)
    {n : ι →₀ ℕ} (hn : n.degree = p) :
    ‖MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f)‖ ≤
      ((p : ℝ) * ∑ j, ∑ k, ‖h j k‖) ^ r * C := by
  classical
  induction r generalizing n with
  | zero => simpa using hf n hn
  | succ r ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_comm (_ ^ r), mul_assoc]
    exact norm_coeff_bargmannDeriv_le h (fun _ hm => ih hm) hn

/-- `|[z^n] δ_h^r f| ≤ (∣n∣ ‖h‖₁)^r max_{∣m∣ = ∣n∣} |[z^m] f|`. -/
private theorem norm_coeff_bargmannDeriv_iterate_le_sup' [DecidableEq ι] (h : Matrix ι ι ℂ)
    (f : MvPowerSeries ι ℂ) (r : ℕ) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f)‖ ≤
      ((n.degree : ℝ) * ∑ j, ∑ k, ‖h j k‖) ^ r *
        (Finset.finsuppAntidiag Finset.univ n.degree).sup' ⟨n, mem_finsuppAntidiag_univ.2 rfl⟩
          fun m => ‖MvPowerSeries.coeff m f‖ :=
  norm_coeff_bargmannDeriv_iterate_le h (fun _ hm =>
    Finset.le_sup' (fun m => ‖MvPowerSeries.coeff m f‖) (mem_finsuppAntidiag_univ.2 hm)) r rfl

/-- The series `Σ_r [z^n] δ_h^r f / r!` converges absolutely. -/
private theorem summable_norm_coeff_bargmannDeriv_iterate (h : Matrix ι ι ℂ) (f : MvPowerSeries ι ℂ)
    (n : ι →₀ ℕ) :
    Summable fun r : ℕ =>
      ‖((r.factorial : ℂ)⁻¹) * MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f)‖ := by
  classical
  set K : ℝ := (n.degree : ℝ) * ∑ j, ∑ k, ‖h j k‖
  set C := (Finset.finsuppAntidiag Finset.univ n.degree).sup' ⟨n, mem_finsuppAntidiag_univ.2 rfl⟩
    fun m => ‖MvPowerSeries.coeff m f‖
  refine Summable.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => ?_)
    ((Real.summable_pow_div_factorial K).mul_right C)
  rw [norm_mul, norm_inv, Complex.norm_natCast, div_mul_eq_mul_div, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_coeff_bargmannDeriv_iterate_le_sup' h f r n)
    (by positivity)

/-- `𝔅 dΓ(h)^r = δ_h^r 𝔅`. -/
private theorem toBargmann_dSecondQuant_pow (h : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) (r : ℕ) :
    toBargmann ((dSecondQuant h ^ r) ψ) = (⇑(bargmannDeriv h))^[r] (toBargmann ψ) := by
  classical
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, toBargmann_dSecondQuant_eq_bargmannDeriv, ih,
      Function.iterate_succ_apply']

/-- `(dΓ(h)^r ψ)(n) = √(n!) [zⁿ] δ_h^r 𝔅ψ`. -/
private theorem coeff_dSecondQuant_pow (h : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) (r : ℕ)
    (n : ι →₀ ℕ) :
    ((dSecondQuant h ^ r) ψ).coeff n =
      sqrtFactorial n * MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (toBargmann ψ)) := by
  classical
  rw [← toBargmann.symm_apply_apply ((dSecondQuant h ^ r) ψ), toBargmann_dSecondQuant_pow,
    coeff_toBargmann_symm]

/-- **Lemma 8(c).** If `|[z^m] 𝔅ψ| ≤ C` for all `m` of degree `p`, then
`|[z^n] 𝔅 dΓ(h)^r ψ| ≤ (p ‖h‖₁)^r C` for every `r` and every `n` of degree `p`, with
`‖h‖₁ = Σ_{jk} |h_jk|`. -/
theorem norm_coeff_toBargmann_dSecondQuant_pow_le (h : Matrix ι ι ℂ) {ψ : FormalFock ι ℂ}
    {p : ℕ} {C : ℝ}
    (hψ : ∀ m : ι →₀ ℕ, m.degree = p → ‖MvPowerSeries.coeff m (toBargmann ψ)‖ ≤ C) (r : ℕ)
    {n : ι →₀ ℕ} (hn : n.degree = p) :
    ‖MvPowerSeries.coeff n (toBargmann ((dSecondQuant h ^ r) ψ))‖ ≤
      ((p : ℝ) * ∑ j, ∑ k, ‖h j k‖) ^ r * C := by
  rw [toBargmann_dSecondQuant_pow]
  exact norm_coeff_bargmannDeriv_iterate_le h hψ r hn

/-- **Lemma 8(c)**, with the maximum:
`|[z^n] 𝔅 dΓ(h)^r ψ| ≤ (∣n∣ ‖h‖₁)^r max_{∣m∣ = ∣n∣} |[z^m] 𝔅ψ|`. -/
theorem norm_coeff_toBargmann_dSecondQuant_pow_le_sup' [DecidableEq ι] (h : Matrix ι ι ℂ)
    (ψ : FormalFock ι ℂ) (r : ℕ) (n : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff n (toBargmann ((dSecondQuant h ^ r) ψ))‖ ≤
      ((n.degree : ℝ) * ∑ j, ∑ k, ‖h j k‖) ^ r *
        (Finset.finsuppAntidiag Finset.univ n.degree).sup' ⟨n, mem_finsuppAntidiag_univ.2 rfl⟩
          fun m => ‖MvPowerSeries.coeff m (toBargmann ψ)‖ := by
  rw [toBargmann_dSecondQuant_pow]
  exact norm_coeff_bargmannDeriv_iterate_le_sup' h _ r n

/-- **Lemma 8(c).** The series `Σ_r [z^n] 𝔅 dΓ(h)^r ψ / r!` converges absolutely. -/
theorem summable_norm_coeff_toBargmann_dSecondQuant_pow (h : Matrix ι ι ℂ)
    (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    Summable fun r : ℕ =>
      ‖((r.factorial : ℂ)⁻¹) * MvPowerSeries.coeff n (toBargmann ((dSecondQuant h ^ r) ψ))‖ := by
  simp_rw [toBargmann_dSecondQuant_pow]
  exact summable_norm_coeff_bargmannDeriv_iterate h _ n

/-- **Lemma 8(c).** The series of `e^{dΓ(h)} ψ` converges absolutely at every `n`, for every `ψ`. -/
theorem summable_norm_coeff_dSecondQuant_pow (h : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ)
    (n : ι →₀ ℕ) :
    Summable fun r : ℕ => ‖((r.factorial : ℂ)⁻¹) * ((dSecondQuant h ^ r) ψ).coeff n‖ := by
  classical
  simp_rw [coeff_dSecondQuant_pow, mul_left_comm _ (sqrtFactorial n), norm_mul (sqrtFactorial n)]
  exact (summable_norm_coeff_bargmannDeriv_iterate h _ n).mul_left _

/-! ### Theorem 9: the exponential form -/

/-- The entries of the matrix exponential are the sums of the entries of its series. -/
private theorem hasSum_exp_apply [DecidableEq ι] (h : Matrix ι ι ℂ) (k l : ι) :
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) * (h ^ r) k l) (NormedSpace.exp h k l) := by
  have hs : HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) • h ^ r) (NormedSpace.exp h) := by
    open scoped Matrix.Norms.L2Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) h
  have := Pi.hasSum.1 (Pi.hasSum.1 hs k) l
  simpa using this

/-- `δ_h (gᵀ z)ₗ = ((h g)ᵀ z)ₗ`. -/
private theorem bargmannDeriv_linearForms (h g : Matrix ι ι ℂ) (l : ι) :
    bargmannDeriv h (linearForms g l) = linearForms (h * g) l := by
  classical
  conv_lhs => rw [linearForms]
  simp only [map_sum, Derivation.map_smul, bargmannDeriv_X, linearForms, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- `δ_h^r zₗ = Σ_k (h^r)_kl z_k`. -/
private theorem bargmannDeriv_iterate_X [DecidableEq ι] (h : Matrix ι ι ℂ) (r : ℕ) (l : ι) :
    (⇑(bargmannDeriv h))^[r] (X l) = linearForms (h ^ r) l := by
  induction r with
  | zero => rw [Function.iterate_zero_apply, pow_zero, linearForms_one]
  | succ r ih => rw [Function.iterate_succ_apply', ih, bargmannDeriv_linearForms, pow_succ']

/-- `δ_h^r zₗ = ((h^r)ᵀ z)ₗ`, in the Bargmann picture: `𝔅 dΓ(h)^r ∣eₗ⟩ = ((h^r)ᵀ z)ₗ`. -/
theorem toBargmann_dSecondQuant_pow_single_one [DecidableEq ι] (h : Matrix ι ι ℂ) (r : ℕ)
    (l : ι) :
    toBargmann ((dSecondQuant h ^ r) (single (Finsupp.single l 1) 1)) = linearForms (h ^ r) l := by
  rw [toBargmann_dSecondQuant_pow, toBargmann_single_one, bargmannDeriv_iterate_X]

/-- The Cauchy product of two absolutely convergent series. -/
private theorem hasSum_sum_antidiagonal_mul {u v : ℕ → ℂ} {A B : ℂ} (hu : HasSum u A)
    (hv : HasSum v B) (hu' : Summable fun r => ‖u r‖) (hv' : Summable fun r => ‖v r‖) :
    HasSum (fun r => ∑ st ∈ Finset.antidiagonal r, u st.1 * v st.2) (A * B) := by
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hu' hv').of_norm
  rw [← hu.tsum_eq, ← hv.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hu' hv']
  exact hs.hasSum

/-- The multiplicativity of the coefficientwise exponential of `δ_h`. -/
private theorem hasSum_mul (h : Matrix ι ι ℂ) {f g : MvPowerSeries ι ℂ} {F G : MvPowerSeries ι ℂ}
    (hf : ∀ n, HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f)) (MvPowerSeries.coeff n F))
    (hg : ∀ n, HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] g)) (MvPowerSeries.coeff n G))
    (n : ι →₀ ℕ) :
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (f * g)))
      (MvPowerSeries.coeff n (F * G)) := by
  classical
  set u : (ι →₀ ℕ) → ℕ → ℂ := fun a s =>
    ((s.factorial : ℂ)⁻¹) * MvPowerSeries.coeff a ((⇑(bargmannDeriv h))^[s] f)
  set v : (ι →₀ ℕ) → ℕ → ℂ := fun b t =>
    ((t.factorial : ℂ)⁻¹) * MvPowerSeries.coeff b ((⇑(bargmannDeriv h))^[t] g)
  have hterm : ∀ r : ℕ, ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (f * g)) =
      ∑ x ∈ Finset.antidiagonal n, ∑ st ∈ Finset.antidiagonal r, u x.1 st.1 * v x.2 st.2 := by
    intro r
    rw [Derivation.iterate_apply_mul, map_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun st hst => ?_
    rw [Finset.mem_antidiagonal] at hst
    rw [map_nsmul, nsmul_eq_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc := inv_factorial_mul_choose (k := r) (a := st.1) (by omega)
    rw [show r - st.1 = st.2 by omega] at hc
    simp only [u, v]
    rw [← mul_assoc, hc]
    ring
  simp_rw [hterm]
  rw [MvPowerSeries.coeff_mul]
  refine hasSum_sum fun x _ => hasSum_sum_antidiagonal_mul (hf x.1) (hg x.2)
    (summable_norm_coeff_bargmannDeriv_iterate h f x.1)
    (summable_norm_coeff_bargmannDeriv_iterate h g x.2)

/-- `Σ_r [z^n] δ_h^r f / r! = [z^n] f((e^h)ᵀ z)` for every power series `f`. -/
private theorem hasSum_coeff_bargmannDeriv_iterate [DecidableEq ι] (h : Matrix ι ι ℂ)
    (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) :
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f))
      (MvPowerSeries.coeff n (subst (linearForms (NormedSpace.exp h)) f)) := by
  have hS := hasSubst_linearForms (NormedSpace.exp h)
  -- the variables
  have hX : ∀ (l : ι) (n : ι →₀ ℕ), HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (X l : MvPowerSeries ι ℂ)))
      (MvPowerSeries.coeff n
        (subst (linearForms (NormedSpace.exp h)) (X l : MvPowerSeries ι ℂ))) := by
    intro l n
    rw [subst_X hS, coeff_linearForms]
    simp only [bargmannDeriv_iterate_X, coeff_linearForms, Finset.mul_sum, mul_ite, mul_zero]
    refine hasSum_sum fun k _ => ?_
    split_ifs
    · exact hasSum_exp_apply h k l
    · exact hasSum_zero
  -- the polynomials
  have hpoly : ∀ (q : MvPolynomial ι ℂ) (n : ι →₀ ℕ), HasSum (fun r : ℕ =>
      ((r.factorial : ℂ)⁻¹) *
        MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (q : MvPowerSeries ι ℂ)))
      (MvPowerSeries.coeff n
        (subst (linearForms (NormedSpace.exp h)) (q : MvPowerSeries ι ℂ))) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      intro n
      have h0 : ∀ r : ℕ, r ≠ 0 →
          (⇑(bargmannDeriv h))^[r] (MvPowerSeries.C a : MvPowerSeries ι ℂ) = 0 := by
        intro r hr
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
        rw [Function.iterate_succ_apply, bargmannDeriv_apply]
        simp [pderiv_C]
      rw [MvPolynomial.coe_C, subst_C]
      have hs := hasSum_single (f := fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] (MvPowerSeries.C a))) 0
        fun r hr => by simp only [h0 r hr, map_zero, mul_zero]
      convert hs using 1
      simp
    | add p q hp hq =>
      intro n
      simpa only [MvPolynomial.coe_add, iterate_map_add, map_add, mul_add,
        subst_add hS] using (hp n).add (hq n)
    | mul_X p i ih =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul hS]
      exact hasSum_mul h ih (hX i)
  -- the reduction to a polynomial
  have hq : ∀ m : ι →₀ ℕ, m.degree = n.degree → MvPowerSeries.coeff m f =
      MvPowerSeries.coeff m (truncTotal (n.degree + 1) f : MvPowerSeries ι ℂ) := fun m hm => by
    rw [MvPolynomial.coeff_coe, coeff_truncTotal _ (by omega)]
  have h1 : (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r] f)) = fun r : ℕ =>
      ((r.factorial : ℂ)⁻¹) * MvPowerSeries.coeff n ((⇑(bargmannDeriv h))^[r]
        (truncTotal (n.degree + 1) f : MvPowerSeries ι ℂ)) :=
    funext fun r => by rw [coeff_bargmannDeriv_iterate_congr h hq r rfl]
  rw [h1, coeff_subst_linearForms_congr _ hq]
  exact hpoly _ n

/-- **Theorem 9**, in the Bargmann picture: for every `ψ` and `n`,
`Σ_r [zⁿ] 𝔅 dΓ(h)^r ψ / r!` converges to `[zⁿ] (𝔅ψ)((e^h)ᵀ z)`. -/
theorem hasSum_coeff_toBargmann_dSecondQuant_pow [DecidableEq ι] (h : Matrix ι ι ℂ)
    (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
      MvPowerSeries.coeff n (toBargmann ((dSecondQuant h ^ r) ψ)))
      (MvPowerSeries.coeff n (subst (linearForms (NormedSpace.exp h)) (toBargmann ψ))) := by
  simp_rw [toBargmann_dSecondQuant_pow]
  exact hasSum_coeff_bargmannDeriv_iterate h _ n

/-- **Theorem 9.** `Γ(e^h) = e^{dΓ(h)}` on the formal Fock space: for every `ψ` and `n`, the
series `Σ_r (dΓ(h)^r ψ)(n) / r!` converges to `(Γ(e^h) ψ)(n)`. -/
theorem hasSum_coeff_dSecondQuant_pow [DecidableEq ι] (h : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ)
    (n : ι →₀ ℕ) :
    HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) * ((dSecondQuant h ^ r) ψ).coeff n)
      ((secondQuant (NormedSpace.exp h) ψ).coeff n) := by
  have := (hasSum_coeff_bargmannDeriv_iterate h (toBargmann ψ) n).mul_left (sqrtFactorial n)
  rw [← toBargmann.symm_apply_apply (secondQuant _ ψ), toBargmann_secondQuant,
    coeff_toBargmann_symm]
  simp_rw [coeff_dSecondQuant_pow]
  convert this using 1
  funext r
  ring

/-- **Theorem 9.** `Γ(e^h) = e^{dΓ(h)}`, with the coefficientwise exponential. -/
theorem secondQuant_exp [DecidableEq ι] (h : Matrix ι ι ℂ) :
    ⇑(secondQuant (NormedSpace.exp h)) = coeffExp (dSecondQuant h) := by
  funext ψ
  ext n
  rw [coeff_coeffExp, (hasSum_coeff_dSecondQuant_pow h ψ n).tsum_eq]

/-- `dΓ(c h) = c dΓ(h)`. -/
theorem dSecondQuant_smul (c : ℂ) (h : Matrix ι ι ℂ) :
    dSecondQuant (c • h) = c • dSecondQuant h := by
  classical
  simp only [dSecondQuant, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- **Theorem 9**, the paper's (12): `Γ(e^{iM}) = e^{i dΓ(M)}`. -/
theorem secondQuant_exp_I_smul [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ⇑(secondQuant (NormedSpace.exp (Complex.I • M))) = coeffExp (Complex.I • dSecondQuant M) := by
  rw [secondQuant_exp, dSecondQuant_smul]

/-- **Lemma 8(c).** `e^{dΓ(h)}` is a linear map of the formal Fock space. -/
theorem isLinearMap_coeffExp_dSecondQuant (h : Matrix ι ι ℂ) :
    IsLinearMap ℂ (coeffExp (dSecondQuant h)) := by
  classical
  rw [← secondQuant_exp]
  exact (secondQuant _).isLinear

/-- **Lemma 8(c).** `e^{dΓ(h)}` maps every sector into itself. -/
theorem coeffExp_dSecondQuant_sector (h : Matrix ι ι ℂ) (p : ℕ) (ψ : FormalFock ι ℂ) :
    coeffExp (dSecondQuant h) (sector p ψ) = sector p (coeffExp (dSecondQuant h) ψ) := by
  classical
  rw [← secondQuant_exp]
  exact secondQuant_sector _ p ψ

end BosonicLean.Fock.FormalFock

/-! ### Theorem 14(a)–(c): conjugation of operators -/

namespace BosonicLean.Fock.FormalFock

open ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- `Γ(𝒰*)` preserves the squared norm of every formal vector. -/
theorem sqNorm_secondQuant_conjTranspose [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (ψ : FormalFock ι ℂ) :
    sqNorm (secondQuant (U : Matrix ι ι ℂ)ᴴ ψ) = sqNorm ψ := by
  have h := sqNorm_secondQuant (star U) ψ
  rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose] at h

/-- **Theorem 14(a).** `O ↦ O^𝒰 = Γ(𝒰*) O Γ(𝒰)` is multiplicative. -/
theorem secondQuant_conjTranspose_mul_mul_mul [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O O' : Module.End ℂ (FormalFock ι ℂ)) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * (O * O') * secondQuant (U : Matrix ι ι ℂ) =
      (secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ)) *
        (secondQuant (U : Matrix ι ι ℂ)ᴴ * O' * secondQuant (U : Matrix ι ι ℂ)) := by
  have h := secondQuant_mul_conjTranspose_self U
  calc _ = secondQuant (U : Matrix ι ι ℂ)ᴴ * O *
        (secondQuant (U : Matrix ι ι ℂ) * secondQuant (U : Matrix ι ι ℂ)ᴴ) * O' *
          secondQuant (U : Matrix ι ι ℂ) := by rw [h, mul_one, mul_assoc _ O]
    _ = _ := by simp only [mul_assoc]

/-- **Theorem 14(a).** `O ↦ O^𝒰` is linear. -/
theorem secondQuant_conjTranspose_mul_add_mul [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O O' : Module.End ℂ (FormalFock ι ℂ)) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * (O + O') * secondQuant (U : Matrix ι ι ℂ) =
      secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ) +
        secondQuant (U : Matrix ι ι ℂ)ᴴ * O' * secondQuant (U : Matrix ι ι ℂ) := by
  rw [mul_add, add_mul]

/-- **Theorem 14(a).** `O ↦ O^𝒰` is linear. -/
theorem secondQuant_conjTranspose_mul_smul_mul [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (c : ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ * (c • O) * secondQuant (U : Matrix ι ι ℂ) =
      c • (secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ)) := by
  rw [mul_smul_comm, smul_mul_assoc]

/-- **Theorem 14(a).** A polynomial in the ladder operators, the evaluation of a noncommutative
polynomial `p` in the generators `aⱼ†` (left summand) and `aⱼ` (right summand), is mapped by
`O ↦ O^𝒰` to the evaluation of the same `p` at `Σ_k conj(𝒰_jk) a_k†` and `Σ_k 𝒰_jk a_k`. -/
theorem secondQuant_conjTranspose_mul_lift_mul [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (p : FreeAlgebra ℂ (ι ⊕ ι)) :
    secondQuant (U : Matrix ι ι ℂ)ᴴ *
        FreeAlgebra.lift ℂ (Sum.elim (fun j => create j) (fun j => annihilate j)) p *
        secondQuant (U : Matrix ι ι ℂ) =
      FreeAlgebra.lift ℂ (Sum.elim (fun j => ∑ k, conj ((U : Matrix ι ι ℂ) j k) • create k)
        (fun j => ∑ k, (U : Matrix ι ι ℂ) j k • annihilate k)) p := by
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, smul_mul_assoc, secondQuant_conjTranspose_mul_self]
  | grade1 x =>
    rcases x with j | j
    · rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, Sum.elim_inl, Sum.elim_inl,
        secondQuant_conjTranspose_mul_create_mul]
    · rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, Sum.elim_inr, Sum.elim_inr,
        secondQuant_conjTranspose_mul_annihilate_mul]
  | mul a b ha hb =>
    rw [map_mul, map_mul, secondQuant_conjTranspose_mul_mul_mul, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, secondQuant_conjTranspose_mul_add_mul, ha, hb]

end BosonicLean.Fock.FormalFock

namespace BosonicLean.Fock.FockSpace

open FormalFock
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι]

/-- **Theorem 14(b).** For `ψ ∈ Γ_s`, `𝖴_𝒰 ψ ∈ dom O^max` if and only if `ψ ∈ dom (O^𝒰)^max`. -/
theorem mem_domain_maxRealization_conj [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) (ψ : FockSpace ι) :
    secondQuantUnitary U ψ ∈ (maxRealization O).domain ↔
      ψ ∈ (maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O *
        secondQuant (U : Matrix ι ι ℂ))).domain := by
  rw [mem_domain_maxRealization, mem_domain_maxRealization, toFormal_secondQuantUnitary,
    Module.End.mul_apply, Module.End.mul_apply, sqNorm_secondQuant_conjTranspose]

/-- **Theorem 14(b).** `dom (O^𝒰)^max` is the preimage of `dom O^max` under `𝖴_𝒰`. -/
theorem domain_maxRealization_conj [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) :
    (maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O *
        secondQuant (U : Matrix ι ι ℂ))).domain =
      (maxRealization O).domain.comap (secondQuantUnitary U).toLinearEquiv.toLinearMap := by
  ext ψ
  rw [Submodule.mem_comap]
  exact (mem_domain_maxRealization_conj U O ψ).symm

/-- **Theorem 14(b).** `(O^𝒰)^max = 𝖴_𝒰⁻¹ O^max 𝖴_𝒰` on its domain. -/
theorem maxRealization_conj_apply [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) (ψ : FockSpace ι)
    (hψ : ψ ∈ (maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O *
      secondQuant (U : Matrix ι ι ℂ))).domain) :
    maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ))
        ⟨ψ, hψ⟩ =
      (secondQuantUnitary U).symm
        (maxRealization O
          ⟨secondQuantUnitary U ψ, (mem_domain_maxRealization_conj U O ψ).2 hψ⟩) := by
  refine toFormal_injective ?_
  rw [toFormal_maxRealization, secondQuantUnitary_symm, toFormal_secondQuantUnitary,
    toFormal_maxRealization, toFormal_secondQuantUnitary, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rfl

/-- **Theorem 14(b).** `⟨𝖴_𝒰 ψ, O^max 𝖴_𝒰 ψ⟩ = ⟨ψ, (O^𝒰)^max ψ⟩`. -/
theorem inner_maxRealization_conj [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) (ψ : FockSpace ι)
    (hO : secondQuantUnitary U ψ ∈ (maxRealization O).domain) :
    ⟪secondQuantUnitary U ψ, maxRealization O ⟨_, hO⟩⟫_ℂ =
      ⟪ψ, maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ))
        ⟨ψ, (mem_domain_maxRealization_conj U O ψ).1 hO⟩⟫_ℂ := by
  rw [maxRealization_conj_apply, ← (secondQuantUnitary U).inner_map_map ψ,
    LinearIsometryEquiv.apply_symm_apply]

/-- **Theorem 14(c).** If `O^max` is defined on all of `Γ_s` and equals the bounded operator `A`,
then `(O^𝒰)^max` is defined on all of `Γ_s` and equals `𝖴_𝒰* A 𝖴_𝒰`. -/
theorem toFormal_star_mul_mul_secondQuantRep [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) (A : FockSpace ι →L[ℂ] FockSpace ι)
    (hA : ∀ ψ, toFormal (A ψ) = O (toFormal ψ)) (ψ : FockSpace ι) :
    toFormal ((star (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) * A *
        (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι)) ψ) =
      (secondQuant (U : Matrix ι ι ℂ)ᴴ * O * secondQuant (U : Matrix ι ι ℂ)) (toFormal ψ) := by
  rw [star_secondQuantRep, mul_apply_eq_comp, mul_apply_eq_comp,
    secondQuantRep_apply, secondQuantRep_apply, toFormal_secondQuantUnitary, hA,
    toFormal_secondQuantUnitary, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rfl

/-- **Theorem 14(c).** Under the hypothesis of `toFormal_star_mul_mul_secondQuantRep`,
`(O^𝒰)^max` is defined on all of `Γ_s`. -/
theorem domain_maxRealization_conj_eq_top [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (O : Module.End ℂ (FormalFock ι ℂ)) (A : FockSpace ι →L[ℂ] FockSpace ι)
    (hA : ∀ ψ, toFormal (A ψ) = O (toFormal ψ)) :
    (maxRealization (secondQuant (U : Matrix ι ι ℂ)ᴴ * O *
      secondQuant (U : Matrix ι ι ℂ))).domain = ⊤ := by
  refine eq_top_iff.2 fun ψ _ => ?_
  rw [mem_domain_maxRealization, ← toFormal_star_mul_mul_secondQuantRep U O A hA,
    sqNorm_toFormal]
  exact ENNReal.ofReal_lt_top

/-- **Theorem 14(c).** For every bounded operator `A` of `Γ_s`,
`⟨𝖴_𝒰 ψ, A 𝖴_𝒰 ψ⟩ = ⟨ψ, 𝖴_𝒰* A 𝖴_𝒰 ψ⟩`. -/
theorem inner_secondQuantRep_apply [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (A : FockSpace ι →L[ℂ] FockSpace ι) (ψ : FockSpace ι) :
    ⟪(secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ,
        A ((secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ)⟫_ℂ =
      ⟪ψ, (star (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) * A *
        (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι)) ψ⟫_ℂ := by
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

end BosonicLean.Fock.FockSpace
