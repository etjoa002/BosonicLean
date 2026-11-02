/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.GaussianUnitary
import BosonicLean.Weyl.State
import BosonicLean.PhaseSpace.Channel
import BosonicLean.PhaseSpace.DirectSum
import BosonicLean.PhaseSpace.Positivity
import BosonicLean.Analysis.GramIsometry
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Characteristic functions and pure Gaussian states

The characteristic function of a vector `ψ` of the Fock space `Γ_s` of `n` modes is
`χ_ψ(u) = ⟨ψ, W(u) ψ⟩`, with the Weyl operators `W(u) = D(α(u))` of
`BosonicLean.Fock.FockSpace.weylOp`. By the irreducibility of the Fock representation a nonzero
vector is cyclic for the Weyl operators, and a vector is determined up to a phase by its
characteristic function; the proof goes through an intertwining isometry built from the Gram
matrix `⟨W(u)ψ, W(v)ψ⟩ = e^{iσ(u, v)/2} χ_ψ(v - u)`.

A vector has the **Gaussian characteristic function** with displacement vector `d` and covariance
matrix `γ` (real symmetric, the vacuum at `γ = 1`) if
`χ_ψ(u) = exp(-iσ(u, d) - ¼ uᵀ Ω γ Ωᵀ u)`. Such a vector is a unit vector, `(d, γ)` are unique and
`γ` is admissible. Below every admissible `γ` lies a symplectic `γ₀`, and a vector state cannot be
a nontrivial Gaussian mixture: realizing `γ - γ₀` with ancilla modes and using irreducibility, `γ`
is symplectic. A **pure Gaussian state** is `U∣0⟩` for a Gaussian unitary `U`, the paper's (4);
the two definitions agree, and a pure Gaussian state is determined up to a phase by its
displacement vector and covariance matrix.

The next section inverts the paper's non-unitary parametrization (8) of one-mode Gaussian vectors.
The last one shows that a pure Gaussian state has a nonzero vacuum component, so that a nonzero
vector orthogonal to the vacuum, in particular a number state `∣m⟩` with `m ≠ 0`, is not a
multiple of a pure Gaussian state.

## Main definitions

* `BosonicLean.Fock.FockSpace.charFun ψ`: the characteristic function `χ_ψ`.
* `BosonicLean.Fock.FockSpace.gaussianCharFun d γ`: `exp(-iσ(u, d) - ¼ uᵀ Ω γ Ωᵀ u)`.
* `BosonicLean.Fock.FockSpace.HasGaussianCharFun ψ d γ`: `ψ` has this characteristic function.
* `BosonicLean.Fock.FockSpace.IsPureGaussian ψ`: `ψ = U∣0⟩` for a Gaussian unitary `U`.

## Main results

* `FockSpace.charFun_zero`, `charFun_neg`, `norm_charFun_le`, `charFun_smul`,
  `IsGaussianUnitary.charFun_apply`: Definition 1.
* `BosonicLean.exists_unique_linearIsometry_of_inner_eq` (in `BosonicLean.Analysis.GramIsometry`):
  Lemma 2.
* `FockSpace.inner_weylOp_apply`, `dense_span_weylOp_apply`,
  `exists_unique_linearIsometry_of_charFun_comp`: Lemma 3, the intertwiner.
* `FockSpace.exists_eq_smul_of_charFun_eq`: Theorem 4, a vector is determined up to a phase by
  its characteristic function.
* `FockSpace.gaussianCharFun_eq_exp_disp_cov`, `HasGaussianCharFun.norm_eq_one`,
  `HasGaussianCharFun.unique`, `HasGaussianCharFun.isAdmissible`: Definition 5 and Lemma 6.
* `FockSpace.exists_symplectic_le_of_isAdmissible`: Lemma 7.
* `FockSpace.IsGaussianUnitary.hasGaussianCharFun_apply_vacuum`: Theorem 8.
* `FockSpace.IsGaussianUnitary.moments`: Proposition 9, the paper's (13).
* `FockSpace.exists_isGaussianUnitary`, `exists_eq_mul_transpose`: Lemma 11.
* `FockSpace.HasGaussianCharFun.mem_symplecticGroup`: Theorem 12.
* `FockSpace.isPureGaussian_iff_exists_hasGaussianCharFun`,
  `HasGaussianCharFun.exists_isGaussianUnitary`, `HasGaussianCharFun.exists_eq_smul`:
  Theorem 13 and Corollary 14.
* `FockSpace.exists_isGaussianUnitary_hasGaussianCharFun`, `exists_hasGaussianCharFun_iff`:
  Corollary 14a, existence for every admissible symplectic covariance matrix.
* `exists_tanhPhase_eq`, `cosh_norm_eq_of_tanhPhase`, `FockSpace.tensorVec_gaussVec_eq`,
  `squeezeSymplectic_mul_self`: Lemma 15, the paper's (8) and (9) inverted.
* `FockSpace.inner_vacuum_left`, `inner_vacuum_secondQuantUnitary`: `⟨0∣ψ⟩ = ψ(0)`, and `Γ(𝒰)`
  preserves it.
* `FockSpace.IsPureGaussian.inner_vacuum_ne_zero`, `ne_smul_of_inner_vacuum_eq_zero`,
  `numberState_ne_smul`: non-Gaussianity (GA-BMPS milestone B6, (3a)–(3c)).

The numbering is that of GA-BMPS milestone B5, part B5.4.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), Sec. II A, (4), (8), (9), (10), (11), (13).
-/

open scoped InnerProductSpace ComplexConjugate Matrix ComplexOrder
open Finset Matrix Gaussian

namespace BosonicLean.Fock

namespace FockSpace

variable {n : ℕ}

/-- Bounded operators on the Fock space of `n` modes. -/
local notation "𝔹" n => FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)

/-! ### Definition 1: the characteristic function -/

/-- **Definition 1.** The characteristic function `χ_ψ(u) = ⟨ψ, W(u) ψ⟩` of a vector `ψ` of the
Fock space. -/
noncomputable def charFun (ψ : FockSpace (Fin n)) (u : PhaseIndex n → ℝ) : ℂ :=
  ⟪ψ, (weylOp u : 𝔹 n) ψ⟫_ℂ

/-- `W(0) = 1`. -/
private theorem weylOp_zero : (weylOp (0 : PhaseIndex n → ℝ) : 𝔹 n) = 1 := by
  have h : complexOfPhase (0 : PhaseIndex n → ℝ) = 0 := by
    funext j
    simp [complexOfPhase]
  rw [weylOp, h, displacement_zero]
  rfl

/-- `W(δ(α)) = D(α)`. -/
private theorem weylOp_phaseOfComplex (α : Fin n → ℂ) :
    weylOp (phaseOfComplex α) = displacement α := by
  rw [weylOp, complexOfPhase_phaseOfComplex]

/-- `W(u)* = W(-u)`, on the operators. -/
private theorem star_coe_weylOp (u : PhaseIndex n → ℝ) :
    star (weylOp u : 𝔹 n) = (weylOp (-u) : 𝔹 n) := by
  rw [← Unitary.coe_star, star_weylOp]

/-- **Definition 1.** `χ_ψ(0) = ‖ψ‖²`. -/
theorem charFun_zero (ψ : FockSpace (Fin n)) : charFun ψ 0 = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [charFun, weylOp_zero, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- **Definition 1.** `χ_ψ(-u) = conj χ_ψ(u)`. -/
theorem charFun_neg (ψ : FockSpace (Fin n)) (u : PhaseIndex n → ℝ) :
    charFun ψ (-u) = conj (charFun ψ u) := by
  rw [charFun, charFun, ← star_coe_weylOp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- **Definition 1.** `|χ_ψ(u)| ≤ ‖ψ‖²`. -/
theorem norm_charFun_le (ψ : FockSpace (Fin n)) (u : PhaseIndex n → ℝ) :
    ‖charFun ψ u‖ ≤ ‖ψ‖ ^ 2 := by
  rw [charFun, sq]
  calc _ ≤ ‖ψ‖ * ‖(weylOp u : 𝔹 n) ψ‖ := norm_inner_le_norm _ _
    _ = ‖ψ‖ * ‖ψ‖ := by rw [Unitary.norm_map]

/-- **Definition 1.** `χ_{cψ} = |c|² χ_ψ`. -/
theorem charFun_smul (c : ℂ) (ψ : FockSpace (Fin n)) (u : PhaseIndex n → ℝ) :
    charFun (c • ψ) u = ((‖c‖ ^ 2 : ℝ) : ℂ) * charFun ψ u := by
  rw [charFun, charFun, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul]
  push_cast
  rfl

/-- **Definition 1**, the paper's covariance of characteristic functions:
`χ_{Uψ}(u) = e^{-iσ(u, d)} χ_ψ(S⁻¹u)` for a Gaussian unitary with data `(S, d)`. -/
theorem IsGaussianUnitary.charFun_apply {U : unitary (𝔹 n)}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) (ψ : FockSpace (Fin n)) (u : PhaseIndex n → ℝ) :
    charFun ((U : 𝔹 n) ψ) u =
      Complex.exp (-((symplecticBilin n u d : ℝ) : ℂ) * Complex.I) * charFun ψ (S⁻¹ *ᵥ u) := by
  rw [charFun, charFun, ← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
    ← mul_apply_eq_comp, ← ContinuousLinearMap.star_eq_adjoint,
    hU.2 u, _root_.smul_apply, inner_smul_right]

/-! ### Lemma 3 and Theorem 4: the intertwiner -/

/-- **Lemma 3**, the Gram identity: `⟨W(u)ψ, W(v)ψ⟩ = e^{iσ(u, v)/2} χ_ψ(v - u)`, BosonicLean's
`twistedKernel` of `χ_ψ`. -/
theorem inner_weylOp_apply (ψ : FockSpace (Fin n)) (u v : PhaseIndex n → ℝ) :
    ⟪(weylOp u : 𝔹 n) ψ, (weylOp v : 𝔹 n) ψ⟫_ℂ =
      Weyl.twistedKernel (symplecticBilin n) (charFun ψ) ![u, v] 0 1 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
    ← ContinuousLinearMap.star_eq_adjoint, star_coe_weylOp, weylOp_mul, _root_.smul_apply,
    inner_smul_right, Weyl.twistedKernel, Matrix.of_apply, Weyl.relPhase, charFun]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_add_eq_sub, map_neg,
    LinearMap.neg_apply]
  congr 2
  push_cast
  ring

/-- The Gram identity for every pair of a family. -/
private theorem inner_weylOp_apply' (ψ : FockSpace (Fin n)) {ι : Type*}
    (u : ι → PhaseIndex n → ℝ) (j k : ι) :
    ⟪(weylOp (u j) : 𝔹 n) ψ, (weylOp (u k) : 𝔹 n) ψ⟫_ℂ =
      Weyl.twistedKernel (symplecticBilin n) (charFun ψ) u j k := by
  rw [inner_weylOp_apply]
  simp [Weyl.twistedKernel]

/-- `W(v) W(u) ψ` is a multiple of `W(v + u) ψ`. -/
private theorem weylOp_weylOp_apply (u v : PhaseIndex n → ℝ) (ψ : FockSpace (Fin n)) :
    (weylOp v : 𝔹 n) ((weylOp u : 𝔹 n) ψ) =
      Weyl.relPhase (symplecticBilin n) v u • (weylOp (v + u) : 𝔹 n) ψ := by
  rw [← mul_apply_eq_comp, weylOp_mul, _root_.smul_apply]

/-- **Lemma 3**, cyclicity: every nonzero vector is cyclic for the Weyl operators (B5.3a,
Corollary 12(b)). -/
theorem dense_span_weylOp_apply {ψ : FockSpace (Fin n)} (hψ : ψ ≠ 0) :
    Dense (Submodule.span ℂ (Set.range fun u : PhaseIndex n → ℝ => (weylOp u : 𝔹 n) ψ) :
      Set (FockSpace (Fin n))) := by
  set E := Submodule.span ℂ (Set.range fun u : PhaseIndex n → ℝ => (weylOp u : 𝔹 n) ψ)
  have hE : ∀ v : PhaseIndex n → ℝ, ∀ x ∈ E, (weylOp v : 𝔹 n) x ∈ E := by
    intro v x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [weylOp_weylOp_apply]
      exact E.smul_mem _ (Submodule.subset_span ⟨v + u, rfl⟩)
    | zero => rw [map_zero]; exact E.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact E.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact E.smul_mem c hx
  have hK : ∀ α : Fin n → ℂ, ∀ x ∈ E.topologicalClosure,
      (displacement α : 𝔹 n) x ∈ E.topologicalClosure := by
    intro α x hx
    rw [← weylOp_phaseOfComplex]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
    exact map_mem_closure (weylOp (phaseOfComplex α) : 𝔹 n).continuous hx
      fun y hy => hE _ y hy
  rcases eq_bot_or_eq_top_of_invariant E.topologicalClosure E.isClosed_topologicalClosure hK with
    h | h
  · exfalso
    have : ψ ∈ E.topologicalClosure := E.le_topologicalClosure
      (Submodule.subset_span ⟨0, by simp [weylOp_zero]⟩)
    rw [h, Submodule.mem_bot] at this
    exact hψ this
  · exact (Submodule.dense_iff_topologicalClosure_eq_top).2 h

/-- **Lemma 3 (the intertwiner).** Let `ι : ℝ^{2n} → ℝ^{2n'}` be linear with
`σ'(ιu, ιv) = σ(u, v)`, `ψ ≠ 0` and `χ_ψ = χ_φ ∘ ι`. There is exactly one linear isometry `T`
with `T ψ = φ` and `T W(u) = W(ιu) T` for every `u`. -/
theorem exists_unique_linearIsometry_of_charFun_comp {n' : ℕ}
    (ι : (PhaseIndex n → ℝ) →ₗ[ℝ] (PhaseIndex n' → ℝ))
    (hι : ∀ u v, symplecticBilin n' (ι u) (ι v) = symplecticBilin n u v)
    {ψ : FockSpace (Fin n)} {φ : FockSpace (Fin n')} (hψ : ψ ≠ 0)
    (h : ∀ u, charFun ψ u = charFun φ (ι u)) :
    ∃! T : FockSpace (Fin n) →ₗᵢ[ℂ] FockSpace (Fin n'), T ψ = φ ∧
      ∀ u x, T ((weylOp u : 𝔹 n) x) = (weylOp (ι u) : 𝔹 n') (T x) := by
  have hgram : ∀ u v, ⟪(weylOp u : 𝔹 n) ψ, (weylOp v : 𝔹 n) ψ⟫_ℂ =
      ⟪(weylOp (ι u) : 𝔹 n') φ, (weylOp (ι v) : 𝔹 n') φ⟫_ℂ := by
    intro u v
    rw [inner_weylOp_apply, inner_weylOp_apply]
    simp only [Weyl.twistedKernel, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hι, ← map_sub, h]
  obtain ⟨T, hT, huniq⟩ := exists_unique_linearIsometry_of_inner_eq
    (fun u => (weylOp u : 𝔹 n) ψ) (fun u => (weylOp (ι u) : 𝔹 n') φ) hgram
    (dense_span_weylOp_apply hψ)
  have hTψ : T ψ = φ := by
    have := hT 0
    rwa [map_zero, weylOp_zero, weylOp_zero, one_apply_eq_self,
      one_apply_eq_self] at this
  have hcomm : ∀ v x, T ((weylOp v : 𝔹 n) x) = (weylOp (ι v) : 𝔹 n') (T x) := by
    intro v
    have hext : T.toContinuousLinearMap.comp (weylOp v : 𝔹 n) =
        (weylOp (ι v) : 𝔹 n').comp T.toContinuousLinearMap := by
      refine ContinuousLinearMap.ext_on (dense_span_weylOp_apply hψ) ?_
      rintro _ ⟨u, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      rw [weylOp_weylOp_apply, map_smul, hT, hT, weylOp_weylOp_apply, ← map_add, Weyl.relPhase,
        Weyl.relPhase, hι]
    exact fun x => DFunLike.congr_fun hext x
  refine ⟨T, ⟨hTψ, hcomm⟩, fun T' hT' => huniq T' fun u => ?_⟩
  rw [hT'.2, hT'.1]

/-- **Theorem 4.** A vector is determined up to a phase by its characteristic function: if
`ψ ≠ 0` and `χ_φ = χ_ψ`, then `φ = cψ` with `|c| = 1`. -/
theorem exists_eq_smul_of_charFun_eq {ψ φ : FockSpace (Fin n)} (hψ : ψ ≠ 0)
    (h : ∀ u, charFun φ u = charFun ψ u) : ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  obtain ⟨T, ⟨hTψ, hT⟩, -⟩ := exists_unique_linearIsometry_of_charFun_comp LinearMap.id
    (fun _ _ => rfl) hψ fun u => (h u).symm
  have hc := eq_smul_one_of_commute_displacement T.toContinuousLinearMap fun α =>
    ContinuousLinearMap.ext fun x => by
      simpa only [mul_apply_eq_comp, LinearIsometry.coe_toContinuousLinearMap,
        LinearMap.id_apply, weylOp_phaseOfComplex] using hT (phaseOfComplex α) x
  set c := ⟪vacuum, T.toContinuousLinearMap vacuum⟫_ℂ
  refine ⟨c, ?_, ?_⟩
  · have h1 : ‖T vacuum‖ = ‖(vacuum : FockSpace (Fin n))‖ := T.norm_map vacuum
    rw [← LinearIsometry.coe_toContinuousLinearMap, hc, _root_.smul_apply, one_apply_eq_self,
      norm_smul, norm_vacuum, mul_one] at h1
    exact h1
  · rw [← hTψ, ← LinearIsometry.coe_toContinuousLinearMap, hc, _root_.smul_apply,
      one_apply_eq_self]

/-! ### Definition 5 and Lemma 6: Gaussian characteristic functions -/

/-- **Definition 5.** The Gaussian function `exp(-iσ(u, d) - ¼ uᵀ Ω γ Ωᵀ u)` of the displacement
vector `d` and the covariance matrix `γ`. -/
noncomputable def gaussianCharFun (d : PhaseIndex n → ℝ)
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (u : PhaseIndex n → ℝ) : ℂ :=
  Complex.exp (-((symplecticBilin n u d : ℝ) : ℂ) * Complex.I -
    ((u ⬝ᵥ (symplecticForm n * γ * (symplecticForm n)ᵀ) *ᵥ u : ℝ) : ℂ) / 4)

/-- **Definition 5.** `ψ` has the **Gaussian characteristic function** with displacement vector
`d` and covariance matrix `γ`: `γ` is symmetric and `χ_ψ(u) = exp(-iσ(u, d) - ¼ uᵀ Ω γ Ωᵀ u)` for
every `u`. -/
def HasGaussianCharFun (ψ : FockSpace (Fin n)) (d : PhaseIndex n → ℝ)
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) : Prop :=
  γᵀ = γ ∧ ∀ u, charFun ψ u = gaussianCharFun d γ u

/-- **Definition 5**, the convention of `BosonicLean.Weyl.GaussianState`: the Gaussian function is
`exp(i disp(u) - cov(u, u)/4)` with `disp = -σ(·, d)` and `cov = Ω γ Ωᵀ`. -/
theorem gaussianCharFun_eq_exp_disp_cov (d : PhaseIndex n → ℝ)
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (u : PhaseIndex n → ℝ) :
    gaussianCharFun d γ u =
      Complex.exp (Complex.I * ((-(symplecticBilin n u d) : ℝ) : ℂ) -
        ((Matrix.toBilin' (symplecticForm n * γ * (symplecticForm n)ᵀ) u u : ℝ) : ℂ) / 4) := by
  rw [gaussianCharFun, Matrix.toBilin'_apply']
  congr 1
  push_cast
  ring

/-- **Lemma 6(a).** A vector with a Gaussian characteristic function is a unit vector. -/
theorem HasGaussianCharFun.norm_eq_one {ψ : FockSpace (Fin n)} {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (h : HasGaussianCharFun ψ d γ) : ‖ψ‖ = 1 := by
  have h0 := h.2 0
  rw [charFun_zero, gaussianCharFun] at h0
  simp only [map_zero, LinearMap.zero_apply, Complex.ofReal_zero, neg_zero, zero_mul,
    zero_dotProduct, zero_div, sub_zero, Complex.exp_zero] at h0
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h0)

/-- `(P u) ⬝ (M (P v)) = u ⬝ (P M P v)` for symmetric `P`. -/
private theorem mulVec_dotProduct_mulVec {ι : Type*} [Fintype ι] {P : Matrix ι ι ℝ}
    (hP : Pᵀ = P) (M : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (P *ᵥ u) ⬝ᵥ (M *ᵥ (P *ᵥ v)) = u ⬝ᵥ ((P * M * P) *ᵥ v) := by
  conv_lhs => rw [← hP]
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec, transpose_transpose, dotProduct_comm,
    mulVec_mulVec, mulVec_mulVec, hP]
  exact dotProduct_comm _ _

/-- Two symmetric matrices with the same quadratic form are equal. -/
private theorem eq_of_dotProduct_mulVec_self_eq {ι : Type*} [Fintype ι]
    {M M' : Matrix ι ι ℝ} (hM : Mᵀ = M) (hM' : M'ᵀ = M')
    (h : ∀ u, u ⬝ᵥ M *ᵥ u = u ⬝ᵥ M' *ᵥ u) : M = M' := by
  classical
  set N := M - M' with hNdef
  have hN : Nᵀ = N := by rw [transpose_sub, hM, hM']
  have h0 : ∀ u, u ⬝ᵥ N *ᵥ u = 0 := fun u => by
    rw [sub_mulVec, dotProduct_sub, h, sub_self]
  have hB : ∀ u v, u ⬝ᵥ N *ᵥ v = 0 := by
    intro u v
    have h1 := h0 (u + v)
    have hsym : v ⬝ᵥ N *ᵥ u = u ⬝ᵥ N *ᵥ v := by
      rw [← dotProduct_transpose_mulVec, hN]
    rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h0 u, h0 v, hsym] at h1
    linarith
  rw [← sub_eq_zero]
  ext i j
  have := hB (Pi.single i 1) (Pi.single j 1)
  simpa [hNdef, mulVec_single, single_dotProduct] using this

/-- `Ωᵀ (Ω γ Ωᵀ) Ω = γ`. -/
private theorem transpose_symplecticForm_mul_conj (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    (symplecticForm n)ᵀ * (symplecticForm n * γ * (symplecticForm n)ᵀ) * symplecticForm n = γ := by
  simp only [← Matrix.mul_assoc, transpose_symplecticForm_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, transpose_symplecticForm_mul_self, Matrix.mul_one]

/-- **Lemma 6(b).** The displacement vector and the covariance matrix are unique. -/
theorem HasGaussianCharFun.unique {ψ : FockSpace (Fin n)} {d d' : PhaseIndex n → ℝ}
    {γ γ' : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (h : HasGaussianCharFun ψ d γ)
    (h' : HasGaussianCharFun ψ d' γ') : d = d' ∧ γ = γ' := by
  have he : ∀ u, gaussianCharFun d γ u = gaussianCharFun d' γ' u := fun u =>
    (h.2 u).symm.trans (h'.2 u)
  have hq : ∀ u, u ⬝ᵥ (symplecticForm n * γ * (symplecticForm n)ᵀ) *ᵥ u =
      u ⬝ᵥ (symplecticForm n * γ' * (symplecticForm n)ᵀ) *ᵥ u := by
    intro u
    have := congrArg (fun z : ℂ => Real.log ‖z‖) (he u)
    simp only [gaussianCharFun, Complex.norm_exp, Real.log_exp, Complex.sub_re, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.I_re, Complex.neg_im, Complex.ofReal_im,
      Complex.I_im, Complex.div_ofNat_re] at this
    linarith
  have hsym : ∀ g : Matrix (PhaseIndex n) (PhaseIndex n) ℝ, gᵀ = g →
      (symplecticForm n * g * (symplecticForm n)ᵀ)ᵀ = symplecticForm n * g * (symplecticForm n)ᵀ :=
    fun g hg => by rw [transpose_mul, transpose_mul, transpose_transpose, hg, Matrix.mul_assoc]
  have hγ : γ = γ' := by
    have hM := eq_of_dotProduct_mulVec_self_eq (hsym γ h.1) (hsym γ' h'.1) hq
    rw [← transpose_symplecticForm_mul_conj γ, hM, transpose_symplecticForm_mul_conj]
  subst hγ
  refine ⟨eq_of_exp_symplecticBilin_eq fun u => ?_, rfl⟩
  have := he u
  rw [gaussianCharFun, gaussianCharFun, Complex.exp_sub, Complex.exp_sub] at this
  exact (div_left_inj' (Complex.exp_ne_zero _)).1 this

/-- The twisted kernels of a characteristic function are Gram matrices, hence positive
semidefinite. -/
private theorem posSemidef_twistedKernel_charFun (ψ : FockSpace (Fin n)) (m : ℕ)
    (u : Fin m → PhaseIndex n → ℝ) :
    (Weyl.twistedKernel (symplecticBilin n) (charFun ψ) u).PosSemidef := by
  convert posSemidef_gram ℂ fun j => (weylOp (u j) : 𝔹 n) ψ using 1
  ext j k
  rw [gram, Matrix.of_apply, inner_weylOp_apply']

/-- For symmetric `γ`, `γ + iΩ ≥ 0` if and only if `γ - iΩ ≥ 0`: entrywise conjugation, as
transposition of the Hermitian matrix. -/
private theorem posSemidef_add_iff_sub {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : γᵀ = γ) :
    (γ.map Complex.ofReal + Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef ↔
      (γ.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef := by
  rw [← posSemidef_transpose_iff]
  congr! 1
  rw [transpose_add, transpose_smul, ← transpose_map, ← transpose_map, hγ,
    transpose_symplecticForm,
    Matrix.map_neg _ Complex.ofReal_neg, smul_neg, ← sub_eq_add_neg]

/-- The state condition `cov + iσ ≥ 0` for `cov = toBilin' ν` and `σ` of `Ω` is `ν + iΩ ≥ 0`. -/
private theorem isStateConditionC_iff_posSemidef' (ν : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    Weyl.IsStateConditionC (Matrix.toBilin' ν) (symplecticBilin n) ↔
      (ν.map Complex.ofReal + Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef := by
  have h := isStateConditionC_iff_posSemidef 0 ν
  have h0 : (Matrix.toBilin' (symplecticForm n)).comp (Matrix.toLin' (0 : Matrix (PhaseIndex n)
      (PhaseIndex n) ℝ)) (Matrix.toLin' 0) = 0 := by
    ext u v
    simp
  rw [h0, sub_zero, transpose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_zero] at h
  exact h

/-- **Lemma 6(c).** The covariance matrix is admissible, `γ - iΩ ≥ 0`: the twisted kernels of
`χ_ψ` are Gram matrices, so BosonicLean's state condition holds for `cov = Ω γ Ωᵀ`, and congruence
by `Ω` and conjugation give `γ - iΩ ≥ 0`. -/
theorem HasGaussianCharFun.isAdmissible {ψ : FockSpace (Fin n)} {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (h : HasGaussianCharFun ψ d γ) :
    IsAdmissible γ := by
  set M := symplecticForm n * γ * (symplecticForm n)ᵀ with hMdef
  have hMs : Mᵀ = M := by rw [hMdef, transpose_mul, transpose_mul, transpose_transpose, h.1,
    Matrix.mul_assoc]
  have hstate : Weyl.IsStateConditionC (Matrix.toBilin' M) (symplecticBilin n) :=
    Weyl.isStateConditionC_of_posSemidef_twistedKernel isAlt_symplecticBilin
      (Matrix.isSymm_toBilin'_iff_isSymm.2 hMs) (-(symplecticBilin n).flip d)
      (fun u => by
        rw [h.2 u, gaussianCharFun_eq_exp_disp_cov]
        simp only [LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, hMdef])
      (posSemidef_twistedKernel_charFun ψ)
  rw [isStateConditionC_iff_posSemidef'] at hstate
  have hc := hstate.conjTranspose_mul_mul_same ((symplecticForm n).map Complex.ofReal)
  have hmap : ∀ A B : Matrix (PhaseIndex n) (PhaseIndex n) ℝ,
      (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := fun A B =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hct : ((symplecticForm n).map Complex.ofReal)ᴴ = (symplecticForm n)ᵀ.map Complex.ofReal := by
    ext i j
    simp
  rw [hct, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← hmap, ← hmap,
    ← hmap, ← hmap, transpose_symplecticForm_mul_conj,
    transpose_symplecticForm_mul_self, Matrix.one_mul] at hc
  exact ⟨h.1, (posSemidef_add_iff_sub h.1).1 hc⟩

/-! ### Lemma 7: a symplectic matrix below an admissible one -/

/-- The pair form of admissibility: `2 aᵀ Ω b ≤ aᵀ γ a + bᵀ γ b`. -/
private theorem two_mul_dotProduct_le_of_isAdmissible {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : IsAdmissible γ) (a b : PhaseIndex n → ℝ) :
    2 * (a ⬝ᵥ symplecticForm n *ᵥ b) ≤ a ⬝ᵥ γ *ᵥ a + b ⬝ᵥ γ *ᵥ b := by
  have h := (isStateConditionC_iff_posSemidef' γ).2 ((posSemidef_add_iff_sub hγ.1).2 hγ.2)
  have hp := (Weyl.isStateConditionC_iff_pair (Matrix.isSymm_toBilin'_iff_isSymm.2 hγ.1)
    isAlt_symplecticBilin).1 h a b
  simpa only [symplecticBilin, Matrix.toBilin'_apply'] using hp

open scoped MatrixOrder in
/-- **Lemma 7.** Below every admissible `γ` lies a symplectic one: `γ₀ = γ^{1/2} |A| γ^{1/2}` with
`A = γ^{-1/2} Ω γ^{-1/2}` is symmetric, positive definite and symplectic, and `γ - γ₀ ≥ 0`
(`γ` is positive definite by `IsAdmissible.posDef`). -/
theorem exists_symplectic_le_of_isAdmissible {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : IsAdmissible γ) :
    ∃ γ₀ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ, γ₀.PosDef ∧
      γ₀ ∈ symplecticGroup (Fin n) ℝ ∧ (γ - γ₀).PosSemidef := by
  have hpd := hγ.posDef
  have hγ0 : 0 ≤ γ := nonneg_iff_posSemidef.2 hpd.posSemidef
  -- `s = γ^{1/2}` and `si = γ^{-1/2}`
  set s := CFC.sqrt γ with hs
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg γ
  have hss : s * s = γ := CFC.sqrt_mul_sqrt_self γ hγ0
  have hst : sᵀ = s := by
    have := (nonneg_iff_posSemidef.1 hs0).1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hsu : IsUnit s := (CFC.isUnit_sqrt_iff γ hγ0).2 hpd.isUnit
  have hsd : IsUnit s.det := (isUnit_iff_isUnit_det s).1 hsu
  set si := s⁻¹ with hsi
  have hsis : si * s = 1 := nonsing_inv_mul s hsd
  have hssi : s * si = 1 := mul_nonsing_inv s hsd
  have hsit : siᵀ = si := by rw [hsi, transpose_nonsing_inv, hst]
  -- `A = γ^{-1/2} Ω γ^{-1/2}`, `B = γ^{1/2} Ω γ^{1/2}`, `A B = B A = -1`
  set Ω := symplecticForm n with hΩ
  have hΩΩ : Ω * Ω = -1 := symplecticForm_sq n
  set A := si * Ω * si with hA
  set B := s * Ω * s with hB
  have hAt : Aᵀ = -A := by
    rw [hA, transpose_mul, transpose_mul, hsit, hΩ, transpose_symplecticForm, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc]
  have hAB : A * B = -1 := by
    rw [hA, hB]
    calc si * Ω * si * (s * Ω * s) = si * Ω * (si * s) * Ω * s := by simp only [Matrix.mul_assoc]
      _ = si * (Ω * Ω) * s := by rw [hsis, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = -1 := by rw [hΩΩ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hsis]
  have hBA : B * A = -1 := by
    rw [hA, hB]
    calc s * Ω * s * (si * Ω * si) = s * Ω * (s * si) * Ω * si := by simp only [Matrix.mul_assoc]
      _ = s * (Ω * Ω) * si := by rw [hssi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = -1 := by rw [hΩΩ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hssi]
  -- the bound `|A x| ≤ |x|`, from admissibility
  have hbound : ∀ x, (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have h := two_mul_dotProduct_le_of_isAdmissible hγ (si *ᵥ (A *ᵥ x)) (si *ᵥ x)
    have hsγs : si * γ * si = 1 := by
      rw [← hss, ← Matrix.mul_assoc, hsis, Matrix.one_mul, hssi]
    rw [mulVec_dotProduct_mulVec hsit, mulVec_dotProduct_mulVec hsit,
      mulVec_dotProduct_mulVec hsit, hsγs, one_mulVec, one_mulVec, ← hA] at h
    linarith
  have hAA : (1 - Aᵀ * A).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one,
        transpose_mul, transpose_transpose]
    · have hx : star x = x := star_trivial x
      rw [hx, sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
        ← dotProduct_transpose_mulVec, transpose_transpose, dotProduct_comm (A *ᵥ x)]
      linarith [hbound x, dotProduct_comm (A *ᵥ x) (A *ᵥ x)]
  -- `P = |A| = (Aᵀ A)^{1/2}`
  have hAA0 : 0 ≤ Aᵀ * A := by
    rw [nonneg_iff_posSemidef, ← conjTranspose_eq_transpose_of_trivial]
    exact posSemidef_conjTranspose_mul_self A
  set P := CFC.sqrt (Aᵀ * A) with hP
  have hP0 : 0 ≤ P := CFC.sqrt_nonneg _
  have hPP : P * P = Aᵀ * A := CFC.sqrt_mul_sqrt_self _ hAA0
  have hPt : Pᵀ = P := by
    have := (nonneg_iff_posSemidef.1 hP0).1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hP1 : (1 - P).PosSemidef := by
    -- `0 ≤ |x - Px|²` and `|Px|² = |Ax|² ≤ |x|²` give `x ⬝ P x ≤ x ⬝ x`
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one, hPt]
    · have hx : star x = x := star_trivial x
      have hPx : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
        rw [← dotProduct_transpose_mulVec, hPt, mulVec_mulVec, hPP, ← mulVec_mulVec,
          ← dotProduct_transpose_mulVec, transpose_transpose]
      have hsym : (P *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (P *ᵥ x) := dotProduct_comm _ _
      have h0 : 0 ≤ (x - P *ᵥ x) ⬝ᵥ (x - P *ᵥ x) :=
        dotProduct_self_star_nonneg (x - P *ᵥ x) |>.trans_eq (by rw [star_trivial])
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym] at h0
      rw [hx, sub_mulVec, one_mulVec, dotProduct_sub]
      linarith [hbound x]
  have hPA : Commute P A := by
    have hc : Commute (Aᵀ * A) A := by
      rw [hAt, Matrix.neg_mul]
      exact ((Commute.refl A).mul_left (Commute.refl A)).neg_left
    rw [hP, CFC.sqrt_eq_cfc]
    exact hc.cfc_nnreal _
  have hPB : P * B = B * P := by
    calc P * B = -(B * A) * P * B := by rw [hBA, neg_neg, Matrix.one_mul]
      _ = -(B * (P * A) * B) := by rw [hPA.eq]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(B * P * (A * B)) := by simp only [Matrix.mul_assoc]
      _ = B * P := by rw [hAB]; simp
  -- unit facts
  have hΩu : IsUnit Ω := (isUnit_iff_isUnit_det Ω).2
    (isUnit_det_of_right_inverse (B := -Ω) (by rw [Matrix.mul_neg, hΩΩ, neg_neg]))
  have hsiu : IsUnit si := (isUnit_iff_isUnit_det si).2 (isUnit_det_of_right_inverse hsis)
  have hAu : IsUnit A := (hsiu.mul hΩu).mul hsiu
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hAu
  have hPu : IsUnit P := (CFC.isUnit_sqrt_iff _ hAA0).2 ((isUnit_iff_isUnit_det _).2 (by
    rw [det_mul, det_transpose]
    exact hAd.mul hAd))
  refine ⟨s * P * s, ?_, ?_, ?_⟩
  · have hPd : P.PosDef := (nonneg_iff_posSemidef.1 hP0).posDef_iff_isUnit.2 hPu
    have := hPd.mul_mul_conjTranspose_same (B := s) (vecMul_injective_iff_isUnit.2 hsu)
    rwa [conjTranspose_eq_transpose_of_trivial, hst] at this
  · rw [mem_symplecticGroup_iff, ← hΩ, transpose_mul, transpose_mul, hst, hPt,
      ← Matrix.mul_assoc s P s]
    calc s * P * s * Ω * (s * P * s) = s * (P * B * P) * s := by
          rw [hB]; simp only [Matrix.mul_assoc]
      _ = s * A * s := by
          rw [hPB, Matrix.mul_assoc B, hPP, hAt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc,
            hBA, Matrix.neg_mul, Matrix.one_mul, neg_neg]
      _ = Ω := by
          rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hssi, Matrix.one_mul, Matrix.mul_assoc,
            hsis, Matrix.mul_one]
  · have := hP1.mul_mul_conjTranspose_same s
    rwa [conjTranspose_eq_transpose_of_trivial, hst, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hss] at this

/-! ### Theorem 8 and Proposition 9: Gaussian unitaries on the vacuum -/

/-- `S⁻¹ = Ω Sᵀ Ωᵀ` for symplectic `S`. -/
private theorem inv_eq_of_mem_symplecticGroup {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    S⁻¹ = symplecticForm n * Sᵀ * (symplecticForm n)ᵀ := by
  refine Matrix.inv_eq_left_inv ?_
  calc symplecticForm n * Sᵀ * (symplecticForm n)ᵀ * S =
        -(symplecticForm n * (Sᵀ * symplecticForm n * S)) := by
        rw [transpose_symplecticForm]
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = 1 := by rw [mem_symplecticGroup_iff'.1 hS, symplecticForm_sq, neg_neg]

/-- **Theorem 8.** `U∣0⟩` has the Gaussian characteristic function with displacement vector `d`
and covariance matrix `S Sᵀ`, which is symplectic (B5.2's `mul_transpose_mem`). -/
theorem IsGaussianUnitary.hasGaussianCharFun_apply_vacuum {U : unitary (𝔹 n)}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) : HasGaussianCharFun ((U : 𝔹 n) vacuum) d (S * Sᵀ) := by
  refine ⟨by rw [transpose_mul, transpose_transpose], fun u => ?_⟩
  set M := symplecticForm n * Sᵀ * (symplecticForm n)ᵀ
  have hq : ∑ i, (S⁻¹ *ᵥ u) i ^ 2 =
      u ⬝ᵥ (symplecticForm n * (S * Sᵀ) * (symplecticForm n)ᵀ) *ᵥ u := by
    have hsq : ∑ i, (S⁻¹ *ᵥ u) i ^ 2 = (S⁻¹ *ᵥ u) ⬝ᵥ (S⁻¹ *ᵥ u) := by
      simp only [dotProduct, sq]
    have hMM : Mᵀ * M = symplecticForm n * (S * Sᵀ) * (symplecticForm n)ᵀ := by
      simp only [M, transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (symplecticForm n)ᵀ (symplecticForm n),
        transpose_symplecticForm_mul_self, Matrix.one_mul]
    rw [hsq, inv_eq_of_mem_symplecticGroup hU.1, ← dotProduct_transpose_mulVec M u (M *ᵥ u),
      mulVec_mulVec, hMM]
  rw [hU.charFun_apply, charFun, inner_vacuum_weylOp, hq, gaussianCharFun, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The quadratures on the vacuum: `q̂ⱼ∣0⟩ = ∣eⱼ⟩/√2`, `p̂ⱼ∣0⟩ = i∣eⱼ⟩/√2`. -/
private noncomputable def vacuumQuadrature : PhaseIndex n → FockSpace (Fin n)
  | Sum.inl j => ((Real.sqrt 2 : ℂ)⁻¹) • lp.single 2 (Finsupp.single j 1) 1
  | Sum.inr j => (Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • lp.single 2 (Finsupp.single j 1) 1

open FormalFock in
/-- `R̂ₘ ∣0⟩ = vacuumQuadrature m`. -/
private theorem quadrature_vacuum (m : PhaseIndex n) :
    quadrature m (toFormal (vacuum : FockSpace (Fin n))) = toFormal (vacuumQuadrature m) := by
  have ha : ∀ j : Fin n, annihilate j (single (0 : Fin n →₀ ℕ) (1 : ℂ)) = 0 :=
    fun j => by rw [annihilate_single]; simp
  have hc : ∀ j : Fin n, create j (single (0 : Fin n →₀ ℕ) (1 : ℂ)) =
      single (Finsupp.single j 1) 1 := fun j => by
    rw [create_single]
    simp [sqrtC]
  rcases m with j | j
  · simp only [quadrature, vacuumQuadrature, toFormal_vacuum, LinearMap.smul_apply,
      LinearMap.add_apply, ha, hc, zero_add, map_smul, toFormal_lpSingle]
  · simp only [quadrature, vacuumQuadrature, toFormal_vacuum, LinearMap.smul_apply,
      LinearMap.sub_apply, ha, hc, sub_zero, map_smul, toFormal_lpSingle, div_eq_mul_inv]

/-- `⟨eⱼ, eₖ⟩ = δⱼₖ` for the one-particle vectors `∣eⱼ⟩`. -/
private theorem inner_lpSingle_single (j k : Fin n) :
    ⟪(lp.single 2 (Finsupp.single j 1) (1 : ℂ) : FockSpace (Fin n)),
      lp.single 2 (Finsupp.single k 1) (1 : ℂ)⟫_ℂ = if j = k then 1 else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne : (Finsupp.single j 1 : Fin n →₀ ℕ) ≠ Finsupp.single k 1 := fun h =>
      hjk (Finsupp.single_left_injective one_ne_zero h)
    rw [Pi.single_eq_of_ne hne]
    simp [hjk]

/-- `⟨R̂ₘ0, R̂ₘ'0⟩ = (δₘₘ' + iΩₘₘ')/2`. -/
private theorem inner_vacuumQuadrature (m m' : PhaseIndex n) :
    ⟪vacuumQuadrature m, vacuumQuadrature m'⟫_ℂ =
      ((if m = m' then 1 else 0) + Complex.I * (symplecticForm n m m' : ℂ)) / 2 := by
  set t : ℂ := (Real.sqrt 2 : ℂ)⁻¹ with htdef
  have ht : t * t = 1 / 2 := by
    rw [htdef, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hct : conj t = t := by rw [htdef, map_inv₀, Complex.conj_ofReal]
  rcases m with j | j <;> rcases m' with k | k <;>
    simp only [vacuumQuadrature, inner_smul_left, inner_smul_right, inner_lpSingle_single,
      symplecticForm_eq_fromBlocks, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte,
      Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, map_mul, hct, Complex.conj_I,
      ← htdef] <;>
    split_ifs <;> push_cast
  all_goals first
    | linear_combination ht
    | linear_combination Complex.I * ht
    | linear_combination (-Complex.I) * ht
    | linear_combination (-Complex.I ^ 2) * ht + (-(1 : ℂ) / 2) * Complex.I_sq
    | ring

/-- `⟨0, R̂ₘ0⟩ = 0`. -/
private theorem inner_vacuum_vacuumQuadrature (m : PhaseIndex n) :
    ⟪(vacuum : FockSpace (Fin n)), vacuumQuadrature m⟫_ℂ = 0 := by
  have h : ∀ j : Fin n, ⟪(vacuum : FockSpace (Fin n)),
      lp.single 2 (Finsupp.single j 1) (1 : ℂ)⟫_ℂ = 0 := fun j => by
    rw [vacuum, lp.inner_single_left, lp.single_apply,
      Pi.single_eq_of_ne (Finsupp.single_ne_zero.2 one_ne_zero).symm, inner_zero_right]
  rcases m with j | j <;> simp [vacuumQuadrature, inner_smul_right, h]

/-- The vacuum lies in `𝒬 = ⋂ⱼ dom aⱼ`. -/
private theorem vacuum_mem_maxDomain (j : Fin n) :
    (vacuum : FockSpace (Fin n)) ∈ maxDomain (FormalFock.annihilate j) := by
  change Memℓp (FormalFock.annihilate j (toFormal (vacuum : FockSpace (Fin n)))).coeff 2
  rw [toFormal_vacuum, FormalFock.annihilate_single]
  simp only [Finsupp.coe_zero, Pi.zero_apply, lt_self_iff_false, ↓reduceIte]
  exact zero_memℓp

/-- **Proposition 9**, the paper's (13): for `ψ = U∣0⟩`, `R̂ₖψ = φₖ ∈ Γ_s`, `⟨ψ, φₖ⟩ = dₖ` and
`⟨φₖ - dₖψ, φₗ - dₗψ⟩ = (γₖₗ + iΩₖₗ)/2` with `γ = S Sᵀ`: in the paper's notation `rₖ = dₖ` and
`Γₖₗ = γₖₗ/2`, the anticommutator expectation read as `2 Re⟨(R̂ₖ - rₖ)ψ, (R̂ₗ - rₗ)ψ⟩`. -/
theorem IsGaussianUnitary.moments {U : unitary (𝔹 n)}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) :
    ∃ φ : PhaseIndex n → FockSpace (Fin n),
      (∀ k, quadrature k (toFormal ((U : 𝔹 n) vacuum)) = toFormal (φ k)) ∧
      (∀ k, ⟪(U : 𝔹 n) vacuum, φ k⟫_ℂ = (d k : ℂ)) ∧
      ∀ k l, ⟪φ k - (d k : ℂ) • (U : 𝔹 n) vacuum, φ l - (d l : ℂ) • (U : 𝔹 n) vacuum⟫_ℂ =
        (((S * Sᵀ) k l : ℂ) + Complex.I * (symplecticForm n k l : ℂ)) / 2 := by
  set ξ : PhaseIndex n → FockSpace (Fin n) := fun k =>
    ∑ m, (S k m : ℂ) • vacuumQuadrature m + (d k : ℂ) • vacuum with hξ
  have hsub : ∀ k, (U : 𝔹 n) (ξ k) - (d k : ℂ) • (U : 𝔹 n) vacuum =
      (U : 𝔹 n) (∑ m, (S k m : ℂ) • vacuumQuadrature m) := fun k => by
    rw [← map_smul, ← map_sub, hξ, add_sub_cancel_right]
  refine ⟨fun k => (U : 𝔹 n) (ξ k), fun k => hU.quadrature_apply vacuum_mem_maxDomain k ?_,
    fun k => ?_, fun k l => ?_⟩
  · simp only [hξ, map_add, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      quadrature_vacuum]
  · rw [Unitary.inner_map_map, hξ]
    simp only [inner_add_right, inner_sum, inner_smul_right, inner_vacuum_vacuumQuadrature,
      mul_zero, sum_const_zero, zero_add]
    rw [inner_self_eq_norm_sq_to_K, norm_vacuum]
    simp
  · rw [hsub, hsub, Unitary.inner_map_map]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      inner_vacuumQuadrature]
    conv_rhs => rw [← mem_symplecticGroup_iff.1 hU.1]
    simp only [mul_apply, transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    have e1 : ∀ x x₁, (S l x : ℂ) * ((S k x₁ : ℂ) *
        (((if x₁ = x then 1 else 0) + Complex.I * (symplecticForm n x₁ x : ℂ)) / 2)) =
        (if x₁ = x then (S k x₁ : ℂ) * (S l x : ℂ) / 2 else 0) +
          Complex.I * ((S k x₁ : ℂ) * (symplecticForm n x₁ x : ℂ)) * (S l x : ℂ) / 2 := by
      intro x x₁
      split_ifs <;> ring
    simp only [mul_sum, e1, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
    rw [add_div, sum_div, sum_div]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [sum_mul, mul_sum, sum_div]
    exact sum_congr rfl fun _ _ => by ring

/-! ### Definition 10, Lemma 11: pure Gaussian states -/

/-- **Definition 10**, the paper's (4): `ψ` is a **pure Gaussian state** if `ψ = U∣0⟩` for a
Gaussian unitary `U`. The paper's "up to global phase" is absorbed: `cU` with `|c| = 1` is
Gaussian with the same data. -/
def IsPureGaussian (ψ : FockSpace (Fin n)) : Prop :=
  ∃ (U : unitary (𝔹 n)) (S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (d : PhaseIndex n → ℝ),
    IsGaussianUnitary U S d ∧ ψ = (U : 𝔹 n) vacuum

/-- **Lemma 11(a).** Every pair `(S, d)` with `S` symplectic is the data of a Gaussian unitary:
`Γ(𝒰) D(α) S(r) Γ(𝒲)` for a Bloch–Messiah decomposition `S = O_𝒰 Σ(r) O_𝒲` and
`δ(α) = O_𝒰ᵀ d`. -/
theorem exists_isGaussianUnitary {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) (d : PhaseIndex n → ℝ) :
    ∃ U : unitary (𝔹 n), IsGaussianUnitary U S d := by
  obtain ⟨OU, hOU, OW, hOW, r, -, hSd⟩ := exists_blochMessiah hS
  obtain ⟨𝒰, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOU
  obtain ⟨𝒲, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOW
  have h := isGaussianUnitary_decomposition 𝒰 𝒲
    (complexOfPhase ((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d)) fun j => (r j : ℂ)
  rw [squeezeSymplectic_ofReal, ← hSd, phaseOfComplex_complexOfPhase, Matrix.mulVec_mulVec,
    ← orthogonalSymplecticOfUnitary_star, ← orthogonalSymplecticOfUnitary_mul,
    Unitary.mul_star_self, orthogonalSymplecticOfUnitary_one, Matrix.one_mulVec] at h
  exact ⟨_, h⟩

/-- **Lemma 11(b).** A positive definite symplectic matrix is `S Sᵀ` with `S` symplectic: by the
symplectic diagonalization `γ = O Σ(r)² Oᵀ`, `S = O Σ(r)`. -/
theorem exists_eq_mul_transpose {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hγ : γ.PosDef)
    (hγs : γ ∈ symplecticGroup (Fin n) ℝ) :
    ∃ S ∈ symplecticGroup (Fin n) ℝ, γ = S * Sᵀ := by
  obtain ⟨O, hO, r, -, hM⟩ := exists_orthogonalSymplectic_diagonalization hγ hγs
  refine ⟨O * squeezingMatrix r, Submonoid.mul_mem _ (Submonoid.mem_inf.1 hO).1
    (squeezingMatrix_mem r), ?_⟩
  rw [hM, transpose_mul, squeezingMatrix_transpose, sq]
  simp only [Matrix.mul_assoc]

/-! ### Theorem 12: the covariance matrix is symplectic

The proof realizes `γ - γ₀ = Ωᵀ C² Ω` with `2n` ancilla modes: on `n + (n + n)` modes, positions
first, BosonicLean's `splitPhase` splits the coordinates into those of the `n` modes and those of
the `n + n` ancilla modes, which are labelled by the coordinates of `ℝ^{2n}`
(`finSumFinEquiv`). -/

section DirectSum

variable {m : ℕ}

/-- `(A ⊕ B)(C ⊕ D) = AC ⊕ BD`. -/
private theorem directSumCov_mul (A C : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (B D : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) :
    directSumCov A B * directSumCov C D = directSumCov (A * C) (B * D) := by
  simp only [directSumCov, ← phaseSplitEquiv_coe n m, submatrix_mul_equiv, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- `(A ⊕ B)ᵀ = Aᵀ ⊕ Bᵀ`. -/
private theorem transpose_directSumCov (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (B : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) :
    (directSumCov A B)ᵀ = directSumCov Aᵀ Bᵀ := by
  simp only [directSumCov, transpose_submatrix, fromBlocks_transpose, transpose_zero]

/-- A direct sum of symplectic matrices is symplectic. -/
private theorem directSumCov_mem_symplecticGroup {A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    {B : Matrix (PhaseIndex m) (PhaseIndex m) ℝ} (hA : A ∈ symplecticGroup (Fin n) ℝ)
    (hB : B ∈ symplecticGroup (Fin m) ℝ) : directSumCov A B ∈ symplecticGroup (Fin (n + m)) ℝ := by
  rw [mem_symplecticGroup_iff, symplecticForm_directSum, transpose_directSumCov, directSumCov_mul,
    directSumCov_mul, mem_symplecticGroup_iff.1 hA, mem_symplecticGroup_iff.1 hB]

/-- The quadratic form of a direct sum on split vectors. -/
private theorem dotProduct_directSumCov_mulVec (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (B : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) (a a' : PhaseIndex n → ℝ)
    (b b' : PhaseIndex m → ℝ) :
    (fun i => Sum.elim a b (splitPhase i)) ⬝ᵥ
        (directSumCov A B *ᵥ fun i => Sum.elim a' b' (splitPhase i)) =
      a ⬝ᵥ A *ᵥ a' + b ⬝ᵥ B *ᵥ b' := by
  have e : ∀ f : PhaseIndex n ⊕ PhaseIndex m → ℝ,
      (fun i => f (splitPhase i)) = f ∘ phaseSplitEquiv n m := fun f => by
    rw [phaseSplitEquiv_coe]
    rfl
  rw [e, e, directSumCov, ← phaseSplitEquiv_coe n m, submatrix_mulVec_equiv, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id, comp_equiv_dotProduct_comp_equiv, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

end DirectSum

/-- The vector of `n + (n + n)` modes with the `n` modes at `u` and the ancilla modes at
positions `x` and momenta `0`. -/
private noncomputable def ancillaVec (u x : PhaseIndex n → ℝ) : PhaseIndex (n + (n + n)) → ℝ :=
  fun i => Sum.elim u (Sum.elim (fun k : Fin (n + n) => x (finSumFinEquiv.symm k)) 0)
    (splitPhase i)

/-- Proof device of Theorem 12: `ι(u) = (u, (Cu, 0))`, the `n` modes of `u` followed by `2n`
ancilla modes (labelled by the coordinates of `u`) with positions `Cu` and momenta `0`. -/
private noncomputable def ancillaEmbedding (C : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    (PhaseIndex n → ℝ) →ₗ[ℝ] (PhaseIndex (n + (n + n)) → ℝ) where
  toFun u i := Sum.elim u
    (Sum.elim (fun m : Fin (n + n) => (C *ᵥ u) (finSumFinEquiv.symm m)) 0) (splitPhase i)
  map_add' u v := by
    funext i
    dsimp only [Pi.add_apply]
    rcases splitPhase i with a | (b | b) <;> simp [mulVec_add]
  map_smul' c u := by
    funext i
    dsimp only [Pi.smul_apply, RingHom.id_apply]
    rcases splitPhase i with a | (b | b) <;> simp [mulVec_smul]

private theorem ancillaEmbedding_apply (C : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (u : PhaseIndex n → ℝ) : ancillaEmbedding C u = ancillaVec u (C *ᵥ u) := rfl

private theorem ancillaVec_add (u x u' x' : PhaseIndex n → ℝ) :
    ancillaVec u x + ancillaVec u' x' = ancillaVec (u + u') (x + x') := by
  funext i
  simp only [ancillaVec, Pi.add_apply]
  rcases splitPhase i with a | (b | b) <;> simp

/-- `σ'` on ancilla vectors: the ancilla momenta vanish, so only the `n` modes contribute. -/
private theorem symplecticBilin_ancillaVec (u x u' x' : PhaseIndex n → ℝ) :
    symplecticBilin (n + (n + n)) (ancillaVec u x) (ancillaVec u' x') = symplecticBilin n u u' := by
  have h0 : ∀ a a' : Fin (n + n) → ℝ, (Sum.elim a 0 : PhaseIndex (n + n) → ℝ) ⬝ᵥ
      symplecticForm (n + n) *ᵥ Sum.elim a' 0 = 0 := fun a a' => by
    have := symplecticBilin_apply (n := n + n) (Sum.elim a 0) (Sum.elim a' 0)
    rw [symplecticBilin, Matrix.toBilin'_apply'] at this
    rw [this]
    simp
  unfold ancillaVec
  rw [symplecticBilin, Matrix.toBilin'_apply', symplecticForm_directSum,
    dotProduct_directSumCov_mulVec, h0, add_zero, ← Matrix.toBilin'_apply']
  rfl

/-- Theorem 12, step 1: `σ'(ιu, ιv) = σ(u, v)`. -/
private theorem symplecticBilin_ancillaEmbedding (C : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (u v : PhaseIndex n → ℝ) :
    symplecticBilin (n + (n + n)) (ancillaEmbedding C u) (ancillaEmbedding C v) =
      symplecticBilin n u v :=
  symplecticBilin_ancillaVec _ _ _ _

/-- The Gaussian function of `((d, 0), γ₀ ⊕ 1)` on ancilla vectors. -/
private theorem gaussianCharFun_ancillaVec (γ₀ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (d u x : PhaseIndex n → ℝ) :
    gaussianCharFun (fun i => Sum.elim d 0 (splitPhase i)) (directSumCov γ₀ 1) (ancillaVec u x) =
      Complex.exp (-((symplecticBilin n u d : ℝ) : ℂ) * Complex.I -
        ((u ⬝ᵥ (symplecticForm n * γ₀ * (symplecticForm n)ᵀ) *ᵥ u + x ⬝ᵥ x : ℝ) : ℂ) / 4) := by
  have hd : (fun i => Sum.elim d 0 (splitPhase i)) = ancillaVec d 0 := by
    funext i
    simp only [ancillaVec]
    rcases splitPhase i with a | (b | b) <;> rfl
  have hM : symplecticForm (n + (n + n)) * directSumCov γ₀ 1 * (symplecticForm (n + (n + n)))ᵀ =
      directSumCov (symplecticForm n * γ₀ * (symplecticForm n)ᵀ) 1 := by
    rw [symplecticForm_directSum, transpose_directSumCov, directSumCov_mul, directSumCov_mul,
      Matrix.mul_one, symplecticForm_mul_transpose_self]
  have hx : (fun k : Fin (n + n) => x (finSumFinEquiv.symm k)) ⬝ᵥ
      (fun k : Fin (n + n) => x (finSumFinEquiv.symm k)) = x ⬝ᵥ x :=
    comp_equiv_dotProduct_comp_equiv (x := x) (y := x) finSumFinEquiv.symm
  rw [gaussianCharFun, hd, symplecticBilin_ancillaVec, hM]
  unfold ancillaVec
  rw [dotProduct_directSumCov_mulVec, one_mulVec]
  congr 3
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    mul_zero, sum_const_zero, add_zero] at hx ⊢
  rw [hx]

/-- Theorem 12, step 1: with `C` symmetric and `C² = Ω(γ - γ₀)Ωᵀ`, the Gaussian function of
`((d, 0), γ₀ ⊕ 1)` composed with `ι` is that of `(d, γ)`. -/
private theorem gaussianCharFun_ancillaEmbedding {C γ γ₀ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hC : Cᵀ = C) (hC2 : C * C = symplecticForm n * (γ - γ₀) * (symplecticForm n)ᵀ)
    (d u : PhaseIndex n → ℝ) :
    gaussianCharFun (fun i => Sum.elim d 0 (splitPhase i)) (directSumCov γ₀ 1)
        (ancillaEmbedding C u) = gaussianCharFun d γ u := by
  rw [ancillaEmbedding_apply, gaussianCharFun_ancillaVec, gaussianCharFun]
  have hCu : (C *ᵥ u) ⬝ᵥ (C *ᵥ u) =
      u ⬝ᵥ (symplecticForm n * (γ - γ₀) * (symplecticForm n)ᵀ) *ᵥ u := by
    rw [← dotProduct_transpose_mulVec C u (C *ᵥ u), hC, mulVec_mulVec, hC2]
  rw [hCu, ← dotProduct_add, ← add_mulVec, ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel]

/-- Theorem 12, step 4: if `A W(v) = W(ιv) A` for every `v` and `W(w)` commutes with every
`W(ιv)`, then `A* W(w) A` commutes with every `W(v)`. -/
private theorem commute_adjoint_comp_weylOp {n' : ℕ}
    (A : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n'))
    (ι : (PhaseIndex n → ℝ) →ₗ[ℝ] (PhaseIndex n' → ℝ))
    (hA : ∀ v, A.comp (weylOp v : 𝔹 n) = (weylOp (ι v) : 𝔹 n').comp A)
    (w : PhaseIndex n' → ℝ)
    (hw : ∀ v, (weylOp w : 𝔹 n') * weylOp (ι v) = (weylOp (ι v) : 𝔹 n') * weylOp w)
    (v : PhaseIndex n → ℝ) :
    Commute ((ContinuousLinearMap.adjoint A).comp ((weylOp w : 𝔹 n').comp A))
      (weylOp v : 𝔹 n) := by
  have hadj : (ContinuousLinearMap.adjoint A).comp (weylOp (ι v) : 𝔹 n') =
      (weylOp v : 𝔹 n).comp (ContinuousLinearMap.adjoint A) := by
    have := congrArg ContinuousLinearMap.adjoint (hA (-v))
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_coe_weylOp, star_coe_weylOp, map_neg, neg_neg, neg_neg] at this
    exact this.symm
  rw [Commute, SemiconjBy, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  calc ((ContinuousLinearMap.adjoint A).comp ((weylOp w : 𝔹 n').comp A)).comp (weylOp v : 𝔹 n)
      = (ContinuousLinearMap.adjoint A).comp (((weylOp w : 𝔹 n') * weylOp (ι v)).comp A) := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.comp_assoc, hA v, ContinuousLinearMap.comp_assoc]
    _ = ((ContinuousLinearMap.adjoint A).comp (weylOp (ι v) : 𝔹 n')).comp
          ((weylOp w : 𝔹 n').comp A) := by
        rw [hw v, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [hadj, ContinuousLinearMap.comp_assoc]

/-- `(c • 1)` for `|c| = 1` is unitary. -/
private theorem smul_one_mem_unitary {c : ℂ} (hc : ‖c‖ = 1) :
    c • (1 : 𝔹 n) ∈ unitary (𝔹 n) := by
  refine Unitary.smul_mem_of_mem ?_ (one_mem _)
  rw [Unitary.mem_iff, Complex.star_def, RCLike.conj_mul, RCLike.mul_conj, hc]
  norm_num

open scoped MatrixOrder in
/-- **Theorem 12.** The covariance matrix of a vector with a Gaussian characteristic function is
symplectic. With `γ₀ ≤ γ` symplectic (Lemma 7) and `C = (Ω(γ - γ₀)Ωᵀ)^{1/2}`, the pure Gaussian
state `φ'` of `((d, 0), γ₀ ⊕ 1)` on `n + 2n` modes has `χ_ψ = χ_φ' ∘ ι` with `ι(u) = (u, (Cu, 0))`;
the intertwiner `T` of Lemma 3 makes `T* W(0, (η, 0)) T` commute with every `W(v)`, so by
irreducibility it is a multiple of `1`, which forces `C = 0`. -/
theorem HasGaussianCharFun.mem_symplecticGroup {ψ : FockSpace (Fin n)} {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (h : HasGaussianCharFun ψ d γ) :
    γ ∈ symplecticGroup (Fin n) ℝ := by
  obtain ⟨γ₀, hγ₀pd, hγ₀s, hΔ⟩ := exists_symplectic_le_of_isAdmissible h.isAdmissible
  -- Step 1: `C = (Ω(γ - γ₀)Ωᵀ)^{1/2}`
  have hΔ' : (symplecticForm n * (γ - γ₀) * (symplecticForm n)ᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hΔ.mul_mul_conjTranspose_same (symplecticForm n)
  set C := CFC.sqrt (symplecticForm n * (γ - γ₀) * (symplecticForm n)ᵀ) with hCdef
  have hC0 : 0 ≤ C := CFC.sqrt_nonneg _
  have hCt : Cᵀ = C := by
    have := (nonneg_iff_posSemidef.1 hC0).1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hCC : C * C = symplecticForm n * (γ - γ₀) * (symplecticForm n)ᵀ :=
    CFC.sqrt_mul_sqrt_self _ (nonneg_iff_posSemidef.2 hΔ')
  -- Step 2: the pure Gaussian state `φ'` of `((d, 0), γ₀ ⊕ 1)` on `n + 2n` modes
  obtain ⟨S₀, hS₀, hγ₀eq⟩ := exists_eq_mul_transpose hγ₀pd hγ₀s
  obtain ⟨U', hU'⟩ := exists_isGaussianUnitary
    (directSumCov_mem_symplecticGroup hS₀ (one_mem (symplecticGroup (Fin (n + n)) ℝ)))
    (fun i => Sum.elim d 0 (splitPhase i))
  have hSS : directSumCov S₀ 1 * (directSumCov S₀ (1 : Matrix (PhaseIndex (n + n))
      (PhaseIndex (n + n)) ℝ))ᵀ = directSumCov γ₀ 1 := by
    rw [transpose_directSumCov, directSumCov_mul, ← hγ₀eq, transpose_one, Matrix.mul_one]
  set φ' := (U' : 𝔹 (n + (n + n))) vacuum
  have hχφ : ∀ w, charFun φ' w =
      gaussianCharFun (fun i => Sum.elim d 0 (splitPhase i)) (directSumCov γ₀ 1) w := fun w => by
    rw [hU'.hasGaussianCharFun_apply_vacuum.2 w, hSS]
  -- Step 3: the intertwiner
  have hψ : ψ ≠ 0 := fun h0 => by
    have := h.norm_eq_one
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨T, ⟨hTψ, hT⟩, -⟩ := exists_unique_linearIsometry_of_charFun_comp (ancillaEmbedding C)
    (symplecticBilin_ancillaEmbedding C) hψ fun u => by
      rw [h.2 u, hχφ, gaussianCharFun_ancillaEmbedding hCt hCC]
  set Tc := T.toContinuousLinearMap
  have hTc : ∀ v, Tc.comp (weylOp v : 𝔹 n) =
      (weylOp (ancillaEmbedding C v) : 𝔹 (n + (n + n))).comp Tc :=
    fun v => ContinuousLinearMap.ext fun x => hT v x
  -- Step 4: `W(0, (η, 0))` commutes with every `W(ιv)`, so `T* W(0, (η, 0)) T = c 1`
  have hcommW : ∀ (η v : PhaseIndex n → ℝ),
      (weylOp (ancillaVec 0 η) : 𝔹 (n + (n + n))) *
          (weylOp (ancillaEmbedding C v) : 𝔹 (n + (n + n))) =
        (weylOp (ancillaEmbedding C v) : 𝔹 (n + (n + n))) * weylOp (ancillaVec 0 η) := by
    intro η v
    rw [weylOp_mul, weylOp_mul, add_comm (ancillaVec 0 η) (ancillaEmbedding C v), Weyl.relPhase,
      Weyl.relPhase, ancillaEmbedding_apply,
      symplecticBilin_ancillaVec, symplecticBilin_ancillaVec, map_zero, LinearMap.zero_apply,
      (symplecticBilin n v).map_zero]
  have hX : ∀ η : PhaseIndex n → ℝ, ∃ c : ℂ, (ContinuousLinearMap.adjoint Tc).comp
      ((weylOp (ancillaVec 0 η) : 𝔹 (n + (n + n))).comp Tc) = c • 1 := by
    intro η
    refine ⟨_, eq_smul_one_of_commute_displacement _ fun α => ?_⟩
    rw [← weylOp_phaseOfComplex]
    exact commute_adjoint_comp_weylOp Tc (ancillaEmbedding C) hTc (ancillaVec 0 η) (hcommW η) _
  -- Step 5: `C = 0`
  have hTapp : ∀ x, Tc x = T x := fun x => rfl
  have hcf : ∀ w, ⟪φ', (weylOp w : 𝔹 (n + (n + n))) φ'⟫_ℂ =
      charFun φ' w := fun w => rfl
  have hG : ∀ η : PhaseIndex n → ℝ, ∃ c : ℂ, ∀ u, c * charFun ψ u =
      gaussianCharFun (fun i => Sum.elim d 0 (splitPhase i)) (directSumCov γ₀ 1)
        (ancillaVec u (η + C *ᵥ u)) := by
    intro η
    obtain ⟨c, hc⟩ := hX η
    refine ⟨c, fun u => ?_⟩
    have h1 := congrArg (fun X : 𝔹 n => ⟪ψ, X ((weylOp u : 𝔹 n) ψ)⟫_ℂ) hc
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      _root_.smul_apply, one_apply_eq_self, inner_smul_right, hTapp] at h1
    rw [charFun, ← h1, hT, hTψ, ← mul_apply_eq_comp, weylOp_mul, _root_.smul_apply,
      inner_smul_right, hcf, hχφ, ancillaEmbedding_apply, ancillaVec_add, zero_add,
      Weyl.relPhase, symplecticBilin_ancillaVec, map_zero, LinearMap.zero_apply]
    simp
  have hCu : ∀ u, C *ᵥ u = 0 := by
    intro u
    obtain ⟨c, hc⟩ := hG (C *ᵥ u)
    have h0 := hc 0
    have hu := hc u
    have hg0 : charFun ψ 0 = 1 := by
      rw [charFun_zero, h.norm_eq_one]
      norm_num
    rw [hg0, mul_one, mulVec_zero, add_zero, gaussianCharFun_ancillaVec] at h0
    rw [h.2 u, ← gaussianCharFun_ancillaEmbedding hCt hCC d u, ancillaEmbedding_apply, h0,
      gaussianCharFun_ancillaVec, gaussianCharFun_ancillaVec] at hu
    have hn := congrArg norm hu
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add] at hn
    have hr := Real.exp_injective hn
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.I_re,
      Complex.neg_im, Complex.ofReal_im, Complex.I_im, Complex.div_ofNat_re, mul_zero, sub_zero,
      zero_mul, neg_zero, zero_dotProduct, add_dotProduct, dotProduct_add] at hr
    have hv : (C *ᵥ u) ⬝ᵥ (C *ᵥ u) = 0 := by linarith
    exact dotProduct_self_eq_zero.1 hv
  have hC : C = 0 := Matrix.toLin'.injective (LinearMap.ext fun u => by
    rw [Matrix.toLin'_apply, hCu u, map_zero, LinearMap.zero_apply])
  have hγ : γ = γ₀ := by
    rw [hC, Matrix.zero_mul] at hCC
    rw [← sub_eq_zero, ← transpose_symplecticForm_mul_conj (γ - γ₀), ← hCC, Matrix.mul_zero,
      Matrix.zero_mul]
  rw [hγ]
  exact hγ₀s

/-! ### Theorem 13 and Corollary 14: the two definitions agree -/

/-- **Theorem 13(b).** If `ψ` has `(d, γ)` and `γ = S Sᵀ` with `S` symplectic, then `ψ = U∣0⟩`
for a Gaussian unitary with data `(S, d)`: by Lemma 11(a), Theorem 8 and Theorem 4. -/
theorem HasGaussianCharFun.exists_isGaussianUnitary {ψ : FockSpace (Fin n)}
    {d : PhaseIndex n → ℝ} {γ S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (h : HasGaussianCharFun ψ d γ) (hS : S ∈ symplecticGroup (Fin n) ℝ) (hγ : γ = S * Sᵀ) :
    ∃ U : unitary (𝔹 n), IsGaussianUnitary U S d ∧ ψ = (U : 𝔹 n) vacuum := by
  obtain ⟨U', hU'⟩ := FockSpace.exists_isGaussianUnitary hS d
  have hv := hU'.hasGaussianCharFun_apply_vacuum
  have hne : (U' : 𝔹 n) vacuum ≠ 0 := fun h0 => by
    have := Unitary.norm_map U' vacuum
    rw [h0, norm_zero, norm_vacuum] at this
    exact zero_ne_one this
  obtain ⟨c, hc, hψc⟩ := exists_eq_smul_of_charFun_eq hne fun u => by rw [h.2, hv.2, hγ]
  set W : unitary (𝔹 n) := ⟨c • 1, smul_one_mem_unitary hc⟩
  have hW : IsGaussianUnitary W 1 0 := isGaussianUnitary_of_eq_smul_one rfl
  have hWU := hW.mul hU'
  rw [Matrix.one_mul, Matrix.one_mulVec, zero_add] at hWU
  refine ⟨W * U', hWU, ?_⟩
  rw [hψc, MulMemClass.coe_mul, mul_apply_eq_comp]
  rfl

/-- **Theorem 13(a).** The two definitions agree: `ψ` is a pure Gaussian state if and only if it
has a Gaussian characteristic function. -/
theorem isPureGaussian_iff_exists_hasGaussianCharFun {ψ : FockSpace (Fin n)} :
    IsPureGaussian ψ ↔ ∃ (d : PhaseIndex n → ℝ) (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ),
      HasGaussianCharFun ψ d γ := by
  constructor
  · rintro ⟨U, S, d, hU, rfl⟩
    exact ⟨d, S * Sᵀ, hU.hasGaussianCharFun_apply_vacuum⟩
  · rintro ⟨d, γ, h⟩
    obtain ⟨S, hS, hγ⟩ := exists_eq_mul_transpose h.isAdmissible.posDef h.mem_symplecticGroup
    obtain ⟨U, hU, hψ⟩ := h.exists_isGaussianUnitary hS hγ
    exact ⟨U, S, d, hU, hψ⟩

/-- **Corollary 14**, the paper's "completely characterized by its displacement vector and
covariance matrix" for pure states: two vectors with the same Gaussian characteristic function
differ by a phase. -/
theorem HasGaussianCharFun.exists_eq_smul {ψ φ : FockSpace (Fin n)} {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hψ : HasGaussianCharFun ψ d γ)
    (hφ : HasGaussianCharFun φ d γ) : ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  have hne : ψ ≠ 0 := fun h0 => by
    have := hψ.norm_eq_one
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact exists_eq_smul_of_charFun_eq hne fun u => by rw [hφ.2, hψ.2]

/-! ### Corollary 14a: existence -/

/-- **Corollary 14a**, existence: every admissible symplectic `γ` and every `d` are the data of
`U∣0⟩` for a Gaussian unitary `U`, by Lemma 11 and Theorem 8. -/
theorem exists_isGaussianUnitary_hasGaussianCharFun {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hγ : IsAdmissible γ)
    (hγs : γ ∈ symplecticGroup (Fin n) ℝ) :
    ∃ (U : unitary (𝔹 n)) (S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ),
      IsGaussianUnitary U S d ∧ HasGaussianCharFun ((U : 𝔹 n) vacuum) d γ := by
  obtain ⟨S, hS, rfl⟩ := exists_eq_mul_transpose hγ.posDef hγs
  obtain ⟨U, hU⟩ := FockSpace.exists_isGaussianUnitary hS d
  exact ⟨U, S, hU, hU.hasGaussianCharFun_apply_vacuum⟩

/-- **Corollary 14a**, characterization: a vector with displacement vector `d` and covariance
matrix `γ` exists if and only if `γ` is admissible and symplectic. -/
theorem exists_hasGaussianCharFun_iff {d : PhaseIndex n → ℝ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    (∃ ψ : FockSpace (Fin n), HasGaussianCharFun ψ d γ) ↔
      IsAdmissible γ ∧ γ ∈ symplecticGroup (Fin n) ℝ := by
  constructor
  · rintro ⟨ψ, h⟩
    exact ⟨h.isAdmissible, h.mem_symplecticGroup⟩
  · rintro ⟨hγ, hγs⟩
    obtain ⟨U, -, -, h⟩ := exists_isGaussianUnitary_hasGaussianCharFun (d := d) hγ hγs
    exact ⟨_, h⟩

end FockSpace

/-! ### Lemma 15: inverting the paper's (8) -/

/-- **Lemma 15(a).** `τ` maps `ℂ` onto the open unit disc: for `|τ₀| < 1`,
`ζ = artanh(|τ₀|) τ₀/|τ₀|` (`ζ = 0` if `τ₀ = 0`) has `τ(ζ) = τ₀`. -/
theorem exists_tanhPhase_eq {τ₀ : ℂ} (hτ₀ : ‖τ₀‖ < 1) : ∃ ζ : ℂ, tanhPhase ζ = τ₀ := by
  rcases eq_or_ne τ₀ 0 with rfl | h0
  · exact ⟨0, tanhPhase_zero⟩
  have ht0 : 0 < ‖τ₀‖ := norm_pos_iff.2 h0
  have hr : Real.tanh (Real.artanh ‖τ₀‖) = ‖τ₀‖ := Real.tanh_artanh ⟨by linarith, hτ₀⟩
  have hr0 : 0 < Real.artanh ‖τ₀‖ := Real.artanh_pos ⟨ht0, hτ₀⟩
  refine ⟨((Real.artanh ‖τ₀‖ / ‖τ₀‖ : ℝ) : ℂ) * τ₀, ?_⟩
  have hn : ‖((Real.artanh ‖τ₀‖ / ‖τ₀‖ : ℝ) : ℂ) * τ₀‖ = Real.artanh ‖τ₀‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hr0.le ht0.le),
      div_mul_cancel₀ _ ht0.ne']
  have hne : ((Real.artanh ‖τ₀‖ / ‖τ₀‖ : ℝ) : ℂ) * τ₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, hn]
    exact hr0.ne'
  simp only [tanhPhase, hne, ↓reduceIte, hn, hr]
  have h1 : (‖τ₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
  have h2 : (Real.artanh ‖τ₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  push_cast
  field_simp

/-- **Lemma 15(a).** `cosh |ζ| = (1 - |τ(ζ)|²)^{-1/2}`. -/
theorem cosh_norm_eq_of_tanhPhase (ζ : ℂ) :
    Real.cosh ‖ζ‖ = (1 - ‖tanhPhase ζ‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hc := Real.cosh_pos ‖ζ‖
  have h : 1 - ‖tanhPhase ζ‖ ^ 2 = (Real.cosh ‖ζ‖ ^ 2)⁻¹ := by
    rw [norm_tanhPhase, Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
    linarith [Real.cosh_sq_sub_sinh_sq ‖ζ‖]
  rw [h, Real.rpow_neg (inv_nonneg.2 (sq_nonneg _)), Real.inv_rpow (sq_nonneg _), inv_inv,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]

/-- The parameters of one mode of `M_ζ` for `τ(ζ) = -2κ`, `ζ ≠ 0`: with `r = |ζ|`, `t = tanh r`,
`(x, y) = (Re ζ, Im ζ)/r`, `cosh² r (1 - t²) = 1`, `sinh r = t cosh r`, `x² + y² = 1`,
`|κ|² = t²/4` and `κ = -t(x + iy)/2`. -/
private theorem squeeze_params {ζ κ : ℂ} (hζ : tanhPhase ζ = -2 * κ) (h : ζ ≠ 0) :
    Real.cosh ‖ζ‖ ^ 2 * (1 - Real.tanh ‖ζ‖ ^ 2) = 1 ∧
      Real.sinh ‖ζ‖ = Real.tanh ‖ζ‖ * Real.cosh ‖ζ‖ ∧
      (ζ.re / ‖ζ‖) ^ 2 + (ζ.im / ‖ζ‖) ^ 2 = 1 ∧ ‖κ‖ ^ 2 = Real.tanh ‖ζ‖ ^ 2 / 4 ∧
      κ.re = -(Real.tanh ‖ζ‖ * (ζ.re / ‖ζ‖)) / 2 ∧
      κ.im = -(Real.tanh ‖ζ‖ * (ζ.im / ‖ζ‖)) / 2 := by
  have hr : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 h
  have hs : Real.sinh ‖ζ‖ = Real.tanh ‖ζ‖ * Real.cosh ‖ζ‖ := by
    rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ (Real.cosh_pos _).ne']
  have hτ : tanhPhase ζ = ζ * ((Real.tanh ‖ζ‖ / ‖ζ‖ : ℝ) : ℂ) := by
    simp only [tanhPhase, h, ↓reduceIte]
  have hκ : κ = -(ζ * ((Real.tanh ‖ζ‖ / ‖ζ‖ : ℝ) : ℂ)) / 2 := by
    rw [← hτ, hζ]
    ring
  refine ⟨?_, hs, ?_, ?_, ?_, ?_⟩
  · have := Real.cosh_sq_sub_sinh_sq ‖ζ‖
    rw [hs] at this
    linear_combination this
  · rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hr),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  · have : ‖κ‖ = ‖tanhPhase ζ‖ / 2 := by
      rw [hζ, norm_mul, norm_neg]
      norm_num
    rw [this, norm_tanhPhase]
    ring
  · rw [hκ]
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  · rw [hκ]
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero]
    ring

/-- **Lemma 15(c).** `M_ζ² = γ_κ` for `τ(ζ) = -2κ`: for each mode `j` the `2 × 2` matrix on
`(qⱼ, pⱼ)` is `(1 - 4|κⱼ|²)⁻¹ [[1 + 4|κⱼ|² + 4 Re κⱼ, 4 Im κⱼ], [4 Im κⱼ, 1 + 4|κⱼ|² - 4 Re κⱼ]]`,
and there are no entries between different modes. -/
theorem squeezeSymplectic_mul_self {n : ℕ} {ζ κ : Fin n → ℂ}
    (hζ : ∀ j, tanhPhase (ζ j) = -2 * κ j) :
    squeezeSymplectic ζ * squeezeSymplectic ζ =
      fromBlocks (diagonal fun j => (1 + 4 * ‖κ j‖ ^ 2 + 4 * (κ j).re) / (1 - 4 * ‖κ j‖ ^ 2))
        (diagonal fun j => 4 * (κ j).im / (1 - 4 * ‖κ j‖ ^ 2))
        (diagonal fun j => 4 * (κ j).im / (1 - 4 * ‖κ j‖ ^ 2))
        (diagonal fun j => (1 + 4 * ‖κ j‖ ^ 2 - 4 * (κ j).re) / (1 - 4 * ‖κ j‖ ^ 2)) := by
  rw [squeezeSymplectic, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> refine congrArg diagonal (funext fun j => ?_) <;>
  · rcases eq_or_ne (ζ j) 0 with h | h
    · have hk : κ j = 0 := by
        have := hζ j
        rw [h, tanhPhase_zero] at this
        linear_combination this / 2
      simp [h, hk]
    · obtain ⟨hA, hs, hB, hn, hre, him⟩ := squeeze_params (hζ j) h
      simp only [h, ↓reduceIte]
      simp only [hn, hre, him]
      generalize Real.cosh ‖ζ j‖ = c at *
      generalize Real.sinh ‖ζ j‖ = s at *
      generalize Real.tanh ‖ζ j‖ = t at *
      generalize (ζ j).re / ‖ζ j‖ = x at *
      generalize (ζ j).im / ‖ζ j‖ = y at *
      subst hs
      have hden : 1 - 4 * (t ^ 2 / 4) ≠ 0 := by
        intro h0
        rw [show 1 - t ^ 2 = 1 - 4 * (t ^ 2 / 4) by ring, h0, mul_zero] at hA
        exact zero_ne_one hA
      rw [eq_div_iff hden]
      first
        | linear_combination (1 - 2 * t * x + t ^ 2 * (x ^ 2 + y ^ 2)) * hA + t ^ 2 * hB
        | linear_combination (-2 * t * y) * hA
        | linear_combination (1 + 2 * t * x + t ^ 2 * (x ^ 2 + y ^ 2)) * hA + t ^ 2 * hB

namespace FockSpace

open FormalFock

/-- **Lemma 15(b)**, the paper's (8) inverted: for `τ(ζⱼ) = -2κⱼ` and
`αⱼ = (ℓⱼ + 2κⱼℓ̄ⱼ)/(1 - 4|κⱼ|²)`, so that `ℓⱼ = αⱼ - 2κⱼᾱⱼ`,
`⊗ⱼ g(κⱼ, ℓⱼ) = ∏ⱼ (1 - 4|κⱼ|²)^{-1/4} e^{|αⱼ|²/2 - κⱼᾱⱼ²} D(α) S(ζ)∣0⟩`. -/
theorem tensorVec_gaussVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (κ ℓ ζ : ι → ℂ)
    (hζ : ∀ j, tanhPhase (ζ j) = -2 * κ j) :
    tensorVec (fun j => gaussVec (κ j) (ℓ j)) =
      (∏ j, ((((1 - 4 * ‖κ j‖ ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((‖(ℓ j + 2 * κ j * conj (ℓ j)) / (1 - 4 * ‖κ j‖ ^ 2)‖ ^ 2 : ℝ) : ℂ) / 2 -
            κ j * conj ((ℓ j + 2 * κ j * conj (ℓ j)) / (1 - 4 * ‖κ j‖ ^ 2)) ^ 2))) •
        toFormal ((displacement (fun j => (ℓ j + 2 * κ j * conj (ℓ j)) /
            (1 - 4 * ‖κ j‖ ^ 2)) : FockSpace ι →L[ℂ] FockSpace ι)
          ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum)) := by
  set α : ι → ℂ := fun j => (ℓ j + 2 * κ j * conj (ℓ j)) / (1 - 4 * ‖κ j‖ ^ 2) with hαdef
  have hκ : ∀ j, ‖κ j‖ < 1 / 2 := fun j => by
    have h1 := norm_tanhPhase_lt_one (ζ j)
    rw [hζ, norm_mul, norm_neg] at h1
    norm_num at h1
    linarith
  have hc : ∀ j, 0 < 1 - 4 * ‖κ j‖ ^ 2 := fun j => by
    nlinarith [hκ j, norm_nonneg (κ j)]
  have hc' : ∀ j, (1 - 4 * ‖κ j‖ ^ 2 : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (hc j).ne'
  have hℓ : ∀ j, α j + tanhPhase (ζ j) * conj (α j) = ℓ j := fun j => by
    have hn : κ j * conj (κ j) = ((‖κ j‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]
      push_cast
      rfl
    have hcr : conj ((1 : ℂ) - 4 * (‖κ j‖ : ℂ) ^ 2) = 1 - 4 * (‖κ j‖ : ℂ) ^ 2 := by
      rw [map_sub, map_mul, map_one, map_pow, Complex.conj_ofReal, map_ofNat]
    rw [hζ, hαdef]
    simp only [map_div₀, map_add, map_mul, Complex.conj_conj, map_ofNat, hcr]
    field_simp [hc' j]
    push_cast at hn
    linear_combination (-4 * ℓ j) * hn
  have hk : ∀ j, -tanhPhase (ζ j) / 2 = κ j := fun j => by rw [hζ]; ring
  rw [displacement_squeeze_vacuum]
  simp only [hk, hℓ]
  rw [smul_smul]
  suffices h : (∏ j, ((((1 - 4 * ‖κ j‖ ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - κ j * conj (α j) ^ 2))) *
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 -
          ∑ j, tanhPhase (ζ j) * conj (α j) ^ 2 / 2)) = 1 by
    rw [h, one_smul]
  have hcosh : ∀ j, Real.cosh ‖ζ j‖ = (1 - 4 * ‖κ j‖ ^ 2) ^ (-(1 / 2 : ℝ)) := fun j => by
    rw [cosh_norm_eq_of_tanhPhase, hζ, norm_mul, norm_neg]
    norm_num
    ring_nf
  have hK : (∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) = ∏ j, (1 - 4 * ‖κ j‖ ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.finsetProd_rpow _ _ fun j _ => (Real.cosh_pos _).le]
    refine prod_congr rfl fun j _ => ?_
    rw [hcosh, ← Real.rpow_mul (hc j).le]
    norm_num
  rw [hK, prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod]
  have hprod : (∏ j, ((((1 - 4 * ‖κ j‖ ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))) *
      ∏ j, (((1 - 4 * ‖κ j‖ ^ 2) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← prod_mul_distrib]
    refine prod_eq_one fun j _ => ?_
    rw [← Complex.ofReal_mul, ← Real.rpow_add (hc j)]
    norm_num
  calc _ = ((∏ j, ((((1 - 4 * ‖κ j‖ ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))) *
        ∏ j, (((1 - 4 * ‖κ j‖ ^ 2) ^ (1 / 4 : ℝ) : ℝ) : ℂ)) *
        (Complex.exp (∑ j, ((((‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - κ j * conj (α j) ^ 2))) *
          Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 -
            ∑ j, tanhPhase (ζ j) * conj (α j) ^ 2 / 2)) := by ring
    _ = 1 := by
      rw [hprod, one_mul, ← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      simp only [hζ, Complex.ofReal_sum, sum_sub_distrib, sum_div, neg_div, ← sum_neg_distrib]
      ring_nf
      have hsum : ∑ x, ((‖α x‖ ^ 2 : ℝ) : ℂ) * (1 / 2) + ∑ x, ((‖α x‖ ^ 2 : ℝ) : ℂ) * (-1 / 2) =
          0 := by
        rw [← sum_add_distrib]
        exact sum_eq_zero fun j _ => by ring
      rw [sum_neg_distrib]
      linear_combination hsum

/-! ### Non-Gaussianity: the vacuum component -/

/-- The vacuum component `⟨0∣ψ⟩` of a vector of `Γ_s` is its coefficient at the vacuum. -/
theorem inner_vacuum_left {ι : Type*} [DecidableEq ι] (ψ : FockSpace ι) :
    ⟪(vacuum : FockSpace ι), ψ⟫_ℂ = ψ 0 := by
  rw [vacuum, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

/-- `Γ(𝒰)` preserves the vacuum component: `⟨0∣Γ(𝒰)ψ⟩ = ⟨0∣ψ⟩`. -/
theorem inner_vacuum_secondQuantUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (ψ : FockSpace ι) :
    ⟪(vacuum : FockSpace ι), secondQuantUnitary U ψ⟫_ℂ = ⟪(vacuum : FockSpace ι), ψ⟫_ℂ := by
  conv_lhs => rw [← secondQuantRep_vacuum U, secondQuantRep_apply]
  exact (secondQuantUnitary U).inner_map_map _ _

variable {n : ℕ}

/-- **A pure Gaussian state has a nonzero vacuum component.** By the decomposition
`U = c Γ(𝒰) D(α) S(r) Γ(𝒲)` of a Gaussian unitary (the paper's Proposition 5), `Γ(𝒲)` fixing the
vacuum and `Γ(𝒰)` preserving the vacuum component, `⟨0∣U∣0⟩ = c ⟨0∣D(α) S(r)∣0⟩`, a nonzero multiple
of the vacuum coefficient `1` of `⊗ⱼ g(κⱼ, ℓⱼ)` (the paper's (8)). -/
theorem IsPureGaussian.inner_vacuum_ne_zero {ψ : FockSpace (Fin n)}
    (h : IsPureGaussian ψ) : ⟪(vacuum : FockSpace (Fin n)), ψ⟫_ℂ ≠ 0 := by
  obtain ⟨U, S, d, hU, rfl⟩ := h
  obtain ⟨c, 𝒰, 𝒲, α, r, -, hc, hUeq⟩ := hU.exists_decomposition
  have hc0 : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hc; exact zero_ne_one hc
  rw [hUeq, _root_.smul_apply, inner_smul_right, mul_apply_eq_comp, mul_apply_eq_comp,
    mul_apply_eq_comp, secondQuantRep_vacuum, secondQuantRep_apply,
    inner_vacuum_secondQuantUnitary, inner_vacuum_left, ← coeff_toFormal,
    displacement_squeeze_vacuum, coeff_smul, coeff_tensorVec]
  simp only [Finsupp.coe_zero, Pi.zero_apply, coeff_gaussVec, Nat.factorial_zero,
    BosonicLean.cMatrix_zero, mul_one, smul_eq_mul]
  refine mul_ne_zero hc0 (mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) ?_)
  · exact Complex.ofReal_ne_zero.2
      (Real.rpow_pos_of_pos (prod_pos fun j _ => Real.cosh_pos _) _).ne'
  · refine prod_ne_zero_iff.2 fun j _ => ?_
    simp [sqrtC]

/-- A nonzero vector orthogonal to the vacuum is not a multiple of a pure Gaussian state. -/
theorem ne_smul_of_inner_vacuum_eq_zero {Ψ ψ : FockSpace (Fin n)} (hΨ : Ψ ≠ 0)
    (h0 : ⟪(vacuum : FockSpace (Fin n)), Ψ⟫_ℂ = 0) (hψ : IsPureGaussian ψ) (c : ℂ) :
    Ψ ≠ c • ψ := by
  rintro rfl
  rw [inner_smul_right, mul_eq_zero] at h0
  rcases h0 with hc | h
  · exact hΨ (by rw [hc, zero_smul])
  · exact hψ.inner_vacuum_ne_zero h

/-- **Number states are not Gaussian** (Tjoa–Cirac, the remark after (10)): for `m ≠ 0` the number
state `∣m⟩` is not a multiple of a pure Gaussian state. -/
theorem numberState_ne_smul {m : Fin n →₀ ℕ} (hm : m ≠ 0) {ψ : FockSpace (Fin n)}
    (hψ : IsPureGaussian ψ) (c : ℂ) :
    (lp.single 2 m 1 : FockSpace (Fin n)) ≠ c • ψ := by
  refine ne_smul_of_inner_vacuum_eq_zero (fun h => ?_) ?_ hψ c
  · have := congrArg (fun φ : FockSpace (Fin n) => φ m) h
    simp at this
  · rw [inner_vacuum_left, lp.single_apply, Pi.single_eq_of_ne hm.symm]

end FockSpace

end BosonicLean.Fock
