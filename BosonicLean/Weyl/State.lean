/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.Automorphism
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# States on the CCR algebra and Gaussian states

A state on `CCR(V, σ)` is a continuous normalized linear functional with `ω(a⋆a) ≥ 0`.
Its characteristic function `χ(u) = ω(W(u))` has positive semidefinite twisted kernels
and determines the state. A Gaussian state carries a covariance form `γ` and a
displacement `d` with `χ(u) = exp(i d(u) − γ(u,u)/4)`; its covariance satisfies the state
condition `γ + iσ ≥ 0`, in three equivalent forms. A state is bounded by the norm.
-/

open Matrix
open scoped ComplexOrder ComplexConjugate

namespace BosonicLean.Weyl

section General

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : LinearMap.BilinForm ℝ V)

/-- The Weyl operator `W(u)` as an element of `CCR σ`. (QCALean notes: `def:gs-state`) -/
noncomputable def wCCR (u : V) : CCR σ := ⟨weyl σ u, weyl_mem_CCR σ u⟩

/-- A state on `CCR σ`, a continuous linear functional with `ω(1) = 1` and `ω(a⋆a) ≥ 0` in the order
of `ℂ`. (QCALean notes: `def:gs-state`) -/
structure State where
  /-- The functional. -/
  toCLM : CCR σ →L[ℂ] ℂ
  map_one : toCLM 1 = 1
  nonneg : ∀ a : CCR σ, 0 ≤ toCLM (star a * a)

variable {σ}

@[ext] theorem State.ext {ω ω' : State σ} (h : ω.toCLM = ω'.toCLM) : ω = ω' := by
  cases ω; cases ω'; cases h; rfl

/-- The characteristic function `χ_ω(u) = ω(W(u))`. (QCALean notes: `def:gs-chi`) -/
noncomputable def State.charFun (ω : State σ) (u : V) : ℂ := ω.toCLM (wCCR σ u)

theorem wCCR_zero : wCCR σ 0 = 1 := Subtype.ext (weyl_zero σ)

/-- The Weyl relation in `CCR(V, σ)`: `W(u) W(w) = e^{−iσ(u,w)/2} W(u + w)`. -/
theorem wCCR_mul (hσ : σ.IsAlt) (u w : V) :
    wCCR σ u * wCCR σ w =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • wCCR σ (u + w) :=
  Subtype.ext (weyl_mul σ hσ u w)

/-- `W(u)⋆ W(w) = e^{iσ(u,w)/2} W(w − u)`. -/
theorem star_wCCR_mul (hσ : σ.IsAlt) (u w : V) :
    star (wCCR σ u) * wCCR σ w =
      Complex.exp (Complex.I * (σ u w : ℂ) / 2) • wCCR σ (w - u) := by
  apply Subtype.ext
  change star (weyl σ u) * weyl σ w = _ • weyl σ (w - u)
  rw [star_weyl σ hσ, weyl_mul σ hσ, neg_add_eq_sub]
  congr 2
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  push_cast
  ring

variable (σ) in
/-- The twisted kernel `K_{jk} = e^{iσ(u_j,u_k)/2} χ(u_k − u_j)`. (QCALean notes: `def:gs-chi`) -/
noncomputable def twistedKernel (χ : V → ℂ) {ι : Type*} (u : ι → V) : Matrix ι ι ℂ :=
  Matrix.of fun j k => Complex.exp (Complex.I * (σ (u j) (u k) : ℂ) / 2) * χ (u k - u j)

/-- (QCALean notes: `def:gs-chi`, `prop:gs-twisted`) -/
theorem State.charFun_zero (ω : State σ) : ω.charFun 0 = 1 := by
  rw [State.charFun, wCCR_zero, ω.map_one]

/-- Twisted positivity, as a sum. (QCALean notes: `prop:gs-twisted`) -/
theorem State.twisted_nonneg (hσ : σ.IsAlt) (ω : State σ) {ι : Type*} [Fintype ι]
    (u : ι → V) (c : ι → ℂ) :
    0 ≤ ∑ j, ∑ k, conj (c j) * c k * twistedKernel σ ω.charFun u j k := by
  have h := ω.nonneg (∑ k, c k • wCCR σ (u k))
  rw [star_sum, Finset.sum_mul_sum] at h
  convert h using 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_smul, smul_mul_smul, star_wCCR_mul hσ, smul_smul, map_smul, twistedKernel,
    Matrix.of_apply, State.charFun, smul_eq_mul]
  simp only [Complex.star_def]
  ring

/-- The complex quadratic form as a double sum. -/
theorem star_dotProduct_mulVec_eq {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ (K *ᵥ c) = ∑ j, ∑ k, conj (c j) * c k * K j k := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A complex matrix with non-negative quadratic form is positive semidefinite. -/
theorem posSemidef_of_nonneg {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ)
    (h : ∀ c : ι → ℂ, 0 ≤ ∑ j, ∑ k, conj (c j) * c k * K j k) : K.PosSemidef := by
  classical
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => by
    rw [star_dotProduct_mulVec_eq]; exact h c
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have hv := h (WithLp.ofLp v)
  rw [← star_dotProduct_mulVec_eq] at hv
  have hre : conj (star (WithLp.ofLp v) ⬝ᵥ (K *ᵥ WithLp.ofLp v)) =
      star (WithLp.ofLp v) ⬝ᵥ (K *ᵥ WithLp.ofLp v) :=
    Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hv).2.symm
  have hin : inner ℂ (K.toEuclideanLin v) v =
      conj (star (WithLp.ofLp v) ⬝ᵥ (K *ᵥ WithLp.ofLp v)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, toEuclideanLin]
    rw [← Complex.star_def, ← star_dotProduct_star, star_star, dotProduct_comm]
  rw [hin, hre]
  exact hre

/-- Twisted positivity, as positive semidefiniteness of the twisted kernel. (QCALean notes:
`prop:gs-twisted`) -/
theorem State.twistedKernel_posSemidef (hσ : σ.IsAlt) (ω : State σ) {ι : Type*} [Finite ι]
    (u : ι → V) : (twistedKernel σ ω.charFun u).PosSemidef :=
  have := Fintype.ofFinite ι
  posSemidef_of_nonneg _ (ω.twisted_nonneg hσ u)

/-- `χ(−u) = conj χ(u)`. (QCALean notes: `prop:gs-twisted`)
-/
theorem State.charFun_neg (hσ : σ.IsAlt) (ω : State σ) (u : V) :
    ω.charFun (-u) = conj (ω.charFun u) := by
  have h := (ω.twistedKernel_posSemidef hσ ![0, u]).1.apply 1 0
  simp only [twistedKernel, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    zero_div, Complex.exp_zero, one_mul, sub_zero, zero_sub] at h
  rw [← h, Complex.star_def]

/-- `|χ(u)| ≤ 1`. (QCALean notes: `prop:gs-twisted`) -/
theorem State.norm_charFun_le (hσ : σ.IsAlt) (ω : State σ) (u : V) : ‖ω.charFun u‖ ≤ 1 := by
  have h := ω.twisted_nonneg hσ ![0, u] ![-ω.charFun u, 1]
  have hσu : σ u u = 0 := hσ u
  simp only [twistedKernel, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_zero, LinearMap.zero_apply, hσu,
    Complex.ofReal_zero, mul_zero, zero_div, Complex.exp_zero, one_mul, sub_zero, zero_sub,
    sub_self, ω.charFun_zero, ω.charFun_neg hσ] at h
  have hre := (Complex.nonneg_iff.1 h).1
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, map_neg] at hre
  have hn : ‖ω.charFun u‖ ^ 2 = (ω.charFun u).re ^ 2 + (ω.charFun u).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg (ω.charFun u)]

/-- A state is determined by its characteristic function. (QCALean notes: `prop:gs-pullback`) -/
theorem State.ext_charFun (hσ : σ.IsAlt) {ω ω' : State σ}
    (h : ∀ u, ω.charFun u = ω'.charFun u) : ω = ω' := by
  ext1
  have hW : Set.EqOn ω.toCLM ω'.toCLM (Set.range (CCR.weylSystem σ hσ).W) := by
    rintro _ ⟨u, rfl⟩; exact h u
  have hcl := (LinearMap.eqOn_span' (f := ω.toCLM.toLinearMap) (g := ω'.toCLM.toLinearMap)
    hW).closure ω.toCLM.continuous ω'.toCLM.continuous
  exact ContinuousLinearMap.ext fun y => hcl (weyl_mem_closure_span _ hσ y)

/-- The pullback `ω ∘ α` of a state along a star-automorphism. (QCALean notes: `prop:gs-pullback`)
-/
noncomputable def State.comp (ω : State σ) (α : CCR σ ≃⋆ₐ[ℂ] CCR σ) : State σ where
  toCLM := ω.toCLM.comp ⟨α.toAlgEquiv.toLinearEquiv.toLinearMap,
    AddMonoidHomClass.continuous_of_bound α 1 fun x => by
      rw [StarAlgEquiv.norm_map, one_mul]⟩
  map_one := by
    change ω.toCLM (α 1) = 1
    rw [_root_.map_one]; exact ω.map_one
  nonneg a := by
    change 0 ≤ ω.toCLM (α (star a * a))
    rw [map_mul, map_star]
    exact ω.nonneg _

/-- (QCALean notes: `prop:gs-pullback`) -/
@[simp] theorem State.comp_apply (ω : State σ) (α : CCR σ ≃⋆ₐ[ℂ] CCR σ) (a : CCR σ) :
    (ω.comp α).toCLM a = ω.toCLM (α a) := rfl

theorem State.comp_comp (ω : State σ) (α β : CCR σ ≃⋆ₐ[ℂ] CCR σ) :
    (ω.comp α).comp β = ω.comp (β.trans α) := rfl

/-- `χ_{ω ∘ α} = χ_ω ∘ T` when `α(W(u)) = W(T u)`. (QCALean notes: `prop:gs-pullback`) -/
theorem State.comp_charFun (ω : State σ) (α : CCR σ ≃⋆ₐ[ℂ] CCR σ) (T : V → V)
    (hT : ∀ u, α (wCCR σ u) = wCCR σ (T u)) (u : V) :
    (ω.comp α).charFun u = ω.charFun (T u) := by
  rw [State.charFun, State.comp_apply, hT]; rfl

end General

section StateCondition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The state condition (c), in real-pair form: `γ(u,u) ≥ 0` and `σ(u,w)² ≤ γ(u,u) γ(w,w)`. (QCALean
notes: `def:gs-statecond`) -/
def IsStateCondition (γ σ : LinearMap.BilinForm ℝ V) : Prop :=
  (∀ u, 0 ≤ γ u u) ∧ ∀ u w, σ u w ^ 2 ≤ γ u u * γ w w

/-- The state condition (b), in pair form: `2 σ(a,b) ≤ γ(a,a) + γ(b,b)`. (QCALean notes:
`def:gs-statecond`) -/
def IsStateConditionPair (γ σ : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ a b, 2 * σ a b ≤ γ a a + γ b b

/-- The state condition (a): `γ + iσ ≥ 0` on every finite family. (QCALean notes:
`def:gs-statecond`) -/
def IsStateConditionC (γ σ : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ (m : ℕ) (u : Fin m → V),
    (Matrix.of fun j k => (γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)).PosSemidef

/-- A bilinear form on two linear combinations of a family. -/
theorem bilin_sum_sum (B : LinearMap.BilinForm ℝ V) {ι : Type*} [Fintype ι] (u : ι → V)
    (x y : ι → ℝ) :
    B (∑ j, x j • u j) (∑ k, y k • u k) = ∑ j, ∑ k, x j * y k * B (u j) (u k) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The quadratic form of `γ + iσ` on `μ = Σ c_k u_k = a + i b` is `γ(a,a) + γ(b,b) − 2σ(a,b)`. -/
theorem sum_conj_mul_stateMatrix {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm)
    (hσ : σ.IsAlt) {ι : Type*} [Fintype ι] (u : ι → V) (c : ι → ℂ) :
    ∑ j, ∑ k, conj (c j) * c k * ((γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)) =
      ((γ (∑ k, (c k).re • u k) (∑ k, (c k).re • u k) +
        γ (∑ k, (c k).im • u k) (∑ k, (c k).im • u k) -
        2 * σ (∑ k, (c k).re • u k) (∑ k, (c k).im • u k) : ℝ) : ℂ) := by
  set a := ∑ k, (c k).re • u k
  set b := ∑ k, (c k).im • u k
  have hre : (∑ j, ∑ k, conj (c j) * c k *
      ((γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ))).re =
      γ a a + γ b b - σ a b + σ b a := by
    simp only [a, b, bilin_sum_sum, Complex.re_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (∑ j, ∑ k, conj (c j) * c k *
      ((γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ))).im =
      γ a b - γ b a + σ a a + σ b b := by
    simp only [a, b, bilin_sum_sum, Complex.im_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  apply Complex.ext
  · rw [hre, Complex.ofReal_re, isAlt_swap hσ]; ring
  · rw [him, Complex.ofReal_im, hγ.eq a b, hσ a, hσ b]; ring

/-- The matrix of `γ + iσ` on a family is Hermitian. -/
theorem isHermitian_stateMatrix {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm)
    (hσ : σ.IsAlt) {ι : Type*} (u : ι → V) :
    (Matrix.of fun j k => (γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_add, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, hγ.eq (u k) (u j), isAlt_swap hσ (u k) (u j),
    Complex.ofReal_neg]
  ring

/-- The state conditions (a) and (b) are equivalent. (QCALean notes: `prop:gs-statecond`) -/
theorem isStateConditionC_iff_pair {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm)
    (hσ : σ.IsAlt) : IsStateConditionC γ σ ↔ IsStateConditionPair γ σ := by
  constructor
  · intro h a b
    have h2 := (posSemidef_iff_dotProduct_mulVec.1 (h 2 ![a, b])).2 ![1, Complex.I]
    rw [star_dotProduct_mulVec_eq] at h2
    simp only [Matrix.of_apply] at h2
    rw [sum_conj_mul_stateMatrix hγ hσ, Complex.zero_le_real] at h2
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, one_smul, zero_smul, add_zero,
      zero_add] at h2
    linarith
  · intro h m u
    refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_stateMatrix hγ hσ u) fun c => ?_
    rw [star_dotProduct_mulVec_eq]
    simp only [Matrix.of_apply]
    rw [sum_conj_mul_stateMatrix hγ hσ, Complex.zero_le_real]
    linarith [h (∑ k, (c k).re • u k) (∑ k, (c k).im • u k)]

/-- The state conditions (b) and (c) are equivalent. (QCALean notes: `prop:gs-statecond`) -/
theorem isStateConditionPair_iff {γ σ : LinearMap.BilinForm ℝ V} :
    IsStateConditionPair γ σ ↔ IsStateCondition γ σ := by
  constructor
  · intro h
    have hpos : ∀ u, 0 ≤ γ u u := fun u => by simpa using h u 0
    refine ⟨hpos, fun u w => ?_⟩
    have hq : ∀ t : ℝ, 0 ≤ γ u u * (t * t) + (-2 * σ u w) * t + γ w w := fun t => by
      have := h (t • u) w
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      linear_combination this
    have := discrim_le_zero hq
    rw [discrim] at this
    linear_combination this / 4
  · rintro ⟨hpos, h⟩ a b
    have ha := hpos a
    have hb := hpos b
    have hab := h a b
    nlinarith [sq_nonneg (γ a a - γ b b), sq_nonneg (2 * σ a b - (γ a a + γ b b))]

/-- The state condition (a) is equivalent to its real-pair form (c). (QCALean notes:
`prop:gs-statecond`) -/
theorem isStateConditionC_iff {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm) (hσ : σ.IsAlt) :
    IsStateConditionC γ σ ↔ IsStateCondition γ σ :=
  (isStateConditionC_iff_pair hγ hσ).trans isStateConditionPair_iff

/-- The real-pair form does not depend on the sign of `σ`. -/
theorem isStateCondition_neg {γ σ : LinearMap.BilinForm ℝ V} :
    IsStateCondition γ (-σ) ↔ IsStateCondition γ σ := by
  simp [IsStateCondition]

/-- The state condition with `γ − iσ` in place of `γ + iσ`. (QCALean notes: `prop:gs-statecond`) -/
theorem isStateConditionC_neg {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm)
    (hσ : σ.IsAlt) : IsStateConditionC γ (-σ) ↔ IsStateConditionC γ σ := by
  rw [isStateConditionC_iff hγ (fun x => by simp [hσ x]), isStateConditionC_iff hγ hσ,
    isStateCondition_neg]

/-- The state condition is preserved by sums: `γ₁ + iσ₁ ≥ 0` and `γ₂ + iσ₂ ≥ 0` give
`(γ₁ + γ₂) + i(σ₁ + σ₂) ≥ 0`. -/
theorem IsStateConditionC.add {γ₁ σ₁ γ₂ σ₂ : LinearMap.BilinForm ℝ V}
    (h₁ : IsStateConditionC γ₁ σ₁) (h₂ : IsStateConditionC γ₂ σ₂) :
    IsStateConditionC (γ₁ + γ₂) (σ₁ + σ₂) := by
  intro m u
  convert (h₁ m u).add (h₂ m u) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.add_apply, LinearMap.add_apply]
  push_cast
  ring

/-- The state condition is preserved by pull-back along a linear map:
`γ(f·, f·) + iσ(f·, f·) ≥ 0`. -/
theorem IsStateConditionC.comp {γ σ : LinearMap.BilinForm ℝ V} (h : IsStateConditionC γ σ)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] V) :
    IsStateConditionC (γ.comp f f) (σ.comp f f) :=
  fun m u => h m (fun j => f (u j))

/-- The state condition is preserved by a common non-negative scale. -/
theorem IsStateConditionC.smul {γ σ : LinearMap.BilinForm ℝ V} (h : IsStateConditionC γ σ)
    {c : ℝ} (hc : 0 ≤ c) : IsStateConditionC (c • γ) (c • σ) := by
  intro m u
  have := (h m u).smul (a := (c : ℂ)) (Complex.zero_le_real.2 hc)
  convert this using 1
  ext j k
  simp only [LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Matrix.of_apply,
    Matrix.smul_apply]
  ring

end StateCondition

section Gaussian

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : LinearMap.BilinForm ℝ V}

variable (σ) in
/-- A Gaussian state, a state with a symmetric covariance form `cov` and a displacement `disp` such
that `χ(u) = exp(i disp(u) − cov(u,u)/4)`. (QCALean notes: `def:gs-gaussian`) -/
structure GaussianState extends State σ where
  /-- The covariance form. -/
  cov : LinearMap.BilinForm ℝ V
  isSymm : cov.IsSymm
  /-- The displacement. -/
  disp : V →ₗ[ℝ] ℝ
  charFun_eq : ∀ u, toState.charFun u =
    Complex.exp (Complex.I * (disp u : ℂ) - (cov u u : ℂ) / 4)

namespace GaussianState

theorem charFun_ne_zero (ω : GaussianState σ) (u : V) : ω.charFun u ≠ 0 := by
  rw [ω.charFun_eq]; exact Complex.exp_ne_zero _

/-- The twisted kernel of a Gaussian state on the family `s u_k` factorizes as
`conj χ(s u_j) χ(s u_k) e^{s² H_{jk}}` with `H = (γ + iσ)/2`. -/
theorem twistedKernel_smul (ω : GaussianState σ) {ι : Type*} (w : ι → V) (s : ℝ) (j k : ι) :
    twistedKernel σ ω.charFun (fun i => s • w i) j k =
      conj (ω.charFun (s • w j)) * ω.charFun (s • w k) *
        Complex.exp ((s : ℂ) ^ 2 *
          (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2)) := by
  simp only [twistedKernel, Matrix.of_apply, ω.charFun_eq, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  have h := ω.isSymm.eq (w k) (w j)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat, h]
  push_cast
  ring

/-- The Schur-complement step: for coefficients with `Σ b = 0`,
`Σ conj b_j b_k (e^{s² H_{jk}} − 1) ≥ 0`. -/
theorem sum_exp_sub_one_nonneg_of_sum_eq_zero (hσ : σ.IsAlt) (ω : GaussianState σ)
    {ι : Type*} [Fintype ι] (w : ι → V) (b : ι → ℂ) (hb : ∑ i, b i = 0) (s : ℝ) :
    0 ≤ ∑ j, ∑ k, conj (b j) * b k * (Complex.exp ((s : ℂ) ^ 2 *
      (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2)) - 1) := by
  have h := ω.toState.twisted_nonneg hσ (fun i => s • w i)
    (fun i => b i / ω.charFun (s • w i))
  simp only [ω.twistedKernel_smul] at h
  have e1 : ∀ j k, conj (b j / ω.charFun (s • w j)) * (b k / ω.charFun (s • w k)) *
      (conj (ω.charFun (s • w j)) * ω.charFun (s • w k) * Complex.exp ((s : ℂ) ^ 2 *
        (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2))) =
      conj (b j) * b k * Complex.exp ((s : ℂ) ^ 2 *
        (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2)) := by
    intro j k
    have hj := ω.charFun_ne_zero (s • w j)
    have hk := ω.charFun_ne_zero (s • w k)
    have hj' : conj (ω.charFun (s • w j)) ≠ 0 := (map_ne_zero _).2 hj
    rw [map_div₀]
    field_simp
  simp only [e1] at h
  have e2 : ∑ j, ∑ k, conj (b j) * b k * (Complex.exp ((s : ℂ) ^ 2 *
      (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2)) - 1) =
      ∑ j, ∑ k, conj (b j) * b k * Complex.exp ((s : ℂ) ^ 2 *
        (((ω.cov (w j) (w k) : ℂ) + Complex.I * (σ (w j) (w k) : ℂ)) / 2)) -
      (∑ j, conj (b j)) * ∑ k, b k := by
    rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e2, hb, mul_zero, sub_zero]
  exact h

/-- `Σ conj b_j b_k (e^{s² H_{jk}} − 1) ≥ 0` for every family and all coefficients: the family
`(0, s u_1, …, s u_m)` with the coefficient `−Σ b_k` at `0`. -/
theorem sum_exp_sub_one_nonneg (hσ : σ.IsAlt) (ω : GaussianState σ) {ι : Type*} [Fintype ι]
    (u : ι → V) (b : ι → ℂ) (s : ℝ) :
    0 ≤ ∑ j, ∑ k, conj (b j) * b k * (Complex.exp ((s : ℂ) ^ 2 *
      (((ω.cov (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)) / 2)) - 1) := by
  have h := ω.sum_exp_sub_one_nonneg_of_sum_eq_zero hσ (fun o : Option ι => o.elim 0 u)
    (fun o => o.elim (-∑ i, b i) b) (by simp [Fintype.sum_option]) s
  simpa [Fintype.sum_option] using h

/-- The linear term: `Re Σ conj b_j b_k (γ + iσ)(u_j,u_k) ≥ 0`, from
`|e^z − 1 − z| ≤ |z|²` for `|z| ≤ 1` and an elementary limit. -/
theorem re_sum_nonneg (hσ : σ.IsAlt) (ω : GaussianState σ) {ι : Type*} [Fintype ι]
    (u : ι → V) (b : ι → ℂ) :
    0 ≤ (∑ j, ∑ k, conj (b j) * b k *
      ((ω.cov (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ))).re := by
  set H : ι → ι → ℂ := fun j k =>
    ((ω.cov (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)) / 2 with hH
  set h := (∑ j, ∑ k, conj (b j) * b k * H j k).re with hh
  set C := ∑ j, ∑ k, ‖b j‖ * ‖b k‖ * ‖H j k‖ ^ 2 with hC
  set D := ∑ j, ∑ k, ‖H j k‖ with hD
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have key : ∀ τ : ℝ, 0 < τ → (∀ j k, τ * ‖H j k‖ ≤ 1) → 0 ≤ τ * h + τ ^ 2 * C := by
    intro τ hτ hsmall
    have hB := ω.sum_exp_sub_one_nonneg hσ u b (Real.sqrt τ)
    have hs : ((Real.sqrt τ : ℝ) : ℂ) ^ 2 = (τ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hτ.le]
    rw [hs] at hB
    change 0 ≤ ∑ j, ∑ k, conj (b j) * b k * (Complex.exp ((τ : ℂ) * H j k) - 1) at hB
    have hsplit : ∑ j, ∑ k, conj (b j) * b k * (Complex.exp ((τ : ℂ) * H j k) - 1) =
        (τ : ℂ) * ∑ j, ∑ k, conj (b j) * b k * H j k +
          ∑ j, ∑ k, conj (b j) * b k *
            (Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hR : ∀ j k, ‖Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k‖ ≤
        τ ^ 2 * ‖H j k‖ ^ 2 := by
      intro j k
      have hn : ‖(τ : ℂ) * H j k‖ = τ * ‖H j k‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]
      calc _ ≤ ‖(τ : ℂ) * H j k‖ ^ 2 :=
            Complex.norm_exp_sub_one_sub_id_le (hn ▸ hsmall j k)
        _ = τ ^ 2 * ‖H j k‖ ^ 2 := by rw [hn]; ring
    have hbound : ‖∑ j, ∑ k, conj (b j) * b k *
        (Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k)‖ ≤ τ ^ 2 * C := by
      calc _ ≤ ∑ j, ‖∑ k, conj (b j) * b k *
              (Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k)‖ := norm_sum_le _ _
        _ ≤ ∑ j, ∑ k, ‖b j‖ * ‖b k‖ * (τ ^ 2 * ‖H j k‖ ^ 2) := by
            refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_
            refine Finset.sum_le_sum fun k _ => ?_
            rw [norm_mul, norm_mul, Complex.norm_conj]
            gcongr
            exact hR j k
        _ = τ ^ 2 * C := by
            rw [hC, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
    have hre := (Complex.nonneg_iff.1 hB).1
    rw [hsplit, Complex.add_re, Complex.re_ofReal_mul, ← hh] at hre
    have := le_abs_self (∑ j, ∑ k, conj (b j) * b k *
      (Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k)).re
    have := Complex.abs_re_le_norm (∑ j, ∑ k, conj (b j) * b k *
      (Complex.exp ((τ : ℂ) * H j k) - 1 - (τ : ℂ) * H j k))
    linarith
  have h2 : ∑ j, ∑ k, conj (b j) * b k *
      ((ω.cov (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)) =
      ((2 : ℝ) : ℂ) * ∑ j, ∑ k, conj (b j) * b k * H j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hH]; push_cast; ring
  rw [h2, Complex.re_ofReal_mul, ← hh]
  suffices 0 ≤ h by linarith
  by_contra hneg'
  have hneg : h < 0 := lt_of_not_ge hneg'
  set τ := min (1 / (D + 1)) (-h / (C + 1)) with hτdef
  have hτ : 0 < τ := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hsmall : ∀ j k, τ * ‖H j k‖ ≤ 1 := by
    intro j k
    have hHD : ‖H j k‖ ≤ D :=
      (Finset.single_le_sum (f := fun k => ‖H j k‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, ‖H j k‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j))
    calc τ * ‖H j k‖ ≤ 1 / (D + 1) * (D + 1) :=
          mul_le_mul (min_le_left _ _) (by linarith) (norm_nonneg _) (by positivity)
      _ = 1 := by field_simp
  have h1 : τ * (C + 1) ≤ -h := by
    have := min_le_right (1 / (D + 1)) (-h / (C + 1))
    rwa [← hτdef, le_div_iff₀ (by positivity)] at this
  have := key τ hτ hsmall
  nlinarith [mul_le_mul_of_nonneg_left h1 hτ.le, pow_pos hτ 2]

/-- Necessity (thesis (4.5)–(4.6)): the covariance form of a Gaussian state satisfies the state
condition `γ + iσ ≥ 0`. (QCALean notes: `thm:gs-necessity`) -/
theorem isStateConditionC (hσ : σ.IsAlt) (ω : GaussianState σ) :
    IsStateConditionC ω.cov σ := by
  intro m u
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_stateMatrix ω.isSymm hσ u)
    fun c => ?_
  rw [star_dotProduct_mulVec_eq]
  simp only [Matrix.of_apply]
  have h := ω.re_sum_nonneg hσ u c
  rw [sum_conj_mul_stateMatrix ω.isSymm hσ] at h ⊢
  rw [Complex.ofReal_re] at h
  exact Complex.zero_le_real.2 h

/-- The covariance form of a Gaussian state satisfies the state condition in real-pair form.
(QCALean notes: `thm:gs-necessity`) -/
theorem isStateCondition (hσ : σ.IsAlt) (ω : GaussianState σ) : IsStateCondition ω.cov σ :=
  (isStateConditionC_iff ω.isSymm hσ).1 (ω.isStateConditionC hσ)

/-- The covariance form of a Gaussian state satisfies the state condition in pair form. (QCALean
notes: `thm:gs-necessity`) -/
theorem isStateConditionPair (hσ : σ.IsAlt) (ω : GaussianState σ) :
    IsStateConditionPair ω.cov σ :=
  isStateConditionPair_iff.2 (ω.isStateCondition hσ)

end GaussianState

end Gaussian

section Norm

/-- A normalized functional on a unital C*-algebra that is non-negative on every `a⋆a` is
bounded by the norm, `|φ(a)| ≤ ‖a‖`: Cauchy–Schwarz for the form `φ(a⋆b)`.
(QCALean notes: `lem:cv-norm`) -/
theorem norm_apply_le_of_nonneg_star_mul_self {A : Type*} [CStarAlgebra A] (φ : A →L[ℂ] ℂ)
    (h1 : φ 1 = 1) (hpos : ∀ a, 0 ≤ φ (star a * a)) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ φ.toLinearMap fun x hx => by
    obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hx
    exact hpos y
  have hf : ∀ x, f x = φ x := fun _ => rfl
  have hsq : ∀ x : A, ‖f.toPreGNS x‖ ^ 2 = ‖φ (star x * x)‖ := fun x => by
    have := congrArg norm (f.preGNS_norm_sq (f.toPreGNS x))
    rw [f.ofPreGNS_toPreGNS, hf] at this
    rw [← this]
    simp
  have e1 : ‖f.toPreGNS (1 : A)‖ = 1 := by
    have := hsq 1
    rw [star_one, one_mul, h1, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have ha : ‖f.toPreGNS a‖ ≤ ‖a‖ := by
    have hb := f.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a)
    rw [hf 1, h1, norm_one, one_mul, CStarRing.norm_star_mul_self, hf] at hb
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hsq a, sq]
    exact hb
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS 1) (f.toPreGNS a)
  rw [f.preGNS_inner_def, f.ofPreGNS_toPreGNS, f.ofPreGNS_toPreGNS, star_one, one_mul, hf, e1,
    one_mul] at hcs
  exact hcs.trans ha

/-- A state is bounded by the norm, `|ω(a)| ≤ ‖a‖`. (QCALean notes: `lem:cv-norm`) -/
theorem State.norm_apply_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (ω : State σ) (a : CCR σ) : ‖ω.toCLM a‖ ≤ ‖a‖ :=
  norm_apply_le_of_nonneg_star_mul_self ω.toCLM ω.map_one ω.nonneg a

end Norm

end BosonicLean.Weyl
