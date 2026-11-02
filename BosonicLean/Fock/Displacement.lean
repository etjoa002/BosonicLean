/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.ExpVec

/-!
# Displacement operators on the bosonic Fock space

For `α ∈ ℂ^ι` the displacement operator `D(α)` acts on `ψ ∈ Γ_s(ι)` by its normal-ordered form
`D(α)ψ = e^{-|α|²/2} e^{α·a†} (e^{-ᾱ·a} ψ)`, computed in three steps: the lowering exponential
`e^{-ᾱ·a} ψ`, summed coefficient by coefficient (it converges absolutely, Lemma 5); the raising
exponential `e^{α·a†}`, a finite sum at each coefficient; and the factor `e^{-|α|²/2}`. On the
exponential vectors `D(α) ε(z) = e^{-|α|²/2 - ⟨α, z⟩} ε(z + α)`, so `D(α)` preserves their inner
products and, by the extension lemma, is an isometry of `Γ_s`; `D(α) D(-α) = 1` makes it unitary.
The operators satisfy the Weyl relation `D(α) D(β) = e^{(⟨β, α⟩ - ⟨α, β⟩)/2} D(α + β)`, intertwine
the ladder operators by translation, `D(α)* aⱼ D(α) = aⱼ + αⱼ`, and form strongly continuous
one-parameter groups along rays. A bounded operator commuting with every `D(α)` is a multiple of
the identity: the Fock representation is irreducible.

## Main definitions

* `BosonicLean.Fock.FormalFock.orderedDisplacement α`: the normal-ordered form, coefficientwise.
* `BosonicLean.Fock.FockSpace.displacement α`: the displacement operator `D(α)`, a unitary of
  `Γ_s(ι)`.
* `BosonicLean.Fock.FockSpace.fiberFock j n`: the fiber of a vector of `Γ_s(ι)` along mode `j`.

## Main results

* `FockSpace.displacement_expVec`, `star_displacement`, `displacement_zero`, `displacement_mul`
  (the Weyl relation), `displacement_vacuum`, `displacement_eq_prod`, `displacement_single_apply`:
  Theorem 8.
* `FockSpace.annihilate_displacement`, `create_displacement`,
  `displacement_mem_maxDomain_iff`: Theorem 9.
* `FockSpace.displacement_smul_mul`, `continuous_displacement_apply`,
  `hasDerivAt_displacement_smul`: Theorem 10.
* `FockSpace.eq_smul_one_of_commute_displacement`: Theorem 11, irreducibility.
* `FockSpace.exists_eq_smul_of_conj_eq`, `eq_of_conj_eq_of_inner_vacuum`,
  `eq_bot_or_eq_top_of_invariant`, `dense_span_displacement_vacuum`: Corollary 12.
* `FockSpace.displacement_matrixElement`: the number-basis matrix elements of one mode (Lemma 14).

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), (5), (A30), (A31), (A37).
* K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser (1992),
  §§19–20.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open Finset

namespace BosonicLean.Fock

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Definition 7.** The normal-ordered form `e^{-|α|²/2} e^{α·a†} e^{-ᾱ·a} ψ` of the displacement
operator, coefficientwise: the lowering exponential is the coefficientwise exponential and the
raising exponential is a finite sum at each coefficient. -/
noncomputable def orderedDisplacement (α : ι → ℂ) (ψ : FormalFock ι ℂ) : FormalFock ι ℂ :=
  ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ) • (raiseDisp α).exp (coeffExp (lowerDisp α) ψ)

omit [DecidableEq ι] in
/-- `-ᾱ·a ε(z) = -⟨α, z⟩ ε(z)`. -/
theorem lowerDisp_expVecFormal (α z : ι → ℂ) :
    lowerDisp α (expVecFormal z) = (-∑ j, conj (α j) * z j) • expVecFormal z := by
  simp only [lowerDisp, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    annihilate_expVecFormal, smul_smul, neg_smul, Finset.sum_smul]

omit [DecidableEq ι] in
/-- `e^{-ᾱ·a} ε(z) = e^{-⟨α, z⟩} ε(z)`, the series converging at every coefficient. -/
theorem coeffExp_lowerDisp_expVecFormal (α z : ι → ℂ) :
    coeffExp (lowerDisp α) (expVecFormal z) =
      Complex.exp (-∑ j, conj (α j) * z j) • expVecFormal z := by
  set c : ℂ := -∑ j, conj (α j) * z j
  have hpow : ∀ r : ℕ, (lowerDisp α ^ r) (expVecFormal z) = c ^ r • expVecFormal z := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, lowerDisp_expVecFormal, smul_smul,
        pow_succ', mul_comm]
  ext n
  rw [coeff_coeffExp, coeff_smul, smul_eq_mul, Complex.exp_eq_exp_ℂ,
    ← ((NormedSpace.expSeries_div_hasSum_exp c).mul_right ((expVecFormal z).coeff n)).tsum_eq]
  refine tsum_congr fun r => ?_
  rw [hpow, coeff_smul, smul_eq_mul, div_eq_inv_mul]
  ring

omit [DecidableEq ι] in
/-- **Theorem 8(a), coefficientwise.** The ordered form on an exponential vector:
`e^{-|α|²/2} e^{α·a†} e^{-ᾱ·a} ε(z) = e^{-|α|²/2 - ⟨α, z⟩} ε(z + α)`. -/
theorem orderedDisplacement_expVecFormal (α z : ι → ℂ) :
    orderedDisplacement α (expVecFormal z) =
      Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
        expVecFormal (z + α) := by
  classical
  rw [orderedDisplacement, coeffExp_lowerDisp_expVecFormal, map_smul,
    raiseDisp_exp_expVecFormal, smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The inner-product representation of the lowering exponential of `D(α)` (Lemma 5(a)). -/
private theorem exists_inner_coeffExp_lowerDisp (α : ι → ℂ) (n : ι →₀ ℕ) :
    ∃ χ : FockSpace ι, ∀ ψ : FockSpace ι,
      (coeffExp (lowerDisp α) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ := by
  classical
  obtain ⟨χ, -, hχ⟩ := coeff_coeffExp_lowerDisp α n
  exact ⟨χ, hχ⟩

/-- The ordered form of `D(α)` as a linear map from `Γ_s` to the formal Fock space. -/
noncomputable def orderedDisplacementLin (α : ι → ℂ) : FockSpace ι →ₗ[ℂ] FormalFock ι ℂ where
  toFun ψ := orderedDisplacement α (toFormal ψ)
  map_add' ψ φ := by
    change orderedDisplacement α (toFormal (ψ + φ)) =
      orderedDisplacement α (toFormal ψ) + orderedDisplacement α (toFormal φ)
    rw [orderedDisplacement, orderedDisplacement, orderedDisplacement,
      coeffExp_toFormal_add (exists_inner_coeffExp_lowerDisp α) ψ φ, map_add, smul_add]
  map_smul' c ψ := by
    change orderedDisplacement α (toFormal (c • ψ)) = c • orderedDisplacement α (toFormal ψ)
    rw [orderedDisplacement, orderedDisplacement,
      map_smul, coeffExp_smul, map_smul, smul_comm]

omit [DecidableEq ι] in
/-- The ordered form of `D(α)` as a linear map acts by `orderedDisplacement`. -/
theorem orderedDisplacementLin_apply (α : ι → ℂ) (ψ : FockSpace ι) :
    orderedDisplacementLin α ψ = orderedDisplacement α (toFormal ψ) := rfl

omit [DecidableEq ι] in
/-- The coefficients of the ordered form depend continuously on `ψ ∈ Γ_s` (Lemma 5(c)). -/
theorem continuous_coeff_orderedDisplacementLin (α : ι → ℂ) (n : ι →₀ ℕ) :
    Continuous fun ψ : FockSpace ι => (orderedDisplacementLin α ψ).coeff n := by
  classical
  simp only [orderedDisplacementLin_apply, orderedDisplacement, coeff_smul, smul_eq_mul]
  exact continuous_const.mul ((IsCoeffFinite.exp
    (raiseDisp α).raisesParticleNumber.isCoeffFinite).continuous_coeff_comp
      (continuous_coeff_coeffExp_lowerDisp α) n)

omit [DecidableEq ι] in
/-- The exponent `-|α|²/2 - ⟨α, z⟩` of Theorem 8(a) as a sum over the modes. -/
theorem exponent_displacement_eq_sum (α z : ι → ℂ) :
    -((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j =
      ∑ j, (-(conj (α j) * α j) / 2 - conj (α j) * z j) := by
  classical
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_neg_distrib]
  simp only [Complex.conj_mul']

omit [DecidableEq ι] in
/-- `D(α)` preserves the inner products of exponential vectors. -/
private theorem inner_dispVec (α w z : ι → ℂ) :
    ⟪Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * w j) • expVec (w + α),
      Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
        expVec (z + α)⟫_ℂ = ⟪expVec w, expVec z⟫_ℂ := by
  classical
  rw [inner_smul_left, inner_smul_right, inner_expVec, inner_expVec, ← Complex.exp_conj,
    ← Complex.exp_add, ← Complex.exp_add, exponent_displacement_eq_sum,
    exponent_displacement_eq_sum]
  congr 1
  simp only [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_sub, map_neg, map_div₀, map_mul, Complex.conj_conj, map_ofNat, Pi.add_apply,
    map_add]
  ring

omit [DecidableEq ι] in
/-- `D(α)` is an isometry of `Γ_s` acting by the ordered form. -/
private theorem exists_displacement_isometry (α : ι → ℂ) :
    ∃ L : FockSpace ι →ₗᵢ[ℂ] FockSpace ι, ∀ ψ, toFormal (L ψ) = orderedDisplacementLin α ψ :=
  exists_linearIsometry_of_expVec (orderedDisplacementLin α)
    (continuous_coeff_orderedDisplacementLin α)
    (fun z => Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
      expVec (z + α))
    (fun z => by
      rw [orderedDisplacementLin_apply, toFormal_expVec, orderedDisplacement_expVecFormal,
        map_smul, toFormal_expVec])
    (inner_dispVec α)

omit [DecidableEq ι] in
private theorem memℓp_orderedDisplacement (α : ι → ℂ) (ψ : FockSpace ι) :
    Memℓp (orderedDisplacement α (toFormal ψ)).coeff 2 := by
  classical
  obtain ⟨L, hL⟩ := exists_displacement_isometry α
  rw [← orderedDisplacementLin_apply, ← hL ψ]
  exact lp.memℓp (L ψ)

/-- `D(α)` as a map of `Γ_s`: the ordered form, which lies in `Γ_s`. -/
private noncomputable def dispFun (α : ι → ℂ) (ψ : FockSpace ι) : FockSpace ι :=
  ⟨(orderedDisplacement α (toFormal ψ)).coeff, memℓp_orderedDisplacement α ψ⟩

omit [DecidableEq ι] in
private theorem toFormal_dispFun (α : ι → ℂ) (ψ : FockSpace ι) :
    toFormal (dispFun α ψ) = orderedDisplacement α (toFormal ψ) := rfl

/-- `D(α)` as a linear isometry of `Γ_s`. -/
private noncomputable def dispIsometry (α : ι → ℂ) : FockSpace ι →ₗᵢ[ℂ] FockSpace ι :=
  have h : ∀ ψ, dispFun α ψ = (exists_displacement_isometry α).choose ψ := fun ψ =>
    toFormal_injective (by rw [toFormal_dispFun, (exists_displacement_isometry α).choose_spec]; rfl)
  { toFun := dispFun α
    map_add' := fun ψ φ => by simp only [h, map_add]
    map_smul' := fun c ψ => by simp only [h, map_smul, RingHom.id_apply]
    norm_map' := fun ψ => by
      change ‖dispFun α ψ‖ = ‖ψ‖
      rw [h, LinearIsometry.norm_map] }

omit [DecidableEq ι] in
private theorem toFormal_dispIsometry (α : ι → ℂ) (ψ : FockSpace ι) :
    toFormal (dispIsometry α ψ) = orderedDisplacement α (toFormal ψ) := rfl

omit [DecidableEq ι] in
private theorem dispIsometry_expVec (α z : ι → ℂ) :
    dispIsometry α (expVec z) =
      Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
        expVec (z + α) :=
  toFormal_injective (by
    rw [toFormal_dispIsometry, toFormal_expVec, orderedDisplacement_expVecFormal, map_smul,
      toFormal_expVec])

omit [DecidableEq ι] in
/-- `D(α) D(-α) = 1` on `Γ_s`. -/
private theorem dispIsometry_neg (α : ι → ℂ) (ψ : FockSpace ι) :
    dispIsometry α (dispIsometry (-α) ψ) = ψ := by
  classical
  have h := ext_expVec (f := (dispIsometry α).toContinuousLinearMap.comp
    (dispIsometry (-α)).toContinuousLinearMap) (g := ContinuousLinearMap.id ℂ _) fun z => by
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      ContinuousLinearMap.id_apply, dispIsometry_expVec, map_smul, smul_smul]
    rw [← Complex.exp_add, show z + -α + α = z by abel, exponent_displacement_eq_sum,
      exponent_displacement_eq_sum, ← sum_add_distrib]
    convert one_smul ℂ (expVec z) using 2
    convert Complex.exp_zero using 2
    refine sum_eq_zero fun j _ => ?_
    simp only [Pi.neg_apply, Pi.add_apply, map_neg]
    ring
  exact congrFun (congrArg DFunLike.coe h) ψ

/-- `D(α)` as a linear isometric equivalence of `Γ_s`, with inverse `D(-α)`. -/
private noncomputable def dispEquiv (α : ι → ℂ) : FockSpace ι ≃ₗᵢ[ℂ] FockSpace ι :=
  { dispIsometry α with
    invFun := dispIsometry (-α)
    left_inv := fun ψ => by
      have := dispIsometry_neg (-α) ψ
      rwa [neg_neg] at this
    right_inv := fun ψ => dispIsometry_neg α ψ }

/-- **Definition 7.** The **displacement operator** `D(α)`, the unitary of `Γ_s(ι)` that acts by
the normal-ordered form `e^{-|α|²/2} e^{α·a†} e^{-ᾱ·a}` (`toFormal_displacement`). -/
noncomputable def displacement (α : ι → ℂ) : unitary (FockSpace ι →L[ℂ] FockSpace ι) :=
  Unitary.linearIsometryEquiv.symm (dispEquiv α)

omit [DecidableEq ι] in
/-- **Definition 7.** `D(α)` acts by the ordered form. -/
theorem toFormal_displacement (α : ι → ℂ) (ψ : FockSpace ι) :
    toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ) =
      orderedDisplacement α (toFormal ψ) := rfl

omit [DecidableEq ι] in
/-- **Theorem 8(a).** `D(α) ε(z) = e^{-|α|²/2 - ⟨α, z⟩} ε(z + α)`. -/
theorem displacement_expVec (α z : ι → ℂ) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) (expVec z) =
      Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
        expVec (z + α) :=
  dispIsometry_expVec α z

omit [DecidableEq ι] in
/-- `D(α) D(-α) = 1`. -/
theorem displacement_mul_neg (α : ι → ℂ) : displacement α * displacement (-α) = 1 := by
  classical
  refine Subtype.ext (ContinuousLinearMap.ext fun ψ => ?_)
  exact dispIsometry_neg α ψ

end FockSpace

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Theorem 8 -/

omit [DecidableEq ι] in
/-- **Theorem 8(b).** `D(α)* = D(-α)`. -/
theorem star_displacement (α : ι → ℂ) : star (displacement α) = displacement (-α) := by
  classical
  rw [Unitary.star_eq_inv]
  exact inv_eq_of_mul_eq_one_right (displacement_mul_neg α)

omit [DecidableEq ι] in
/-- **Theorem 8(b).** `D(0) = 1`. -/
theorem displacement_zero : displacement (0 : ι → ℂ) = 1 := by
  classical
  refine Subtype.ext (ext_expVec fun z => ?_)
  rw [displacement_expVec]
  simp

omit [DecidableEq ι] in
/-- The exponent of the Weyl relation, mode by mode. -/
private theorem weyl_exponent (α β z : ι → ℂ) :
    (-((∑ j, ‖β j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (β j) * z j) +
        (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * (z + β) j) =
      (∑ j, (α j * conj (β j) - conj (α j) * β j)) / 2 +
        (-((∑ j, ‖(α + β) j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj ((α + β) j) * z j) := by
  classical
  rw [exponent_displacement_eq_sum, exponent_displacement_eq_sum, exponent_displacement_eq_sum,
    Finset.sum_div, ← sum_add_distrib, ← sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

omit [DecidableEq ι] in
/-- **Theorem 8(c), the Weyl relation.** `D(α) D(β) = e^{(⟨β, α⟩ - ⟨α, β⟩)/2} D(α + β)`, that is,
`e^{(Σⱼ αⱼ β̄ⱼ - ᾱⱼ βⱼ)/2} D(α + β)`. -/
theorem displacement_mul (α β : ι → ℂ) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) * displacement β =
      Complex.exp ((∑ j, (α j * conj (β j) - conj (α j) * β j)) / 2) •
        (displacement (α + β) : FockSpace ι →L[ℂ] FockSpace ι) := by
  classical
  refine ext_expVec fun z => ?_
  rw [mul_apply_eq_comp, displacement_expVec, map_smul, displacement_expVec,
    smul_smul, smul_apply, displacement_expVec, smul_smul,
    show z + β + α = z + (α + β) by abel, ← Complex.exp_add, ← Complex.exp_add, weyl_exponent]

/-- **Theorem 8(d).** `D(α)∣0⟩ = e^{-|α|²/2} ε(α)`, the coherent state of the paper's (5). -/
theorem displacement_vacuum (α : ι → ℂ) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) vacuum =
      ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ) • expVec α := by
  rw [← expVec_zero, displacement_expVec, zero_add]
  congr 1
  simp only [Pi.zero_apply, mul_zero, sum_const_zero, sub_zero, Complex.ofReal_exp]
  push_cast
  ring_nf

omit [DecidableEq ι] in
/-- Displacements with `Σⱼ (αⱼ β̄ⱼ - ᾱⱼ βⱼ) = 0` compose without a phase. -/
theorem displacement_mul_of_phase_eq_zero {α β : ι → ℂ}
    (h : ∑ j, (α j * conj (β j) - conj (α j) * β j) = 0) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) * displacement β = displacement (α + β) := by
  classical
  rw [displacement_mul, h, zero_div, Complex.exp_zero, one_smul]

/-- `D(Σ_{j ∈ l} αⱼ eⱼ) = Π_{j ∈ l} D(αⱼ eⱼ)` along a list of distinct modes. -/
private theorem displacement_list_sum (α : ι → ℂ) :
    ∀ l : List ι, l.Nodup →
      (displacement (l.map fun j => Pi.single j (α j)).sum : FockSpace ι →L[ℂ] FockSpace ι) =
        (l.map fun j => (displacement (Pi.single j (α j)) : FockSpace ι →L[ℂ] FockSpace ι)).prod
  | [], _ => by simp [displacement_zero]
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons,
      ← displacement_list_sum α l hl.2, displacement_mul_of_phase_eq_zero]
    refine sum_eq_zero fun k _ => ?_
    by_cases hka : k = a
    · obtain rfl := hka
      have hk : (l.map fun j => Pi.single j (α j)).sum k = 0 := by
        rw [Pi.list_sum_apply, List.map_map]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact Pi.single_eq_of_ne (fun h => hl.1 (by rw [h]; exact hj)) _
      rw [hk]
      simp
    · simp [Pi.single_eq_of_ne hka]

/-- **Theorem 8(d).** `D(α) = Πⱼ D(αⱼ eⱼ)`, the paper's (A30); the factors commute
(Theorem 8(c)). -/
theorem displacement_eq_prod (α : ι → ℂ) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) =
      (univ.toList.map fun j => (displacement (Pi.single j (α j)) :
        FockSpace ι →L[ℂ] FockSpace ι)).prod := by
  rw [← displacement_list_sum α _ (nodup_toList univ), Finset.sum_map_toList,
    Finset.univ_sum_single]

/-! #### The fiber along one mode -/

omit [Fintype ι] [DecidableEq ι] in
/-- The fiber of a square-summable family along mode `j` is square-summable. -/
private theorem memℓp_fiber (j : ι) (n : ι →₀ ℕ) (ψ : FockSpace ι) :
    Memℓp (fiber j (toFormal ψ) n).coeff 2 := by
  classical
  have hinj : Function.Injective fun m : Unit →₀ ℕ => n.update j (m ()) := fun a b h => by
    have := congrArg (fun f : ι →₀ ℕ => f j) h
    simp only [Finsupp.coe_update, Function.update_self] at this
    exact Finsupp.ext fun u => by cases u; exact this
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have := (summable_sq ψ).comp_injective hinj
  simp only [coeff_fiber, coeff_toFormal, ENNReal.toReal_ofNat, Real.rpow_two]
  exact this

/-- The fiber of `ψ ∈ Γ_s(ι)` along mode `j` at the occupations `n` of the other modes: the vector
`m ↦ ψ(n with nⱼ replaced by m)` of `Γ_s` of one mode. -/
noncomputable def fiberFock (j : ι) (n : ι →₀ ℕ) : FockSpace ι →L[ℂ] FockSpace Unit :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨(fiber j (toFormal ψ) n).coeff, memℓp_fiber j n ψ⟩
      map_add' := fun ψ φ => rfl
      map_smul' := fun c ψ => rfl }
    1 fun ψ => by
      rw [one_mul]
      change ‖(⟨(fiber j (toFormal ψ) n).coeff, memℓp_fiber j n ψ⟩ : FockSpace Unit)‖ ≤ ‖ψ‖
      have hinj : Function.Injective fun m : Unit →₀ ℕ => n.update j (m ()) := fun a b h => by
        have := congrArg (fun f : ι →₀ ℕ => f j) h
        simp only [Finsupp.coe_update, Function.update_self] at this
        exact Finsupp.ext fun u => by cases u; exact this
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
      exact (summable_sq _).tsum_le_tsum_of_inj _ hinj (fun _ _ => by positivity)
        (fun m => le_rfl) (summable_sq ψ)

omit [Fintype ι] in
/-- The fiber of `ψ ∈ Γ_s` has the coefficients of the formal fiber. -/
theorem toFormal_fiberFock (j : ι) (n : ι →₀ ℕ) (ψ : FockSpace ι) :
    toFormal (fiberFock j n ψ) = fiber j (toFormal ψ) n := rfl

/-- The fiber of an exponential vector along mode `j`. -/
theorem fiberFock_expVec (j : ι) (n : ι →₀ ℕ) (z : ι → ℂ) :
    fiberFock j n (expVec z) =
      (∏ k ∈ univ.erase j, (z k) ^ (n k) / sqrtC (n k).factorial) •
        expVec fun _ : Unit => z j := by
  refine toFormal_injective ?_
  rw [toFormal_fiberFock, toFormal_expVec, map_smul, toFormal_expVec, expVecFormal_eq_tensorVec,
    fiber_tensorVec]
  congr 1
  exact prod_congr rfl fun k _ => coeff_expVecFormal_unit _ _

/-- **Theorem 8(d).** `D(αⱼ eⱼ)` acts on mode `j` as the one-mode `D(αⱼ)`:
`(D(a eⱼ) ψ)(n) = (D(a) ψₙ)(nⱼ)`, with `ψₙ` the fiber of `ψ` along mode `j` at `n`. -/
theorem displacement_single_apply (j : ι) (a : ℂ) (ψ : FockSpace ι) (n : ι →₀ ℕ) :
    (displacement (Pi.single j a) : FockSpace ι →L[ℂ] FockSpace ι) ψ n =
      (displacement (fun _ : Unit => a) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (fiberFock j n ψ) (Finsupp.single () (n j)) := by
  have h := ext_expVec
    (f := (innerSL ℂ (lp.single 2 n (1 : ℂ))).comp
      (displacement (Pi.single j a) : FockSpace ι →L[ℂ] FockSpace ι))
    (g := (innerSL ℂ (lp.single 2 (Finsupp.single () (n j)) (1 : ℂ))).comp
      ((displacement (fun _ : Unit => a) : FockSpace Unit →L[ℂ] FockSpace Unit).comp
        (fiberFock j n))) fun z => by
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, lp.inner_single_left,
      RCLike.inner_apply', map_one, one_mul]
    rw [displacement_expVec, fiberFock_expVec, map_smul, displacement_expVec,
      lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply,
      expVec_apply, expVec_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      sqrtFactorial_eq_prod, sqrtFactorial, factorial_single]
    have hs : ∑ k, ‖(Pi.single j a : ι → ℂ) k‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
      simp
    have hz : ∑ k, conj ((Pi.single j a : ι → ℂ) k) * z k = conj a * z j := by
      rw [sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
      simp
    rw [hs, hz, ← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ _ (mem_univ j)]
    simp only [Pi.add_apply, Pi.single_eq_same, Finsupp.single_eq_same, univ_unique,
      sum_singleton, prod_singleton, PUnit.default_eq_unit]
    have hprod : ∏ k ∈ univ.erase j, (z k + (Pi.single j a : ι → ℂ) k) ^ n k =
        ∏ k ∈ univ.erase j, z k ^ n k :=
      prod_congr rfl fun k hk => by rw [Pi.single_eq_of_ne (ne_of_mem_erase hk), add_zero]
    rw [hprod, prod_div_distrib]
    have h1 := sqrtC_ne_zero (Nat.factorial_pos (n j))
    have h2 : ∏ k ∈ univ.erase j, sqrtC (n k).factorial ≠ 0 :=
      prod_ne_zero_iff.2 fun k _ => sqrtC_ne_zero (Nat.factorial_pos _)
    field_simp
  have := congrArg (fun f => f ψ) h
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, lp.inner_single_left,
    RCLike.inner_apply', map_one, one_mul] using this

end FockSpace

/-! ### Theorem 9: intertwining with the ladder operators -/

namespace FormalFock

variable {ι : Type*}

/-- If `X T = T X + S` with `S` commuting with `T`, then `X T^{k+1} = T^{k+1} X + (k+1) S T^k`. -/
private theorem mul_pow_succ_eq_of_mul_eq {A : Type*} [Ring A] [Algebra ℂ A] {X T S : A}
    (hS : X * T = T * X + S) (hST : Commute S T) (k : ℕ) :
    X * T ^ (k + 1) = T ^ (k + 1) * X + ((k + 1 : ℕ) : ℂ) • (S * T ^ k) := by
  induction k with
  | zero => simp [hS]
  | succ k ih =>
    calc X * T ^ (k + 1 + 1) = (X * T ^ (k + 1)) * T := by rw [pow_succ _ (k + 1), mul_assoc]
      _ = T ^ (k + 1) * (X * T) + ((k + 1 : ℕ) : ℂ) • (S * T ^ (k + 1)) := by
          rw [ih, add_mul, mul_assoc, smul_mul_assoc, mul_assoc, ← pow_succ]
      _ = T ^ (k + 1 + 1) * X + S * T ^ (k + 1) + ((k + 1 : ℕ) : ℂ) • (S * T ^ (k + 1)) := by
          rw [hS, mul_add, ← mul_assoc, ← pow_succ, (hST.pow_right (k + 1)).eq]
      _ = T ^ (k + 1 + 1) * X + ((k + 1 + 1 : ℕ) : ℂ) • (S * T ^ (k + 1)) := by
          push_cast
          module

/-- **The Leibniz rule for raising exponentials.** If `aⱼ T = T aⱼ + S` with `S` commuting with
`T`, then `aⱼ e^T ψ = e^T aⱼ ψ + e^T S ψ`. -/
theorem annihilate_exp_eq (T : NumberRaisingOp ι ℂ) (j : ι) {S : Module.End ℂ (FormalFock ι ℂ)}
    (hS : annihilate j * T.op = T.op * annihilate j + S) (hST : Commute S T.op)
    (ψ : FormalFock ι ℂ) :
    annihilate j (T.exp ψ) = T.exp (annihilate j ψ) + T.exp (S ψ) := by
  ext n
  have hM : n.degree ≤ n.degree + 1 := Nat.le_succ _
  have hM' : (n + Finsupp.single j 1).degree ≤ n.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hterm : ∀ k ∈ range (n.degree + 1 + 1), sqrtC (n j + 1) •
      ((k.factorial : ℂ)⁻¹ • ((T.op ^ k) ψ).coeff (n + Finsupp.single j 1)) =
      (k.factorial : ℂ)⁻¹ • ((T.op ^ k) (annihilate j ψ)).coeff n +
        (if k = 0 then 0 else ((k - 1).factorial : ℂ)⁻¹ •
          ((T.op ^ (k - 1)) (S ψ)).coeff n) := by
    intro k _
    rw [smul_comm, ← coeff_annihilate, ← Module.End.mul_apply]
    rcases k with _ | k
    · simp
    · rw [mul_pow_succ_eq_of_mul_eq hS hST k, LinearMap.add_apply, coeff_add, smul_add,
        LinearMap.smul_apply, coeff_smul, smul_smul, Module.End.mul_apply,
        (hST.pow_right k).eq, Module.End.mul_apply]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      congr 1
      rw [Nat.factorial_succ]
      have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
      push_cast
      field_simp
  rw [coeff_annihilate, NumberRaisingOp.coeff_exp_eq_sum T _ hM', smul_sum, sum_congr rfl hterm,
    sum_add_distrib, coeff_add, NumberRaisingOp.coeff_exp_eq_sum T _ hM,
    NumberRaisingOp.coeff_exp]
  congr 1
  rw [sum_range_succ', ite_eq_left rfl, add_zero]
  refine sum_congr rfl fun k _ => ?_
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

/-- The creation operator commutes with the exponential of an operator that raises the particle
number and commutes with it. -/
theorem commute_create_exp_of_commute (j : ι) (T : NumberRaisingOp ι ℂ)
    (h : Commute (create j : Module.End ℂ (FormalFock ι ℂ)) T.op) :
    Commute (create j : Module.End ℂ (FormalFock ι ℂ)) T.exp := by
  classical
  ext ψ n
  have hR : (T.exp (create j ψ)).coeff n = ∑ k ∈ range (n.degree + 1),
      (k.factorial : ℂ)⁻¹ • (create j ((T.op ^ k) ψ)).coeff n := by
    rw [NumberRaisingOp.coeff_exp]
    refine sum_congr rfl fun k _ => ?_
    rw [← Module.End.mul_apply (T.op ^ k), ← (h.pow_right k).eq, Module.End.mul_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply, hR, coeff_create]
  split_ifs with hn
  · have hd : (n - Finsupp.single j 1).degree ≤ n.degree := by
      have := degree_sub_single_add_one hn
      omega
    rw [NumberRaisingOp.coeff_exp_eq_sum T ψ hd, smul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [coeff_create, ite_eq_left hn, smul_comm]
  · symm
    refine sum_eq_zero fun k _ => ?_
    rw [coeff_create, ite_eq_right hn, smul_zero]

/-- `aⱼ` commutes with the coefficientwise exponential of an operator commuting with `aⱼ`. -/
theorem annihilate_coeffExp_of_commute (j : ι) {Λ : Module.End ℂ (FormalFock ι ℂ)}
    (h : Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) Λ) (ψ : FormalFock ι ℂ) :
    annihilate j (coeffExp Λ ψ) = coeffExp Λ (annihilate j ψ) := by
  classical
  ext n
  rw [coeff_annihilate, coeff_coeffExp, coeff_coeffExp, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  rw [← Module.End.mul_apply (Λ ^ r), ← (h.pow_right r).eq, Module.End.mul_apply,
    coeff_annihilate, smul_eq_mul]
  ring

/-- **The commutator rule for lowering exponentials.** If `Λ aⱼ† = aⱼ† Λ + C` with `C` commuting
with `Λ`, then `(e^Λ aⱼ† ψ)(n) = (aⱼ† e^Λ ψ)(n) + (e^Λ C ψ)(n)`, provided the two series on the
right converge. -/
theorem coeff_coeffExp_create {Λ C : Module.End ℂ (FormalFock ι ℂ)} (j : ι)
    (hΛ : Λ * create j = create j * Λ + C) (hC : Commute C Λ) {ψ : FormalFock ι ℂ}
    (n : ι →₀ ℕ)
    (h1 : Summable fun r : ℕ =>
      ((r.factorial : ℂ)⁻¹) * ((Λ ^ r) ψ).coeff (n - Finsupp.single j 1))
    (h2 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) * ((Λ ^ r) (C ψ)).coeff n) :
    (coeffExp Λ (create j ψ)).coeff n =
      (create j (coeffExp Λ ψ)).coeff n + (coeffExp Λ (C ψ)).coeff n := by
  classical
  set f : ℕ → ℂ := fun r => ((r.factorial : ℂ)⁻¹) * ((Λ ^ r) (C ψ)).coeff n
  have hterm : ∀ r : ℕ, ((r.factorial : ℂ)⁻¹) * ((Λ ^ r) (create j ψ)).coeff n =
      ((r.factorial : ℂ)⁻¹) * (create j ((Λ ^ r) ψ)).coeff n +
        (if r = 0 then 0 else f (r - 1)) := by
    intro r
    rcases r with _ | r
    · simp
    · have hp : Λ ^ (r + 1) * create j =
          create j * Λ ^ (r + 1) + ((r + 1 : ℕ) : ℂ) • (C * Λ ^ r) := by
        rw [mul_pow_succ_eq_of_mul_eq (X := create j) (T := Λ) (S := -C)
          (by rw [hΛ]; abel) hC.neg_left r, neg_mul, smul_neg]
        abel
      rw [(hC.pow_right r).eq] at hp
      rw [← Module.End.mul_apply (Λ ^ (r + 1)) (create j), hp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply, coeff_add, coeff_smul,
        mul_add, smul_eq_mul]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, f]
      congr 1
      rw [Nat.factorial_succ]
      have hk : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
      push_cast
      field_simp
  have hs1 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) * (create j ((Λ ^ r) ψ)).coeff n := by
    by_cases hn : 0 < n j
    · refine (h1.mul_left (sqrtC (n j))).congr fun r => ?_
      rw [coeff_create, ite_eq_left hn, smul_eq_mul]
      ring
    · simp only [coeff_create, ite_eq_right hn, mul_zero]
      exact summable_zero
  have hs2 : Summable fun r : ℕ => (if r = 0 then 0 else f (r - 1)) := by
    rw [← summable_nat_add_iff 1]
    simpa using h2
  rw [coeff_coeffExp, tsum_congr hterm, hs1.tsum_add hs2]
  congr 1
  · rw [coeff_create]
    split_ifs with hn
    · rw [coeff_coeffExp, smul_eq_mul, ← tsum_mul_left]
      refine tsum_congr fun r => ?_
      rw [coeff_create, ite_eq_left hn, smul_eq_mul]
      ring
    · simp only [coeff_create, ite_eq_right hn, mul_zero, tsum_zero]
  · rw [hs2.tsum_eq_zero_add, coeff_coeffExp]
    simp [f]

end FormalFock

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `aⱼ (α·a†) = (α·a†) aⱼ + αⱼ`. -/
theorem annihilate_mul_raiseDisp (α : ι → ℂ) (j : ι) :
    annihilate j * (raiseDisp α).op = (raiseDisp α).op * annihilate j + α j • 1 := by
  classical
  have hac : ∀ j k : ι, (annihilate j : Module.End ℂ (FormalFock ι ℂ)) * create k =
      create k * annihilate j + if j = k then 1 else 0 := fun j k => by
    rw [← sub_eq_iff_eq_add', ← Ring.lie_def, lie_annihilate_create (R := ℂ)]
  rw [raiseDisp_op, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, hac, smul_add, smul_mul_assoc]
  rw [sum_add_distrib]
  congr 1
  simp

omit [DecidableEq ι] in
/-- `aⱼ†` commutes with `α·a†`. -/
theorem commute_create_raiseDisp (α : ι → ℂ) (j : ι) :
    Commute (create j : Module.End ℂ (FormalFock ι ℂ)) (raiseDisp α).op := by
  classical
  rw [raiseDisp_op]
  exact Commute.sum_right _ _ _ fun k _ =>
    (commute_iff_lie_eq.2 (lie_create_create (R := ℂ) j k)).smul_right _

omit [DecidableEq ι] in
/-- `aⱼ` commutes with `-ᾱ·a`. -/
theorem commute_annihilate_lowerDisp (α : ι → ℂ) (j : ι) :
    Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) (lowerDisp α) := by
  classical
  rw [lowerDisp]
  exact (Commute.sum_right _ _ _ fun k _ =>
    (commute_annihilate_annihilate j k).smul_right _).neg_right

omit [DecidableEq ι] in
/-- `(-ᾱ·a) aⱼ† = aⱼ† (-ᾱ·a) - ᾱⱼ`. -/
theorem lowerDisp_mul_create (α : ι → ℂ) (j : ι) :
    lowerDisp α * create j = create j * lowerDisp α + (-conj (α j)) • 1 := by
  classical
  have hac : ∀ j k : ι, (annihilate j : Module.End ℂ (FormalFock ι ℂ)) * create k =
      create k * annihilate j + if j = k then 1 else 0 := fun j k => by
    rw [← sub_eq_iff_eq_add', ← Ring.lie_def, lie_annihilate_create (R := ℂ)]
  rw [lowerDisp, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, hac, smul_add, mul_smul_comm]
  rw [sum_add_distrib, neg_add, neg_smul]
  congr 2
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Theorem 9.** If `aⱼ ψ = φ` with `ψ, φ ∈ Γ_s`, then `aⱼ D(α) ψ = D(α) φ + αⱼ D(α) ψ`: on the
domain of the maximal realization of `aⱼ`, `D(α)* aⱼ D(α) = aⱼ + αⱼ`, the paper's
`D† a D = a + α`. -/
theorem annihilate_displacement (α : ι → ℂ) (j : ι) {ψ φ : FockSpace ι}
    (h : annihilate j (toFormal ψ) = toFormal φ) :
    annihilate j (toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
      toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) φ) +
        α j • toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ) := by
  classical
  simp only [toFormal_displacement]
  rw [orderedDisplacement, orderedDisplacement, map_smul,
    annihilate_exp_eq _ j (annihilate_mul_raiseDisp α j) ((Commute.one_left _).smul_left _),
    annihilate_coeffExp_of_commute j (commute_annihilate_lowerDisp α j), h]
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_add]
  rw [smul_comm]

omit [DecidableEq ι] in
/-- **Theorem 9.** If `aⱼ† ψ = φ` with `ψ, φ ∈ Γ_s`, then `aⱼ† D(α) ψ = D(α) φ + ᾱⱼ D(α) ψ`: on the
domain of the maximal realization, `D(α)* aⱼ† D(α) = aⱼ† + ᾱⱼ`, the paper's (A31). -/
theorem create_displacement (α : ι → ℂ) (j : ι) {ψ φ : FockSpace ι}
    (h : create j (toFormal ψ) = toFormal φ) :
    create j (toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
      toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) φ) +
        conj (α j) • toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ) := by
  classical
  -- `aⱼ† e^{-ᾱ·a} ψ = e^{-ᾱ·a} φ + ᾱⱼ e^{-ᾱ·a} ψ`
  have hL : create j (coeffExp (lowerDisp α) (toFormal ψ)) =
      coeffExp (lowerDisp α) (toFormal φ) + conj (α j) • coeffExp (lowerDisp α) (toFormal ψ) := by
    ext n
    have h1 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        ((lowerDisp α ^ r) (toFormal ψ)).coeff (n - Finsupp.single j 1) :=
      (summable_coeffExp_lowerDisp α ψ _).of_norm
    have h2 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        ((lowerDisp α ^ r) (((-conj (α j)) • 1 : Module.End ℂ (FormalFock ι ℂ))
          (toFormal ψ))).coeff n := by
      simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, coeff_smul, smul_eq_mul]
      exact ((summable_coeffExp_lowerDisp α ψ n).of_norm.mul_left (-conj (α j))).congr
        fun r => by ring
    have := coeff_coeffExp_create j (lowerDisp_mul_create α j)
      ((Commute.one_left _).smul_left _) n h1 h2
    rw [h] at this
    rw [coeff_add, coeff_smul, smul_eq_mul, this]
    simp only [LinearMap.smul_apply, Module.End.one_apply, coeff_coeffExp, map_smul, coeff_smul,
      smul_eq_mul]
    rw [show (∑' r : ℕ, ((r.factorial : ℂ)⁻¹) * (-conj (α j) *
      ((lowerDisp α ^ r) (toFormal ψ)).coeff n)) = -conj (α j) * ∑' r : ℕ,
        ((r.factorial : ℂ)⁻¹) * ((lowerDisp α ^ r) (toFormal ψ)).coeff n by
      rw [← tsum_mul_left]; exact tsum_congr fun r => by ring]
    ring
  simp only [toFormal_displacement]
  rw [orderedDisplacement, orderedDisplacement, map_smul, ← Module.End.mul_apply (create j),
    (commute_create_exp_of_commute j _ (commute_create_raiseDisp α j)).eq, Module.End.mul_apply,
    hL, map_add, map_smul, smul_add, smul_comm]

omit [DecidableEq ι] in
/-- **Theorem 9.** `D(α)` maps the domain of the maximal realization of `aⱼ` onto itself. -/
theorem displacement_mem_maxDomain_iff (α : ι → ℂ) (j : ι) (ψ : FockSpace ι) :
    (displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ ∈ maxDomain (annihilate j) ↔
      ψ ∈ maxDomain (annihilate j) := by
  classical
  have key : ∀ (β : ι → ℂ) (χ : FockSpace ι), χ ∈ maxDomain (annihilate j) →
      (displacement β : FockSpace ι →L[ℂ] FockSpace ι) χ ∈ maxDomain (annihilate j) := by
    intro β χ hχ
    obtain ⟨φ, hφ⟩ : ∃ φ : FockSpace ι, annihilate j (toFormal χ) = toFormal φ :=
      ⟨⟨(annihilate j (toFormal χ)).coeff, hχ⟩, rfl⟩
    change Memℓp (annihilate j (toFormal
      ((displacement β : FockSpace ι →L[ℂ] FockSpace ι) χ))).coeff 2
    rw [annihilate_displacement β j hφ, ← map_smul, ← map_add,
      show ∀ x : FockSpace ι, (toFormal x).coeff = ⇑x from fun _ => rfl]
    exact lp.memℓp _
  refine ⟨fun h => ?_, key α ψ⟩
  have h2 := key (-α) _ h
  have hinv : (displacement (-α) : FockSpace ι →L[ℂ] FockSpace ι)
      ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ) = ψ := by
    have h1 := displacement_mul_neg (-α)
    rw [neg_neg] at h1
    exact congrArg (fun u : unitary (FockSpace ι →L[ℂ] FockSpace ι) =>
      (u : FockSpace ι →L[ℂ] FockSpace ι) ψ) h1
  rwa [hinv] at h2

end FockSpace

/-! ### Theorem 10: one-parameter groups of displacements -/

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Theorem 10(a).** Along a ray the displacements form a one-parameter group:
`D(tα) D(t'α) = D((t + t')α)` for real `t, t'`. -/
theorem displacement_smul_mul (α : ι → ℂ) (t s : ℝ) :
    (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι) * displacement ((s : ℂ) • α) =
      displacement (((t + s : ℝ) : ℂ) • α) := by
  classical
  rw [displacement_mul_of_phase_eq_zero, Complex.ofReal_add, add_smul]
  refine sum_eq_zero fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  ring

omit [DecidableEq ι] in
/-- **Theorem 10(b).** Strong continuity: `α ↦ D(α) ψ` is continuous for every `ψ ∈ Γ_s`. -/
theorem continuous_displacement_apply (ψ : FockSpace ι) :
    Continuous fun α : ι → ℂ => (displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ := by
  classical
  set E := Submodule.span ℂ (Set.range (expVec (ι := ι)))
  have hE : ∀ χ ∈ E, Continuous fun α : ι → ℂ =>
      (displacement α : FockSpace ι →L[ℂ] FockSpace ι) χ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp only [displacement_expVec]
      have h1 : Continuous fun α : ι → ℂ =>
          Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) := by
        fun_prop
      exact h1.smul ((continuous_expVec (ι := ι)).comp (continuous_const.add continuous_id))
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul]; exact hx.const_smul c
  have hequi : Equicontinuous fun α : ι → ℂ =>
      ⇑(displacement α : FockSpace ι →L[ℂ] FockSpace ι) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun α =>
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, Unitary.norm_map, NNReal.coe_one,
          one_mul]).equicontinuous
  refine continuous_iff_continuousAt.2 fun α₀ => ?_
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := nhds α₀)
    (displacement α₀ : FockSpace ι →L[ℂ] FockSpace ι).continuous
  have hsub : closure (E : Set (FockSpace ι)) ⊆ _ :=
    hclosed.closure_subset_iff.2 fun χ hχ => (hE χ hχ).continuousAt
  exact hsub ((dense_span_expVec (ι := ι)).closure_eq ▸ Set.mem_univ ψ)

/-! ### Theorem 11 and Corollary 12: irreducibility -/

omit [DecidableEq ι] in
/-- `D(α)* = D(-α)` as bounded operators. -/
private theorem adjoint_displacement (α : ι → ℂ) :
    ContinuousLinearMap.adjoint (displacement α : FockSpace ι →L[ℂ] FockSpace ι) =
      displacement (-α) := by
  classical
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star, star_displacement]

/-- **Theorem 11, claim (i).** If `T` commutes with every `D(α)`, then
`⟨ε(α), T∣0⟩⟩ = ⟨T*∣0⟩, ε(-α)⟩`. -/
theorem inner_expVec_apply_vacuum {T : FockSpace ι →L[ℂ] FockSpace ι}
    (hT : ∀ α : ι → ℂ, Commute T (displacement α : FockSpace ι →L[ℂ] FockSpace ι)) (α : ι → ℂ) :
    ⟪expVec α, T vacuum⟫_ℂ = ⟪(ContinuousLinearMap.adjoint T) vacuum, expVec (-α)⟫_ℂ := by
  set c : ℂ := ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have hc' : conj c = c := Complex.conj_ofReal _
  have h1 : ⟪(displacement α : FockSpace ι →L[ℂ] FockSpace ι) vacuum, T vacuum⟫_ℂ =
      c * ⟪expVec α, T vacuum⟫_ℂ := by
    rw [displacement_vacuum, inner_smul_left, hc']
  have h2 : ⟪(displacement α : FockSpace ι →L[ℂ] FockSpace ι) vacuum, T vacuum⟫_ℂ =
      c * ⟪(ContinuousLinearMap.adjoint T) vacuum, expVec (-α)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_displacement, ← mul_apply_eq_comp,
      ← (hT (-α)).eq, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left,
      displacement_vacuum, inner_smul_right]
    simp only [Pi.neg_apply, norm_neg, c]
  exact mul_left_cancel₀ hc (h1.symm.trans h2)

/-- **Theorem 11, claim (ii).** A bounded operator commuting with every `D(α)` maps the vacuum to a
multiple of itself. -/
theorem apply_vacuum_of_commute {T : FockSpace ι →L[ℂ] FockSpace ι}
    (hT : ∀ α : ι → ℂ, Commute T (displacement α : FockSpace ι →L[ℂ] FockSpace ι)) :
    T vacuum = ⟪vacuum, T vacuum⟫_ℂ • vacuum := by
  set P := (secondQuantRep (-1 : Matrix.unitaryGroup ι ℂ) : FockSpace ι →L[ℂ] FockSpace ι)
  have hP : ContinuousLinearMap.adjoint P = P := by
    have h1 : star (-1 : Matrix.unitaryGroup ι ℂ) = -1 := Subtype.ext (by
      simp only [Unitary.coe_star, Unitary.coe_neg, OneMemClass.coe_one, star_neg, star_one])
    rw [← ContinuousLinearMap.star_eq_adjoint, star_secondQuantRep, h1]
  have h : ∀ z, ⟪expVec z, T vacuum⟫_ℂ = ⟪P ((ContinuousLinearMap.adjoint T) vacuum), expVec z⟫_ℂ :=
    fun z => by
      rw [← ContinuousLinearMap.adjoint_inner_right, hP, secondQuantRep_expVec, Unitary.coe_neg,
        Matrix.UnitaryGroup.one_val, Matrix.neg_mulVec, Matrix.one_mulVec,
        inner_expVec_apply_vacuum hT]
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    unfold vacuum
    rw [lp.single_apply_self, mul_one, lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  · rw [(coeff_eq_zero_of_inner_expVec_eq h hn).1, lp.coeFn_smul, Pi.smul_apply, vacuum,
      lp.single_apply_ne _ _ _ hn, smul_zero]

end FockSpace

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- `‖∣0⟩‖ = 1`. -/
theorem norm_vacuum : ‖(vacuum : FockSpace ι)‖ = 1 := by
  classical
  rw [vacuum, lp.norm_single (by norm_num), norm_one]

/-- `ε(α) = e^{|α|²/2} D(α)∣0⟩`. -/
private theorem expVec_eq_smul_displacement_vacuum (α : ι → ℂ) :
    expVec α = ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ)⁻¹ •
      (displacement α : FockSpace ι →L[ℂ] FockSpace ι) vacuum := by
  rw [displacement_vacuum, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2
    (Real.exp_pos _).ne'), one_smul]

/-- **Theorem 11 (irreducibility of the Fock representation).** A bounded operator on `Γ_s(ι)`
that commutes with every `D(α)` is the multiple `⟨0∣T∣0⟩ 1` of the identity. -/
theorem eq_smul_one_of_commute_displacement (T : FockSpace ι →L[ℂ] FockSpace ι)
    (hT : ∀ α : ι → ℂ, Commute T (displacement α : FockSpace ι →L[ℂ] FockSpace ι)) :
    T = ⟪vacuum, T vacuum⟫_ℂ • 1 := by
  set c : ℂ := ⟪vacuum, T vacuum⟫_ℂ
  have hv : T vacuum = c • vacuum := apply_vacuum_of_commute hT
  refine ext_expVec fun α => ?_
  rw [expVec_eq_smul_displacement_vacuum, map_smul, ← mul_apply_eq_comp,
    (hT α).eq, mul_apply_eq_comp, hv, map_smul, smul_apply, one_apply_eq_self,
    smul_comm]

omit [DecidableEq ι] in
/-- **Corollary 12(a).** Two unitaries with the same conjugation action on all `D(α)` agree up to a
phase. -/
theorem exists_eq_smul_of_conj_eq (V V' : unitary (FockSpace ι →L[ℂ] FockSpace ι))
    (h : ∀ α : ι → ℂ, (star V : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V =
      (star V' : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V') :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (V : FockSpace ι →L[ℂ] FockSpace ι) = c • (V' : FockSpace ι →L[ℂ] FockSpace ι) := by
  classical
  have hV : (V : FockSpace ι →L[ℂ] FockSpace ι) * star (V : FockSpace ι →L[ℂ] FockSpace ι) = 1 :=
    Unitary.mul_star_self_of_mem V.2
  have hV' : (V' : FockSpace ι →L[ℂ] FockSpace ι) *
      star (V' : FockSpace ι →L[ℂ] FockSpace ι) = 1 := Unitary.mul_star_self_of_mem V'.2
  have hV'' : star (V' : FockSpace ι →L[ℂ] FockSpace ι) *
      (V' : FockSpace ι →L[ℂ] FockSpace ι) = 1 := Unitary.star_mul_self_of_mem V'.2
  set W : FockSpace ι →L[ℂ] FockSpace ι :=
    (V : FockSpace ι →L[ℂ] FockSpace ι) * star (V' : FockSpace ι →L[ℂ] FockSpace ι)
  have hW : ∀ α : ι → ℂ, Commute W (displacement α : FockSpace ι →L[ℂ] FockSpace ι) := by
    intro α
    change W * displacement α = displacement α * W
    calc W * displacement α
        = V * (star (V' : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V') *
            star (V' : FockSpace ι →L[ℂ] FockSpace ι) := by
          simp only [W, mul_assoc, hV', mul_one]
      _ = V * (star (V : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V) *
            star (V' : FockSpace ι →L[ℂ] FockSpace ι) := by rw [h α]
      _ = displacement α * W := by
          simp only [W, ← mul_assoc, hV, one_mul]
  have hc := eq_smul_one_of_commute_displacement W hW
  set c : ℂ := ⟪vacuum, W vacuum⟫_ℂ
  refine ⟨c, ?_, ?_⟩
  · have hWu : W ∈ unitary (FockSpace ι →L[ℂ] FockSpace ι) :=
      Submonoid.mul_mem _ V.2 (Unitary.star_mem V'.2)
    have h1 : ‖W vacuum‖ = ‖(vacuum : FockSpace ι)‖ := Unitary.norm_map ⟨W, hWu⟩ vacuum
    rw [hc, smul_apply, one_apply_eq_self, norm_smul,
      norm_vacuum, mul_one] at h1
    exact h1
  · calc (V : FockSpace ι →L[ℂ] FockSpace ι) = W * V' := by
          simp only [W, mul_assoc, hV'', mul_one]
      _ = c • (V' : FockSpace ι →L[ℂ] FockSpace ι) := by
          rw [hc]
          exact ContinuousLinearMap.ext fun x => rfl

/-- **Corollary 12(a).** The phase is `1` if the vacuum expectation values agree and are
nonzero. -/
theorem eq_of_conj_eq_of_inner_vacuum (V V' : unitary (FockSpace ι →L[ℂ] FockSpace ι))
    (h : ∀ α : ι → ℂ, (star V : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V =
      (star V' : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * V')
    (hv : ⟪vacuum, (V : FockSpace ι →L[ℂ] FockSpace ι) vacuum⟫_ℂ =
      ⟪vacuum, (V' : FockSpace ι →L[ℂ] FockSpace ι) vacuum⟫_ℂ)
    (h0 : ⟪vacuum, (V' : FockSpace ι →L[ℂ] FockSpace ι) vacuum⟫_ℂ ≠ 0) : V = V' := by
  obtain ⟨c, -, hc⟩ := exists_eq_smul_of_conj_eq V V' h
  have hc1 : c = 1 := by
    rw [hc, smul_apply, inner_smul_right] at hv
    exact mul_right_cancel₀ h0 (hv.trans (one_mul _).symm)
  rw [hc1, one_smul] at hc
  exact Subtype.ext hc

omit [DecidableEq ι] in
/-- **Corollary 12(b).** A closed subspace invariant under every `D(α)` is `0` or `Γ_s`. -/
theorem eq_bot_or_eq_top_of_invariant (K : Submodule ℂ (FockSpace ι))
    (hK : IsClosed (K : Set (FockSpace ι)))
    (h : ∀ α : ι → ℂ, ∀ x ∈ K, (displacement α : FockSpace ι →L[ℂ] FockSpace ι) x ∈ K) :
    K = ⊥ ∨ K = ⊤ := by
  classical
  have : CompleteSpace K := hK.completeSpace_coe
  -- the orthogonal projection onto `K` commutes with every `D(α)`
  have hP : ∀ α : ι → ℂ,
      Commute K.starProjection (displacement α : FockSpace ι →L[ℂ] FockSpace ι) := by
    intro α
    refine ContinuousLinearMap.ext fun x => ?_
    change K.starProjection ((displacement α : FockSpace ι →L[ℂ] FockSpace ι) x) =
      (displacement α : FockSpace ι →L[ℂ] FockSpace ι) (K.starProjection x)
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (h α _ (K.starProjection_apply_mem x)) fun w hw => ?_
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, adjoint_displacement]
    exact (Submodule.mem_orthogonal' _ _).1 (K.sub_starProjection_mem_orthogonal x) _
      (h (-α) w hw)
  have hc := eq_smul_one_of_commute_displacement _ hP
  set c : ℂ := ⟪vacuum, K.starProjection vacuum⟫_ℂ
  -- the projection is idempotent, so `c = 0` or `c = 1`
  have hidem : c * c = c := by
    have h2 := K.isIdempotentElem_starProjection.eq
    rw [hc] at h2
    have h3 : (c * c) • (vacuum : FockSpace ι) = c • vacuum := by
      have := congrArg (fun X : FockSpace ι →L[ℂ] FockSpace ι => X vacuum) h2
      simpa [smul_smul] using this
    have hvac : (vacuum : FockSpace ι) ≠ 0 := fun h0 => by
      have := norm_vacuum (ι := ι)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    exact smul_left_injective ℂ hvac h3
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by linear_combination hidem
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rcases hc01 with h0 | h1
  · left
    refine (Submodule.eq_bot_iff K).2 fun x hx => ?_
    rw [← K.starProjection_eq_self_iff.2 hx, hc, h0]
    simp
  · right
    refine eq_top_iff.2 fun x _ => ?_
    have := K.starProjection_apply_mem x
    rwa [hc, h1, one_smul, one_apply_eq_self] at this

/-- **Corollary 12(c).** The vacuum is cyclic: the vectors `D(α)∣0⟩` span a dense subspace. -/
theorem dense_span_displacement_vacuum :
    Dense (Submodule.span ℂ (Set.range fun α : ι → ℂ =>
      (displacement α : FockSpace ι →L[ℂ] FockSpace ι) vacuum) : Set (FockSpace ι)) := by
  refine (dense_span_expVec (ι := ι)).mono (Submodule.span_le.2 ?_)
  rintro _ ⟨α, rfl⟩
  rw [expVec_eq_smul_displacement_vacuum]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

end FockSpace

/-! ### Lemma 14: the number-basis matrix elements of one mode -/

namespace FormalFock

/-- A product vector over the single mode `Unit` is its factor. -/
theorem tensorVec_unit (φ : Unit → FormalFock Unit ℂ) : tensorVec φ = φ () := by
  ext n
  rw [coeff_tensorVec, Fintype.prod_unique, PUnit.default_eq_unit, ← Finsupp.unique_single n]

/-- One mode: `e^{ℓ a†} ∣k⟩` is the one-mode Gaussian operator applied to `∣k⟩`. -/
theorem raiseDisp_exp_numberState (ℓ : ℂ) (k : ℕ) :
    (raiseDisp fun _ : Unit => ℓ).exp (numberState k) = gaussExp 0 ℓ (numberState k) := by
  rw [numberState, raiseDisp_exp_single, tensorVec_unit]
  simp [numberState]

/-- One mode: the coefficients of `(-ᾱ a)^r ∣n⟩`. -/
theorem coeff_lowerDisp_pow_numberState (α : ℂ) (r n l : ℕ) :
    (((lowerDisp fun _ : Unit => α) ^ r) (numberState n)).coeff (Finsupp.single () l) =
      if r ≤ n ∧ l = n - r then (-conj α) ^ r * (sqrtC n.factorial / sqrtC (n - r).factorial)
      else 0 := by
  have hΛ : (lowerDisp fun _ : Unit => α) = (-conj α) • annihilate () := by
    simp [lowerDisp, neg_smul]
  rw [hΛ, smul_pow, LinearMap.smul_apply, annihilate_pow_numberState]
  by_cases h1 : r ≤ n
  · by_cases h2 : l = n - r
    · simp [h1, h2, coeff_numberState]
    · simp [h1, h2, coeff_numberState]
  · simp [h1]

/-- One mode: `e^{-ᾱ a} ∣n⟩ = Σ_{k ≤ n} (-ᾱ)^{n-k}/(n-k)! √(n!/k!) ∣k⟩`, a finite sum. -/
theorem coeffExp_lowerDisp_numberState (α : ℂ) (n : ℕ) :
    coeffExp (lowerDisp fun _ : Unit => α) (numberState n) =
      ∑ k ∈ range (n + 1), (((n - k).factorial : ℂ)⁻¹ * (-conj α) ^ (n - k) *
        (sqrtC n.factorial / sqrtC k.factorial)) • numberState k := by
  ext m
  obtain ⟨l, rfl⟩ : ∃ l, m = Finsupp.single () l := ⟨m (), Finsupp.unique_single m⟩
  rw [coeff_coeffExp, coeff_sum]
  simp only [coeff_lowerDisp_pow_numberState, coeff_smul, coeff_numberState, smul_eq_mul,
    Finsupp.single_eq_same, mul_ite, mul_one, mul_zero]
  by_cases hl : l ≤ n
  · rw [tsum_eq_single (n - l), sum_ite_eq (range (n + 1)) l, ite_eq_left (mem_range.2 (by omega)),
      ite_eq_left ⟨by omega, by omega⟩, show n - (n - l) = l by omega]
    · ring
    · intro r hr
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hr (by omega)
  · rw [sum_ite_eq (range (n + 1)) l, ite_eq_right (fun h => hl (by have := mem_range.1 h; omega))]
    refine (tsum_congr fun r => ?_).trans tsum_zero
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hl (by omega)

end FormalFock

namespace FockSpace

open FormalFock

/-- **Lemma 14.** One mode:
`⟨m∣D(α)∣n⟩ = e^{-|α|²/2} Σ_{j ≤ m, n} αᵐ⁻ʲ (-ᾱ)ⁿ⁻ʲ √(m! n!)/((m-j)! (n-j)! j!)`, a finite sum. -/
theorem displacement_matrixElement (α : ℂ) (m n : ℕ) :
    (displacement (fun _ : Unit => α) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (lp.single 2 (Finsupp.single () n) 1) (Finsupp.single () m) =
      ((Real.exp (-‖α‖ ^ 2 / 2) : ℝ) : ℂ) * ∑ j ∈ range (min m n + 1),
        α ^ (m - j) * (-conj α) ^ (n - j) * (Real.sqrt (m.factorial * n.factorial : ℕ) : ℂ) /
          ((m - j).factorial * (n - j).factorial * j.factorial : ℕ) := by
  rw [← coeff_toFormal, toFormal_displacement, toFormal_lpSingle, orderedDisplacement,
    coeff_smul, smul_eq_mul, ← numberState, coeffExp_lowerDisp_numberState, map_sum, coeff_sum]
  simp only [univ_unique, sum_singleton]
  congr 1
  simp only [map_smul, coeff_smul, smul_eq_mul, raiseDisp_exp_numberState,
    coeff_gaussExp_numberState, cMatrix_zero_left, mul_ite, mul_zero]
  rw [← sum_filter]
  have hfilt : (range (n + 1)).filter (fun k => k ≤ m) = range (min m n + 1) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  rw [hfilt]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  have h0 : ∀ k : ℕ, sqrtC k.factorial ≠ 0 := fun k => sqrtC_ne_zero (Nat.factorial_pos k)
  have hmn : (Real.sqrt (m.factorial * n.factorial : ℕ) : ℂ) =
      sqrtC m.factorial * sqrtC n.factorial := by
    rw [← sqrtC_mul]
    rfl
  have hjj := sqrtC_mul_self j.factorial
  rw [hmn]
  push_cast
  have hf : ∀ k : ℕ, (k.factorial : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  field_simp
  rw [← hjj]
  ring

end FockSpace

/-! ### Theorem 10(c): the generator -/

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector with at most `e` particles is the finite sum of its components. -/
theorem VanishesAbove.eq_sum {e : ℕ} {ψ : FormalFock ι ℂ}
    (h : VanishesAbove e ψ) :
    ψ = ∑ m ∈ (range (e + 1)).biUnion fun d => finsuppAntidiag univ d,
      ψ.coeff m • single m (1 : ℂ) :=
  eq_sum_single_of_support_subset fun p hp => by
    rw [Finset.mem_coe, mem_biUnion]
    refine ⟨p.degree, mem_range.2 ?_, mem_finsuppAntidiag_univ.2 rfl⟩
    by_contra hle
    exact hp (h p (by omega))

omit [Fintype ι] [DecidableEq ι] in
/-- `aⱼ` removes a particle: if `ψ(p) = 0` whenever `e < |p| + s`, then `(aⱼ ψ)(p) = 0`
whenever `e < |p| + s + 1`. -/
theorem annihilate_vanishes {e s : ℕ} {ψ : FormalFock ι ℂ}
    (h : ∀ p : ι →₀ ℕ, e < p.degree + s → ψ.coeff p = 0) (j : ι) :
    ∀ p : ι →₀ ℕ, e < p.degree + (s + 1) → (annihilate j ψ).coeff p = 0 := fun p hp => by
  rw [coeff_annihilate, h _ (by rw [map_add, Finsupp.degree_single]; omega), smul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- If `L` removes at least one particle and `ψ` has at most `e` particles, then `(Lᵏ ψ)(p) = 0`
whenever `e < |p| + k`; in particular `Lᵏ ψ = 0` for `k > e`. -/
theorem vanishes_pow_of_lowers {L : Module.End ℂ (FormalFock ι ℂ)}
    (hL : ∀ (e s : ℕ) (ψ : FormalFock ι ℂ),
      (∀ p : ι →₀ ℕ, e < p.degree + s → ψ.coeff p = 0) →
        ∀ p : ι →₀ ℕ, e < p.degree + (s + 1) → (L ψ).coeff p = 0)
    {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ) (k : ℕ) :
    ∀ p : ι →₀ ℕ, e < p.degree + k → ((L ^ k) ψ).coeff p = 0 := by
  induction k with
  | zero => simpa using fun p (hp : e < p.degree) => h p hp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hL e k _ ih

omit [Fintype ι] [DecidableEq ι] in
/-- If `L` removes at least one particle, then `Lᵏ ψ = 0` for `k > e` when `ψ` has at most `e`
particles, and `e^L ψ = Σ_{k ≤ M} Lᵏ ψ / k!` coefficientwise for every `M ≥ e`. -/
theorem coeffExp_eq_sum_of_lowers {L : Module.End ℂ (FormalFock ι ℂ)}
    (hL : ∀ (e s : ℕ) (ψ : FormalFock ι ℂ),
      (∀ p : ι →₀ ℕ, e < p.degree + s → ψ.coeff p = 0) →
        ∀ p : ι →₀ ℕ, e < p.degree + (s + 1) → (L ψ).coeff p = 0)
    {e M : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ) (hM : e ≤ M) :
    coeffExp L ψ = ∑ k ∈ range (M + 1), ((k.factorial : ℂ))⁻¹ • (L ^ k) ψ := by
  have hk := vanishes_pow_of_lowers hL h
  ext p
  rw [coeff_coeffExp, coeff_sum, tsum_eq_sum (s := range (M + 1)) fun k hk' => by
    rw [hk k p (by rw [mem_range] at hk'; omega), mul_zero]]
  simp only [coeff_smul, smul_eq_mul]

omit [DecidableEq ι] in
/-- `-ᾱ·a` removes a particle. -/
theorem lowerDisp_lowers (α : ι → ℂ) (e s : ℕ) (ψ : FormalFock ι ℂ)
    (h : ∀ p : ι →₀ ℕ, e < p.degree + s → ψ.coeff p = 0) :
    ∀ p : ι →₀ ℕ, e < p.degree + (s + 1) → (lowerDisp α ψ).coeff p = 0 := fun p hp => by
  rw [lowerDisp, LinearMap.neg_apply, coeff_neg, LinearMap.sum_apply, coeff_sum,
    sum_eq_zero fun j _ => by rw [LinearMap.smul_apply, coeff_smul,
      annihilate_vanishes h j p hp, smul_zero], neg_zero]

/-- `Γ(diag d) ∣m⟩ = (Πⱼ dⱼ^{mⱼ}) ∣m⟩`. -/
theorem secondQuant_diagonal_single (d : ι → ℂ) (m : ι →₀ ℕ) :
    secondQuant (Matrix.diagonal d) (single m 1) = (m.prod fun j k => d j ^ k) • single m 1 := by
  refine toBargmann.injective ?_
  have hl : ∀ j, linearForms (Matrix.diagonal d) j = d j • MvPowerSeries.X j := fun j => by
    rw [linearForms, sum_eq_single j (fun k _ hk => by rw [Matrix.diagonal_apply_ne d hk,
      zero_smul]) (by simp), Matrix.diagonal_apply_eq]
  rw [toBargmann_secondQuant_single, map_smul, toBargmann_single, mul_one]
  simp only [hl]
  rw [← MvPowerSeries.monomial_eq, ← map_smul, ← map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `lowerDisp (tα) = t · lowerDisp α` for real `t`. -/
private theorem lowerDisp_ofReal_smul (α : ι → ℂ) (t : ℝ) :
    lowerDisp ((t : ℂ) • α) = (t : ℂ) • lowerDisp α := by
  simp only [lowerDisp, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, smul_neg,
    Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
/-- The scalar `e^{-t²|α|²/2} tᵏ/k!` of `D(tα)`: value `δₖ₀` and derivative `δₖ₁` at `t = 0`. -/
private theorem hasDerivAt_dispScalar (α : ι → ℂ) (k : ℕ) :
    HasDerivAt (fun t : ℝ => ((Real.exp (-(∑ j, ‖((t : ℂ) • α) j‖ ^ 2) / 2) : ℝ) : ℂ) *
      ((t : ℂ) ^ k * ((k.factorial : ℂ))⁻¹)) (if k = 1 then 1 else 0) 0 := by
  have hn : ∀ t : ℝ, ∑ j, ‖((t : ℂ) • α) j‖ ^ 2 = t ^ 2 * ∑ j, ‖α j‖ ^ 2 := fun t => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, ← Finset.mul_sum]
  have hg : HasDerivAt (fun t : ℝ => Real.exp (-(∑ j, ‖((t : ℂ) • α) j‖ ^ 2) / 2)) 0 0 := by
    simp only [hn]
    have := (((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∑ j, ‖α j‖ ^ 2)).neg.div_const 2).exp
    simpa using this
  have hp : HasDerivAt (fun t : ℝ => (t : ℂ) ^ k * ((k.factorial : ℂ))⁻¹)
      (((k : ℝ) * 0 ^ (k - 1) : ℝ) * ((k.factorial : ℂ))⁻¹) 0 := by
    have := ((hasDerivAt_pow k (0 : ℝ)).ofReal_comp).mul_const ((k.factorial : ℂ))⁻¹
    simpa using this
  convert hg.ofReal_comp.mul hp using 1
  rcases k with _ | _ | k <;> simp

/-- **Theorem 10(c)** on a number state. -/
private theorem hasDerivAt_displacement_smul_single (α : ι → ℂ) (n : ι →₀ ℕ) {G : FockSpace ι}
    (hG : toFormal G =
      (∑ j, (α j • create j - conj (α j) • annihilate j) : Module.End ℂ (FormalFock ι ℂ))
        (single n 1)) :
    HasDerivAt (fun t : ℝ => (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι)
      (lp.single 2 n 1)) G 0 := by
  -- `V m t = e^{tα·a†} ∣m⟩` in `Γ_s`, with derivative `W m = α·a† ∣m⟩` at `t = 0`
  choose V hV using fun (m : ι →₀ ℕ) (t : ℝ) =>
    (mem_range_toFormal_iff ((raiseDisp ((t : ℂ) • α)).exp (single m 1))).2
      (sqNorm_raiseDisp_exp_lt_top _ m)
  have hVd : ∀ m, ∃ w : FockSpace ι, toFormal w = (raiseDisp α).op (single m 1) ∧
      HasDerivAt (V m) w 0 := by
    intro m
    obtain ⟨w, hw⟩ := exists_toFormal_eq_of_vanishesAbove
      ((vanishesAbove_single m 1).gaussRaise_op 0 α)
    refine ⟨w, hw, hasDerivAt_gaussRaise_exp (κ := fun _ => 0) (ℓ := fun t => (t : ℂ) • α)
      (κ' := 0) (ℓ' := α) (fun j => hasDerivAt_const _ _) (fun j => ?_) rfl (by simp) m
      (fun t => hV m t) hw⟩
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (α j)
  choose W hWf hWd using hVd
  have hV0 : ∀ m, toFormal (V m 0) = single m 1 := fun m => by
    rw [hV, NumberRaisingOp.exp_of_op_eq_zero (by simp [raiseDisp_op])]
    rfl
  have hvan : ∀ k, VanishesAbove n.degree ((lowerDisp α ^ k) (single n 1)) := fun k p hp =>
    vanishes_pow_of_lowers (lowerDisp_lowers α) (vanishesAbove_single n 1) k p (by omega)
  -- the expansion `D(tα)∣n⟩ = Σₖ Σₘ e^{-t²|α|²/2} (tᵏ/k!) ((-ᾱ·a)ᵏ∣n⟩)(m) e^{tα·a†}∣m⟩`
  have hf : (fun t : ℝ => (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι)
      (lp.single 2 n 1)) = fun t : ℝ => ∑ k ∈ range (n.degree + 2),
        ∑ m ∈ (range (n.degree + 1)).biUnion fun d => finsuppAntidiag univ d,
          ((((Real.exp (-(∑ j, ‖((t : ℂ) • α) j‖ ^ 2) / 2) : ℝ) : ℂ) *
            ((t : ℂ) ^ k * ((k.factorial : ℂ))⁻¹)) *
              ((lowerDisp α ^ k) (single n 1)).coeff m) • V m t := by
    funext t
    refine toFormal_injective ?_
    rw [toFormal_displacement, toFormal_lpSingle, orderedDisplacement,
      coeffExp_eq_sum_of_lowers (lowerDisp_lowers _) (vanishesAbove_single n 1)
        (M := n.degree + 1) (by omega), lowerDisp_ofReal_smul]
    simp only [smul_pow, LinearMap.smul_apply]
    have hξ : ∑ k ∈ range (n.degree + 1 + 1),
        ((k.factorial : ℂ))⁻¹ • (t : ℂ) ^ k • (lowerDisp α ^ k) (single n 1) =
        ∑ k ∈ range (n.degree + 2),
          ∑ m ∈ (range (n.degree + 1)).biUnion fun d => finsuppAntidiag univ d,
            (((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * ((lowerDisp α ^ k) (single n 1)).coeff m) •
              single m (1 : ℂ) := by
      refine sum_congr rfl fun k _ => ?_
      conv_lhs => rw [(hvan k).eq_sum]
      rw [smul_sum, smul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [smul_smul, smul_smul]
    rw [hξ]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, hV]
    refine sum_congr rfl fun k _ => sum_congr rfl fun m _ => ?_
    congr 1
    ring
  rw [hf]
  have hd := HasDerivAt.fun_sum fun k (_ : k ∈ range (n.degree + 2)) =>
    HasDerivAt.fun_sum fun m (_ : m ∈ (range (n.degree + 1)).biUnion
      fun d => finsuppAntidiag univ d) =>
      ((hasDerivAt_dispScalar α k).mul_const (((lowerDisp α ^ k) (single n 1)).coeff m)).smul
        (hWd m)
  refine hd.congr_deriv (toFormal_injective ?_)
  rw [hG]
  simp only [map_sum, map_add, map_smul, hWf, hV0]
  rw [sum_range_succ', sum_range_succ']
  simp only [Complex.ofReal_zero, Pi.smul_apply, smul_eq_mul, zero_mul, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, neg_zero, zero_div,
    Real.exp_zero, Complex.ofReal_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self,
    mul_zero, zero_smul, Nat.add_eq_right, ↓reduceIte, add_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, inv_one, mul_one, one_mul, pow_zero, Nat.factorial_zero,
    Module.End.one_apply, coeff_single, mul_ite, ite_smul, one_smul, zero_ne_one, ite_self,
    sum_ite_eq', mem_biUnion, mem_range, Order.lt_add_one_iff, mem_finsuppAntidiag, subset_univ,
    and_true, exists_eq_right', sum_sub_distrib, LinearMap.sub_apply, LinearMap.coe_sum,
    LinearMap.coe_smul, Finset.sum_apply]
  have h1 := (hvan 1).eq_sum
  rw [pow_one] at h1
  rw [← h1, ite_eq_left (by rw [Finsupp.degree_eq_sum]), raiseDisp_op, lowerDisp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.neg_apply]
  abel

end FockSpace

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A finitely supported vector of `Γ_s` is the finite sum of its components. -/
theorem eq_sum_lpSingle_of_finite {φ : FockSpace ι} (hφ : (Function.support φ).Finite) :
    φ = ∑ n ∈ hφ.toFinset, φ n • (lp.single 2 n (1 : ℂ) : FockSpace ι) := by
  refine toFormal_injective ?_
  rw [map_sum]
  ext p
  simp only [map_smul, toFormal_lpSingle, coeff_sum, coeff_smul, coeff_single, coeff_toFormal,
    smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, Set.Finite.mem_toFinset,
    Function.mem_support, ne_eq]
  split_ifs with h <;> simp_all

omit [DecidableEq ι] in
/-- **Theorem 10(c).** On a finitely supported `φ`, `t ↦ D(tα) φ` is differentiable at `t = 0`
with derivative the generator `(α·a† - ᾱ·a) φ`. -/
theorem hasDerivAt_displacement_smul (α : ι → ℂ) {φ G : FockSpace ι}
    (hφ : (Function.support φ).Finite)
    (hG : toFormal G = (∑ j, (α j • create j - conj (α j) • annihilate j) :
      Module.End ℂ (FormalFock ι ℂ)) (toFormal φ)) :
    HasDerivAt (fun t : ℝ => (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι) φ)
      G 0 := by
  classical
  have hGn : ∀ n : ι →₀ ℕ, ∃ g : FockSpace ι, toFormal g =
      (∑ j, (α j • create j - conj (α j) • annihilate j) : Module.End ℂ (FormalFock ι ℂ))
        (single n 1) := fun n => by
    refine exists_toFormal_eq_of_vanishesAbove (e := n.degree + 1) fun p hp => ?_
    rw [LinearMap.sum_apply, coeff_sum]
    refine sum_eq_zero fun j _ => ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, coeff_sub, coeff_smul,
      coeff_smul, (vanishesAbove_single n 1).create j p hp,
      annihilate_vanishes (s := 0) (fun q hq => vanishesAbove_single n 1 q (by omega)) j p
        (by omega), smul_zero, smul_zero, sub_zero]
  choose g hg using hGn
  have hGsum : G = ∑ n ∈ hφ.toFinset, φ n • g n := by
    refine toFormal_injective ?_
    rw [hG]
    conv_lhs => rw [eq_sum_lpSingle_of_finite hφ]
    simp only [map_sum, map_smul, toFormal_lpSingle, hg]
  rw [hGsum]
  have hf : (fun t : ℝ => (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι) φ) =
      fun t : ℝ => ∑ n ∈ hφ.toFinset, φ n •
        (displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι) (lp.single 2 n 1) := by
    funext t
    conv_lhs => rw [eq_sum_lpSingle_of_finite hφ]
    simp only [map_sum, map_smul]
  rw [hf]
  exact HasDerivAt.fun_sum fun n _ =>
    (hasDerivAt_displacement_smul_single α n (hg n)).const_smul (φ n)

end FockSpace

end BosonicLean.Fock
