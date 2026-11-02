/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.Quadratic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Quadratic Hamiltonians generate Gaussian unitaries

For `H = ½ R̂ᵀ K R̂ + fᵀ R̂` with `K` real symmetric and `f` real, `e^{-itH̄}` is a Gaussian unitary
with symplectic matrix `M_t = exp(tΩK)` and displacement vector `d_t = ∫₀ᵗ exp(sΩK) Ωf ds`: the
classical flow of the Hamilton function `½ xᵀKx + fᵀx`. The paper (Tjoa and Cirac,
arXiv:2607.28753) states this as (1) and (3).

## The classical flow

* `M_t` is a one-parameter group of symplectic matrices, with `M_t⁻¹ = M_{-t}`;
* `d_t` satisfies the cocycle identity `d_{s+t} = d_s + M_s d_t`;
* the exponential series `Σ_k (-t)ᵏ (ΩK)ᵏ u / k! = M_t⁻¹ u`;
* the series `Σ_{k ≥ 0} (-t)^{k+1} fᵀ (ΩK)ᵏ u / (k+1)! = σ(u, d_t)`.

## Main results

* `FockSpace.isGenerator_field_weylOp`, `FockSpace.isGenerator_displacement` (Corollary 9,
  displacements): `W(sv) = e^{-isΦ̄_v}` with the field `Φ_v = σ(v, R̂)`, and
  `D(sα) = e^{-is i(α·a† - ᾱ·a)}`, the paper's (5).
* `FockSpace.exists_maxRealization_field_apply_eq` (the identity `(*)`): for `2 C_H |t| < 1` and
  `ψ ∈ 𝒟`, `Φ̄_u e^{-itH̄} ψ = e^{-itH̄} (Φ_{M_t⁻¹u} + σ(u, d_t)) ψ`. The proof rearranges the
  absolutely convergent double series obtained from the Leibniz rule
  `Φ_u Hᵐ = Σ_{a + b = m} C(m, a) Hᵇ adᵃ Φ_u` and `adᵃ Φ_u = (-i)ᵃ (Φ_{(ΩK)ᵃu} + λ_a)`, and
  compares coefficients in the formal Fock space.
* `FockSpace.isGaussianUnitary_of_isGenerator_quadraticHamiltonian` (Theorem 7): every
  `e^{-itH̄}` is a Gaussian unitary with data `(M_t, d_t)`;
  `FockSpace.isGaussianUnitary_one_of_isGenerator_quadraticHamiltonian` is the case `t = 1`.
-/

open scoped Matrix
open Matrix Gaussian

namespace BosonicLean.Fock

variable {n : ℕ}

/-- `M_t = exp(tΩK)`. -/
noncomputable def quadraticSymplectic (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (t : ℝ) :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ := NormedSpace.exp (t • (symplecticForm n * K))

/-- `d_t = ∫₀ᵗ exp(sΩK) Ωf ds`. -/
noncomputable def quadraticDisplacement (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) (t : ℝ) : PhaseIndex n → ℝ :=
  ∫ s in (0 : ℝ)..t, quadraticSymplectic K s *ᵥ (symplecticForm n *ᵥ f)

theorem quadraticSymplectic_zero (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    quadraticSymplectic K 0 = 1 := by
  simp [quadraticSymplectic]

theorem quadraticSymplectic_add (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (s t : ℝ) :
    quadraticSymplectic K (s + t) = quadraticSymplectic K s * quadraticSymplectic K t := by
  rw [quadraticSymplectic, add_smul, Matrix.exp_add_of_commute]
  · rfl
  · exact ((Commute.refl _).smul_left s).smul_right t

theorem quadraticSymplectic_neg_mul (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (t : ℝ) :
    quadraticSymplectic K (-t) * quadraticSymplectic K t = 1 := by
  rw [← quadraticSymplectic_add, neg_add_cancel, quadraticSymplectic_zero]

theorem quadraticSymplectic_mul_neg (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (t : ℝ) :
    quadraticSymplectic K t * quadraticSymplectic K (-t) = 1 := by
  rw [← quadraticSymplectic_add, add_neg_cancel, quadraticSymplectic_zero]

theorem inv_quadraticSymplectic (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (t : ℝ) :
    (quadraticSymplectic K t)⁻¹ = quadraticSymplectic K (-t) :=
  Matrix.inv_eq_left_inv (quadraticSymplectic_neg_mul K t)

/-- `(tΩK)ᵀ = Ω (-tΩK) Ω⁻¹` for symmetric `K`: `ΩK` is a Hamiltonian matrix. -/
theorem transpose_smul_symplecticForm_mul {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (t : ℝ) :
    (t • (symplecticForm n * K))ᵀ =
      symplecticForm n * ((-t) • (symplecticForm n * K)) * (symplecticForm n)⁻¹ := by
  rw [symplecticForm_inv, transpose_smul, transpose_mul, hK.eq, transpose_symplecticForm,
    Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, symplecticForm_sq, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_smul, smul_neg]

theorem quadraticSymplectic_mem {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hK : K.IsSymm)
    (t : ℝ) : quadraticSymplectic K t ∈ symplecticGroup (Fin n) ℝ := by
  have hΩ : IsUnit (symplecticForm n) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
      (B := -symplecticForm n) (by rw [Matrix.mul_neg, symplecticForm_sq, neg_neg]))
  have h : (quadraticSymplectic K t)ᵀ * symplecticForm n * quadraticSymplectic K t =
      symplecticForm n := by
    rw [quadraticSymplectic, ← Matrix.exp_transpose, transpose_smul_symplecticForm_mul hK,
      Matrix.exp_conj _ _ hΩ, Matrix.mul_assoc _ (symplecticForm n)⁻¹,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hΩ), Matrix.mul_one,
      Matrix.mul_assoc]
    change symplecticForm n * (quadraticSymplectic K (-t) * quadraticSymplectic K t) = _
    rw [quadraticSymplectic_neg_mul, Matrix.mul_one]
  exact mem_symplecticGroup_iff'.2 h

theorem continuous_quadraticSymplectic (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    Continuous (quadraticSymplectic K) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

theorem intervalIntegrable_quadraticSymplectic_mulVec
    (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (v : PhaseIndex n → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s => quadraticSymplectic K s *ᵥ v) MeasureTheory.volume a b :=
  ((continuous_quadraticSymplectic K).matrix_mulVec continuous_const).intervalIntegrable a b

theorem quadraticDisplacement_zero (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : quadraticDisplacement K f 0 = 0 :=
  intervalIntegral.integral_same

theorem quadraticDisplacement_add (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) (s t : ℝ) :
    quadraticDisplacement K f (s + t) =
      quadraticDisplacement K f s + quadraticSymplectic K s *ᵥ quadraticDisplacement K f t := by
  set v := symplecticForm n *ᵥ f
  have hg := intervalIntegrable_quadraticSymplectic_mulVec K v
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := t)
    (fun r => quadraticSymplectic K r *ᵥ v) s
  rw [add_zero] at hshift
  rw [quadraticDisplacement, quadraticDisplacement, quadraticDisplacement,
    ← intervalIntegral.integral_add_adjacent_intervals (hg 0 s) (hg s (s + t)), ← hshift]
  congr 1
  simp_rw [quadraticSymplectic_add, ← Matrix.mulVec_mulVec]
  exact (Matrix.mulVecLin (quadraticSymplectic K s)).toContinuousLinearMap
    |>.intervalIntegral_comp_comm (hg 0 t)

/-- `Σ_k (-t)^k (ΩK)^k u / k! = M_t⁻¹ u`. -/
theorem hasSum_pow_mulVec (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (t : ℝ)
    (u : PhaseIndex n → ℝ) :
    HasSum (fun k : ℕ => ((-t) ^ k / k.factorial) • ((symplecticForm n * K) ^ k *ᵥ u))
      ((quadraticSymplectic K t)⁻¹ *ᵥ u) := by
  let φ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ →ₗ[ℝ] (PhaseIndex n → ℝ) :=
    { toFun := fun A => A *ᵥ u
      map_add' := fun A B => Matrix.add_mulVec A B u
      map_smul' := fun c A => Matrix.smul_mulVec c A u }
  have h : HasSum (fun k : ℕ => ((k.factorial⁻¹ : ℝ) • ((-t) • (symplecticForm n * K)) ^ k))
      (quadraticSymplectic K (-t)) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' _
  rw [inv_quadraticSymplectic]
  convert h.map φ φ.continuous_of_finiteDimensional using 1
  funext k
  simp only [Function.comp_apply, φ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_pow, smul_smul, Matrix.smul_mulVec, div_eq_inv_mul]

open scoped Matrix.Norms.Operator in
/-- `Σ_k |t|ᵏ |fᵀ Aᵏ u| / k!` converges for every square matrix `A`. -/
theorem summable_abs_pow_div_factorial_mul_dotProduct
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (f u : PhaseIndex n → ℝ) (t : ℝ) :
    Summable fun k : ℕ => |t| ^ k / k.factorial * |f ⬝ᵥ (A ^ k *ᵥ u)| := by
  have hdot : ∀ w : PhaseIndex n → ℝ, |f ⬝ᵥ w| ≤ (∑ i, |f i|) * ‖w‖ := fun w => by
    rw [dotProduct, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    gcongr
    exact (Real.norm_eq_abs (w i)).symm.le.trans (norm_le_pi_norm w i)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (((NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (|t| • A)).mul_right ‖u‖).mul_left
      (∑ i, |f i|))
  have hk : |t| ^ k / k.factorial * |f ⬝ᵥ (A ^ k *ᵥ u)| =
      |f ⬝ᵥ (((k.factorial⁻¹ : ℝ) • (|t| • A) ^ k) *ᵥ u)| := by
    rw [smul_pow, smul_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹ * |t| ^ k), div_eq_inv_mul]
  rw [hk]
  exact (hdot _).trans (mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _)
    (by positivity))

/-- `Σ_{k≥1} (-t)^k fᵀ(ΩK)^{k-1}u / k! = σ(u, d_t)`, written with the index shifted by one. -/
theorem hasSum_symplecticBilin_quadraticDisplacement {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ) (t : ℝ) (u : PhaseIndex n → ℝ) :
    HasSum (fun k : ℕ => (-t) ^ (k + 1) / (k + 1).factorial *
        (f ⬝ᵥ ((symplecticForm n * K) ^ k *ᵥ u)))
      (symplecticBilin n u (quadraticDisplacement K f t)) := by
  set c : ℕ → ℝ := fun k => f ⬝ᵥ ((symplecticForm n * K) ^ k *ᵥ u) with hc
  -- `σ(u, d_t) = -∫₀ᵗ fᵀ M_s⁻¹ u ds`
  have hσ : symplecticBilin n u (quadraticDisplacement K f t) =
      ∫ s in (0 : ℝ)..t, -(f ⬝ᵥ ((quadraticSymplectic K s)⁻¹ *ᵥ u)) := by
    rw [quadraticDisplacement, ← LinearMap.coe_toContinuousLinearMap' (symplecticBilin n u),
      ← ContinuousLinearMap.intervalIntegral_comp_comm _
        (intervalIntegrable_quadraticSymplectic_mulVec K _ 0 t)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [← symplecticBilin_inv_mulVec (quadraticSymplectic_mem hK s), symplecticBilin,
      Matrix.toBilin'_apply', Matrix.mulVec_mulVec, symplecticForm_sq, Matrix.neg_mulVec,
      Matrix.one_mulVec, dotProduct_neg, dotProduct_comm]
  -- `∫₀ᵗ -((-s)ᵏ/k!) c_k ds = (-t)^{k+1}/(k+1)! c_k`
  have hint : ∀ k : ℕ, ∫ s in (0 : ℝ)..t, -((-s) ^ k / k.factorial * c k) =
      (-t) ^ (k + 1) / (k + 1).factorial * c k := by
    intro k
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_div, intervalIntegral.integral_comp_neg (fun s => s ^ k),
      integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hσ, show (fun k : ℕ => (-t) ^ (k + 1) / (k + 1).factorial *
      (f ⬝ᵥ ((symplecticForm n * K) ^ k *ᵥ u))) =
      fun k => ∫ s in (0 : ℝ)..t, -((-s) ^ k / k.factorial * c k) from
    funext fun k => (hint k).symm]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => |t| ^ k / k.factorial * |c k|) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => -((-s) ^ k / k.factorial * c k))
      |>.aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ fun s hs => ?_
    have hst : |s| ≤ |t| := by
      rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hs) with h | h <;>
        refine abs_le.2 ⟨?_, ?_⟩ <;>
        linarith [le_abs_self t, neg_abs_le t, abs_nonneg t]
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, Nat.abs_cast]
    gcongr
  · exact MeasureTheory.ae_of_all _ fun s _ =>
      summable_abs_pow_div_factorial_mul_dotProduct _ f u t
  · exact intervalIntegrable_const
  · refine MeasureTheory.ae_of_all _ fun s _ => ?_
    let ψ : (PhaseIndex n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => f ⬝ᵥ v
        map_add' := fun v w => dotProduct_add f v w
        map_smul' := fun r v => dotProduct_smul r f v }
    have h := ((hasSum_pow_mulVec K s u).map ψ ψ.continuous_of_finiteDimensional).neg
    convert h using 2 with k
    simp only [Function.comp_apply, ψ, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul,
      smul_eq_mul, hc]

namespace FockSpace

open scoped ComplexConjugate
open FormalFock

/-! ### The fields generate the Weyl operators -/

/-- `α(su) = s α(u)`. -/
theorem complexOfPhase_smul (s : ℝ) (u : PhaseIndex n → ℝ) :
    complexOfPhase (s • u) = (s : ℂ) • complexOfPhase u := by
  funext j
  simp only [complexOfPhase, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- `(Ωᵀv)_{q_j} = -p_j` and `(Ωᵀv)_{p_j} = q_j`. -/
theorem transpose_symplecticForm_mulVec_inl (v : PhaseIndex n → ℝ) (j : Fin n) :
    ((symplecticForm n)ᵀ *ᵥ v) (Sum.inl j) = -v (Sum.inr j) := by
  simp [symplecticForm_eq_fromBlocks, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

theorem transpose_symplecticForm_mulVec_inr (v : PhaseIndex n → ℝ) (j : Fin n) :
    ((symplecticForm n)ᵀ *ᵥ v) (Sum.inr j) = v (Sum.inl j) := by
  simp [symplecticForm_eq_fromBlocks, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.one_apply]

/-- `α(v)·a† - conj α(v)·a = -iΦ_v`. -/
theorem sum_smul_create_sub_smul_annihilate (v : PhaseIndex n → ℝ) :
    (∑ j, (complexOfPhase v j • create j - conj (complexOfPhase v j) • annihilate j) :
      Module.End ℂ (FormalFock (Fin n) ℂ)) = (-Complex.I) • field v := by
  rw [field, Fintype.sum_sum_type, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [transpose_symplecticForm_mulVec_inl, transpose_symplecticForm_mulVec_inr, quadrature,
    complexOfPhase, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]

theorem weylOp_zero : weylOp (0 : PhaseIndex n → ℝ) = 1 := by
  have h : complexOfPhase (0 : PhaseIndex n → ℝ) = 0 := by
    simpa using complexOfPhase_smul 0 (0 : PhaseIndex n → ℝ)
  rw [weylOp, h, displacement_zero]

/-- `s ↦ W(sv)` is a strongly continuous one-parameter unitary group. -/
theorem isUnitaryGroup_weylOp (v : PhaseIndex n → ℝ) :
    IsUnitaryGroup (fun s : ℝ => weylOp (s • v)) where
  map_zero := by rw [zero_smul, weylOp_zero]
  map_add s t := by
    apply Subtype.ext
    have h : symplecticBilin n (s • v) (t • v) = 0 := by
      rw [map_smul, map_smul, LinearMap.smul_apply, isAlt_symplecticBilin v, smul_zero,
        smul_zero]
    rw [MulMemClass.coe_mul, weylOp_mul, ← add_smul, Weyl.relPhase, h]
    simp
  continuous_apply ψ := by
    simp only [weylOp, complexOfPhase_smul]
    exact (continuous_displacement_apply ψ).comp
      (Complex.continuous_ofReal.smul continuous_const)

/-- **Corollary 9**, displacements in real coordinates: the maximal realization of the field
`Φ_v = σ(v, R̂)` generates `s ↦ W(sv)`, that is `W(sv) = e^{-isΦ̄_v}`. -/
theorem isGenerator_field_weylOp (v : PhaseIndex n → ℝ) :
    IsGenerator (maxRealization (field v)) (fun s : ℝ => weylOp (s • v)) := by
  rw [field_eq_quadraticHamiltonian]
  refine isGenerator_of_hasDerivAt Matrix.isSymm_zero _ (isUnitaryGroup_weylOp v) fun ψ => ?_
  simp only [weylOp, complexOfPhase_smul]
  refine hasDerivAt_displacement_smul _ (finite_support_coe ψ) ?_
  have h := toFormal_quadraticHamiltonianOnFinite_pow 0 ((symplecticForm n)ᵀ *ᵥ v) 1 ψ
  rw [pow_one, pow_one] at h
  rw [map_neg, map_smul, h, ← field_eq_quadraticHamiltonian, sum_smul_create_sub_smul_annihilate,
    LinearMap.smul_apply, neg_smul]

/-- **Corollary 9**, displacements: `s ↦ D(sα)` is generated by the maximal realization of
`i Σⱼ (αⱼ aⱼ† - ᾱⱼ aⱼ)`, so `D(α) = e^{α·a† - ᾱ·a}`, the paper's (5). -/
theorem isGenerator_displacement (α : Fin n → ℂ) :
    IsGenerator (maxRealization (Complex.I • ∑ j, (α j • create j - conj (α j) • annihilate j) :
      Module.End ℂ (FormalFock (Fin n) ℂ))) (fun s : ℝ => displacement ((s : ℂ) • α)) := by
  have e1 : (Complex.I • ∑ j, (α j • create j - conj (α j) • annihilate j) :
      Module.End ℂ (FormalFock (Fin n) ℂ)) = field (phaseOfComplex α) := by
    conv_lhs => rw [← complexOfPhase_phaseOfComplex α]
    rw [sum_smul_create_sub_smul_annihilate, smul_smul, mul_neg, Complex.I_mul_I, neg_neg,
      one_smul]
  have e2 : (fun s : ℝ => displacement ((s : ℂ) • α)) =
      fun s : ℝ => weylOp (s • phaseOfComplex α) := by
    funext s
    rw [weylOp, complexOfPhase_smul, complexOfPhase_phaseOfComplex]
  rw [e1, e2]
  exact isGenerator_field_weylOp _

/-! ### The conjugated field on `𝒟` -/

/-- **Leibniz rule.** `X Hᵐ = Σ_{i + j = m} C(m, i) Hʲ (adⁱ X)`, where `ad X = XH - HX`. -/
theorem mul_pow_eq_sum_antidiagonal (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (X H : A) (m : ℕ) :
    X * H ^ m = ∑ p ∈ Finset.antidiagonal m,
      m.choose p.1 • (H ^ p.2 * ((LinearMap.mulRight R H - LinearMap.mulLeft R H) ^ p.1) X) := by
  set D := LinearMap.mulRight R H - LinearMap.mulLeft R H
  have hc : Commute D (LinearMap.mulLeft R H) :=
    ((LinearMap.commute_mulLeft_right H H).sub_right (Commute.refl _)).symm
  have h := hc.add_pow' m
  rw [sub_add_cancel, LinearMap.pow_mulRight] at h
  have h' := congrArg (fun T : Module.End R A => T X) h
  simp only [LinearMap.mulRight_apply] at h'
  rw [h', LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.smul_apply, (hc.pow_pow p.1 p.2).eq, Module.End.mul_apply, LinearMap.pow_mulLeft,
    LinearMap.mulLeft_apply]

/-- The constants `λ_0 = 0`, `λ_{k+1} = fᵀ(ΩK)ᵏu` of `adᵏ Φ_u`. -/
private noncomputable def adConst (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f u : PhaseIndex n → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => f ⬝ᵥ ((symplecticForm n * K) ^ k *ᵥ u)

/-- `adᵏ Φ_u = (-i)ᵏ (Φ_{(ΩK)ᵏu} + λ_k)`, with `ad X = XH - HX`. -/
private theorem ad_pow_field {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hK : K.IsSymm)
    (f u : PhaseIndex n → ℝ) (k : ℕ) :
    ((LinearMap.mulRight ℂ (quadraticHamiltonian K f) -
        LinearMap.mulLeft ℂ (quadraticHamiltonian K f)) ^ k) (field u) =
      (-Complex.I) ^ k • (field ((symplecticForm n * K) ^ k *ᵥ u) +
        ((adConst K f u k : ℝ) : ℂ) • 1) := by
  induction k with
  | zero => simp [adConst]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
    have e : ∀ (X : Module.End ℂ (FormalFock (Fin n) ℂ)) (c : ℂ),
        (X + c • 1) * quadraticHamiltonian K f - quadraticHamiltonian K f * (X + c • 1) =
          X * quadraticHamiltonian K f - quadraticHamiltonian K f * X := fun X c => by
      rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]; abel
    rw [e, field_mul_quadraticHamiltonian_sub hK, smul_smul, ← pow_succ,
      pow_succ' (symplecticForm n * K), Matrix.mulVec_mulVec]
    rfl

/-- `(-it)ᵐ/m! · C(m, a) · (-i)ᵃ = (-t)ᵃ/a! · (-it)ᵇ/b!` for `a + b = m`. -/
private theorem expCoeff_mul_choose_mul (t : ℝ) {a b m : ℕ} (h : a + b = m) :
    expCoeff t m * ((m.choose a : ℂ) * (-Complex.I) ^ a) =
      (((-t) ^ a / a.factorial : ℝ) : ℂ) * expCoeff t b := by
  subst h
  have key : (-(t : ℂ) * Complex.I) ^ a * (-Complex.I) ^ a = (-(t : ℂ)) ^ a := by
    rw [← mul_pow]
    congr 1
    linear_combination (t : ℂ) * Complex.I_sq
  rw [expCoeff, expCoeff, Nat.cast_choose ℂ (Nat.le_add_right a b), Nat.add_sub_cancel_left,
    pow_add]
  have h1 : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have h2 : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have h3 : ((a + b).factorial : ℂ) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  push_cast
  field_simp
  linear_combination (-(t : ℂ) * Complex.I) ^ b * key

/-- `Φ_u` on `𝒟`: `Φ_u = H_{0, Ωᵀu}` as a map of `𝒟`. -/
theorem toFormal_quadraticHamiltonianOnFinite_zero (u : PhaseIndex n → ℝ)
    (χ : finiteSupport (Fin n)) :
    toFormal (quadraticHamiltonianOnFinite 0 ((symplecticForm n)ᵀ *ᵥ u) χ : FockSpace (Fin n)) =
      field u (toFormal χ) := by
  have h := toFormal_quadraticHamiltonianOnFinite_pow 0 ((symplecticForm n)ᵀ *ᵥ u) 1 χ
  rw [pow_one, pow_one] at h
  rw [h, field_eq_quadraticHamiltonian]

theorem isCoeffFinite_field (u : PhaseIndex n → ℝ) : IsCoeffFinite (field u) := by
  rw [field_eq_quadraticHamiltonian]
  exact isCoeffFinite_quadraticHamiltonian _ _

/-- The series term `(-it)ᵐ/m! Φ_u Hᵐ x`, rearranged by the Leibniz rule:
`Σ_{a + b = m} (-t)ᵃ/a! (-it)ᵇ/b! Hᵇ (Φ_{(ΩK)ᵃu} + λ_a) x`. -/
private theorem expCoeff_smul_field_pow_apply {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f u : PhaseIndex n → ℝ) (t : ℝ) (m : ℕ) (x : FormalFock (Fin n) ℂ) :
    expCoeff t m • field u ((quadraticHamiltonian K f ^ m) x) =
      ∑ p ∈ Finset.antidiagonal m, ((((-t) ^ p.1 / p.1.factorial : ℝ) : ℂ) * expCoeff t p.2) •
        (quadraticHamiltonian K f ^ p.2) ((field ((symplecticForm n * K) ^ p.1 *ᵥ u) +
          ((adConst K f u p.1 : ℝ) : ℂ) • 1) x) := by
  rw [← Module.End.mul_apply, mul_pow_eq_sum_antidiagonal ℂ, LinearMap.sum_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [ad_pow_field hK, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, LinearMap.smul_apply,
    LinearMap.smul_apply, Module.End.mul_apply, smul_smul, smul_smul, mul_assoc,
    expCoeff_mul_choose_mul t (Finset.mem_antidiagonal.1 hp)]

/-- **Theorem 7**, the identity `(*)` in the formal Fock space: for `2 C_H |t| < 1`, `ψ ∈ 𝒟` and
`ξ = (Φ_{M_t⁻¹u} + σ(u, d_t)) ψ`, `Φ_u e^{-itH̄} ψ = e^{-itH̄} ξ`. -/
theorem field_toFormal_apply_of_isGenerator {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : IsGenerator (maxRealization (quadraticHamiltonian K f)) U) {t : ℝ}
    (ht : 2 * quadraticBound K f * |t| < 1) (ψ : finiteSupport (Fin n)) (u : PhaseIndex n → ℝ)
    {ξ : FockSpace (Fin n)}
    (hξ : toFormal ξ = (field ((quadraticSymplectic K t)⁻¹ *ᵥ u) +
      ((symplecticBilin n u (quadraticDisplacement K f t) : ℝ) : ℂ) • 1) (toFormal ψ)) :
    field u (toFormal ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ)) =
      toFormal ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ξ) := by
  set A := symplecticForm n * K
  set Hf := quadraticHamiltonianOnFinite K f
  set Ut := (U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
  set σt := symplecticBilin n u (quadraticDisplacement K f t)
  set w := (quadraticSymplectic K t)⁻¹ *ᵥ u
  -- the quadratures of `ψ`, in `𝒟`
  set Rk : PhaseIndex n → finiteSupport (Fin n) := fun k =>
    onFinite (quadrature k) (exists_vanishesAbove_quadrature k) ψ
  have hRk : ∀ k, toFormal (Rk k : FockSpace (Fin n)) = quadrature k (toFormal ψ) := fun k =>
    toFormal_onFinite _ _ ψ
  -- the coefficients of the double series
  set r : ℕ → ℝ := fun j => (-t) ^ j / j.factorial
  set α : PhaseIndex n → ℕ → ℂ := fun k j =>
    ((r j * ((symplecticForm n)ᵀ *ᵥ (A ^ j *ᵥ u)) k : ℝ) : ℂ)
  set β : ℕ → ℂ := fun j => ((r j * adConst K f u j : ℝ) : ℂ)
  set b : finiteSupport (Fin n) → ℕ → FockSpace (Fin n) := fun χ i =>
    expCoeff t i • ((Hf ^ i) χ : FockSpace (Fin n))
  have hb : ∀ χ, HasSum (b χ) (Ut χ) := fun χ =>
    (existsUnique_isGenerator_quadraticHamiltonian hK f).2 U hU t ht χ
  have hbs : ∀ χ, Summable fun i => ‖b χ i‖ := fun χ => by
    refine (summable_quadraticHamiltonianOnFinite K f (abs_nonneg t) ht χ).congr fun i => ?_
    simp only [b, Hf, norm_smul, norm_expCoeff]
  have hα : ∀ k, HasSum (α k) ((((symplecticForm n)ᵀ *ᵥ w) k : ℝ) : ℂ) := fun k => by
    let φ : (PhaseIndex n → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj k).comp (Matrix.mulVecLin (symplecticForm n)ᵀ)
    have h := (hasSum_pow_mulVec K t u).map φ φ.continuous_of_finiteDimensional
    refine Complex.hasSum_ofReal.2 ?_
    convert h using 1
    · funext j
      simp only [Function.comp_apply, φ, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, r, A]
    · simp only [φ, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, w]
  have hαs : ∀ k, Summable fun j => ‖α k j‖ := fun k => by
    refine (summable_abs_pow_div_factorial_mul_dotProduct A
      (fun l => (symplecticForm n)ᵀ k l) u t).congr fun j => ?_
    simp only [α, r, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg,
      Nat.abs_cast]
    rfl
  have hβ : HasSum β (σt : ℂ) := by
    refine Complex.hasSum_ofReal.2 ((hasSum_nat_add_iff' 1).1 ?_)
    simp only [Finset.sum_range_one, adConst, r, mul_zero, sub_zero]
    exact hasSum_symplecticBilin_quadraticDisplacement hK f t u
  have hβs : Summable fun j => ‖β j‖ := by
    refine (summable_nat_add_iff 1).1 ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_abs_pow_div_factorial_mul_dotProduct A f u t).mul_left |t|)
    simp only [β, r, adConst, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
      abs_neg, Nat.abs_cast]
    calc |t| ^ (j + 1) / ((j + 1).factorial : ℝ) * |f ⬝ᵥ (A ^ j *ᵥ u)|
        = |t| * (|t| ^ j / ((j + 1).factorial : ℝ) * |f ⬝ᵥ (A ^ j *ᵥ u)|) := by
          rw [pow_succ]; ring
      _ ≤ |t| * (|t| ^ j / (j.factorial : ℝ) * |f ⬝ᵥ (A ^ j *ᵥ u)|) := by
        gcongr
        omega
  have hprod : ∀ (γ : ℕ → ℂ) (χ : finiteSupport (Fin n)), (Summable fun j => ‖γ j‖) →
      Summable fun p : ℕ × ℕ => γ p.1 • b χ p.2 := fun γ χ hγ =>
    Summable.of_norm_bounded
      (hγ.mul_of_nonneg (hbs χ) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      fun p => (norm_smul _ _).le
  -- the double series and its sum
  set F : ℕ × ℕ → FockSpace (Fin n) := fun p =>
    ∑ k, α k p.1 • b (Rk k) p.2 + β p.1 • b ψ p.2
  have hF : HasSum F (∑ k, ((((symplecticForm n)ᵀ *ᵥ w) k : ℝ) : ℂ) • Ut (Rk k) +
      (σt : ℂ) • Ut ψ) :=
    (hasSum_sum fun k _ => (hα k).smul (hb _) (hprod _ _ (hαs k))).add
      (hβ.smul (hb ψ) (hprod _ _ hβs))
  have htot : ∑ k, ((((symplecticForm n)ᵀ *ᵥ w) k : ℝ) : ℂ) • Ut (Rk k) + (σt : ℂ) • Ut ψ =
      Ut ξ := by
    have hξ' : ξ = ∑ k, ((((symplecticForm n)ᵀ *ᵥ w) k : ℝ) : ℂ) • (Rk k : FockSpace (Fin n)) +
        (σt : ℂ) • (ψ : FockSpace (Fin n)) := by
      apply toFormal_injective
      rw [hξ]
      simp only [map_add, map_sum, map_smul, LinearMap.add_apply, field, LinearMap.sum_apply,
        LinearMap.smul_apply, hRk, Module.End.one_apply]
    rw [hξ', map_add, map_sum]
    simp only [map_smul]
  -- the antidiagonal sums are the terms of the series of `Φ_u U_t ψ`
  have hterm : ∀ m, ∑ p ∈ Finset.antidiagonal m, F p = expCoeff t m •
      (quadraticHamiltonianOnFinite 0 ((symplecticForm n)ᵀ *ᵥ u) ((Hf ^ m) ψ) :
        FockSpace (Fin n)) := fun m => by
    apply toFormal_injective
    rw [map_smul, toFormal_quadraticHamiltonianOnFinite_zero,
      toFormal_quadraticHamiltonianOnFinite_pow, expCoeff_smul_field_pow_apply hK, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [F, b, Hf, map_add, map_sum, map_smul, toFormal_quadraticHamiltonianOnFinite_pow, hRk,
      LinearMap.add_apply, field, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply,
      smul_add, Finset.smul_sum, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [α, r]
      push_cast
      ring
    · congr 1
      simp only [β, r]
      push_cast
      ring
  have hseries := BosonicLean.HasSum.sum_antidiagonal hF
  simp only [hterm] at hseries
  rw [htot] at hseries
  -- compare coefficients
  refine FormalFock.ext (funext fun m => ?_)
  let ℓ : FockSpace (Fin n) →ₗ[ℂ] ℂ :=
    { toFun := fun x => (field u (toFormal x)).coeff m
      map_add' := fun x y => by simp only [map_add, coeff_add]
      map_smul' := fun c x => by simp only [map_smul, coeff_smul, RingHom.id_apply] }
  have hℓ : Continuous ℓ := (isCoeffFinite_field u).continuous_coeff m
  let ev : FockSpace (Fin n) →ₗ[ℂ] ℂ :=
    { toFun := fun x => x m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Continuous ev := (lp.lipschitzWith_one_eval 2 m).continuous
  have h1 := (hb ψ).map ℓ hℓ
  have h2 := hseries.map ev hev
  have e : ⇑ℓ ∘ b ψ = ⇑ev ∘ fun i => expCoeff t i •
      (quadraticHamiltonianOnFinite 0 ((symplecticForm n)ᵀ *ᵥ u) ((Hf ^ i) ψ) :
        FockSpace (Fin n)) := by
    funext i
    simp only [Function.comp_apply, b]
    rw [map_smul, map_smul]
    congr 1
    show (field u (toFormal ((Hf ^ i) ψ : FockSpace (Fin n)))).coeff m =
      (toFormal (quadraticHamiltonianOnFinite 0 ((symplecticForm n)ᵀ *ᵥ u) ((Hf ^ i) ψ) :
        FockSpace (Fin n))).coeff m
    rw [toFormal_quadraticHamiltonianOnFinite_zero]
  rw [e] at h1
  exact h1.unique h2

/-- **Theorem 7**, the identity `(*)`: for `2 C_H |t| < 1`, `ψ ∈ 𝒟` and
`ξ = (Φ_{M_t⁻¹u} + σ(u, d_t)) ψ`, `e^{-itH̄} ψ ∈ dom Φ̄_u` and `Φ̄_u e^{-itH̄} ψ = e^{-itH̄} ξ`. -/
theorem exists_maxRealization_field_apply_eq {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : IsGenerator (maxRealization (quadraticHamiltonian K f)) U) {t : ℝ}
    (ht : 2 * quadraticBound K f * |t| < 1) (ψ : finiteSupport (Fin n)) (u : PhaseIndex n → ℝ)
    {ξ : FockSpace (Fin n)}
    (hξ : toFormal ξ = (field ((quadraticSymplectic K t)⁻¹ *ᵥ u) +
      ((symplecticBilin n u (quadraticDisplacement K f t) : ℝ) : ℂ) • 1) (toFormal ψ)) :
    ∃ h : (U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ ∈
        (maxRealization (field u)).domain,
      maxRealization (field u) ⟨_, h⟩ = (U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ξ := by
  have he := field_toFormal_apply_of_isGenerator hK f hU ht ψ u hξ
  have hmem : (U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ ∈
      (maxRealization (field u)).domain := by
    show Memℓp (field u (toFormal ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ))).coeff 2
    rw [he]
    exact ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ξ).2
  exact ⟨hmem, toFormal_injective (by rw [toFormal_maxRealization]; exact he)⟩

/-! ### Theorem 7: `e^{-itH̄}` is a Gaussian unitary -/

/-- **Theorem 7** for `2 C_H |t| < 1`, by exponentiating `(*)`. -/
theorem isGaussianUnitary_of_isGenerator_quadraticHamiltonian_of_lt
    {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : IsGenerator (maxRealization (quadraticHamiltonian K f)) U) {t : ℝ}
    (ht : 2 * quadraticBound K f * |t| < 1) :
    IsGaussianUnitary (U t) (quadraticSymplectic K t) (quadraticDisplacement K f t) := by
  refine ⟨quadraticSymplectic_mem hK t, fun u => ?_⟩
  set Z := U t
  set w := (quadraticSymplectic K t)⁻¹ *ᵥ u
  set σt := symplecticBilin n u (quadraticDisplacement K f t)
  have hZ : ∀ x, (star (Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      ((Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) x) = x := fun x => by
    show ((star (Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) *
      (Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) x = x
    rw [Unitary.star_mul_self_of_mem Z.2]
    rfl
  -- `s ↦ e^{isσ} Z* W(su) Z` is generated by `Z* Φ̄_u Z - σ`
  have hX := ((isGenerator_field_weylOp u).unitaryConj Z).addConst (-σt)
  -- on `𝒟`, `Z* Φ̄_u Z - σ = Φ_w` by `(*)`, so `Φ̄_w` generates it
  have hV := isGenerator_of_hasDerivAt Matrix.isSymm_zero ((symplecticForm n)ᵀ *ᵥ w)
    hX.isUnitaryGroup fun ψ => by
      set ξ : FockSpace (Fin n) :=
        (quadraticHamiltonianOnFinite 0 ((symplecticForm n)ᵀ *ᵥ w) ψ : FockSpace (Fin n)) +
          (σt : ℂ) • (ψ : FockSpace (Fin n)) with hξdef
      have hξ : toFormal ξ = (field w + (σt : ℂ) • 1) (toFormal ψ) := by
        simp only [ξ, map_add, map_smul, toFormal_quadraticHamiltonianOnFinite_zero,
          LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
      obtain ⟨hmem, heq⟩ := exists_maxRealization_field_apply_eq hK f hU ht ψ u hξ
      refine (hX.hasDerivAt ⟨ψ, hmem⟩).congr_deriv ?_
      congr 2
      rw [addConst_apply]
      show (star (Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
          (maxRealization (field u) ⟨(Z : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ, hmem⟩) +
          ((-σt : ℝ) : ℂ) • (ψ : FockSpace (Fin n)) = _
      rw [heq, hZ, hξdef]
      simp only [Complex.ofReal_neg, neg_smul, add_neg_cancel_right]
  have hW := isGenerator_field_weylOp w
  rw [field_eq_quadraticHamiltonian] at hW
  have h1 := congrArg (fun V : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =>
    ((V 1 : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) :
      FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) (hV.unique hW)
  simp only [one_mul, neg_neg, one_smul, MulMemClass.coe_mul, Unitary.coe_star] at h1
  have hph : ((phaseUnitary σt : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) :
      FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) = Complex.exp (σt * Complex.I) • 1 := rfl
  rw [hph, smul_mul_assoc, one_mul] at h1
  rw [← h1, smul_smul, ← Complex.exp_add, show -(σt : ℂ) * Complex.I + σt * Complex.I = 0 by ring,
    Complex.exp_zero, one_smul]

/-- **Theorem 7.** For real symmetric `K`, real `f` and every real `t`, `e^{-itH̄}` is a Gaussian
unitary with symplectic matrix `M_t = exp(tΩK)` and displacement vector
`d_t = ∫₀ᵗ exp(sΩK) Ωf ds`: `e^{itH̄} W(u) e^{-itH̄} = e^{-iσ(u, d_t)} W(M_t⁻¹u)`. Here
`e^{-itH̄}` is any (by `existsUnique_isGenerator_quadraticHamiltonian`, the unique) strongly
continuous one-parameter unitary group generated by `H̄`. -/
theorem isGaussianUnitary_of_isGenerator_quadraticHamiltonian
    {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : IsGenerator (maxRealization (quadraticHamiltonian K f)) U) (t : ℝ) :
    IsGaussianUnitary (U t) (quadraticSymplectic K t) (quadraticDisplacement K f t) := by
  set C := quadraticBound K f
  -- `U (k s) = (U s)ᵏ` has the composed data
  have hpow : ∀ {s : ℝ}, 2 * C * |s| < 1 → ∀ k : ℕ, IsGaussianUnitary (U (k * s))
      (quadraticSymplectic K (k * s)) (quadraticDisplacement K f (k * s)) := by
    intro s hs k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul]
      exact isGaussianUnitary_of_isGenerator_quadraticHamiltonian_of_lt hK f hU (by simp)
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ℝ) * s = k * s + s := by push_cast; ring
      rw [e, hU.isUnitaryGroup.map_add, quadraticSymplectic_add, quadraticDisplacement_add]
      exact ih.mul (isGaussianUnitary_of_isGenerator_quadraticHamiltonian_of_lt hK f hU hs)
  set m : ℕ := ⌈2 * C * |t|⌉₊ + 1
  have hm : (0 : ℝ) < m := by positivity
  have hs : 2 * C * |t / m| < 1 := by
    rw [abs_div, Nat.abs_cast, ← mul_div_assoc, div_lt_one hm]
    have := Nat.le_ceil (2 * C * |t|)
    have hm' : (m : ℝ) = ⌈2 * C * |t|⌉₊ + 1 := by push_cast [m]; ring
    linarith
  have h := hpow hs m
  rwa [show (m : ℝ) * (t / m) = t by field_simp] at h

/-- **Theorem 7** at `t = 1`, the paper's (3) in Weyl form: `e^{-iH̄}` is a Gaussian unitary with
symplectic matrix `exp(ΩK)` and displacement vector `d_1`. -/
theorem isGaussianUnitary_one_of_isGenerator_quadraticHamiltonian
    {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : IsGenerator (maxRealization (quadraticHamiltonian K f)) U) :
    IsGaussianUnitary (U 1) (NormedSpace.exp (symplecticForm n * K))
      (quadraticDisplacement K f 1) := by
  have h := isGaussianUnitary_of_isGenerator_quadraticHamiltonian hK f hU 1
  rwa [quadraticSymplectic, one_smul] at h

/-! ### Corollaries 8 and 9: the paper's (1) and (5) -/

section Paper

open Finset

local notation "𝔼" => Module.End ℂ (FormalFock (Fin n) ℂ)

/-- The paper's quadratic Hamiltonian `H_G = a†ha + ½(a†Δa†ᵀ + aᵀΔ̄a) + a†η + η†a`, (1). -/
noncomputable def ladderHamiltonian (h Δ : Matrix (Fin n) (Fin n) ℂ) (η : Fin n → ℂ) : 𝔼 :=
  ∑ i, ∑ j, h i j • (create i * annihilate j : 𝔼) +
    (1 / 2 : ℂ) • ∑ i, ∑ j, (Δ i j • (create i * create j : 𝔼) +
      conj (Δ i j) • (annihilate i * annihilate j : 𝔼)) +
    ∑ j, (η j • (create j : 𝔼) + conj (η j) • (annihilate j : 𝔼))

/-- The real symmetric matrix `K` of `H_G`: with `h = X + iY`, `Δ = P + iQ`,
`K = [[X + P, Q - Y], [Q + Y, X - P]]`. -/
noncomputable def ladderMatrix (h Δ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  fromBlocks (h.map Complex.re + Δ.map Complex.re) (Δ.map Complex.im - h.map Complex.im)
    (Δ.map Complex.im + h.map Complex.im) (h.map Complex.re - Δ.map Complex.re)

private theorem quad_pair (h Δ : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((ladderMatrix h Δ (Sum.inl i) (Sum.inl j) / 2 : ℝ) : ℂ) •
        (quadrature (Sum.inl i) * quadrature (Sum.inl j) : 𝔼) +
      ((ladderMatrix h Δ (Sum.inl i) (Sum.inr j) / 2 : ℝ) : ℂ) •
        (quadrature (Sum.inl i) * quadrature (Sum.inr j) : 𝔼) +
      ((ladderMatrix h Δ (Sum.inr i) (Sum.inl j) / 2 : ℝ) : ℂ) •
        (quadrature (Sum.inr i) * quadrature (Sum.inl j) : 𝔼) +
      ((ladderMatrix h Δ (Sum.inr i) (Sum.inr j) / 2 : ℝ) : ℂ) •
        (quadrature (Sum.inr i) * quadrature (Sum.inr j) : 𝔼) =
    (1 / 2 : ℂ) • (Δ i j • (create i * create j : 𝔼) +
      conj (Δ i j) • (annihilate i * annihilate j : 𝔼)) +
    (1 / 2 : ℂ) • (h i j • (create i * annihilate j : 𝔼) +
      conj (h i j) • (annihilate i * create j : 𝔼)) := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs' : (Complex.I / (Real.sqrt 2 : ℂ)) * (Complex.I / (Real.sqrt 2 : ℂ)) = -1 / 2 := by
    rw [div_mul_div_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs'' : ((Real.sqrt 2 : ℂ))⁻¹ * (Complex.I / (Real.sqrt 2 : ℂ)) = Complex.I / 2 := by
    rw [mul_div_assoc', inv_mul_eq_div, div_div, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs''' : (Complex.I / (Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ))⁻¹ = Complex.I / 2 := by
    rw [mul_comm, hs'']
  set x := (h i j).re
  set y := (h i j).im
  set p := (Δ i j).re
  set q := (Δ i j).im
  have hh : h i j = x + y * Complex.I := (Complex.re_add_im _).symm
  have hd : Δ i j = p + q * Complex.I := (Complex.re_add_im _).symm
  have hh' : conj (h i j) = x - y * Complex.I := by
    rw [hh]; simp [Complex.conj_ofReal, sub_eq_add_neg]
  have hd' : conj (Δ i j) = p - q * Complex.I := by
    rw [hd]; simp [Complex.conj_ofReal, sub_eq_add_neg]
  simp only [ladderMatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply]
  rw [hh', hd', hh, hd]
  simp only [quadrature, smul_mul_smul_comm, hs, hs', hs'', hs''', add_mul, mul_add, sub_mul,
    mul_sub, smul_add, smul_sub, smul_smul]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  push_cast
  module

private theorem linear_pair (η : Fin n → ℂ) (j : Fin n) :
    (phaseOfComplex η (Sum.inl j) : ℂ) • (quadrature (Sum.inl j) : 𝔼) +
      (phaseOfComplex η (Sum.inr j) : ℂ) • (quadrature (Sum.inr j) : 𝔼) =
    η j • (create j : 𝔼) + conj (η j) • (annihilate j : 𝔼) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))
  set x := (η j).re
  set y := (η j).im
  have he : η j = x + y * Complex.I := (Complex.re_add_im _).symm
  have he' : conj (η j) = x - y * Complex.I := by
    rw [he]; simp [Complex.conj_ofReal, sub_eq_add_neg]
  rw [he', he]
  simp only [phaseOfComplex, Sum.elim_inl, Sum.elim_inr, quadrature, smul_smul, smul_add,
    smul_sub, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  push_cast
  have e1 : (Real.sqrt 2 : ℂ) * (x : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = x := by field_simp
  have e2 : (Real.sqrt 2 : ℂ) * (y : ℂ) * (Complex.I / (Real.sqrt 2 : ℂ)) = y * Complex.I := by
    field_simp
  have e1' : (Real.sqrt 2 : ℂ) * ((η j).re : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = x := e1
  have e2' : (Real.sqrt 2 : ℂ) * ((η j).im : ℂ) * (Complex.I / (Real.sqrt 2 : ℂ)) =
      y * Complex.I := e2
  rw [e1', e2']
  module

/-- `(ladderMatrix h Δ)` is symmetric when `h` is Hermitian and `Δ` symmetric. -/
theorem ladderMatrix_isSymm {h Δ : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hΔ : Δ.IsSymm) : (ladderMatrix h Δ).IsSymm := by
  have hre : ∀ i j, (h j i).re = (h i j).re := fun i j => by
    rw [← hh.apply j i]; simp
  have him : ∀ i j, (h j i).im = -(h i j).im := fun i j => by
    rw [← hh.apply j i]; simp
  ext (k | k) (l | l) <;>
    simp only [ladderMatrix, Matrix.transpose_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sub_apply,
      Matrix.map_apply, hre k l, him k l, hΔ.apply k l] <;> ring

/-- **Corollary 8**, the identity: `H_G = H_{K,f} - ½ tr h` with `f = δ(η)`. -/
theorem ladderHamiltonian_eq {h Δ : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (η : Fin n → ℂ) :
    ladderHamiltonian h Δ η =
      quadraticHamiltonian (ladderMatrix h Δ) (phaseOfComplex η) - (Matrix.trace h / 2) • 1 := by
  classical
  -- the quadratic part, mode pair by mode pair
  have hq : (∑ k, ∑ l, ((ladderMatrix h Δ k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l : 𝔼)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (Δ i j • (create i * create j : 𝔼) +
        conj (Δ i j) • (annihilate i * annihilate j : 𝔼)) +
        (1 / 2 : ℂ) • (h i j • (create i * annihilate j : 𝔼) +
          conj (h i j) • (annihilate i * create j : 𝔼))) := by
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← quad_pair]; abel
  -- the linear part
  have hl : (∑ k, (phaseOfComplex η k : ℂ) • (quadrature k : 𝔼)) =
      ∑ j, (η j • (create j : 𝔼) + conj (η j) • (annihilate j : 𝔼)) := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => linear_pair η j
  -- normal ordering of `a_i a_j†`
  have hno : (∑ i, ∑ j, conj (h i j) • (annihilate i * create j : 𝔼)) =
      ∑ i, ∑ j, h i j • (create i * annihilate j : 𝔼) + Matrix.trace h • 1 := by
    simp only [annihilate_mul_create, smul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hh.apply i j]; rfl
    · simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Matrix.trace, Matrix.diag, ← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      exact hh.apply i i
  rw [quadraticHamiltonian, hq, hl, ladderHamiltonian]
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.smul_sum, hno]
  module

/-- **Corollary 9**, squeezing: `s ↦ S(sζ)` is generated by the maximal realization of
`(i/2) Σ_j (ζ̄_j a_j² - ζ_j a_j†²)`, so `S(ζ) = e^{½ Σ_j (ζ̄_j a_j² - ζ_j a_j†²)}`, the paper's (5). -/
theorem isGenerator_squeeze (ζ : Fin n → ℂ) :
    IsGenerator (maxRealization ((Complex.I / 2) •
        ∑ j, (conj (ζ j) • (annihilate j : 𝔼) ^ 2 - ζ j • (create j : 𝔼) ^ 2)))
      (fun s : ℝ => squeeze ((s : ℂ) • ζ)) := by
  classical
  set Δ : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => -(Complex.I * ζ j)
  have hh : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := Matrix.isHermitian_zero
  have hΔ : Δ.IsSymm := Matrix.isSymm_diagonal _
  have hK := ladderMatrix_isSymm hh hΔ
  have hX : (Complex.I / 2) • ∑ j, (conj (ζ j) • (annihilate j : 𝔼) ^ 2 - ζ j • (create j : 𝔼) ^ 2) =
      quadraticHamiltonian (ladderMatrix 0 Δ) 0 := by
    have h1 := ladderHamiltonian_eq hh (Δ := Δ) 0
    have hp : phaseOfComplex (0 : Fin n → ℂ) = 0 := by
      funext k; rcases k with j | j <;> simp [phaseOfComplex]
    rw [hp, Matrix.trace_zero, zero_div, zero_smul, sub_zero] at h1
    rw [← h1, ladderHamiltonian]
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add, Pi.zero_apply,
      map_zero, add_zero, Δ, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]
    simp only [smul_ite, ite_smul, smul_zero, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, map_neg, map_mul, Complex.conj_I, Finset.smul_sum, smul_sub, smul_add, pow_two]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_smul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    module
  have hU : IsUnitaryGroup (fun s : ℝ => squeeze ((s : ℂ) • ζ)) :=
    ⟨by simp [squeeze_zero], fun s t => Subtype.ext (squeeze_smul_mul ζ s t).symm, fun ψ =>
      (continuous_squeeze_apply ψ).comp (Complex.continuous_ofReal.smul continuous_const)⟩
  rw [hX]
  refine isGenerator_of_hasDerivAt hK 0 hU fun ψ => ?_
  refine hasDerivAt_squeeze_smul ζ (finite_support_coe ψ) ?_
  rw [map_neg, map_smul, quadraticHamiltonianOnFinite, toFormal_onFinite, ← hX]
  simp only [LinearMap.smul_apply, smul_smul, LinearMap.sum_apply, LinearMap.sub_apply,
    Finset.smul_sum, smul_sub]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.I * (Complex.I / 2 * (starRingEnd ℂ) (ζ j)) = -((starRingEnd ℂ) (ζ j) / 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  have e2 : Complex.I * (Complex.I / 2 * ζ j) = -(ζ j / 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  module

/-- `Φ_{Ωe_k} = R̂_k`. -/
theorem field_symplecticForm_mulVec_single (k : PhaseIndex n) :
    field (symplecticForm n *ᵥ Pi.single k 1) = (quadrature k : 𝔼) := by
  classical
  rw [field, Matrix.mulVec_mulVec, transpose_symplecticForm, neg_mul, symplecticForm_sq,
    neg_neg, Matrix.one_mulVec]
  simp [Pi.single_apply]

/-- **Lemma 5(b).** `[R̂_k, H] = i (ΩKR̂ + Ωf)_k`. -/
theorem quadrature_mul_quadraticHamiltonian_sub {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ) (k : PhaseIndex n) :
    (quadrature k : 𝔼) * quadraticHamiltonian K f - quadraticHamiltonian K f * quadrature k =
      Complex.I • (∑ m, (((symplecticForm n * K) k m : ℝ) : ℂ) • (quadrature m : 𝔼) +
        (((symplecticForm n *ᵥ f) k : ℝ) : ℂ) • 1) := by
  classical
  set w : PhaseIndex n → ℝ := symplecticForm n *ᵥ Pi.single k 1
  have h := field_mul_quadraticHamiltonian_sub hK f w
  rw [field_symplecticForm_mulVec_single, field_symplecticForm_mul_mulVec] at h
  rw [h]
  -- `(K Ω e_k)_m = -(ΩK)_km` and `f ⬝ Ω e_k = -(Ωf)_k`
  have hA : ∀ m, (K *ᵥ w) m = -((symplecticForm n * K) k m) := fun m => by
    have hT : (symplecticForm n * K) k m = -(K * symplecticForm n) m k := by
      have := congrFun (congrFun (show (symplecticForm n * K)ᵀ = -(K * symplecticForm n) by
        rw [Matrix.transpose_mul, transpose_symplecticForm, hK.eq, Matrix.mul_neg]) m) k
      simpa [Matrix.transpose_apply] using this
    rw [hT, neg_neg, Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hb : f ⬝ᵥ w = -((symplecticForm n *ᵥ f) k) := by
    have hT : ∀ i, symplecticForm n i k = -symplecticForm n k i := fun i => by
      have := congrFun (congrFun (transpose_symplecticForm (n := n)) k) i
      simpa [Matrix.transpose_apply] using this
    simp [w, dotProduct, Matrix.mulVec, Pi.single_apply, hT, Finset.sum_neg_distrib, mul_comm]
  simp only [hA, hb, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib, ← neg_add, smul_neg,
    neg_mul, neg_neg]

/-- The maximal realization of `T - c` is that of `T` shifted by `-c`. -/
theorem maxRealization_sub_smul_one (T : 𝔼) (c : ℝ) :
    maxRealization (T - (c : ℂ) • 1) = addConst (maxRealization T) (-c) := by
  have hdom : ∀ ψ : FockSpace (Fin n),
      ψ ∈ (maxRealization (T - (c : ℂ) • 1)).domain ↔ ψ ∈ (maxRealization T).domain := fun ψ => by
    show Memℓp ((T - (c : ℂ) • 1) (toFormal ψ)).coeff 2 ↔ Memℓp (T (toFormal ψ)).coeff 2
    have e : ((T - (c : ℂ) • 1) (toFormal ψ)).coeff =
        (T (toFormal ψ)).coeff - (c : ℂ) • ⇑ψ := by
      ext m; simp [coeff_toFormal]
    rw [e]
    exact ⟨fun h => by simpa using h.add ((lp.memℓp ψ).const_smul (c : ℂ)),
      fun h => h.sub ((lp.memℓp ψ).const_smul (c : ℂ))⟩
  refine LinearPMap.ext (Submodule.ext hdom) fun ψ h1 h2 => ?_
  apply toFormal_injective
  rw [toFormal_maxRealization]
  show _ = toFormal (maxRealization T ⟨ψ, h2⟩ + ((-c : ℝ) : ℂ) • ψ)
  rw [map_add, map_smul, toFormal_maxRealization]
  simp [sub_eq_add_neg]

/-- **Corollary 8.** For `h` Hermitian, `Δ` symmetric and `η ∈ ℂⁿ`, the maximal realization of
the paper's `H_G` (1) is self-adjoint and generates exactly one strongly continuous one-parameter
unitary group, and for every real `θ` the unitary `U_G = e^{iθ} e^{-iH̄_G}` is Gaussian with data
`(e^{ΩK}, d₁)`, `K = ladderMatrix h Δ`, `f = δ(η)`: the paper's (3) for every `U_G` of (1). -/
theorem isGaussianUnitary_ladderHamiltonian {h Δ : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hΔ : Δ.IsSymm) (η : Fin n → ℂ) :
    IsSelfAdjoint (maxRealization (ladderHamiltonian h Δ η)) ∧
      (∃! U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
        IsGenerator (maxRealization (ladderHamiltonian h Δ η)) U) ∧
      ∀ U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
        IsGenerator (maxRealization (ladderHamiltonian h Δ η)) U → ∀ θ : ℝ,
        IsGaussianUnitary (phaseUnitary θ * U 1)
          (NormedSpace.exp (symplecticForm n * ladderMatrix h Δ))
          (quadraticDisplacement (ladderMatrix h Δ) (phaseOfComplex η) 1) := by
  have hK := ladderMatrix_isSymm hh hΔ
  set K := ladderMatrix h Δ
  set f := phaseOfComplex η
  -- `tr h / 2` is real
  set c : ℝ := (Matrix.trace h).re / 2
  have hc : Matrix.trace h / 2 = (c : ℂ) := by
    have hreal : (Matrix.trace h).im = 0 := by
      have : star (Matrix.trace h) = Matrix.trace h := by
        rw [← Matrix.trace_conjTranspose, hh.eq]
      have := congrArg Complex.im this
      simp at this; linarith
    apply Complex.ext <;> simp [c, hreal]
  have hHG : maxRealization (ladderHamiltonian h Δ η) =
      addConst (maxRealization (quadraticHamiltonian K f)) (-c) := by
    rw [ladderHamiltonian_eq hh η, hc, maxRealization_sub_smul_one]
  obtain ⟨⟨V, hV, hVu⟩, -⟩ := existsUnique_isGenerator_quadraticHamiltonian hK f
  have hW := hV.addConst (-c)
  rw [← hHG] at hW
  have hsa : IsSelfAdjoint (maxRealization (ladderHamiltonian h Δ η)) := hW.isSelfAdjoint
  refine ⟨hsa, ⟨_, hW, fun U hU => hU.unique hW⟩, fun U hU θ => ?_⟩
  have hUe := hU.unique hW
  rw [hUe]
  -- `e^{iθ} e^{ic} V 1`: scalars times a Gaussian unitary
  have hph : ∀ a : ℝ, IsGaussianUnitary (n := n) (phaseUnitary (E := FockSpace (Fin n)) a) 1 0 :=
    fun a => isGaussianUnitary_of_eq_smul_one (c := Complex.exp (a * Complex.I)) rfl
  have h1 := isGaussianUnitary_one_of_isGenerator_quadraticHamiltonian hK f hV
  have h2 := (hph θ).mul ((hph (1 * -(-c))).mul h1)
  simp only [one_mul, Matrix.one_mulVec, zero_add] at h2
  rw [← mul_assoc] at h2 ⊢
  simpa only [one_mul] using h2

end Paper

end FockSpace

end BosonicLean.Fock
