/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Squeeze
import BosonicLean.PhaseSpace.BlochMessiah
import BosonicLean.Weyl.System

/-!
# Gaussian unitaries on the bosonic Fock space

In real coordinates `u = (q, p) ∈ ℝ^{2N}`, positions first, with `α(u) = (q + ip)/√2` and the
symplectic form `σ(u, v) = uᵀ Ω v` of `BosonicLean.PhaseSpace`, the Weyl operators are
`W(u) = D(α(u))`; they satisfy the Weyl relation `W(u) W(v) = e^{-iσ(u, v)/2} W(u + v)` of
`BosonicLean.Weyl`, and `⟨0∣W(u)∣0⟩ = e^{-|u|²/4}`. A unitary `U` is a **Gaussian unitary** with
symplectic matrix `S` and displacement vector `d` if `U* W(u) U = e^{-iσ(u, d)} W(S⁻¹u)` for every
`u`: the Weyl form of the paper's (A3), `U†R̂U = SR̂ + d`. The data compose like affine maps and are
unique.

The displacements, the second quantizations of unitary matrices and the squeezing operators are
Gaussian, with data `(1, δ(α))`, `(O_𝒰, 0)` and `(M_ζ, 0)`; for real squeezing parameters `M_r` is
the squeezing matrix `Σ(r)` of the Bloch–Messiah decomposition. Conversely, by the irreducibility
of the Fock representation, every Gaussian unitary is `c Γ(𝒰) D(α) S(r) Γ(𝒲)` with `|c| = 1` for a
Bloch–Messiah decomposition `S = O_𝒰 Σ(r) O_𝒲`: the paper's Proposition 5.

## Main definitions

* `BosonicLean.Fock.complexOfPhase`, `BosonicLean.Fock.phaseOfComplex`: `α(u)` and `δ(α)`.
* `BosonicLean.Fock.symplecticBilin n`: `σ(u, v) = uᵀ Ω v`.
* `BosonicLean.Fock.FockSpace.weylOp u`: the Weyl operator `W(u)`.
* `BosonicLean.Fock.FockSpace.IsGaussianUnitary U S d`: Definition 18.
* `BosonicLean.Fock.squeezeSymplectic ζ`: the symplectic matrix `M_ζ` of `S(ζ)`.
* `BosonicLean.Fock.FockSpace.quadrature k`: the quadratures `R̂ = (q̂, p̂)` on formal vectors.

## Main results

* `BosonicLean.Fock.isAlt_symplecticBilin`: `σ(u, u) = 0`;
  `BosonicLean.Fock.eq_of_exp_symplecticBilin_eq`: `e^{-iσ(u, d)} = e^{-iσ(u, d')}` for every `u`
  forces `d = d'`.
* `FockSpace.weylOp_mul`, `inner_vacuum_weylOp`, `star_weylOp`, `IsGaussianUnitary.mul`,
  `IsGaussianUnitary.star`, `isGaussianUnitary_of_eq_smul_one`, `IsGaussianUnitary.unique`,
  `IsGaussianUnitary.exists_eq_smul`: Proposition 19.
* `FockSpace.isGaussianUnitary_displacement`, `isGaussianUnitary_secondQuantRep`,
  `isGaussianUnitary_squeeze`, `squeezeSymplectic_ofReal` (in `BosonicLean.Fock`),
  `isGaussianUnitary_conj_squeeze_single`, `hasDerivAt_conj_squeeze_single`: Theorem 20, with
  the paper's (30) and (31).
* `FockSpace.IsGaussianUnitary.eq_of_blochMessiah`, `IsGaussianUnitary.exists_decomposition`,
  `isGaussianUnitary_decomposition`,
  `secondQuantRep_mul_displacement_mul_squeeze_mul_secondQuantRep`: Theorem 21, the paper's
  Proposition 5.
* `FockSpace.displacement_squeeze_vacuum`, `displacement_squeeze_vacuum_unit`,
  `apply_vacuum_of_eq_decomposition`, `IsGaussianUnitary.apply_vacuum`,
  `IsGaussianUnitary.exists_eq_oneMode`, `exists_toFormal_eq_affine`,
  `IsGaussianUnitary.quadrature_apply`,
  `IsGaussianUnitary.apply_mem_maxDomain_iff`: Corollary 22, the paper's (8), (11), (6) and (A3)
  on `𝒬 = ⋂ⱼ dom aⱼ`.

Only this direction of (A3) is proved: a Gaussian unitary in the Weyl sense maps `𝒬` onto itself
and satisfies `U* R̂ₖ U = Σₗ Sₖₗ R̂ₗ + dₖ` there; the converse is not formalized.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), Proposition 5, (6), (8), (11), (30), (31), (A1)–(A42).
-/

open scoped InnerProductSpace ComplexConjugate Matrix
open Finset Matrix Gaussian

namespace BosonicLean.Fock

variable {n : ℕ}

/-! ### Real coordinates -/

/-- `α(u) = (q + ip)/√2` for `u = (q, p)`, positions first. -/
noncomputable def complexOfPhase (u : PhaseIndex n → ℝ) : Fin n → ℂ := fun j =>
  ((u (Sum.inl j) : ℂ) + (u (Sum.inr j) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

/-- The displacement vector `δ(α) = √2 (Re α, Im α)`, positions first (the paper's (A33)). -/
noncomputable def phaseOfComplex (α : Fin n → ℂ) : PhaseIndex n → ℝ :=
  Sum.elim (fun j => Real.sqrt 2 * (α j).re) (fun j => Real.sqrt 2 * (α j).im)

private theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num))

private theorem sqrt_two_mul_self : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `α(δ(α)) = α`. -/
theorem complexOfPhase_phaseOfComplex (α : Fin n → ℂ) :
    complexOfPhase (phaseOfComplex α) = α := by
  funext j
  simp only [complexOfPhase, phaseOfComplex, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_mul]
  have h := sqrt_two_ne_zero
  field_simp
  exact Complex.re_add_im _

/-- `δ(α(u)) = u`. -/
theorem phaseOfComplex_complexOfPhase (u : PhaseIndex n → ℝ) :
    phaseOfComplex (complexOfPhase u) = u := by
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  funext i
  rcases i with j | j
  · simp only [phaseOfComplex, complexOfPhase, Sum.elim_inl]
    rw [Complex.div_ofReal_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
    field_simp
  · simp only [phaseOfComplex, complexOfPhase, Sum.elim_inr]
    rw [Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    field_simp

/-- `α` is additive. -/
theorem complexOfPhase_add (u v : PhaseIndex n → ℝ) :
    complexOfPhase (u + v) = complexOfPhase u + complexOfPhase v := by
  funext j
  simp only [complexOfPhase, Pi.add_apply, Complex.ofReal_add]
  ring

/-- `α(-u) = -α(u)`. -/
theorem complexOfPhase_neg (u : PhaseIndex n → ℝ) :
    complexOfPhase (-u) = -complexOfPhase u := by
  funext j
  simp only [complexOfPhase, Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- `α` is injective. -/
theorem complexOfPhase_injective : Function.Injective (complexOfPhase (n := n)) := fun u v h => by
  rw [← phaseOfComplex_complexOfPhase u, h, phaseOfComplex_complexOfPhase]

/-- `|α(u)|² = |u|²/2`. -/
theorem sum_norm_complexOfPhase_sq (u : PhaseIndex n → ℝ) :
    ∑ j, ‖complexOfPhase u j‖ ^ 2 = (∑ i, u i ^ 2) / 2 := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [complexOfPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (by norm_num),
    ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

/-- `σ(u, v) = uᵀ Ω v`, the bilinear form of `BosonicLean.Weyl` for `n` modes. -/
noncomputable def symplecticBilin (n : ℕ) : LinearMap.BilinForm ℝ (PhaseIndex n → ℝ) :=
  Matrix.toBilin' (symplecticForm n)

/-- `σ(u, v) = Σⱼ (qⱼ p'ⱼ - pⱼ q'ⱼ)`. -/
theorem symplecticBilin_apply (u v : PhaseIndex n → ℝ) :
    symplecticBilin n u v =
      ∑ j, (u (Sum.inl j) * v (Sum.inr j) - u (Sum.inr j) * v (Sum.inl j)) := by
  rw [symplecticBilin, Matrix.toBilin'_apply, symplecticForm_eq_fromBlocks]
  simp [Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, sum_add_distrib, sum_neg_distrib]
  ring

/-- `σ` is alternating: `σ(u, u) = 0`. -/
theorem isAlt_symplecticBilin : (symplecticBilin n).IsAlt := fun u => by
  rw [symplecticBilin_apply]
  exact sum_eq_zero fun j _ => by ring

/-- **Proposition 19(a)**, per mode: `α β̄ - ᾱ β = -iσ` with `α = α(u)`, `β = α(v)`. -/
theorem sum_complexOfPhase_mul_conj_sub (u v : PhaseIndex n → ℝ) :
    ∑ j, (complexOfPhase u j * conj (complexOfPhase v j) -
      conj (complexOfPhase u j) * complexOfPhase v j) =
      -(symplecticBilin n u v : ℂ) * Complex.I := by
  rw [symplecticBilin_apply, Complex.ofReal_sum, neg_mul, sum_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [complexOfPhase, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, sqrt_two_mul_self, div_eq_iff two_ne_zero]
  push_cast
  ring

/-- A symplectic matrix preserves `σ`: `σ(Su, Sv) = σ(u, v)`. -/
theorem symplecticBilin_mulVec {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) (u v : PhaseIndex n → ℝ) :
    symplecticBilin n (S *ᵥ u) (S *ᵥ v) = symplecticBilin n u v := by
  rw [symplecticBilin, Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, mem_symplecticGroup_iff'.1 hS]

/-- `σ(S⁻¹u, v) = σ(u, Sv)` for a symplectic matrix `S`. -/
theorem symplecticBilin_inv_mulVec {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) (u v : PhaseIndex n → ℝ) :
    symplecticBilin n (S⁻¹ *ᵥ u) v = symplecticBilin n u (S *ᵥ v) := by
  rw [← symplecticBilin_mulVec hS, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (SymplecticGroup.symplectic_det hS), Matrix.one_mulVec]

/-- `α(O_𝒰 u) = 𝒰 α(u)`: `O_𝒰` is `𝒰` acting on `ℂⁿ ≅ ℝ²ⁿ`. -/
theorem complexOfPhase_mulVec_orthogonalSymplecticOfUnitary (U : unitaryGroup (Fin n) ℂ)
    (u : PhaseIndex n → ℝ) :
    complexOfPhase (orthogonalSymplecticOfUnitary U *ᵥ u) =
      (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ complexOfPhase u := by
  funext j
  simp only [complexOfPhase, orthogonalSymplecticOfUnitary, mulVec, dotProduct,
    Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply, mul_div_assoc']
  rw [← sum_div]
  congr 1
  push_cast
  rw [add_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← Complex.re_add_im ((U : Matrix (Fin n) (Fin n) ℂ) j k)]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The symplectic matrix `M_ζ = ⊕ⱼ (cⱼ I - sⱼ R_{φⱼ})` of `S(ζ)`, positions first:
`R_φ = [[cos φ, sin φ], [sin φ, -cos φ]]`, `ζⱼ = rⱼ e^{iφⱼ}`. -/
noncomputable def squeezeSymplectic (ζ : Fin n → ℂ) : Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  fromBlocks
    (diagonal fun j => Real.cosh ‖ζ j‖ -
      Real.sinh ‖ζ j‖ * (if ζ j = 0 then 0 else (ζ j).re / ‖ζ j‖))
    (diagonal fun j => -Real.sinh ‖ζ j‖ * (if ζ j = 0 then 0 else (ζ j).im / ‖ζ j‖))
    (diagonal fun j => -Real.sinh ‖ζ j‖ * (if ζ j = 0 then 0 else (ζ j).im / ‖ζ j‖))
    (diagonal fun j => Real.cosh ‖ζ j‖ +
      Real.sinh ‖ζ j‖ * (if ζ j = 0 then 0 else (ζ j).re / ‖ζ j‖))

/-- `α(M_ζ u) = L_ζ α(u)`, with `(L_ζ β)ⱼ = cⱼ βⱼ - e^{iφⱼ} sⱼ β̄ⱼ`. -/
theorem complexOfPhase_squeezeSymplectic_mulVec (ζ : Fin n → ℂ) (u : PhaseIndex n → ℝ) :
    complexOfPhase (squeezeSymplectic ζ *ᵥ u) = FockSpace.squeezeMap ζ (complexOfPhase u) := by
  funext j
  simp only [complexOfPhase, squeezeSymplectic, mulVec, dotProduct, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    diagonal_apply, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte, FockSpace.squeezeMap]
  rcases eq_or_ne (ζ j) 0 with h | h
  · simp [h]
  have hn : ‖ζ j‖ ≠ 0 := norm_ne_zero_iff.2 h
  have hn' : (‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn
  have h2 := sqrt_two_ne_zero
  have hz : ζ j / (‖ζ j‖ : ℂ) = (((ζ j).re : ℂ) + ((ζ j).im : ℂ) * Complex.I) / (‖ζ j‖ : ℂ) := by
    rw [Complex.re_add_im]
  simp only [h, ↓reduceIte, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hz,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `M_ζ` is symplectic: per mode `(c - s cos φ)(c + s cos φ) - s² sin² φ = c² - s² = 1`. -/
theorem squeezeSymplectic_mem (ζ : Fin n → ℂ) :
    squeezeSymplectic ζ ∈ symplecticGroup (Fin n) ℝ := by
  rw [squeezeSymplectic, SymplecticGroup.fromBlocks_mem_iff]
  simp only [diagonal_transpose, diagonal_mul_diagonal]
  refine ⟨by rw [funext fun j => mul_comm _ _], by rw [funext fun j => mul_comm _ _], ?_⟩
  rw [diagonal_sub, ← diagonal_one]
  congr 1
  funext j
  rcases eq_or_ne (ζ j) 0 with h | h
  · simp [h]
  have hn : ‖ζ j‖ ≠ 0 := norm_ne_zero_iff.2 h
  have hc := Real.cosh_sq_sub_sinh_sq ‖ζ j‖
  have hre : (ζ j).re ^ 2 + (ζ j).im ^ 2 = ‖ζ j‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp only [h, ↓reduceIte]
  field_simp
  linear_combination (‖ζ j‖ ^ 2) * hc - Real.sinh ‖ζ j‖ ^ 2 * hre

/-- `M_{-ζ} M_ζ = 1`. -/
theorem squeezeSymplectic_neg_mul (ζ : Fin n → ℂ) :
    squeezeSymplectic (-ζ) * squeezeSymplectic ζ = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun u => complexOfPhase_injective ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    complexOfPhase_squeezeSymplectic_mulVec, complexOfPhase_squeezeSymplectic_mulVec]
  have := FockSpace.squeezeMap_squeezeMap_neg (-ζ) (complexOfPhase u)
  rwa [neg_neg] at this

/-- `M_ζ⁻¹ = M_{-ζ}`. -/
theorem inv_squeezeSymplectic (ζ : Fin n → ℂ) :
    (squeezeSymplectic ζ)⁻¹ = squeezeSymplectic (-ζ) :=
  Matrix.inv_eq_left_inv (squeezeSymplectic_neg_mul ζ)

/-- **Theorem 20(c).** For real squeezing parameters, `M_r = Σ(r)`, the squeezing matrix of the
Bloch–Messiah decomposition (the paper's (A27)–(A29)). -/
theorem squeezeSymplectic_ofReal (r : Fin n → ℝ) :
    squeezeSymplectic (fun j => (r j : ℂ)) = squeezingMatrix r := by
  have key : ∀ x : ℝ,
      Real.cosh ‖(x : ℂ)‖ - Real.sinh ‖(x : ℂ)‖ *
          (if (x : ℂ) = 0 then 0 else (x : ℂ).re / ‖(x : ℂ)‖) = Real.exp (-x) ∧
        Real.cosh ‖(x : ℂ)‖ + Real.sinh ‖(x : ℂ)‖ *
          (if (x : ℂ) = 0 then 0 else (x : ℂ).re / ‖(x : ℂ)‖) = Real.exp x ∧
        -Real.sinh ‖(x : ℂ)‖ * (if (x : ℂ) = 0 then 0 else (x : ℂ).im / ‖(x : ℂ)‖) = 0 := by
    intro x
    rcases lt_trichotomy x 0 with h | rfl | h
    · have hx : (x : ℂ) ≠ 0 := by exact_mod_cast h.ne
      simp only [hx, ↓reduceIte, Complex.ofReal_re, Complex.ofReal_im, zero_div, mul_zero,
        neg_zero, and_true, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h, Real.cosh_neg,
        Real.sinh_neg, div_neg, div_self h.ne]
      exact ⟨by rw [← Real.cosh_sub_sinh]; ring, by rw [← Real.cosh_add_sinh]; ring⟩
    · simp
    · have hx : (x : ℂ) ≠ 0 := by exact_mod_cast h.ne'
      simp only [hx, ↓reduceIte, Complex.ofReal_re, Complex.ofReal_im, zero_div, mul_zero,
        and_true, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h, div_self h.ne',
        mul_one]
      exact ⟨Real.cosh_sub_sinh x, Real.cosh_add_sinh x⟩
  rw [squeezingMatrix, ← fromBlocks_diagonal, squeezeSymplectic, ← diagonal_zero]
  congr 1 <;> congr 1 <;> funext j
  · exact (key (r j)).1
  · exact (key (r j)).2.2
  · exact (key (r j)).2.2
  · exact (key (r j)).2.1

/-- `σ(u, w) = 0` for every `u` forces `w = 0`. -/
theorem eq_zero_of_symplecticBilin_eq_zero {w : PhaseIndex n → ℝ}
    (h : ∀ u, symplecticBilin n u w = 0) : w = 0 := by
  have h1 := h (symplecticForm n *ᵥ w)
  rw [symplecticBilin, Matrix.toBilin'_apply', dotProduct_self_eq_zero] at h1
  have h2 := congrArg (fun v => symplecticForm n *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, symplecticForm_sq, Matrix.neg_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero, neg_eq_zero] at h2
  exact h2

/-- If `e^{-iσ(u, d)} = e^{-iσ(u, d')}` for every `u`, then `d = d'`. -/
theorem eq_of_exp_symplecticBilin_eq {d d' : PhaseIndex n → ℝ}
    (h : ∀ u, Complex.exp (-((symplecticBilin n u d : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((symplecticBilin n u d' : ℝ) : ℂ) * Complex.I)) : d = d' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_symplecticBilin_eq_zero fun u => ?_
  by_contra hne
  set v := (Real.pi / symplecticBilin n u (d - d')) • u with hv
  have h2 : symplecticBilin n v d - symplecticBilin n v d' = Real.pi := by
    rw [← map_sub, hv, map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hne]
  have h3 : Complex.exp (-((Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    have e : -((Real.pi : ℝ) : ℂ) * Complex.I = -((symplecticBilin n v d : ℝ) : ℂ) * Complex.I +
        ((symplecticBilin n v d' : ℝ) : ℂ) * Complex.I := by
      rw [← h2]
      push_cast
      ring
    rw [e, Complex.exp_add, h v, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at h3
  norm_num at h3

/-- `O_𝒰⁻¹ = O_{𝒰*}`. -/
private theorem inv_orthogonalSymplecticOfUnitary (U : unitaryGroup (Fin n) ℂ) :
    (orthogonalSymplecticOfUnitary U)⁻¹ = orthogonalSymplecticOfUnitary (star U) :=
  Matrix.inv_eq_left_inv (by
    rw [← orthogonalSymplecticOfUnitary_mul, Unitary.star_mul_self,
      orthogonalSymplecticOfUnitary_one])

namespace FockSpace

/-! ### Definition 18 and Proposition 19: Weyl operators and Gaussian unitaries -/

/-- **Definition 18.** The Weyl operator `W(u) = D(α(u))` of the real phase-space vector `u`. -/
noncomputable def weylOp (u : PhaseIndex n → ℝ) :
    unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) :=
  displacement (complexOfPhase u)

/-- **Proposition 19(a).** The Weyl relation `W(u) W(v) = e^{-iσ(u, v)/2} W(u + v)` in the
convention of `BosonicLean.Weyl` (its `relPhase`). -/
theorem weylOp_mul (u v : PhaseIndex n → ℝ) :
    (weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * weylOp v =
      Weyl.relPhase (symplecticBilin n) u v •
        (weylOp (u + v) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) := by
  rw [weylOp, weylOp, weylOp, displacement_mul, sum_complexOfPhase_mul_conj_sub,
    complexOfPhase_add, Weyl.relPhase]
  congr 2
  push_cast
  ring

/-- **Proposition 19(a).** `⟨0∣W(u)∣0⟩ = e^{-|u|²/4}`: the vacuum has `γ = 2V = 1` and zero
displacement in the convention of `BosonicLean.Weyl`. -/
theorem inner_vacuum_weylOp (u : PhaseIndex n → ℝ) :
    ⟪vacuum, (weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) vacuum⟫_ℂ =
      ((Real.exp (-(∑ i, u i ^ 2) / 4) : ℝ) : ℂ) := by
  have hv : ∀ y : FockSpace (Fin n), ⟪vacuum, y⟫_ℂ = y 0 := fun y => by
    rw [vacuum, lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  rw [hv, weylOp, displacement_vacuum, lp.coeFn_smul, Pi.smul_apply, expVec_apply,
    sum_norm_complexOfPhase_sq]
  simp [FormalFock.sqrtFactorial, sqrtC]
  ring_nf

/-- **Proposition 19(a).** `W(u)* = W(-u)`. -/
theorem star_weylOp (u : PhaseIndex n → ℝ) : star (weylOp u) = weylOp (-u) := by
  rw [weylOp, weylOp, star_displacement, complexOfPhase_neg]

/-- **Definition 18.** `U` is a **Gaussian unitary** with symplectic matrix `S` and displacement
vector `d`: `U* W(u) U = e^{-iσ(u, d)} W(S⁻¹u)` for every `u`, the Weyl form of the paper's (A3),
`U†R̂U = SR̂ + d`. -/
def IsGaussianUnitary (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
    (S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (d : PhaseIndex n → ℝ) : Prop :=
  S ∈ symplecticGroup (Fin n) ℝ ∧
    ∀ u, (star U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * weylOp u * U =
      Complex.exp (-((symplecticBilin n u d : ℝ) : ℂ) * Complex.I) •
        (weylOp (S⁻¹ *ᵥ u) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))

/-- **Proposition 19(b).** Composition: `(S₁, d₁)(S₂, d₂) = (S₁S₂, d₁ + S₁d₂)`. -/
theorem IsGaussianUnitary.mul {U₁ U₂ : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S₁ S₂ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d₁ d₂ : PhaseIndex n → ℝ}
    (h₁ : IsGaussianUnitary U₁ S₁ d₁) (h₂ : IsGaussianUnitary U₂ S₂ d₂) :
    IsGaussianUnitary (U₁ * U₂) (S₁ * S₂) (d₁ + S₁ *ᵥ d₂) := by
  refine ⟨Submonoid.mul_mem _ h₁.1 h₂.1, fun u => ?_⟩
  have e : ∀ A B X C E : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n),
      B * A * X * (C * E) = B * (A * X * C) * E := fun _ _ _ _ _ => by simp only [mul_assoc]
  rw [MulMemClass.coe_mul, star_mul, e, h₁.2 u, mul_smul_comm, smul_mul_assoc, h₂.2, smul_smul,
    ← Complex.exp_add, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec,
    symplecticBilin_inv_mulVec h₁.1, map_add]
  congr 2
  push_cast
  ring

/-- **Proposition 19(b).** The adjoint: `U*` has the data `(S⁻¹, -S⁻¹d)`. -/
theorem IsGaussianUnitary.star {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (h : IsGaussianUnitary U S d) : IsGaussianUnitary (Star.star U) S⁻¹ (-(S⁻¹ *ᵥ d)) := by
  refine ⟨by
    rw [← SymplecticGroup.coe_inv' ⟨S, h.1⟩]
    exact (⟨S, h.1⟩⁻¹ : symplecticGroup (Fin n) ℝ).2, fun u => ?_⟩
  have hdet := SymplecticGroup.symplectic_det h.1
  have hU : (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
      Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have hX : ∀ X : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n),
      (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        (Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * X * U) *
          Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) = X := fun X => by
    simp only [← mul_assoc, hU, one_mul]
    rw [mul_assoc, hU, mul_one]
  have h1 := h.2 (S *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] at h1
  have h3 : (weylOp (S *ᵥ u) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      Complex.exp (-((symplecticBilin n (S *ᵥ u) d : ℝ) : ℂ) * Complex.I) •
        ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * weylOp u *
          Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) := by
    rw [← hX (weylOp (S *ᵥ u) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)), h1, mul_smul_comm,
      smul_mul_assoc]
  have hσ : symplecticBilin n u (S⁻¹ *ᵥ d) = symplecticBilin n (S *ᵥ u) d := by
    rw [← symplecticBilin_mulVec h.1 u (S⁻¹ *ᵥ d), Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have he : Complex.exp (-((symplecticBilin n u (-(S⁻¹ *ᵥ d)) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((symplecticBilin n (S *ᵥ u) d : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero, map_neg, hσ]
    congr 1
    push_cast
    ring
  rw [Matrix.nonsing_inv_nonsing_inv _ hdet, Unitary.coe_star, star_star, h3, smul_smul, he,
    one_smul]

/-- **Proposition 19(b).** A phase, `U = c • 1`, is Gaussian with data `(1, 0)`. -/
theorem isGaussianUnitary_of_eq_smul_one
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))} {c : ℂ}
    (hU : (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) = c • 1) : IsGaussianUnitary U 1 0 := by
  refine ⟨one_mem _, fun u => ?_⟩
  have h1 : Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * U = 1 :=
    Unitary.star_mul_self_of_mem U.2
  have hc : (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * weylOp u = weylOp u * U := by
    rw [hU, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  simp only [inv_one, Matrix.one_mulVec, map_zero, Complex.ofReal_zero, neg_zero, zero_mul,
    Complex.exp_zero, one_smul]
  rw [mul_assoc, ← hc, ← mul_assoc, h1, one_mul]

/-- If `c W(a) = c' W(b)` with `|c| = |c'| = 1`, then `a = b` and `c = c'`: by the vacuum
expectation values of Proposition 19(a). -/
theorem eq_of_smul_weylOp_eq {a b : PhaseIndex n → ℝ} {c c' : ℂ} (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1)
    (h : c • (weylOp a : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      c' • (weylOp b : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) : a = b ∧ c = c' := by
  have hrp : ∀ u v : PhaseIndex n → ℝ, ‖Weyl.relPhase (symplecticBilin n) u v‖ = 1 := fun u v =>
    Complex.norm_exp_ofReal_mul_I _
  have h1 := congrArg (fun T : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n) =>
    ⟪vacuum, ((weylOp (-b) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * T) vacuum⟫_ℂ) h
  simp only [mul_smul_comm, weylOp_mul, smul_smul, _root_.smul_apply,
    inner_smul_right, inner_vacuum_weylOp, neg_add_cancel] at h1
  have h2 := congrArg norm h1
  simp only [norm_mul, hc, hc', hrp, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sum_const_zero, neg_zero, zero_div, Real.exp_zero, abs_one] at h2
  rw [Real.exp_eq_one_iff, neg_div, neg_eq_zero, div_eq_zero_iff] at h2
  have hab : -b + a = 0 := by
    funext i
    have h3 : ∑ i, (-b + a) i ^ 2 = 0 := h2.resolve_right (by norm_num)
    rw [sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at h3
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (h3 i (mem_univ _))
  have hab' : a = b := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact hab
  refine ⟨hab', ?_⟩
  subst hab'
  have h4 := congrArg (fun T : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n) => ‖T vacuum‖)
    (sub_eq_zero.2 h)
  simp only [← sub_smul, _root_.smul_apply, norm_smul, Unitary.norm_map, norm_vacuum,
    mul_one, _root_.zero_apply, norm_zero] at h4
  exact sub_eq_zero.1 (norm_eq_zero.1 h4)

/-- **Proposition 19(c).** The data of a Gaussian unitary are unique. -/
theorem IsGaussianUnitary.unique {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S S' : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d d' : PhaseIndex n → ℝ}
    (h : IsGaussianUnitary U S d) (h' : IsGaussianUnitary U S' d') : S = S' ∧ d = d' := by
  have hS := fun u => eq_of_smul_weylOp_eq
    (by rw [← Complex.ofReal_neg]; exact Complex.norm_exp_ofReal_mul_I _)
    (by rw [← Complex.ofReal_neg]; exact Complex.norm_exp_ofReal_mul_I _)
    ((h.2 u).symm.trans (h'.2 u))
  have hinv : S⁻¹ = S'⁻¹ := Matrix.toLin'.injective (LinearMap.ext fun u => (hS u).1)
  refine ⟨by rw [← Matrix.nonsing_inv_nonsing_inv S (SymplecticGroup.symplectic_det h.1), hinv,
    Matrix.nonsing_inv_nonsing_inv _ (SymplecticGroup.symplectic_det h'.1)], ?_⟩
  exact eq_of_exp_symplecticBilin_eq fun u => (hS u).2

/-! ### Theorem 20: displacements, passive transformations and squeezers -/

/-- **Theorem 20(a).** `D(α)` is Gaussian with data `(1, δ(α))`: it translates the quadratures by
its displacement vector, the paper's (A31)–(A33). -/
theorem isGaussianUnitary_displacement (α : Fin n → ℂ) :
    IsGaussianUnitary (displacement α) 1 (phaseOfComplex α) := by
  refine ⟨Submonoid.one_mem _, fun u => ?_⟩
  rw [inv_one, Matrix.one_mulVec]
  conv_lhs => rw [← complexOfPhase_phaseOfComplex α]
  rw [← Unitary.coe_star, star_displacement, weylOp, displacement_mul, smul_mul_assoc,
    displacement_mul, smul_smul, ← Complex.exp_add,
    show -complexOfPhase (phaseOfComplex α) + complexOfPhase u +
      complexOfPhase (phaseOfComplex α) = complexOfPhase u by abel]
  congr 2
  rw [← sum_complexOfPhase_mul_conj_sub,
    ← add_div, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg]
  ring

/-- **Theorem 20(b).** `Γ(𝒰)` is Gaussian with data `(O_𝒰, 0)`: the paper's (A17)–(A19), (A26). -/
theorem isGaussianUnitary_secondQuantRep (U : unitaryGroup (Fin n) ℂ) :
    IsGaussianUnitary (secondQuantRep U) (orthogonalSymplecticOfUnitary U) 0 := by
  refine ⟨(Submonoid.mem_inf.1 (orthogonalSymplecticOfUnitary_mem U)).1, fun u => ?_⟩
  rw [weylOp, star_secondQuantRep_mul_displacement_mul, map_zero, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, one_smul, inv_orthogonalSymplecticOfUnitary, weylOp,
    complexOfPhase_mulVec_orthogonalSymplecticOfUnitary, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]

/-- **Theorem 20(c).** `S(ζ)` is Gaussian with data `(M_ζ, 0)`. -/
theorem isGaussianUnitary_squeeze (ζ : Fin n → ℂ) :
    IsGaussianUnitary (squeeze ζ) (squeezeSymplectic ζ) 0 := by
  refine ⟨squeezeSymplectic_mem ζ, fun u => ?_⟩
  rw [weylOp, star_squeeze_mul_displacement_mul, map_zero, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, one_smul, inv_squeezeSymplectic, weylOp,
    complexOfPhase_squeezeSymplectic_mulVec]

open FormalFock

/-- Changing the data along equalities. -/
private theorem IsGaussianUnitary.congr {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S S' : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d d' : PhaseIndex n → ℝ}
    (h : IsGaussianUnitary U S d) (hS : S = S') (hd : d = d') : IsGaussianUnitary U S' d' :=
  hS ▸ hd ▸ h

/-- **Theorem 20(d)**, the paper's (31): `Γ(𝒰)* S(ζ eⱼ) Γ(𝒰)` is Gaussian with data
`(O_𝒰ᵀ M_{ζeⱼ} O_𝒰, 0)`. -/
theorem isGaussianUnitary_conj_squeeze_single (U : unitaryGroup (Fin n) ℂ) (j : Fin n) (ζ : ℂ) :
    IsGaussianUnitary (star (secondQuantRep U) * squeeze (Pi.single j ζ) * secondQuantRep U)
      ((orthogonalSymplecticOfUnitary U)ᵀ * squeezeSymplectic (Pi.single j ζ) *
        orthogonalSymplecticOfUnitary U) 0 :=
  (((isGaussianUnitary_secondQuantRep U).star.mul (isGaussianUnitary_squeeze _)).mul
    (isGaussianUnitary_secondQuantRep U)).congr
    (by rw [inv_orthogonalSymplecticOfUnitary, orthogonalSymplecticOfUnitary_star])
    (by simp)

/-- `Γ(𝒰)* X² Γ(𝒰) = (Γ(𝒰)* X Γ(𝒰))²`. -/
private theorem secondQuant_conj_sq (U : unitaryGroup (Fin n) ℂ)
    (X : Module.End ℂ (FormalFock (Fin n) ℂ)) :
    secondQuant (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * X ^ 2 *
        secondQuant (U : Matrix (Fin n) (Fin n) ℂ) =
      (secondQuant (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * X *
        secondQuant (U : Matrix (Fin n) (Fin n) ℂ)) ^ 2 := by
  rw [sq, sq]
  have h := secondQuant_mul_conjTranspose_self U
  calc secondQuant (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (X * X) * secondQuant (U : Matrix _ _ ℂ) =
        secondQuant (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * X *
          (secondQuant (U : Matrix _ _ ℂ) * secondQuant (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) * X *
            secondQuant (U : Matrix _ _ ℂ) := by rw [h, mul_one]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- **Theorem 20(d)**, the paper's (31) through its one-parameter group: on a finitely supported
`φ`, the derivative of `t ↦ Γ(𝒰)* S(tζ eⱼ) Γ(𝒰) φ` at `t = 0` is `½(ζ̄ bⱼ² - ζ bⱼ†²)φ` with
`bⱼ = Σₖ 𝒰ⱼₖ aₖ`. -/
theorem hasDerivAt_conj_squeeze_single (U : unitaryGroup (Fin n) ℂ) (j : Fin n) (ζ : ℂ)
    {φ G : FockSpace (Fin n)} (hφ : (Function.support φ).Finite)
    (hG : toFormal G =
      ((conj ζ / 2) • (∑ k, (U : Matrix (Fin n) (Fin n) ℂ) j k • annihilate k) ^ 2 -
        (ζ / 2) • (∑ k, conj ((U : Matrix (Fin n) (Fin n) ℂ) j k) • create k) ^ 2 :
          Module.End ℂ (FormalFock (Fin n) ℂ)) (toFormal φ)) :
    HasDerivAt (fun t : ℝ => ((star (secondQuantRep U) * squeeze (Pi.single j ((t : ℂ) * ζ)) *
      secondQuantRep U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) :
        FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) φ) G 0 := by
  set ψ := (secondQuantRep U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) φ with hψdef
  have hψt : toFormal ψ = secondQuant (U : Matrix (Fin n) (Fin n) ℂ) (toFormal φ) := by
    rw [hψdef, secondQuantRep_apply, toFormal_secondQuantUnitary]
  obtain ⟨e, he⟩ := exists_vanishesAbove_of_finite hφ
  have hψ : (Function.support ψ).Finite :=
    (show VanishesAbove e (toFormal ψ) by rw [hψt]; exact he.secondQuant _).finite_support
  set L : Module.End ℂ (FormalFock (Fin n) ℂ) :=
    ∑ k, ((conj ((Pi.single j ζ : Fin n → ℂ) k) / 2) • annihilate k ^ 2 -
      ((Pi.single j ζ : Fin n → ℂ) k / 2) • create k ^ 2) with hL
  have hLj : L = (conj ζ / 2) • annihilate j ^ 2 - (ζ / 2) • create j ^ 2 := by
    rw [hL, sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
    simp
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : FockSpace (Fin n), toFormal G₀ = L (toFormal ψ) := by
    refine exists_toFormal_eq_of_vanishesAbove (e := e + 2) fun p hp => ?_
    rw [hLj, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, coeff_sub,
      coeff_smul, coeff_smul, hψt]
    have h1 := VanishesAbove.secondQuant he (U : Matrix (Fin n) (Fin n) ℂ)
    have h2 : VanishesAbove (e + 2) ((create j ^ 2)
        (secondQuant (U : Matrix (Fin n) (Fin n) ℂ) (toFormal φ))) := by
      rw [sq, Module.End.mul_apply]
      exact (h1.create j).create j
    rw [h2 p hp, sq, Module.End.mul_apply,
      annihilate_vanishes (annihilate_vanishes (s := 0) (fun q hq => h1 q (by omega)) j) j p
        (by omega), smul_zero, smul_zero, sub_zero]
  have hd := hasDerivAt_squeeze_smul (Pi.single j ζ) hψ hG₀
  have hsm : ∀ t : ℝ, Pi.single j ((t : ℂ) * ζ) = (t : ℂ) • (Pi.single j ζ : Fin n → ℂ) :=
    fun t => by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Pi.single_eq_of_ne hk]
  have hf : (fun t : ℝ => ((star (secondQuantRep U) * squeeze (Pi.single j ((t : ℂ) * ζ)) *
      secondQuantRep U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))) :
        FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) φ) =
      fun t : ℝ => (star (secondQuantRep U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
        ((squeeze ((t : ℂ) • (Pi.single j ζ : Fin n → ℂ)) :
          FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ) := by
    funext t
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, mul_apply_eq_comp, mul_apply_eq_comp,
      Unitary.coe_star, hsm]
  rw [hf]
  refine ((((star (secondQuantRep U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).congr_deriv (toFormal_injective ?_))
  rw [ContinuousLinearMap.coe_restrictScalars', star_secondQuantRep, secondQuantRep_apply,
    toFormal_secondQuantUnitary, hG₀, hG, hψt, hLj, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    ← secondQuant_conjTranspose_mul_annihilate_mul, ← secondQuant_conjTranspose_mul_create_mul,
    ← secondQuant_conj_sq, ← secondQuant_conj_sq]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub, map_smul]

/-! ### Theorem 21: the paper's Proposition 5 -/

/-- **Theorem 21(b).** `Γ(𝒰) D(α) S(ζ) Γ(𝒲)` is Gaussian with data
`(O_𝒰 M_ζ O_𝒲, O_𝒰 δ(α))`, the paper's (A35). -/
theorem isGaussianUnitary_decomposition (𝒰 𝒲 : unitaryGroup (Fin n) ℂ) (α ζ : Fin n → ℂ) :
    IsGaussianUnitary (secondQuantRep 𝒰 * displacement α * squeeze ζ * secondQuantRep 𝒲)
      (orthogonalSymplecticOfUnitary 𝒰 * squeezeSymplectic ζ * orthogonalSymplecticOfUnitary 𝒲)
      (orthogonalSymplecticOfUnitary 𝒰 *ᵥ phaseOfComplex α) :=
  ((((isGaussianUnitary_secondQuantRep 𝒰).mul (isGaussianUnitary_displacement α)).mul
    (isGaussianUnitary_squeeze ζ)).mul (isGaussianUnitary_secondQuantRep 𝒲)).congr
    (by rw [Matrix.mul_one]) (by simp)

/-- Two Gaussian unitaries with the same data differ by a phase (Proposition 19(c), second part,
by Corollary 12(a)). -/
theorem IsGaussianUnitary.exists_eq_smul
    {U V : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) (hV : IsGaussianUnitary V S d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) = c • (V : FockSpace (Fin n) →L[ℂ] _) := by
  refine exists_eq_smul_of_conj_eq U V fun β => ?_
  have h1 := hU.2 (phaseOfComplex β)
  have h2 := hV.2 (phaseOfComplex β)
  rw [weylOp, complexOfPhase_phaseOfComplex] at h1 h2
  rw [h1, h2]

/-- **Theorem 21(a)**, the paper's Proposition 5 and (A36)–(A37): for every Bloch–Messiah
decomposition `S = O_𝒰 Σ(r) O_𝒲`, a Gaussian unitary with data `(S, d)` is
`c Γ(𝒰) D(α) S(r) Γ(𝒲)` with `δ(α) = O_𝒰ᵀ d` and `|c| = 1`. -/
theorem IsGaussianUnitary.eq_of_blochMessiah
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) (𝒰 𝒲 : unitaryGroup (Fin n) ℂ) (r : Fin n → ℝ)
    (hS : S = orthogonalSymplecticOfUnitary 𝒰 * squeezingMatrix r *
      orthogonalSymplecticOfUnitary 𝒲) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      c • ((secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        displacement (complexOfPhase ((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d)) *
          squeeze (fun j => (r j : ℂ)) * secondQuantRep 𝒲) := by
  have hV := (isGaussianUnitary_decomposition 𝒰 𝒲
    (complexOfPhase ((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d)) fun j => (r j : ℂ)).congr
    (S' := S) (d' := d) (by rw [squeezeSymplectic_ofReal, hS])
    (by rw [phaseOfComplex_complexOfPhase, Matrix.mulVec_mulVec,
      ← orthogonalSymplecticOfUnitary_star, ← orthogonalSymplecticOfUnitary_mul,
      Unitary.mul_star_self, orthogonalSymplecticOfUnitary_one, Matrix.one_mulVec])
  obtain ⟨c, hc, h⟩ := hU.exists_eq_smul hV
  refine ⟨c, hc, ?_⟩
  rw [h, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul]

/-- **Theorem 21(a), existence form**, the paper's (A12): every Gaussian unitary is
`c Γ(𝒰) D(α) S(r) Γ(𝒲)` with `r ≥ 0` and `|c| = 1`. -/
theorem IsGaussianUnitary.exists_decomposition
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) :
    ∃ (c : ℂ) (𝒰 𝒲 : unitaryGroup (Fin n) ℂ) (α : Fin n → ℂ) (r : Fin n → ℝ),
      0 ≤ r ∧ ‖c‖ = 1 ∧ (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
        c • ((secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
          displacement α * squeeze (fun j => (r j : ℂ)) * secondQuantRep 𝒲) := by
  obtain ⟨OU, hOU, OW, hOW, r, hr, hS⟩ := exists_blochMessiah hU.1
  obtain ⟨𝒰, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOU
  obtain ⟨𝒲, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOW
  obtain ⟨c, hc, h⟩ := hU.eq_of_blochMessiah 𝒰 𝒲 r hS
  exact ⟨c, 𝒰, 𝒲, _, r, hr, hc, h⟩

/-- **Theorem 21(c)**, second part: the squeezing phases are absorbed into the passive factors,
`Γ(𝒰) D(α) S(ζ) Γ(𝒱) = Γ(𝒰 Θ) D(Θ* α) S(|ζ|) Γ(Θ* 𝒱)` for every diagonal phase matrix
`Θ = R(θ)` with `|ζⱼ| e^{-2iθⱼ} = ζⱼ`. -/
theorem secondQuantRep_mul_displacement_mul_squeeze_mul_secondQuantRep
    (𝒰 𝒱 : unitaryGroup (Fin n) ℂ) (α ζ : Fin n → ℂ) (θ : Fin n → ℝ)
    (hθ : ∀ j, (‖ζ j‖ : ℂ) * Complex.exp (-(θ j : ℂ) * Complex.I) ^ 2 = ζ j) :
    (secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        (displacement α : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        (squeeze ζ : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        (secondQuantRep 𝒱 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      (secondQuantRep (𝒰 * phaseDiag θ) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        (displacement (((star (phaseDiag θ) : unitaryGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) *ᵥ α) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
          (squeeze (fun j => (‖ζ j‖ : ℂ)) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
          (secondQuantRep (star (phaseDiag θ) * 𝒱) :
            FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) := by
  have hDR : (displacement α : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
      (secondQuantRep (phaseDiag θ) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      (secondQuantRep (phaseDiag θ) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
        displacement (((star (phaseDiag θ) : unitaryGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) *ᵥ α) := by
    rw [secondQuantRep_mul_displacement, Matrix.mulVec_mulVec, Unitary.coe_star,
      Unitary.mul_star_self_of_mem (phaseDiag θ).2, Matrix.one_mulVec]
  rw [squeeze_eq_rotation_mul_squeeze_norm_mul ζ θ hθ, rotation, star_secondQuantRep, map_mul,
    map_mul, MulMemClass.coe_mul, MulMemClass.coe_mul]
  simp only [mul_assoc]
  have key : ∀ A D R X D' : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n), D * R = R * D' →
      A * (D * (R * X)) = A * (R * (D' * X)) := fun A D R X D' h => by
    rw [← mul_assoc D, h, mul_assoc]
  exact key _ _ _ _ _ hDR

end FockSpace

/-! ### Corollary 22: the vacuum and one mode -/

namespace FormalFock

/-- `⊗ⱼ (cⱼ φⱼ) = (Πⱼ cⱼ) ⊗ⱼ φⱼ`. -/
theorem tensorVec_smul {ι : Type*} [Fintype ι] (c : ι → ℂ) (φ : ι → FormalFock Unit ℂ) :
    tensorVec (fun j => c j • φ j) = (∏ j, c j) • tensorVec φ := by
  ext n
  rw [coeff_tensorVec, coeff_smul, coeff_tensorVec, smul_eq_mul, ← prod_mul_distrib]
  rfl

end FormalFock

namespace FockSpace

open FormalFock

section Vacuum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Corollary 22(a)**, the paper's (8) on several modes:
`D(α) S(ζ)∣0⟩ = (Πⱼ cⱼ)^{-1/2} e^{-|α|²/2 - Σⱼ τⱼ ᾱⱼ²/2} ⊗ⱼ g(κⱼ, ℓⱼ)` with `κⱼ = -τⱼ/2` and
`ℓⱼ = αⱼ - 2κⱼ ᾱⱼ`. -/
theorem displacement_squeeze_vacuum (α ζ : ι → ℂ) :
    toFormal ((displacement α : FockSpace ι →L[ℂ] FockSpace ι)
      ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum)) =
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 -
            ∑ j, tanhPhase (ζ j) * conj (α j) ^ 2 / 2)) •
        tensorVec fun j =>
          gaussVec (-tanhPhase (ζ j) / 2) (α j + tanhPhase (ζ j) * conj (α j)) := by
  have hκ : ∀ j, ‖-tanhPhase (ζ j) / 2‖ < 1 / 2 := fun j => by
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [norm_tanhPhase_lt_one (ζ j)]
  obtain ⟨χ, hχ⟩ := (mem_range_toFormal_iff _).2 (sqNorm_tensorVec_lt_top fun j =>
    by rw [sqNorm_lt_top_iff, ← (Finsupp.uniqueEquiv ()).symm.summable_iff]
       exact summable_sq_coeff_gaussVec (hκ j) (α j + tanhPhase (ζ j) * conj (α j)))
  set K : ℂ := (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hK
  suffices h : (displacement α : FockSpace ι →L[ℂ] FockSpace ι)
      ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum) =
      (K * Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 -
        ∑ j, tanhPhase (ζ j) * conj (α j) ^ 2 / 2)) • χ by
    rw [h, map_smul, hχ]
  refine ext_inner_expVec fun w => ?_
  have hε : ∀ j, Summable fun m : ℕ =>
      ‖(expVecFormal fun _ : Unit => w j).coeff (Finsupp.single () m)‖ ^ 2 :=
    fun j => summable_sq_coeff_expVecFormal_unit (w j)
  have hS := hasSum_conj_mul_tensorVec hε fun j => summable_sq_coeff_gaussVec (hκ j)
    (α j + tanhPhase (ζ j) * conj (α j))
  have hin : ⟪expVec w, χ⟫_ℂ = ∏ j, Complex.exp (-tanhPhase (ζ j) / 2 * conj (w j) ^ 2 +
      (α j + tanhPhase (ζ j) * conj (α j)) * conj (w j)) := by
    refine (lp.hasSum_inner (𝕜 := ℂ) (expVec w) χ).unique ?_
    convert hS using 1
    · funext n
      rw [RCLike.inner_apply', expVec_apply, ← coeff_toFormal χ, hχ, ← coeff_expVecFormal,
        expVecFormal_eq_tensorVec]
    · refine prod_congr rfl fun j _ => ?_
      refine ((hasSum_conj_mul_coeff_expVecFormal_gaussVec ?_ (w j) _).tsum_eq).symm
      linarith [hκ j]
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← Unitary.coe_star, star_displacement,
    displacement_expVec,
    inner_smul_left, ← expVec_zero, inner_expVec_squeeze_expVec, inner_smul_right, hin,
    ← Complex.exp_conj, ← Complex.exp_sum]
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sum_const_zero, Complex.exp_zero, mul_one]
  rw [show ∀ a b c : ℂ, Complex.exp a * (b * Complex.exp c) = b * Complex.exp (a + c) from
      fun a b c => by rw [Complex.exp_add]; ring,
    show ∀ a b c : ℂ, b * Complex.exp a * Complex.exp c = b * Complex.exp (a + c) from
      fun a b c => by rw [Complex.exp_add]; ring]
  congr 2
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, map_sub, map_neg, map_div₀, map_sum,
    map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj, map_ofNat, Pi.neg_apply,
    sum_div, ← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, norm_neg]
  ring

end Vacuum

/-- **Corollary 22(a)**, the paper's (8): for one mode,
`D(α) S(ζ)∣0⟩ = c^{-1/2} e^{-|α|²/2 - τᾱ²/2} g(κ, ℓ)` with `κ = -τ/2` and `ℓ = α - 2κᾱ`. -/
theorem displacement_squeeze_vacuum_unit (α ζ : ℂ) :
    toFormal ((displacement (fun _ : Unit => α) : FockSpace Unit →L[ℂ] FockSpace Unit)
      ((squeeze (fun _ : Unit => ζ) : FockSpace Unit →L[ℂ] FockSpace Unit) vacuum)) =
      ((((Real.cosh ‖ζ‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-((‖α‖ ^ 2 : ℝ) : ℂ) / 2 - tanhPhase ζ * conj α ^ 2 / 2)) •
        gaussVec (-tanhPhase ζ / 2) (α + tanhPhase ζ * conj α) := by
  rw [displacement_squeeze_vacuum, tensorVec_unit]
  simp only [univ_unique, prod_singleton, sum_singleton]

/-- **Corollary 22(a)**, the paper's (11) and (A40)–(A42), for a given decomposition: if
`U = c Γ(𝒰) D(α) S(r) Γ(𝒲)`, the form of Theorem 21(a), then
`U∣0⟩ = c Γ(𝒰)(⊗ⱼ D(αⱼ) S(rⱼ)∣0⟩)` with the same `c`. -/
theorem apply_vacuum_of_eq_decomposition {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {c : ℂ} {𝒰 𝒲 : unitaryGroup (Fin n) ℂ} {α : Fin n → ℂ} {r : Fin n → ℝ}
    (h : (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
      c • ((secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * displacement α *
        squeeze (fun j => (r j : ℂ)) * secondQuantRep 𝒲)) :
    toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) vacuum) =
      c • secondQuant (𝒰 : Matrix (Fin n) (Fin n) ℂ) (tensorVec fun j =>
        toFormal ((displacement (fun _ : Unit => α j) : FockSpace Unit →L[ℂ] FockSpace Unit)
          ((squeeze (fun _ : Unit => (r j : ℂ)) : FockSpace Unit →L[ℂ] FockSpace Unit)
            vacuum))) := by
  rw [h, _root_.smul_apply, map_smul]
  congr 1
  simp only [displacement_squeeze_vacuum_unit]
  rw [mul_apply_eq_comp, mul_apply_eq_comp, mul_apply_eq_comp,
    secondQuantRep_vacuum, secondQuantRep_apply, toFormal_secondQuantUnitary,
    displacement_squeeze_vacuum, tensorVec_smul]
  congr 2
  rw [prod_mul_distrib, ← Complex.exp_sum, ← Complex.ofReal_prod,
    Real.finsetProd_rpow _ _ fun j _ => (Real.cosh_pos _).le]
  congr 2
  push_cast
  simp only [sum_sub_distrib, neg_div, sum_neg_distrib, sum_div]

/-- **Corollary 22(a)**, the paper's (11) and (A40)–(A42), existence form: a Gaussian unitary maps
the vacuum to `c Γ(𝒰)(⊗ⱼ D(αⱼ) S(rⱼ)∣0⟩)` with `r ≥ 0`, a passive transformation of a product of
one-mode displaced squeezed vacua. -/
theorem IsGaussianUnitary.apply_vacuum {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) :
    ∃ (c : ℂ) (𝒰 : unitaryGroup (Fin n) ℂ) (α : Fin n → ℂ) (r : Fin n → ℝ),
      0 ≤ r ∧ ‖c‖ = 1 ∧ toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) vacuum) =
        c • secondQuant (𝒰 : Matrix (Fin n) (Fin n) ℂ) (tensorVec fun j =>
          toFormal ((displacement (fun _ : Unit => α j) : FockSpace Unit →L[ℂ] FockSpace Unit)
            ((squeeze (fun _ : Unit => (r j : ℂ)) : FockSpace Unit →L[ℂ] FockSpace Unit)
              vacuum))) := by
  obtain ⟨c, 𝒰, 𝒲, α, r, hr, hc, hU'⟩ := hU.exists_decomposition
  exact ⟨c, 𝒰, α, r, hr, hc, apply_vacuum_of_eq_decomposition hU'⟩

/-- `diag(e^{-iθⱼ}) diag(e^{-iθ'ⱼ}) = diag(e^{-i(θⱼ + θ'ⱼ)})`. -/
theorem phaseDiag_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (θ θ' : ι → ℝ) :
    phaseDiag θ * phaseDiag θ' = phaseDiag (θ + θ') := by
  refine Subtype.ext ?_
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← Complex.exp_add, Pi.add_apply, Complex.ofReal_add]
  ring_nf

/-- `R(θ) R(θ') = R(θ + θ')`. -/
theorem rotation_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (θ θ' : ι → ℝ) :
    rotation θ * rotation θ' = rotation (θ + θ') := by
  rw [rotation, rotation, rotation, ← map_mul, phaseDiag_mul]

/-- Every `1 × 1` unitary matrix is `diag(e^{-iθ})`. -/
theorem exists_phaseDiag_eq (U : unitaryGroup (Fin 1) ℂ) :
    ∃ θ : ℝ, U = phaseDiag fun _ => θ := by
  set z := (U : Matrix (Fin 1) (Fin 1) ℂ) 0 0 with hz
  have hn : ‖z‖ = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 U.2) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply, Matrix.one_apply_eq,
      RCLike.star_def, ← hz, Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj,
      Complex.normSq_eq_norm_sq] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  refine ⟨-Complex.arg z, Subtype.ext ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  change z = Matrix.diagonal _ 0 0
  rw [Matrix.diagonal_apply_eq]
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z, hn]
  push_cast
  ring_nf

/-- **Corollary 22(b)**, the paper's (6): every one-mode Gaussian unitary is
`c D(α) S(ζ) R(θ)` with `|c| = 1`. -/
theorem IsGaussianUnitary.exists_eq_oneMode
    {U : unitary (FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1))}
    {S : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ} {d : PhaseIndex 1 → ℝ}
    (hU : IsGaussianUnitary U S d) :
    ∃ (c α ζ : ℂ) (θ : ℝ), ‖c‖ = 1 ∧ (U : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) =
      c • ((displacement (fun _ : Fin 1 => α) : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) *
        squeeze (fun _ : Fin 1 => ζ) * rotation (fun _ : Fin 1 => θ)) := by
  obtain ⟨c, 𝒰, 𝒲, α, r, hr, hc, h⟩ := hU.exists_decomposition
  obtain ⟨θ₁, rfl⟩ := exists_phaseDiag_eq 𝒰
  obtain ⟨θ₂, rfl⟩ := exists_phaseDiag_eq 𝒲
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin 1 → ℂ,
      ζ = fun j => (r j : ℂ) * Complex.exp (-(θ₁ : ℂ) * Complex.I) ^ 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin 1 → ℂ,
      β = ((phaseDiag fun _ : Fin 1 => θ₁ : unitaryGroup (Fin 1) ℂ) :
        Matrix (Fin 1) (Fin 1) ℂ) *ᵥ α := ⟨_, rfl⟩
  have hnorm : ∀ j, ‖ζ j‖ = r j := fun j => by
    rw [hζ, norm_mul, norm_pow, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_pow,
      mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hr j)]
  have hθ : ∀ j, (‖ζ j‖ : ℂ) * Complex.exp (-((fun _ : Fin 1 => θ₁) j : ℂ) * Complex.I) ^ 2 =
      ζ j := fun j => by rw [hnorm, hζ]
  have hR : Star.star (rotation (fun _ : Fin 1 => θ₁) :
      FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) * rotation (fun _ : Fin 1 => θ₁) = 1 :=
    Unitary.star_mul_self_of_mem (rotation _).2
  have hSR : (squeeze ζ : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) *
      rotation (fun _ : Fin 1 => θ₁) =
      (rotation (fun _ : Fin 1 => θ₁) : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) *
        squeeze (fun j => (r j : ℂ)) := by
    rw [squeeze_eq_rotation_mul_squeeze_norm_mul ζ _ hθ, mul_assoc, hR, mul_one]
    simp only [hnorm]
  have hΓ : ∀ θ : Fin 1 → ℝ,
      (secondQuantRep (phaseDiag θ) : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) =
        (rotation θ : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1)) := fun _ => rfl
  have hβ0 : (fun _ : Fin 1 => β 0) = β := funext fun j => by rw [Subsingleton.elim j 0]
  have hζ0 : (fun _ : Fin 1 => ζ 0) = ζ := funext fun j => by rw [Subsingleton.elim j 0]
  have hθ12 : (fun _ : Fin 1 => θ₁ + θ₂) = (fun _ : Fin 1 => θ₁) + fun _ => θ₂ := rfl
  refine ⟨c, β 0, ζ 0, θ₁ + θ₂, hc, ?_⟩
  rw [hβ0, hζ0, h, hθ12, ← rotation_mul, MulMemClass.coe_mul, secondQuantRep_mul_displacement,
    ← hβ, hΓ, hΓ]
  congr 1
  have key : ∀ A B C E F : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1), B * C = E * B →
      A * B * C * F = A * E * (B * F) := fun A B C E F hBC => by
    rw [mul_assoc A B C, hBC, ← mul_assoc A E B, mul_assoc (A * E) B F]
  exact key _ _ _ _ _ hSR.symm

/-! ### Corollary 22(c): the quadratures -/

/-- The quadratures `R̂ = (q̂, p̂)`, positions first: `q̂ⱼ = (aⱼ + aⱼ†)/√2`,
`p̂ⱼ = i(aⱼ† - aⱼ)/√2`. -/
noncomputable def quadrature : PhaseIndex n → Module.End ℂ (FormalFock (Fin n) ℂ)
  | Sum.inl j => ((Real.sqrt 2 : ℂ)⁻¹) • (annihilate j + create j)
  | Sum.inr j => (Complex.I / (Real.sqrt 2 : ℂ)) • (create j - annihilate j)

/-- `V` implements the affine map `R̂ ↦ M R̂ + d` on the quadratures over
`𝒬 = ∩ⱼ dom aⱼ`: it maps `𝒬` into `𝒬`, and `R̂ₖ V ψ = V ((M R̂ + d)ₖ ψ)`. -/
private def ImplementsQuadratures (V : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
    (M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (d : PhaseIndex n → ℝ) : Prop :=
  ∀ ψ : FockSpace (Fin n), (∀ j, ψ ∈ maxDomain (annihilate j)) →
    (∀ j, V ψ ∈ maxDomain (annihilate j)) ∧
      ∀ (k : PhaseIndex n) (χ : FockSpace (Fin n)),
        toFormal χ = (∑ l, (M k l : ℂ) • quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ))
          (toFormal ψ) + (d k : ℂ) • toFormal ψ →
        quadrature k (toFormal (V ψ)) = toFormal (V χ)

/-- **Corollary 22(c)**, the quadratures on `𝒬`: for `ψ ∈ 𝒬 = ∩ⱼ dom aⱼ`, every quadrature
`R̂ₖ ψ` is the formal vector of some `χ ∈ Γ_s`. -/
private theorem exists_toFormal_eq_quadrature {ψ : FockSpace (Fin n)}
    (hψ : ∀ j, ψ ∈ maxDomain (annihilate j)) (k : PhaseIndex n) :
    ∃ χ : FockSpace (Fin n), toFormal χ = quadrature k (toFormal ψ) := by
  have ha : ∀ j, ∃ φ : FockSpace (Fin n), toFormal φ = annihilate j (toFormal ψ) :=
    fun j => ⟨⟨(annihilate j (toFormal ψ)).coeff, hψ j⟩, rfl⟩
  have hc : ∀ j, ∃ φ : FockSpace (Fin n), toFormal φ = create j (toFormal ψ) := fun j => by
    have h := hψ j
    rw [← maxDomain_create] at h
    exact ⟨⟨(create j (toFormal ψ)).coeff, h⟩, rfl⟩
  rcases k with j | j
  · obtain ⟨φ, hφ⟩ := ha j
    obtain ⟨φ', hφ'⟩ := hc j
    exact ⟨((Real.sqrt 2 : ℂ)⁻¹) • (φ + φ'), by
      rw [map_smul, map_add, hφ, hφ', quadrature, LinearMap.smul_apply, LinearMap.add_apply]⟩
  · obtain ⟨φ, hφ⟩ := ha j
    obtain ⟨φ', hφ'⟩ := hc j
    exact ⟨(Complex.I / (Real.sqrt 2 : ℂ)) • (φ' - φ), by
      rw [map_smul, map_sub, hφ, hφ', quadrature, LinearMap.smul_apply, LinearMap.sub_apply]⟩

/-- **Corollary 22(c)**, the vector `χ` of `IsGaussianUnitary.quadrature_apply` exists: for
`ψ ∈ 𝒬 = ∩ⱼ dom aⱼ`, a real matrix `M` and `d`, the formal vector `(M R̂ + d)ₖ ψ` is the formal
vector of some `χ ∈ Γ_s`. -/
theorem exists_toFormal_eq_affine {ψ : FockSpace (Fin n)}
    (hψ : ∀ j, ψ ∈ maxDomain (annihilate j)) (M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (d : PhaseIndex n → ℝ) (k : PhaseIndex n) :
    ∃ χ : FockSpace (Fin n), toFormal χ =
      (∑ l, (M k l : ℂ) • quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ)) (toFormal ψ) +
        (d k : ℂ) • toFormal ψ := by
  choose Q hQ using exists_toFormal_eq_quadrature hψ
  refine ⟨∑ l, (M k l : ℂ) • Q l + (d k : ℂ) • ψ, ?_⟩
  simp only [map_add, map_sum, map_smul, hQ, LinearMap.sum_apply, LinearMap.smul_apply]

/-- `Σₗ aₗ (Σₘ bₗₘ qₘ + cₗ x) + d x = Σₘ (Σₗ aₗ bₗₘ) qₘ + (d + Σₗ aₗ cₗ) x`. -/
private theorem affine_sum_smul {κ E : Type*} [Fintype κ] [AddCommGroup E] [Module ℂ E]
    (a c : κ → ℂ) (b : κ → κ → ℂ) (q : κ → E) (d : ℂ) (x : E) :
    ∑ l, a l • (∑ m, b l m • q m + c l • x) + d • x =
      ∑ m, (∑ l, a l * b l m) • q m + (d + ∑ l, a l * c l) • x := by
  simp only [smul_add, Finset.smul_sum, smul_smul, sum_add_distrib, Finset.sum_smul, add_smul]
  rw [Finset.sum_comm]
  abel

/-- Composition of affine actions on the quadratures. -/
private theorem ImplementsQuadratures.mul {V₁ V₂ : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)}
    {M₁ M₂ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d₁ d₂ : PhaseIndex n → ℝ}
    (h₁ : ImplementsQuadratures V₁ M₁ d₁) (h₂ : ImplementsQuadratures V₂ M₂ d₂) :
    ImplementsQuadratures (V₁ * V₂) (M₁ * M₂) (d₁ + M₁ *ᵥ d₂) := by
  intro ψ hψ
  obtain ⟨hD₂, hQ₂⟩ := h₂ ψ hψ
  obtain ⟨hD₁, hQ₁⟩ := h₁ (V₂ ψ) hD₂
  refine ⟨hD₁, fun k χ hχ => ?_⟩
  choose X hX using exists_toFormal_eq_affine hψ M₂ d₂
  have hR : ∀ l, quadrature l (toFormal (V₂ ψ)) = toFormal (V₂ (X l)) := fun l => hQ₂ l (X l) (hX l)
  have hχ' : toFormal (V₂ (∑ l, (M₁ k l : ℂ) • X l + (d₁ k : ℂ) • ψ)) =
      (∑ l, (M₁ k l : ℂ) • quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ))
        (toFormal (V₂ ψ)) + (d₁ k : ℂ) • toFormal (V₂ ψ) := by
    simp only [map_add, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hR]
  have hXχ : ∑ l, (M₁ k l : ℂ) • X l + (d₁ k : ℂ) • ψ = χ := by
    refine toFormal_injective ?_
    rw [hχ]
    simp only [map_add, map_sum, map_smul, hX, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [affine_sum_smul]
    simp only [Matrix.mul_apply, Pi.add_apply, Matrix.mulVec, dotProduct]
    push_cast
    rfl
  rw [mul_apply_eq_comp, hQ₁ k _ hχ', hXχ, mul_apply_eq_comp]

/-- A phase multiple implements the same affine map. -/
private theorem ImplementsQuadratures.smul {V : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)}
    {M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (h : ImplementsQuadratures V M d) (c : ℂ) : ImplementsQuadratures (c • V) M d := by
  intro ψ hψ
  obtain ⟨hD, hQ⟩ := h ψ hψ
  refine ⟨fun j => (maxDomain (annihilate j)).smul_mem c (hD j), fun k χ hχ => ?_⟩
  rw [_root_.smul_apply, map_smul, map_smul, hQ k χ hχ, _root_.smul_apply, map_smul]

/-- The quadrature relation from the ladder relations: if `aⱼ V ψ = V (Σ ...)` for both ladder
operators, then the quadratures transform by the corresponding real matrix. -/
private theorem quadrature_of_ladder {V : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)}
    {ψ : FockSpace (Fin n)} (A B : Fin n → FockSpace (Fin n))
    (hA : ∀ j, annihilate j (toFormal (V ψ)) = toFormal (V (A j)))
    (hB : ∀ j, create j (toFormal (V ψ)) = toFormal (V (B j))) (k : PhaseIndex n) :
    quadrature k (toFormal (V ψ)) = toFormal (V (match k with
      | Sum.inl j => ((Real.sqrt 2 : ℂ)⁻¹) • (A j + B j)
      | Sum.inr j => (Complex.I / (Real.sqrt 2 : ℂ)) • (B j - A j))) := by
  rcases k with j | j
  · simp only [quadrature, LinearMap.smul_apply, LinearMap.add_apply, hA, hB, map_smul, map_add]
  · simp only [quadrature, LinearMap.smul_apply, LinearMap.sub_apply, hA, hB, map_smul, map_sub]

/-- On `𝒬`, the ladder operators of `ψ` are in `Γ_s`. -/
private theorem exists_ladder {ψ : FockSpace (Fin n)} (hψ : ∀ j, ψ ∈ maxDomain (annihilate j)) :
    (∃ φ : Fin n → FockSpace (Fin n), ∀ j, annihilate j (toFormal ψ) = toFormal (φ j)) ∧
      ∃ φ' : Fin n → FockSpace (Fin n), ∀ j, create j (toFormal ψ) = toFormal (φ' j) := by
  refine ⟨⟨fun j => ⟨(annihilate j (toFormal ψ)).coeff, hψ j⟩, fun j => rfl⟩,
    ⟨fun j => ⟨(create j (toFormal ψ)).coeff, ?_⟩, fun j => rfl⟩⟩
  have h := hψ j
  rw [← maxDomain_create] at h
  exact h

private theorem sqrt_two_inv_mul_sqrt_two : ((Real.sqrt 2 : ℂ))⁻¹ * 2 = Real.sqrt 2 := by
  rw [← sqrt_two_mul_self, ← mul_assoc, inv_mul_cancel₀ sqrt_two_ne_zero, one_mul]

/-- The quadrature `q̂ⱼ = (aⱼ + aⱼ†)/√2`. -/
private theorem quadrature_inl (j : Fin n) (x : FormalFock (Fin n) ℂ) :
    quadrature (Sum.inl j) x = ((Real.sqrt 2 : ℂ))⁻¹ • (annihilate j x + create j x) := rfl

/-- The quadrature `p̂ⱼ = i(aⱼ† - aⱼ)/√2`. -/
private theorem quadrature_inr (j : Fin n) (x : FormalFock (Fin n) ℂ) :
    quadrature (Sum.inr j) x = (Complex.I / (Real.sqrt 2 : ℂ)) • (create j x - annihilate j x) :=
  rfl

/-- The row `k` of a real matrix applied to the quadratures, split into positions and momenta. -/
private theorem sum_smul_quadrature_apply (M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (k : PhaseIndex n) (x : FormalFock (Fin n) ℂ) :
    (∑ l, (M k l : ℂ) • quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ)) x =
      ∑ m, ((M k (Sum.inl m) : ℂ) • quadrature (Sum.inl m) x +
        (M k (Sum.inr m) : ℂ) • quadrature (Sum.inr m) x) := by
  rw [LinearMap.sum_apply, Fintype.sum_sum_type, ← sum_add_distrib]
  rfl

/-- **Corollary 22(c)** for `D(α)`: `R̂ D(α) ψ = D(α)(R̂ + δ(α))ψ` on `𝒬`, the paper's
(A31)–(A33). -/
private theorem implementsQuadratures_displacement (α : Fin n → ℂ) :
    ImplementsQuadratures (displacement α : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) 1
      (phaseOfComplex α) := by
  intro ψ hψ
  refine ⟨fun j => (displacement_mem_maxDomain_iff α j ψ).2 (hψ j), fun k χ hχ => ?_⟩
  obtain ⟨⟨φ, hφ⟩, ⟨φ', hφ'⟩⟩ := exists_ladder hψ
  have hA : ∀ j, annihilate j (toFormal ((displacement α : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((displacement α : FockSpace (Fin n) →L[ℂ] _) (φ j + α j • ψ)) := fun j => by
    rw [annihilate_displacement α j (hφ j), map_add, map_smul, map_add, map_smul]
  have hB : ∀ j, create j (toFormal ((displacement α : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((displacement α : FockSpace (Fin n) →L[ℂ] _) (φ' j + conj (α j) • ψ)) :=
    fun j => by rw [create_displacement α j (hφ' j), map_add, map_smul, map_add, map_smul]
  rw [quadrature_of_ladder _ _ hA hB k]
  congr 2
  refine toFormal_injective ?_
  have hone : (∑ l, ((1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) k l : ℂ) • quadrature l :
      Module.End ℂ (FormalFock (Fin n) ℂ)) (toFormal ψ) = quadrature k (toFormal ψ) := by
    rw [LinearMap.sum_apply, sum_eq_single k (fun l _ hl => by
      rw [Matrix.one_apply_ne (Ne.symm hl), Complex.ofReal_zero, zero_smul,
        LinearMap.zero_apply]) (by simp)]
    rw [Matrix.one_apply_eq, Complex.ofReal_one, one_smul]
  rw [hχ, hone]
  rcases k with j | j
  · have e : ((Real.sqrt 2 : ℂ))⁻¹ * (α j + conj (α j)) = ((Real.sqrt 2 * (α j).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      linear_combination ((α j).re : ℂ) * sqrt_two_inv_mul_sqrt_two
    rw [quadrature_inl, hφ, hφ']
    simp only [map_smul, map_add, phaseOfComplex, Sum.elim_inl]
    linear_combination (norm := module) e • toFormal ψ
  · have e : Complex.I / (Real.sqrt 2 : ℂ) * (conj (α j) - α j) =
        ((Real.sqrt 2 * (α j).im : ℝ) : ℂ) := by
      rw [← neg_sub, Complex.sub_conj]
      push_cast
      linear_combination (-2 * ((α j).im : ℂ) * ((Real.sqrt 2 : ℂ))⁻¹) * Complex.I_sq +
        ((α j).im : ℂ) * sqrt_two_inv_mul_sqrt_two
    rw [quadrature_inr, hφ, hφ']
    simp only [map_smul, map_add, map_sub, phaseOfComplex, Sum.elim_inr]
    linear_combination (norm := module) e • toFormal ψ

/-- `aⱼ† Γ(𝒰) = Γ(𝒰) Σₖ conj(𝒰ⱼₖ) aₖ†`. -/
private theorem create_mul_secondQuant (U : unitaryGroup (Fin n) ℂ) (j : Fin n) :
    create j * secondQuant (U : Matrix (Fin n) (Fin n) ℂ) =
      secondQuant (U : Matrix (Fin n) (Fin n) ℂ) *
        ∑ k, conj ((U : Matrix (Fin n) (Fin n) ℂ) j k) • create k := by
  rw [← secondQuant_conjTranspose_mul_create_mul, ← mul_assoc, ← mul_assoc,
    secondQuant_mul_conjTranspose_self, one_mul]

/-- **Corollary 22(c)** for `Γ(𝒰)`: `R̂ Γ(𝒰) ψ = Γ(𝒰) O_𝒰 R̂ ψ` on `𝒬`, the paper's (A17)–(A19). -/
private theorem implementsQuadratures_secondQuantRep (U : unitaryGroup (Fin n) ℂ) :
    ImplementsQuadratures (secondQuantRep U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
      (orthogonalSymplecticOfUnitary U) 0 := by
  intro ψ hψ
  obtain ⟨⟨φ, hφ⟩, ⟨φ', hφ'⟩⟩ := exists_ladder hψ
  have hΓ : ∀ x : FockSpace (Fin n),
      toFormal ((secondQuantRep U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) x) =
        secondQuant (U : Matrix (Fin n) (Fin n) ℂ) (toFormal x) := fun x => by
    rw [secondQuantRep_apply, toFormal_secondQuantUnitary]
  have hA : ∀ j, annihilate j (toFormal ((secondQuantRep U : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((secondQuantRep U : FockSpace (Fin n) →L[ℂ] _)
        (∑ k, (U : Matrix (Fin n) (Fin n) ℂ) j k • φ k)) := fun j => by
    rw [hΓ, hΓ, ← Module.End.mul_apply, annihilate_mul_secondQuant, Module.End.mul_apply,
      LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hφ, map_sum, map_smul]
  have hB : ∀ j, create j (toFormal ((secondQuantRep U : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((secondQuantRep U : FockSpace (Fin n) →L[ℂ] _)
        (∑ k, conj ((U : Matrix (Fin n) (Fin n) ℂ) j k) • φ' k)) := fun j => by
    rw [hΓ, hΓ, ← Module.End.mul_apply, create_mul_secondQuant, Module.End.mul_apply,
      LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hφ', map_sum, map_smul]
  refine ⟨fun j => ?_, fun k χ hχ => ?_⟩
  · change Memℓp (annihilate j (toFormal _)).coeff 2
    rw [hA, show ∀ x : FockSpace (Fin n), (toFormal x).coeff = ⇑x from fun _ => rfl]
    exact lp.memℓp _
  rw [quadrature_of_ladder _ _ hA hB k]
  congr 2
  refine toFormal_injective ?_
  rw [hχ, sum_smul_quadrature_apply, Pi.zero_apply, Complex.ofReal_zero, zero_smul, add_zero]
  rcases k with j | j
  · simp only [orthogonalSymplecticOfUnitary, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      Matrix.map_apply, Matrix.neg_apply, quadrature_inl, quadrature_inr, hφ, hφ', map_smul,
      map_add, map_sum, smul_add, Finset.smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    set u := (U : Matrix (Fin n) (Fin n) ℂ) j k with hu
    have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
    conv_lhs => rw [hu']
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    module
  · simp only [orthogonalSymplecticOfUnitary, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.map_apply, quadrature_inl, quadrature_inr, hφ, hφ', map_smul, map_sub, map_sum,
      smul_sub, Finset.smul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    set u := (U : Matrix (Fin n) (Fin n) ℂ) j k with hu
    have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
    conv_lhs => rw [hu']
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (norm := module)
      (-((u.im : ℂ) * ((Real.sqrt 2 : ℂ))⁻¹) * Complex.I_sq) • (toFormal (φ' k) + toFormal (φ k))

/-- **Corollary 22(c)** for `S(ζ)`: `R̂ S(ζ) ψ = S(ζ) M_ζ R̂ ψ` on `𝒬`. -/
private theorem implementsQuadratures_squeeze (ζ : Fin n → ℂ) :
    ImplementsQuadratures (squeeze ζ : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
      (squeezeSymplectic ζ) 0 := by
  intro ψ hψ
  refine ⟨fun j => (squeeze_mem_maxDomain_iff ζ j ψ).2 (hψ j), fun k χ hχ => ?_⟩
  obtain ⟨⟨φ, hφ⟩, ⟨φ', hφ'⟩⟩ := exists_ladder hψ
  have hA : ∀ j, annihilate j (toFormal ((squeeze ζ : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((squeeze ζ : FockSpace (Fin n) →L[ℂ] _)
        ((Real.cosh ‖ζ j‖ : ℂ) • φ j -
          ((if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ)) • φ' j)) := fun j =>
    annihilate_squeeze ζ j (hφ j) (hφ' j)
  have hB : ∀ j, create j (toFormal ((squeeze ζ : FockSpace (Fin n) →L[ℂ] _) ψ)) =
      toFormal ((squeeze ζ : FockSpace (Fin n) →L[ℂ] _)
        ((Real.cosh ‖ζ j‖ : ℂ) • φ' j -
          conj ((if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) *
            (Real.sinh ‖ζ j‖ : ℂ)) • φ j)) := fun j =>
    create_squeeze ζ j (hφ j) (hφ' j)
  rw [quadrature_of_ladder _ _ hA hB k]
  congr 2
  refine toFormal_injective ?_
  rw [hχ, sum_smul_quadrature_apply, Pi.zero_apply, Complex.ofReal_zero, zero_smul, add_zero]
  -- `e^{iφ} sinh r = x + iy` with real `x, y`
  have hs : ∀ j, ((if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ)) =
      (((if ζ j = 0 then 0 else (ζ j).re / ‖ζ j‖) * Real.sinh ‖ζ j‖ : ℝ) : ℂ) +
        (((if ζ j = 0 then 0 else (ζ j).im / ‖ζ j‖) * Real.sinh ‖ζ j‖ : ℝ) : ℂ) * Complex.I :=
    fun j => by
      split_ifs with h
      · simp
      · rw [show ζ j / (‖ζ j‖ : ℂ) = (((ζ j).re : ℂ) + ((ζ j).im : ℂ) * Complex.I) / ‖ζ j‖ by
          rw [Complex.re_add_im]]
        push_cast
        ring
  rcases k with j | j
  · rw [sum_eq_single j (fun m _ hm => by
      simp [squeezeSymplectic, Matrix.diagonal_apply_ne _ (Ne.symm hm)]) (by simp)]
    simp only [squeezeSymplectic, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.diagonal_apply_eq,
      quadrature_inl, quadrature_inr, hφ, hφ', map_smul, map_add, map_sub, hs, map_mul,
      Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_neg]
    module
  · rw [sum_eq_single j (fun m _ hm => by
      simp [squeezeSymplectic, Matrix.diagonal_apply_ne _ (Ne.symm hm)]) (by simp)]
    simp only [squeezeSymplectic, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.diagonal_apply_eq,
      quadrature_inl, quadrature_inr, hφ, hφ', map_smul, map_add, map_sub, hs, map_mul,
      Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_neg]
    linear_combination (norm := module)
      (((((if ζ j = 0 then 0 else (ζ j).im / ‖ζ j‖) : ℝ) : ℂ) * (Real.sinh ‖ζ j‖ : ℂ) *
        ((Real.sqrt 2 : ℂ))⁻¹) * Complex.I_sq) • (toFormal (φ' j) + toFormal (φ j))

/-- A Gaussian unitary with data `(S, d)` implements `R̂ ↦ S R̂ + d` on `𝒬`: by the
Bloch–Messiah decomposition of Theorem 21(a) and the generators above. -/
private theorem IsGaussianUnitary.implementsQuadratures
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) :
    ImplementsQuadratures (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) S d := by
  obtain ⟨OU, hOU, OW, hOW, r, -, hS⟩ := exists_blochMessiah hU.1
  obtain ⟨𝒰, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOU
  obtain ⟨𝒲, rfl⟩ := mem_orthogonalSymplectic_iff.1 hOW
  obtain ⟨c, -, hc⟩ := hU.eq_of_blochMessiah 𝒰 𝒲 r hS
  have hI := ((((implementsQuadratures_secondQuantRep 𝒰).mul
    (implementsQuadratures_displacement
      (complexOfPhase ((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d)))).mul
    (implementsQuadratures_squeeze fun j => (r j : ℂ))).mul
    (implementsQuadratures_secondQuantRep 𝒲)).smul c
  have hO : orthogonalSymplecticOfUnitary 𝒰 * (orthogonalSymplecticOfUnitary 𝒰)ᵀ = 1 := by
    rw [← orthogonalSymplecticOfUnitary_star, ← orthogonalSymplecticOfUnitary_mul,
      Unitary.mul_star_self, orthogonalSymplecticOfUnitary_one]
  rw [Matrix.mul_one, squeezeSymplectic_ofReal, ← hS, phaseOfComplex_complexOfPhase,
    Matrix.mulVec_mulVec, hO, Matrix.one_mulVec] at hI
  simp only [zero_add, Matrix.mulVec_zero, add_zero] at hI
  rw [hc]
  exact hI

/-- **Corollary 22(c)**: for a Gaussian unitary with data `(S, d)`, `R̂ₖ U ψ = U ((S R̂ + d)ₖ ψ)`
on `𝒬 = ∩ⱼ dom aⱼ`: Gaussian unitaries in the sense of Definition 18 satisfy the paper's (A3),
`U†R̂U = SR̂ + d`, on `𝒬`, which `U` maps onto itself (`apply_mem_maxDomain_iff`); the vector `χ`
exists by `exists_toFormal_eq_affine`. -/
theorem IsGaussianUnitary.quadrature_apply
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) {ψ χ : FockSpace (Fin n)}
    (hψ : ∀ j, ψ ∈ maxDomain (annihilate j)) (k : PhaseIndex n)
    (hχ : toFormal χ = (∑ l, (S k l : ℂ) • quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ))
      (toFormal ψ) + (d k : ℂ) • toFormal ψ) :
    quadrature k (toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ)) =
      toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) χ) :=
  (hU.implementsQuadratures ψ hψ).2 k χ hχ

/-- **Corollary 22(c)**, the domain: a Gaussian unitary maps `𝒬 = ∩ⱼ dom aⱼ` onto itself,
`Uψ ∈ 𝒬 ↔ ψ ∈ 𝒬`. -/
theorem IsGaussianUnitary.apply_mem_maxDomain_iff
    {U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {d : PhaseIndex n → ℝ}
    (hU : IsGaussianUnitary U S d) {ψ : FockSpace (Fin n)} :
    (∀ j, (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ ∈ maxDomain (annihilate j)) ↔
      ∀ j, ψ ∈ maxDomain (annihilate j) := by
  refine ⟨fun h => ?_, fun h => (hU.implementsQuadratures ψ h).1⟩
  have h1 : Star.star (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * U = 1 :=
    Unitary.star_mul_self_of_mem U.2
  have h2 := (hU.star.implementsQuadratures _ h).1
  rwa [Unitary.coe_star, ← mul_apply_eq_comp, h1, one_apply_eq_self] at h2

end FockSpace

end BosonicLean.Fock
