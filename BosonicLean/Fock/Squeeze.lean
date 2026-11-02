/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Displacement
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Squeezing and rotation operators on the bosonic Fock space

For `ζ ∈ ℂ^ι` write `ζⱼ = rⱼ e^{iφⱼ}`, `cⱼ = cosh rⱼ`, `sⱼ = sinh rⱼ` and `τⱼ = e^{iφⱼ} tanh rⱼ`
(`τⱼ = 0` at `ζⱼ = 0`), the paper's (C16); `|τⱼ| < 1`. The squeezing operator `S(ζ)` acts on
`ψ ∈ Γ_s(ι)` by its normal-ordered form
`S(ζ)ψ = (Πⱼ cⱼ)^{-1/2} e^{-½ Σⱼ τⱼ aⱼ†²} Γ(diag(cⱼ⁻¹)) e^{½ Σⱼ τ̄ⱼ aⱼ²} ψ`,
with the lowering exponential summed coefficient by coefficient (it converges absolutely because
`|τⱼ| < 1`) and the raising exponential a finite sum at each coefficient. On an exponential vector
it gives a product of one-mode Gaussian vectors, whose inner products Mehler's formula computes; so
`S(ζ)` is an isometry. It is covariant under displacements, `S(ζ) D(β) = D(L_ζ β) S(ζ)` with
`(L_ζ β)ⱼ = cⱼ βⱼ - e^{iφⱼ} sⱼ β̄ⱼ`, and the irreducibility of the Fock representation then makes it
unitary with `S(ζ)* = S(-ζ)`. The rotation `R(θ)` is the second quantization of `diag(e^{-iθⱼ})`.

The same irreducibility argument, with the vacuum expectation values of Mehler's formula, gives the
product over the modes, the one-parameter groups along rays and the absorption of the squeezing
phases into rotations; a coefficientwise computation gives the intertwining with the ladder
operators, and the derivative of the ordered form on number states gives the generator.

## Main definitions

* `BosonicLean.Fock.tanhPhase ζ`: `τ = ζ tanh|ζ|/|ζ|`.
* `BosonicLean.Fock.FormalFock.orderedSqueeze ζ`: the normal-ordered form, coefficientwise.
* `BosonicLean.Fock.FockSpace.squeeze ζ`: the squeezing operator `S(ζ)`, a unitary of `Γ_s(ι)`.
* `BosonicLean.Fock.FockSpace.phaseDiag θ`, `BosonicLean.Fock.FockSpace.rotation θ`: `R(θ)`.
* `BosonicLean.Fock.FockSpace.gaussianUnitary α ζ θ`: the single-mode Gaussian unitary
  `U_G = D(α) S(ζ) R(θ)` of Tjoa–Cirac, (6).

## Main results

* `FockSpace.squeeze_matrixElement`, `rotation_matrixElement`: Lemma 14.
* `FockSpace.squeeze_expVec`, `squeeze_vacuum`, `squeeze_mul_displacement`, `star_squeeze`,
  `squeeze_zero`, `squeeze_eq_prod`, `squeeze_single_apply`: Theorem 15; the isometry of 15(b) is
  that of the unitary `S(ζ)`.
* `FockSpace.annihilate_squeeze`, `create_squeeze`, `maxDomain_create`,
  `squeeze_mem_maxDomain_iff`: Theorem 16.
* `FockSpace.squeeze_smul_mul`, `continuous_squeeze_apply`, `hasDerivAt_squeeze_smul`:
  Theorem 17.
* `FockSpace.star_secondQuantRep_mul_displacement_mul`, `secondQuantRep_mul_displacement`:
  Theorem 20(b), the paper's (30).
* `FockSpace.squeeze_eq_rotation_mul_squeeze_norm_mul`, `squeeze_eq_conj`: Theorem 21(c), phase
  absorption.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), (5), (C16), (C17).
* A. Perelomov, *Generalized Coherent States and Their Applications*, Springer (1986).
-/

open scoped InnerProductSpace ComplexConjugate ENNReal
open Finset

namespace BosonicLean.Fock

/-! ### The parameters `τ = e^{iφ} tanh r` and `e^{iφ} sinh r` -/

/-- `τ(ζ) = ζ tanh|ζ|/|ζ|` (`0` at `ζ = 0`): `e^{iφ} tanh r` for `ζ = r e^{iφ}`, the paper's `τ` of
(C16). -/
noncomputable def tanhPhase (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0 else ζ * ((Real.tanh ‖ζ‖ / ‖ζ‖ : ℝ) : ℂ)

/-- `e^{iφ} sinh r` for `ζ = r e^{iφ}` (`0` at `ζ = 0`); an abbreviation inside this file, the
statements write it out as `squeezeMap` does. -/
private noncomputable def sinhPhase (ζ : ℂ) : ℂ :=
  (if ζ = 0 then 0 else ζ / (‖ζ‖ : ℂ)) * (Real.sinh ‖ζ‖ : ℂ)

/-- `e^{iφ} tanh r = e^{iφ} sinh r / cosh r`. -/
private theorem tanhPhase_eq_sinhPhase_div (ζ : ℂ) :
    tanhPhase ζ = sinhPhase ζ / (Real.cosh ‖ζ‖ : ℂ) := by
  rw [tanhPhase, sinhPhase]
  split_ifs with h
  · simp
  · have h1 : (‖ζ‖ : ℂ) ≠ 0 := by simpa using h
    have h2 : (Real.cosh ‖ζ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    push_cast
    field_simp

/-- `|e^{iφ} sinh r|² = sinh² r`. -/
private theorem conj_sinhPhase_mul_self (ζ : ℂ) :
    conj (sinhPhase ζ) * sinhPhase ζ = ((Real.sinh ‖ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [sinhPhase]
  split_ifs with h
  · simp [h]
  · have h1 : (‖ζ‖ : ℂ) ≠ 0 := by simpa using h
    rw [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
    have h2 : conj ζ * ζ = (‖ζ‖ : ℂ) ^ 2 := Complex.conj_mul' ζ
    push_cast
    field_simp
    rw [mul_comm (conj ζ), ← h2]
    ring

/-- `cosh² r - |e^{iφ} sinh r|² = 1`. -/
private theorem cosh_sq_sub_conj_sinhPhase_mul_self (ζ : ℂ) :
    (Real.cosh ‖ζ‖ : ℂ) ^ 2 - conj (sinhPhase ζ) * sinhPhase ζ = 1 := by
  rw [conj_sinhPhase_mul_self, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    Real.cosh_sq_sub_sinh_sq, Complex.ofReal_one]

/-- `|τ(ζ)| = tanh |ζ|`. -/
theorem norm_tanhPhase (ζ : ℂ) : ‖tanhPhase ζ‖ = Real.tanh ‖ζ‖ := by
  rw [tanhPhase]
  split_ifs with h
  · simp [h]
  · have ht : 0 ≤ Real.tanh ‖ζ‖ := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.2 (norm_nonneg _)) (Real.cosh_pos _).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ht (norm_nonneg _))]
    field_simp [norm_ne_zero_iff.2 h]

/-- `|τ| < 1`. -/
theorem norm_tanhPhase_lt_one (ζ : ℂ) : ‖tanhPhase ζ‖ < 1 := by
  rw [norm_tanhPhase]
  exact Real.tanh_lt_one _

/-- `τ(-ζ) = -τ(ζ)`. -/
theorem tanhPhase_neg (ζ : ℂ) : tanhPhase (-ζ) = -tanhPhase ζ := by
  by_cases h : ζ = 0
  · simp [tanhPhase, h]
  · have h' : -ζ ≠ 0 := neg_ne_zero.2 h
    simp only [tanhPhase, h, h', ↓reduceIte, norm_neg, neg_mul]

/-- `e^{iφ} sinh r` is odd in `ζ`. -/
private theorem sinhPhase_neg (ζ : ℂ) : sinhPhase (-ζ) = -sinhPhase ζ := by
  by_cases h : ζ = 0
  · simp [sinhPhase, h]
  · have h' : -ζ ≠ 0 := neg_ne_zero.2 h
    simp only [sinhPhase, h, h', ↓reduceIte, norm_neg, neg_div, neg_mul]

/-- `τ(0) = 0`. -/
theorem tanhPhase_zero : tanhPhase 0 = 0 := by simp [tanhPhase]

/-- `1 - |τ|² = 1/cosh² r`. -/
theorem one_sub_normSq_tanhPhase (ζ : ℂ) :
    1 - ‖tanhPhase ζ‖ ^ 2 = (Real.cosh ‖ζ‖ ^ 2)⁻¹ := by
  rw [norm_tanhPhase, Real.tanh_eq_sinh_div_cosh, div_pow]
  have h := Real.cosh_sq_sub_sinh_sq ‖ζ‖
  have h0 : Real.cosh ‖ζ‖ ^ 2 ≠ 0 := by positivity
  field_simp
  linarith

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Definition 13: the ordered form of `S(ζ)` -/

/-- The diagonal matrix `diag(1/cosh|ζⱼ|)`; its second quantization multiplies the coefficient at
`n` by `Πⱼ cⱼ^{-nⱼ}`. -/
noncomputable def coshInvDiag (ζ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun j => (((Real.cosh ‖ζ j‖)⁻¹ : ℝ) : ℂ)

/-- **Definition 13.** The normal-ordered form
`(Πⱼ cⱼ)^{-1/2} e^{-½ Σⱼ τⱼ aⱼ†²} Γ(diag(cⱼ⁻¹)) e^{½ Σⱼ τ̄ⱼ aⱼ²} ψ` of the squeezing operator,
coefficientwise. -/
noncomputable def orderedSqueeze (ζ : ι → ℂ) (ψ : FormalFock ι ℂ) : FormalFock ι ℂ :=
  (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
    (raiseSqueeze fun j => tanhPhase (ζ j)).exp
      (secondQuant (coshInvDiag ζ) (coeffExp (lowerSqueeze fun j => tanhPhase (ζ j)) ψ))

omit [DecidableEq ι] in
/-- `½ Σⱼ τ̄ⱼ aⱼ² ε(z) = (½ Σⱼ τ̄ⱼ zⱼ²) ε(z)`. -/
theorem lowerSqueeze_expVecFormal (τ z : ι → ℂ) :
    lowerSqueeze τ (expVecFormal z) = (∑ j, conj (τ j) / 2 * z j ^ 2) • expVecFormal z := by
  simp only [lowerSqueeze, LinearMap.sum_apply, LinearMap.smul_apply, pow_two,
    Module.End.mul_apply, annihilate_expVecFormal, map_smul, smul_smul, Finset.sum_smul]

omit [DecidableEq ι] in
/-- `e^{½ Σⱼ τ̄ⱼ aⱼ²} ε(z) = e^{½ Σⱼ τ̄ⱼ zⱼ²} ε(z)`. -/
theorem coeffExp_lowerSqueeze_expVecFormal (τ z : ι → ℂ) :
    coeffExp (lowerSqueeze τ) (expVecFormal z) =
      Complex.exp (∑ j, conj (τ j) / 2 * z j ^ 2) • expVecFormal z := by
  set c : ℂ := ∑ j, conj (τ j) / 2 * z j ^ 2
  have hpow : ∀ r : ℕ, (lowerSqueeze τ ^ r) (expVecFormal z) = c ^ r • expVecFormal z := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, lowerSqueeze_expVecFormal, smul_smul,
        pow_succ', mul_comm]
  ext n
  rw [coeff_coeffExp, coeff_smul, smul_eq_mul, Complex.exp_eq_exp_ℂ,
    ← ((NormedSpace.expSeries_div_hasSum_exp c).mul_right ((expVecFormal z).coeff n)).tsum_eq]
  refine tsum_congr fun r => ?_
  rw [hpow, coeff_smul, smul_eq_mul, div_eq_inv_mul]
  ring

omit [DecidableEq ι] in
/-- `e^{-½ Σⱼ τⱼ aⱼ†²} ε(w) = ⊗ⱼ g(-τⱼ/2, wⱼ)`, a product of one-mode Gaussian vectors. -/
theorem raiseSqueeze_exp_expVecFormal (τ w : ι → ℂ) :
    (raiseSqueeze τ).exp (expVecFormal w) =
      tensorVec fun j => gaussVec (-τ j / 2) (w j) := by
  classical
  rw [expVecFormal_eq_tensorVec, raiseSqueeze, gaussRaise_exp_tensorVec]
  congr 1
  funext j
  rw [← gaussVec_zero_left, ← gaussExp_vacuum, ← Module.End.mul_apply, gaussExp_mul_gaussExp,
    gaussExp_vacuum, add_zero, Pi.zero_apply, zero_add]

/-- **Theorem 15(a), coefficientwise.** The ordered form on an exponential vector:
`(Πⱼ cⱼ)^{-1/2} e^{½ Σⱼ τ̄ⱼ zⱼ²} ⊗ⱼ g(-τⱼ/2, zⱼ/cⱼ)`. -/
theorem orderedSqueeze_expVecFormal (ζ z : ι → ℂ) :
    orderedSqueeze ζ (expVecFormal z) =
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (∑ j, conj (tanhPhase (ζ j)) * z j ^ 2 / 2)) •
        tensorVec fun j => gaussVec (-tanhPhase (ζ j) / 2) (z j / (Real.cosh ‖ζ j‖ : ℂ)) := by
  rw [orderedSqueeze, coeffExp_lowerSqueeze_expVecFormal, map_smul, secondQuant_expVecFormal,
    map_smul, raiseSqueeze_exp_expVecFormal, smul_smul]
  congr 2
  · congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · funext j
    rw [coshInvDiag, Matrix.mulVec_diagonal]
    push_cast
    simp only [div_eq_inv_mul]

end FormalFock

/-! ### Mehler's formula for one mode -/

namespace FormalFock

/-- For `|κ| < 1/2`, the one-mode Gaussian vector `g(κ, ℓ) = e^{κ a†² + ℓ a†}∣0⟩` is
square-summable. -/
theorem summable_sq_coeff_gaussVec {κ : ℂ} (hκ : ‖κ‖ < 1 / 2) (ℓ : ℂ) :
    Summable fun m : ℕ => ‖(gaussVec κ ℓ).coeff (Finsupp.single () m)‖ ^ 2 := by
  refine (hasSum_factorial_mul_normSq_cMatrix κ ℓ hκ).summable.congr fun m => ?_
  rw [coeff_gaussVec, norm_mul, mul_pow, sqrtC, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _), Complex.normSq_eq_norm_sq]

/-- **Mehler's formula for one mode**: the overlap of two Gaussian vectors,
`⟨g(κ, ℓ), g(κ', ℓ')⟩ = 𝒮(κ̄κ') exp(Δ (κ' ℓ̄² + ℓ̄ ℓ' + κ̄ ℓ'²))` with `Δ = (1 - 4κ̄κ')⁻¹` and
`𝒮` the binomial series of `(1 - 4X)^{-1/2}`, for `|κ| + |κ'| < 1`; the series converges absolutely.
This is `BosonicLean.pairingSeries_eq` with the arguments `(ℓ̄, κ̄, κ', ℓ')`. -/
theorem hasSum_conj_mul_coeff_gaussVec {κ κ' : ℂ} (h : ‖κ‖ + ‖κ'‖ < 1) (ℓ ℓ' : ℂ) :
    HasSum (fun m : ℕ => conj ((gaussVec κ ℓ).coeff (Finsupp.single () m)) *
        (gaussVec κ' ℓ').coeff (Finsupp.single () m))
      (centralBinomSeries (conj κ * κ') * NormedSpace.exp
        (Ring.inverse (1 - (4 : ℂ) • (conj κ * κ')) *
          (κ' * conj ℓ ^ 2 + ℓ' * conj ℓ + conj κ * ℓ' ^ 2))) := by
  have hb : ∀ x : ℂ, HasPowerBound x 1 ‖x‖ := fun x m => by simp [norm_pow]
  have hS := (summable_norm_pairingSeries (A := ℂ) (by simp) (hb (conj κ)) (hb κ')
    (norm_nonneg _) (norm_nonneg _) (by simpa using h) (conj ℓ) ℓ').of_norm.hasSum
  rw [← pairingSeries, pairingSeries_eq (by simp) (Commute.all _ _) (Commute.all _ _)
    (Commute.all _ _) (Commute.all _ _) (Commute.all _ _) (Commute.all _ _) (hb _) (hb _)
    (norm_nonneg _) (norm_nonneg _) (by simpa using h)] at hS
  convert hS using 2 with m
  rw [coeff_gaussVec, coeff_gaussVec, map_mul, conj_cMatrix, sqrtC, Complex.conj_ofReal,
    ← sqrtC, smul_eq_mul]
  have := sqrtC_mul_self m.factorial
  rw [← this]
  ring

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-mode factor of `S(ζ)ε(z)` and its overlaps (Mehler's formula with `κ = κ' = -τ/2`):
`⟨g(-τ/2, w/c), g(-τ/2, z/c)⟩ = c e^{-τ w̄²/2 + w̄ z - τ̄ z²/2}`. -/
private theorem tsum_overlap_squeezed (ζ w z : ℂ) :
    ∑' m : ℕ, conj ((gaussVec (-tanhPhase ζ / 2) (w / (Real.cosh ‖ζ‖ : ℂ))).coeff
        (Finsupp.single () m)) *
      (gaussVec (-tanhPhase ζ / 2) (z / (Real.cosh ‖ζ‖ : ℂ))).coeff (Finsupp.single () m) =
      (Real.cosh ‖ζ‖ : ℂ) *
        Complex.exp (-tanhPhase ζ * conj w ^ 2 / 2 + conj w * z -
          conj (tanhPhase ζ) * z ^ 2 / 2) := by
  set τ := tanhPhase ζ
  set c : ℝ := Real.cosh ‖ζ‖
  have hc : 0 < c := Real.cosh_pos _
  have hτ := norm_tanhPhase_lt_one ζ
  have hκ : ‖-τ / 2‖ + ‖-τ / 2‖ < 1 := by
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith
  rw [(hasSum_conj_mul_coeff_gaussVec hκ _ _).tsum_eq]
  -- the binomial series at `|τ|²/4`
  have hττ : conj (-τ / 2) * (-τ / 2) = ((‖τ‖ ^ 2 / 4 : ℝ) : ℂ) := by
    rw [map_div₀, map_neg, map_ofNat]
    have := Complex.conj_mul' τ
    push_cast
    linear_combination this / 4
  have h1 : 1 - ‖τ‖ ^ 2 = (c ^ 2)⁻¹ := one_sub_normSq_tanhPhase ζ
  have hS : centralBinomSeries (conj (-τ / 2) * (-τ / 2)) = (c : ℂ) := by
    rw [hττ, centralBinomSeries_ofReal_of_abs_lt (by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖τ‖ ^ 2 / 4)]
      nlinarith [norm_nonneg τ])]
    congr 1
    rw [show 1 - 4 * (‖τ‖ ^ 2 / 4) = 1 - ‖τ‖ ^ 2 by ring, h1, Real.inv_rpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num [Real.rpow_neg_one]
  have hI : Ring.inverse (1 - (4 : ℂ) • (conj (-τ / 2) * (-τ / 2))) = (c : ℂ) ^ 2 := by
    rw [hττ, Ring.inverse_eq_inv', smul_eq_mul]
    push_cast
    rw [show (1 : ℂ) - 4 * ((‖τ‖ : ℂ) ^ 2 / 4) = ((1 - ‖τ‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, h1]
    push_cast
    rw [inv_inv]
  rw [hS, hI, ← Complex.exp_eq_exp_ℂ]
  congr 2
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  rw [map_div₀, map_div₀, Complex.conj_ofReal, map_neg, map_ofNat]
  field_simp
  ring

end FockSpace

/-! ### Theorem 15(a), (b): `S(ζ)` on exponential vectors, isometry -/

namespace FormalFock

/-- A one-mode vector with square-summable coefficients has finite squared norm. -/
private theorem sqNorm_lt_top_of_summable_unit {φ : FormalFock Unit ℂ}
    (h : Summable fun m : ℕ => ‖φ.coeff (Finsupp.single () m)‖ ^ 2) : sqNorm φ < ∞ := by
  rw [sqNorm_lt_top_iff, ← (Finsupp.uniqueEquiv ()).symm.summable_iff]
  exact h

/-- The binomial series at `0` is `1`. -/
theorem centralBinomSeries_zero : centralBinomSeries (0 : ℂ) = 1 := by
  rw [centralBinomSeries, tsum_eq_single 0 fun i hi => by simp [zero_pow hi]]
  simp

/-- One mode: `⟨ε(w), g(κ, ℓ)⟩ = e^{κ w̄² + ℓ w̄}`, the generating function of the `Cₘ(κ, ℓ)`. -/
theorem hasSum_conj_mul_coeff_expVecFormal_gaussVec {κ : ℂ} (hκ : ‖κ‖ < 1) (w ℓ : ℂ) :
    HasSum (fun m : ℕ => conj ((expVecFormal fun _ : Unit => w).coeff (Finsupp.single () m)) *
        (gaussVec κ ℓ).coeff (Finsupp.single () m))
      (Complex.exp (κ * conj w ^ 2 + ℓ * conj w)) := by
  rw [← gaussVec_zero_left]
  convert hasSum_conj_mul_coeff_gaussVec (κ := 0) (κ' := κ) (by simpa using hκ) w ℓ using 1
  rw [map_zero, zero_mul, centralBinomSeries_zero, smul_zero, sub_zero, Ring.inverse_one,
    one_mul, one_mul, ← Complex.exp_eq_exp_ℂ, zero_mul, add_zero]

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The inner-product representation of the lowering exponential of `S(ζ)` (Lemma 5(b)). -/
private theorem exists_inner_coeffExp_lowerSqueeze (ζ : ι → ℂ) (n : ι →₀ ℕ) :
    ∃ χ : FockSpace ι, ∀ ψ : FockSpace ι,
      (coeffExp (lowerSqueeze fun j => tanhPhase (ζ j)) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ := by
  classical
  obtain ⟨χ, -, hχ⟩ := coeff_coeffExp_lowerSqueeze (fun j => norm_tanhPhase_lt_one (ζ j)) n
  exact ⟨χ, hχ⟩

/-- The ordered form of `S(ζ)` as a linear map from `Γ_s` to the formal Fock space. -/
noncomputable def orderedSqueezeLin (ζ : ι → ℂ) : FockSpace ι →ₗ[ℂ] FormalFock ι ℂ where
  toFun ψ := orderedSqueeze ζ (toFormal ψ)
  map_add' ψ φ := by
    change orderedSqueeze ζ (toFormal (ψ + φ)) =
      orderedSqueeze ζ (toFormal ψ) + orderedSqueeze ζ (toFormal φ)
    rw [orderedSqueeze, orderedSqueeze, orderedSqueeze,
      coeffExp_toFormal_add (exists_inner_coeffExp_lowerSqueeze ζ) ψ φ, map_add, map_add,
      smul_add]
  map_smul' c ψ := by
    change orderedSqueeze ζ (toFormal (c • ψ)) = c • orderedSqueeze ζ (toFormal ψ)
    rw [orderedSqueeze, orderedSqueeze,
      map_smul, coeffExp_smul, map_smul, map_smul, smul_comm]

/-- The ordered form of `S(ζ)` as a linear map acts by `orderedSqueeze`. -/
theorem orderedSqueezeLin_apply (ζ : ι → ℂ) (ψ : FockSpace ι) :
    orderedSqueezeLin ζ ψ = orderedSqueeze ζ (toFormal ψ) := rfl

/-- The coefficients of the ordered form of `S(ζ)` depend continuously on `ψ ∈ Γ_s`. -/
theorem continuous_coeff_orderedSqueezeLin (ζ : ι → ℂ) (n : ι →₀ ℕ) :
    Continuous fun ψ : FockSpace ι => (orderedSqueezeLin ζ ψ).coeff n := by
  have hT : IsCoeffFinite ((raiseSqueeze fun j => tanhPhase (ζ j)).exp *
      secondQuant (coshInvDiag ζ)) :=
    (IsCoeffFinite.exp (raiseSqueeze _).raisesParticleNumber.isCoeffFinite).mul
      (isCoeffFinite_secondQuant _)
  simp only [orderedSqueezeLin_apply, orderedSqueeze, coeff_smul, smul_eq_mul]
  exact continuous_const.mul (hT.continuous_coeff_comp
    (continuous_coeff_coeffExp_lowerSqueeze (fun j => norm_tanhPhase_lt_one (ζ j))) n)

/-- The scalar `(Πⱼ cⱼ)^{-1/2} e^{½ Σⱼ τ̄ⱼ zⱼ²}` of Theorem 15(a). -/
private noncomputable def sqScalar (ζ z : ι → ℂ) : ℂ :=
  (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (∑ j, conj (tanhPhase (ζ j)) * z j ^ 2 / 2)

/-- The one-mode factors `g(-τⱼ/2, zⱼ/cⱼ)` of Theorem 15(a). -/
private noncomputable def sqFactor (ζ z : ι → ℂ) (j : ι) : FormalFock Unit ℂ :=
  gaussVec (-tanhPhase (ζ j) / 2) (z j / (Real.cosh ‖ζ j‖ : ℂ))

omit [Fintype ι] [DecidableEq ι] in
private theorem summable_sq_sqFactor (ζ z : ι → ℂ) (j : ι) :
    Summable fun m : ℕ => ‖(sqFactor ζ z j).coeff (Finsupp.single () m)‖ ^ 2 := by
  classical
  refine summable_sq_coeff_gaussVec ?_ _
  rw [norm_div, norm_neg, Complex.norm_ofNat]
  linarith [norm_tanhPhase_lt_one (ζ j)]

private theorem memℓp_orderedSqueeze_expVecFormal (ζ z : ι → ℂ) :
    Memℓp (orderedSqueeze ζ (expVecFormal z)).coeff 2 := by
  rw [memℓp_coeff_iff_sqNorm_lt_top, orderedSqueeze_expVecFormal]
  exact sqNorm_smul_lt_top (sqNorm_tensorVec_lt_top fun j =>
    sqNorm_lt_top_of_summable_unit (summable_sq_sqFactor ζ z j)) _

/-- `S(ζ) ε(z)` as a vector of `Γ_s`. -/
private noncomputable def sqVec (ζ z : ι → ℂ) : FockSpace ι :=
  ⟨(orderedSqueeze ζ (expVecFormal z)).coeff, memℓp_orderedSqueeze_expVecFormal ζ z⟩

private theorem toFormal_sqVec (ζ z : ι → ℂ) :
    toFormal (sqVec ζ z) = sqScalar ζ z • tensorVec (sqFactor ζ z) := by
  change orderedSqueeze ζ (expVecFormal z) = _
  rw [orderedSqueeze_expVecFormal]
  rfl

private theorem sqVec_apply (ζ z : ι → ℂ) (n : ι →₀ ℕ) :
    sqVec ζ z n = sqScalar ζ z * (tensorVec (sqFactor ζ z)).coeff n := by
  rw [← coeff_toFormal, toFormal_sqVec, coeff_smul, smul_eq_mul]

omit [DecidableEq ι] in
/-- `(Πⱼ cⱼ)^{-1/2} (Πⱼ cⱼ)^{-1/2} Πⱼ cⱼ = 1`. -/
private theorem rpow_mul_rpow_mul_prod (ζ : ι → ℂ) :
    (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∏ j, (Real.cosh ‖ζ j‖ : ℂ) = 1 := by
  classical
  have hpos : 0 < ∏ j, Real.cosh ‖ζ j‖ := prod_pos fun j _ => Real.cosh_pos _
  rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, ← Complex.ofReal_prod, ← Complex.ofReal_mul]
  norm_num [Real.rpow_neg_one, hpos.ne']

/-- **Theorem 15(b).** `⟨S(ζ) ε(w), S(ζ) ε(z)⟩ = ⟨ε(w), ε(z)⟩`. -/
private theorem inner_sqVec (ζ w z : ι → ℂ) :
    ⟪sqVec ζ w, sqVec ζ z⟫_ℂ = ⟪expVec w, expVec z⟫_ℂ := by
  have hS : HasSum (fun n => conj (sqVec ζ w n) * sqVec ζ z n)
      (conj (sqScalar ζ w) * sqScalar ζ z * ∏ j, ∑' m : ℕ,
        conj ((sqFactor ζ w j).coeff (Finsupp.single () m)) *
          (sqFactor ζ z j).coeff (Finsupp.single () m)) := by
    have h := (hasSum_conj_mul_tensorVec (summable_sq_sqFactor ζ w)
      (summable_sq_sqFactor ζ z)).mul_left (conj (sqScalar ζ w) * sqScalar ζ z)
    refine h.congr_fun fun n => ?_
    rw [sqVec_apply, sqVec_apply, map_mul]
    ring
  refine (lp.hasSum_inner (𝕜 := ℂ) (sqVec ζ w) (sqVec ζ z)).unique ?_ |>.trans
    (inner_expVec w z).symm
  convert hS using 1
  · funext n
    rw [RCLike.inner_apply']
  · simp only [sqFactor, tsum_overlap_squeezed, prod_mul_distrib, ← Complex.exp_sum, sqScalar,
      map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_sum, map_div₀, map_pow,
      Complex.conj_conj, map_ofNat]
    have h1 := rpow_mul_rpow_mul_prod ζ
    calc Complex.exp (∑ j, conj (w j) * z j)
        = (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (∏ j, (Real.cosh ‖ζ j‖ : ℂ)) * Complex.exp (∑ j, conj (w j) * z j) := by
          rw [h1, one_mul]
      _ = _ := by
          rw [show ∀ a b c d e f : ℂ,
              a * Complex.exp b * (c * Complex.exp d) * (e * Complex.exp f) =
                a * c * e * Complex.exp (b + d + f) from fun a b c d e f => by
              rw [Complex.exp_add, Complex.exp_add]; ring]
          congr 2
          rw [← sum_add_distrib, ← sum_add_distrib]
          refine sum_congr rfl fun j _ => ?_
          ring

end FockSpace

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S(ζ)` is an isometry of `Γ_s` acting by the ordered form (Theorem 15(b)). -/
private theorem exists_squeeze_isometry (ζ : ι → ℂ) :
    ∃ L : FockSpace ι →ₗᵢ[ℂ] FockSpace ι, ∀ ψ, toFormal (L ψ) = orderedSqueezeLin ζ ψ :=
  exists_linearIsometry_of_expVec (orderedSqueezeLin ζ) (continuous_coeff_orderedSqueezeLin ζ)
    (sqVec ζ) (fun _ => rfl) (inner_sqVec ζ)

private theorem memℓp_orderedSqueeze (ζ : ι → ℂ) (ψ : FockSpace ι) :
    Memℓp (orderedSqueeze ζ (toFormal ψ)).coeff 2 := by
  obtain ⟨L, hL⟩ := exists_squeeze_isometry ζ
  rw [← orderedSqueezeLin_apply, ← hL ψ]
  exact lp.memℓp (L ψ)

/-- `S(ζ)` as a map of `Γ_s`: the ordered form, which lies in `Γ_s`. -/
private noncomputable def sqFun (ζ : ι → ℂ) (ψ : FockSpace ι) : FockSpace ι :=
  ⟨(orderedSqueeze ζ (toFormal ψ)).coeff, memℓp_orderedSqueeze ζ ψ⟩

/-- `S(ζ)` as a linear isometry of `Γ_s`. -/
private noncomputable def sqIsometry (ζ : ι → ℂ) : FockSpace ι →ₗᵢ[ℂ] FockSpace ι :=
  have h : ∀ ψ, sqFun ζ ψ = (exists_squeeze_isometry ζ).choose ψ := fun ψ =>
    toFormal_injective (by rw [(exists_squeeze_isometry ζ).choose_spec]; rfl)
  { toFun := sqFun ζ
    map_add' := fun ψ φ => by simp only [h, map_add]
    map_smul' := fun c ψ => by simp only [h, map_smul, RingHom.id_apply]
    norm_map' := fun ψ => by
      change ‖sqFun ζ ψ‖ = ‖ψ‖
      rw [h, LinearIsometry.norm_map] }

private theorem toFormal_sqIsometry (ζ : ι → ℂ) (ψ : FockSpace ι) :
    toFormal (sqIsometry ζ ψ) = orderedSqueeze ζ (toFormal ψ) := rfl

private theorem sqIsometry_expVec (ζ z : ι → ℂ) : sqIsometry ζ (expVec z) = sqVec ζ z := rfl

/-! ### Theorem 15(c): covariance under displacements -/

/-- The real-linear map `β ↦ cⱼ βⱼ - e^{iφⱼ} sⱼ β̄ⱼ` of the covariance of `S(ζ)` under
displacements. -/
noncomputable def squeezeMap (ζ β : ι → ℂ) : ι → ℂ := fun j =>
  (Real.cosh ‖ζ j‖ : ℂ) * β j -
    (if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ) * conj (β j)

omit [Fintype ι] [DecidableEq ι] in
private theorem squeezeMap_apply (ζ β : ι → ℂ) (j : ι) :
    squeezeMap ζ β j = (Real.cosh ‖ζ j‖ : ℂ) * β j - sinhPhase (ζ j) * conj (β j) := rfl

/-- `⟨ε(w), S(ζ) ε(z)⟩`, by Mehler's formula with `κ = 0` on each mode. -/
private theorem inner_expVec_sqVec (ζ w z : ι → ℂ) :
    ⟪expVec w, sqVec ζ z⟫_ℂ = sqScalar ζ z * Complex.exp (∑ j,
      (-tanhPhase (ζ j) / 2 * conj (w j) ^ 2 + z j / (Real.cosh ‖ζ j‖ : ℂ) * conj (w j))) := by
  have hε : ∀ j, Summable fun m : ℕ =>
      ‖(expVecFormal fun _ : Unit => w j).coeff (Finsupp.single () m)‖ ^ 2 :=
    fun j => summable_sq_coeff_expVecFormal_unit (w j)
  have hS := (hasSum_conj_mul_tensorVec hε (summable_sq_sqFactor ζ z)).mul_left (sqScalar ζ z)
  refine (lp.hasSum_inner (𝕜 := ℂ) (expVec w) (sqVec ζ z)).unique ?_
  convert hS using 1
  · funext n
    rw [RCLike.inner_apply', expVec_apply, sqVec_apply, ← coeff_expVecFormal,
      expVecFormal_eq_tensorVec]
    ring
  · rw [Complex.exp_sum]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    refine ((hasSum_conj_mul_coeff_expVecFormal_gaussVec ?_ (w j) _).tsum_eq).symm
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [norm_tanhPhase_lt_one (ζ j)]

/-- **Theorem 15(c) on exponential vectors**, weakly. -/
private theorem inner_sqIsometry_displacement (ζ β w z : ι → ℂ) :
    ⟪expVec w, sqIsometry ζ ((displacement β : FockSpace ι →L[ℂ] FockSpace ι) (expVec z))⟫_ℂ =
      ⟪expVec w, (displacement (squeezeMap ζ β) : FockSpace ι →L[ℂ] FockSpace ι)
        (sqIsometry ζ (expVec z))⟫_ℂ := by
  set C : ℂ := (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  set γ := squeezeMap ζ β
  have hL : ⟪expVec w, sqIsometry ζ ((displacement β : FockSpace ι →L[ℂ] FockSpace ι)
      (expVec z))⟫_ℂ = C * Complex.exp (∑ j, ((-(conj (β j) * β j) / 2 - conj (β j) * z j) +
        (conj (tanhPhase (ζ j)) * (z j + β j) ^ 2 / 2 + (-tanhPhase (ζ j) / 2 * conj (w j) ^ 2 +
          (z j + β j) / (Real.cosh ‖ζ j‖ : ℂ) * conj (w j))))) := by
    rw [displacement_expVec, map_smul, sqIsometry_expVec, inner_smul_right, inner_expVec_sqVec,
      sqScalar, exponent_displacement_eq_sum]
    simp only [sum_add_distrib, Complex.exp_add, Pi.add_apply]
    ring
  have hR : ⟪expVec w, (displacement γ : FockSpace ι →L[ℂ] FockSpace ι)
      (sqIsometry ζ (expVec z))⟫_ℂ = C * Complex.exp (∑ j,
        (conj (-(conj (-γ j) * (-γ j)) / 2 - conj (-γ j) * w j) +
          (conj (tanhPhase (ζ j)) * z j ^ 2 / 2 + (-tanhPhase (ζ j) / 2 * conj (w j - γ j) ^ 2 +
            z j / (Real.cosh ‖ζ j‖ : ℂ) * conj (w j - γ j))))) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, star_displacement,
      displacement_expVec,
      sqIsometry_expVec, inner_smul_left, inner_expVec_sqVec, sqScalar,
      exponent_displacement_eq_sum, ← Complex.exp_conj, map_sum]
    simp only [sum_add_distrib, Complex.exp_add, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
    ring
  rw [hL, hR]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  simp only [γ, squeezeMap_apply, map_sub, map_mul, map_neg, map_div₀,
    Complex.conj_conj, Complex.conj_ofReal, map_ofNat, tanhPhase_eq_sinhPhase_div]
  have hc : (Real.cosh ‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
  have h := cosh_sq_sub_conj_sinhPhase_mul_self (ζ j)
  field_simp
  linear_combination (-(β j) * (2 * conj (w j) + β j * conj (sinhPhase (ζ j)) -
    conj (β j) * (Real.cosh ‖ζ j‖ : ℂ))) * h

/-- `S(ζ)` as a bounded operator, before unitarity is known. -/
private noncomputable def sqCLM (ζ : ι → ℂ) : FockSpace ι →L[ℂ] FockSpace ι :=
  (sqIsometry ζ).toContinuousLinearMap

/-- **Theorem 15(c)** for the isometry `S(ζ)`: `S(ζ) D(β) = D(L_ζ β) S(ζ)`. -/
private theorem sqCLM_mul_displacement (ζ β : ι → ℂ) :
    sqCLM ζ * (displacement β : FockSpace ι →L[ℂ] FockSpace ι) =
      (displacement (squeezeMap ζ β) : FockSpace ι →L[ℂ] FockSpace ι) * sqCLM ζ :=
  ext_expVec fun z => ext_inner_expVec fun w => inner_sqIsometry_displacement ζ β w z

omit [Fintype ι] [DecidableEq ι] in
/-- `L_ζ L_{-ζ} = 1`. -/
theorem squeezeMap_squeezeMap_neg (ζ β : ι → ℂ) : squeezeMap ζ (squeezeMap (-ζ) β) = β := by
  classical
  funext j
  rw [squeezeMap_apply, squeezeMap_apply, Pi.neg_apply, norm_neg, sinhPhase_neg]
  simp only [map_sub, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
  have h := cosh_sq_sub_conj_sinhPhase_mul_self (ζ j)
  linear_combination β j * h

/-- The vacuum coefficient of `S(ζ) x` is `(Πⱼ cⱼ)^{-1/2} ⟨χ₀, x⟩` with
`χ₀ = e^{½ Σⱼ τⱼ aⱼ†²}∣0⟩`. -/
private theorem sqIsometry_apply_zero (ζ : ι → ℂ) {χ : FockSpace ι}
    (hχ : ∀ ψ : FockSpace ι,
      (coeffExp (lowerSqueeze fun j => tanhPhase (ζ j)) (toFormal ψ)).coeff 0 = ⟪χ, ψ⟫_ℂ)
    (x : FockSpace ι) :
    sqIsometry ζ x 0 = (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ⟪χ, x⟫_ℂ := by
  rw [← coeff_toFormal, toFormal_sqIsometry, orderedSqueeze, coeff_smul, smul_eq_mul,
    NumberRaisingOp.coeff_exp]
  simp only [map_zero, zero_add, range_one, sum_singleton, Nat.factorial_zero,
    Nat.cast_one, inv_one, pow_zero, Module.End.one_apply, one_smul]
  rw [coeff_secondQuant, map_zero, finsuppAntidiag_zero, sum_singleton, ← hχ x]
  congr 1
  have h1 : matrixCoeff (coshInvDiag ζ) 0 0 = 1 := by
    rw [matrixCoeff, secondQuant_vacuum, coeff_single, ite_eq_left rfl]
  rw [h1, one_mul]

/-- `⟨g(-τ/2, 0), g(-τ/2, 0)⟩ = cosh|ζ|`, the squared norm of the squeezed vacuum of one mode up to
its normalization. -/
private theorem tsum_overlap_squeezed_zero (ζ : ℂ) :
    ∑' m : ℕ, conj ((gaussVec (-tanhPhase ζ / 2) 0).coeff (Finsupp.single () m)) *
      (gaussVec (-tanhPhase ζ / 2) 0).coeff (Finsupp.single () m) = (Real.cosh ‖ζ‖ : ℂ) := by
  have h := tsum_overlap_squeezed ζ 0 0
  simp only [zero_div, map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero, sub_zero, Complex.exp_zero, mul_one] at h
  exact h

/-- `⟨0∣S(ζ) S(-ζ)∣0⟩ = 1`. -/
private theorem sqIsometry_sqIsometry_neg_vacuum (ζ : ι → ℂ) :
    ⟪vacuum, sqIsometry ζ (sqIsometry (-ζ) vacuum)⟫_ℂ = 1 := by
  obtain ⟨χ, hχf, hχ⟩ := coeff_coeffExp_lowerSqueeze (fun j => norm_tanhPhase_lt_one (ζ j)) 0
  have hv : ∀ y : FockSpace ι, ⟪vacuum, y⟫_ℂ = y 0 := fun y => by
    rw [vacuum, lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  rw [hv, sqIsometry_apply_zero ζ hχ, ← expVec_zero, sqIsometry_expVec]
  -- `χ₀ = ⊗ⱼ g(τⱼ/2, 0)`, the same product vector as `S(-ζ)∣0⟩` up to its scalar
  have hχt : toFormal χ = tensorVec (sqFactor (-ζ) 0) := by
    rw [hχf, raiseSqueeze_exp_single]
    congr 1
    funext j
    simp [sqFactor, tanhPhase_neg, gaussExp_vacuum]
  have hS : HasSum (fun n => conj (χ n) * sqVec (-ζ) 0 n)
      (sqScalar (-ζ) 0 * ∏ j, ∑' m : ℕ, conj ((sqFactor (-ζ) 0 j).coeff (Finsupp.single () m)) *
        (sqFactor (-ζ) 0 j).coeff (Finsupp.single () m)) := by
    refine ((hasSum_conj_mul_tensorVec (summable_sq_sqFactor (-ζ) 0)
      (summable_sq_sqFactor (-ζ) 0)).mul_left (sqScalar (-ζ) 0)).congr_fun fun n => ?_
    rw [sqVec_apply, ← coeff_toFormal χ, hχt]
    ring
  rw [(lp.hasSum_inner (𝕜 := ℂ) χ (sqVec (-ζ) 0)).unique (by
    simpa only [RCLike.inner_apply'] using hS)]
  simp only [sqFactor, sqScalar, Pi.neg_apply, Pi.zero_apply, zero_div, norm_neg,
    tsum_overlap_squeezed_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sum_const_zero, Complex.exp_zero, mul_one]
  rw [← mul_assoc]
  exact rpow_mul_rpow_mul_prod ζ

end FockSpace

/-! ### Theorem 15(d): unitarity -/

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S(ζ) S(-ζ) = 1`, by irreducibility. -/
private theorem sqIsometry_sqIsometry_neg (ζ : ι → ℂ) (ψ : FockSpace ι) :
    sqIsometry ζ (sqIsometry (-ζ) ψ) = ψ := by
  have hP : ∀ β : ι → ℂ,
      Commute (sqCLM ζ * sqCLM (-ζ)) (displacement β : FockSpace ι →L[ℂ] FockSpace ι) := by
    intro β
    change sqCLM ζ * sqCLM (-ζ) * displacement β = displacement β * (sqCLM ζ * sqCLM (-ζ))
    rw [mul_assoc, sqCLM_mul_displacement, ← mul_assoc, sqCLM_mul_displacement,
      squeezeMap_squeezeMap_neg, mul_assoc]
  have h := eq_smul_one_of_commute_displacement _ hP
  have h1 : ⟪vacuum, (sqCLM ζ * sqCLM (-ζ)) vacuum⟫_ℂ = 1 :=
    sqIsometry_sqIsometry_neg_vacuum ζ
  rw [h1, one_smul] at h
  exact congrArg (fun T : FockSpace ι →L[ℂ] FockSpace ι => T ψ) h

/-- `S(ζ)` as a linear isometric equivalence of `Γ_s`, with inverse `S(-ζ)`. -/
private noncomputable def sqEquiv (ζ : ι → ℂ) : FockSpace ι ≃ₗᵢ[ℂ] FockSpace ι :=
  { sqIsometry ζ with
    invFun := sqIsometry (-ζ)
    left_inv := fun ψ => by
      have := sqIsometry_sqIsometry_neg (-ζ) ψ
      rwa [neg_neg] at this
    right_inv := fun ψ => sqIsometry_sqIsometry_neg ζ ψ }

/-- **Definition 13.** The **squeezing operator** `S(ζ)` with per-mode squeezing parameters
`ζ ∈ ℂ^ι`, the unitary of `Γ_s(ι)` that acts by the normal-ordered form
`(Πⱼ cⱼ)^{-1/2} e^{-½ Σⱼ τⱼ aⱼ†²} Γ(diag(cⱼ⁻¹)) e^{½ Σⱼ τ̄ⱼ aⱼ²}` (`toFormal_squeeze`). -/
noncomputable def squeeze (ζ : ι → ℂ) : unitary (FockSpace ι →L[ℂ] FockSpace ι) :=
  Unitary.linearIsometryEquiv.symm (sqEquiv ζ)

/-- **Definition 13.** `S(ζ)` acts by the ordered form. -/
theorem toFormal_squeeze (ζ : ι → ℂ) (ψ : FockSpace ι) :
    toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ) =
      orderedSqueeze ζ (toFormal ψ) := rfl

private theorem squeeze_coe (ζ : ι → ℂ) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) = sqCLM ζ := rfl

/-- **Theorem 15(a).** `S(ζ) ε(z) = (Πⱼ cⱼ)^{-1/2} e^{½ Σⱼ τ̄ⱼ zⱼ²} ⊗ⱼ g(-τⱼ/2, zⱼ/cⱼ)`, with the
unnormalized squeezed coherent states `g(κ, ℓ) = e^{κ a†² + ℓ a†}∣0⟩`. -/
theorem squeeze_expVec (ζ z : ι → ℂ) :
    toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)) =
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (∑ j, conj (tanhPhase (ζ j)) * z j ^ 2 / 2)) •
        tensorVec fun j => gaussVec (-tanhPhase (ζ j) / 2) (z j / (Real.cosh ‖ζ j‖ : ℂ)) := by
  rw [toFormal_squeeze, toFormal_expVec, orderedSqueeze_expVecFormal]

/-- **Theorem 15(a), the squeezed vacuum** (the paper's (5)): `S(ζ)∣0⟩ = ⊗ⱼ cⱼ^{-1/2} g(-τⱼ/2, 0)`,
with `κⱼ = -τⱼ/2`, `|κⱼ| < 1/2`. -/
theorem squeeze_vacuum (ζ : ι → ℂ) :
    toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum) =
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) •
        tensorVec fun j => gaussVec (-tanhPhase (ζ j) / 2) 0 := by
  rw [← expVec_zero, squeeze_expVec]
  simp

/-- **Theorem 15(c), covariance under displacements.** `S(ζ) D(β) = D(L_ζ β) S(ζ)` with
`(L_ζ β)ⱼ = cⱼ βⱼ - e^{iφⱼ} sⱼ β̄ⱼ`. -/
theorem squeeze_mul_displacement (ζ β : ι → ℂ) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) * displacement β =
      (displacement (squeezeMap ζ β) : FockSpace ι →L[ℂ] FockSpace ι) * squeeze ζ :=
  sqCLM_mul_displacement ζ β

/-- `S(ζ) S(-ζ) = 1`. -/
theorem squeeze_mul_neg (ζ : ι → ℂ) : squeeze ζ * squeeze (-ζ) = 1 :=
  Subtype.ext (ContinuousLinearMap.ext fun ψ => sqIsometry_sqIsometry_neg ζ ψ)

/-- **Theorem 15(d).** `S(ζ)* = S(-ζ)`. -/
theorem star_squeeze (ζ : ι → ℂ) : star (squeeze ζ) = squeeze (-ζ) := by
  rw [Unitary.star_eq_inv]
  exact inv_eq_of_mul_eq_one_right (squeeze_mul_neg ζ)

/-- **Theorem 15(d).** `S(0) = 1`. -/
theorem squeeze_zero : squeeze (0 : ι → ℂ) = 1 := by
  refine Subtype.ext (ext_expVec fun z => toFormal_injective ?_)
  rw [squeeze_expVec, OneMemClass.coe_one, one_apply_eq_self, toFormal_expVec,
    expVecFormal_eq_tensorVec]
  simp [tanhPhase_zero, gaussVec_zero_left]

end FockSpace

/-! ### Rotations and Lemma 14 for `S` and `R` -/

namespace FormalFock

/-- One mode: the second quantization of the scalar `d` is `dⁿ` on `∣n⟩`. -/
theorem secondQuant_diagonal_numberState (d : ℂ) (p : ℕ) :
    secondQuant (Matrix.diagonal fun _ : Unit => d) (numberState p) = d ^ p • numberState p := by
  refine toBargmann.injective ?_
  have hl : linearForms (Matrix.diagonal fun _ : Unit => d) () = d • MvPowerSeries.X () := by
    simp [linearForms]
  rw [numberState, toBargmann_secondQuant_single, Finsupp.prod_single_index (by simp), hl,
    smul_pow, MvPowerSeries.X_pow_eq, map_smul, toBargmann_single, mul_one,
    ← mul_one (sqrtFactorial _)⁻¹, ← smul_eq_mul, map_smul, smul_comm, smul_eq_mul, mul_one]

/-- One mode: `e^{-τ a†²/2}` on a number state is the one-mode Gaussian operator. -/
theorem raiseSqueeze_exp_numberState (τ : ℂ) (k : ℕ) :
    (raiseSqueeze fun _ : Unit => τ).exp (numberState k) = gaussExp (-τ / 2) 0 (numberState k) := by
  rw [numberState, raiseSqueeze_exp_single, tensorVec_unit]
  simp [numberState]

/-- One mode: the coefficients of `(τ̄ a²/2)^r ∣n⟩`. -/
theorem coeff_lowerSqueeze_pow_numberState (τ : ℂ) (r n l : ℕ) :
    (((lowerSqueeze fun _ : Unit => τ) ^ r) (numberState n)).coeff (Finsupp.single () l) =
      if 2 * r ≤ n ∧ l = n - 2 * r then (conj τ / 2) ^ r *
        (sqrtC n.factorial / sqrtC (n - 2 * r).factorial) else 0 := by
  have hΛ : (lowerSqueeze fun _ : Unit => τ) = (conj τ / 2) • annihilate () ^ 2 := by
    simp [lowerSqueeze]
  rw [hΛ, smul_pow, ← pow_mul, LinearMap.smul_apply, annihilate_pow_numberState, mul_comm 2 r]
  by_cases h1 : r * 2 ≤ n
  · rw [ite_eq_left h1, coeff_smul, coeff_smul, coeff_numberState, Finsupp.single_eq_same]
    by_cases h2 : l = n - r * 2
    · rw [ite_eq_left h2, ite_eq_left ⟨h1, h2⟩, smul_eq_mul, smul_eq_mul, mul_one]
    · rw [ite_eq_right h2, ite_eq_right fun h => h2 h.2, smul_zero, smul_zero]
  · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1, smul_zero]
    rfl

/-- One mode: `e^{τ̄ a²/2} ∣n⟩ = Σ_{j ≤ n/2} (τ̄/2)ʲ/j! √(n!/(n-2j)!) ∣n - 2j⟩`, a finite sum. -/
theorem coeffExp_lowerSqueeze_numberState (τ : ℂ) (n : ℕ) :
    coeffExp (lowerSqueeze fun _ : Unit => τ) (numberState n) =
      ∑ j ∈ range (n / 2 + 1), (((j.factorial : ℂ)⁻¹ * (conj τ / 2) ^ j *
        (sqrtC n.factorial / sqrtC (n - 2 * j).factorial))) • numberState (n - 2 * j) := by
  ext m
  obtain ⟨l, rfl⟩ : ∃ l, m = Finsupp.single () l := ⟨m (), Finsupp.unique_single m⟩
  rw [coeff_coeffExp, coeff_sum]
  simp only [coeff_lowerSqueeze_pow_numberState, coeff_smul, coeff_numberState, smul_eq_mul,
    Finsupp.single_eq_same, mul_ite, mul_one, mul_zero]
  -- both sides have at most one nonzero term, at `2j = n - l`
  by_cases hl : l ≤ n ∧ Even (n - l)
  · obtain ⟨hln, j, hj⟩ := hl
    have hj' : n - l = 2 * j := by omega
    rw [tsum_eq_single j fun r hr => ite_eq_right_iff.2 fun h => absurd (by omega) hr,
      sum_eq_single j (fun i hi' hi => ite_eq_right_iff.2 fun h =>
        absurd (by rw [mem_range] at hi'; omega) hi)
        fun h => absurd (mem_range.2 (by omega)) h]
    simp only [show 2 * j ≤ n by omega, show l = n - 2 * j by omega, and_self, ↓reduceIte]
    ring
  · rw [sum_eq_zero fun i hi => ite_eq_right_iff.2 fun h =>
      absurd ⟨by rw [mem_range] at hi; omega, i, by rw [mem_range] at hi; omega⟩ hl]
    exact (tsum_congr fun r => ite_eq_right_iff.2 fun h =>
      absurd ⟨by omega, r, by omega⟩ hl).trans tsum_zero

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal unitary `diag(e^{-iθⱼ})`. -/
noncomputable def phaseDiag (θ : ι → ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal fun j => Complex.exp (-(θ j : ℂ) * Complex.I), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.star_apply, show star (Complex.exp (-(θ j : ℂ) * Complex.I)) =
      conj (Complex.exp (-(θ j : ℂ) * Complex.I)) from rfl, ← Complex.exp_conj, ← Complex.exp_add,
      map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_zero]
    congr 1
    ring⟩

/-- **Definition 13.** The rotation `R(θ) = Γ(diag(e^{-iθⱼ}))`, the second quantization of the
diagonal unitary (B5.1); it is `e^{-i Σⱼ θⱼ n̂ⱼ}` by `FormalFock.secondQuant_exp`. -/
noncomputable def rotation (θ : ι → ℝ) : unitary (FockSpace ι →L[ℂ] FockSpace ι) :=
  secondQuantRep (phaseDiag θ)

/-- `diag(e^{-iθⱼ}) = 1` when every `e^{-iθⱼ} = 1`. -/
private theorem phaseDiag_eq_one {θ : ι → ℝ} (h : ∀ j, Complex.exp (-(θ j : ℂ) * Complex.I) = 1) :
    phaseDiag θ = 1 := by
  refine Subtype.ext ?_
  change Matrix.diagonal (fun j => Complex.exp (-(θ j : ℂ) * Complex.I)) = 1
  simp only [h, Matrix.diagonal_one]

/-- A degenerate case of Definition 13: `R(0) = 1`. -/
@[simp]
theorem rotation_zero : rotation (0 : ι → ℝ) = 1 := by
  rw [rotation, phaseDiag_eq_one fun j => by simp, map_one]

/-- A degenerate case of Definition 13: `R(2π) = 1`. -/
@[simp]
theorem rotation_two_pi : rotation (fun _ : ι => 2 * Real.pi) = 1 := by
  rw [rotation, phaseDiag_eq_one fun j => Complex.exp_eq_one_iff.2 ⟨-1, by push_cast; ring⟩,
    map_one]

/-- **Lemma 14.** One mode: `⟨k∣R(θ)∣n⟩ = δ_{kn} e^{-iθn}`. -/
theorem rotation_matrixElement (θ : ℝ) (k n : ℕ) :
    (rotation (fun _ : Unit => θ) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (lp.single 2 (Finsupp.single () n) 1) (Finsupp.single () k) =
      if k = n then Complex.exp (-(θ : ℂ) * n * Complex.I) else 0 := by
  rw [← coeff_toFormal, rotation, secondQuantRep_apply, toFormal_secondQuantUnitary,
    toFormal_lpSingle, ← numberState]
  change (secondQuant (Matrix.diagonal fun _ : Unit => Complex.exp (-(θ : ℂ) * Complex.I))
    (numberState n)).coeff _ = _
  rw [secondQuant_diagonal_numberState, coeff_smul, coeff_numberState, Finsupp.single_eq_same,
    smul_eq_mul, ← Complex.exp_nat_mul]
  split_ifs
  · rw [mul_one]
    congr 1
    ring
  · rw [mul_zero]

/-- **Lemma 14.** One mode:
`⟨k∣S(ζ)∣n⟩ = c^{-1/2} Σ (-τ/2)ⁱ/i! √(k!/p!) c^{-p} (τ̄/2)ʲ/j! √(n!/p!)`, over
`p = n - 2j = k - 2i ≥ 0`, with `τ = tanhPhase ζ` and `c = cosh|ζ|`; a finite sum. -/
theorem squeeze_matrixElement (ζ : ℂ) (k n : ℕ) :
    (squeeze (fun _ : Unit => ζ) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (lp.single 2 (Finsupp.single () n) 1) (Finsupp.single () k) =
      (((Real.cosh ‖ζ‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑ j ∈ range (n / 2 + 1),
        if n - 2 * j ≤ k ∧ Even (k - (n - 2 * j)) then
          (-tanhPhase ζ / 2) ^ ((k - (n - 2 * j)) / 2) / ((k - (n - 2 * j)) / 2).factorial *
            (Real.sqrt (k.factorial / (n - 2 * j).factorial : ℝ) : ℂ) *
            (((Real.cosh ‖ζ‖)⁻¹ ^ (n - 2 * j) : ℝ) : ℂ) *
            (conj (tanhPhase ζ) / 2) ^ j / j.factorial *
            (Real.sqrt (n.factorial / (n - 2 * j).factorial : ℝ) : ℂ)
        else 0 := by
  rw [← coeff_toFormal, toFormal_squeeze, toFormal_lpSingle, orderedSqueeze, coeff_smul,
    smul_eq_mul, ← numberState, coeffExp_lowerSqueeze_numberState, map_sum, map_sum, coeff_sum]
  simp only [univ_unique, prod_singleton]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [map_smul, map_smul, coshInvDiag, secondQuant_diagonal_numberState, map_smul,
    raiseSqueeze_exp_numberState, coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul,
    coeff_gaussExp_numberState]
  by_cases hp : n - 2 * j ≤ k
  · rw [ite_eq_left hp]
    obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' (k - (n - 2 * j))
    · rw [ite_eq_left ⟨hp, i, by omega⟩, hi, cMatrix_zero_right_even, show 2 * i / 2 = i by omega,
        Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_div (Nat.cast_nonneg _)]
      simp only [sqrtC, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv]
      ring
    · have hne : ¬(n - 2 * j ≤ k ∧ Even (k - (n - 2 * j))) := by
        rintro ⟨-, m, hm⟩
        omega
      rw [ite_eq_right hne, hi, cMatrix_zero_right_odd, mul_zero, zero_div, mul_zero, mul_zero]
  · rw [ite_eq_right hp, ite_eq_right fun h => hp h.1, mul_zero, mul_zero]

/-- The **single-mode Gaussian unitary** `U_G = D(α) S(ζ) e^{-iθn̂}` of Tjoa–Cirac, (6), with
`e^{-iθn̂} = R(θ)`. -/
noncomputable def gaussianUnitary (α ζ : ℂ) (θ : ℝ) :
    unitary (FockSpace Unit →L[ℂ] FockSpace Unit) :=
  displacement (fun _ => α) * squeeze (fun _ => ζ) * rotation (fun _ => θ)

end FockSpace

/-! ### Theorem 15(e): the product over the modes -/

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 15(c)**, conjugated form: `S(ζ)* D(α) S(ζ) = D(L_{-ζ} α)`. -/
theorem star_squeeze_mul_displacement_mul (ζ α : ι → ℂ) :
    (star (squeeze ζ) : FockSpace ι →L[ℂ] FockSpace ι) * displacement α * squeeze ζ =
      displacement (squeezeMap (-ζ) α) := by
  have h1 : squeeze (-ζ) * squeeze ζ = 1 := by simpa using squeeze_mul_neg (-ζ)
  rw [← Unitary.coe_star, star_squeeze, squeeze_mul_displacement, mul_assoc,
    ← MulMemClass.coe_mul, h1,
    OneMemClass.coe_one, mul_one]

/-- The vacuum expectation value `⟨0∣S(ζ)∣0⟩ = (Πⱼ cⱼ)^{-1/2}`. -/
private theorem inner_vacuum_squeeze_vacuum (ζ : ι → ℂ) :
    ⟪vacuum, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum⟫_ℂ =
      (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hv : ∀ y : FockSpace ι, ⟪vacuum, y⟫_ℂ = y 0 := fun y => by
    rw [vacuum, lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  have hg : ∀ j, (gaussVec (-tanhPhase (ζ j) / 2) 0).coeff
      (Finsupp.single () ((0 : ι →₀ ℕ) j)) = 1 := fun j => by
    rw [Finsupp.coe_zero, Pi.zero_apply, coeff_gaussVec, cMatrix_zero, Nat.factorial_zero,
      mul_one]
    simp [sqrtC]
  rw [hv, ← coeff_toFormal, squeeze_vacuum, coeff_smul, coeff_tensorVec, smul_eq_mul]
  simp only [hg, prod_const_one, mul_one]

/-- The overlap of two squeezed vacua, by Mehler's formula:
`⟨S(ζ)∣0⟩, S(ζ')∣0⟩⟩ = (Πⱼ cⱼ)^{-1/2} (Πⱼ c'ⱼ)^{-1/2} Πⱼ 𝒮(τ̄ⱼ τ'ⱼ / 4)`, with
`𝒮(x) = Σᵢ C(2i, i) xⁱ = (1 - 4x)^{-1/2}`. -/
theorem inner_squeeze_vacuum (ζ ζ' : ι → ℂ) :
    ⟪(squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum,
      (squeeze ζ' : FockSpace ι →L[ℂ] FockSpace ι) vacuum⟫_ℂ =
      (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (((∏ j, Real.cosh ‖ζ' j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∏ j, centralBinomSeries (conj (tanhPhase (ζ j)) * tanhPhase (ζ' j) / 4) := by
  have hκ : ∀ ζ : ℂ, ‖-tanhPhase ζ / 2‖ < 1 / 2 := fun ζ => by
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [norm_tanhPhase_lt_one ζ]
  have hS := hasSum_conj_mul_tensorVec (fun j => summable_sq_coeff_gaussVec (hκ (ζ j)) 0)
    (fun j => summable_sq_coeff_gaussVec (hκ (ζ' j)) 0)
  have hT : HasSum (fun n => conj ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) vacuum n) *
      (squeeze ζ' : FockSpace ι →L[ℂ] FockSpace ι) vacuum n)
      ((((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (((∏ j, Real.cosh ‖ζ' j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∏ j, ∑' m : ℕ, conj ((gaussVec (-tanhPhase (ζ j) / 2) 0).coeff (Finsupp.single () m)) *
          (gaussVec (-tanhPhase (ζ' j) / 2) 0).coeff (Finsupp.single () m)) := by
    refine (hS.mul_left _).congr_fun fun n => ?_
    rw [← coeff_toFormal, ← coeff_toFormal, squeeze_vacuum, squeeze_vacuum, coeff_smul,
      coeff_smul, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal]
    ring
  rw [(lp.hasSum_inner (𝕜 := ℂ) _ _).unique (by simpa only [RCLike.inner_apply'] using hT)]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [(hasSum_conj_mul_coeff_gaussVec (by linarith [hκ (ζ j), hκ (ζ' j)]) 0 0).tsum_eq]
  simp only [map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero, NormedSpace.exp_zero, mul_one]
  congr 1
  simp only [map_div₀, map_neg, map_ofNat]
  ring

/-- Squeezings of disjoint sets of modes multiply: `S(ζ + ζ') = S(ζ) S(ζ')` if, for every `j`,
`ζⱼ = 0` or `ζ'ⱼ = 0`. -/
theorem squeeze_add_of_disjoint {ζ ζ' : ι → ℂ} (h : ∀ j, ζ j = 0 ∨ ζ' j = 0) :
    squeeze (ζ + ζ') = squeeze ζ * squeeze ζ' := by
  refine (eq_of_conj_eq_of_inner_vacuum _ _ (fun α => ?_) ?_ ?_).symm
  · have e : ∀ A B X C E : FockSpace ι →L[ℂ] FockSpace ι,
        A * B * X * (C * E) = A * (B * X * C) * E := fun _ _ _ _ _ => by simp only [mul_assoc]
    rw [star_squeeze_mul_displacement_mul, ← Unitary.coe_star, star_mul, MulMemClass.coe_mul,
      MulMemClass.coe_mul, e, Unitary.coe_star, Unitary.coe_star,
      star_squeeze_mul_displacement_mul, star_squeeze_mul_displacement_mul]
    congr 2
    funext j
    rcases h j with h | h <;> simp [squeezeMap, h]
  · rw [inner_vacuum_squeeze_vacuum, MulMemClass.coe_mul, mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, star_squeeze, inner_squeeze_vacuum]
    have hc : ∀ j, Real.cosh ‖ζ j + ζ' j‖ = Real.cosh ‖ζ j‖ * Real.cosh ‖ζ' j‖ := fun j => by
      rcases h j with h | h <;> simp [h]
    have hb : ∀ j, centralBinomSeries (conj (tanhPhase (-ζ j)) * tanhPhase (ζ' j) / 4) = 1 :=
      fun j => by rcases h j with h | h <;> simp [h, tanhPhase_zero, centralBinomSeries_zero]
    simp only [Pi.neg_apply, hb, prod_const_one, mul_one, Pi.add_apply, hc, prod_mul_distrib,
      norm_neg]
    rw [Real.mul_rpow (prod_nonneg fun j _ => (Real.cosh_pos _).le)
      (prod_nonneg fun j _ => (Real.cosh_pos _).le), Complex.ofReal_mul]
  · rw [inner_vacuum_squeeze_vacuum]
    exact Complex.ofReal_ne_zero.2
      (Real.rpow_pos_of_pos (prod_pos fun j _ => Real.cosh_pos _) _).ne'

/-- `S(Σ_{j ∈ l} ζⱼ eⱼ) = Π_{j ∈ l} S(ζⱼ eⱼ)` along a list of distinct modes. -/
private theorem squeeze_list_sum (ζ : ι → ℂ) :
    ∀ l : List ι, l.Nodup →
      (squeeze (l.map fun j => Pi.single j (ζ j)).sum : FockSpace ι →L[ℂ] FockSpace ι) =
        (l.map fun j => (squeeze (Pi.single j (ζ j)) : FockSpace ι →L[ℂ] FockSpace ι)).prod
  | [], _ => by simp [squeeze_zero]
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons,
      ← squeeze_list_sum ζ l hl.2, squeeze_add_of_disjoint, MulMemClass.coe_mul]
    intro k
    by_cases hka : k = a
    · obtain rfl := hka
      right
      rw [Pi.list_sum_apply, List.map_map]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact Pi.single_eq_of_ne (fun h => hl.1 (by rw [h]; exact hj)) _
    · left
      exact Pi.single_eq_of_ne hka _

/-- **Theorem 15(e).** `S(ζ) = Πⱼ S(ζⱼ eⱼ)`; the factors commute (`squeeze_add_of_disjoint`), and
`S(ζⱼ eⱼ)` acts on mode `j` as the one-mode `S(ζⱼ)` (`squeeze_single_apply`). -/
theorem squeeze_eq_prod (ζ : ι → ℂ) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) =
      (univ.toList.map fun j => (squeeze (Pi.single j (ζ j)) :
        FockSpace ι →L[ℂ] FockSpace ι)).prod := by
  rw [← squeeze_list_sum ζ _ (nodup_toList univ), Finset.sum_map_toList,
    Finset.univ_sum_single]

/-- **Theorem 15(e).** `S(a eⱼ)` acts on mode `j` as the one-mode `S(a)`:
`(S(a eⱼ) ψ)(n) = (S(a) ψₙ)(nⱼ)`, with `ψₙ` the fiber of `ψ` along mode `j` at `n`. -/
theorem squeeze_single_apply (j : ι) (a : ℂ) (ψ : FockSpace ι) (n : ι →₀ ℕ) :
    (squeeze (Pi.single j a) : FockSpace ι →L[ℂ] FockSpace ι) ψ n =
      (squeeze (fun _ : Unit => a) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (fiberFock j n ψ) (Finsupp.single () (n j)) := by
  have h := ext_expVec
    (f := (innerSL ℂ (lp.single 2 n (1 : ℂ))).comp
      (squeeze (Pi.single j a) : FockSpace ι →L[ℂ] FockSpace ι))
    (g := (innerSL ℂ (lp.single 2 (Finsupp.single () (n j)) (1 : ℂ))).comp
      ((squeeze (fun _ : Unit => a) : FockSpace Unit →L[ℂ] FockSpace Unit).comp
        (fiberFock j n))) fun z => by
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, lp.inner_single_left,
      RCLike.inner_apply', map_one, one_mul]
    rw [fiberFock_expVec, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      ← coeff_toFormal ((squeeze (Pi.single j a) : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)),
      ← coeff_toFormal ((squeeze (fun _ : Unit => a) : FockSpace Unit →L[ℂ] FockSpace Unit)
        (expVec fun _ => z j)), squeeze_expVec, squeeze_expVec, coeff_smul, coeff_smul,
      smul_eq_mul, smul_eq_mul, coeff_tensorVec, coeff_tensorVec]
    have hs : ∏ k, Real.cosh ‖(Pi.single j a : ι → ℂ) k‖ = Real.cosh ‖a‖ := by
      rw [prod_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
      simp
    have hz : ∑ k, conj (tanhPhase ((Pi.single j a : ι → ℂ) k)) * z k ^ 2 / 2 =
        conj (tanhPhase a) * z j ^ 2 / 2 := by
      rw [sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk, tanhPhase_zero])
        (by simp)]
      simp
    have hp : ∏ k ∈ univ.erase j, (gaussVec (-tanhPhase ((Pi.single j a : ι → ℂ) k) / 2)
        (z k / (Real.cosh ‖(Pi.single j a : ι → ℂ) k‖ : ℂ))).coeff (Finsupp.single () (n k)) =
        ∏ k ∈ univ.erase j, z k ^ n k / sqrtC (n k).factorial :=
      prod_congr rfl fun k hk => by
        rw [Pi.single_eq_of_ne (ne_of_mem_erase hk), tanhPhase_zero, norm_zero, Real.cosh_zero,
          Complex.ofReal_one, div_one, neg_zero, zero_div, gaussVec_zero_left,
          coeff_expVecFormal_unit]
    rw [hs, hz, ← mul_prod_erase univ _ (mem_univ j), hp]
    simp only [Pi.single_eq_same, Finsupp.single_eq_same, univ_unique, sum_singleton,
      prod_singleton, PUnit.default_eq_unit]
    ring
  have := congrArg (fun f => f ψ) h
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, lp.inner_single_left,
    RCLike.inner_apply', map_one, one_mul] using this

end FockSpace

/-! ### Theorem 17(a): one-parameter groups of squeezers -/

/-- `cosh|xζ| = cosh(x|ζ|)` for real `x`. -/
theorem cosh_norm_ofReal_mul (x : ℝ) (ζ : ℂ) : Real.cosh ‖(x : ℂ) * ζ‖ = Real.cosh (x * ‖ζ‖) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Real.cosh_abs (x * ‖ζ‖), abs_mul,
    abs_norm]

/-- Along a ray, `e^{iφ} sinh r` is `e^{iφ} sinh(x|ζ|)`: `sinhPhase (xζ) = (ζ/|ζ|) sinh(x|ζ|)` for
real `x` (and `0` at `ζ = 0`). -/
private theorem sinhPhase_ofReal_mul (x : ℝ) (ζ : ℂ) :
    sinhPhase (x * ζ) = (if ζ = 0 then 0 else ζ / (‖ζ‖ : ℂ)) * (Real.sinh (x * ‖ζ‖) : ℂ) := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · simp [sinhPhase]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sinhPhase]
  have hxζ : (x : ℂ) * ζ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hx) hζ
  have hn : (‖ζ‖ : ℂ) ≠ 0 := by simpa using hζ
  simp only [sinhPhase, hxζ, hζ, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h, neg_mul, Real.sinh_neg]
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
    push_cast
    field_simp
  · rw [abs_of_pos h]
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
    push_cast
    field_simp

/-- Along a ray, `tanhPhase (xζ) = (ζ/|ζ|) tanh(x|ζ|)` for real `x` (and `0` at `ζ = 0`). -/
theorem tanhPhase_ofReal_mul (x : ℝ) (ζ : ℂ) :
    tanhPhase (x * ζ) = (if ζ = 0 then 0 else ζ / (‖ζ‖ : ℂ)) * (Real.tanh (x * ‖ζ‖) : ℂ) := by
  rw [tanhPhase_eq_sinhPhase_div, sinhPhase_ofReal_mul, cosh_norm_ofReal_mul,
    Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div, mul_div_assoc]

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Along a ray, `L_{xζ} L_{yζ} = L_{(x+y)ζ}`, by the addition formulas for `cosh` and `sinh`. -/
theorem squeezeMap_smul_squeezeMap_smul (ζ β : ι → ℂ) (x y : ℝ) :
    squeezeMap ((x : ℂ) • ζ) (squeezeMap ((y : ℂ) • ζ) β) =
      squeezeMap (((x + y : ℝ) : ℂ) • ζ) β := by
  have key : ∀ (ξ γ : ι → ℂ) (j : ι),
      squeezeMap ξ γ j = (Real.cosh ‖ξ j‖ : ℂ) * γ j - sinhPhase (ξ j) * conj (γ j) :=
    fun _ _ _ => rfl
  funext j
  simp only [key, Pi.smul_apply, smul_eq_mul, cosh_norm_ofReal_mul, sinhPhase_ofReal_mul,
    add_mul, Real.cosh_add, Real.sinh_add]
  rcases eq_or_ne (ζ j) 0 with h | h
  · simp [h]
  have hu : (ζ j / (‖ζ j‖ : ℂ)) * conj (ζ j / (‖ζ j‖ : ℂ)) = 1 := by
    have hn : (‖ζ j‖ : ℂ) ≠ 0 := by simpa using h
    rw [Complex.mul_conj', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.2 h)]
    simp
  simp only [h, ↓reduceIte, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj,
    Complex.ofReal_add, Complex.ofReal_mul]
  linear_combination ((Real.sinh (x * ‖ζ j‖) : ℂ) * (Real.sinh (y * ‖ζ j‖) : ℂ) * β j) * hu

/-- `|tanh x| < 1`. -/
private theorem abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 :=
  abs_lt.2 ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

/-- The vacuum factor of Theorem 17(a) for one mode:
`(cosh a cosh b)^{-1/2} (1 + tanh a tanh b)^{-1/2} = cosh(a + b)^{-1/2}`. -/
private theorem cosh_mul_cosh_mul_one_add_tanh (a b : ℝ) :
    Real.cosh a * Real.cosh b * (1 + Real.tanh a * Real.tanh b) = Real.cosh (a + b) := by
  rw [Real.cosh_add, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have ha := (Real.cosh_pos a).ne'
  have hb := (Real.cosh_pos b).ne'
  field_simp

/-- **Theorem 17(a).** Along a ray the squeezings form a one-parameter group:
`S(tζ₀) S(sζ₀) = S((t + s)ζ₀)` for real `t, s`. -/
theorem squeeze_smul_mul (ζ₀ : ι → ℂ) (t s : ℝ) :
    (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι) * squeeze ((s : ℂ) • ζ₀) =
      squeeze (((t + s : ℝ) : ℂ) • ζ₀) := by
  have hneg : ∀ x : ℝ, -((x : ℂ) • ζ₀) = ((-x : ℝ) : ℂ) • ζ₀ := fun x => by
    rw [Complex.ofReal_neg, neg_smul]
  have h : squeeze ((t : ℂ) • ζ₀) * squeeze ((s : ℂ) • ζ₀) = squeeze (((t + s : ℝ) : ℂ) • ζ₀) := by
    refine eq_of_conj_eq_of_inner_vacuum _ _ (fun α => ?_) ?_ ?_
    · have e : ∀ A B X C E : FockSpace ι →L[ℂ] FockSpace ι,
          A * B * X * (C * E) = A * (B * X * C) * E := fun _ _ _ _ _ => by simp only [mul_assoc]
      rw [star_squeeze_mul_displacement_mul, ← Unitary.coe_star, star_mul, MulMemClass.coe_mul,
        MulMemClass.coe_mul, e, Unitary.coe_star, Unitary.coe_star,
        star_squeeze_mul_displacement_mul, star_squeeze_mul_displacement_mul, hneg, hneg, hneg,
        squeezeMap_smul_squeezeMap_smul]
      rw [show -s + -t = -(t + s) by ring]
    · rw [inner_vacuum_squeeze_vacuum, MulMemClass.coe_mul, mul_apply_eq_comp,
        ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        ← Unitary.coe_star, star_squeeze, inner_squeeze_vacuum]
      have hb : ∀ j, centralBinomSeries (conj (tanhPhase (-((t : ℂ) * ζ₀ j))) *
          tanhPhase ((s : ℂ) * ζ₀ j) / 4) =
          (((1 + Real.tanh (t * ‖ζ₀ j‖) * Real.tanh (s * ‖ζ₀ j‖)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        intro j
        have ha : 4 * |-(Real.tanh (t * ‖ζ₀ j‖) * Real.tanh (s * ‖ζ₀ j‖)) / 4| < 1 := by
          rw [abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          have h1 := abs_tanh_lt_one (t * ‖ζ₀ j‖)
          have h2 := abs_tanh_lt_one (s * ‖ζ₀ j‖)
          have h3 : |Real.tanh (t * ‖ζ₀ j‖)| * |Real.tanh (s * ‖ζ₀ j‖)| < 1 :=
            (mul_le_of_le_one_right (abs_nonneg _) h2.le).trans_lt h1
          linarith
        have hx : conj (tanhPhase (-((t : ℂ) * ζ₀ j))) * tanhPhase ((s : ℂ) * ζ₀ j) / 4 =
            ((-(Real.tanh (t * ‖ζ₀ j‖) * Real.tanh (s * ‖ζ₀ j‖)) / 4 : ℝ) : ℂ) := by
          simp only [tanhPhase_neg, tanhPhase_ofReal_mul]
          rcases eq_or_ne (ζ₀ j) 0 with h | h
          · simp [h]
          have hu : conj (ζ₀ j / (‖ζ₀ j‖ : ℂ)) * (ζ₀ j / (‖ζ₀ j‖ : ℂ)) = 1 := by
            rw [Complex.conj_mul', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
              div_self (norm_ne_zero_iff.2 h)]
            simp
          simp only [h, ↓reduceIte, map_neg, map_mul, Complex.conj_ofReal, Complex.ofReal_div,
            Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
          linear_combination (-(Real.tanh (t * ‖ζ₀ j‖) : ℂ) * (Real.tanh (s * ‖ζ₀ j‖) : ℂ) / 4) * hu
        rw [hx, centralBinomSeries_ofReal_of_abs_lt ha]
        congr 3
        ring
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hb, norm_neg, cosh_norm_ofReal_mul]
      rw [← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      have hpos : ∀ x : ℝ, 0 ≤ ∏ j, Real.cosh (x * ‖ζ₀ j‖) := fun x =>
        prod_nonneg fun j _ => (Real.cosh_pos _).le
      have h1 : ∀ j, 0 ≤ 1 + Real.tanh (t * ‖ζ₀ j‖) * Real.tanh (s * ‖ζ₀ j‖) := fun j => by
        have h1 := abs_tanh_lt_one (t * ‖ζ₀ j‖)
        have h2 := abs_tanh_lt_one (s * ‖ζ₀ j‖)
        have h3 := neg_abs_le (Real.tanh (t * ‖ζ₀ j‖) * Real.tanh (s * ‖ζ₀ j‖))
        rw [abs_mul] at h3
        nlinarith [abs_nonneg (Real.tanh (t * ‖ζ₀ j‖)), abs_nonneg (Real.tanh (s * ‖ζ₀ j‖))]
      rw [Real.finsetProd_rpow _ _ fun j _ => h1 j, ← Real.mul_rpow (hpos t) (hpos s),
        ← Real.mul_rpow (mul_nonneg (hpos t) (hpos s)) (prod_nonneg fun j _ => h1 j),
        ← prod_mul_distrib, ← prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun j _ => ?_
      rw [cosh_mul_cosh_mul_one_add_tanh, add_mul]
    · rw [inner_vacuum_squeeze_vacuum]
      exact Complex.ofReal_ne_zero.2
        (Real.rpow_pos_of_pos (prod_pos fun j _ => Real.cosh_pos _) _).ne'
  rw [← MulMemClass.coe_mul, h]

end FockSpace

/-! ### Theorem 17(b): strong continuity -/

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 15(a)**, matrix elements between exponential vectors:
`⟨ε(w), S(ζ) ε(z)⟩ = (Πⱼ cⱼ)^{-1/2} e^{½ Σⱼ τ̄ⱼ zⱼ²} e^{Σⱼ (-τⱼ w̄ⱼ²/2 + zⱼ w̄ⱼ/cⱼ)}`. -/
theorem inner_expVec_squeeze_expVec (ζ w z : ι → ℂ) :
    ⟪expVec w, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ =
      (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (∑ j, conj (tanhPhase (ζ j)) * z j ^ 2 / 2) *
        Complex.exp (∑ j, (-tanhPhase (ζ j) / 2 * conj (w j) ^ 2 +
          z j / (Real.cosh ‖ζ j‖ : ℂ) * conj (w j))) :=
  inner_expVec_sqVec ζ w z

end FockSpace

/-- `sinh r / r`, continued by its limit `1` at `r = 0`. -/
private noncomputable def sinhDiv : ℝ → ℝ := Function.update (fun r => Real.sinh r / r) 0 1

private theorem continuous_sinhDiv : Continuous sinhDiv := by
  refine continuous_iff_continuousAt.2 fun r => ?_
  rcases eq_or_ne r 0 with rfl | hr
  · refine continuousAt_update_same.2 ?_
    have h := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_sinh 0)
    rw [Real.cosh_zero] at h
    refine Filter.Tendsto.congr (fun x => ?_) h
    rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]
  · exact (continuousAt_update_of_ne hr).2
      ((Real.continuous_sinh.continuousAt).div continuousAt_id hr)

private theorem sinhPhase_eq_mul_sinhDiv (ζ : ℂ) : sinhPhase ζ = ζ * (sinhDiv ‖ζ‖ : ℂ) := by
  rcases eq_or_ne ζ 0 with rfl | h
  · simp [sinhPhase]
  have hn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 h
  rw [sinhPhase, ite_eq_right h, sinhDiv, Function.update_of_ne hn]
  push_cast
  ring

/-- `ζ ↦ e^{iφ} sinh r` is continuous. -/
private theorem continuous_sinhPhase : Continuous sinhPhase := by
  rw [show sinhPhase = fun ζ => ζ * (sinhDiv ‖ζ‖ : ℂ) from funext sinhPhase_eq_mul_sinhDiv]
  exact continuous_id.mul (Complex.continuous_ofReal.comp (continuous_sinhDiv.comp continuous_norm))

/-- `ζ ↦ τ(ζ) = e^{iφ} tanh r` is continuous. -/
theorem continuous_tanhPhase : Continuous tanhPhase := by
  rw [show tanhPhase = fun ζ => sinhPhase ζ / (Real.cosh ‖ζ‖ : ℂ) from
    funext tanhPhase_eq_sinhPhase_div]
  exact continuous_sinhPhase.div
    (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp continuous_norm))
    fun ζ => Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ζ ↦ ⟨ε(w), S(ζ) ε(z)⟩` is continuous. -/
theorem continuous_inner_expVec_squeeze_expVec (w z : ι → ℂ) :
    Continuous fun ζ : ι → ℂ =>
      ⟪expVec w, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ := by
  simp only [inner_expVec_squeeze_expVec]
  have hc : ∀ j, Continuous fun ζ : ι → ℂ => Real.cosh ‖ζ j‖ := fun j =>
    Real.continuous_cosh.comp (continuous_norm.comp (continuous_apply j))
  have hc' : ∀ j, Continuous fun ζ : ι → ℂ => (Real.cosh ‖ζ j‖ : ℂ) := fun j =>
    Complex.continuous_ofReal.comp (hc j)
  have ht : ∀ j, Continuous fun ζ : ι → ℂ => tanhPhase (ζ j) := fun j =>
    continuous_tanhPhase.comp (continuous_apply j)
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · exact Complex.continuous_ofReal.comp ((continuous_finsetProd _ fun j _ => hc j).rpow_const
      fun ζ => Or.inl (prod_pos fun j _ => Real.cosh_pos _).ne')
  · exact Complex.continuous_exp.comp (continuous_finsetSum _ fun j _ =>
      ((Complex.continuous_conj.comp (ht j)).mul continuous_const).div_const _)
  · refine Complex.continuous_exp.comp (continuous_finsetSum _ fun j _ => ?_)
    refine (((ht j).neg.div_const _).mul continuous_const).add ?_
    exact (continuous_const.div (hc' j) fun ζ => Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne').mul
      continuous_const

/-- Weak continuity on exponential vectors: `ζ ↦ ⟨x, S(ζ) ε(z)⟩` is continuous for every `x`. -/
private theorem continuous_inner_squeeze_expVec (x : FockSpace ι) (z : ι → ℂ) :
    Continuous fun ζ : ι → ℂ =>
      ⟪x, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ := by
  set E := Submodule.span ℂ (Set.range (expVec (ι := ι)))
  have hE : ∀ y ∈ E, Continuous fun ζ : ι → ℂ =>
      ⟪y, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact continuous_inner_expVec_squeeze_expVec w z
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [inner_add_left]; exact hx.add hy
    | smul c x _ hx => simp only [inner_smul_left]; exact continuous_const.mul hx
  have hequi : Equicontinuous fun ζ : ι → ℂ => fun y : FockSpace ι =>
      ⟪y, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ :=
    (LipschitzWith.uniformEquicontinuous _ ‖expVec z‖₊ fun ζ =>
      LipschitzWith.of_dist_le_mul fun y y' => by
        rw [dist_eq_norm, dist_eq_norm, ← inner_sub_left, coe_nnnorm, mul_comm]
        refine (norm_inner_le_norm _ _).trans_eq ?_
        rw [Unitary.norm_map]).equicontinuous
  refine continuous_iff_continuousAt.2 fun ζ₀ => ?_
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := nhds ζ₀)
    (continuous_id.inner continuous_const :
      Continuous fun y : FockSpace ι =>
        ⟪y, (squeeze ζ₀ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ)
  have hsub : closure (E : Set (FockSpace ι)) ⊆ _ :=
    hclosed.closure_subset_iff.2 fun y hy => (hE y hy).continuousAt
  exact hsub ((dense_span_expVec (ι := ι)).closure_eq ▸ Set.mem_univ x)

/-- Strong continuity on exponential vectors, from weak continuity and isometry. -/
private theorem continuous_squeeze_expVec (z : ι → ℂ) :
    Continuous fun ζ : ι → ℂ => (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z) := by
  refine continuous_iff_continuousAt.2 fun ζ₀ => ?_
  set v₀ := (squeeze ζ₀ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)
  have hn : ∀ ζ : ι → ℂ, ‖(squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)‖ =
      ‖expVec z‖ := fun ζ => Unitary.norm_map _ _
  have hg : Continuous fun ζ : ι → ℂ =>
      2 * ‖expVec z‖ ^ 2 - 2 * RCLike.re ⟪v₀, (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι)
        (expVec z)⟫_ℂ :=
    continuous_const.sub (continuous_const.mul
      (RCLike.continuous_re.comp (continuous_inner_squeeze_expVec v₀ z)))
  have hsq : ∀ ζ : ι → ℂ, ‖(squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z) - v₀‖ =
      Real.sqrt (2 * ‖expVec z‖ ^ 2 - 2 * RCLike.re ⟪v₀,
        (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (expVec z)⟫_ℂ) := fun ζ => by
    rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq ℂ, hn, hn, ← inner_conj_symm,
      RCLike.conj_re]
    congr 1
    ring
  have ht := (Real.continuous_sqrt.comp hg).tendsto ζ₀
  rw [Function.comp_apply, ← hsq ζ₀, sub_self, norm_zero] at ht
  exact tendsto_iff_norm_sub_tendsto_zero.2 (Filter.Tendsto.congr (fun ζ => (hsq ζ).symm) ht)

/-- **Theorem 17(b).** Strong continuity: `ζ ↦ S(ζ) ψ` is continuous for every `ψ ∈ Γ_s`. -/
theorem continuous_squeeze_apply (ψ : FockSpace ι) :
    Continuous fun ζ : ι → ℂ => (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ := by
  set E := Submodule.span ℂ (Set.range (expVec (ι := ι)))
  have hE : ∀ χ ∈ E, Continuous fun ζ : ι → ℂ =>
      (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) χ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact continuous_squeeze_expVec z
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul]; exact hx.const_smul c
  have hequi : Equicontinuous fun ζ : ι → ℂ =>
      ⇑(squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun ζ =>
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, Unitary.norm_map, NNReal.coe_one,
          one_mul]).equicontinuous
  refine continuous_iff_continuousAt.2 fun ζ₀ => ?_
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := nhds ζ₀)
    (squeeze ζ₀ : FockSpace ι →L[ℂ] FockSpace ι).continuous
  have hsub : closure (E : Set (FockSpace ι)) ⊆ _ :=
    hclosed.closure_subset_iff.2 fun χ hχ => (hE χ hχ).continuousAt
  exact hsub ((dense_span_expVec (ι := ι)).closure_eq ▸ Set.mem_univ ψ)

end FockSpace

/-! ### Theorems 20(b) and 21(c): passive transformations and phase absorption -/

namespace FockSpace

open FormalFock
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem ofReal_sum_norm_sq (x : ι → ℂ) : ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) = star x ⬝ᵥ x := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul', Complex.ofReal_sum,
    Complex.ofReal_pow]

/-- **Theorem 20(b), the paper's (30).** `Γ(𝒰)* D(β) Γ(𝒰) = D(𝒰* β)`. -/
theorem star_secondQuantRep_mul_displacement_mul (U : Matrix.unitaryGroup ι ℂ) (β : ι → ℂ) :
    (star (secondQuantRep U) : FockSpace ι →L[ℂ] FockSpace ι) * displacement β *
        secondQuantRep U = displacement ((U : Matrix ι ι ℂ)ᴴ *ᵥ β) := by
  have hU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 U.2
  have hU' : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.1 U.2
  have hdot : ∀ v w : ι → ℂ, ∑ j, conj (v j) * w j = star v ⬝ᵥ w := fun _ _ => rfl
  refine ext_expVec fun z => ?_
  rw [star_secondQuantRep, mul_apply_eq_comp, mul_apply_eq_comp,
    secondQuantRep_expVec, displacement_expVec, map_smul, secondQuantRep_expVec,
    displacement_expVec, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, ofReal_sum_norm_sq, ofReal_sum_norm_sq, hdot,
    hdot, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]

/-- **Theorem 20(b)**, commuted: `Γ(𝒰) D(β) = D(𝒰β) Γ(𝒰)`. -/
theorem secondQuantRep_mul_displacement (U : Matrix.unitaryGroup ι ℂ) (β : ι → ℂ) :
    (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) *
        (displacement β : FockSpace ι →L[ℂ] FockSpace ι) =
      (displacement ((U : Matrix ι ι ℂ) *ᵥ β) :
        FockSpace ι →L[ℂ] FockSpace ι) *
        (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) := by
  have hU : (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) *
      star (secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) = 1 :=
    Unitary.mul_star_self_of_mem (secondQuantRep U).2
  have h := star_secondQuantRep_mul_displacement_mul U ((U : Matrix ι ι ℂ) *ᵥ β)
  rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem U.2,
    Matrix.one_mulVec] at h
  rw [← h]
  simp only [← mul_assoc, hU, one_mul]

/-- **Theorem 21(c), phase absorption.** If `|ζⱼ| e^{-2iθⱼ} = ζⱼ` for every `j`, then
`S(ζ) = R(θ) S(|ζ|) R(θ)*`, with `R(θ) = Γ(diag(e^{-iθⱼ}))`. -/
theorem squeeze_eq_rotation_mul_squeeze_norm_mul (ζ : ι → ℂ) (θ : ι → ℝ)
    (hθ : ∀ j, (‖ζ j‖ : ℂ) * Complex.exp (-(θ j : ℂ) * Complex.I) ^ 2 = ζ j) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) =
      (rotation θ : FockSpace ι →L[ℂ] FockSpace ι) * squeeze (fun j => (‖ζ j‖ : ℂ)) *
        (star (rotation θ) : FockSpace ι →L[ℂ] FockSpace ι) := by
  have h : squeeze ζ =
      rotation θ * squeeze (fun j => (‖ζ j‖ : ℂ)) * star (rotation θ) := by
    refine eq_of_conj_eq_of_inner_vacuum _ _ (fun α => ?_) ?_ ?_
    · have e : ∀ A B C X P Q R : FockSpace ι →L[ℂ] FockSpace ι,
          A * (B * C) * X * (P * Q * R) = A * (B * (C * X * P) * Q) * R := fun _ _ _ _ _ _ _ => by
        simp only [mul_assoc]
      have hR : (rotation θ : FockSpace ι →L[ℂ] FockSpace ι) =
          star (secondQuantRep (star (phaseDiag θ)) : FockSpace ι →L[ℂ] FockSpace ι) := by
        rw [star_secondQuantRep, star_star]
        rfl
      rw [star_squeeze_mul_displacement_mul, ← Unitary.coe_star, star_mul, star_mul, star_star,
        MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, e,
        Unitary.coe_star, Unitary.coe_star, rotation, star_secondQuantRep_mul_displacement_mul,
        star_squeeze_mul_displacement_mul, star_secondQuantRep, ← rotation, hR,
        star_secondQuantRep_mul_displacement_mul]
      congr 2
      funext j
      have hsq : ∀ ξ : ι → ℂ, ∀ γ : ι → ℂ, ∀ k,
          squeezeMap (-ξ) γ k = (Real.cosh ‖ξ k‖ : ℂ) * γ k + sinhPhase (ξ k) * conj (γ k) :=
        fun ξ γ k => by
          change (Real.cosh ‖-ξ k‖ : ℂ) * γ k - sinhPhase (-ξ k) * conj (γ k) = _
          rw [norm_neg, sinhPhase_neg, neg_mul, sub_neg_eq_add]
      have hΘv : ((phaseDiag θ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
          Matrix.diagonal fun j => Complex.exp (-(θ j : ℂ) * Complex.I) := rfl
      rw [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
        hΘv, Matrix.mulVec_diagonal, hsq, hsq, Matrix.diagonal_conjTranspose,
        Matrix.mulVec_diagonal, Complex.norm_real, Real.norm_eq_abs, abs_norm, Pi.star_apply,
        RCLike.star_def]
      have hu1 : Complex.exp (-(θ j : ℂ) * Complex.I) *
          conj (Complex.exp (-(θ j : ℂ) * Complex.I)) = 1 := by
        rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, map_neg, Complex.conj_ofReal,
          Complex.conj_I, ← Complex.exp_zero]
        congr 1
        ring
      rcases eq_or_ne (ζ j) 0 with hz | hz
      · simp only [hz, norm_zero, Complex.ofReal_zero, sinhPhase, ↓reduceIte, zero_mul, add_zero,
          Real.cosh_zero, Complex.ofReal_one, one_mul]
        linear_combination (-α j) * hu1
      have hn : (‖ζ j‖ : ℂ) ≠ 0 := by simpa using hz
      have hs : sinhPhase (‖ζ j‖ : ℂ) = (Real.sinh ‖ζ j‖ : ℂ) := by
        rw [sinhPhase, ite_eq_right hn, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self hn, one_mul]
      have hs' : sinhPhase (ζ j) = Complex.exp (-(θ j : ℂ) * Complex.I) ^ 2 *
          (Real.sinh ‖ζ j‖ : ℂ) := by
        have h2 : ζ j / (‖ζ j‖ : ℂ) = Complex.exp (-(θ j : ℂ) * Complex.I) ^ 2 := by
          rw [div_eq_iff hn, mul_comm]
          exact (hθ j).symm
        rw [sinhPhase, ite_eq_right hz, h2]
      rw [hs, hs', map_mul, Complex.conj_conj]
      linear_combination (-((Real.cosh ‖ζ j‖ : ℂ) * α j)) * hu1
    · rw [inner_vacuum_squeeze_vacuum, MulMemClass.coe_mul, MulMemClass.coe_mul,
        mul_apply_eq_comp, mul_apply_eq_comp, Unitary.coe_star, rotation, star_secondQuantRep,
        secondQuantRep_vacuum, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.star_eq_adjoint, star_secondQuantRep, secondQuantRep_vacuum,
        inner_vacuum_squeeze_vacuum]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    · rw [MulMemClass.coe_mul, MulMemClass.coe_mul, mul_apply_eq_comp, mul_apply_eq_comp,
        Unitary.coe_star, rotation, star_secondQuantRep, secondQuantRep_vacuum,
        ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        star_secondQuantRep, secondQuantRep_vacuum, inner_vacuum_squeeze_vacuum]
      exact Complex.ofReal_ne_zero.2
        (Real.rpow_pos_of_pos (prod_pos fun j _ => Real.cosh_pos _) _).ne'
  rw [h, MulMemClass.coe_mul, MulMemClass.coe_mul, Unitary.coe_star]

/-- `|ζ| (e^{iφ/2})² = ζ` with `φ = arg ζ`. -/
private theorem norm_mul_exp_half_arg_sq (ζ : ℂ) :
    (‖ζ‖ : ℂ) * Complex.exp (-((-(Complex.arg ζ / 2) : ℝ) : ℂ) * Complex.I) ^ 2 = ζ := by
  rw [← Complex.exp_nat_mul]
  convert Complex.norm_mul_exp_arg_mul_I ζ using 3
  push_cast
  ring

/-- **Theorem 21(c), phase absorption**, the proposal's form: `S(ζ) = Γ(Θ) S(|ζ|) Γ(Θ)*` with
`Θ = diag(e^{iφⱼ/2})`, `φⱼ = arg ζⱼ`; the case `θⱼ = -φⱼ/2` of
`squeeze_eq_rotation_mul_squeeze_norm_mul`. -/
theorem squeeze_eq_conj (ζ : ι → ℂ) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) =
      (secondQuantRep (phaseDiag fun j => -(Complex.arg (ζ j) / 2)) :
        FockSpace ι →L[ℂ] FockSpace ι) * squeeze (fun j => (‖ζ j‖ : ℂ)) *
          (star (secondQuantRep (phaseDiag fun j => -(Complex.arg (ζ j) / 2))) :
            FockSpace ι →L[ℂ] FockSpace ι) :=
  squeeze_eq_rotation_mul_squeeze_norm_mul ζ _ fun j => norm_mul_exp_half_arg_sq (ζ j)

end FockSpace

/-! ### Theorem 16: intertwining with the ladder operators -/

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- `aⱼ aₖ†² = aₖ†² aⱼ + 2δⱼₖ aₖ†`. -/
theorem annihilate_mul_create_sq (j k : ι) :
    (annihilate j : Module.End ℂ (FormalFock ι ℂ)) * create k ^ 2 =
      create k ^ 2 * annihilate j + if j = k then (2 : ℂ) • create k else 0 := by
  have hac : ∀ j k : ι, (annihilate j : Module.End ℂ (FormalFock ι ℂ)) * create k =
      create k * annihilate j + if j = k then 1 else 0 := fun j k => by
    rw [← sub_eq_iff_eq_add', ← Ring.lie_def, lie_annihilate_create (R := ℂ)]
  have h := hac j k
  rw [sq, ← mul_assoc, h, add_mul, mul_assoc, h, mul_add, ← mul_assoc]
  split_ifs <;>
    simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, two_smul, mul_assoc, add_assoc]

omit [Fintype ι] in
/-- `aₖ² aⱼ† = aⱼ† aₖ² + 2δₖⱼ aₖ`. -/
theorem annihilate_sq_mul_create (k j : ι) :
    (annihilate k : Module.End ℂ (FormalFock ι ℂ)) ^ 2 * create j =
      create j * annihilate k ^ 2 + if k = j then (2 : ℂ) • annihilate k else 0 := by
  have hac : ∀ j k : ι, (annihilate j : Module.End ℂ (FormalFock ι ℂ)) * create k =
      create k * annihilate j + if j = k then 1 else 0 := fun j k => by
    rw [← sub_eq_iff_eq_add', ← Ring.lie_def, lie_annihilate_create (R := ℂ)]
  have h := hac k j
  rw [sq, mul_assoc, h, mul_add, ← mul_assoc, h, add_mul, mul_assoc]
  split_ifs
  · simp only [mul_one, one_mul, two_smul, add_assoc]
  · simp only [mul_zero, zero_mul, add_zero]

omit [DecidableEq ι] in
/-- `aⱼ (-½ Σₖ τₖ aₖ†²) = (-½ Σₖ τₖ aₖ†²) aⱼ - τⱼ aⱼ†`. -/
theorem annihilate_mul_raiseSqueeze (τ : ι → ℂ) (j : ι) :
    annihilate j * (raiseSqueeze τ).op =
      (raiseSqueeze τ).op * annihilate j + (-τ j) • create j := by
  classical
  rw [raiseSqueeze_op, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_smul_comm, annihilate_mul_create_sq, smul_add, smul_mul_assoc]
  rw [sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp), ite_eq_left rfl,
    smul_smul]
  congr 1
  ring

omit [DecidableEq ι] in
/-- `aⱼ†` commutes with `-½ Σₖ τₖ aₖ†²`. -/
theorem commute_create_raiseSqueeze (τ : ι → ℂ) (j : ι) :
    Commute (create j : Module.End ℂ (FormalFock ι ℂ)) (raiseSqueeze τ).op := by
  classical
  rw [raiseSqueeze_op]
  exact Commute.sum_right _ _ _ fun k _ =>
    ((commute_iff_lie_eq.2 (lie_create_create (R := ℂ) j k)).pow_right 2).smul_right _

omit [DecidableEq ι] in
/-- `aⱼ` commutes with `½ Σₖ τ̄ₖ aₖ²`. -/
theorem commute_annihilate_lowerSqueeze (τ : ι → ℂ) (j : ι) :
    Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) (lowerSqueeze τ) := by
  rw [lowerSqueeze]
  exact Commute.sum_right _ _ _ fun k _ =>
    ((commute_annihilate_annihilate j k).pow_right 2).smul_right _

omit [DecidableEq ι] in
/-- `(½ Σₖ τ̄ₖ aₖ²) aⱼ† = aⱼ† (½ Σₖ τ̄ₖ aₖ²) + τ̄ⱼ aⱼ`. -/
theorem lowerSqueeze_mul_create (τ : ι → ℂ) (j : ι) :
    lowerSqueeze τ * create j = create j * lowerSqueeze τ + conj (τ j) • annihilate j := by
  classical
  rw [lowerSqueeze, Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, annihilate_sq_mul_create, smul_add, mul_smul_comm]
  rw [sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), ite_eq_left rfl, smul_smul]
  congr 1
  ring

/-- `aⱼ Γ(diag d) = dⱼ Γ(diag d) aⱼ`. -/
theorem annihilate_secondQuant_diagonal (d : ι → ℂ) (j : ι) (ψ : FormalFock ι ℂ) :
    annihilate j (secondQuant (Matrix.diagonal d) ψ) =
      d j • secondQuant (Matrix.diagonal d) (annihilate j ψ) := by
  rw [← Module.End.mul_apply, annihilate_mul_secondQuant, Module.End.mul_apply,
    Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.diagonal_apply_ne d (Ne.symm hk),
      zero_smul]) (by simp), Matrix.diagonal_apply_eq, LinearMap.smul_apply, map_smul]

/-- `Γ(diag d) aⱼ† = dⱼ aⱼ† Γ(diag d)`. -/
theorem secondQuant_diagonal_create (d : ι → ℂ) (j : ι) (ψ : FormalFock ι ℂ) :
    secondQuant (Matrix.diagonal d) (create j ψ) =
      d j • create j (secondQuant (Matrix.diagonal d) ψ) := by
  rw [← Module.End.mul_apply, secondQuant_mul_create, Module.End.mul_apply,
    Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.diagonal_apply_ne d hk, zero_smul])
      (by simp), Matrix.diagonal_apply_eq, LinearMap.smul_apply]

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 16 (intertwining).** If `aⱼ ψ = φ` and `aⱼ† ψ = φ'` with `ψ, φ, φ' ∈ Γ_s`, then
`aⱼ S(ζ) ψ = S(ζ)(cⱼ φ - e^{iφⱼ} sⱼ φ')`: on the domain of the maximal realization,
`S(ζ)* aⱼ S(ζ) = cⱼ aⱼ - e^{iφⱼ} sⱼ aⱼ†`, the paper's `S† a S = a cosh r - a† e^{iφ} sinh r`. -/
theorem annihilate_squeeze (ζ : ι → ℂ) (j : ι) {ψ φ φ' : FockSpace ι}
    (h : annihilate j (toFormal ψ) = toFormal φ) (h' : create j (toFormal ψ) = toFormal φ') :
    annihilate j (toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
      toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι)
        ((Real.cosh ‖ζ j‖ : ℂ) • φ -
          ((if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ)) • φ')) := by
  change annihilate j _ = toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι)
    ((Real.cosh ‖ζ j‖ : ℂ) • φ - sinhPhase (ζ j) • φ'))
  have hτ : ∀ k, ‖tanhPhase (ζ k)‖ < 1 := fun k => norm_tanhPhase_lt_one (ζ k)
  have hT : ∀ n, ∃ χ : FockSpace ι, ∀ ψ : FockSpace ι,
      (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ :=
    fun n => let ⟨χ, _, hχ⟩ := coeff_coeffExp_lowerSqueeze hτ n; ⟨χ, hχ⟩
  -- `aⱼ† e^Λ ψ = e^Λ φ' - τ̄ⱼ e^Λ φ`
  have hC : create j (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal ψ)) =
      coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ') -
        conj (tanhPhase (ζ j)) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ) := by
    ext n
    have hCψ : (conj (tanhPhase (ζ j)) • annihilate j : Module.End ℂ (FormalFock ι ℂ))
        (toFormal ψ) = toFormal (conj (tanhPhase (ζ j)) • φ) := by
      rw [LinearMap.smul_apply, h, map_smul]
    have h1 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        (((lowerSqueeze fun k => tanhPhase (ζ k)) ^ r) (toFormal ψ)).coeff
          (n - Finsupp.single j 1) :=
      (summable_coeffExp_lowerSqueeze hτ ψ _).of_norm
    have h2 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        (((lowerSqueeze fun k => tanhPhase (ζ k)) ^ r)
          ((conj (tanhPhase (ζ j)) • annihilate j : Module.End ℂ (FormalFock ι ℂ))
            (toFormal ψ))).coeff n := by
      rw [hCψ]
      exact (summable_coeffExp_lowerSqueeze hτ _ n).of_norm
    have := coeff_coeffExp_create j (lowerSqueeze_mul_create _ j)
      ((commute_annihilate_lowerSqueeze _ j).smul_left _) n h1 h2
    rw [h', hCψ, map_smul, coeffExp_smul] at this
    rw [coeff_sub, this, coeff_smul, smul_eq_mul]
    ring
  have hd : ∀ x : FormalFock ι ℂ,
      create j (secondQuant (coshInvDiag ζ) x) =
        (Real.cosh ‖ζ j‖ : ℂ) • secondQuant (coshInvDiag ζ) (create j x) := fun x => by
    rw [coshInvDiag, secondQuant_diagonal_create, smul_smul]
    have hc : (Real.cosh ‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hc, one_smul]
  have hlin : coeffExp (lowerSqueeze fun k => tanhPhase (ζ k))
      (toFormal ((Real.cosh ‖ζ j‖ : ℂ) • φ - sinhPhase (ζ j) • φ')) =
      (Real.cosh ‖ζ j‖ : ℂ) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ) -
        sinhPhase (ζ j) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ') := by
    rw [sub_eq_add_neg, ← neg_smul, coeffExp_toFormal_add hT, map_smul, coeffExp_smul, map_smul,
      coeffExp_smul, neg_smul, ← sub_eq_add_neg]
  simp only [toFormal_squeeze]
  rw [orderedSqueeze, orderedSqueeze, map_smul,
    annihilate_exp_eq _ j (annihilate_mul_raiseSqueeze _ j)
      ((commute_create_raiseSqueeze _ j).smul_left _), ← map_add, hlin]
  congr 2
  rw [LinearMap.smul_apply, hd, hC, coshInvDiag, annihilate_secondQuant_diagonal,
    annihilate_coeffExp_of_commute j (commute_annihilate_lowerSqueeze _ j), h]
  simp only [map_sub, map_smul, smul_sub, smul_smul]
  have hc : (Real.cosh ‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
  have e1 : (((Real.cosh ‖ζ j‖)⁻¹ : ℝ) : ℂ) +
      -tanhPhase (ζ j) * ((Real.cosh ‖ζ j‖ : ℂ) * -conj (tanhPhase (ζ j))) =
      (Real.cosh ‖ζ j‖ : ℂ) := by
    rw [tanhPhase_eq_sinhPhase_div, map_div₀, Complex.conj_ofReal, Complex.ofReal_inv]
    have := cosh_sq_sub_conj_sinhPhase_mul_self (ζ j)
    field_simp
    linear_combination -this
  have e2 : -tanhPhase (ζ j) * (Real.cosh ‖ζ j‖ : ℂ) = -sinhPhase (ζ j) := by
    rw [tanhPhase_eq_sinhPhase_div]
    field_simp
  linear_combination (norm := module)
    e1 • secondQuant (Matrix.diagonal fun k => (((Real.cosh ‖ζ k‖)⁻¹ : ℝ) : ℂ))
      (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ)) +
    e2 • secondQuant (Matrix.diagonal fun k => (((Real.cosh ‖ζ k‖)⁻¹ : ℝ) : ℂ))
      (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ'))

/-- **Theorem 16**, the creation operator: if `aⱼ ψ = φ` and `aⱼ† ψ = φ'` with
`ψ, φ, φ' ∈ Γ_s`, then `aⱼ† S(ζ) ψ = S(ζ)(cⱼ φ' - e^{-iφⱼ} sⱼ φ)`. -/
theorem create_squeeze (ζ : ι → ℂ) (j : ι)
    {ψ φ φ' : FockSpace ι} (h : annihilate j (toFormal ψ) = toFormal φ)
    (h' : create j (toFormal ψ) = toFormal φ') :
    create j (toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
      toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι)
        ((Real.cosh ‖ζ j‖ : ℂ) • φ' -
          conj ((if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ)) • φ)) := by
  change create j _ = toFormal ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι)
    ((Real.cosh ‖ζ j‖ : ℂ) • φ' - conj (sinhPhase (ζ j)) • φ))
  have hτ : ∀ k, ‖tanhPhase (ζ k)‖ < 1 := fun k => norm_tanhPhase_lt_one (ζ k)
  have hT : ∀ n, ∃ χ : FockSpace ι, ∀ ψ : FockSpace ι,
      (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal ψ)).coeff n = ⟪χ, ψ⟫_ℂ :=
    fun n => let ⟨χ, _, hχ⟩ := coeff_coeffExp_lowerSqueeze hτ n; ⟨χ, hχ⟩
  have hC : create j (coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal ψ)) =
      coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ') -
        conj (tanhPhase (ζ j)) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ) := by
    ext n
    have hCψ : (conj (tanhPhase (ζ j)) • annihilate j : Module.End ℂ (FormalFock ι ℂ))
        (toFormal ψ) = toFormal (conj (tanhPhase (ζ j)) • φ) := by
      rw [LinearMap.smul_apply, h, map_smul]
    have h1 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        (((lowerSqueeze fun k => tanhPhase (ζ k)) ^ r) (toFormal ψ)).coeff
          (n - Finsupp.single j 1) :=
      (summable_coeffExp_lowerSqueeze hτ ψ _).of_norm
    have h2 : Summable fun r : ℕ => ((r.factorial : ℂ)⁻¹) *
        (((lowerSqueeze fun k => tanhPhase (ζ k)) ^ r)
          ((conj (tanhPhase (ζ j)) • annihilate j : Module.End ℂ (FormalFock ι ℂ))
            (toFormal ψ))).coeff n := by
      rw [hCψ]
      exact (summable_coeffExp_lowerSqueeze hτ _ n).of_norm
    have := coeff_coeffExp_create j (lowerSqueeze_mul_create _ j)
      ((commute_annihilate_lowerSqueeze _ j).smul_left _) n h1 h2
    rw [h', hCψ, map_smul, coeffExp_smul] at this
    rw [coeff_sub, this, coeff_smul, smul_eq_mul]
    ring
  have hd : ∀ x : FormalFock ι ℂ,
      create j (secondQuant (coshInvDiag ζ) x) =
        (Real.cosh ‖ζ j‖ : ℂ) • secondQuant (coshInvDiag ζ) (create j x) := fun x => by
    rw [coshInvDiag, secondQuant_diagonal_create, smul_smul]
    have hc : (Real.cosh ‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hc, one_smul]
  have hlin : coeffExp (lowerSqueeze fun k => tanhPhase (ζ k))
      (toFormal ((Real.cosh ‖ζ j‖ : ℂ) • φ' - conj (sinhPhase (ζ j)) • φ)) =
      (Real.cosh ‖ζ j‖ : ℂ) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ') -
        conj (sinhPhase (ζ j)) • coeffExp (lowerSqueeze fun k => tanhPhase (ζ k)) (toFormal φ) := by
    rw [sub_eq_add_neg, ← neg_smul, coeffExp_toFormal_add hT, map_smul, coeffExp_smul, map_smul,
      coeffExp_smul, neg_smul, ← sub_eq_add_neg]
  have hcτ : (Real.cosh ‖ζ j‖ : ℂ) * conj (tanhPhase (ζ j)) = conj (sinhPhase (ζ j)) := by
    rw [tanhPhase_eq_sinhPhase_div, map_div₀, Complex.conj_ofReal]
    have hc : (Real.cosh ‖ζ j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.cosh_pos _).ne'
    field_simp
  simp only [toFormal_squeeze]
  rw [orderedSqueeze, orderedSqueeze, map_smul, ← Module.End.mul_apply (create j),
    (commute_create_exp_of_commute j _ (commute_create_raiseSqueeze _ j)).eq,
    Module.End.mul_apply, hd, hC, hlin]
  simp only [map_sub, map_smul, smul_sub, smul_smul, hcτ]

end FockSpace

namespace FormalFock

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
private theorem enorm_sqrtC_sq (k : ℕ) : (‖sqrtC k‖₊ : ℝ≥0∞) ^ 2 = k := by
  rw [← ENNReal.coe_pow, ← ENNReal.coe_natCast]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_pow, coe_nnnorm, NNReal.coe_natCast, sqrtC, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq ι] in
/-- `‖aⱼ ψ‖² = Σₘ mⱼ |ψ(m)|²` in `[0, ∞]`. -/
theorem sqNorm_annihilate (j : ι) (ψ : FormalFock ι ℂ) :
    sqNorm (annihilate j ψ) = ∑' m, (m j : ℝ≥0∞) * (‖ψ.coeff m‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  have hinj : Function.Injective fun m : ι →₀ ℕ => m + Finsupp.single j 1 :=
    fun a b hab => add_right_cancel hab
  have hsupp : Function.support (fun m : ι →₀ ℕ => (m j : ℝ≥0∞) * (‖ψ.coeff m‖₊ : ℝ≥0∞) ^ 2) ⊆
      Set.range fun m : ι →₀ ℕ => m + Finsupp.single j 1 := by
    intro m hm
    have h0 : m j ≠ 0 := fun h => hm (by simp [h])
    refine ⟨m - Finsupp.single j 1, ?_⟩
    ext k
    by_cases hk : k = j
    · subst hk
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same]
      omega
    · simp [Ne.symm hk]
  rw [← hinj.tsum_eq hsupp, sqNorm]
  refine tsum_congr fun n => ?_
  rw [coeff_annihilate, nnnorm_smul, ENNReal.coe_mul, mul_pow, enorm_sqrtC_sq]
  simp

omit [DecidableEq ι] in
/-- `‖aⱼ† ψ‖² = ‖aⱼ ψ‖² + ‖ψ‖²` in `[0, ∞]`. -/
theorem sqNorm_create (j : ι) (ψ : FormalFock ι ℂ) :
    sqNorm (create j ψ) = sqNorm (annihilate j ψ) + sqNorm ψ := by
  classical
  have hinj : Function.Injective fun m : ι →₀ ℕ => m + Finsupp.single j 1 :=
    fun a b hab => add_right_cancel hab
  have hsupp : Function.support (fun n => (‖(create j ψ).coeff n‖₊ : ℝ≥0∞) ^ 2) ⊆
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
  rw [sqNorm, ← hinj.tsum_eq hsupp, sqNorm_annihilate, sqNorm, ← ENNReal.tsum_add]
  refine tsum_congr fun m => ?_
  rw [coeff_create, ite_eq_left (by simp), nnnorm_smul, ENNReal.coe_mul, mul_pow,
    enorm_sqrtC_sq, add_tsub_cancel_right]
  simp [add_mul]

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Theorem 16.** The maximal realizations of `aⱼ` and `aⱼ†` have the same domain, since
`‖aⱼ† ψ‖² = ‖aⱼ ψ‖² + ‖ψ‖²`. -/
theorem maxDomain_create (j : ι) :
    maxDomain (create j : Module.End ℂ (FormalFock ι ℂ)) = maxDomain (annihilate j) := by
  classical
  ext ψ
  change Memℓp (create j (toFormal ψ)).coeff 2 ↔ Memℓp (annihilate j (toFormal ψ)).coeff 2
  have hψ := (memℓp_coeff_iff_sqNorm_lt_top (toFormal ψ)).1 (lp.memℓp ψ)
  rw [memℓp_coeff_iff_sqNorm_lt_top, memℓp_coeff_iff_sqNorm_lt_top, sqNorm_create,
    ENNReal.add_lt_top]
  tauto

/-- **Theorem 16.** `S(ζ)` maps the domain of the maximal realization of `aⱼ` (equivalently of
`aⱼ†`, `maxDomain_create`) onto itself. -/
theorem squeeze_mem_maxDomain_iff (ζ : ι → ℂ) (j : ι) (ψ : FockSpace ι) :
    (squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ ∈ maxDomain (annihilate j) ↔
      ψ ∈ maxDomain (annihilate j) := by
  have key : ∀ (ξ : ι → ℂ) (χ : FockSpace ι), χ ∈ maxDomain (annihilate j) →
      (squeeze ξ : FockSpace ι →L[ℂ] FockSpace ι) χ ∈ maxDomain (annihilate j) := by
    intro ξ χ hχ
    have hχ' : χ ∈ maxDomain (create j : Module.End ℂ (FormalFock ι ℂ)) := by
      rwa [maxDomain_create]
    obtain ⟨φ, hφ⟩ : ∃ φ : FockSpace ι, annihilate j (toFormal χ) = toFormal φ :=
      ⟨⟨(annihilate j (toFormal χ)).coeff, hχ⟩, rfl⟩
    obtain ⟨φ', hφ'⟩ : ∃ φ' : FockSpace ι, create j (toFormal χ) = toFormal φ' :=
      ⟨⟨(create j (toFormal χ)).coeff, hχ'⟩, rfl⟩
    change Memℓp (annihilate j (toFormal ((squeeze ξ : FockSpace ι →L[ℂ] FockSpace ι) χ))).coeff 2
    rw [annihilate_squeeze ξ j hφ hφ', show ∀ x : FockSpace ι, (toFormal x).coeff = ⇑x from
      fun _ => rfl]
    exact lp.memℓp _
  refine ⟨fun h => ?_, key ζ ψ⟩
  have h2 := key (-ζ) _ h
  have hinv : (squeeze (-ζ) : FockSpace ι →L[ℂ] FockSpace ι)
      ((squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ) = ψ := by
    have h1 := squeeze_mul_neg (-ζ)
    rw [neg_neg] at h1
    exact congrArg (fun u : unitary (FockSpace ι →L[ℂ] FockSpace ι) =>
      (u : FockSpace ι →L[ℂ] FockSpace ι) ψ) h1
  rwa [hinv] at h2

end FockSpace

/-! ### Theorem 17(c): the generator -/

/-- `t ↦ τ(tζ)` has derivative `ζ` at `t = 0`. -/
theorem hasDerivAt_tanhPhase_ofReal_mul (ζ : ℂ) :
    HasDerivAt (fun t : ℝ => tanhPhase ((t : ℂ) * ζ)) ζ 0 := by
  have hcosh : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  have ht : HasDerivAt (fun t : ℝ => Real.tanh (t * ‖ζ‖)) ‖ζ‖ 0 := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    have h1 := ((hasDerivAt_id' (0 : ℝ)).mul_const ‖ζ‖).sinh
    have h2 := ((hasDerivAt_id' (0 : ℝ)).mul_const ‖ζ‖).cosh
    convert h1.div h2 (hcosh _) using 1
    simp
  simp only [tanhPhase_ofReal_mul]
  convert (ht.ofReal_comp).const_mul (if ζ = 0 then 0 else ζ / (‖ζ‖ : ℂ)) using 1
  split_ifs with h
  · simp [h]
  · have hn : (‖ζ‖ : ℂ) ≠ 0 := by simpa using h
    field_simp

/-- `τ(0) = 0`. -/
private theorem tanhPhase_ofReal_zero_mul (ζ : ℂ) : tanhPhase (((0 : ℝ) : ℂ) * ζ) = 0 := by
  simp [tanhPhase_zero]

namespace FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- `(aⱼ² ψ)(m) = √(mⱼ + 1) √(mⱼ + 2) ψ(m + 2eⱼ)`. -/
theorem coeff_annihilate_sq (j : ι) (ψ : FormalFock ι ℂ) (m : ι →₀ ℕ) :
    ((annihilate j ^ 2) ψ).coeff m = sqrtC (m j + 1) *
      sqrtC ((m + Finsupp.single j 1 : ι →₀ ℕ) j + 1) *
        ψ.coeff (m + Finsupp.single j 1 + Finsupp.single j 1) := by
  rw [sq, Module.End.mul_apply, coeff_annihilate, coeff_annihilate, smul_eq_mul, smul_eq_mul,
    mul_assoc]

omit [DecidableEq ι] in
/-- `½ Σⱼ τ̄ⱼ aⱼ²` removes particles. -/
theorem lowerSqueeze_lowers (τ : ι → ℂ) (e s : ℕ) (ψ : FormalFock ι ℂ)
    (h : ∀ p : ι →₀ ℕ, e < p.degree + s → ψ.coeff p = 0) :
    ∀ p : ι →₀ ℕ, e < p.degree + (s + 1) → (lowerSqueeze τ ψ).coeff p = 0 := fun p hp => by
  rw [lowerSqueeze, LinearMap.sum_apply, coeff_sum]
  refine sum_eq_zero fun j _ => ?_
  rw [LinearMap.smul_apply, coeff_smul, sq, Module.End.mul_apply,
    annihilate_vanishes (annihilate_vanishes h j) j p (by omega), smul_zero]

omit [DecidableEq ι] in
/-- The coefficients of `(½ Σⱼ τ̄ⱼ(t) aⱼ²)ᵏ ψ`, `τ(t) = τ(tζ₀)`, at `t = 0`: derivative
`(½ Σⱼ ζ̄₀ⱼ aⱼ² ψ)(m)` for `k = 1` and `0` otherwise. -/
theorem hasDerivAt_coeff_lowerSqueeze_pow (ζ₀ : ι → ℂ) (ψ : FormalFock ι ℂ) (k : ℕ) :
    ∀ m : ι →₀ ℕ, HasDerivAt (fun t : ℝ =>
      (((lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j)) ^ k) ψ).coeff m)
        (if k = 1 then (lowerSqueeze ζ₀ ψ).coeff m else 0) 0 := by
  have hexp : ∀ (τ : ι → ℂ) (y : FormalFock ι ℂ) (m : ι →₀ ℕ), (lowerSqueeze τ y).coeff m =
      ∑ j, conj (τ j) / 2 * (sqrtC (m j + 1) * sqrtC ((m + Finsupp.single j 1 : ι →₀ ℕ) j + 1) *
        y.coeff (m + Finsupp.single j 1 + Finsupp.single j 1)) := fun τ y m => by
    rw [lowerSqueeze, LinearMap.sum_apply, coeff_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, coeff_smul, coeff_annihilate_sq, smul_eq_mul]
  induction k with
  | zero =>
    intro m
    simpa using hasDerivAt_const (0 : ℝ) (ψ.coeff m)
  | succ k ih =>
    intro m
    simp only [pow_succ', Module.End.mul_apply, hexp]
    have hd := HasDerivAt.fun_sum fun j (_ : j ∈ univ) =>
      (((hasDerivAt_tanhPhase_ofReal_mul (ζ₀ j)).star).div_const 2).mul
        ((ih (m + Finsupp.single j 1 + Finsupp.single j 1)).const_mul
          (sqrtC (m j + 1) * sqrtC ((m + Finsupp.single j 1 : ι →₀ ℕ) j + 1)))
    refine hd.congr_deriv ?_
    simp only [tanhPhase_ofReal_zero_mul, star_zero, zero_div, zero_mul, add_zero]
    rcases k with _ | k
    · simp only [pow_zero, Module.End.one_apply, zero_add, ↓reduceIte]
      rfl
    · simp [tanhPhase_zero, lowerSqueeze]

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- `t ↦ cosh |tζⱼ|` has derivative `0` at `t = 0`. -/
private theorem hasDerivAt_cosh_norm_smul (ζ₀ : ι → ℂ) (j : ι) :
    HasDerivAt (fun t : ℝ => Real.cosh ‖((t : ℂ) • ζ₀) j‖) 0 0 := by
  simp only [Pi.smul_apply, smul_eq_mul, cosh_norm_ofReal_mul]
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const ‖ζ₀ j‖).cosh

/-- **Theorem 17(c)** on a number state. -/
private theorem hasDerivAt_squeeze_smul_single (ζ₀ : ι → ℂ) (n : ι →₀ ℕ) {G : FockSpace ι}
    (hG : toFormal G = (∑ j, ((conj (ζ₀ j) / 2) • annihilate j ^ 2 - (ζ₀ j / 2) • create j ^ 2) :
      Module.End ℂ (FormalFock ι ℂ)) (single n 1)) :
    HasDerivAt (fun t : ℝ => (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι)
      (lp.single 2 n 1)) G 0 := by
  have hvn := vanishesAbove_single n (1 : ℂ)
  -- `W m t = e^{-½ Σⱼ τⱼ(t) aⱼ†²} ∣m⟩` in `Γ_s`, with derivative `-½ Σⱼ ζ₀ⱼ aⱼ†² ∣m⟩` at `0`
  choose W hW using fun (m : ι →₀ ℕ) (t : ℝ) =>
    (mem_range_toFormal_iff ((raiseSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j)).exp
      (single m 1))).2 (sqNorm_raiseSqueeze_exp_lt_top (fun j => norm_tanhPhase_lt_one _) m)
  have hWd : ∀ m, ∃ w : FockSpace ι,
      toFormal w = (gaussRaise (fun j => -ζ₀ j / 2) 0).op (single m 1) ∧
        HasDerivAt (W m) w 0 := by
    intro m
    obtain ⟨w, hw⟩ := exists_toFormal_eq_of_vanishesAbove
      ((vanishesAbove_single m 1).gaussRaise_op (fun j => -ζ₀ j / 2) 0)
    refine ⟨w, hw, hasDerivAt_gaussRaise_exp
      (κ := fun t j => -tanhPhase (((t : ℂ) • ζ₀) j) / 2) (ℓ := fun _ => 0)
      (κ' := fun j => -ζ₀ j / 2) (ℓ' := 0)
      (fun j => ((hasDerivAt_tanhPhase_ofReal_mul (ζ₀ j)).neg).div_const 2)
      (fun j => hasDerivAt_const _ _) (by funext j; simp [tanhPhase_zero]) rfl m
      (fun t => hW m t) hw⟩
  choose R hRf hRd using hWd
  have hW0 : ∀ m, toFormal (W m 0) = single m 1 := fun m => by
    rw [hW, NumberRaisingOp.exp_of_op_eq_zero (by simp [raiseSqueeze_op, tanhPhase_zero])]
    rfl
  -- the lowering part `X t = e^{½ Σⱼ τ̄ⱼ(t) aⱼ²} ∣n⟩`, a finite sum
  have hXsum : ∀ t : ℝ, coeffExp (lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j))
      (single n 1) = ∑ k ∈ range (n.degree + 2), ((k.factorial : ℂ))⁻¹ •
        ((lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j)) ^ k) (single n 1) := fun t =>
    coeffExp_eq_sum_of_lowers (lowerSqueeze_lowers _) hvn (by omega)
  have hXvan : ∀ t : ℝ, VanishesAbove n.degree
      (coeffExp (lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j)) (single n 1)) := by
    intro t
    rw [hXsum t]
    exact vanishesAbove_sum _ fun k _ => VanishesAbove.smul (fun p hp =>
      vanishes_pow_of_lowers (lowerSqueeze_lowers _) hvn k p (by omega)) _
  have hXd : ∀ m, HasDerivAt (fun t : ℝ =>
      (coeffExp (lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j)) (single n 1)).coeff m)
        ((lowerSqueeze ζ₀ (single n 1)).coeff m) 0 := by
    intro m
    simp only [hXsum, coeff_sum, coeff_smul, smul_eq_mul]
    refine (HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_coeff_lowerSqueeze_pow ζ₀ (single n 1) k m).const_mul _).congr_deriv ?_
    rw [sum_eq_single 1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hX0 : ∀ m, (coeffExp (lowerSqueeze fun j => tanhPhase ((((0 : ℝ) : ℂ) • ζ₀) j))
      (single n 1)).coeff m = (single n (1 : ℂ)).coeff m := fun m => by
    rw [hXsum, sum_range_succ']
    simp [tanhPhase_zero, lowerSqueeze]
  -- the scalars
  have hK : HasDerivAt (fun t : ℝ =>
      (((∏ j, Real.cosh ‖((t : ℂ) • ζ₀) j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) 0 0 := by
    have hP := HasDerivAt.fun_finsetProd fun j (_ : j ∈ univ) => hasDerivAt_cosh_norm_smul ζ₀ j
    have := (hP.rpow_const (p := -(1 / 2 : ℝ))
      (Or.inl (prod_pos fun j _ => Real.cosh_pos _).ne')).ofReal_comp
    simpa using this
  have hd : ∀ m : ι →₀ ℕ, HasDerivAt (fun t : ℝ =>
      m.prod fun j k => ((((Real.cosh ‖((t : ℂ) • ζ₀) j‖)⁻¹ : ℝ) : ℂ)) ^ k) 0 0 := by
    intro m
    have := HasDerivAt.fun_finsetProd fun j (_ : j ∈ m.support) =>
      (((hasDerivAt_cosh_norm_smul ζ₀ j).inv (Real.cosh_pos _).ne').ofReal_comp).pow (m j)
    simpa [Finsupp.prod] using this
  -- the expansion
  have hf : (fun t : ℝ => (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι)
      (lp.single 2 n 1)) = fun t : ℝ =>
        ∑ m ∈ (range (n.degree + 1)).biUnion fun d => finsuppAntidiag univ d,
          ((((∏ j, Real.cosh ‖((t : ℂ) • ζ₀) j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((m.prod fun j k => ((((Real.cosh ‖((t : ℂ) • ζ₀) j‖)⁻¹ : ℝ) : ℂ)) ^ k) *
              (coeffExp (lowerSqueeze fun j => tanhPhase (((t : ℂ) • ζ₀) j))
                (single n 1)).coeff m)) • W m t := by
    funext t
    refine toFormal_injective ?_
    rw [toFormal_squeeze, toFormal_lpSingle, orderedSqueeze, coshInvDiag]
    conv_lhs => rw [(hXvan t).eq_sum]
    simp only [map_sum, map_smul, secondQuant_diagonal_single, smul_sum, smul_smul, hW]
    refine sum_congr rfl fun m _ => ?_
    congr 1
    ring
  rw [hf]
  have hD := HasDerivAt.fun_sum fun m (_ : m ∈ (range (n.degree + 1)).biUnion
      fun d => finsuppAntidiag univ d) => (hK.mul ((hd m).mul (hXd m))).smul (hRd m)
  refine hD.congr_deriv (toFormal_injective ?_)
  have hΛ : VanishesAbove n.degree (lowerSqueeze ζ₀ (single n 1)) := fun p hp =>
    lowerSqueeze_lowers ζ₀ n.degree 0 _ (fun q hq => hvn q (by omega)) p (by omega)
  have h1 : ∑ x ∈ (range (n.degree + 1)).biUnion (fun d => finsuppAntidiag univ d),
      (single n (1 : ℂ)).coeff x • (gaussRaise (fun j => -ζ₀ j / 2) 0).op (single x 1) =
        (gaussRaise (fun j => -ζ₀ j / 2) 0).op (single n 1) := by
    conv_rhs => rw [hvn.eq_sum]
    rw [map_sum]
    simp only [map_smul]
  have hK0 : ((((∏ j, Real.cosh ‖((((0 : ℝ)) : ℂ) • ζ₀) j‖) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) = 1 := by
    simp
  have hd0 : ∀ x : ι →₀ ℕ,
      (x.prod fun j k => ((((Real.cosh ‖((((0 : ℝ)) : ℂ) • ζ₀) j‖)⁻¹ : ℝ) : ℂ)) ^ k) = 1 := by
    intro x
    simp [Finsupp.prod]
  simp only [Pi.mul_apply, map_sum, map_add, map_smul, hRf, hW0, hX0, hK0, hd0, one_mul,
    zero_mul, zero_add]
  rw [sum_add_distrib, h1, ← hΛ.eq_sum, hG]
  simp only [gaussRaise_op, lowerSqueeze, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, Pi.zero_apply, zero_smul, add_zero,
    sum_sub_distrib]
  rw [sub_eq_add_neg, add_comm, ← sum_neg_distrib]
  refine congrArg₂ _ rfl (sum_congr rfl fun j _ => ?_)
  rw [← neg_smul, neg_div]

end FockSpace

namespace FockSpace

open FormalFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 17(c).** On a finitely supported `φ`, `t ↦ S(tζ₀) φ` is differentiable at `t = 0`
with derivative the generator `½ Σⱼ (ζ̄₀ⱼ aⱼ² - ζ₀ⱼ aⱼ†²) φ`. -/
theorem hasDerivAt_squeeze_smul (ζ₀ : ι → ℂ) {φ G : FockSpace ι}
    (hφ : (Function.support φ).Finite)
    (hG : toFormal G =
      (∑ j, ((conj (ζ₀ j) / 2) • annihilate j ^ 2 - (ζ₀ j / 2) • create j ^ 2) :
        Module.End ℂ (FormalFock ι ℂ)) (toFormal φ)) :
    HasDerivAt (fun t : ℝ => (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι) φ) G 0 := by
  have hGn : ∀ n : ι →₀ ℕ, ∃ g : FockSpace ι, toFormal g =
      (∑ j, ((conj (ζ₀ j) / 2) • annihilate j ^ 2 - (ζ₀ j / 2) • create j ^ 2) :
        Module.End ℂ (FormalFock ι ℂ)) (single n 1) := fun n => by
    have hvn := vanishesAbove_single n (1 : ℂ)
    refine exists_toFormal_eq_of_vanishesAbove (e := n.degree + 2) fun p hp => ?_
    rw [LinearMap.sum_apply, coeff_sum]
    refine sum_eq_zero fun j _ => ?_
    have h2 : VanishesAbove (n.degree + 2) ((create j ^ 2) (single n 1)) := by
      rw [sq, Module.End.mul_apply]
      exact (hvn.create j).create j
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, coeff_sub, coeff_smul,
      coeff_smul, h2 p hp, sq, Module.End.mul_apply,
      annihilate_vanishes (annihilate_vanishes (s := 0) (fun q hq => hvn q (by omega)) j) j p
        (by omega), smul_zero, smul_zero, sub_zero]
  choose g hg using hGn
  have hGsum : G = ∑ n ∈ hφ.toFinset, φ n • g n := by
    refine toFormal_injective ?_
    rw [hG]
    conv_lhs => rw [eq_sum_lpSingle_of_finite hφ]
    simp only [map_sum, map_smul, toFormal_lpSingle, hg]
  rw [hGsum]
  have hf : (fun t : ℝ => (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι) φ) =
      fun t : ℝ => ∑ n ∈ hφ.toFinset, φ n •
        (squeeze ((t : ℂ) • ζ₀) : FockSpace ι →L[ℂ] FockSpace ι) (lp.single 2 n 1) := by
    funext t
    conv_lhs => rw [eq_sum_lpSingle_of_finite hφ]
    simp only [map_sum, map_smul]
  rw [hf]
  exact HasDerivAt.fun_sum fun n _ =>
    (hasDerivAt_squeeze_smul_single ζ₀ n (hg n)).const_smul (φ n)

end FockSpace

end BosonicLean.Fock
