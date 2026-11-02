/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Cast
import BosonicLean.Analysis.Majorant
import BosonicLean.Analysis.PowerBound

/-!
# The coefficients `Cₙ(K, L)` of `e^{K z²} e^{L z}`

For elements `K`, `L` of a `ℂ`-algebra, `Cₙ(K, L) = Σ_{t ≤ n/2} K^t L^{n-2t} / (t! (n-2t)!)` is the
coefficient of `zⁿ` in `e^{K z²} e^{L z}`, with `K` to the left of `L`. For commuting `K`, `L` it is
`H_n(L, K) / n!`, with `H_n` the two-variable (Kampé de Fériet) Hermite polynomial; in particular
`Cₙ(-1/2, x) = He_n(x) / n!` (`Polynomial.hermite`). Differentiating in `z` gives, coefficientwise,
the Hermite three-term recurrence `(n+2) C_{n+2} = 2 K Cₙ + C_{n+1} L`, with no commutation of `K`
and `L` assumed; at `K = -1/2` it reads `He_{n+2}(x) = x He_{n+1}(x) - (n+1) He_n(x)`. Translating
`L` by a scalar gives the translation formula (Appell property), and differentiating along a ray
`s ↦ Cₙ(K, sL)` gives the Appell derivative rule. In a normed algebra, a power bound of `K` bounds
`‖Cₙ(K, L)‖` by the scalar majorant coefficients `c_n(r, ‖L‖)` (`BosonicLean.majorantCoeff`).

These are the coefficients of a single-mode Gaussian vector `e^{κ a†² + ℓ a†}∣0⟩`, and, with matrix
values, the tensors of a bosonic matrix product state (Tjoa and Cirac). They were introduced in the
companion library GABMPS and moved here with their statements unchanged (GA-BMPS milestone B5, part
B5.3a, Step 0), since the bosonic Fock space needs them.

## Main definitions

* `BosonicLean.cMatrix K L n`: `Cₙ(K, L)`.
* `BosonicLean.cCoeff n t`: the coefficient of `K^t L^{n-2t}` in `Cₙ`, zero when `2t > n`.

## Main results

* `BosonicLean.cMatrix_zero`, `BosonicLean.cMatrix_one`: `C₀ = 1`, `C₁ = L`.
* `BosonicLean.cMatrix_smul_sq_smul`: homogeneity, `Cₙ(λ² K, λ L) = λⁿ Cₙ(K, L)`.
* `BosonicLean.cMatrix_succ_succ`: the Hermite three-term recurrence.
* `BosonicLean.cMatrix_add_smul_one`, `BosonicLean.cMatrix_add_of_commute`: the translation formula.
* `BosonicLean.hasDerivAt_cMatrix_smul`: the Appell derivative rule along a ray,
  `d/dλ C_{n+1}(K, λL) = Cₙ(K, λL) L`.
* `BosonicLean.norm_cMatrix_le`: `‖Cₙ(Q, P)‖ ≤ C c_n(r, ‖P‖)` under a power bound `(C, r)` of `Q`.
* `BosonicLean.majorantCoeff_le_succ`: `c_n(r, a) ≤ c_{n+1}(r, a + 1)`.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), Definition 1 and Appendix C.
-/

open Finset

namespace BosonicLean

section Def

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- `Cₙ = Σ_{m ≤ n/2} K^m L^{n-2m} / (m! (n-2m)!)`, with `K` to the left of `L`: the coefficient
of `zⁿ` in `e^{K z²} e^{L z}`. For commuting `K`, `L` this is `H_n(L, K) / n!`, where `H_n(x, y)`
is the two-variable (Kampé de Fériet) Hermite polynomial, `Σₙ H_n(x, y) tⁿ/n! = e^{x t + y t²}`;
in general it is the form ordered with `K` to the left. In particular
`Cₙ(-1/2, x) = He_n(x) / n!` with `He_n` the probabilists' Hermite polynomial
(`Polynomial.hermite`). -/
noncomputable def cMatrix (K L : R) (n : ℕ) : R :=
  ∑ m ∈ range (n / 2 + 1),
    (((m.factorial * (n - 2 * m).factorial : ℕ) : ℂ)⁻¹) • (K ^ m * L ^ (n - 2 * m))

/-- `Cₙ` commutes with algebra homomorphisms. -/
theorem map_cMatrix {S : Type*} [Ring S] [Algebra ℂ S] (f : R →ₐ[ℂ] S) (K L : R) (n : ℕ) :
    f (cMatrix K L n) = cMatrix (f K) (f L) n := by
  simp [cMatrix, map_sum, map_smul, map_mul, map_pow]

end Def

/-- The coefficient of `K^t L^{n-2t}` in `Cₙ`: `1 / (t! (n-2t)!)` if `2t ≤ n`, and `0` otherwise. -/
noncomputable def cCoeff (n t : ℕ) : ℂ :=
  if 2 * t ≤ n then (((t.factorial * (n - 2 * t).factorial : ℕ) : ℂ))⁻¹ else 0

/-- `c(n, t) = 1 / (t! (n-2t)!)` for `2t ≤ n`. -/
theorem cCoeff_of_le {n t : ℕ} (h : 2 * t ≤ n) :
    cCoeff n t = (((t.factorial * (n - 2 * t).factorial : ℕ) : ℂ))⁻¹ := by
  simp only [cCoeff, h, ↓reduceIte]

/-- `c(n, t) = 0` for `2t > n`. -/
theorem cCoeff_of_lt {n t : ℕ} (h : n < 2 * t) : cCoeff n t = 0 := by
  simp only [cCoeff, show ¬ 2 * t ≤ n by omega, ↓reduceIte]

/-- The scalar recurrence at `t = 0`: `(n+2) / (n+2)! = 1 / (n+1)!`. -/
theorem cCoeff_succ_succ_zero (n : ℕ) :
    ((n + 2 : ℕ) : ℂ) * cCoeff (n + 2) 0 = cCoeff (n + 1) 0 := by
  rw [cCoeff_of_le (by omega), cCoeff_of_le (by omega)]
  simp only [Nat.factorial_zero, one_mul, Nat.mul_zero, Nat.sub_zero]
  rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ]
  have h : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  push_cast at h ⊢
  field_simp

/-- The scalar recurrence: `(n+2) c(n+2, t+1) = 2 c(n, t) + c(n+1, t+1)`. -/
theorem cCoeff_succ_succ (n t : ℕ) :
    ((n + 2 : ℕ) : ℂ) * cCoeff (n + 2) (t + 1) = 2 * cCoeff n t + cCoeff (n + 1) (t + 1) := by
  rcases lt_trichotomy (2 * t) n with h | h | h
  · -- `2t < n`: write `n = 2t + k + 1`
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * t + k + 1 := ⟨n - 2 * t - 1, by omega⟩
    rw [cCoeff_of_le (by omega), cCoeff_of_le (by omega), cCoeff_of_le (by omega)]
    rw [show 2 * t + k + 1 + 2 - 2 * (t + 1) = k + 1 by omega,
      show 2 * t + k + 1 - 2 * t = k + 1 by omega,
      show 2 * t + k + 1 + 1 - 2 * (t + 1) = k by omega,
      Nat.factorial_succ t, Nat.factorial_succ k]
    push_cast
    field_simp
    ring
  · -- `2t = n`
    subst h
    rw [cCoeff_of_le (by omega), cCoeff_of_le le_rfl, cCoeff_of_lt (by omega),
      show 2 * t + 2 - 2 * (t + 1) = 0 by omega, Nat.sub_self, Nat.factorial_succ t]
    push_cast
    field_simp
    ring
  · -- `2t > n`: all three vanish
    rw [cCoeff_of_lt (by omega : n + 2 < 2 * (t + 1)), cCoeff_of_lt h,
      cCoeff_of_lt (by omega : n + 1 < 2 * (t + 1))]
    ring

/-- The scalar identity behind the translation formula:
`c(n, t) C(n-2t, j) = c(n-j, t) / j!` for `j ≤ n`. -/
theorem cCoeff_mul_choose {n t j : ℕ} (hj : j ≤ n) :
    cCoeff n t * ((n - 2 * t).choose j : ℂ) = ((j.factorial : ℂ))⁻¹ * cCoeff (n - j) t := by
  by_cases h1 : 2 * t + j ≤ n
  · rw [cCoeff_of_le (by omega), cCoeff_of_le (by omega), Nat.cast_choose ℂ (by omega),
      show n - 2 * t - j = n - j - 2 * t by omega]
    push_cast
    have h0 : ((n - 2 * t).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · by_cases h2 : 2 * t ≤ n
    · rw [Nat.choose_eq_zero_of_lt (by omega), cCoeff_of_lt (by omega : n - j < 2 * t)]
      simp
    · rw [cCoeff_of_lt (by omega : n < 2 * t), cCoeff_of_lt (by omega : n - j < 2 * t)]
      simp

section Algebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- `Cₙ` as a sum over any range `N > n/2`, with the coefficients `cCoeff`. -/
theorem cMatrix_eq_sum_range (K L : R) (n N : ℕ) (hN : n / 2 + 1 ≤ N) :
    cMatrix K L n = ∑ t ∈ range N, cCoeff n t • (K ^ t * L ^ (n - 2 * t)) := by
  rw [cMatrix]
  refine sum_subset_zero_on_sdiff (range_subset_range.mpr hN) (fun t ht => ?_) (fun t ht => ?_)
  · have : n < 2 * t := by
      rw [mem_sdiff, mem_range, mem_range] at ht
      omega
    rw [cCoeff_of_lt this, zero_smul]
  · have : 2 * t ≤ n := by
      have := mem_range.mp ht
      omega
    rw [cCoeff_of_le this]

/-- `C₀ = 1`. -/
theorem cMatrix_zero (K L : R) : cMatrix K L 0 = 1 := by
  simp [cMatrix]

/-- `C₁ = L`. -/
theorem cMatrix_one (K L : R) : cMatrix K L 1 = L := by
  simp [cMatrix]

/-- `Cₘ(0, L) = Lᵐ / m!`: without the quadratic term, `e^{L z}` has the coefficients `Lᵐ / m!`. -/
theorem cMatrix_zero_left (L : R) (m : ℕ) :
    cMatrix (0 : R) L m = ((m.factorial : ℂ)⁻¹) • L ^ m := by
  rw [cMatrix, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, zero_mul, smul_zero]
  · simp

/-- **Homogeneity of `Cₙ`.** `Cₙ(λ² K, λ L) = λⁿ Cₙ(K, L)`: every term of `Cₙ` has degree `n` when
`K` is given weight `2`. -/
theorem cMatrix_smul_sq_smul (lam : ℂ) (K L : R) (n : ℕ) :
    cMatrix (lam ^ 2 • K) (lam • L) n = lam ^ n • cMatrix K L n := by
  simp only [cMatrix, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : 2 * t ≤ n := by have := Finset.mem_range.1 ht; omega
  rw [smul_pow, smul_pow, smul_mul_smul_comm, smul_comm, ← pow_mul, ← pow_add,
    show 2 * t + (n - 2 * t) = n by omega]

/-- **The Hermite three-term recurrence** `(n+2) C_{n+2} = 2 K Cₙ + C_{n+1} L`, with no
commutation assumed. -/
theorem cMatrix_succ_succ (K L : R) (n : ℕ) :
    ((n + 2 : ℕ) : ℂ) • cMatrix K L (n + 2) =
      (2 : ℂ) • (K * cMatrix K L n) + cMatrix K L (n + 1) * L := by
  rw [cMatrix_eq_sum_range K L (n + 2) (n + 3) (by omega),
    cMatrix_eq_sum_range K L n (n + 2) (by omega),
    cMatrix_eq_sum_range K L (n + 1) (n + 3) (by omega)]
  rw [smul_sum, mul_sum, smul_sum, sum_mul]
  rw [sum_range_succ' _ (n + 2),
    sum_range_succ' (fun t => cCoeff (n + 1) t • (K ^ t * L ^ (n + 1 - 2 * t)) * L) (n + 2)]
  rw [← add_assoc, ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun t _ => ?_
    have hK : K * (K ^ t * L ^ (n - 2 * t)) = K ^ (t + 1) * L ^ (n + 2 - 2 * (t + 1)) := by
      rw [show n + 2 - 2 * (t + 1) = n - 2 * t by omega, pow_succ', mul_assoc]
    have hL : cCoeff (n + 1) (t + 1) • (K ^ (t + 1) * L ^ (n + 1 - 2 * (t + 1))) * L =
        cCoeff (n + 1) (t + 1) • (K ^ (t + 1) * L ^ (n + 2 - 2 * (t + 1))) := by
      by_cases ht : 2 * (t + 1) ≤ n + 1
      · rw [smul_mul_assoc, mul_assoc, ← pow_succ,
          show n + 1 - 2 * (t + 1) + 1 = n + 2 - 2 * (t + 1) by omega]
      · rw [cCoeff_of_lt (by omega), zero_smul, zero_smul, zero_mul]
    rw [hL, smul_smul, mul_smul_comm, hK, smul_smul, ← add_smul, cCoeff_succ_succ]
  · simp only [pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero]
    rw [smul_mul_assoc, ← pow_succ, smul_smul, cCoeff_succ_succ_zero]

/-- The binomial expansion of `(L + u)ᵐ` for a scalar `u`. -/
theorem add_smul_one_pow (L : R) (u : ℂ) (m : ℕ) :
    (L + u • (1 : R)) ^ m = ∑ j ∈ range (m + 1), ((m.choose j : ℂ) * u ^ j) • L ^ (m - j) := by
  rw [add_comm, ((Commute.one_left L).smul_left u).add_pow]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_pow, one_pow, smul_one_mul, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_comm]

/-- **The translation formula (Appell property).** For a scalar `u`,
`Cₙ(K, L + u) = Σ_{j ≤ n} uʲ/j! C_{n-j}(K, L)`. -/
theorem cMatrix_add_smul_one (K L : R) (u : ℂ) (n : ℕ) :
    cMatrix K (L + u • 1) n =
      ∑ j ∈ range (n + 1), (((j.factorial : ℂ))⁻¹ * u ^ j) • cMatrix K L (n - j) := by
  have hC : ∀ j, cMatrix K L (n - j) =
      ∑ t ∈ range (n + 1), cCoeff (n - j) t • (K ^ t * L ^ (n - j - 2 * t)) :=
    fun j => cMatrix_eq_sum_range K L (n - j) (n + 1) (by omega)
  have hext : ∀ t, ∑ j ∈ range (n - 2 * t + 1),
      (((n - 2 * t).choose j : ℂ) * u ^ j) • L ^ (n - 2 * t - j) =
      ∑ j ∈ range (n + 1), (((n - 2 * t).choose j : ℂ) * u ^ j) • L ^ (n - 2 * t - j) := by
    intro t
    refine sum_subset (range_subset_range.mpr (by omega)) fun j _ hj => ?_
    rw [Nat.choose_eq_zero_of_lt (by rw [mem_range] at hj; omega)]
    simp
  rw [cMatrix_eq_sum_range K _ n (n + 1) (by omega)]
  simp_rw [hC, add_smul_one_pow, hext, mul_sum, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, smul_smul, smul_smul, show n - 2 * t - j = n - j - 2 * t by omega,
    ← mul_assoc, cCoeff_mul_choose (by rw [mem_range] at hj; omega)]
  ring_nf

/-- The binomial expansion of `(L + M)ʳ` for `M` commuting with `L`, over any range `n ≥ r`. -/
theorem add_pow_of_commute (L M : R) (hML : Commute M L) {r n : ℕ} (hr : r ≤ n) :
    (L + M) ^ r = ∑ j ∈ range (n + 1), ((r.choose j : ℂ)) • (M ^ j * L ^ (r - j)) := by
  rw [add_comm, hML.add_pow]
  refine sum_subset_zero_on_sdiff (range_subset_range.mpr (by omega)) (fun j hj => ?_)
    (fun j _ => ?_)
  · rw [mem_sdiff, mem_range, mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℂ]

/-- **The translation formula with a commuting increment.** If `M` commutes with `K` and `L`, then
`Cₙ(K, L + M) = Σ_{j ≤ n} Mʲ C_{n-j}(K, L) / j!`. -/
theorem cMatrix_add_of_commute (K L M : R) (hMK : Commute M K) (hML : Commute M L) (n : ℕ) :
    cMatrix K (L + M) n =
      ∑ j ∈ range (n + 1), ((j.factorial : ℂ))⁻¹ • (M ^ j * cMatrix K L (n - j)) := by
  have hC : ∀ j, cMatrix K L (n - j) =
      ∑ t ∈ range (n + 1), cCoeff (n - j) t • (K ^ t * L ^ (n - j - 2 * t)) :=
    fun j => cMatrix_eq_sum_range K L (n - j) (n + 1) (by omega)
  have hpow : ∀ t, (L + M) ^ (n - 2 * t) =
      ∑ j ∈ range (n + 1), (((n - 2 * t).choose j : ℂ)) • (M ^ j * L ^ (n - 2 * t - j)) :=
    fun t => add_pow_of_commute L M hML (by omega)
  rw [cMatrix_eq_sum_range K _ n (n + 1) (by omega)]
  simp_rw [hC, hpow, mul_sum, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, smul_smul, mul_smul_comm, smul_smul, ← mul_assoc,
    ((hMK.pow_pow j t).eq).symm, mul_assoc, show n - 2 * t - j = n - j - 2 * t by omega,
    cCoeff_mul_choose (by rw [mem_range] at hj; omega)]

end Algebra

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

omit [NormedRing A] [NormedAlgebra ℂ A] in
/-- The majorant coefficients are the real scalar case of `Cₙ`: `c_n(r, a) = Cₙ(r, a)` in `ℂ`. -/
theorem ofReal_majorantCoeff (r a : ℝ) (n : ℕ) :
    ((majorantCoeff r a n : ℝ) : ℂ) = cMatrix (r : ℂ) (a : ℂ) n := by
  simp only [majorantCoeff, cMatrix, Complex.ofReal_sum, smul_eq_mul]
  refine sum_congr rfl fun t _ => ?_
  push_cast
  ring

omit [NormedAlgebra ℂ A] in
/-- `‖P^m‖ ≤ ‖P‖^m` when `‖1‖ ≤ 1` (this includes the zero algebra). -/
theorem norm_pow_le_of_norm_one_le (h1 : ‖(1 : A)‖ ≤ 1) (P : A) (m : ℕ) : ‖P ^ m‖ ≤ ‖P‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using h1
  · exact norm_pow_le' P hm

/-- **Norm bound for the Fock-tensor polynomial.** If `Q` has a power bound `(C, r)`, `r ≥ 0`,
then `‖Cₙ(Q, P)‖ ≤ C c_n(r, ‖P‖)`. -/
theorem norm_cMatrix_le (h1 : ‖(1 : A)‖ ≤ 1) {Q : A} {C r : ℝ} (hQ : HasPowerBound Q C r)
    (hr : 0 ≤ r) (P : A) (n : ℕ) : ‖cMatrix Q P n‖ ≤ C * majorantCoeff r ‖P‖ n := by
  have hC : 0 ≤ C := by
    have := hQ 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  rw [cMatrix, majorantCoeff, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun t _ => ?_)
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hpow : ‖Q ^ t * P ^ (n - 2 * t)‖ ≤ C * r ^ t * ‖P‖ ^ (n - 2 * t) :=
    (norm_mul_le _ _).trans (mul_le_mul (hQ t) (norm_pow_le_of_norm_one_le h1 P _)
      (norm_nonneg _) (by positivity))
  have hden : (0 : ℝ) < ((t.factorial * (n - 2 * t).factorial : ℕ) : ℝ) := by positivity
  calc (((t.factorial * (n - 2 * t).factorial : ℕ) : ℝ))⁻¹ * ‖Q ^ t * P ^ (n - 2 * t)‖
      ≤ (((t.factorial * (n - 2 * t).factorial : ℕ) : ℝ))⁻¹ *
          (C * r ^ t * ‖P‖ ^ (n - 2 * t)) := by gcongr
    _ = C * (r ^ t * ‖P‖ ^ (n - 2 * t) /
          ((t.factorial : ℝ) * ((n - 2 * t).factorial : ℝ))) := by
        push_cast
        field_simp

end Banach

/-! ### Scalar facts -/

/-- `c(n+1, t) (n + 1 - 2t) = c(n, t)`: the coefficient form of `d/dL`. -/
theorem cCoeff_succ_mul (n t : ℕ) :
    cCoeff (n + 1) t * ((n + 1 - 2 * t : ℕ) : ℂ) = cCoeff n t := by
  rcases lt_trichotomy (2 * t) (n + 1) with h | h | h
  · rw [cCoeff_of_le (by omega), cCoeff_of_le (by omega),
      show n + 1 - 2 * t = (n - 2 * t) + 1 by omega, Nat.factorial_succ (n - 2 * t)]
    have h0 : ((n - 2 * t).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : (t.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
  · rw [cCoeff_of_lt (by omega : n < 2 * t), show n + 1 - 2 * t = 0 by omega]
    simp
  · rw [cCoeff_of_lt h, cCoeff_of_lt (by omega : n < 2 * t), zero_mul]

/-- **Comparison of majorant coefficients.** `c_n(r, a) ≤ c_{n+1}(r, a + 1)` for `r, a ≥ 0`. -/
theorem majorantCoeff_le_succ {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (n : ℕ) :
    majorantCoeff r a n ≤ majorantCoeff r (a + 1) (n + 1) := by
  have hshift : majorantCoeff r (a + 1) (n + 1) =
      ∑ j ∈ range (n + 2), majorantCoeff r a (n + 1 - j) / (j.factorial : ℝ) := by
    apply Complex.ofReal_injective
    rw [ofReal_majorantCoeff, Complex.ofReal_sum]
    have h := cMatrix_add_smul_one (r : ℂ) (a : ℂ) 1 (n + 1)
    simp only [one_pow, mul_one, smul_eq_mul] at h
    push_cast
    rw [h]
    refine sum_congr rfl fun j _ => ?_
    rw [ofReal_majorantCoeff]
    field_simp
  rw [hshift]
  have hj : 1 ∈ range (n + 2) := mem_range.mpr (by omega)
  calc majorantCoeff r a n = majorantCoeff r a (n + 1 - 1) / ((1 : ℕ).factorial : ℝ) := by simp
    _ ≤ ∑ j ∈ range (n + 2), majorantCoeff r a (n + 1 - j) / (j.factorial : ℝ) :=
        single_le_sum (f := fun j => majorantCoeff r a (n + 1 - j) / (j.factorial : ℝ))
          (fun j _ => div_nonneg (majorantCoeff_nonneg hr ha _) (Nat.cast_nonneg _)) hj

/-! ### Commutation and the special value `L = 0` -/

section Algebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- An element commuting with `K` and `L` commutes with `Cₙ(K, L)`. -/
theorem commute_cMatrix_right {X K L : R} (hK : Commute X K) (hL : Commute X L) (n : ℕ) :
    Commute X (cMatrix K L n) := by
  unfold cMatrix
  exact Commute.sum_right _ _ _ fun t _ =>
    ((hK.pow_right t).mul_right (hL.pow_right _)).smul_right _

/-- `C_{2m}(K, 0) = Kᵐ / m!`. -/
theorem cMatrix_zero_right_even (K : R) (m : ℕ) :
    cMatrix K 0 (2 * m) = ((m.factorial : ℂ))⁻¹ • K ^ m := by
  rw [cMatrix_eq_sum_range K 0 (2 * m) (m + 1) (by omega), sum_eq_single m]
  · rw [cCoeff_of_le le_rfl, Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, mul_one]
  · intro t ht htm
    have : 2 * t ≠ 2 * m := by omega
    rcases Nat.lt_or_ge (2 * m) (2 * t) with h | h
    · rw [cCoeff_of_lt h, zero_smul]
    · rw [zero_pow (by omega), mul_zero, smul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self m)) h

/-- `C_{2m+1}(K, 0) = 0`. -/
theorem cMatrix_zero_right_odd (K : R) (m : ℕ) : cMatrix K 0 (2 * m + 1) = 0 := by
  rw [cMatrix_eq_sum_range K 0 (2 * m + 1) (m + 1) (by omega)]
  refine sum_eq_zero fun t ht => ?_
  rw [mem_range] at ht
  rw [zero_pow (by omega), mul_zero, smul_zero]

end Algebra

/-! ### The derivative of `Cₙ(K, λL)` -/

section Deriv

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- `Cₘ(K, sL)` as a polynomial in `s`. -/
theorem cMatrix_smul_eq_sum (K L : A) (s : ℂ) (m N : ℕ) (hN : m / 2 + 1 ≤ N) :
    cMatrix K (s • L) m =
      ∑ u ∈ range N, (cCoeff m u * s ^ (m - 2 * u)) • (K ^ u * L ^ (m - 2 * u)) := by
  rw [cMatrix_eq_sum_range K _ m N hN]
  refine sum_congr rfl fun u _ => ?_
  rw [smul_pow, mul_smul_comm, smul_smul]

/-- **The Appell derivative rule.** `d/dλ C_{n+1}(K, λL) = Cₙ(K, λL) L`, with no commutation
assumed. -/
theorem hasDerivAt_cMatrix_smul (K L : A) (n : ℕ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => cMatrix K (s • L) (n + 1)) (cMatrix K (t • L) n * L) t := by
  have h1 : (fun s : ℂ => cMatrix K (s • L) (n + 1)) = fun s =>
      ∑ u ∈ range (n + 2), (cCoeff (n + 1) u * s ^ (n + 1 - 2 * u)) •
        (K ^ u * L ^ (n + 1 - 2 * u)) :=
    funext fun s => cMatrix_smul_eq_sum K L s (n + 1) (n + 2) (by omega)
  rw [h1, cMatrix_smul_eq_sum K L t n (n + 2) (by omega), sum_mul]
  apply HasDerivAt.fun_sum
  intro u _
  have hd := ((hasDerivAt_pow (n + 1 - 2 * u) t).const_mul (cCoeff (n + 1) u)).smul_const
    (K ^ u * L ^ (n + 1 - 2 * u))
  convert hd using 1
  by_cases hu : 2 * u ≤ n
  · have he : n + 1 - 2 * u = (n - 2 * u) + 1 := by omega
    rw [smul_mul_assoc, mul_assoc, ← pow_succ, ← he, ← cCoeff_succ_mul n u,
      show n + 1 - 2 * u - 1 = n - 2 * u by omega]
    congr 1
    ring
  · rw [cCoeff_of_lt (by omega : n < 2 * u), zero_mul, zero_smul, zero_mul,
      ← mul_assoc, cCoeff_succ_mul, cCoeff_of_lt (by omega : n < 2 * u), zero_mul, zero_smul]

/-- The derivative of `s ↦ Cₙ(K, sL)` for every `n`: `0` for `n = 0`, and `C_{n-1}(K, sL) L`
otherwise. -/
theorem hasDerivAt_cMatrix_smul' (K L : A) (n : ℕ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => cMatrix K (s • L) n)
      (if n = 0 then 0 else cMatrix K (t • L) (n - 1) * L) t := by
  cases n with
  | zero => simpa [cMatrix_zero] using hasDerivAt_const t (1 : A)
  | succ m => simpa using hasDerivAt_cMatrix_smul K L m t

/-- On the disc `‖s‖ ≤ ρ`: `‖Cₙ(K, sL)‖ ≤ C c_n(r, ρ‖L‖ + 1)`. -/
theorem norm_cMatrix_smul_le (h1 : ‖(1 : A)‖ ≤ 1) {K : A} {C r : ℝ} (hK : HasPowerBound K C r)
    (hr : 0 ≤ r) (L : A) (n : ℕ) {s : ℂ} {ρ : ℝ} (hs : ‖s‖ ≤ ρ) :
    ‖cMatrix K (s • L) n‖ ≤ C * majorantCoeff r (ρ * ‖L‖ + 1) n := by
  have hsL : ‖s • L‖ ≤ ρ * ‖L‖ + 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg L, norm_nonneg s]
  exact (norm_cMatrix_le h1 hK hr _ n).trans (mul_le_mul_of_nonneg_left
    (majorantCoeff_mono hr (norm_nonneg _) hsL n) hK.const_nonneg)

/-- On the disc `‖s‖ ≤ ρ`, the derivative of `Cₙ(K, sL)` is bounded by `C ‖L‖ c_n(r, ρ‖L‖ + 1)`. -/
theorem norm_deriv_cMatrix_smul_le (h1 : ‖(1 : A)‖ ≤ 1) {K : A} {C r : ℝ}
    (hK : HasPowerBound K C r) (hr : 0 ≤ r) (L : A) (n : ℕ) {s : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hs : ‖s‖ ≤ ρ) :
    ‖(if n = 0 then (0 : A) else cMatrix K (s • L) (n - 1) * L)‖ ≤
      C * ‖L‖ * majorantCoeff r (ρ * ‖L‖ + 1) n := by
  have hC := hK.const_nonneg
  cases n with
  | zero =>
    simp only [↓reduceIte, norm_zero]
    exact mul_nonneg (mul_nonneg hC (norm_nonneg _))
      (majorantCoeff_nonneg hr (by positivity) _)
  | succ m =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hsL : ‖s • L‖ ≤ ρ * ‖L‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg L)
    calc ‖cMatrix K (s • L) m * L‖ ≤ ‖cMatrix K (s • L) m‖ * ‖L‖ := norm_mul_le _ _
      _ ≤ (C * majorantCoeff r (ρ * ‖L‖) m) * ‖L‖ :=
          mul_le_mul_of_nonneg_right ((norm_cMatrix_le h1 hK hr _ m).trans
            (mul_le_mul_of_nonneg_left (majorantCoeff_mono hr (norm_nonneg _) hsL m) hC))
            (norm_nonneg L)
      _ ≤ (C * majorantCoeff r (ρ * ‖L‖ + 1) (m + 1)) * ‖L‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (majorantCoeff_le_succ hr (by positivity) m) hC) (norm_nonneg L)
      _ = C * ‖L‖ * majorantCoeff r (ρ * ‖L‖ + 1) (m + 1) := by ring

end Deriv

/-- Complex conjugation commutes with `Cₙ` in `ℂ`. -/
theorem conj_cMatrix (κ ℓ : ℂ) (n : ℕ) :
    starRingEnd ℂ (cMatrix κ ℓ n) = cMatrix (starRingEnd ℂ κ) (starRingEnd ℂ ℓ) n := by
  simp [cMatrix, map_sum, smul_eq_mul]

end BosonicLean
