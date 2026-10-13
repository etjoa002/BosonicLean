/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.RaisingExp
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# The Bargmann picture of the formal Fock space

The Bargmann map sends a formal Fock vector to the formal power series
`𝔅ψ = Σₙ ψ(n) zⁿ / √(n!)`, so that `𝔅∣n⟩ = zⁿ/√(n!)`, the orthonormal basis of Bargmann's space.
It is a linear bijection onto all formal power series, and it turns the ladder operators into
multiplication and differentiation: `𝔅 aⱼ† = zⱼ 𝔅` and `𝔅 aⱼ = ∂ⱼ 𝔅`. Coefficients may lie in
any `ℂ`-algebra `R`, in particular in the bond matrices, where power series do not commute.

Under `𝔅`, the exponential `e^{X ⊗ (aⱼ†)^p}` becomes multiplication by the one-variable series
`E_X^{(p)}(zⱼ) = Σₖ Xᵏ zⱼ^{pk}/k!`. The truncation of the exponential at `∣n∣` particles is
invisible, because `zⱼ^m f` has no coefficient at `n` when `m > nⱼ`.

## Main definitions

* `BosonicLean.Fock.FormalFock.toBargmann`: the Bargmann map, a linear equivalence
  `FormalFock ι R ≃ₗ[ℂ] MvPowerSeries ι R`.
* `BosonicLean.Fock.FormalFock.expSeries X j p`: the series `Σₖ Xᵏ zⱼ^{pk}/k!`.

## Main results

* `toBargmann_create`, `toBargmann_annihilate`, `toBargmann_lmul`, `toBargmann_vacuum`.
* `toBargmann_raisingExp_gen`: `𝔅(e^{X ⊗ (aⱼ†)^p} ψ) = E_X^{(p)}(zⱼ) · 𝔅ψ`.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform.
  Part I*, Comm. Pure Appl. Math. 14 (1961) 187–214.
-/

namespace BosonicLean.Fock.FormalFock

open Finset MvPowerSeries

variable {ι R : Type*} [Ring R] [Algebra ℂ R]

/-- `√(n!)` for a multi-index, as a complex number. -/
noncomputable def sqrtFactorial (n : ι →₀ ℕ) : ℂ := sqrtC (factorial n)

theorem sqrtFactorial_ne_zero (n : ι →₀ ℕ) : sqrtFactorial n ≠ 0 :=
  sqrtC_ne_zero (factorial_pos n)

theorem sqrtFactorial_add_single (n : ι →₀ ℕ) (j : ι) :
    sqrtFactorial (n + Finsupp.single j 1) = sqrtC (n j + 1) * sqrtFactorial n := by
  rw [sqrtFactorial, sqrtFactorial, factorial_add_single, sqrtC, sqrtC, sqrtC, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

/-- `√(n!) = √nⱼ · √((n - eⱼ)!)` when `nⱼ ≥ 1`. -/
theorem sqrtFactorial_eq_mul {n : ι →₀ ℕ} {j : ι} (h : 0 < n j) :
    sqrtFactorial n = sqrtC (n j) * sqrtFactorial (n - Finsupp.single j 1) := by
  conv_lhs => rw [← sub_single_add_single h]
  rw [sqrtFactorial_add_single]
  congr 2
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

/-- The Bargmann map `𝔅ψ = Σₙ ψ(n) zⁿ/√(n!)`, a linear equivalence onto formal power series. -/
noncomputable def toBargmann : FormalFock ι R ≃ₗ[ℂ] MvPowerSeries ι R where
  toFun ψ := fun n => (sqrtFactorial n)⁻¹ • ψ.coeff n
  invFun f := ⟨fun n => sqrtFactorial n • MvPowerSeries.coeff n f⟩
  map_add' ψ φ := by
    ext n
    exact smul_add _ _ _
  map_smul' c ψ := by
    ext n
    exact smul_comm _ c _
  left_inv ψ := by
    ext n
    change sqrtFactorial n • ((sqrtFactorial n)⁻¹ • ψ.coeff n) = ψ.coeff n
    rw [smul_smul, mul_inv_cancel₀ (sqrtFactorial_ne_zero n), one_smul]
  right_inv f := by
    ext n
    change (sqrtFactorial n)⁻¹ • (sqrtFactorial n • MvPowerSeries.coeff n f) = _
    rw [smul_smul, inv_mul_cancel₀ (sqrtFactorial_ne_zero n), one_smul]

theorem coeff_toBargmann (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (toBargmann ψ) = (sqrtFactorial n)⁻¹ • ψ.coeff n := rfl

omit [Algebra ℂ R] in
/-- The coefficient of `zⱼ · f` at `n`: the coefficient of `f` one step down, or zero. -/
theorem coeff_X_mul_eq (f : MvPowerSeries ι R) (j : ι) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (X j * f) =
      if 0 < n j then MvPowerSeries.coeff (n - Finsupp.single j 1) f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

omit [Algebra ℂ R] in
/-- The coefficient of `zⱼ^m · f` at `n` is that of `f` at `n - m eⱼ` if `m ≤ nⱼ`, and `0`
otherwise. -/
theorem coeff_X_pow_mul_eq (f : MvPowerSeries ι R) (j : ι) (m : ℕ)
    (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (X j ^ m * f) =
      if m ≤ n j then MvPowerSeries.coeff (n - Finsupp.single j m) f else 0 := by
  rw [X_pow_eq, coeff_monomial_mul, one_mul]
  simp only [Finsupp.single_le_iff]

omit [Algebra ℂ R] in
/-- The coefficient of `zⱼ^m · f` vanishes at every `n` with `nⱼ < m`. -/
theorem coeff_X_pow_mul_eq_zero (f : MvPowerSeries ι R) (j : ι) {m : ℕ} {n : ι →₀ ℕ}
    (h : n j < m) : MvPowerSeries.coeff n (X j ^ m * f) = 0 := by
  classical
  rw [X_pow_eq, coeff_monomial_mul, ite_eq_right_iff]
  intro hle
  rw [Finsupp.single_le_iff] at hle
  omega

/-- The Bargmann map turns `aⱼ†` into multiplication by `zⱼ`. -/
theorem toBargmann_create (j : ι) (ψ : FormalFock ι R) :
    toBargmann (create j ψ) = X j * toBargmann ψ := by
  ext n
  rw [coeff_X_mul_eq, coeff_toBargmann, coeff_create]
  split_ifs with h
  · rw [coeff_toBargmann, smul_smul, sqrtFactorial_eq_mul h]
    congr 1
    have h1 := sqrtC_ne_zero h
    have h2 := sqrtFactorial_ne_zero (n - Finsupp.single j 1)
    field_simp
  · exact smul_zero _

/-- The Bargmann map turns `aⱼ` into the derivative `∂ⱼ` (coefficientwise, for any `R`). -/
theorem toBargmann_annihilate (j : ι) (ψ : FormalFock ι R) :
    toBargmann (annihilate j ψ) = (toBargmann ψ).pderivFun j := by
  ext n
  rw [coeff_pderivFun, coeff_toBargmann, coeff_toBargmann, coeff_annihilate,
    sqrtFactorial_add_single, smul_smul, ← Nat.cast_add_one, ← nsmul_eq_mul',
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have h1 := sqrtFactorial_ne_zero n
  have h2 : sqrtC (n j + 1) ≠ 0 := sqrtC_ne_zero (Nat.succ_pos _)
  have h3 := sqrtC_mul_self (n j + 1)
  push_cast at h3 ⊢
  field_simp
  rw [sq]
  exact h3

/-- For scalar coefficients, `∂ⱼ` is Mathlib's partial derivative. -/
theorem toBargmann_annihilate_complex (j : ι) (ψ : FormalFock ι ℂ) :
    toBargmann (annihilate j ψ) = MvPowerSeries.pderiv (R := ℂ) j (toBargmann ψ) :=
  toBargmann_annihilate j ψ

/-- The Bargmann map turns left multiplication by `X` into multiplication by the constant `X`. -/
theorem toBargmann_lmul (X : R) (ψ : FormalFock ι R) :
    toBargmann (lmul X ψ) = C X * toBargmann ψ := by
  ext n
  rw [coeff_C_mul, coeff_toBargmann, coeff_toBargmann, coeff_lmul]
  exact (mul_smul_comm _ X _).symm

/-- The Bargmann image of `c ∣0⟩` is the constant `c`. -/
theorem toBargmann_vacuum [DecidableEq ι] (c : R) :
    toBargmann (single (0 : ι →₀ ℕ) c) = C c := by
  ext n
  rw [coeff_toBargmann, coeff_single, coeff_C]
  split_ifs with h
  · subst h
    simp [sqrtFactorial, sqrtC]
  · exact smul_zero _

theorem toBargmann_create_pow (j : ι) (p : ℕ) (ψ : FormalFock ι R) :
    toBargmann ((create j ^ p) ψ) = X j ^ p * toBargmann ψ := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ', Module.End.mul_apply, toBargmann_create, ih, pow_succ', mul_assoc]

theorem toBargmann_gen_pow (X : R) (j : ι) {p : ℕ} (hp : 1 ≤ p) (k : ℕ)
    (ψ : FormalFock ι R) :
    toBargmann (((gen X j p hp).op ^ k) ψ) =
      monomial (Finsupp.single j (p * k)) (X ^ k) * toBargmann ψ := by
  induction k with
  | zero => simp [monomial_zero_eq_C]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change toBargmann ((lmul X * create j ^ p : Module.End ℂ (FormalFock ι R)) _) = _
    rw [Module.End.mul_apply, toBargmann_lmul, toBargmann_create_pow, ih, X_pow_eq,
      ← monomial_zero_eq_C, ← mul_assoc, ← mul_assoc, monomial_mul_monomial,
      monomial_mul_monomial, zero_add, ← Finsupp.single_add, mul_one, ← pow_succ', mul_add,
      mul_one, add_comm]

/-- The series `E_X^{(p)}(zⱼ) = Σₖ Xᵏ zⱼ^{pk}/k!`; at a multi-index `a` only `k ≤ aⱼ` can
contribute. -/
noncomputable def expSeries [DecidableEq ι] (X : R) (j : ι) (p : ℕ) : MvPowerSeries ι R :=
  fun a => ∑ k ∈ range (a j + 1),
    if a = Finsupp.single j (p * k) then ((k.factorial : ℂ)⁻¹) • X ^ k else 0

theorem coeff_expSeries [DecidableEq ι] (X : R) (j : ι) (p : ℕ) (a : ι →₀ ℕ) :
    MvPowerSeries.coeff a (expSeries X j p) = ∑ k ∈ range (a j + 1),
      if a = Finsupp.single j (p * k) then ((k.factorial : ℂ)⁻¹) • X ^ k else 0 := rfl

omit [Algebra ℂ R] in
/-- Only coefficients at `a ≤ n` of the left factor matter for the coefficient at `n`. -/
theorem coeff_mul_congr_left {E E' : MvPowerSeries ι R} (f : MvPowerSeries ι R)
    (n : ι →₀ ℕ) (h : ∀ a ≤ n, MvPowerSeries.coeff a E = MvPowerSeries.coeff a E') :
    MvPowerSeries.coeff n (E * f) = MvPowerSeries.coeff n (E' * f) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  rw [h x.1 (by rw [← hx]; exact le_self_add)]

/-- Under the Bargmann map, `e^{X ⊗ (aⱼ†)^p}` (`p ≥ 1`) becomes multiplication by
`E_X^{(p)}(zⱼ)`. -/
theorem toBargmann_raisingExp_gen [DecidableEq ι] (X : R) (j : ι) {p : ℕ} (hp : 1 ≤ p)
    (ψ : FormalFock ι R) :
    toBargmann (raisingExp (gen X j p hp) ψ) = expSeries X j p * toBargmann ψ := by
  ext n
  set c : ℕ → ℂ := fun k => ((k.factorial : ℂ)⁻¹)
  set E' : MvPowerSeries ι R := ∑ k ∈ range (n.degree + 1),
    monomial (Finsupp.single j (p * k)) (c k • X ^ k)
  have hE : ∀ a ≤ n, MvPowerSeries.coeff a (expSeries X j p) = MvPowerSeries.coeff a E' := by
    intro a ha
    rw [coeff_expSeries]
    simp only [E', map_sum, coeff_monomial]
    have hsub : range (a j + 1) ⊆ range (n.degree + 1) := by
      intro k hk
      simp only [mem_range] at hk ⊢
      have := Finsupp.le_degree j n
      have := ha j
      omega
    refine sum_subset hsub fun k _ hk => ?_
    rw [ite_eq_right_iff]
    rintro rfl
    simp only [mem_range, Finsupp.single_eq_same, not_lt] at hk
    nlinarith
  rw [coeff_mul_congr_left _ n hE, coeff_toBargmann, coeff_raisingExp]
  simp only [E', sum_mul, map_sum, smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [smul_comm, ← coeff_toBargmann, toBargmann_gen_pow, coeff_monomial_mul,
    coeff_monomial_mul]
  split_ifs <;> simp [c]

end BosonicLean.Fock.FormalFock
