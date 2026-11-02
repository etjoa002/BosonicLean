/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Ladder
import BosonicLean.Fock.NumberState
import BosonicLean.Fock.NumberRaisingExp
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The lowering exponential

On the formal Fock space with coefficients in a `ℂ`-algebra `R`, the operator `X ⊗ aⱼ`
(`lmul X ∘ aⱼ`) lowers the occupation of mode `j`:
`((X ⊗ aⱼ)^m ψ)(n) = √((nⱼ+1)(nⱼ+2)⋯(nⱼ+m)) X^m ψ(n + m eⱼ)`.
Unlike an operator that raises the particle number, it has an exponential series with infinitely
many terms at each coefficient.
The lowering exponential `e^{X ⊗ aⱼ}` is therefore defined coefficientwise, as the sum of
`((X ⊗ aⱼ)^m ψ)(n) / m!` over `m` in the topology of `R`; it is meaningful at the coefficients
where this series converges, and every statement about it asserts the convergence it uses.

## Main definitions

* `BosonicLean.Fock.FormalFock.lowerExp X j ψ`: `e^{X ⊗ aⱼ} ψ`, coefficientwise.

## Main results

* `BosonicLean.Fock.FormalFock.coeff_lmul_annihilate_pow`: the coefficients of `(X ⊗ aⱼ)^m ψ`.
* `BosonicLean.Fock.FormalFock.coeff_lmul_create_pow`: the coefficients of `(X ⊗ aⱼ†)^k ψ`.
* `BosonicLean.Fock.FormalFock.coeff_exp_gen_one_of_vanish`: on a vector with no particle
  in mode `j`, `(e^{L ⊗ aⱼ†} φ)(n) = L^{nⱼ} φ(n - nⱼ eⱼ) / √(nⱼ!)`.
-/

namespace BosonicLean.Fock.FormalFock

variable {ι R : Type*} [Ring R] [Algebra ℂ R]

/-- The coefficients of `(X ⊗ aⱼ)^m ψ`:
`((X ⊗ aⱼ)^m ψ)(n) = √((nⱼ+1)⋯(nⱼ+m)) X^m ψ(n + m eⱼ)`. -/
theorem coeff_lmul_annihilate_pow (X : R) (j : ι) (m : ℕ)
    (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    ((((lmul X).comp (annihilate j)) ^ m) ψ).coeff n =
      sqrtC ((n j + 1).ascFactorial m) • (X ^ m * ψ.coeff (n + Finsupp.single j m)) := by
  classical
  induction m generalizing ψ with
  | zero => simp [sqrtC]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.comp_apply, coeff_lmul, coeff_annihilate,
      Nat.ascFactorial_succ, sqrtC_mul]
    have hn : n + Finsupp.single j m + Finsupp.single j 1 = n + Finsupp.single j (m + 1) := by
      rw [add_assoc, ← Finsupp.single_add]
    have hj : (n + Finsupp.single j m) j + 1 = n j + 1 + m := by
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    rw [hn, hj]
    simp only [mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ]
    rw [mul_comm (sqrtC ((n j + 1).ascFactorial m))]

/-- The coefficients of `(X ⊗ aⱼ†)^k ψ`: `√((nⱼ-k+1)⋯nⱼ) X^k ψ(n - k eⱼ)` for `k ≤ nⱼ`, and `0`
otherwise. -/
theorem coeff_lmul_create_pow (X : R) (j : ι) (k : ℕ) (ψ : FormalFock ι R)
    (n : ι →₀ ℕ) :
    ((((lmul X : Module.End ℂ (FormalFock ι R)) * (create j : Module.End ℂ (FormalFock ι R))) ^ k)
      ψ).coeff n =
      if k ≤ n j then
        sqrtC ((n j - k + 1).ascFactorial k) • (X ^ k * ψ.coeff (n - Finsupp.single j k))
      else 0 := by
  classical
  induction k generalizing ψ with
  | zero => simp [sqrtC]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Module.End.mul_apply, coeff_lmul, coeff_create]
    have hj : (n - Finsupp.single j k) j = n j - k := by simp
    rw [hj]
    by_cases hk : k + 1 ≤ n j
    · have hk' : k ≤ n j := by omega
      have hpos : 0 < n j - k := by omega
      have hsub : n - Finsupp.single j k - Finsupp.single j 1 = n - Finsupp.single j (k + 1) := by
        rw [tsub_tsub, ← Finsupp.single_add]
      have hasc : (n j - k + 1).ascFactorial k * (n j - k) =
          (n j - (k + 1) + 1).ascFactorial (k + 1) := by
        rw [show n j - (k + 1) + 1 = n j - k by omega, Nat.ascFactorial_succ,
          ← Nat.succ_ascFactorial, mul_comm]
      simp only [hk, hk', hpos, ↓reduceIte, hsub]
      simp only [mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ]
      rw [← sqrtC_mul, hasc]
    · simp only [hk, ↓reduceIte]
      split_ifs with hk' hpos
      · omega
      · simp
      · rfl

/-- On a vector `φ` with no particle in mode `j`, `e^{L ⊗ aⱼ†}` acts by
`(e^{L ⊗ aⱼ†} φ)(n) = L^{nⱼ} φ(n - nⱼ eⱼ) / √(nⱼ!)`. -/
theorem coeff_exp_gen_one_of_vanish (L : R) (j : ι) {φ : FormalFock ι R}
    (hφ : ∀ n : ι →₀ ℕ, 0 < n j → φ.coeff n = 0) (n : ι →₀ ℕ) :
    ((gen L j 1 le_rfl).exp φ).coeff n =
      (sqrtC (n j).factorial)⁻¹ • (L ^ n j * φ.coeff (n - Finsupp.single j (n j))) := by
  classical
  rw [NumberRaisingOp.coeff_exp]
  have hop : (gen L j 1 le_rfl).op =
      (lmul L : Module.End ℂ (FormalFock ι R)) * (create j : Module.End ℂ (FormalFock ι R)) := by
    simp only [gen, pow_one]
  rw [hop, Finset.sum_eq_single (n j)]
  · rw [coeff_lmul_create_pow]
    simp only [le_refl, ↓reduceIte, Nat.sub_self, zero_add, Nat.one_ascFactorial, smul_smul]
    congr 1
    have h0 : sqrtC (n j).factorial ≠ 0 := sqrtC_ne_zero (Nat.factorial_pos _)
    have h1 := sqrtC_mul_self (n j).factorial
    field_simp
    rw [sq, h1, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  · intro k _ hk
    rw [coeff_lmul_create_pow]
    split_ifs with hkn
    · rw [hφ _ (by simp; omega), mul_zero, smul_zero, smul_zero]
    · rw [smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finsupp.le_degree j n))) h

variable [TopologicalSpace R]

/-- The **lowering exponential** `e^{X ⊗ aⱼ} ψ`, coefficientwise:
`(e^{X ⊗ aⱼ} ψ)(n) = Σ_m ((X ⊗ aⱼ)^m ψ)(n) / m!`. The value at `n` is meaningful where this series
converges; statements about `lowerExp` assert that convergence. For a general coefficient algebra
the sum is taken unconditionally; for matrices (finite dimension) this is absolute convergence. -/
noncomputable def lowerExp (X : R) (j : ι) (ψ : FormalFock ι R) : FormalFock ι R :=
  ⟨fun n => ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • ((((lmul X).comp (annihilate j)) ^ m) ψ).coeff n⟩

theorem coeff_lowerExp (X : R) (j : ι) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (lowerExp X j ψ).coeff n =
      ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • ((((lmul X).comp (annihilate j)) ^ m) ψ).coeff n :=
  rfl

end BosonicLean.Fock.FormalFock

/-! Deprecated names (B4.5, decision 5: standard terminology). -/

namespace BosonicLean.Fock.FormalFock

@[deprecated coeff_exp_gen_one_of_vanish (since := "2026-10-19")]
alias coeff_raisingExp_gen_one_of_vanish := coeff_exp_gen_one_of_vanish

end BosonicLean.Fock.FormalFock
