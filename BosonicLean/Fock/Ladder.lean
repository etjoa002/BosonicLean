/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Formal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Ladder operators on the formal Fock space

The creation and annihilation operators act coefficientwise,
`(aᵢ† ψ)(n) = √nᵢ ψ(n - eᵢ)` (zero if `nᵢ = 0`) and `(aᵢ ψ)(n) = √(nᵢ+1) ψ(n + eᵢ)`. On number
states this is `aᵢ†∣n⟩ = √(nᵢ+1)∣n + eᵢ⟩` and `aᵢ∣n⟩ = √nᵢ∣n - eᵢ⟩`. Each coefficient of the
result involves a single coefficient of `ψ`, so both operators are defined on the whole formal
Fock space and the canonical commutation relations hold there without domain conditions.

For a coefficient algebra `R`, `lmul X` multiplies every coefficient on the left by `X ∈ R`.
With `R` the bond matrices it realizes `X ⊗ A` for a ladder word `A` as `lmul X ∘ A`.

## Main definitions

* `BosonicLean.Fock.FormalFock.create i`, `annihilate i`: `aᵢ†` and `aᵢ`.
* `BosonicLean.Fock.FormalFock.lmul X`: left multiplication of every coefficient by `X`.

## Main results

* `lie_annihilate_create`: `⁅aᵢ, aⱼ†⁆ = δᵢⱼ`.
* `lie_annihilate_annihilate`, `lie_create_create`: `⁅aᵢ, aⱼ⁆ = 0`, `⁅aᵢ†, aⱼ†⁆ = 0`.
-/

namespace BosonicLean.Fock

/-- `√m` as a complex number. -/
noncomputable def sqrtC (m : ℕ) : ℂ := ((Real.sqrt m : ℝ) : ℂ)

theorem sqrtC_mul_self (m : ℕ) : sqrtC m * sqrtC m = m := by
  rw [sqrtC, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg m), Complex.ofReal_natCast]

theorem sqrtC_ne_zero {m : ℕ} (h : 0 < m) : sqrtC m ≠ 0 := by
  rw [sqrtC, Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  exact_mod_cast h

namespace FormalFock

variable {ι R : Type*}

theorem add_single_sub_single (n : ι →₀ ℕ) (i : ι) :
    n + Finsupp.single i 1 - Finsupp.single i 1 = n :=
  add_tsub_cancel_right _ _

theorem sub_single_add_single {n : ι →₀ ℕ} {i : ι} (h : 0 < n i) :
    n - Finsupp.single i 1 + Finsupp.single i 1 = n :=
  tsub_add_cancel_of_le (by rw [Finsupp.single_le_iff]; exact h)

theorem sub_single_apply_of_ne (n : ι →₀ ℕ) {i j : ι} (h : i ≠ j) :
    (n - Finsupp.single j 1 : ι →₀ ℕ) i = n i := by
  simp [Ne.symm h]

theorem add_single_apply_of_ne (n : ι →₀ ℕ) {i j : ι} (h : i ≠ j) :
    (n + Finsupp.single j 1 : ι →₀ ℕ) i = n i := by
  simp [Ne.symm h]

section Ladder

variable [AddCommGroup R] [Module ℂ R]

/-- The creation operator `aᵢ†`: `(aᵢ† ψ)(n) = √nᵢ ψ(n - eᵢ)`, and `0` when `nᵢ = 0`. -/
noncomputable def create (i : ι) : FormalFock ι R →ₗ[ℂ] FormalFock ι R where
  toFun ψ := ⟨fun n => if 0 < n i then sqrtC (n i) • ψ.coeff (n - Finsupp.single i 1) else 0⟩
  map_add' ψ φ := by
    ext n
    simp only [coeff_add]
    split_ifs <;> simp [smul_add]
  map_smul' c ψ := by
    ext n
    simp only [coeff_smul, RingHom.id_apply]
    split_ifs <;> simp [smul_comm c]

/-- The annihilation operator `aᵢ`: `(aᵢ ψ)(n) = √(nᵢ+1) ψ(n + eᵢ)`. -/
noncomputable def annihilate (i : ι) : FormalFock ι R →ₗ[ℂ] FormalFock ι R where
  toFun ψ := ⟨fun n => sqrtC (n i + 1) • ψ.coeff (n + Finsupp.single i 1)⟩
  map_add' ψ φ := by
    ext n
    simp [smul_add]
  map_smul' c ψ := by
    ext n
    simp [smul_comm c]

theorem coeff_create (i : ι) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (create i ψ).coeff n =
      if 0 < n i then sqrtC (n i) • ψ.coeff (n - Finsupp.single i 1) else 0 := rfl

theorem coeff_annihilate (i : ι) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (annihilate i ψ).coeff n = sqrtC (n i + 1) • ψ.coeff (n + Finsupp.single i 1) := rfl

/-- The canonical commutation relation `⁅aᵢ, aⱼ†⁆ = δᵢⱼ` on the whole formal Fock space. -/
theorem lie_annihilate_create [DecidableEq ι] (i j : ι) :
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ =
      if i = j then 1 else 0 := by
  ext ψ n
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, coeff_sub,
    coeff_annihilate, coeff_create, coeff_create]
  by_cases hij : i = j
  · subst hij
    have hpos : 0 < (n + Finsupp.single i 1 : ι →₀ ℕ) i := by simp
    simp only [hpos, ↓reduceIte, Module.End.one_apply, add_single_sub_single, smul_smul]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    split_ifs with h
    · rw [coeff_annihilate, sub_single_add_single h, smul_smul]
      have hn : (n - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = n i := by
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
      rw [hn, sqrtC_mul_self, sqrtC_mul_self, ← sub_smul]
      push_cast
      simp
    · have h0 : n i = 0 := by omega
      rw [sqrtC_mul_self, h0, sub_zero]
      simp
  · simp only [hij, ↓reduceIte, LinearMap.zero_apply, coeff_zero]
    rw [add_single_apply_of_ne n (Ne.symm hij)]
    split_ifs with h
    · rw [coeff_annihilate, sub_single_apply_of_ne n hij, smul_smul, smul_smul, mul_comm,
        sub_eq_zero]
      congr 2
      exact (tsub_add_eq_add_tsub (by rw [Finsupp.single_le_iff]; exact h)).symm
    · simp

/-- Annihilation operators commute: `⁅aᵢ, aⱼ⁆ = 0`. -/
theorem lie_annihilate_annihilate (i j : ι) :
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), annihilate (R := R) j⁆ = 0 := by
  rw [Ring.lie_def, sub_eq_zero]
  by_cases hij : i = j
  · rw [hij]
  ext ψ n
  simp only [Module.End.mul_apply, coeff_annihilate, smul_smul]
  rw [add_single_apply_of_ne n hij, add_single_apply_of_ne n (Ne.symm hij), mul_comm,
    add_right_comm]

/-- Creation operators commute: `⁅aᵢ†, aⱼ†⁆ = 0`. -/
theorem lie_create_create (i j : ι) :
    ⁅(create (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ = 0 := by
  rw [Ring.lie_def, sub_eq_zero]
  by_cases hij : i = j
  · rw [hij]
  ext ψ n
  simp only [Module.End.mul_apply, coeff_create]
  rw [sub_single_apply_of_ne n hij, sub_single_apply_of_ne n (Ne.symm hij)]
  by_cases hi : 0 < n i <;> by_cases hj : 0 < n j <;> simp only [hi, hj, ↓reduceIte,
    smul_zero]
  rw [smul_smul, smul_smul, mul_comm, tsub_right_comm]

end Ladder

section Lmul

variable [Ring R] [Algebra ℂ R]

/-- Left multiplication of every coefficient by `X`; with bond matrices, `X ⊗ A` is
`lmul X ∘ A`. -/
def lmul (X : R) : FormalFock ι R →ₗ[ℂ] FormalFock ι R where
  toFun ψ := ⟨fun n => X * ψ.coeff n⟩
  map_add' ψ φ := by
    ext n
    simp [mul_add]
  map_smul' c ψ := by
    ext n
    simp

theorem coeff_lmul (X : R) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (lmul X ψ).coeff n = X * ψ.coeff n :=
  rfl

theorem lmul_mul (X Y : R) : (lmul (X * Y) : FormalFock ι R →ₗ[ℂ] FormalFock ι R) =
    lmul X ∘ₗ lmul Y := by
  ext ψ n
  simp [coeff_lmul, mul_assoc]

theorem lmul_one : (lmul 1 : FormalFock ι R →ₗ[ℂ] FormalFock ι R) = LinearMap.id := by
  ext ψ n
  simp [coeff_lmul]

/-- Left multiplication commutes with creation. -/
theorem lmul_comp_create (X : R) (i : ι) :
    lmul X ∘ₗ create i = (create i ∘ₗ lmul X : FormalFock ι R →ₗ[ℂ] FormalFock ι R) := by
  ext ψ n
  simp only [LinearMap.comp_apply, coeff_lmul, coeff_create]
  split_ifs <;> simp

/-- Left multiplication commutes with annihilation. -/
theorem lmul_comp_annihilate (X : R) (i : ι) :
    lmul X ∘ₗ annihilate i = (annihilate i ∘ₗ lmul X : FormalFock ι R →ₗ[ℂ] FormalFock ι R) := by
  ext ψ n
  simp [coeff_lmul, coeff_annihilate]

end Lmul

end FormalFock

end BosonicLean.Fock
