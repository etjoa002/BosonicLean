/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.TransferInstance

/-!
# The formal Fock space

The formal Fock space over a set of modes `ι` with coefficients in `R` consists of all
families `n ↦ ψ(n)` indexed by occupation-number multi-indices `n : ι →₀ ℕ`, read as
`Σₙ ψ(n) ∣n⟩`, with no summability condition. For finite `ι` it is the full product
`∏_N ⊗ₛᴺ ℂ^ι` of the particle-number sectors; the bosonic Fock space `Γₛ(ℂ^ι)` (the square
summable families) and the finite-particle space (the finitely supported ones) are subspaces.
Operators that raise the particle number act sector by sector on it, so their exponentials are
exact without any analysis.

## Main definitions

* `BosonicLean.Fock.FormalFock ι R`: the formal Fock space; `ψ.coeff n` is the coefficient of
  the number state `∣n⟩`.
* `BosonicLean.Fock.FormalFock.single m c`: the number state `c ∣m⟩`.
* `BosonicLean.Fock.FormalFock.VanishesBelow k ψ`: `ψ` has no component with fewer than `k`
  particles; under the Bargmann map, its power series has order at least `k`.
* `BosonicLean.Fock.factorial n`: the multi-index factorial `n! = ∏ᵢ nᵢ!`.

## Main results

* `BosonicLean.Fock.factorial_eq_mul`: `n! = nⱼ · (n - eⱼ)!` when `nⱼ ≥ 1`.
-/

namespace BosonicLean.Fock

/-- The formal Fock space over the modes `ι` with coefficients in `R`: a family of
coefficients over occupation-number multi-indices, with no summability condition. -/
@[ext]
structure FormalFock (ι R : Type*) where
  /-- The coefficient `ψ(n)` of the number state `∣n⟩`. -/
  coeff : (ι →₀ ℕ) → R

namespace FormalFock

variable {ι R : Type*}

theorem coeff_injective : Function.Injective (coeff : FormalFock ι R → (ι →₀ ℕ) → R) :=
  fun _ _ h => FormalFock.ext h

instance [Zero R] : Zero (FormalFock ι R) := ⟨⟨0⟩⟩
instance [Add R] : Add (FormalFock ι R) := ⟨fun ψ φ => ⟨ψ.coeff + φ.coeff⟩⟩
instance [Neg R] : Neg (FormalFock ι R) := ⟨fun ψ => ⟨-ψ.coeff⟩⟩
instance [Sub R] : Sub (FormalFock ι R) := ⟨fun ψ φ => ⟨ψ.coeff - φ.coeff⟩⟩
instance {S : Type*} [SMul S R] : SMul S (FormalFock ι R) := ⟨fun c ψ => ⟨c • ψ.coeff⟩⟩

instance [AddCommGroup R] : AddCommGroup (FormalFock ι R) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The coefficient family, as an additive map. -/
def coeffAddMonoidHom [AddCommGroup R] : FormalFock ι R →+ ((ι →₀ ℕ) → R) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance {S : Type*} [Semiring S] [AddCommGroup R] [Module S R] :
    Module S (FormalFock ι R) :=
  coeff_injective.module S coeffAddMonoidHom fun _ _ => rfl

section Coeff

variable [AddCommGroup R]

@[simp] theorem coeff_zero (n : ι →₀ ℕ) : (0 : FormalFock ι R).coeff n = 0 := rfl

@[simp] theorem coeff_add (ψ φ : FormalFock ι R) (n : ι →₀ ℕ) :
    (ψ + φ).coeff n = ψ.coeff n + φ.coeff n := rfl

@[simp] theorem coeff_neg (ψ : FormalFock ι R) (n : ι →₀ ℕ) : (-ψ).coeff n = -ψ.coeff n := rfl

@[simp] theorem coeff_sub (ψ φ : FormalFock ι R) (n : ι →₀ ℕ) :
    (ψ - φ).coeff n = ψ.coeff n - φ.coeff n := rfl

@[simp] theorem coeff_smul {S : Type*} [Semiring S] [Module S R] (c : S) (ψ : FormalFock ι R)
    (n : ι →₀ ℕ) : (c • ψ).coeff n = c • ψ.coeff n := rfl

@[simp] theorem coeff_sum {α : Type*} (s : Finset α) (f : α → FormalFock ι R) (n : ι →₀ ℕ) :
    (∑ a ∈ s, f a).coeff n = ∑ a ∈ s, (f a).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

end Coeff

/-- The number state `c ∣m⟩`: coefficient `c` at `m` and `0` elsewhere. -/
def single [Zero R] [DecidableEq ι] (m : ι →₀ ℕ) (c : R) : FormalFock ι R :=
  ⟨fun n => if n = m then c else 0⟩

@[simp]
theorem coeff_single [Zero R] [DecidableEq ι] (m : ι →₀ ℕ) (c : R) (n : ι →₀ ℕ) :
    (single m c).coeff n = if n = m then c else 0 := rfl

/-- `ψ` vanishes below `k`: it has no component with fewer than `k` particles. Equivalently, its
Bargmann image (`BosonicLean.Fock.FormalFock.toBargmann`) has order at least `k`. -/
def VanishesBelow [Zero R] (k : ℕ) (ψ : FormalFock ι R) : Prop :=
  ∀ n : ι →₀ ℕ, n.degree < k → ψ.coeff n = 0

theorem vanishesBelow_zero [Zero R] (ψ : FormalFock ι R) : VanishesBelow 0 ψ :=
  fun _ h => absurd h (Nat.not_lt_zero _)

end FormalFock

/-- The factorial `n! = ∏ᵢ nᵢ!` of an occupation-number multi-index. -/
def factorial {ι : Type*} (n : ι →₀ ℕ) : ℕ :=
  n.prod fun _ k => k.factorial

theorem factorial_pos {ι : Type*} (n : ι →₀ ℕ) : 0 < factorial n :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

@[simp]
theorem factorial_zero {ι : Type*} : factorial (0 : ι →₀ ℕ) = 1 := by
  simp [factorial]

theorem factorial_eq_prod {ι : Type*} [Fintype ι] (n : ι →₀ ℕ) :
    factorial n = ∏ i, (n i).factorial :=
  Finsupp.prod_fintype _ _ fun _ => Nat.factorial_zero

section Single

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorial_add_single (m : ι →₀ ℕ) (j : ι) :
    factorial (m + Finsupp.single j 1) = (m j + 1) * factorial m := by
  unfold factorial
  have h1 := Finsupp.mul_prod_erase' (m + Finsupp.single j 1) j (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' m j (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase j (m + Finsupp.single j 1) = Finsupp.erase j m := by
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Finsupp.erase_ne hi]
  rw [← h1, ← h2, he]
  simp [Nat.factorial_succ, mul_assoc]

omit [DecidableEq ι] in
/-- The multi-index factorial loses the factor `nⱼ` when one particle is removed from mode `j`. -/
theorem factorial_eq_mul (n : ι →₀ ℕ) (j : ι) (h : 0 < n j) :
    factorial n = n j * factorial (n - Finsupp.single j 1) := by
  have hle : Finsupp.single j 1 ≤ n := by
    rw [Finsupp.single_le_iff]; exact h
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [factorial_add_single]
  congr 1
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

end Single

end BosonicLean.Fock
