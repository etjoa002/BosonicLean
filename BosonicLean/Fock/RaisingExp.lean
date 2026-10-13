/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Ladder
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

/-!
# Raising operators and their exponentials

A linear map `T` on the formal Fock space is *raising*, short for order-raising, if it maps
vectors with no component below `k` particles to vectors with no component below `k + 1`
particles. Since `VanishesBelow k ψ` says that the Bargmann image of `ψ` (a formal power series)
has order at least `k`, a raising map raises the order of power series by at least one; the
creation operators `aⱼ†` are the basic examples. For such `T` the coefficient of `Tᵏψ` at `∣n⟩`
vanishes once `k > ∣n∣`, so the exponential series `Σₖ Tᵏψ/k!` has only finitely many terms at
each coefficient:
`(e^T ψ)(n) = Σ_{k ≤ ∣n∣} (Tᵏψ)(n)/k!`.
No norm or topology is needed, and for commuting raising `S` and `T` the exponential law
`e^{S+T} = e^S e^T` holds.

## Main definitions

* `BosonicLean.Fock.FormalFock.IsRaising T`: `T` raises the particle number.
* `BosonicLean.Fock.FormalFock.RaisingOp`: a linear map bundled with a proof that it raises.
* `BosonicLean.Fock.FormalFock.raisingExp T`: the exponential `e^T` of a raising operator.

## Main results

* `IsRaising.vanishesBelow_pow`: `Tᵃ` raises the particle number by `a`.
* `IsRaising.coeff_pow_eq_of_agree`: the coefficient of `Tᵃψ` at `n` depends only on the
  coefficients of `ψ` with at most `∣n∣` particles.
* `isRaising_lmul_mul_create_pow`: `X ⊗ (aᵢ†)^p` is raising for `p ≥ 1`.
* `raisingExp_add`: `e^{S+T} = e^S e^T` for commuting raising `S`, `T`.
-/

namespace BosonicLean.Fock.FormalFock

open Finset

variable {ι R : Type*}

section Raising

variable [AddCommGroup R] [Module ℂ R]

/-- `T` raises the particle number: if `ψ` has no component below `k` particles, then `T ψ` has
none below `k + 1`. Under the Bargmann map, `T` raises the order of power series. -/
def IsRaising (T : Module.End ℂ (FormalFock ι R)) : Prop :=
  ∀ k ψ, VanishesBelow k ψ → VanishesBelow (k + 1) (T ψ)

namespace IsRaising

variable {S T : Module.End ℂ (FormalFock ι R)}

theorem vanishesBelow_pow (hT : IsRaising T) (a : ℕ) {k : ℕ} {ψ : FormalFock ι R}
    (h : VanishesBelow k ψ) : VanishesBelow (k + a) ((T ^ a) ψ) := by
  induction a with
  | zero => simpa using h
  | succ a ih => rw [pow_succ', Module.End.mul_apply, ← add_assoc]; exact hT _ _ ih

/-- The coefficient of `Tᵃψ` vanishes at every `n` with fewer than `a` particles. -/
theorem coeff_pow_eq_zero (hT : IsRaising T) {a : ℕ} (ψ : FormalFock ι R) {n : ι →₀ ℕ}
    (h : n.degree < a) : ((T ^ a) ψ).coeff n = 0 :=
  hT.vanishesBelow_pow a (vanishesBelow_zero ψ) n (by omega)

/-- The coefficient of `Tᵃψ` at `n` depends only on the coefficients of `ψ` with at most `∣n∣`
particles. -/
theorem coeff_pow_eq_of_agree (hT : IsRaising T) (a : ℕ) {ψ φ : FormalFock ι R}
    {n : ι →₀ ℕ} (h : ∀ m : ι →₀ ℕ, m.degree ≤ n.degree → ψ.coeff m = φ.coeff m) :
    ((T ^ a) ψ).coeff n = ((T ^ a) φ).coeff n := by
  have hv : VanishesBelow (n.degree + 1) (ψ - φ) := fun m hm => by
    rw [coeff_sub, h m (by omega), sub_self]
  have := hT.vanishesBelow_pow a hv n (by omega)
  rwa [map_sub, coeff_sub, sub_eq_zero] at this

/-- The coefficient of `Tψ` at `n` depends only on the coefficients of `ψ` with fewer than `∣n∣`
particles. -/
theorem coeff_eq_of_agree (hT : IsRaising T) {ψ φ : FormalFock ι R} {n : ι →₀ ℕ}
    (h : ∀ m : ι →₀ ℕ, m.degree < n.degree → ψ.coeff m = φ.coeff m) :
    (T ψ).coeff n = (T φ).coeff n := by
  have hv : VanishesBelow n.degree (ψ - φ) := fun m hm => by
    rw [coeff_sub, h m hm, sub_self]
  have := hT _ _ hv n (by omega)
  rwa [map_sub, coeff_sub, sub_eq_zero] at this

theorem add (hS : IsRaising S) (hT : IsRaising T) : IsRaising (S + T) := fun k ψ h n hn => by
  rw [LinearMap.add_apply, coeff_add, hS k ψ h n hn, hT k ψ h n hn, add_zero]

theorem mul (hS : IsRaising S) (hT : IsRaising T) : IsRaising (S * T) := fun k ψ h n hn =>
  hS (k + 1) (T ψ) (hT k ψ h) n (by omega)

theorem smul (hT : IsRaising T) (c : ℂ) : IsRaising (c • T) := fun k ψ h n hn => by
  rw [LinearMap.smul_apply, coeff_smul, hT k ψ h n hn, smul_zero]

end IsRaising

/-- A product of `r` raising maps raises the particle number by `r`: if `ψ` vanishes below `k`,
then `T₁ ⋯ Tᵣ ψ` vanishes below `k + r`. -/
theorem vanishesBelow_list_prod (l : List (Module.End ℂ (FormalFock ι R)))
    (hl : ∀ T ∈ l, IsRaising T) {k : ℕ} {ψ : FormalFock ι R} (h : VanishesBelow k ψ) :
    VanishesBelow (k + l.length) (l.prod ψ) := by
  induction l with
  | nil => simpa using h
  | cons T l ih =>
    rw [List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact hl T (by simp) _ _ (ih fun S hS => hl S (by simp [hS]))

/-- A linear map on the formal Fock space, bundled with the proof that it raises the particle
number. The exponential is defined only for these. -/
structure RaisingOp (ι R : Type*) [AddCommGroup R] [Module ℂ R] where
  /-- The operator. -/
  op : Module.End ℂ (FormalFock ι R)
  /-- It raises the particle number. -/
  isRaising : IsRaising op

instance : Add (RaisingOp ι R) := ⟨fun S T => ⟨S.op + T.op, S.isRaising.add T.isRaising⟩⟩

@[simp] theorem RaisingOp.add_op (S T : RaisingOp ι R) : (S + T).op = S.op + T.op := rfl

/-- The exponential `e^T` of a raising operator:
`(e^T ψ)(n) = Σ_{k ≤ ∣n∣} (Tᵏψ)(n)/k!`. -/
noncomputable def raisingExp (T : RaisingOp ι R) : Module.End ℂ (FormalFock ι R) where
  toFun ψ := ⟨fun n => ∑ k ∈ range (n.degree + 1),
    ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n⟩
  map_add' ψ φ := by
    ext n
    simp [smul_add, sum_add_distrib]
  map_smul' c ψ := by
    ext n
    simp [smul_sum, smul_comm c]

theorem coeff_raisingExp (T : RaisingOp ι R) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (raisingExp T ψ).coeff n =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n := rfl

/-- The exponential series may be summed to any bound `M ≥ ∣n∣`: the extra terms vanish. -/
theorem coeff_raisingExp_eq_sum (T : RaisingOp ι R) (ψ : FormalFock ι R) {n : ι →₀ ℕ} {M : ℕ}
    (hM : n.degree ≤ M) :
    (raisingExp T ψ).coeff n =
      ∑ k ∈ range (M + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n := by
  rw [coeff_raisingExp]
  refine sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun k _ hk => ?_
  rw [mem_range, not_lt] at hk
  rw [T.isRaising.coeff_pow_eq_zero ψ (by omega), smul_zero]

/-- The scalar identity behind the exponential law: `(k!)⁻¹ · C(k, a) = (a!)⁻¹ ((k - a)!)⁻¹`. -/
theorem inv_factorial_mul_choose {k a : ℕ} (h : a ≤ k) :
    ((k.factorial : ℂ)⁻¹) * (k.choose a : ℂ) =
      ((a.factorial : ℂ)⁻¹) * (((k - a).factorial : ℂ)⁻¹) := by
  have hk := Nat.choose_mul_factorial_mul_factorial h
  have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h2 : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have h3 : ((k - a).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp
  exact_mod_cast hk

/-- The exponential law `e^{S+T} = e^S e^T` for commuting raising operators. -/
theorem raisingExp_add (S T : RaisingOp ι R) (hST : Commute S.op T.op) :
    raisingExp (S + T) = raisingExp S * raisingExp T := by
  ext ψ n
  set M := n.degree
  set c : ℕ → ℂ := fun k => ((k.factorial : ℂ)⁻¹)
  set f : ℕ → ℕ → R := fun a b => ((S.op ^ a * T.op ^ b) ψ).coeff n
  -- the terms with more than `M` raisings vanish at `n`
  have hf : ∀ a b, M < a + b → f a b = 0 := fun a b h => by
    have := S.isRaising.vanishesBelow_pow a (T.isRaising.vanishesBelow_pow b
      (vanishesBelow_zero ψ))
    exact this n (by simp only [zero_add] at this ⊢; omega)
  -- left side: binomial expansion of `(S + T)^k`
  have hL : (raisingExp (S + T) ψ).coeff n =
      ∑ k ∈ range (M + 1), ∑ a ∈ range (k + 1), (c a * c (k - a)) • f a (k - a) := by
    rw [coeff_raisingExp]
    refine sum_congr rfl fun k _ => ?_
    rw [RaisingOp.add_op, hST.add_pow, LinearMap.sum_apply, coeff_sum, smul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_range] at ha
    rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
      coeff_smul, smul_smul, inv_factorial_mul_choose (by omega)]
  -- right side: truncate `e^T ψ` at `M` particles, then expand
  have hR : (raisingExp S (raisingExp T ψ)).coeff n =
      ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a * c b) • f a b := by
    rw [coeff_raisingExp]
    refine sum_congr rfl fun a _ => ?_
    have hagree : ∀ m : ι →₀ ℕ, m.degree ≤ M → (raisingExp T ψ).coeff m =
        (∑ b ∈ range (M + 1), c b • (T.op ^ b) ψ).coeff m := fun m hm => by
      rw [coeff_raisingExp_eq_sum T ψ hm, coeff_sum]
      simp [c]
    rw [S.isRaising.coeff_pow_eq_of_agree a hagree, map_sum, coeff_sum, smul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [map_smul, coeff_smul, smul_smul]
    rfl
  -- the square sum reduces to the triangle `a + b ≤ M`
  have hsq : ∀ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a * c b) • f a b =
      ∑ b ∈ range (M + 1 - a), (c a * c b) • f a b := fun a _ => by
    symm
    refine sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun b _ hb => ?_
    rw [mem_range, not_lt] at hb
    rw [hf a b (by omega), smul_zero]
  rw [Module.End.mul_apply, hR, hL, sum_congr rfl hsq]
  exact sum_range_diag_flip (M + 1) fun a b => (c a * c b) • f a b

end Raising

section Create

variable [Ring R] [Algebra ℂ R]

theorem degree_sub_single_add_one {n : ι →₀ ℕ} {i : ι} (h : 0 < n i) :
    (n - Finsupp.single i 1).degree + 1 = n.degree := by
  conv_rhs => rw [← sub_single_add_single h]
  rw [map_add, Finsupp.degree_single]

/-- The creation operator is raising. -/
theorem isRaising_create (i : ι) : IsRaising (create (R := R) i) := fun k ψ h n hn => by
  rw [coeff_create]
  split_ifs with hi
  · rw [h _ (by have := degree_sub_single_add_one hi; omega), smul_zero]
  · rfl

/-- Left multiplication preserves vanishing below `k`. -/
theorem vanishesBelow_lmul (X : R) {k : ℕ} {ψ : FormalFock ι R} (h : VanishesBelow k ψ) :
    VanishesBelow k (lmul X ψ) := fun n hn => by
  rw [coeff_lmul, h n hn, mul_zero]

/-- `X ⊗ (aᵢ†)^p = lmul X ∘ (aᵢ†)^p` is raising for `p ≥ 1`. -/
theorem isRaising_lmul_mul_create_pow (X : R) (i : ι) {p : ℕ} (hp : 1 ≤ p) :
    IsRaising (lmul X * create (R := R) i ^ p) := fun k ψ h n hn => by
  have := (isRaising_create i).vanishesBelow_pow p h
  exact vanishesBelow_lmul X this n (by omega)

/-- The generator `X ⊗ (aᵢ†)^p` (`p ≥ 1`) as a raising operator. -/
noncomputable def gen (X : R) (i : ι) (p : ℕ) (hp : 1 ≤ p) : RaisingOp ι R :=
  ⟨lmul X * create i ^ p, isRaising_lmul_mul_create_pow X i hp⟩

end Create

end BosonicLean.Fock.FormalFock
