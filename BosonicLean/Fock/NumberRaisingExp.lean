/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Ladder
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

/-!
# Operators that raise the particle number, and their exponentials

A linear map `T` on the formal Fock space *raises the particle number* if it maps
vectors with no component below `k` particles to vectors with no component below `k + 1`
particles. Since `VanishesBelow k ψ` says that the Bargmann image of `ψ` (a formal power series)
has order at least `k`, such a map raises the order of power series by at least one; the
creation operators `aⱼ†` are the basic examples. For such `T` the coefficient of `Tᵏψ` at `∣n⟩`
vanishes once `k > ∣n∣`, so the exponential series `Σₖ Tᵏψ/k!` has only finitely many terms at
each coefficient:
`(e^T ψ)(n) = Σ_{k ≤ ∣n∣} (Tᵏψ)(n)/k!`.
No norm or topology is needed, and for commuting such `S` and `T` the exponential law
`e^{S+T} = e^S e^T` holds.

## Main definitions

* `BosonicLean.Fock.FormalFock.RaisesParticleNumber T`: `T` raises the particle number.
* `BosonicLean.Fock.FormalFock.NumberRaisingOp`: a linear map bundled with a proof that it raises
  the particle number.
* `BosonicLean.Fock.FormalFock.NumberRaisingOp.exp T`: the exponential `e^T`.

## Main results

* `RaisesParticleNumber.vanishesBelow_pow`: `Tᵃ` raises the particle number by `a`.
* `RaisesParticleNumber.coeff_pow_eq_of_agree`: the coefficient of `Tᵃψ` at `n` depends only on
  the coefficients of `ψ` with at most `∣n∣` particles.
* `raisesParticleNumber_lmul_mul_create_pow`: `X ⊗ (aᵢ†)^p` raises the particle number for
  `p ≥ 1`.
* `raisesParticleNumber_sum_lmul_mul_prod_create`: every polynomial in the creation operators
  with zero constant term raises the particle number.
* `NumberRaisingOp.exp_add`: `e^{S+T} = e^S e^T` for commuting `S`, `T`.
* `NumberRaisingOp.exp_mul_eq_one`: `e^S e^T = 1` when `S = -T`;
  `NumberRaisingOp.exp_of_op_eq_zero`: `e^0 = 1`.
* `gen_op_eq_smul`, `commute_gen_gen`: generators `c (aⱼ†)^p` with scalar `c` commute.
-/

namespace BosonicLean.Fock.FormalFock

open Finset

variable {ι R : Type*}

section Exp

variable [AddCommGroup R] [Module ℂ R]

/-- `T` raises the particle number: if `ψ` has no component below `k` particles, then `T ψ` has
none below `k + 1`. Under the Bargmann map, `T` raises the order of power series. -/
def RaisesParticleNumber (T : Module.End ℂ (FormalFock ι R)) : Prop :=
  ∀ k ψ, VanishesBelow k ψ → VanishesBelow (k + 1) (T ψ)

namespace RaisesParticleNumber

variable {S T : Module.End ℂ (FormalFock ι R)}

theorem vanishesBelow_pow (hT : RaisesParticleNumber T) (a : ℕ) {k : ℕ} {ψ : FormalFock ι R}
    (h : VanishesBelow k ψ) : VanishesBelow (k + a) ((T ^ a) ψ) := by
  induction a with
  | zero => simpa using h
  | succ a ih => rw [pow_succ', Module.End.mul_apply, ← add_assoc]; exact hT _ _ ih

/-- The coefficient of `Tᵃψ` vanishes at every `n` with fewer than `a` particles. -/
theorem coeff_pow_eq_zero (hT : RaisesParticleNumber T) {a : ℕ} (ψ : FormalFock ι R) {n : ι →₀ ℕ}
    (h : n.degree < a) : ((T ^ a) ψ).coeff n = 0 :=
  hT.vanishesBelow_pow a (vanishesBelow_zero ψ) n (by omega)

/-- The coefficient of `Tᵃψ` at `n` depends only on the coefficients of `ψ` with at most `∣n∣`
particles. -/
theorem coeff_pow_eq_of_agree (hT : RaisesParticleNumber T) (a : ℕ) {ψ φ : FormalFock ι R}
    {n : ι →₀ ℕ} (h : ∀ m : ι →₀ ℕ, m.degree ≤ n.degree → ψ.coeff m = φ.coeff m) :
    ((T ^ a) ψ).coeff n = ((T ^ a) φ).coeff n := by
  have hv : VanishesBelow (n.degree + 1) (ψ - φ) := fun m hm => by
    rw [coeff_sub, h m (by omega), sub_self]
  have := hT.vanishesBelow_pow a hv n (by omega)
  rwa [map_sub, coeff_sub, sub_eq_zero] at this

/-- The coefficient of `Tψ` at `n` depends only on the coefficients of `ψ` with fewer than `∣n∣`
particles. -/
theorem coeff_eq_of_agree (hT : RaisesParticleNumber T) {ψ φ : FormalFock ι R} {n : ι →₀ ℕ}
    (h : ∀ m : ι →₀ ℕ, m.degree < n.degree → ψ.coeff m = φ.coeff m) :
    (T ψ).coeff n = (T φ).coeff n := by
  have hv : VanishesBelow n.degree (ψ - φ) := fun m hm => by
    rw [coeff_sub, h m hm, sub_self]
  have := hT _ _ hv n (by omega)
  rwa [map_sub, coeff_sub, sub_eq_zero] at this

theorem add (hS : RaisesParticleNumber S) (hT : RaisesParticleNumber T) :
    RaisesParticleNumber (S + T) := fun k ψ h n hn => by
  rw [LinearMap.add_apply, coeff_add, hS k ψ h n hn, hT k ψ h n hn, add_zero]

theorem mul (hS : RaisesParticleNumber S) (hT : RaisesParticleNumber T) :
    RaisesParticleNumber (S * T) := fun k ψ h n hn =>
  hS (k + 1) (T ψ) (hT k ψ h) n (by omega)

theorem smul (hT : RaisesParticleNumber T) (c : ℂ) : RaisesParticleNumber (c • T) :=
    fun k ψ h n hn => by
  rw [LinearMap.smul_apply, coeff_smul, hT k ψ h n hn, smul_zero]

theorem zero : RaisesParticleNumber (0 : Module.End ℂ (FormalFock ι R)) := fun _ _ _ n _ => by
  rw [LinearMap.zero_apply, coeff_zero]

theorem sum {κ : Type*} (s : Finset κ) {T : κ → Module.End ℂ (FormalFock ι R)}
    (hT : ∀ k ∈ s, RaisesParticleNumber (T k)) : RaisesParticleNumber (∑ k ∈ s, T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (hT k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => hT k' (Finset.mem_insert_of_mem hk'))

end RaisesParticleNumber

/-- A product of `r` maps that raise the particle number raises it by `r`: if `ψ` vanishes below
`k`, then `T₁ ⋯ Tᵣ ψ` vanishes below `k + r`. -/
theorem vanishesBelow_list_prod (l : List (Module.End ℂ (FormalFock ι R)))
    (hl : ∀ T ∈ l, RaisesParticleNumber T) {k : ℕ} {ψ : FormalFock ι R} (h : VanishesBelow k ψ) :
    VanishesBelow (k + l.length) (l.prod ψ) := by
  induction l with
  | nil => simpa using h
  | cons T l ih =>
    rw [List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact hl T (by simp) _ _ (ih fun S hS => hl S (by simp [hS]))

/-- A linear map on the formal Fock space, bundled with the proof that it raises the particle
number. The exponential is defined only for these. -/
structure NumberRaisingOp (ι R : Type*) [AddCommGroup R] [Module ℂ R] where
  /-- The operator. -/
  op : Module.End ℂ (FormalFock ι R)
  /-- It raises the particle number. -/
  raisesParticleNumber : RaisesParticleNumber op

instance : Add (NumberRaisingOp ι R) :=
  ⟨fun S T => ⟨S.op + T.op, S.raisesParticleNumber.add T.raisesParticleNumber⟩⟩

@[simp] theorem NumberRaisingOp.add_op (S T : NumberRaisingOp ι R) : (S + T).op = S.op + T.op := rfl

/-- The exponential `e^T` of an operator that raises the particle number:
`(e^T ψ)(n) = Σ_{k ≤ ∣n∣} (Tᵏψ)(n)/k!`. -/
noncomputable def NumberRaisingOp.exp (T : NumberRaisingOp ι R) :
    Module.End ℂ (FormalFock ι R) where
  toFun ψ := ⟨fun n => ∑ k ∈ range (n.degree + 1),
    ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n⟩
  map_add' ψ φ := by
    ext n
    simp [smul_add, sum_add_distrib]
  map_smul' c ψ := by
    ext n
    simp [smul_sum, smul_comm c]

theorem NumberRaisingOp.coeff_exp (T : NumberRaisingOp ι R) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (T.exp ψ).coeff n =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n := rfl

/-- The exponential series may be summed to any bound `M ≥ ∣n∣`: the extra terms vanish. -/
theorem NumberRaisingOp.coeff_exp_eq_sum (T : NumberRaisingOp ι R) (ψ : FormalFock ι R)
    {n : ι →₀ ℕ} {M : ℕ} (hM : n.degree ≤ M) :
    (T.exp ψ).coeff n =
      ∑ k ∈ range (M + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n := by
  rw [NumberRaisingOp.coeff_exp]
  refine sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun k _ hk => ?_
  rw [mem_range, not_lt] at hk
  rw [T.raisesParticleNumber.coeff_pow_eq_zero ψ (by omega), smul_zero]

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

/-- The exponential law `e^{S+T} = e^S e^T` for commuting operators that raise the particle
number. -/
theorem NumberRaisingOp.exp_add (S T : NumberRaisingOp ι R) (hST : Commute S.op T.op) :
    (S + T).exp = S.exp * T.exp := by
  ext ψ n
  set M := n.degree
  set c : ℕ → ℂ := fun k => ((k.factorial : ℂ)⁻¹)
  set f : ℕ → ℕ → R := fun a b => ((S.op ^ a * T.op ^ b) ψ).coeff n
  -- the terms with more than `M` factors vanish at `n`
  have hf : ∀ a b, M < a + b → f a b = 0 := fun a b h => by
    have := S.raisesParticleNumber.vanishesBelow_pow a (T.raisesParticleNumber.vanishesBelow_pow b
      (vanishesBelow_zero ψ))
    exact this n (by simp only [zero_add] at this ⊢; omega)
  -- left side: binomial expansion of `(S + T)^k`
  have hL : ((S + T).exp ψ).coeff n =
      ∑ k ∈ range (M + 1), ∑ a ∈ range (k + 1), (c a * c (k - a)) • f a (k - a) := by
    rw [NumberRaisingOp.coeff_exp]
    refine sum_congr rfl fun k _ => ?_
    rw [NumberRaisingOp.add_op, hST.add_pow, LinearMap.sum_apply, coeff_sum, smul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [mem_range] at ha
    rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
      coeff_smul, smul_smul, inv_factorial_mul_choose (by omega)]
  -- right side: truncate `e^T ψ` at `M` particles, then expand
  have hR : (S.exp (T.exp ψ)).coeff n =
      ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a * c b) • f a b := by
    rw [NumberRaisingOp.coeff_exp]
    refine sum_congr rfl fun a _ => ?_
    have hagree : ∀ m : ι →₀ ℕ, m.degree ≤ M → (T.exp ψ).coeff m =
        (∑ b ∈ range (M + 1), c b • (T.op ^ b) ψ).coeff m := fun m hm => by
      rw [NumberRaisingOp.coeff_exp_eq_sum T ψ hm, coeff_sum]
      simp [c]
    rw [S.raisesParticleNumber.coeff_pow_eq_of_agree a hagree, map_sum, coeff_sum, smul_sum]
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

/-- The exponential depends only on the operator, not on the proof that it raises the particle
number. -/
theorem NumberRaisingOp.exp_congr {S T : NumberRaisingOp ι R} (h : S.op = T.op) :
    S.exp = T.exp := by
  cases S
  cases T
  cases h
  rfl

/-- The exponential of the zero operator is the identity. -/
theorem NumberRaisingOp.exp_of_op_eq_zero {T : NumberRaisingOp ι R} (hT : T.op = 0) :
    T.exp = 1 := by
  ext ψ m
  rw [NumberRaisingOp.coeff_exp, sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [hT, zero_pow hk, LinearMap.zero_apply, FormalFock.coeff_zero, smul_zero]
  · simp

/-- **Inverse exponentials**: `e^S e^T = 1` when the operators satisfy `S = -T`. -/
theorem NumberRaisingOp.exp_mul_eq_one {S T : NumberRaisingOp ι R} (h : S.op = -T.op) :
    S.exp * T.exp = 1 := by
  rw [← NumberRaisingOp.exp_add S T (by rw [h]; exact (Commute.refl _).neg_left)]
  exact NumberRaisingOp.exp_of_op_eq_zero (by rw [NumberRaisingOp.add_op, h, neg_add_cancel])

end Exp

section Create

variable [Ring R] [Algebra ℂ R]

theorem degree_sub_single_add_one {n : ι →₀ ℕ} {i : ι} (h : 0 < n i) :
    (n - Finsupp.single i 1).degree + 1 = n.degree := by
  conv_rhs => rw [← sub_single_add_single h]
  rw [map_add, Finsupp.degree_single]

/-- The creation operator raises the particle number. -/
theorem raisesParticleNumber_create (i : ι) : RaisesParticleNumber (create (R := R) i) :=
    fun k ψ h n hn => by
  rw [coeff_create]
  split_ifs with hi
  · rw [h _ (by have := degree_sub_single_add_one hi; omega), smul_zero]
  · rfl

/-- Left multiplication preserves vanishing below `k`. -/
theorem vanishesBelow_lmul (X : R) {k : ℕ} {ψ : FormalFock ι R} (h : VanishesBelow k ψ) :
    VanishesBelow k (lmul X ψ) := fun n hn => by
  rw [coeff_lmul, h n hn, mul_zero]

/-- `X ⊗ (aᵢ†)^p = lmul X ∘ (aᵢ†)^p` raises the particle number for `p ≥ 1`. -/
theorem raisesParticleNumber_lmul_mul_create_pow (X : R) (i : ι) {p : ℕ} (hp : 1 ≤ p) :
    RaisesParticleNumber (lmul X * create (R := R) i ^ p) := fun k ψ h n hn => by
  have := (raisesParticleNumber_create i).vanishesBelow_pow p h
  exact vanishesBelow_lmul X this n (by omega)

/-- A word `X ⊗ a†_{i₁} ⋯ a†_{i_r}` in the creation operators, `r ≥ 1`, with a coefficient
`X ∈ R` on the left, raises the particle number. -/
theorem raisesParticleNumber_lmul_mul_prod_create (X : R) {l : List ι} (hl : l ≠ []) :
    RaisesParticleNumber
      (lmul X * (l.map fun i => (create (R := R) i : Module.End ℂ (FormalFock ι R))).prod) :=
    fun k ψ h n hn => by
  have := vanishesBelow_list_prod (l.map fun i => (create (R := R) i : Module.End ℂ _))
    (fun T hT => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hT
      exact raisesParticleNumber_create i) h
  have hlen : 1 ≤ (l.map fun i => (create (R := R) i : Module.End ℂ (FormalFock ι R))).length := by
    rw [List.length_map]
    exact List.length_pos_iff.2 hl
  exact vanishesBelow_lmul X this n (by omega)

/-- **Every polynomial in the creation operators with zero constant term raises the particle
number**: a finite sum of words `X_k ⊗ a†_{i₁} ⋯ a†_{i_r}` with `r ≥ 1` and coefficients
`X_k ∈ R` on the left, such as `κ (a†)² + ℓ a†` or `K ⊗ (a†)² + L ⊗ a†`. -/
theorem raisesParticleNumber_sum_lmul_mul_prod_create {κ : Type*} (s : Finset κ) (X : κ → R)
    (w : κ → List ι) (hw : ∀ k ∈ s, w k ≠ []) :
    RaisesParticleNumber (∑ k ∈ s,
      lmul (X k) * ((w k).map fun i => (create (R := R) i : Module.End ℂ (FormalFock ι R))).prod) :=
  RaisesParticleNumber.sum s fun k hk => raisesParticleNumber_lmul_mul_prod_create (X k) (hw k hk)

/-- The generator `X ⊗ (aᵢ†)^p` (`p ≥ 1`), which raises the particle number. -/
noncomputable def gen (X : R) (i : ι) (p : ℕ) (hp : 1 ≤ p) : NumberRaisingOp ι R :=
  ⟨lmul X * create i ^ p, raisesParticleNumber_lmul_mul_create_pow X i hp⟩

end Create

section Scalar

/-- With a scalar coefficient, the generator `c ⊗ (aⱼ†)^p` is the operator `c (aⱼ†)^p`. -/
theorem gen_op_eq_smul (c : ℂ) (j : ι) {p : ℕ} (hp : 1 ≤ p) :
    (gen c j p hp : NumberRaisingOp ι ℂ).op = c • create j ^ p := by
  ext ψ m
  simp [gen, Module.End.mul_apply, coeff_lmul]

/-- Generators with scalar coefficients commute, on any modes. -/
theorem commute_gen_gen (c c' : ℂ) (i j : ι) {p p' : ℕ} (hp : 1 ≤ p) (hp' : 1 ≤ p') :
    Commute (gen c i p hp : NumberRaisingOp ι ℂ).op (gen c' j p' hp').op := by
  rw [gen_op_eq_smul, gen_op_eq_smul]
  exact ((commute_iff_lie_eq.mpr (lie_create_create i j)).pow_pow p p' |>.smul_left c).smul_right c'

end Scalar

end BosonicLean.Fock.FormalFock

/-! Deprecated names (B4.5, decision 5: standard terminology). They keep the old signatures, so
that code written for the names `IsRaising`, `RaisingOp` and `raisingExp`, including its dot
notation, still compiles. -/

namespace BosonicLean.Fock.FormalFock

variable {ι R : Type*}

section Deprecated

set_option linter.deprecated false

variable [AddCommGroup R] [Module ℂ R]

/-- Deprecated name of `RaisesParticleNumber`. -/
@[deprecated RaisesParticleNumber (since := "2026-10-19")]
abbrev IsRaising (T : Module.End ℂ (FormalFock ι R)) : Prop := RaisesParticleNumber T

namespace IsRaising

variable {S T : Module.End ℂ (FormalFock ι R)}

@[deprecated RaisesParticleNumber.vanishesBelow_pow (since := "2026-10-19")]
theorem vanishesBelow_pow (hT : IsRaising T) (a : ℕ) {k : ℕ} {ψ : FormalFock ι R}
    (h : VanishesBelow k ψ) : VanishesBelow (k + a) ((T ^ a) ψ) :=
  RaisesParticleNumber.vanishesBelow_pow hT a h

@[deprecated RaisesParticleNumber.coeff_pow_eq_zero (since := "2026-10-19")]
theorem coeff_pow_eq_zero (hT : IsRaising T) {a : ℕ} (ψ : FormalFock ι R) {n : ι →₀ ℕ}
    (h : n.degree < a) : ((T ^ a) ψ).coeff n = 0 :=
  RaisesParticleNumber.coeff_pow_eq_zero hT ψ h

@[deprecated RaisesParticleNumber.coeff_pow_eq_of_agree (since := "2026-10-19")]
theorem coeff_pow_eq_of_agree (hT : IsRaising T) (a : ℕ) {ψ φ : FormalFock ι R}
    {n : ι →₀ ℕ} (h : ∀ m : ι →₀ ℕ, m.degree ≤ n.degree → ψ.coeff m = φ.coeff m) :
    ((T ^ a) ψ).coeff n = ((T ^ a) φ).coeff n :=
  RaisesParticleNumber.coeff_pow_eq_of_agree hT a h

@[deprecated RaisesParticleNumber.coeff_eq_of_agree (since := "2026-10-19")]
theorem coeff_eq_of_agree (hT : IsRaising T) {ψ φ : FormalFock ι R} {n : ι →₀ ℕ}
    (h : ∀ m : ι →₀ ℕ, m.degree < n.degree → ψ.coeff m = φ.coeff m) :
    (T ψ).coeff n = (T φ).coeff n :=
  RaisesParticleNumber.coeff_eq_of_agree hT h

@[deprecated RaisesParticleNumber.add (since := "2026-10-19")]
theorem add (hS : IsRaising S) (hT : IsRaising T) : IsRaising (S + T) :=
  RaisesParticleNumber.add hS hT

@[deprecated RaisesParticleNumber.mul (since := "2026-10-19")]
theorem mul (hS : IsRaising S) (hT : IsRaising T) : IsRaising (S * T) :=
  RaisesParticleNumber.mul hS hT

@[deprecated RaisesParticleNumber.smul (since := "2026-10-19")]
theorem smul (hT : IsRaising T) (c : ℂ) : IsRaising (c • T) :=
  RaisesParticleNumber.smul hT c

end IsRaising

/-- Deprecated name of `NumberRaisingOp`. -/
@[deprecated NumberRaisingOp (since := "2026-10-19")]
abbrev RaisingOp (ι R : Type*) [AddCommGroup R] [Module ℂ R] := NumberRaisingOp ι R

@[deprecated NumberRaisingOp.mk (since := "2026-10-19")]
abbrev RaisingOp.mk (op : Module.End ℂ (FormalFock ι R)) (h : IsRaising op) : RaisingOp ι R :=
  ⟨op, h⟩

@[deprecated NumberRaisingOp.raisesParticleNumber (since := "2026-10-19")]
theorem RaisingOp.isRaising (T : RaisingOp ι R) : IsRaising T.op :=
  T.raisesParticleNumber

@[deprecated NumberRaisingOp.add_op (since := "2026-10-19")]
theorem RaisingOp.add_op (S T : RaisingOp ι R) : (S + T).op = S.op + T.op := rfl

/-- Deprecated name of `NumberRaisingOp.exp`. -/
@[deprecated NumberRaisingOp.exp (since := "2026-10-19")]
noncomputable abbrev raisingExp (T : RaisingOp ι R) : Module.End ℂ (FormalFock ι R) := T.exp

@[deprecated NumberRaisingOp.coeff_exp (since := "2026-10-19")]
theorem coeff_raisingExp (T : RaisingOp ι R) (ψ : FormalFock ι R) (n : ι →₀ ℕ) :
    (raisingExp T ψ).coeff n =
      ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n :=
  NumberRaisingOp.coeff_exp T ψ n

@[deprecated NumberRaisingOp.coeff_exp_eq_sum (since := "2026-10-19")]
theorem coeff_raisingExp_eq_sum (T : RaisingOp ι R) (ψ : FormalFock ι R) {n : ι →₀ ℕ} {M : ℕ}
    (hM : n.degree ≤ M) :
    (raisingExp T ψ).coeff n =
      ∑ k ∈ Finset.range (M + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n :=
  NumberRaisingOp.coeff_exp_eq_sum T ψ hM

@[deprecated NumberRaisingOp.exp_add (since := "2026-10-19")]
theorem raisingExp_add (S T : RaisingOp ι R) (hST : Commute S.op T.op) :
    raisingExp (S + T) = raisingExp S * raisingExp T :=
  NumberRaisingOp.exp_add S T hST

@[deprecated NumberRaisingOp.exp_congr (since := "2026-10-19")]
theorem raisingExp_congr {S T : RaisingOp ι R} (h : S.op = T.op) :
    raisingExp S = raisingExp T :=
  NumberRaisingOp.exp_congr h

@[deprecated NumberRaisingOp.exp_of_op_eq_zero (since := "2026-10-19")]
theorem raisingExp_of_op_eq_zero {T : RaisingOp ι R} (hT : T.op = 0) : raisingExp T = 1 :=
  NumberRaisingOp.exp_of_op_eq_zero hT

@[deprecated NumberRaisingOp.exp_mul_eq_one (since := "2026-10-19")]
theorem raisingExp_mul_eq_one {S T : RaisingOp ι R} (h : S.op = -T.op) :
    raisingExp S * raisingExp T = 1 :=
  NumberRaisingOp.exp_mul_eq_one h

end Deprecated

section DeprecatedCreate

set_option linter.deprecated false

variable [Ring R] [Algebra ℂ R]

@[deprecated raisesParticleNumber_create (since := "2026-10-19")]
theorem isRaising_create (i : ι) : IsRaising (create (R := R) i) :=
  raisesParticleNumber_create i

@[deprecated raisesParticleNumber_lmul_mul_create_pow (since := "2026-10-19")]
theorem isRaising_lmul_mul_create_pow (X : R) (i : ι) {p : ℕ} (hp : 1 ≤ p) :
    IsRaising (lmul X * create (R := R) i ^ p) :=
  raisesParticleNumber_lmul_mul_create_pow X i hp

end DeprecatedCreate

end BosonicLean.Fock.FormalFock
