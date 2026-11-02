/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Bargmann
import BosonicLean.Fock.NumberState
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# One mode in the Bargmann picture

For a single mode the Bargmann map takes values in formal power series in one variable,
`β : ℱ → ℂ⟦z⟧`, with `β(a ψ) = ∂ β(ψ)` and `β(p(a†) ψ) = p β(ψ)` for a polynomial `p`. The
operator `e^{κ (a†)² + ℓ a†}` becomes multiplication by `e^{κ z² + ℓ z}`, and the photon-added
Gaussian (squeezed coherent) state `∣q, κ, ℓ⟩ = (a†)^q e^{κ (a†)² + ℓ a†} ∣0⟩` becomes
`z^q e^{κ z² + ℓ z}`. With `σ p = p' + (2κ z + ℓ) p` one has
`∂ (p e^{κ z² + ℓ z}) = (σ p) e^{κ z² + ℓ z}`. Polynomial multiples of Gaussians with distinct
pairs `(κ, ℓ)` are linearly independent.

## Main definitions

* `BosonicLean.Fock.FormalFock.bargmann`: the Bargmann map of one mode into `ℂ⟦X⟧`.
* `BosonicLean.Fock.FormalFock.gaussExp κ ℓ`: the operator `e^{κ (a†)² + ℓ a†}`.
* `BosonicLean.Fock.FormalFock.photonAdded q κ ℓ`: the state `∣q, κ, ℓ⟩`;
  `gaussVec κ ℓ = ∣0, κ, ℓ⟩`.
* `BosonicLean.Fock.FormalFock.gaussDeriv κ ℓ`: the operator `σ` on polynomials.
* `BosonicLean.Fock.FormalFock.photonClass κ ℓ`: the span of the states `∣q, κ, ℓ⟩`, the vectors
  `p(a†) ∣0, κ, ℓ⟩` with `p` a polynomial.

## Main results

* `bargmann_annihilate`, `bargmann_aeval_create`: `a ↦ ∂`, `p(a†) ↦ p`.
* `gaussExp_mul_gaussExp`, `gaussExp_neg_mul_gaussExp`: the group law of the Gaussian operators.
* `dz_bargmann_gaussVec`: `∂ e^{κ z² + ℓ z} = (2κ z + ℓ) e^{κ z² + ℓ z}`.
* `eq_zero_of_sum_mul_gaussVec`: independence of polynomial multiples of distinct Gaussians.
* `annihilate_mem_photonClass`, `create_mem_photonClass`, `gaussExp_mem_photonClass`: `a`, `a†`
  preserve the class at `(κ, ℓ)`, and `e^{κ (a†)² + ℓ a†}` maps the class at `(0, 0)` into it.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform.
  Part I*, Comm. Pure Appl. Math. 14 (1961) 187–214.
-/

open Finset Polynomial

namespace BosonicLean.Fock.FormalFock

/-! ### The Bargmann map of one mode -/

/-- The formal derivative on `ℂ⟦X⟧` as a linear map. -/
noncomputable abbrev dz : PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ :=
  (PowerSeries.derivative (R := ℂ)).toLinearMap

theorem dz_apply (f : PowerSeries ℂ) : dz f = PowerSeries.derivative f := rfl

/-- The Bargmann map of a single mode, with values in `ℂ⟦X⟧`. -/
noncomputable def bargmann : FormalFock Unit ℂ →ₗ[ℂ] PowerSeries ℂ := toBargmann.toLinearMap

theorem bargmann_apply (ψ : FormalFock Unit ℂ) : bargmann ψ = toBargmann ψ := rfl

theorem bargmann_injective : Function.Injective bargmann := toBargmann.injective

theorem bargmann_annihilate (ψ : FormalFock Unit ℂ) :
    bargmann (annihilate () ψ) = dz (bargmann ψ) :=
  toBargmann_annihilate_complex () ψ

theorem bargmann_annihilate_pow (r : ℕ) (ψ : FormalFock Unit ℂ) :
    bargmann (((annihilate () : Module.End ℂ (FormalFock Unit ℂ)) ^ r) ψ) =
      (dz ^ r) (bargmann ψ) := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', Module.End.mul_apply, bargmann_annihilate, ih, pow_succ',
      Module.End.mul_apply]

/-- In the Bargmann picture `p(a†)` is multiplication by `p`. -/
theorem bargmann_aeval_create (p : ℂ[X]) (ψ : FormalFock Unit ℂ) :
    bargmann (aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) p ψ) =
      (p : PowerSeries ℂ) * bargmann ψ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, map_add, hp, hq, Polynomial.coe_add, add_mul]
  | monomial k c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      LinearMap.smul_apply, map_smul, bargmann_apply, bargmann_apply, toBargmann_create_pow,
      ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X]
    change (c • (PowerSeries.X ^ k * (toBargmann ψ : PowerSeries ℂ)) : PowerSeries ℂ) = _
    rw [PowerSeries.smul_eq_C_mul, mul_assoc]

/-- `q(a†) a^r` is `q ∂^r` in the Bargmann picture. -/
theorem bargmann_aeval_mul_pow (q : ℂ[X]) (r : ℕ) (ψ : FormalFock Unit ℂ) :
    bargmann ((aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) q *
      (annihilate () : Module.End ℂ (FormalFock Unit ℂ)) ^ r) ψ) =
        (q : PowerSeries ℂ) * (dz ^ r) (bargmann ψ) := by
  rw [Module.End.mul_apply, bargmann_aeval_create, bargmann_annihilate_pow]

/-- The derivative of the coerced polynomial is the coerced derivative, iterated. -/
theorem dz_pow_coe (r : ℕ) (p : ℂ[X]) :
    (dz ^ r) (p : PowerSeries ℂ) = ((derivative^[r] p : ℂ[X]) : PowerSeries ℂ) := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply, Function.iterate_succ_apply, dz_apply,
      PowerSeries.derivative_coe]
    exact ih _

/-! ### The Gaussian operator and the photon-added states -/

/-- The Gaussian operator `e^{κ (a†)² + ℓ a†}` of one mode. -/
noncomputable def gaussExp (κ ℓ : ℂ) : Module.End ℂ (FormalFock Unit ℂ) :=
  (gen κ () 2 (by norm_num) + gen ℓ () 1 le_rfl).exp

/-- The **photon-added Gaussian (squeezed coherent) state**
`∣q, κ, ℓ⟩ = (a†)^q e^{κ (a†)² + ℓ a†} ∣0⟩` of one mode, unnormalized, on the formal Fock space. -/
noncomputable def photonAdded (q : ℕ) (κ ℓ : ℂ) : FormalFock Unit ℂ :=
  (create () ^ q) ((gen κ () 2 (by norm_num) + gen ℓ () 1 le_rfl).exp (numberState 0))

/-- The Gaussian vector `e^{κ (a†)² + ℓ a†} ∣0⟩ = ∣0, κ, ℓ⟩`. -/
noncomputable abbrev gaussVec (κ ℓ : ℂ) : FormalFock Unit ℂ := photonAdded 0 κ ℓ

theorem gaussExp_vacuum (κ ℓ : ℂ) : gaussExp κ ℓ (numberState 0) = gaussVec κ ℓ := by
  rw [gaussVec, photonAdded, pow_zero, Module.End.one_apply]; rfl

/-- In the Bargmann picture, `∣q, κ, ℓ⟩` is the series `z^q e^{κ z²} e^{ℓ z}`. -/
theorem toBargmann_photonAdded (q : ℕ) (κ ℓ : ℂ) :
    toBargmann (photonAdded q κ ℓ) =
      MvPowerSeries.X () ^ q * (expSeries κ () 2 * expSeries ℓ () 1) := by
  rw [photonAdded, toBargmann_create_pow,
    NumberRaisingOp.exp_add _ _ (commute_gen_gen κ ℓ () () _ _),
    Module.End.mul_apply, toBargmann_exp_gen, toBargmann_exp_gen, numberState,
    Finsupp.single_zero, toBargmann_vacuum, map_one, mul_one]

/-- `e^{κ (a†)² + ℓ a†} e^{κ' (a†)² + ℓ' a†} = e^{(κ + κ') (a†)² + (ℓ + ℓ') a†}`. -/
theorem gaussExp_mul_gaussExp (κ ℓ κ' ℓ' : ℂ) :
    gaussExp κ ℓ * gaussExp κ' ℓ' = gaussExp (κ + κ') (ℓ + ℓ') := by
  rw [gaussExp, gaussExp, gaussExp, ← NumberRaisingOp.exp_add]
  · apply NumberRaisingOp.exp_congr
    simp only [NumberRaisingOp.add_op, gen_op_eq_smul, add_smul]
    abel
  · simp only [NumberRaisingOp.add_op]
    exact ((commute_gen_gen _ _ _ _ _ _).add_right (commute_gen_gen _ _ _ _ _ _)).add_left
      ((commute_gen_gen _ _ _ _ _ _).add_right (commute_gen_gen _ _ _ _ _ _))

/-- `e^{0} = 1`. -/
theorem gaussExp_zero : gaussExp 0 0 = 1 :=
  NumberRaisingOp.exp_of_op_eq_zero (by simp [NumberRaisingOp.add_op, gen_op_eq_smul])

/-- `e^{-κ (a†)² - ℓ a†} e^{κ (a†)² + ℓ a†} = 1`. -/
theorem gaussExp_neg_mul_gaussExp (κ ℓ : ℂ) : gaussExp (-κ) (-ℓ) * gaussExp κ ℓ = 1 :=
  NumberRaisingOp.exp_mul_eq_one
    (by simp only [NumberRaisingOp.add_op, gen_op_eq_smul, neg_smul]; abel)

/-- In the Bargmann picture `e^{κ (a†)² + ℓ a†}` is multiplication by its value on `∣0⟩`. -/
theorem bargmann_gaussExp (κ ℓ : ℂ) (ψ : FormalFock Unit ℂ) :
    bargmann (gaussExp κ ℓ ψ) = bargmann (gaussVec κ ℓ) * bargmann ψ := by
  have h : ∀ φ : FormalFock Unit ℂ, bargmann (gaussExp κ ℓ φ) =
      MvPowerSeries.X () ^ 0 * (expSeries κ () 2 * expSeries ℓ () 1) * bargmann φ := fun φ => by
    rw [gaussExp, NumberRaisingOp.exp_add _ _ (commute_gen_gen κ ℓ () () _ _), Module.End.mul_apply,
      bargmann_apply, bargmann_apply, toBargmann_exp_gen, toBargmann_exp_gen,
      pow_zero, one_mul, mul_assoc]
  rw [h, ← gaussExp_vacuum, h, bargmann_apply (numberState 0), numberState, Finsupp.single_zero,
    toBargmann_vacuum, map_one, mul_one]

/-- **Products of Gaussians**: `e^{κ z² + ℓ z} e^{κ' z² + ℓ' z} = e^{(κ + κ') z² + (ℓ + ℓ') z}`. -/
theorem bargmann_gaussVec_mul (κ ℓ κ' ℓ' : ℂ) :
    bargmann (gaussVec κ ℓ) * bargmann (gaussVec κ' ℓ') =
      bargmann (gaussVec (κ + κ') (ℓ + ℓ')) := by
  rw [← bargmann_gaussExp, ← gaussExp_vacuum κ', ← Module.End.mul_apply, gaussExp_mul_gaussExp,
    gaussExp_vacuum]

/-- The Gaussian with `κ = ℓ = 0` is the constant series `1`. -/
theorem bargmann_gaussVec_zero : bargmann (gaussVec 0 0) = 1 := by
  rw [← gaussExp_vacuum, gaussExp_zero, Module.End.one_apply, bargmann_apply (numberState 0),
    numberState, Finsupp.single_zero, toBargmann_vacuum, map_one]

/-- In the Bargmann picture `∣q, κ, ℓ⟩` is `z^q e^{κ z² + ℓ z}`. -/
theorem bargmann_photonAdded (q : ℕ) (κ ℓ : ℂ) :
    bargmann (photonAdded q κ ℓ) =
      ((X ^ q : ℂ[X]) : PowerSeries ℂ) * bargmann (gaussVec κ ℓ) := by
  rw [← bargmann_aeval_create, aeval_X_pow, gaussVec, photonAdded, photonAdded, pow_zero,
    Module.End.one_apply]

/-! ### The derivative of the Gaussian -/

/-- The coefficients of `E_c^{(p)}(z) = Σₖ cᵏ z^{pk}/k!`: `(m/p)!⁻¹ c^{m/p}` if `p ∣ m`, else
`0`. -/
theorem coeff_expSeries_unit (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    PowerSeries.coeff m (expSeries c () p : PowerSeries ℂ) =
      if p ∣ m then (((m / p).factorial : ℂ)⁻¹) * c ^ (m / p) else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () m) (expSeries c () p) = _
  rw [coeff_expSeries, Finsupp.single_eq_same]
  simp only [(Finsupp.single_injective ()).eq_iff, smul_eq_mul]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_div_cancel_left k (by omega), sum_eq_single k]
    · simp
    · intro b _ hb
      simp only [Nat.mul_left_cancel_iff (by omega : 0 < p), Ne.symm hb, ↓reduceIte]
    · intro hk
      exact absurd (mem_range.mpr (by nlinarith)) hk
  · exact sum_eq_zero fun k _ => by
      simp only [show ¬ m = p * k from fun h' => h ⟨k, h'⟩, ↓reduceIte]

/-- **The derivative of `E_c^{(p)}`**: `∂ E_c^{(p)} = p c z^{p-1} E_c^{(p)}`. -/
theorem dz_expSeries (c : ℂ) {p : ℕ} (hp : 1 ≤ p) :
    dz (expSeries c () p : PowerSeries ℂ) =
      PowerSeries.C ((p : ℂ) * c) * PowerSeries.X ^ (p - 1) *
        (expSeries c () p : PowerSeries ℂ) := by
  ext m
  rw [dz_apply, PowerSeries.coeff_derivative, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', coeff_expSeries_unit c hp, coeff_expSeries_unit c hp]
  by_cases hm : p - 1 ≤ m
  · have he : m + 1 = (m - (p - 1)) + p := by omega
    by_cases hd : p ∣ m + 1
    · have hd' : p ∣ m - (p - 1) := by
        rw [he] at hd
        exact (Nat.dvd_add_left (dvd_refl p)).mp hd
      simp only [hm, hd, hd', ↓reduceIte]
      obtain ⟨k, hk⟩ := hd'
      have h1 : (m + 1) / p = k + 1 := by
        rw [he, hk, show p * k + p = p * (k + 1) by ring, Nat.mul_div_cancel_left _ (by omega)]
      have h2 : (m - (p - 1)) / p = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
      rw [h1, h2, Nat.factorial_succ]
      have hm1 : ((m : ℂ) + 1) = (p : ℂ) * (k + 1) := by
        have : m + 1 = p * (k + 1) := by rw [he, hk]; ring
        exact_mod_cast this
      have hf : ((k.factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      push_cast
      rw [hm1]
      field_simp
      ring
    · have hd' : ¬ p ∣ m - (p - 1) := fun h' => hd (by rw [he]; exact dvd_add h' (dvd_refl p))
      simp only [hm, hd, hd', ↓reduceIte, zero_mul, mul_zero]
  · have hd : ¬ p ∣ m + 1 := fun ⟨k, hk⟩ => by
      rcases k with _ | k
      · omega
      · have : p * (k + 1) ≥ p := Nat.le_mul_of_pos_right p (by omega)
        omega
    simp only [hm, hd, ↓reduceIte, zero_mul, mul_zero]

/-- **The Gaussian solves `∂ g = (2κz + ℓ) g`**. -/
theorem dz_bargmann_gaussVec (κ ℓ : ℂ) :
    dz (bargmann (gaussVec κ ℓ)) =
      ((C (2 * κ) * X + C ℓ : ℂ[X]) : PowerSeries ℂ) * bargmann (gaussVec κ ℓ) := by
  have hg : bargmann (gaussVec κ ℓ) =
      (expSeries κ () 2 : PowerSeries ℂ) * (expSeries ℓ () 1 : PowerSeries ℂ) := by
    rw [bargmann_apply, toBargmann_photonAdded, pow_zero, one_mul]
  rw [hg, dz_apply, Derivation.leibniz, ← dz_apply, ← dz_apply, dz_expSeries κ (by norm_num),
    dz_expSeries ℓ le_rfl]
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    smul_eq_mul, Nat.cast_ofNat, Nat.cast_one, one_mul, pow_one, pow_zero, mul_one,
    Nat.add_one_sub_one, Nat.sub_self]
  ring

/-! ### The operator `σ` and the independence of Gaussian multiples -/

/-- The operator `σ p = p' + (2κ X + ℓ) p` on polynomials, with
`∂ (p e^{κ z² + ℓ z}) = (σ p) e^{κ z² + ℓ z}`. -/
noncomputable def gaussDeriv (κ ℓ : ℂ) (p : ℂ[X]) : ℂ[X] :=
  derivative p + (C (2 * κ) * X + C ℓ) * p

/-- `∂ (p e^{κ z² + ℓ z}) = (σ p) e^{κ z² + ℓ z}`. -/
theorem dz_coe_mul_bargmann_gaussVec (κ ℓ : ℂ) (p : ℂ[X]) :
    dz ((p : PowerSeries ℂ) * bargmann (gaussVec κ ℓ)) =
      (gaussDeriv κ ℓ p : PowerSeries ℂ) * bargmann (gaussVec κ ℓ) := by
  rw [dz_apply, Derivation.leibniz, PowerSeries.derivative_coe, ← dz_apply, dz_bargmann_gaussVec]
  simp only [gaussDeriv, Polynomial.coe_add, Polynomial.coe_mul, smul_eq_mul]
  ring

/-- `∂^N (p e^{κ z² + ℓ z}) = (σ^N p) e^{κ z² + ℓ z}`. -/
theorem dz_pow_coe_mul_bargmann_gaussVec (κ ℓ : ℂ) (N : ℕ) (p : ℂ[X]) :
    (dz ^ N) ((p : PowerSeries ℂ) * bargmann (gaussVec κ ℓ)) =
      ((gaussDeriv κ ℓ)^[N] p : PowerSeries ℂ) * bargmann (gaussVec κ ℓ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, ih, dz_coe_mul_bargmann_gaussVec,
      Function.iterate_succ_apply']

/-- For `(κ, ℓ) ≠ (0, 0)`, `σ` does not annihilate a nonzero polynomial: the term `(2κX + ℓ) p`
has degree above that of `p'`. -/
theorem gaussDeriv_ne_zero {κ ℓ : ℂ} (hc : ¬ (κ = 0 ∧ ℓ = 0)) {p : ℂ[X]} (hp : p ≠ 0) :
    gaussDeriv κ ℓ p ≠ 0 := by
  set h : ℂ[X] := C (2 * κ) * X + C ℓ
  have hh : h ≠ 0 := fun h0 => hc ⟨by
    have := congrArg (fun q : ℂ[X] => q.coeff 1) h0
    simpa [h] using this, by
    have := congrArg (fun q : ℂ[X] => q.coeff 0) h0
    simpa [h] using this⟩
  intro h0
  have key : (derivative p + h * p).coeff (h.natDegree + p.natDegree) = 0 := by
    rw [show derivative p + h * p = gaussDeriv κ ℓ p from rfl, h0, Polynomial.coeff_zero]
  rw [Polynomial.coeff_add, Polynomial.coeff_derivative,
    coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, zero_add,
    coeff_mul_degree_add_degree] at key
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hh) (leadingCoeff_ne_zero.mpr hp) key

/-- For `(κ, ℓ) ≠ (0, 0)`, `σ^N` does not annihilate a nonzero polynomial. -/
theorem iterate_gaussDeriv_ne_zero {κ ℓ : ℂ} (hc : ¬ (κ = 0 ∧ ℓ = 0)) (N : ℕ) {p : ℂ[X]}
    (hp : p ≠ 0) : (gaussDeriv κ ℓ)^[N] p ≠ 0 := by
  induction N with
  | zero => exact hp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact gaussDeriv_ne_zero hc ih

/-- **Independence of polynomial multiples of Gaussians** with distinct pairs: if
`Σ_{i ∈ s} u_i e^{κ_i z² + ℓ_i z} = 0` in `ℂ⟦X⟧` with the pairs `(κ_i, ℓ_i)` distinct on `s`, every
`u_i` vanishes. -/
theorem eq_zero_of_sum_mul_gaussVec {ι : Type*} (s : Finset ι) (κ ℓ : ι → ℂ)
    (hinj : Set.InjOn (fun i => (κ i, ℓ i)) s) (u : ι → ℂ[X])
    (h : ∑ i ∈ s, (u i : PowerSeries ℂ) * bargmann (gaussVec (κ i) (ℓ i)) = 0) :
    ∀ i ∈ s, u i = 0 := by
  classical
  induction s using Finset.induction_on generalizing κ ℓ u with
  | empty => simp
  | insert a s ha ih =>
    -- divide by `e^{κ_a z² + ℓ_a z}`
    set κ' : ι → ℂ := fun i => κ i - κ a
    set ℓ' : ι → ℂ := fun i => ℓ i - ℓ a
    have h' : ∑ i ∈ insert a s, (u i : PowerSeries ℂ) * bargmann (gaussVec (κ' i) (ℓ' i)) = 0 := by
      have := congrArg (bargmann (gaussVec (-κ a) (-ℓ a)) * ·) h
      simp only [mul_zero, mul_sum, mul_left_comm _ (u _ : PowerSeries ℂ),
        bargmann_gaussVec_mul, neg_add_eq_sub] at this
      exact this
    rw [sum_insert ha, show κ' a = 0 from sub_self _, show ℓ' a = 0 from sub_self _,
      bargmann_gaussVec_zero, mul_one] at h'
    -- differentiate `deg u_a + 1` times
    set N := (u a).natDegree + 1
    have hN := congrArg (dz ^ N) h'
    rw [map_add, map_sum, map_zero, dz_pow_coe, iterate_derivative_eq_zero (Nat.lt_succ_self _),
      Polynomial.coe_zero, zero_add] at hN
    simp only [dz_pow_coe_mul_bargmann_gaussVec] at hN
    have hinj' : Set.InjOn (fun i => (κ' i, ℓ' i)) s := fun i hi j hj hij => by
      simp only [Prod.mk.injEq, κ', ℓ', sub_left_inj] at hij
      exact hinj (mem_insert_of_mem hi) (mem_insert_of_mem hj) (Prod.ext hij.1 hij.2)
    have hs := ih κ' ℓ' hinj' (fun i => (gaussDeriv (κ' i) (ℓ' i))^[N] (u i)) hN
    have hs' : ∀ i ∈ s, u i = 0 := fun i hi => by
      by_contra hu
      refine iterate_gaussDeriv_ne_zero (fun hc => ?_) N hu (hs i hi)
      have hia : i ≠ a := fun hia => ha (hia ▸ hi)
      exact hia (hinj (mem_insert_of_mem hi) (mem_insert_self a s)
        (Prod.ext (sub_eq_zero.mp hc.1) (sub_eq_zero.mp hc.2)))
    have hsum : ∑ i ∈ s, (u i : PowerSeries ℂ) * bargmann (gaussVec (κ' i) (ℓ' i)) = 0 :=
      sum_eq_zero fun i hi => by rw [hs' i hi, Polynomial.coe_zero, zero_mul]
    rw [hsum, add_zero, Polynomial.coe_eq_zero_iff] at h'
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact h'
    · exact hs' i hi

/-! ### The photon-added class -/

/-- The span of the photon-added squeezed coherent states with parameters `(κ, ℓ)`; in the
Bargmann picture the series `p(z) e^{κ z² + ℓ z}` with `p` a polynomial. -/
noncomputable def photonClass (κ ℓ : ℂ) : Submodule ℂ (FormalFock Unit ℂ) :=
  Submodule.span ℂ (Set.range fun q : ℕ => photonAdded q κ ℓ)

/-- `∣q, κ, ℓ⟩ = (a†)^q ∣0, κ, ℓ⟩`. -/
theorem photonAdded_eq_aeval (q : ℕ) (κ ℓ : ℂ) :
    photonAdded q κ ℓ =
      aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) (X ^ q : ℂ[X]) (gaussVec κ ℓ) := by
  rw [aeval_X_pow, gaussVec, photonAdded, photonAdded, pow_zero, Module.End.one_apply]

/-- The class at `(κ, ℓ)` consists of the vectors `p(a†) ∣0, κ, ℓ⟩` with `p` a polynomial. -/
theorem mem_photonClass_iff {κ ℓ : ℂ} {ψ : FormalFock Unit ℂ} :
    ψ ∈ photonClass κ ℓ ↔
      ∃ p : ℂ[X], aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) p (gaussVec κ ℓ) = ψ := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact ⟨X ^ q, (photonAdded_eq_aeval q κ ℓ).symm⟩
    | zero => exact ⟨0, by rw [map_zero, LinearMap.zero_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨p', rfl⟩ := hy
      exact ⟨p + p', by rw [map_add, LinearMap.add_apply]⟩
    | smul c x _ hx =>
      obtain ⟨p, rfl⟩ := hx
      exact ⟨c • p, by rw [map_smul, LinearMap.smul_apply]⟩
  · rintro ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
      rw [map_add, LinearMap.add_apply]
      exact add_mem hp hp'
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, LinearMap.smul_apply,
        ← photonAdded_eq_aeval]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨n, rfl⟩)

/-- `a† (p(a†) ∣0, κ, ℓ⟩) = (X p)(a†) ∣0, κ, ℓ⟩`. -/
theorem create_aeval_gaussVec (κ ℓ : ℂ) (p : ℂ[X]) :
    create () (aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) p (gaussVec κ ℓ)) =
      aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) (X * p) (gaussVec κ ℓ) := by
  rw [map_mul, aeval_X, Module.End.mul_apply]

/-- `a (p(a†) ∣0, κ, ℓ⟩) = (σ p)(a†) ∣0, κ, ℓ⟩` with `σ p = p' + (2κ X + ℓ) p`. -/
theorem annihilate_aeval_gaussVec (κ ℓ : ℂ) (p : ℂ[X]) :
    annihilate () (aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) p (gaussVec κ ℓ)) =
      aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) (gaussDeriv κ ℓ p) (gaussVec κ ℓ) :=
  bargmann_injective (by
    rw [bargmann_annihilate, bargmann_aeval_create, bargmann_aeval_create,
      dz_coe_mul_bargmann_gaussVec])

/-- The class at `(κ, ℓ)` is invariant under `a`. -/
theorem annihilate_mem_photonClass {κ ℓ : ℂ} {ψ : FormalFock Unit ℂ} (h : ψ ∈ photonClass κ ℓ) :
    annihilate () ψ ∈ photonClass κ ℓ := by
  obtain ⟨p, rfl⟩ := mem_photonClass_iff.mp h
  exact mem_photonClass_iff.mpr ⟨_, (annihilate_aeval_gaussVec κ ℓ p).symm⟩

/-- The class at `(κ, ℓ)` is invariant under `a†`. -/
theorem create_mem_photonClass {κ ℓ : ℂ} {ψ : FormalFock Unit ℂ} (h : ψ ∈ photonClass κ ℓ) :
    create () ψ ∈ photonClass κ ℓ := by
  obtain ⟨p, rfl⟩ := mem_photonClass_iff.mp h
  exact mem_photonClass_iff.mpr ⟨_, (create_aeval_gaussVec κ ℓ p).symm⟩

/-- A subspace invariant under `T` is invariant under every polynomial in `T`. This is Mathlib's
`Polynomial.aeval_apply_smul_mem_of_le_comap`, which the library now uses. -/
@[deprecated "use `Polynomial.aeval_apply_smul_mem_of_le_comap`" (since := "2026-10-21")]
theorem aeval_mem_of_forall_mem {T : Module.End ℂ (FormalFock Unit ℂ)}
    {V : Submodule ℂ (FormalFock Unit ℂ)} (hT : ∀ ψ ∈ V, T ψ ∈ V) (p : ℂ[X])
    {ψ : FormalFock Unit ℂ} (hψ : ψ ∈ V) : aeval T p ψ ∈ V :=
  aeval_apply_smul_mem_of_le_comap hψ p T hT

/-- The class at `(κ, ℓ)` is invariant under every polynomial in `a`. -/
theorem aeval_annihilate_mem_photonClass {κ ℓ : ℂ} (p : ℂ[X]) {ψ : FormalFock Unit ℂ}
    (h : ψ ∈ photonClass κ ℓ) :
    aeval (annihilate () : Module.End ℂ (FormalFock Unit ℂ)) p ψ ∈ photonClass κ ℓ :=
  aeval_apply_smul_mem_of_le_comap h p _ fun _ => annihilate_mem_photonClass

/-- The class at `(κ, ℓ)` is invariant under every polynomial in `a†`. -/
theorem aeval_create_mem_photonClass {κ ℓ : ℂ} (p : ℂ[X]) {ψ : FormalFock Unit ℂ}
    (h : ψ ∈ photonClass κ ℓ) :
    aeval (create () : Module.End ℂ (FormalFock Unit ℂ)) p ψ ∈ photonClass κ ℓ :=
  aeval_apply_smul_mem_of_le_comap h p _ fun _ => create_mem_photonClass

/-- `e^{κ (a†)² + ℓ a†}` maps the class at `(0, 0)`, the vectors `p(a†) ∣0⟩`, into the class at
`(κ, ℓ)`. -/
theorem gaussExp_mem_photonClass (κ ℓ : ℂ) {ψ : FormalFock Unit ℂ} (h : ψ ∈ photonClass 0 0) :
    gaussExp κ ℓ ψ ∈ photonClass κ ℓ := by
  obtain ⟨p, rfl⟩ := mem_photonClass_iff.mp h
  refine mem_photonClass_iff.mpr ⟨p, bargmann_injective ?_⟩
  rw [bargmann_aeval_create, bargmann_gaussExp, bargmann_aeval_create, bargmann_gaussVec_zero,
    mul_one, mul_comm]

/-- `∣q, 0, 0⟩ = (a†)^q ∣0⟩ = √(q!) ∣q⟩`. -/
theorem photonAdded_zero_zero (q : ℕ) :
    photonAdded q 0 0 = sqrtC q.factorial • numberState q := by
  rw [show photonAdded q 0 0 = (create () ^ q) (gaussExp 0 0 (numberState 0)) from rfl,
    gaussExp_zero, Module.End.one_apply, create_pow_numberState, zero_add, Nat.factorial_zero]
  simp [sqrtC]

/-- Every number state lies in the class at `(0, 0)`; hence so does every finitely supported
vector. -/
theorem numberState_mem_photonClass_zero (m : ℕ) : numberState m ∈ photonClass 0 0 := by
  have h : numberState m = (sqrtC m.factorial)⁻¹ • photonAdded m 0 0 := by
    rw [photonAdded_zero_zero, smul_smul, inv_mul_cancel₀ (sqrtC_ne_zero (Nat.factorial_pos m)),
      one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end BosonicLean.Fock.FormalFock
