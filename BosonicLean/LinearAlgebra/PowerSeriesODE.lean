/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Complex.Basic

/-!
# Linear differential equations in formal power series

For power series `q₀, …, qₙ ∈ ℂ⟦X⟧` the operator `L = ∑ r, q r ∂ʳ` acts on `ℂ⟦X⟧`. If some `q r`
is nonzero, the solutions of `L g = 0` form a space of dimension at most `n`. As a consequence,
the Wronskian of `n` linearly independent power series is nonzero.

The proof of the dimension bound is the indicial argument at `0`. Multiplying `L g` by `Xⁿ`
writes `Xⁿ L g = ∑ r, (q r Xⁿ⁻ʳ) (Xʳ ∂ʳ g)`, where `Xʳ ∂ʳ` multiplies the `k`-th coefficient by the
falling factorial `k (k - 1) ⋯ (k - r + 1)`. If `w` is the least index at which some `q r Xⁿ⁻ʳ`
has a nonzero coefficient and `g` has order `v`, the coefficient of `X ^ (w + v)` in `Xⁿ L g` is
`I(v) g_v` for the indicial polynomial `I`, a nonzero polynomial of degree at most `n`. So the
order of a nonzero solution is a root of `I` in `ℕ`, and a solution is determined by its
coefficients at these at most `n` roots.

## Main definitions

* `BosonicLean.diffOp`: the operator `∑ r, q r ∂ʳ` on `ℂ⟦X⟧`.
* `BosonicLean.powerSeriesWronskian`: the Wronskian `det [∂ʳ f j]` of `n` power series.

## Main results

* `BosonicLean.finrank_ker_diffOp_le`: if some `q r ≠ 0`, the kernel of `diffOp q` is
  finite-dimensional, of dimension at most `n`.
* `BosonicLean.powerSeriesWronskian_ne_zero`: the Wronskian of linearly independent power series
  is nonzero.
-/

namespace BosonicLean

open PowerSeries

section Coefficients

variable {R : Type*} [CommSemiring R]

/-- The operator `Xʳ ∂ʳ` multiplies the `k`-th coefficient by the falling factorial
`k (k - 1) ⋯ (k - r + 1)`. -/
theorem coeff_X_pow_mul_iterate_derivative (g : R⟦X⟧) (r k : ℕ) :
    coeff k (X ^ r * (derivative (R := R))^[r] g) = (k.descFactorial r : R) * coeff k g := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + r := ⟨k - r, by omega⟩
    rw [Nat.add_sub_cancel, coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]

/-- If the coefficients of `f` vanish below `a` and those of `g` below `b`, the coefficient of
`X ^ (a + b)` in `f * g` is the product of the coefficients of `X ^ a` in `f` and `X ^ b` in
`g`. -/
theorem coeff_add_mul_of_forall_lt {f g : R⟦X⟧} {a b : ℕ} (hf : ∀ i < a, coeff i f = 0)
    (hg : ∀ j < b, coeff j g = 0) : coeff (a + b) (f * g) = coeff a f * coeff b g := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (a, b) (Finset.mem_antidiagonal.2 rfl)]
  rintro ⟨i, j⟩ hij hne
  rw [Finset.mem_antidiagonal] at hij
  rcases lt_or_ge i a with h | h
  · rw [hf i h, zero_mul]
  · have hj : j < b := by
      by_contra hj
      exact hne (Prod.ext (show i = a by omega) (show j = b by omega))
    rw [hg j hj, mul_zero]

end Coefficients

/-- The linear differential operator `Σ_r q_r ∂^r` with power-series coefficients on `ℂ⟦X⟧`. -/
noncomputable def diffOp {n : ℕ} (q : Fin (n + 1) → PowerSeries ℂ) :
    PowerSeries ℂ →ₗ[ℂ] PowerSeries ℂ :=
  ∑ r : Fin (n + 1), q r • ((PowerSeries.derivative (R := ℂ)).toLinearMap ^ (r : ℕ))

/-- The operator `diffOp q` applied to a power series. -/
theorem diffOp_apply {n : ℕ} (q : Fin (n + 1) → PowerSeries ℂ) (g : PowerSeries ℂ) :
    diffOp q g = ∑ r : Fin (n + 1), q r * (derivative (R := ℂ))^[r] g := by
  simp [diffOp, Module.End.pow_apply]

/-- **Solutions of a linear ODE in formal power series.** If some coefficient `q r` is nonzero,
the solutions of `∑ r, q r ∂ʳ g = 0` in `ℂ⟦X⟧` form a finite-dimensional space of dimension at
most `n`. -/
theorem finrank_ker_diffOp_le {n : ℕ} (q : Fin (n + 1) → PowerSeries ℂ) (hq : ∃ r, q r ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (diffOp q)) ∧
      Module.finrank ℂ (LinearMap.ker (diffOp q)) ≤ n := by
  classical
  -- the shifted coefficients `q r Xⁿ⁻ʳ` and the least index `w` of a nonzero coefficient
  let Q : Fin (n + 1) → ℂ⟦X⟧ := fun r => q r * X ^ (n - r)
  have hQ : ∃ k, ∃ r, coeff k (Q r) ≠ 0 := by
    obtain ⟨r, hr⟩ := hq
    obtain ⟨k, hk⟩ := exists_coeff_ne_zero_iff_ne_zero.2 hr
    exact ⟨k + (n - r), r, by simpa [Q] using hk⟩
  set w := Nat.find hQ with hw_def
  have hw : ∀ r, ∀ i < w, coeff i (Q r) = 0 := fun r i hi => by
    have := Nat.find_min hQ hi
    simp only [not_exists, not_not] at this
    exact this r
  obtain ⟨r₀, hr₀⟩ := Nat.find_spec hQ
  -- the indicial polynomial
  let a : Fin (n + 1) → ℂ := fun r => coeff w (Q r)
  let I : Polynomial ℂ := ∑ r, Polynomial.C (a r) * descPochhammer ℂ r
  have hIeval : ∀ v : ℕ, I.eval (v : ℂ) = ∑ r, a r * (v.descFactorial r : ℂ) := by
    intro v
    simp [I, Polynomial.eval_finsetSum, descPochhammer_eval_eq_descFactorial]
  have hIdeg : I.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [descPochhammer_natDegree]
    exact Nat.lt_succ_iff.mp r.is_lt
  have hI0 : I ≠ 0 := by
    let S := Finset.univ.filter fun r => a r ≠ 0
    have hS : S.Nonempty := ⟨r₀, by simpa [S, a] using hr₀⟩
    set m := S.max' hS
    have hm : a m ≠ 0 := by simpa [S] using S.max'_mem hS
    have hcoeff : I.coeff m = a m := by
      simp only [I, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
      rw [Finset.sum_eq_single m]
      · have := (monic_descPochhammer ℂ (m : ℕ)).coeff_natDegree
        rw [descPochhammer_natDegree] at this
        rw [this, mul_one]
      · intro r _ hrm
        by_cases har : a r = 0
        · rw [har, zero_mul]
        · have hle : r ≤ m := S.le_max' r (by simpa [S] using har)
          have hlt : (r : ℕ) < m := lt_of_le_of_ne hle (fun h => hrm (Fin.ext h))
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]),
            mul_zero]
      · intro h
        exact absurd (Finset.mem_univ m) h
    intro h
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact hm hcoeff.symm
  -- the coefficient of `X ^ (w + v)` in `Xⁿ L g`
  have key : ∀ g ∈ LinearMap.ker (diffOp q), ∀ v, (∀ k < v, coeff k g = 0) →
      I.eval (v : ℂ) * coeff v g = 0 := by
    intro g hg v hv
    have h0 : X ^ n * diffOp q g = 0 := by rw [LinearMap.mem_ker.1 hg, mul_zero]
    have hcoeff : coeff (w + v) (X ^ n * diffOp q g) = I.eval (v : ℂ) * coeff v g := by
      rw [diffOp_apply, Finset.mul_sum, map_sum, hIeval, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hsplit : X ^ n * (q r * (derivative (R := ℂ))^[r] g) =
          Q r * (X ^ (r : ℕ) * (derivative (R := ℂ))^[r] g) := by
        have : (X : ℂ⟦X⟧) ^ n = X ^ (n - r) * X ^ (r : ℕ) := by
          rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp r.is_lt)]
        simp only [Q, this]
        ring
      have hvanish : ∀ j < v, coeff j (X ^ (r : ℕ) * (derivative (R := ℂ))^[r] g) = 0 := by
        intro j hj
        rw [coeff_X_pow_mul_iterate_derivative, hv j hj, mul_zero]
      rw [hsplit, coeff_add_mul_of_forall_lt (hw r) hvanish,
        coeff_X_pow_mul_iterate_derivative]
      ring
    rw [← hcoeff, h0, map_zero]
  -- the natural roots of `I`
  let T : Finset ℕ := I.roots.toFinset.preimage Nat.cast Nat.cast_injective.injOn
  have hT : T.card ≤ n :=
    calc T.card ≤ I.roots.toFinset.card :=
          Finset.card_le_card_of_injOn Nat.cast (fun t ht => by simpa [T] using ht)
            Nat.cast_injective.injOn
      _ ≤ Multiset.card I.roots := Multiset.toFinset_card_le _
      _ ≤ I.natDegree := Polynomial.card_roots' I
      _ ≤ n := hIdeg
  -- a solution is determined by its coefficients at `T`
  let φ : LinearMap.ker (diffOp q) →ₗ[ℂ] (T → ℂ) :=
    LinearMap.pi fun t => (coeff (t : ℕ)).comp (LinearMap.ker (diffOp q)).subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    by_contra hne
    have hg0 : (g : ℂ⟦X⟧) ≠ 0 := fun h => hne (Subtype.ext h)
    have hex : ∃ v, coeff v (g : ℂ⟦X⟧) ≠ 0 := exists_coeff_ne_zero_iff_ne_zero.2 hg0
    have hv : coeff (Nat.find hex) (g : ℂ⟦X⟧) ≠ 0 := Nat.find_spec hex
    have hlt : ∀ k < Nat.find hex, coeff k (g : ℂ⟦X⟧) = 0 := fun k hk => by
      simpa using Nat.find_min hex hk
    have hroot : I.eval (Nat.find hex : ℂ) = 0 :=
      (mul_eq_zero.1 (key g g.2 _ hlt)).resolve_right hv
    have hvT : Nat.find hex ∈ T := by simp [T, Polynomial.mem_roots hI0, hroot]
    have := congrFun hg ⟨Nat.find hex, hvT⟩
    exact hv (by simpa [φ] using this)
  have : FiniteDimensional ℂ (LinearMap.ker (diffOp q)) := Module.Finite.of_injective φ hφ
  refine ⟨this, ?_⟩
  calc Module.finrank ℂ (LinearMap.ker (diffOp q)) ≤ Module.finrank ℂ (T → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hφ
    _ = T.card := by simp
    _ ≤ n := hT

/-- The Wronskian `det [∂ʳ f j]_{r, j < n}` of `n` formal power series. -/
noncomputable def powerSeriesWronskian {n : ℕ} (f : Fin n → PowerSeries ℂ) : PowerSeries ℂ :=
  (Matrix.of fun (r j : Fin n) =>
    ((PowerSeries.derivative (R := ℂ)).toLinearMap ^ (r : ℕ)) (f j)).det

/-- **Wronskian criterion.** The Wronskian of linearly independent formal power series is
nonzero. -/
theorem powerSeriesWronskian_ne_zero {n : ℕ} {f : Fin n → PowerSeries ℂ}
    (hf : LinearIndependent ℂ f) : powerSeriesWronskian f ≠ 0 := by
  classical
  intro hW
  cases n with
  | zero =>
    rw [powerSeriesWronskian, Matrix.det_isEmpty] at hW
    exact one_ne_zero hW
  | succ m =>
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hW
    have hker : ∀ j, f j ∈ LinearMap.ker (diffOp c) := by
      intro j
      have := congrFun hc j
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Module.End.pow_apply,
        Pi.zero_apply] at this
      rw [LinearMap.mem_ker, diffOp_apply, ← this]
      rfl
    have hq : ∃ r, c r ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hc0 (funext h)
    obtain ⟨hfin, hle⟩ := finrank_ker_diffOp_le c hq
    let f' : Fin (m + 1) → LinearMap.ker (diffOp c) := fun j => ⟨f j, hker j⟩
    have hf' : LinearIndependent ℂ f' :=
      LinearIndependent.of_comp (LinearMap.ker (diffOp c)).subtype hf
    have := hf'.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega

end BosonicLean

namespace Polynomial

/-- `∂^d p = d! γ` for `d = deg p` and `γ` the leading coefficient of `p`. -/
theorem iterate_derivative_natDegree {R : Type*} [Semiring R] (p : R[X]) :
    derivative^[p.natDegree] p = C ((p.natDegree.factorial : R) * p.leadingCoeff) := by
  ext m
  rw [coeff_iterate_derivative, coeff_C]
  split_ifs with hm
  · subst hm
    rw [zero_add, Nat.descFactorial_self, nsmul_eq_mul, leadingCoeff]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]

end Polynomial
