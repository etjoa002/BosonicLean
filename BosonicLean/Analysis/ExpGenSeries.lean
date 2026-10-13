/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exponential generating series

For a sequence `c : ℕ → E` in a complex Banach space, the exponential generating series is
`f(t) = Σₙ (tⁿ / n!) cₙ`. If `Σₙ ‖cₙ‖ Rⁿ / n! < ∞` for every `R ≥ 0`, then `f` is differentiable on
`ℂ` with `f' = Σₙ (tⁿ / n!) c_{n+1}`, so its `k`-th derivative at `0` is `c_k`. This is the
termwise differentiation behind the derivative form of the sourced transfer matrix
(Tjoa–Cirac, arXiv:2607.28753, Proposition 2).

## Main definitions

* `BosonicLean.expGenSeries c t`: `Σₙ (tⁿ / n!) cₙ`.

## Main results

* `BosonicLean.hasDerivAt_expGenSeries`: the derivative is the series of the shifted sequence.
* `BosonicLean.iteratedDeriv_expGenSeries_zero`: the `k`-th derivative at `0` is `c_k`.
-/

open Finset
open scoped ContDiff

namespace BosonicLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The exponential generating series `Σₙ (tⁿ / n!) cₙ`. A total definition (`0` if the series
diverges); the statements assume `Σₙ ‖cₙ‖ Rⁿ / n! < ∞` for every `R ≥ 0`. -/
noncomputable def expGenSeries (c : ℕ → E) (t : ℂ) : E :=
  ∑' n, (t ^ n / (n.factorial : ℂ)) • c n

/-- `(n + 1) Rⁿ ≤ (R + 1)ⁿ⁺¹` for `R ≥ 0` (one term of the binomial expansion). -/
theorem succ_mul_pow_le_add_one_pow {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * R ^ n ≤ (R + 1) ^ (n + 1) := by
  rw [add_pow]
  have h := single_le_sum (s := range (n + 2))
    (f := fun k => R ^ k * 1 ^ (n + 1 - k) * ((n + 1).choose k : ℝ))
    (fun k _ => by positivity) (mem_range.mpr (by omega : n < n + 2))
  simpa [Nat.choose_succ_self_right, mul_comm] using h

omit [NormedSpace ℂ E] in
/-- The shifted sequence inherits the summability condition. -/
theorem summable_shift {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) :
    ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c (n + 1)‖ * R ^ n / (n.factorial : ℝ) := by
  intro R hR
  have h := (summable_nat_add_iff 1).mpr (hc (R + 1) (by positivity))
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) h
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have key := succ_mul_pow_le_add_one_pow hR n
  rw [Nat.factorial_succ, Nat.cast_mul, div_le_div_iff₀ hf (by positivity)]
  calc ‖c (n + 1)‖ * R ^ n * (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ))
      = ‖c (n + 1)‖ * (((n + 1 : ℕ) : ℝ) * R ^ n) * (n.factorial : ℝ) := by ring
    _ ≤ ‖c (n + 1)‖ * (R + 1) ^ (n + 1) * (n.factorial : ℝ) := by gcongr

omit [NormedSpace ℂ E] in
theorem summable_shift_iterate {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) (k : ℕ) :
    ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c (n + k)‖ * R ^ n / (n.factorial : ℝ) := by
  induction k with
  | zero => simpa using hc
  | succ k ih => simpa [add_assoc, add_comm 1 k] using summable_shift ih

variable [CompleteSpace E]

/-- **Termwise differentiation.** If `Σₙ ‖cₙ‖ Rⁿ / n! < ∞` for every `R ≥ 0`, the exponential
generating series has derivative `Σₙ (tⁿ / n!) c_{n+1}` at every `t ∈ ℂ`. -/
theorem hasDerivAt_expGenSeries {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) (t : ℂ) :
    HasDerivAt (expGenSeries c) (expGenSeries (fun n => c (n + 1)) t) t := by
  set ρ : ℝ := ‖t‖ + 1 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set g : ℕ → ℂ → E := fun n s => (s ^ n / (n.factorial : ℂ)) • c n
  set g' : ℕ → ℂ → E := fun n s => ((n : ℂ) * s ^ (n - 1) / (n.factorial : ℂ)) • c n
  set u : ℕ → ℝ := fun n => (n : ℝ) * ρ ^ (n - 1) / (n.factorial : ℝ) * ‖c n‖
  have hu : Summable u := by
    refine (summable_nat_add_iff 1).mp ?_
    refine (summable_shift hc ρ hρ0).congr fun n => ?_
    simp only [u, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have hg : ∀ n y, y ∈ Metric.ball (0 : ℂ) ρ → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    ((hasDerivAt_pow n y).div_const _).smul_const (c n)
  have hg' : ∀ n y, y ∈ Metric.ball (0 : ℂ) ρ → ‖g' n y‖ ≤ u n := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    simp only [g', u, norm_smul, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
  have hg0 : Summable fun n => g n 0 := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [g, zero_pow hn]
  have ht : t ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, hρ]
    linarith
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hg hg' (Metric.mem_ball_self (by positivity)) hg0 ht
  have h' : HasDerivAt (expGenSeries c) (∑' n, g' n t) t := h
  refine h'.congr_deriv ?_
  rw [tsum_eq_zero_add']
  · simp only [g', Nat.cast_zero, zero_mul, zero_div, zero_smul, zero_add, expGenSeries]
    refine tsum_congr fun n => ?_
    congr 1
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
  · exact (Summable.of_norm_bounded hu fun n => hg' n t ht).comp_injective
      (add_left_injective 1)

omit [CompleteSpace E] in
/-- The value at `0` is the first coefficient. -/
theorem expGenSeries_zero (c : ℕ → E) : expGenSeries c 0 = c 0 := by
  rw [expGenSeries, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- **Iterated derivatives.** Under the summability condition, the `k`-th derivative of the
exponential generating series of `c` is that of `n ↦ c (n + k)`. -/
theorem iteratedDeriv_expGenSeries {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) (k : ℕ) :
    iteratedDeriv k (expGenSeries c) = expGenSeries (fun n => c (n + k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have := (hasDerivAt_expGenSeries (summable_shift_iterate hc k) t).deriv
    simpa [add_assoc, add_comm 1 k] using this

/-- **The `k`-th derivative at `0` is `c_k`.** -/
theorem iteratedDeriv_expGenSeries_zero {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) (k : ℕ) :
    iteratedDeriv k (expGenSeries c) 0 = c k := by
  rw [iteratedDeriv_expGenSeries hc, expGenSeries_zero, zero_add]

/-- **Smoothness.** Under the summability condition the exponential generating series is
infinitely differentiable on `ℂ`. -/
theorem contDiff_expGenSeries {c : ℕ → E}
    (hc : ∀ R : ℝ, 0 ≤ R → Summable fun n => ‖c n‖ * R ^ n / (n.factorial : ℝ)) :
    ContDiff ℂ ∞ (expGenSeries c) :=
  contDiff_of_differentiable_iteratedDeriv fun k _ => by
    rw [iteratedDeriv_expGenSeries hc k]
    exact fun t => (hasDerivAt_expGenSeries (summable_shift_iterate hc k) t).differentiableAt

end BosonicLean
