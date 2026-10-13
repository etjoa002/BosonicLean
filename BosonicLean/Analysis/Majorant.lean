/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The scalar majorant of the bosonic transfer matrix

For `r, a ≥ 0` let `c_n(r, a) = Σ_{t ≤ n/2} r^t a^{n-2t} / (t! (n-2t)!)`, the coefficient of `z^n`
in the majorant series `e^{r z² + a z}` (in the sense of Cauchy's method of majorants). The series
`Σ n! c_n(r, a) c_n(r', b)` is the norm majorant of the transfer matrix of a bosonic MPS. It
converges when `r + r' < 1`.

The proof is elementary: the Cauchy estimate `c_n(r, a) s^n ≤ e^{r s²} e^{a s}` (all coefficients
are nonnegative), the choice `s² = n / (r + r')`, and Stirling's bound `n! ≤ e √n (n/e)^n`.

## Main definitions

* `BosonicLean.majorantCoeff r a n`: the majorant coefficient `c_n(r, a)`, a polynomial in `r, a`.

## Main results

* `BosonicLean.majorantCoeff_mono`: `c_n(r, a)` is nondecreasing in `a ≥ 0`.
* `BosonicLean.majorantCoeff_mul_pow_le`: the Cauchy estimate.
* `BosonicLean.factorial_le_stirling`: `n! ≤ e √n (n/e)^n` for `n ≥ 1`.
* `BosonicLean.summable_majorant`: `Σ n! c_n(r, a) c_n(r', b) < ∞` for `r + r' < 1`.
-/

open Finset Real Nat Filter

namespace BosonicLean

/-- The majorant coefficient `c_n(r, a) = Σ_{t ≤ n/2} r^t a^{n-2t} / (t! (n-2t)!)`, the coefficient
of `zⁿ` in the majorant series `e^{r z² + a z}`. -/
noncomputable def majorantCoeff (r a : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range (n / 2 + 1), r ^ t * a ^ (n - 2 * t) / ((t ! : ℝ) * ((n - 2 * t) ! : ℝ))

theorem majorantCoeff_nonneg {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ majorantCoeff r a n :=
  sum_nonneg fun _ _ => by positivity

/-- `a ↦ c_n(r, a)` is nondecreasing on `[0, ∞)`: a polynomial with nonnegative coefficients. -/
theorem majorantCoeff_mono {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    majorantCoeff r a n ≤ majorantCoeff r b n :=
  sum_le_sum fun _ _ => by gcongr

/-- At `r = 0` only the term `t = 0` survives: `c_n(0, a) = a^n / n!`. -/
theorem majorantCoeff_zero_left (a : ℝ) (n : ℕ) : majorantCoeff 0 a n = a ^ n / (n ! : ℝ) := by
  rw [majorantCoeff, sum_eq_single 0]
  · simp
  · intro t _ ht
    simp [zero_pow ht]
  · intro h
    exact absurd (mem_range.mpr (Nat.succ_pos _)) h

/-- **Cauchy estimate.** For `r, a, s ≥ 0`: `c_n(r, a) s^n ≤ e^{r s²} e^{a s}`. -/
theorem majorantCoeff_mul_pow_le {r a s : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hs : 0 ≤ s) (n : ℕ) :
    majorantCoeff r a n * s ^ n ≤ exp (r * s ^ 2) * exp (a * s) := by
  have key : ∀ t ∈ range (n / 2 + 1),
      r ^ t * a ^ (n - 2 * t) / ((t ! : ℝ) * ((n - 2 * t) ! : ℝ)) * s ^ n =
        (r * s ^ 2) ^ t / (t ! : ℝ) * ((a * s) ^ (n - 2 * t) / ((n - 2 * t) ! : ℝ)) := by
    intro t ht
    have h2t : 2 * t ≤ n := by
      have := mem_range.mp ht
      omega
    have hsn : s ^ n = (s ^ 2) ^ t * s ^ (n - 2 * t) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hsn, mul_pow, mul_pow]
    field_simp
  rw [majorantCoeff, sum_mul, sum_congr rfl key]
  calc ∑ t ∈ range (n / 2 + 1),
        (r * s ^ 2) ^ t / (t ! : ℝ) * ((a * s) ^ (n - 2 * t) / ((n - 2 * t) ! : ℝ))
      ≤ ∑ t ∈ range (n / 2 + 1), (r * s ^ 2) ^ t / (t ! : ℝ) * exp (a * s) := by
        gcongr with t _
        exact pow_div_factorial_le_exp _ (mul_nonneg ha hs) _
    _ = (∑ t ∈ range (n / 2 + 1), (r * s ^ 2) ^ t / (t ! : ℝ)) * exp (a * s) := by
        rw [sum_mul]
    _ ≤ exp (r * s ^ 2) * exp (a * s) := by
        gcongr
        exact sum_le_exp_of_nonneg (mul_nonneg hr (sq_nonneg s)) _

/-- **Stirling's upper bound.** `n! ≤ e √n (n/e)^n` for `n ≥ 1`: Stirling's sequence decreases
from its value `e / √2` at `n = 1`. -/
theorem factorial_le_stirling {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply, Stirling.stirlingSeq_one] at hanti
  have hpos : 0 < √(2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / exp 1) ^ (m + 1) := by
    positivity
  rw [Stirling.stirlingSeq, div_le_div_iff₀ hpos (by positivity)] at hanti
  have hsq : √(2 * ((m + 1 : ℕ) : ℝ)) = √2 * √((m + 1 : ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [hsq] at hanti
  have : ((m + 1) ! : ℝ) * √2 ≤ exp 1 * (√2 * √((m + 1 : ℕ) : ℝ) *
      (((m + 1 : ℕ) : ℝ) / exp 1) ^ (m + 1)) := by linarith
  nlinarith [this]

/-- The term bound: for `n ≥ 1`, `γ = r + r' > 0`,
`n! c_n(r,a) c_n(r',b) ≤ e √n γ^n e^{(a+b) √(n/γ)}`. -/
theorem majorant_term_le {r r' a b : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ : 0 < r + r') {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) * majorantCoeff r a n * majorantCoeff r' b n ≤
      exp 1 * √(n : ℝ) * (r + r') ^ n * exp ((a + b) * √((n : ℝ) / (r + r'))) := by
  set γ := r + r' with hγdef
  set s := √((n : ℝ) / γ) with hsdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hnpos hγ)
  have hs2 : s ^ 2 = (n : ℝ) / γ := Real.sq_sqrt (div_pos hnpos hγ).le
  have hsn : 0 < s ^ n := pow_pos hs n
  have h1 := majorantCoeff_mul_pow_le hr ha hs.le n
  have h2 := majorantCoeff_mul_pow_le hr' hb hs.le n
  have hc1 : majorantCoeff r a n ≤ exp (r * s ^ 2) * exp (a * s) / s ^ n := by
    rw [le_div_iff₀ hsn]; exact h1
  have hc2 : majorantCoeff r' b n ≤ exp (r' * s ^ 2) * exp (b * s) / s ^ n := by
    rw [le_div_iff₀ hsn]; exact h2
  have hprod : majorantCoeff r a n * majorantCoeff r' b n ≤
      exp (r * s ^ 2) * exp (a * s) / s ^ n * (exp (r' * s ^ 2) * exp (b * s) / s ^ n) :=
    mul_le_mul hc1 hc2 (majorantCoeff_nonneg hr' hb n) (by positivity)
  have hγs : γ * s ^ 2 = n := by
    rw [hs2]
    field_simp
  have hexp : exp (r * s ^ 2) * exp (a * s) / s ^ n * (exp (r' * s ^ 2) * exp (b * s) / s ^ n) =
      exp (n : ℝ) * exp ((a + b) * s) / ((n : ℝ) / γ) ^ n := by
    have e1 : exp (r * s ^ 2) * exp (a * s) * (exp (r' * s ^ 2) * exp (b * s)) =
        exp (n : ℝ) * exp ((a + b) * s) := by
      rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, ← hγs, hγdef]
      congr 1
      ring
    calc exp (r * s ^ 2) * exp (a * s) / s ^ n * (exp (r' * s ^ 2) * exp (b * s) / s ^ n)
        = exp (r * s ^ 2) * exp (a * s) * (exp (r' * s ^ 2) * exp (b * s)) / (s ^ 2) ^ n := by
          rw [← pow_mul, two_mul, pow_add]
          ring
      _ = exp (n : ℝ) * exp ((a + b) * s) / ((n : ℝ) / γ) ^ n := by rw [e1, hs2]
  have hfact := factorial_le_stirling hn
  calc (n ! : ℝ) * majorantCoeff r a n * majorantCoeff r' b n
      = (n ! : ℝ) * (majorantCoeff r a n * majorantCoeff r' b n) := by ring
    _ ≤ (n ! : ℝ) * (exp (n : ℝ) * exp ((a + b) * s) / ((n : ℝ) / γ) ^ n) := by
        rw [← hexp]; gcongr
    _ ≤ exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n *
          (exp (n : ℝ) * exp ((a + b) * s) / ((n : ℝ) / γ) ^ n) := by
        gcongr
    _ = exp 1 * √(n : ℝ) * γ ^ n * exp ((a + b) * s) := by
        have hen : exp (n : ℝ) = exp 1 ^ n := by
          rw [← Real.exp_nat_mul, mul_one]
        have hnn : (n : ℝ) ^ n ≠ 0 := pow_ne_zero _ hnpos.ne'
        have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ.ne'
        have hen' : exp 1 ^ n ≠ 0 := pow_ne_zero _ (exp_pos 1).ne'
        rw [hen, div_pow, div_pow]
        field_simp

/-- The arithmetic-geometric mean inequality in the form `c u ≤ δ u² + c² / (4δ)`, `δ > 0`. -/
theorem mul_le_sq_add_div {δ : ℝ} (hδ : 0 < δ) (c u : ℝ) : c * u ≤ δ * u ^ 2 + c ^ 2 / (4 * δ) := by
  have e : δ * u ^ 2 + c ^ 2 / (4 * δ) - c * u = (2 * δ * u - c) ^ 2 / (4 * δ) := by
    field_simp
    ring
  have : 0 ≤ (2 * δ * u - c) ^ 2 / (4 * δ) := by positivity
  linarith

/-- **The majorant series converges.** If `r, r', a, b ≥ 0` and `r + r' < 1`, then
`Σ n! c_n(r, a) c_n(r', b)` converges. -/
theorem summable_majorant {r r' a b : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hγ : r + r' < 1) :
    Summable fun n : ℕ => (n ! : ℝ) * majorantCoeff r a n * majorantCoeff r' b n := by
  rcases (add_nonneg hr hr').eq_or_lt with h0 | hpos
  · -- r = r' = 0: the terms are (a b)^n / n!
    have hr0 : r = 0 := by linarith
    have hr0' : r' = 0 := by linarith
    subst hr0 hr0'
    have : (fun n : ℕ => (n ! : ℝ) * majorantCoeff 0 a n * majorantCoeff 0 b n) =
        fun n => (a * b) ^ n / (n ! : ℝ) := by
      funext n
      rw [majorantCoeff_zero_left, majorantCoeff_zero_left, mul_pow]
      field_simp
    rw [this]
    exact Real.summable_pow_div_factorial _
  · set γ := r + r' with hγdef
    set c := (a + b) / √γ with hcdef
    set δ := -Real.log γ / 2 with hδdef
    have hlog : Real.log γ < 0 := Real.log_neg hpos hγ
    have hδ : 0 < δ := by rw [hδdef]; linarith
    set q := √γ with hqdef
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq1 : q < 1 := by
      rw [hqdef, Real.sqrt_lt' one_pos]; simpa using hγ
    have hexpδ : exp δ * q = 1 := by
      rw [hδdef, hqdef, Real.sqrt_eq_rpow, ← Real.exp_log hpos]
      rw [← Real.exp_mul, ← Real.exp_add, Real.log_exp]
      ring_nf
      simp
    set K := exp 1 * exp (c ^ 2 / (4 * δ)) with hKdef
    have hsum : Summable fun n : ℕ => K * ((n : ℝ) ^ 1 * q ^ n) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hq0])).mul_left K
    refine Summable.of_norm_bounded_eventually_nat hsum ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hterm := majorant_term_le hr hr' ha hb hpos hn
    have hnn : 0 ≤ (n ! : ℝ) * majorantCoeff r a n * majorantCoeff r' b n := by
      have := majorantCoeff_nonneg hr ha n
      have := majorantCoeff_nonneg hr' hb n
      positivity
    rw [Real.norm_of_nonneg hnn]
    refine hterm.trans ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    -- (a+b) √(n/γ) = c √n ≤ δ n + c²/(4δ)
    have hsqrt : √((n : ℝ) / γ) = √(n : ℝ) / √γ := Real.sqrt_div' _ hpos.le
    have hamgm : (a + b) * √((n : ℝ) / γ) ≤ δ * n + c ^ 2 / (4 * δ) := by
      rw [hsqrt, show (a + b) * (√(n : ℝ) / √γ) = c * √(n : ℝ) by rw [hcdef]; ring]
      have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt hnpos.le
      have := mul_le_sq_add_div hδ c (√(n : ℝ))
      rwa [hsq] at this
    have hsqn : √(n : ℝ) ≤ n := by
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Real.sqrt_le_left hnpos.le]
      nlinarith
    have hγq : γ = q ^ 2 := (Real.sq_sqrt hpos.le).symm
    calc exp 1 * √(n : ℝ) * γ ^ n * exp ((a + b) * √((n : ℝ) / γ))
        ≤ exp 1 * (n : ℝ) * γ ^ n * exp (δ * n + c ^ 2 / (4 * δ)) := by
          gcongr
      _ = K * ((n : ℝ) ^ 1 * (q ^ n * (exp δ * q) ^ n)) := by
          rw [hKdef, hγq, ← pow_mul, Real.exp_add, mul_comm δ, Real.exp_nat_mul]
          ring
      _ = K * ((n : ℝ) ^ 1 * q ^ n) := by rw [hexpδ, one_pow, mul_one]

end BosonicLean
