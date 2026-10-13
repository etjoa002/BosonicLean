/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Power bounds

An element `X` of a normed ring has a *power bound* `(C, r)` if `‖X ^ m‖ ≤ C * r ^ m` for every
`m`; `r` is its rate. In a normed algebra with `r > 0` this says that `r⁻¹ X` is power-bounded
with constant `C`: `‖(r⁻¹ X) ^ m‖ ≤ C` for all `m`. (There is no established name for the pair
`(C, r)`; for operator semigroups the analogous pair is the type `(M, ω)` of a growth bound.)
In a complex Banach algebra, every `r` above the spectral radius gives a power bound, by the
`limsup` half of Gelfand's formula. Power bounds are what the convergence arguments for bosonic
matrix product states actually use; the spectral radius, which does not depend on a choice of
norm, is what their statements assume.

## Main definitions

* `BosonicLean.HasPowerBound X C r`: `‖X ^ m‖ ≤ C * r ^ m` for all `m`.

## Main results

* `BosonicLean.HasPowerBound.const_nonneg`: the constant of a power bound is nonnegative.
* `BosonicLean.HasPowerBound.mul_of_commute`: commuting products multiply power bounds.
* `BosonicLean.exists_hasPowerBound_of_spectralRadius_lt`: if `ρ(X) < r`, then `X` has a power
  bound `(C, r)` with `C ≥ 0`.
* `BosonicLean.exists_hasPowerBound_lt_of_spectralRadius_lt`: if `ρ(X) < s`, then `X` has a power
  bound `(C, r)` with `0 ≤ r < s`.
-/

open Filter Topology
open scoped NNReal ENNReal

namespace BosonicLean

section Ring

variable {A : Type*} [NormedRing A]

/-- `X` has the power bound `(C, r)`: `‖X ^ m‖ ≤ C * r ^ m` for every `m`. -/
def HasPowerBound (X : A) (C r : ℝ) : Prop :=
  ∀ m : ℕ, ‖X ^ m‖ ≤ C * r ^ m

/-- The constant of a power bound is nonnegative (take `m = 0`). -/
theorem HasPowerBound.const_nonneg {X : A} {C r : ℝ} (hX : HasPowerBound X C r) : 0 ≤ C := by
  have := hX 0
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

/-- The product of commuting elements with power bounds `(C, r)` and `(C', r')` has the power
bound `(C C', r r')`. -/
theorem HasPowerBound.mul_of_commute {X Y : A} {C C' r r' : ℝ} (h : Commute X Y)
    (hX : HasPowerBound X C r) (hY : HasPowerBound Y C' r') :
    HasPowerBound (X * Y) (C * C') (r * r') := fun m => by
  rw [h.mul_pow]
  calc ‖X ^ m * Y ^ m‖ ≤ ‖X ^ m‖ * ‖Y ^ m‖ := norm_mul_le _ _
    _ ≤ (C * r ^ m) * (C' * r' ^ m) :=
        mul_le_mul (hX m) (hY m) (norm_nonneg _) ((norm_nonneg _).trans (hX m))
    _ = C * C' * (r * r') ^ m := by ring

end Ring

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- From `‖X ^ n‖₊ ^ (1 / n) < r` (as extended reals) and `n ≥ 1`, get `‖X ^ n‖ ≤ r ^ n`. -/
theorem norm_pow_le_of_rpow_lt {a r : ℝ≥0} {n : ℕ} (hn : 1 ≤ n)
    (h : (a : ℝ≥0∞) ^ (1 / n : ℝ) < r) : (a : ℝ) ≤ (r : ℝ) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_lt_coe] at h
  have h1 : a = (a ^ (1 / n : ℝ)) ^ n := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, NNReal.rpow_one]
  have h2 : (a ^ (1 / n : ℝ)) ^ n ≤ r ^ n := pow_le_pow_left₀ zero_le h.le n
  rw [h1]
  exact_mod_cast h2

/-- **Power bound from the spectral radius.** If `ρ(X) < r`, then `‖X ^ m‖ ≤ C * r ^ m` for all
`m`, for some `C ≥ 0`. -/
theorem exists_hasPowerBound_of_spectralRadius_lt {X : A} {r : ℝ≥0}
    (h : spectralRadius ℂ X < r) : ∃ C : ℝ, 0 ≤ C ∧ HasPowerBound X C r := by
  have hr : (0 : ℝ) < r := by
    have h0 : (0 : ℝ≥0∞) < r := lt_of_le_of_lt zero_le h
    exact_mod_cast ENNReal.coe_pos.mp h0
  have hev : ∀ᶠ n : ℕ in atTop, (‖X ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < r :=
    eventually_lt_of_limsup_lt
      ((spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius X).trans_lt h)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set C : ℝ := 1 + ∑ n ∈ Finset.range (N + 1), ‖X ^ n‖ / (r : ℝ) ^ n with hC
  have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.range (N + 1), ‖X ^ n‖ / (r : ℝ) ^ n :=
    Finset.sum_nonneg fun n _ => by positivity
  refine ⟨C, by linarith, fun m => ?_⟩
  have hrm : (0 : ℝ) < (r : ℝ) ^ m := pow_pos hr m
  by_cases hm : m ≤ N
  · have hterm : ‖X ^ m‖ / (r : ℝ) ^ m ≤ ∑ n ∈ Finset.range (N + 1), ‖X ^ n‖ / (r : ℝ) ^ n :=
      Finset.single_le_sum (f := fun n => ‖X ^ n‖ / (r : ℝ) ^ n)
        (fun n _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have : ‖X ^ m‖ / (r : ℝ) ^ m ≤ C := by linarith
    calc ‖X ^ m‖ = ‖X ^ m‖ / (r : ℝ) ^ m * (r : ℝ) ^ m := by field_simp
      _ ≤ C * (r : ℝ) ^ m := mul_le_mul_of_nonneg_right this hrm.le
  · have hm' : N ≤ m := by omega
    have h1 : 1 ≤ m := by omega
    have hle : ‖X ^ m‖ ≤ (r : ℝ) ^ m := by
      have := norm_pow_le_of_rpow_lt h1 (hN m hm')
      simpa using this
    have hC1 : 1 ≤ C := by linarith
    calc ‖X ^ m‖ ≤ (r : ℝ) ^ m := hle
      _ = 1 * (r : ℝ) ^ m := (one_mul _).symm
      _ ≤ C * (r : ℝ) ^ m := mul_le_mul_of_nonneg_right hC1 hrm.le

/-- If `ρ(X) < s`, then `X` has a power bound `(C, r)` with `0 ≤ r < s` and `C ≥ 0`. -/
theorem exists_hasPowerBound_lt_of_spectralRadius_lt {X : A} {s : ℝ≥0}
    (h : spectralRadius ℂ X < s) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < s ∧ HasPowerBound X C r := by
  obtain ⟨r, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, hC, hb⟩ := exists_hasPowerBound_of_spectralRadius_lt h1
  exact ⟨C, r, hC, r.2, by exact_mod_cast ENNReal.coe_lt_coe.mp h2, hb⟩

end Banach

end BosonicLean
