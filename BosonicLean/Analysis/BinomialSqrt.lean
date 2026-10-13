/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Central
import BosonicLean.Analysis.PowerBound

/-!
# The binomial series of `(1 - 4X)^{-1/2}`

For an element `X` of a complex Banach algebra, `𝒮(X) = Σᵢ C(2i, i) Xⁱ`, the generating function
of the central binomial coefficients, is the binomial series of `(1 - 4X)^{-1/2}`. If `X` has a
power bound `(C, r)` with `4r < 1`, the series converges absolutely, `1 - 4X` is invertible, and
`𝒮(X)² = (1 - 4X)⁻¹`. For bosonic matrix product states it is the matrix `Δ^{1/2}` of the
closed form of the transfer matrix.

The square identity rests on the convolution identity `Σ_{i+j=m} C(2i,i) C(2j,j) = 4^m`, proved
here from the recurrence `(n+1) C(2n+2, n+1) = 2 (2n+1) C(2n, n)` by a symmetric-sum argument.

## Main definitions

* `BosonicLean.centralBinomSeries X`: the series `Σᵢ C(2i, i) Xⁱ`.

## Main results

* `BosonicLean.sum_antidiagonal_centralBinom_mul`: `Σ_{i+j=m} C(2i,i) C(2j,j) = 4^m`.
* `BosonicLean.summable_norm_centralBinomSeries`: absolute convergence under a power bound,
  `4r < 1`.
* `BosonicLean.geom_tsum_inverse`: `Σ xⁱ` inverts `1 - x` when the powers are summable in norm.
* `BosonicLean.isUnit_one_sub_four_smul`: `1 - 4X` is invertible under a power bound, `4r < 1`.
* `BosonicLean.centralBinomSeries_mul_self`: `𝒮(X)² = (1 - 4X)⁻¹`.
-/

open Finset

namespace BosonicLean

/-- `2 Σ_{i+j=m} i c_i c_j = m Σ_{i+j=m} c_i c_j`, by the symmetry `i ↔ j`. -/
theorem two_mul_sum_antidiagonal_fst_mul (c : ℕ → ℕ) (m : ℕ) :
    2 * ∑ p ∈ antidiagonal m, p.1 * (c p.1 * c p.2) =
      m * ∑ p ∈ antidiagonal m, c p.1 * c p.2 := by
  have hswap : ∑ p ∈ antidiagonal m, p.1 * (c p.1 * c p.2) =
      ∑ p ∈ antidiagonal m, p.2 * (c p.1 * c p.2) := by
    rw [← Nat.sum_antidiagonal_swap]
    exact sum_congr rfl fun p _ => by simp only [Prod.fst_swap, Prod.snd_swap]; ring
  have hsum : ∑ p ∈ antidiagonal m, p.1 * (c p.1 * c p.2) +
      ∑ p ∈ antidiagonal m, p.2 * (c p.1 * c p.2) = m * ∑ p ∈ antidiagonal m, c p.1 * c p.2 := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun p hp => by rw [← add_mul, mem_antidiagonal.mp hp]
  rw [two_mul]
  nth_rewrite 2 [hswap]
  exact hsum

/-- **The convolution identity** `Σ_{i+j=m} C(2i,i) C(2j,j) = 4^m`. -/
theorem sum_antidiagonal_centralBinom_mul (m : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.centralBinom * p.2.centralBinom = 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    set g : ℕ → ℕ := fun k => ∑ p ∈ antidiagonal k, p.1.centralBinom * p.2.centralBinom with hg
    set T : ℕ → ℕ := fun k =>
      ∑ p ∈ antidiagonal k, p.1 * (p.1.centralBinom * p.2.centralBinom) with hT
    -- `T (m+1) = 4 T m + 2 g m`, from `(i+1) c_{i+1} = (4i + 2) c_i`
    have hstep : T (m + 1) = 4 * T m + 2 * g m := by
      simp only [hT, hg]
      rw [Nat.sum_antidiagonal_succ]
      simp only [zero_mul, zero_add]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun p _ => ?_
      have hrec := Nat.succ_mul_centralBinom_succ p.1
      calc (p.1 + 1) * ((p.1 + 1).centralBinom * p.2.centralBinom)
          = ((p.1 + 1) * (p.1 + 1).centralBinom) * p.2.centralBinom := by ring
        _ = (2 * (2 * p.1 + 1) * p.1.centralBinom) * p.2.centralBinom := by rw [hrec]
        _ = 4 * (p.1 * (p.1.centralBinom * p.2.centralBinom)) +
            2 * (p.1.centralBinom * p.2.centralBinom) := by ring
    have h2m := two_mul_sum_antidiagonal_fst_mul Nat.centralBinom m
    have h2m1 := two_mul_sum_antidiagonal_fst_mul Nat.centralBinom (m + 1)
    change 2 * T m = m * g m at h2m
    change 2 * T (m + 1) = (m + 1) * g (m + 1) at h2m1
    change g (m + 1) = 4 ^ (m + 1)
    change g m = 4 ^ m at ih
    have key : (m + 1) * g (m + 1) = (m + 1) * (4 * g m) := by
      rw [← h2m1, hstep]
      nlinarith [h2m]
    have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) key
    rw [this, ih, pow_succ]
    ring

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The binomial series of `(1 - 4X)^{-1/2}`: `𝒮(X) = Σᵢ C(2i, i) Xⁱ`. It is a total definition
(`0` if the series diverges); every statement about it assumes a power bound with `4r < 1`. -/
noncomputable def centralBinomSeries (X : A) : A :=
  ∑' i, (i.centralBinom : ℂ) • X ^ i

omit [CompleteSpace A] in
/-- Under a power bound `(C, r)` with `0 ≤ r` and `4r < 1`, the terms of `𝒮(X)` are summable in
norm. -/
theorem summable_norm_centralBinomSeries {X : A} {C r : ℝ} (hX : HasPowerBound X C r) (hr0 : 0 ≤ r)
    (hr : 4 * r < 1) : Summable fun i : ℕ => ‖(i.centralBinom : ℂ) • X ^ i‖ := by
  have hC : 0 ≤ C := by
    have := hX 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
    ((summable_geometric_of_lt_one (by positivity) hr).mul_left C)
  rw [norm_smul, Complex.norm_natCast]
  calc (i.centralBinom : ℝ) * ‖X ^ i‖ ≤ (4 : ℝ) ^ i * (C * r ^ i) := by
        gcongr
        · exact_mod_cast Nat.centralBinom_le_four_pow i
        · exact hX i
    _ = C * (4 * r) ^ i := by rw [mul_pow]; ring

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- Under a power bound `(C, r)` with `0 ≤ r < 1`, the powers of `X` are summable in norm. -/
theorem summable_norm_pow {X : A} {C r : ℝ} (hX : HasPowerBound X C r) (hr0 : 0 ≤ r)
    (hr : r < 1) : Summable fun i : ℕ => ‖X ^ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hX
    ((summable_geometric_of_lt_one hr0 hr).mul_left C)

omit [NormedAlgebra ℂ A] in
/-- **Geometric series.** If the powers of `x` are summable in norm, then `Σ xⁱ` inverts
`1 - x` on both sides. -/
theorem geom_tsum_inverse {x : A} (hx : Summable fun i : ℕ => ‖x ^ i‖) :
    (1 - x) * ∑' i, x ^ i = 1 ∧ (∑' i, x ^ i) * (1 - x) = 1 := by
  have hs : HasSum (fun i : ℕ => x ^ i) (∑' i, x ^ i) := hx.of_norm.hasSum
  have hpart := hs.tendsto_sum_nat
  have hzero : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) :=
    hx.of_norm.tendsto_atTop_zero
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - x ^ n) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hzero
  constructor
  · have h1 : Filter.Tendsto (fun n => (1 - x) * ∑ i ∈ range n, x ^ i) Filter.atTop
        (nhds ((1 - x) * ∑' i, x ^ i)) := hpart.const_mul _
    simp_rw [mul_neg_geom_sum] at h1
    exact tendsto_nhds_unique h1 hlim
  · have h1 : Filter.Tendsto (fun n => (∑ i ∈ range n, x ^ i) * (1 - x)) Filter.atTop
        (nhds ((∑' i, x ^ i) * (1 - x))) := hpart.mul_const _
    simp_rw [geom_sum_mul_neg] at h1
    exact tendsto_nhds_unique h1 hlim

omit [CompleteSpace A] in
/-- `4X` has the power bound `(C, 4r)` when `X` has the power bound `(C, r)`. -/
theorem HasPowerBound.four_smul {X : A} {C r : ℝ} (hX : HasPowerBound X C r) :
    HasPowerBound ((4 : ℂ) • X) C (4 * r) := fun m => by
  rw [smul_pow, norm_smul, mul_pow]
  calc ‖(4 : ℂ) ^ m‖ * ‖X ^ m‖ = (4 : ℝ) ^ m * ‖X ^ m‖ := by simp
    _ ≤ (4 : ℝ) ^ m * (C * r ^ m) := by gcongr; exact hX m
    _ = C * (4 ^ m * r ^ m) := by ring

/-- Under a power bound `(C, r)` with `0 ≤ r`, `4r < 1`: `1 - 4X` is a unit with inverse
`Σ (4X)ⁱ`. -/
theorem ring_inverse_one_sub_four_smul {X : A} {C r : ℝ} (hX : HasPowerBound X C r)
    (hr0 : 0 ≤ r) (hr : 4 * r < 1) :
    Ring.inverse (1 - (4 : ℂ) • X) = ∑' i, ((4 : ℂ) • X) ^ i := by
  obtain ⟨h1, h2⟩ := geom_tsum_inverse (summable_norm_pow hX.four_smul (by positivity) hr)
  let u : Aˣ := ⟨1 - (4 : ℂ) • X, ∑' i, ((4 : ℂ) • X) ^ i, h1, h2⟩
  exact Ring.inverse_unit u

/-- Under a power bound `(C, r)` with `0 ≤ r`, `4r < 1`, the element `1 - 4X` is invertible. -/
theorem isUnit_one_sub_four_smul {X : A} {C r : ℝ} (hX : HasPowerBound X C r)
    (hr0 : 0 ≤ r) (hr : 4 * r < 1) : IsUnit (1 - (4 : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := geom_tsum_inverse (summable_norm_pow hX.four_smul (by positivity) hr)
  exact ⟨⟨1 - (4 : ℂ) • X, ∑' i, ((4 : ℂ) • X) ^ i, h1, h2⟩, rfl⟩

/-- **The square identity.** Under a power bound `(C, r)` with `0 ≤ r`, `4r < 1`:
`𝒮(X)² = (1 - 4X)⁻¹`. -/
theorem centralBinomSeries_mul_self {X : A} {C r : ℝ} (hX : HasPowerBound X C r) (hr0 : 0 ≤ r)
    (hr : 4 * r < 1) :
    centralBinomSeries X * centralBinomSeries X = Ring.inverse (1 - (4 : ℂ) • X) := by
  have hs := summable_norm_centralBinomSeries hX hr0 hr
  rw [centralBinomSeries, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs,
    ring_inverse_one_sub_four_smul hX hr0 hr]
  congr 1
  funext n
  calc ∑ kl ∈ antidiagonal n, ((kl.1.centralBinom : ℂ) • X ^ kl.1) *
        ((kl.2.centralBinom : ℂ) • X ^ kl.2)
      = ∑ kl ∈ antidiagonal n, ((kl.1.centralBinom * kl.2.centralBinom : ℕ) : ℂ) • X ^ n := by
        refine sum_congr rfl fun kl hkl => ?_
        rw [smul_mul_smul_comm, ← pow_add, mem_antidiagonal.mp hkl]
        push_cast
        rfl
    _ = ((∑ kl ∈ antidiagonal n, kl.1.centralBinom * kl.2.centralBinom : ℕ) : ℂ) • X ^ n := by
        rw [← sum_smul]
        push_cast
        rfl
    _ = ((4 : ℂ) • X) ^ n := by
        rw [sum_antidiagonal_centralBinom_mul, smul_pow]
        push_cast
        rfl

end Banach

end BosonicLean
