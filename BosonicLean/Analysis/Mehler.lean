/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Analysis.Hermite
import BosonicLean.Analysis.BinomialSqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mehler's formula in a commutative Banach algebra

For elements `P, Q, R, S` of a complex Banach algebra, the *pairing series* is
`Φ(P, Q, R, S) = Σₙ n! Cₙ(Q, P) Cₙ(R, S)`; for scalars it is the bilinear Fischer pairing
`⟨f, g⟩ = Σₙ n! fₙ gₙ` of `e^{Q z² + P z}` and `e^{R z² + S z}`, and so the overlap of two
single-mode Gaussian vectors. If `Q` and `R` have power bounds `(C, r)` and `(C', r')` with
`r + r' < 1`, the series converges absolutely. The algebra may be the zero algebra, so `‖1‖ ≤ 1` is
assumed rather than `‖1‖ = 1`.

For pairwise commuting `P, Q, R, S` under these bounds, Mehler's formula holds:
`Φ(P, Q, R, S) = 𝒮(QR) exp(Δ (R P² + S P + Q S²))` with `Δ = (1 - 4QR)⁻¹` and `𝒮` the binomial
series of `(1 - 4X)^{-1/2}` (`BosonicLean.centralBinomSeries`). For scalars, `Q = R = -ρ/2`,
`P = √ρ x` and `S = √ρ y` turn it into the classical
`Σₙ He_n(x) He_n(y) ρⁿ/n! = (1 - ρ²)^{-1/2} exp((ρ x y - ρ² (x² + y²)/2) / (1 - ρ²))`.
The proof runs a first-order equation in one complex parameter: `F(λ) = Φ(λP, Q, R, λS)` has
`F(0) = 𝒮(QR)` and `F' = 2λ Δ Y F`, so `exp(-λ² Δ Y) F(λ)` has derivative zero and is constant
on `ℂ`.

The pairing series and Mehler's formula were introduced in the companion library GABMPS (the
transfer matrix of a bosonic matrix product state, Tjoa and Cirac, Proposition 1) and moved here
with their statements unchanged (GA-BMPS milestone B5, part B5.3a, Step 0), since the overlaps of
squeezed coherent vectors on the bosonic Fock space need them.

## Main definitions

* `BosonicLean.pairingSeries P Q R S`: `Σₙ n! Cₙ(Q, P) Cₙ(R, S)`.
* `BosonicLean.pairingShift P Q R S`, `BosonicLean.pairingShift' P Q R S`: the index-shifted
  pairing series.

## Main results

* `BosonicLean.summable_norm_pairingSeries`: absolute convergence for `r + r' < 1`.
* `BosonicLean.pairingShift_eq_and`, `BosonicLean.one_sub_mul_pairingShift`: the recurrences for
  the shifted series.
* `BosonicLean.pairingSeries_zero_zero`: `Φ(0, Q, R, 0) = 𝒮(QR)`.
* `BosonicLean.hasDerivAt_pairingSeries_smul`: the first-order equation `F' = 2λ Δ Y F`.
* `BosonicLean.pairingSeries_eq`: Mehler's formula.
* `BosonicLean.centralBinomSeries_ofReal_of_abs_lt`: `𝒮(a) = (1 - 4a)^{-1/2}` for `|a| < 1/4`.
* `BosonicLean.hasSum_factorial_mul_normSq_cMatrix`: the squared norm of a single-mode squeezed
  coherent vector.

## References

* F. G. Mehler, *Ueber die Entwicklung einer Function von beliebig vielen Variablen nach
  Laplaceschen Functionen höherer Ordnung*, J. Reine Angew. Math. 66 (1866) 161–176.
* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), Proposition 1 and Appendix C.
-/

open Finset

namespace BosonicLean

section Pairing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The pairing series `Φ(P, Q, R, S) = Σₙ n! Cₙ(Q, P) Cₙ(R, S)`. It is a total definition
(`0` if the series diverges); every statement about it assumes power bounds that make it
converge absolutely. -/
noncomputable def pairingSeries (P Q R S : A) : A :=
  ∑' n, (n.factorial : ℂ) • (cMatrix Q P n * cMatrix R S n)

/-- The terms of the pairing series are dominated by the majorant coefficients:
`‖n! Cₙ(Q, P) Cₙ(R, S)‖ ≤ C C' n! c_n(r, ‖P‖) c_n(r', ‖S‖)`. -/
theorem norm_pairing_term_le (h1 : ‖(1 : A)‖ ≤ 1) {Q R : A} {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (P S : A) (n : ℕ) :
    ‖(n.factorial : ℂ) • (cMatrix Q P n * cMatrix R S n)‖ ≤
      C * C' * ((n.factorial : ℝ) * majorantCoeff r ‖P‖ n * majorantCoeff r' ‖S‖ n) := by
  have hC : 0 ≤ C := by
    have := hQ 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  rw [norm_smul, Complex.norm_natCast]
  calc (n.factorial : ℝ) * ‖cMatrix Q P n * cMatrix R S n‖
      ≤ (n.factorial : ℝ) * ((C * majorantCoeff r ‖P‖ n) * (C' * majorantCoeff r' ‖S‖ n)) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_cMatrix_le h1 hQ hr P n)
          (norm_cMatrix_le h1 hR hr' S n) (norm_nonneg _)
          (mul_nonneg hC (majorantCoeff_nonneg hr (norm_nonneg _) n)))
    _ = C * C' * ((n.factorial : ℝ) * majorantCoeff r ‖P‖ n * majorantCoeff r' ‖S‖ n) := by
        ring

/-- **Absolute convergence of the pairing series.** If `Q`, `R` have power bounds `(C, r)`,
`(C', r')` with `r, r' ≥ 0` and `r + r' < 1`, the series converges absolutely. -/
theorem summable_norm_pairingSeries (h1 : ‖(1 : A)‖ ≤ 1) {Q R : A} {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) (P S : A) :
    Summable fun n : ℕ => ‖(n.factorial : ℂ) • (cMatrix Q P n * cMatrix R S n)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_pairing_term_le h1 hQ hR hr hr' P S)
    ((summable_majorant hr hr' (norm_nonneg P) (norm_nonneg S) hrr).mul_left (C * C'))

/-- **The majorant bound for the pairing series.** Under the hypotheses of
`BosonicLean.summable_norm_pairingSeries`,
`Σₙ ‖n! Cₙ(Q, P) Cₙ(R, S)‖ ≤ C C' Σₙ n! c_n(r, ‖P‖) c_n(r', ‖S‖)`. -/
theorem tsum_norm_pairingSeries_le (h1 : ‖(1 : A)‖ ≤ 1) {Q R : A} {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) (P S : A) :
    ∑' n : ℕ, ‖(n.factorial : ℂ) • (cMatrix Q P n * cMatrix R S n)‖ ≤
      C * C' * ∑' n : ℕ, (n.factorial : ℝ) * majorantCoeff r ‖P‖ n * majorantCoeff r' ‖S‖ n := by
  have hm := summable_majorant hr hr' (norm_nonneg P) (norm_nonneg S) hrr
  rw [← hm.tsum_mul_left]
  exact (summable_norm_pairingSeries h1 hQ hR hr hr' hrr P S).tsum_le_tsum
    (norm_pairing_term_le h1 hQ hR hr hr' P S) (hm.mul_left _)

end Pairing

section RingAlgebra

variable {B : Type*} [Ring B]

/-- The algebra behind the first-order equation. Let `P, Q, R, S, T` commute pairwise, let
`J = T P F + 2 Q H` and `(1 - 4QR) H = (T S + 2 R T P) F`. Then
`(1 - 4QR)(P H + S J) = 2T (R P² + S P + Q S²) F`. -/
theorem ode_algebra {P Q R S T F H J : B} (hPQ : Commute P Q) (hPR : Commute P R)
    (hPS : Commute P S) (hQR : Commute Q R) (hQS : Commute Q S) (hRS : Commute R S)
    (hTP : Commute T P) (hTQ : Commute T Q) (hTR : Commute T R) (hTS : Commute T S)
    (eJ : J = T * P * F + 2 * (Q * H))
    (eH : (1 - 4 * (Q * R)) * H = (T * S + 2 * (R * (T * P))) * F) :
    (1 - 4 * (Q * R)) * (P * H + S * J) = 2 * T * (R * P ^ 2 + S * P + Q * S ^ 2) * F := by
  have cX : ∀ X : B, Commute Q X → Commute R X → Commute (1 - 4 * (Q * R)) X := fun X hQ hR =>
    (Commute.one_left X).sub_left ((Commute.ofNat_left 4 X).mul_left (hQ.mul_left hR))
  have cXP := cX P hPQ.symm hPR.symm
  have cXS := cX S hQS hRS
  have cXQ := cX Q (Commute.refl Q) hQR.symm
  have hXJ : (1 - 4 * (Q * R)) * J =
      (1 - 4 * (Q * R)) * (T * P * F) + 2 * (Q * ((1 - 4 * (Q * R)) * H)) := by
    rw [eJ, mul_add]
    congr 1
    rw [← mul_assoc _ 2 (Q * H), ← (Commute.ofNat_left 2 _).eq, mul_assoc 2, ← mul_assoc _ Q H,
      cXQ.eq, mul_assoc Q]
  have e1 : P * T * S = T * S * P := by
    rw [← hTP.eq, mul_assoc, hPS.eq, ← mul_assoc]
  have e2 : S * T * P = T * S * P := by rw [← hTS.eq]
  have e3 : P * R * T * P = T * R * P * P := by
    rw [hPR.eq, mul_assoc R P T, ← hTP.eq, ← mul_assoc R T P, ← hTR.eq]
  have e4 : S * Q * T * S = T * Q * S * S := by
    rw [← hQS.eq, mul_assoc Q S T, ← hTS.eq, ← mul_assoc Q T S, ← hTQ.eq]
  calc (1 - 4 * (Q * R)) * (P * H + S * J)
      = P * ((1 - 4 * (Q * R)) * H) + S * ((1 - 4 * (Q * R)) * J) := by
        rw [mul_add, ← mul_assoc, cXP.eq, mul_assoc, ← mul_assoc _ S, cXS.eq, mul_assoc]
    _ = P * ((T * S + 2 * (R * (T * P))) * F) + S * ((1 - 4 * (Q * R)) * (T * P * F) +
          2 * (Q * ((T * S + 2 * (R * (T * P))) * F))) := by rw [hXJ, eH]
    _ = (P * T * S + 2 * (P * R * T * P) + S * T * P + 2 * (S * Q * T * S)) * F := by
        noncomm_ring
    _ = 2 * T * (R * P ^ 2 + S * P + Q * S ^ 2) * F := by
        rw [e1, e2, e3, e4]
        noncomm_ring

end RingAlgebra

/-! ### The index-shifted pairing series and their recurrences

For scalars, `Φ(P, Q, R, S)` is the bilinear Fischer pairing `⟨f, g⟩ = Σₙ n! fₙ gₙ` of
`f = e^{Q z² + P z}` and `g = e^{R z² + S z}`. Multiplication by `z` and `∂ = d/dz` are adjoint
for it, and the index-shifted series are `H = ⟨z f, g⟩ = ⟨f, ∂g⟩` and `J = ⟨∂f, g⟩ = ⟨f, z g⟩`. -/

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- `H(P, Q, R, S) = Σₙ (n+1)! Cₙ(Q, P) C_{n+1}(R, S)`, the index-shifted pairing series with the
second index increased by one. A total definition (`0` if the series diverges). -/
noncomputable def pairingShift (P Q R S : A) : A :=
  ∑' n, ((n + 1).factorial : ℂ) • (cMatrix Q P n * cMatrix R S (n + 1))

/-- `J(P, Q, R, S) = Σₙ (n+1)! C_{n+1}(Q, P) Cₙ(R, S)`, the index-shifted pairing series with the
first index increased by one. A total definition (`0` if the series diverges). -/
noncomputable def pairingShift' (P Q R S : A) : A :=
  ∑' n, ((n + 1).factorial : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S n)

/-- The terms of `H` are dominated by the majorant coefficients with `‖P‖` increased by one. -/
theorem summable_norm_pairingShift (h1 : ‖(1 : A)‖ ≤ 1) {Q R : A} {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) (P S : A) :
    Summable fun n : ℕ => ‖((n + 1).factorial : ℂ) • (cMatrix Q P n * cMatrix R S (n + 1))‖ := by
  have hC := hQ.const_nonneg
  have hC' := hR.const_nonneg
  have hm := (summable_nat_add_iff 1).mpr
    (summable_majorant hr hr' (by positivity : 0 ≤ ‖P‖ + 1) (norm_nonneg S) hrr)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hm.mul_left (C * C'))
  rw [norm_smul, Complex.norm_natCast]
  have hP := (norm_cMatrix_le h1 hQ hr P n).trans
    (mul_le_mul_of_nonneg_left (majorantCoeff_le_succ hr (norm_nonneg P) n) hC)
  have hS := norm_cMatrix_le h1 hR hr' S (n + 1)
  have hb : 0 ≤ C' * majorantCoeff r' ‖S‖ (n + 1) :=
    mul_nonneg hC' (majorantCoeff_nonneg hr' (norm_nonneg _) _)
  calc ((n + 1).factorial : ℝ) * ‖cMatrix Q P n * cMatrix R S (n + 1)‖
      ≤ ((n + 1).factorial : ℝ) * ((C * majorantCoeff r (‖P‖ + 1) (n + 1)) *
          (C' * majorantCoeff r' ‖S‖ (n + 1))) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul hP hS (norm_nonneg _)
          (mul_nonneg hC (majorantCoeff_nonneg hr (by positivity) _)))
    _ = C * C' * (((n + 1).factorial : ℝ) * majorantCoeff r (‖P‖ + 1) (n + 1) *
          majorantCoeff r' ‖S‖ (n + 1)) := by ring

/-- The terms of `J` are dominated by the majorant coefficients with `‖S‖` increased by one. -/
theorem summable_norm_pairingShift' (h1 : ‖(1 : A)‖ ≤ 1) {Q R : A} {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) (P S : A) :
    Summable fun n : ℕ => ‖((n + 1).factorial : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S n)‖ := by
  have hC := hQ.const_nonneg
  have hC' := hR.const_nonneg
  have hm := (summable_nat_add_iff 1).mpr
    (summable_majorant hr hr' (norm_nonneg P) (by positivity : 0 ≤ ‖S‖ + 1) hrr)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hm.mul_left (C * C'))
  rw [norm_smul, Complex.norm_natCast]
  have hP := norm_cMatrix_le h1 hQ hr P (n + 1)
  have hS := (norm_cMatrix_le h1 hR hr' S n).trans
    (mul_le_mul_of_nonneg_left (majorantCoeff_le_succ hr' (norm_nonneg S) n) hC')
  calc ((n + 1).factorial : ℝ) * ‖cMatrix Q P (n + 1) * cMatrix R S n‖
      ≤ ((n + 1).factorial : ℝ) * ((C * majorantCoeff r ‖P‖ (n + 1)) *
          (C' * majorantCoeff r' (‖S‖ + 1) (n + 1))) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul hP hS (norm_nonneg _)
          (mul_nonneg hC (majorantCoeff_nonneg hr (norm_nonneg _) _)))
    _ = C * C' * (((n + 1).factorial : ℝ) * majorantCoeff r ‖P‖ (n + 1) *
          majorantCoeff r' (‖S‖ + 1) (n + 1)) := by ring

variable [CompleteSpace A]

/-- **The recurrences for `H` and `J`.** For pairwise commuting `P, Q, R, S` with power bounds of
`Q`, `R` whose rates add to less than `1`: `H = S Φ + 2 R J` and `J = P Φ + 2 Q H`. -/
theorem pairingShift_eq_and (h1 : ‖(1 : A)‖ ≤ 1) {P Q R S : A} (hPQ : Commute P Q)
    (hPR : Commute P R) (hPS : Commute P S) (hQR : Commute Q R) (hQS : Commute Q S)
    (hRS : Commute R S) {C C' r r' : ℝ} (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r')
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrr : r + r' < 1) :
    pairingShift P Q R S = S * pairingSeries P Q R S + (2 : ℂ) • (R * pairingShift' P Q R S) ∧
      pairingShift' P Q R S = P * pairingSeries P Q R S + (2 : ℂ) • (Q * pairingShift P Q R S) := by
  set a : ℕ → A := fun n => (n.factorial : ℂ) • (cMatrix Q P n * cMatrix R S n) with ha
  set h : ℕ → A := fun n => ((n + 1).factorial : ℂ) • (cMatrix Q P n * cMatrix R S (n + 1))
    with hh
  set j : ℕ → A := fun n => ((n + 1).factorial : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S n)
    with hj
  have hA : HasSum a (pairingSeries P Q R S) :=
    (summable_norm_pairingSeries h1 hQ hR hr hr' hrr P S).of_norm.hasSum
  have hH : HasSum h (pairingShift P Q R S) :=
    (summable_norm_pairingShift h1 hQ hR hr hr' hrr P S).of_norm.hasSum
  have hJ : HasSum j (pairingShift' P Q R S) :=
    (summable_norm_pairingShift' h1 hQ hR hr hr' hrr P S).of_norm.hasSum
  have hA1 : HasSum (fun n => a (n + 1)) (pairingSeries P Q R S - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hA
    simpa [ha, cMatrix_zero] using this
  -- commutation of the outer factors with the polynomials
  have cRQP : ∀ n, Commute R (cMatrix Q P n) := commute_cMatrix_right hQR.symm hPR.symm
  have cSQP : ∀ n, Commute S (cMatrix Q P n) := commute_cMatrix_right hQS.symm hPS.symm
  have cSRS : ∀ n, Commute S (cMatrix R S n) := commute_cMatrix_right hRS.symm (Commute.refl S)
  have cQRS : ∀ n, Commute Q (cMatrix R S n) := commute_cMatrix_right hQR hQS
  have cPRS : ∀ n, Commute P (cMatrix R S n) := commute_cMatrix_right hPR hPS
  have cPQP : ∀ n, Commute P (cMatrix Q P n) := commute_cMatrix_right hPQ (Commute.refl P)
  have hfac : ∀ n, (((n + 2).factorial : ℕ) : ℂ) = ((n + 1).factorial : ℂ) * ((n + 2 : ℕ) : ℂ) := by
    intro n
    rw [Nat.factorial_succ (n + 1)]
    push_cast
    ring
  constructor
  · -- `h (n+1) = S a (n+1) + 2 R j n`
    have hstep : ∀ n, h (n + 1) = S * a (n + 1) + (2 : ℂ) • (R * j n) := by
      intro n
      change (((n + 2).factorial : ℕ) : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S (n + 2)) =
        S * ((((n + 1).factorial : ℕ) : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S (n + 1))) +
          (2 : ℂ) • (R * ((((n + 1).factorial : ℕ) : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S n)))
      rw [hfac, mul_smul, ← mul_smul_comm, cMatrix_succ_succ, mul_add, smul_add, add_comm]
      congr 1
      · rw [mul_smul_comm, ← mul_assoc, ((cSQP (n + 1)).mul_right (cSRS (n + 1))).eq]
      · rw [mul_smul_comm, mul_smul_comm, smul_comm, ← mul_assoc,
          ← (cRQP (n + 1)).eq, mul_assoc]
    have hsum : HasSum (fun n => h (n + 1))
        (S * (pairingSeries P Q R S - 1) + (2 : ℂ) • (R * pairingShift' P Q R S)) := by
      simp_rw [hstep]
      exact (hA1.mul_left S).add ((hJ.mul_left R).const_smul (2 : ℂ))
    have h0 : h 0 = S := by simp [hh, cMatrix_zero, cMatrix_one]
    refine hH.unique ((hasSum_nat_add_iff' 1).mp ?_)
    convert hsum using 1
    rw [sum_range_one, h0, mul_sub, mul_one]
    abel
  · -- `j (n+1) = P a (n+1) + 2 Q h n`
    have hstep : ∀ n, j (n + 1) = P * a (n + 1) + (2 : ℂ) • (Q * h n) := by
      intro n
      change (((n + 2).factorial : ℕ) : ℂ) • (cMatrix Q P (n + 2) * cMatrix R S (n + 1)) =
        P * ((((n + 1).factorial : ℕ) : ℂ) • (cMatrix Q P (n + 1) * cMatrix R S (n + 1))) +
          (2 : ℂ) • (Q * ((((n + 1).factorial : ℕ) : ℂ) • (cMatrix Q P n * cMatrix R S (n + 1))))
      rw [hfac, mul_smul, ← smul_mul_assoc, cMatrix_succ_succ, add_mul, smul_add, add_comm]
      congr 1
      · rw [mul_smul_comm, ← mul_assoc, ← (cPQP (n + 1)).eq,
          mul_assoc]
      · rw [mul_smul_comm, smul_mul_assoc, smul_comm, mul_assoc]
    have hsum : HasSum (fun n => j (n + 1))
        (P * (pairingSeries P Q R S - 1) + (2 : ℂ) • (Q * pairingShift P Q R S)) := by
      simp_rw [hstep]
      exact (hA1.mul_left P).add ((hH.mul_left Q).const_smul (2 : ℂ))
    have j0 : j 0 = P := by simp [hj, cMatrix_zero, cMatrix_one]
    refine hJ.unique ((hasSum_nat_add_iff' 1).mp ?_)
    convert hsum using 1
    rw [sum_range_one, j0, mul_sub, mul_one]
    abel

/-- **`H` in terms of `Φ`.** For pairwise commuting `P, Q, R, S` with power bounds of `Q`, `R`
whose rates add to less than `1`: `(1 - 4QR) H = (S + 2RP) Φ`. -/
theorem one_sub_mul_pairingShift (h1 : ‖(1 : A)‖ ≤ 1) {P Q R S : A} (hPQ : Commute P Q)
    (hPR : Commute P R) (hPS : Commute P S) (hQR : Commute Q R) (hQS : Commute Q S)
    (hRS : Commute R S) {C C' r r' : ℝ} (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r')
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrr : r + r' < 1) :
    (1 - (4 : ℂ) • (Q * R)) * pairingShift P Q R S =
      (S + (2 : ℂ) • (R * P)) * pairingSeries P Q R S := by
  obtain ⟨eH, eJ⟩ :=
    pairingShift_eq_and h1 hPQ hPR hPS hQR hQS hRS hQ hR hr hr' hrr
  set Φ := pairingSeries P Q R S
  set H := pairingShift P Q R S
  have eH' : H = S * Φ + (2 : ℂ) • (R * P * Φ) + (4 : ℂ) • (Q * R * H) := by
    calc H = S * Φ + (2 : ℂ) • (R * pairingShift' P Q R S) := eH
      _ = S * Φ + (2 : ℂ) • (R * (P * Φ + (2 : ℂ) • (Q * H))) := by rw [eJ]
      _ = S * Φ + (2 : ℂ) • (R * P * Φ) + (4 : ℂ) • (Q * R * H) := by
        rw [mul_add, smul_add, mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc, ← hQR.eq,
          add_assoc]
        norm_num
  rw [sub_mul, one_mul, smul_mul_assoc, add_mul, smul_mul_assoc]
  nth_rewrite 1 [eH']
  abel

/-- **The initial value.** `Φ(0, Q, R, 0) = 𝒮(QR)` for commuting `Q`, `R` with power bounds whose
rates add to less than `1`. -/
theorem pairingSeries_zero_zero {Q R : A} (hQR : Commute Q R) {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) :
    pairingSeries 0 Q R 0 = centralBinomSeries (Q * R) := by
  have h4 : 4 * (r * r') < 1 := by nlinarith [sq_nonneg (r - r'), add_nonneg hr hr']
  have hS : HasSum (fun i : ℕ => (i.centralBinom : ℂ) • (Q * R) ^ i) (centralBinomSeries (Q * R)) :=
    (summable_norm_centralBinomSeries (hQ.mul_of_commute hQR hR) (mul_nonneg hr hr')
      h4).of_norm.hasSum
  set f : ℕ → A := fun n => (n.factorial : ℂ) • (cMatrix Q 0 n * cMatrix R 0 n) with hf
  have he : HasSum (fun m => f (2 * m)) (centralBinomSeries (Q * R)) := by
    convert hS using 1
    funext m
    simp only [hf]
    rw [cMatrix_zero_right_even, cMatrix_zero_right_even, smul_mul_smul_comm, smul_smul,
      ← hQR.mul_pow]
    congr 1
    have hc : (m.centralBinom * m.factorial * m.factorial : ℕ) = (2 * m).factorial := by
      rw [Nat.centralBinom_eq_two_mul_choose, mul_assoc]
      have := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
      rwa [show 2 * m - m = m by omega, mul_assoc] at this
    have h0 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [← hc]
    push_cast
    field_simp
  have ho : HasSum (fun m => f (2 * m + 1)) 0 := by
    simp only [hf, cMatrix_zero_right_odd, zero_mul, smul_zero]
    exact hasSum_zero
  have := he.even_add_odd ho
  rw [add_zero] at this
  exact this.tsum_eq

/-- For commuting `Q`, `R` with power bounds whose rates add to less than `1`, `1 - 4QR` is
invertible. -/
theorem isUnit_one_sub_four_smul_mul {Q R : A} (hQR : Commute Q R) {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) : IsUnit (1 - (4 : ℂ) • (Q * R)) :=
  isUnit_one_sub_four_smul (hQ.mul_of_commute hQR hR) (mul_nonneg hr hr')
    (by nlinarith [sq_nonneg (r - r'), add_nonneg hr hr'])

/-- For commuting `Q`, `R` with power bounds whose rates add to less than `1`:
`𝒮(QR)² = Δ = (1 - 4QR)⁻¹`. -/
theorem centralBinomSeries_mul_self_of_commute {Q R : A} (hQR : Commute Q R) {C C' r r' : ℝ}
    (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r') (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r + r' < 1) :
    centralBinomSeries (Q * R) * centralBinomSeries (Q * R) =
      Ring.inverse (1 - (4 : ℂ) • (Q * R)) :=
  centralBinomSeries_mul_self (hQ.mul_of_commute hQR hR) (mul_nonneg hr hr')
    (by nlinarith [sq_nonneg (r - r'), add_nonneg hr hr'])

/-! ### The first-order equation -/

/-- **The first-order equation.** For pairwise commuting `P, Q, R, S` with power bounds of `Q`,
`R` whose rates add to less than `1`, `F(λ) = Φ(λP, Q, R, λS)` satisfies
`F'(λ) = 2λ Δ (R P² + S P + Q S²) F(λ)` with `Δ = (1 - 4QR)⁻¹`, at every `λ ∈ ℂ`. -/
theorem hasDerivAt_pairingSeries_smul (h1 : ‖(1 : A)‖ ≤ 1) {P Q R S : A} (hPQ : Commute P Q)
    (hPR : Commute P R) (hPS : Commute P S) (hQR : Commute Q R) (hQS : Commute Q S)
    (hRS : Commute R S) {C C' r r' : ℝ} (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r')
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrr : r + r' < 1) (t : ℂ) :
    HasDerivAt (fun s : ℂ => pairingSeries (s • P) Q R (s • S))
      (((2 : ℂ) * t) • (Ring.inverse (1 - (4 : ℂ) • (Q * R)) * (R * P ^ 2 + S * P + Q * S ^ 2)) *
        pairingSeries (t • P) Q R (t • S)) t := by
  have hC := hQ.const_nonneg
  have hC' := hR.const_nonneg
  set ρ : ℝ := ‖t‖ + 1 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set U : Set ℂ := Metric.ball 0 ρ with hU
  set dQ : ℕ → ℂ → A := fun n s => if n = 0 then 0 else cMatrix Q (s • P) (n - 1) * P
  set dR : ℕ → ℂ → A := fun n s => if n = 0 then 0 else cMatrix R (s • S) (n - 1) * S
  set g : ℕ → ℂ → A := fun n s => (n.factorial : ℂ) • (cMatrix Q (s • P) n * cMatrix R (s • S) n)
  set g' : ℕ → ℂ → A := fun n s => (n.factorial : ℂ) •
    (dQ n s * cMatrix R (s • S) n + cMatrix Q (s • P) n * dR n s)
  set a : ℝ := ρ * ‖P‖ + 1
  set b : ℝ := ρ * ‖S‖ + 1
  set u : ℕ → ℝ := fun n => C * C' * (‖P‖ + ‖S‖) *
    ((n.factorial : ℝ) * majorantCoeff r a n * majorantCoeff r' b n)
  have hu : Summable u :=
    (summable_majorant hr hr' (by positivity) (by positivity) hrr).mul_left _
  have hg : ∀ n y, y ∈ U → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    ((hasDerivAt_cMatrix_smul' Q P n y).fun_mul
      (hasDerivAt_cMatrix_smul' R S n y)).const_smul (n.factorial : ℂ)
  have hg' : ∀ n y, y ∈ U → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hy' : ‖y‖ ≤ ρ := by
      rw [hU, Metric.mem_ball, dist_zero_right] at hy
      exact hy.le
    have e1 := norm_deriv_cMatrix_smul_le h1 hQ hr P n hρ0 hy'
    have e2 := norm_cMatrix_smul_le h1 hR hr' S n hy'
    have e3 := norm_cMatrix_smul_le h1 hQ hr P n hy'
    have e4 := norm_deriv_cMatrix_smul_le h1 hR hr' S n hρ0 hy'
    have ca := majorantCoeff_nonneg hr (show 0 ≤ a by positivity) n
    have cb := majorantCoeff_nonneg hr' (show 0 ≤ b by positivity) n
    have hsum : ‖dQ n y * cMatrix R (y • S) n + cMatrix Q (y • P) n * dR n y‖ ≤
        C * ‖P‖ * majorantCoeff r a n * (C' * majorantCoeff r' b n) +
          C * majorantCoeff r a n * (C' * ‖S‖ * majorantCoeff r' b n) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul e1 e2 (norm_nonneg _) (by positivity)))
        ((norm_mul_le _ _).trans (mul_le_mul e3 e4 (norm_nonneg _) (by positivity))))
    calc ‖g' n y‖ = (n.factorial : ℝ) *
          ‖dQ n y * cMatrix R (y • S) n + cMatrix Q (y • P) n * dR n y‖ := by
          simp only [g', norm_smul, Complex.norm_natCast]
      _ ≤ (n.factorial : ℝ) * (C * ‖P‖ * majorantCoeff r a n * (C' * majorantCoeff r' b n) +
          C * majorantCoeff r a n * (C' * ‖S‖ * majorantCoeff r' b n)) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = u n := by simp only [u]; ring
  have hg0 : Summable fun n => g n 0 :=
    (summable_norm_pairingSeries h1 hQ hR hr hr' hrr _ _).of_norm
  have ht : t ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right, hρ]
    linarith
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hg hg' (Metric.mem_ball_self (by positivity)) hg0 ht
  -- the recurrences for `H` and `J` at `(tP, Q, R, tS)`
  obtain ⟨eH, eJ⟩ := pairingShift_eq_and h1 (hPQ.smul_left t) (hPR.smul_left t)
    ((hPS.smul_left t).smul_right t) hQR (hQS.smul_right t) (hRS.smul_right t) hQ hR hr hr' hrr
  have eK := one_sub_mul_pairingShift h1 (hPQ.smul_left t) (hPR.smul_left t)
    ((hPS.smul_left t).smul_right t) hQR (hQS.smul_right t) (hRS.smul_right t) hQ hR hr hr' hrr
  have hHs : HasSum (fun n => ((n + 1).factorial : ℂ) •
      (cMatrix Q (t • P) n * cMatrix R (t • S) (n + 1))) (pairingShift (t • P) Q R (t • S)) :=
    (summable_norm_pairingShift h1 hQ hR hr hr' hrr _ _).of_norm.hasSum
  have hJs : HasSum (fun n => ((n + 1).factorial : ℂ) •
      (cMatrix Q (t • P) (n + 1) * cMatrix R (t • S) n)) (pairingShift' (t • P) Q R (t • S)) :=
    (summable_norm_pairingShift' h1 hQ hR hr hr' hrr _ _).of_norm.hasSum
  have cPQt : ∀ n, Commute P (cMatrix Q (t • P) n) :=
    commute_cMatrix_right hPQ ((Commute.refl P).smul_right t)
  have cSRt : ∀ n, Commute S (cMatrix R (t • S) n) :=
    commute_cMatrix_right hRS.symm ((Commute.refl S).smul_right t)
  have cSQt : ∀ n, Commute S (cMatrix Q (t • P) n) :=
    commute_cMatrix_right hQS.symm (hPS.symm.smul_right t)
  -- the derivative series is `P H + S J` at `(tP, Q, R, tS)`
  have hsum1 : HasSum (fun n => (n.factorial : ℂ) • (dQ n t * cMatrix R (t • S) n))
      (P * pairingShift (t • P) Q R (t • S)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have hf : (fun n => ((n + 1).factorial : ℂ) • (dQ (n + 1) t * cMatrix R (t • S) (n + 1))) =
        fun n => P * (((n + 1).factorial : ℂ) •
          (cMatrix Q (t • P) n * cMatrix R (t • S) (n + 1))) := by
      funext n
      simp only [dQ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [mul_smul_comm, ← (cPQt n).eq, mul_assoc]
    rw [sum_range_one]
    simpa only [dQ, ↓reduceIte, zero_mul, smul_zero, sub_zero, hf] using hHs.mul_left P
  have hsum2 : HasSum (fun n => (n.factorial : ℂ) • (cMatrix Q (t • P) n * dR n t))
      (S * pairingShift' (t • P) Q R (t • S)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have hf : (fun n => ((n + 1).factorial : ℂ) • (cMatrix Q (t • P) (n + 1) * dR (n + 1) t)) =
        fun n => S * (((n + 1).factorial : ℂ) •
          (cMatrix Q (t • P) (n + 1) * cMatrix R (t • S) n)) := by
      funext n
      simp only [dR, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [mul_smul_comm, ← mul_assoc, ← ((cSQt (n + 1)).mul_right (cSRt n)).eq]
    rw [sum_range_one]
    simpa only [dR, ↓reduceIte, mul_zero, smul_zero, sub_zero, hf] using hJs.mul_left S
  have hval : ∑' n, g' n t =
      P * pairingShift (t • P) Q R (t • S) + S * pairingShift' (t • P) Q R (t • S) := by
    refine ((hsum1.add hsum2).congr_fun ?_).tsum_eq
    intro n
    simp only [g', smul_add]
  rw [hval] at hderiv
  refine hderiv.congr_deriv ?_
  -- the algebra
  have hX : IsUnit (1 - (4 : ℂ) • (Q * R)) :=
    isUnit_one_sub_four_smul (hQ.mul_of_commute hQR hR) (mul_nonneg hr hr')
      (by nlinarith [sq_nonneg (r - r'), add_nonneg hr hr'])
  have cT : ∀ X : A, Commute (algebraMap ℂ A t) X := fun X => Algebra.commute_algebraMap_left t X
  have key := ode_algebra (F := pairingSeries (t • P) Q R (t • S))
    (H := pairingShift (t • P) Q R (t • S)) (J := pairingShift' (t • P) Q R (t • S))
    hPQ hPR hPS hQR hQS hRS (cT P) (cT Q) (cT R) (cT S)
    (by rw [eJ]; simp only [Algebra.smul_def, map_ofNat, mul_assoc])
    (by simpa only [Algebra.smul_def, map_ofNat, mul_assoc] using eK)
  have hX' : (1 - (4 : ℂ) • (Q * R)) = 1 - 4 * (Q * R) := by rw [Algebra.smul_def, map_ofNat]
  have hXu : IsUnit (1 - 4 * (Q * R)) := hX' ▸ hX
  refine hXu.mul_left_cancel ?_
  generalize pairingSeries (t • P) Q R (t • S) = F at key ⊢
  generalize pairingShift (t • P) Q R (t • S) = H at key ⊢
  generalize pairingShift' (t • P) Q R (t • S) = J at key ⊢
  rw [hX', key, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc,
    Ring.mul_inverse_cancel _ hXu, one_mul, Algebra.smul_def, map_mul, map_ofNat]
  noncomm_ring

/-! ### Mehler's formula -/

/-- **Mehler's formula** with coefficients in a commutative Banach algebra (Tjoa–Cirac,
Proposition 1, core form; Appendix C, the closed form of `𝓔(P, Q, R, S)`). For pairwise commuting
`P, Q, R, S` in a complete normed `ℂ`-algebra with `‖1‖ ≤ 1`, where `Q`, `R` have power bounds
whose rates add to less than `1`:
`Φ(P, Q, R, S) = 𝒮(QR) exp(Δ (R P² + S P + Q S²))` with `Δ = (1 - 4QR)⁻¹`. -/
theorem pairingSeries_eq (h1 : ‖(1 : A)‖ ≤ 1) {P Q R S : A} (hPQ : Commute P Q)
    (hPR : Commute P R) (hPS : Commute P S) (hQR : Commute Q R) (hQS : Commute Q S)
    (hRS : Commute R S) {C C' r r' : ℝ} (hQ : HasPowerBound Q C r) (hR : HasPowerBound R C' r')
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrr : r + r' < 1) :
    pairingSeries P Q R S = centralBinomSeries (Q * R) *
      NormedSpace.exp (Ring.inverse (1 - (4 : ℂ) • (Q * R)) * (R * P ^ 2 + S * P + Q * S ^ 2)) := by
  have hF := hasDerivAt_pairingSeries_smul h1 hPQ hPR hPS hQR hQS hRS hQ hR hr hr' hrr
  set Z := Ring.inverse (1 - (4 : ℂ) • (Q * R)) * (R * P ^ 2 + S * P + Q * S ^ 2) with hZ
  clear_value Z
  set G : ℂ → A := fun s => NormedSpace.exp ((-(s ^ 2)) • Z) * pairingSeries (s • P) Q R (s • S)
  have hE : ∀ s : ℂ, HasDerivAt (fun s : ℂ => NormedSpace.exp ((-(s ^ 2)) • Z))
      ((-(2 * s)) • (NormedSpace.exp ((-(s ^ 2)) • Z) * Z)) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℂ => -(s ^ 2)) (-(2 * s)) s := by
      convert (hasDerivAt_pow 2 s).fun_neg using 1
      simp
    exact (hasDerivAt_exp_smul_const Z (-(s ^ 2))).scomp s h2
  have hG : ∀ s, HasDerivAt G 0 s := by
    intro s
    have := (hE s).fun_mul (hF s)
    convert this using 1
    simp only [smul_mul_assoc, mul_smul_comm, neg_smul]
    rw [neg_mul, smul_mul_assoc, mul_assoc, neg_add_cancel]
  have hconst : G 1 = G 0 :=
    is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) 1 0
  have hG0 : G 0 = centralBinomSeries (Q * R) := by
    simp only [G, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      NormedSpace.exp_zero, one_mul]
    exact pairingSeries_zero_zero hQR hQ hR hr hr' hrr
  have hG1 : G 1 = NormedSpace.exp (-Z) * pairingSeries P Q R S := by
    simp [G]
  -- `𝒮(QR)` commutes with `Z`
  have hX : IsUnit (1 - (4 : ℂ) • (Q * R)) :=
    isUnit_one_sub_four_smul (hQ.mul_of_commute hQR hR) (mul_nonneg hr hr')
      (by nlinarith [sq_nonneg (r - r'), add_nonneg hr hr'])
  obtain ⟨u, hu⟩ := hX
  have cQRX : Commute (Q * R) (1 - (4 : ℂ) • (Q * R)) :=
    (Commute.one_right _).sub_right ((Commute.refl _).smul_right _)
  have cP : Commute (Q * R) P := hPQ.symm.mul_left hPR.symm
  have cQ : Commute (Q * R) Q := (Commute.refl Q).mul_left hQR.symm
  have cR : Commute (Q * R) R := hQR.mul_left (Commute.refl R)
  have cS : Commute (Q * R) S := hQS.mul_left hRS
  have cY : Commute (Q * R) (R * P ^ 2 + S * P + Q * S ^ 2) :=
    ((cR.mul_right (cP.pow_right 2)).add_right (cS.mul_right cP)).add_right
      (cQ.mul_right (cS.pow_right 2))
  have cQRZ : Commute (Q * R) Z := by
    rw [hZ, ← hu, Ring.inverse_unit]
    exact (Commute.units_inv_right (hu ▸ cQRX)).mul_right cY
  have cSZ : Commute (centralBinomSeries (Q * R)) Z :=
    Commute.tsum_left _ fun i => ((cQRZ.pow_left i).smul_left _)
  have hrad : ∀ x : A, x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℂ A).radius := fun x =>
    (NormedSpace.expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _
  have hexp : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) (Commute.refl Z).neg_right
      (hrad _) (hrad _), add_neg_cancel, NormedSpace.exp_zero]
  calc pairingSeries P Q R S
      = NormedSpace.exp Z * (NormedSpace.exp (-Z) * pairingSeries P Q R S) := by
        rw [← mul_assoc, hexp, one_mul]
    _ = NormedSpace.exp Z * centralBinomSeries (Q * R) := by rw [← hG1, hconst, hG0]
    _ = centralBinomSeries (Q * R) * NormedSpace.exp Z := (cSZ.exp_right).eq.symm

end Banach

/-! ### Scalars -/

/-- `C(2(n+1), n+1) ≤ 4 C(2n, n)`. -/
private theorem centralBinom_succ_le_four_mul (n : ℕ) :
    (n + 1).centralBinom ≤ 4 * n.centralBinom := by
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos n)
  rw [Nat.succ_mul_centralBinom_succ]
  calc 2 * (2 * n + 1) * n.centralBinom ≤ ((n + 1) * 4) * n.centralBinom :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) * (4 * n.centralBinom) := by ring

/-- The binomial series at a real point `a` with `|a| < 1/4` is the positive square root:
`𝒮(a) = (1 - 4a)^{-1/2}`. For `a < 0` the series alternates; its partial sums pair into
nonnegative terms because `C(2(n+1), n+1) ≤ 4 C(2n, n)`. -/
theorem centralBinomSeries_ofReal_of_abs_lt {a : ℝ} (ha : 4 * |a| < 1) :
    centralBinomSeries (a : ℂ) = ((1 - 4 * a) ^ (-(1 / 2 : ℝ)) : ℝ) := by
  have hb : HasPowerBound (a : ℂ) 1 |a| := fun m => by simp [norm_pow]
  set f : ℕ → ℝ := fun i => (i.centralBinom : ℝ) * a ^ i with hf
  have hS : centralBinomSeries (a : ℂ) = ((∑' i, f i : ℝ) : ℂ) := by
    rw [centralBinomSeries, Complex.ofReal_tsum]
    simp [hf, smul_eq_mul]
  have hsum : Summable f := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (by positivity) ha) fun i => ?_
    rw [hf, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.centralBinom_le_four_pow i
  have he : Summable fun k => f (2 * k) := hsum.comp_injective fun x y h => by omega
  have ho : Summable fun k => f (2 * k + 1) := hsum.comp_injective fun x y h => by omega
  have hpair : ∀ k, 0 ≤ f (2 * k) + f (2 * k + 1) := fun k => by
    have hC : ((2 * k + 1).centralBinom : ℝ) ≤ 4 * ((2 * k).centralBinom : ℝ) := by
      exact_mod_cast centralBinom_succ_le_four_mul (2 * k)
    have hA : (0 : ℝ) ≤ (2 * k).centralBinom := Nat.cast_nonneg _
    have hB : (0 : ℝ) ≤ (2 * k + 1).centralBinom := Nat.cast_nonneg _
    have hp : 0 ≤ a ^ (2 * k) := by rw [pow_mul]; positivity
    have h1 : -(((2 * k + 1).centralBinom : ℝ) * |a|) ≤ (2 * k + 1).centralBinom * a := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_abs_le a) hB
    have h2 : 0 ≤ ((2 * k).centralBinom : ℝ) + (2 * k + 1).centralBinom * a := by
      nlinarith [abs_nonneg a]
    simp only [hf, pow_succ]
    nlinarith [mul_nonneg hp h2]
  have h0 : 0 < f (2 * 0) + f (2 * 0 + 1) := by
    simp only [hf, mul_zero, zero_add, Nat.centralBinom_zero, pow_zero, Nat.cast_one, one_mul,
      pow_one, show Nat.centralBinom 1 = 2 by decide]
    have := neg_abs_le a
    push_cast
    linarith
  have hs0 : 0 < ∑' i, f i := by
    rw [← tsum_even_add_odd he ho, ← he.tsum_add ho]
    exact (he.add ho).tsum_pos hpair 0 h0
  have hsq := centralBinomSeries_mul_self hb (abs_nonneg a) ha
  rw [hS, Ring.inverse_eq_inv', smul_eq_mul] at hsq
  have h1 : 0 < 1 - 4 * a := by linarith [le_abs_self a]
  have hs2 : (∑' i, f i) ^ 2 = (1 - 4 * a)⁻¹ := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, sq, hsq]
    push_cast
    ring
  rw [hS, Real.rpow_neg h1.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, ← hs2,
    Real.sqrt_sq hs0.le]

/-- **Bond dimension one, single site** (`D = N = 1`). For `|κ| < 1/2`,
`Σₙ n! |Cₙ(κ, ℓ)|² = (1 - 4|κ|²)^{-1/2} exp((2 Re(κ̄ ℓ²) + |ℓ|²)/(1 - 4|κ|²))`, the squared norm
of the single-mode squeezed coherent state `e^{κ a†² + ℓ a†}∣0⟩` (Tjoa–Cirac, Sec. II A 1). -/
theorem hasSum_factorial_mul_normSq_cMatrix (κ ℓ : ℂ) (hκ : ‖κ‖ < 1 / 2) :
    HasSum (fun n : ℕ => (n.factorial : ℝ) * Complex.normSq (cMatrix κ ℓ n))
      ((1 - 4 * ‖κ‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp ((2 * (starRingEnd ℂ κ * ℓ ^ 2).re + ‖ℓ‖ ^ 2) / (1 - 4 * ‖κ‖ ^ 2))) := by
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hQ : HasPowerBound (starRingEnd ℂ κ) 1 ‖κ‖ := fun m => by simp [norm_pow]
  have hR : HasPowerBound κ 1 ‖κ‖ := fun m => by simp [norm_pow]
  have hrr : ‖κ‖ + ‖κ‖ < 1 := by linarith
  have hA := (summable_norm_pairingSeries h1 hQ hR (norm_nonneg _) (norm_nonneg _) hrr
    (starRingEnd ℂ ℓ) ℓ).of_norm.hasSum
  rw [← pairingSeries, pairingSeries_eq h1 (Commute.all _ _) (Commute.all _ _) (Commute.all _ _)
    (Commute.all _ _) (Commute.all _ _) (Commute.all _ _) hQ hR (norm_nonneg _) (norm_nonneg _)
    hrr] at hA
  have ha : 0 ≤ ‖κ‖ ^ 2 := by positivity
  have ha4 : 4 * ‖κ‖ ^ 2 < 1 := by nlinarith [norm_nonneg κ]
  rw [Complex.conj_mul', ← Complex.ofReal_pow,
    centralBinomSeries_ofReal_of_abs_lt (by rwa [abs_of_nonneg ha]),
    Ring.inverse_eq_inv', ← Complex.exp_eq_exp_ℂ] at hA
  have hY : κ * starRingEnd ℂ ℓ ^ 2 + ℓ * starRingEnd ℂ ℓ + starRingEnd ℂ κ * ℓ ^ 2 =
      ((2 * (starRingEnd ℂ κ * ℓ ^ 2).re + ‖ℓ‖ ^ 2 : ℝ) : ℂ) := by
    have hc : κ * starRingEnd ℂ ℓ ^ 2 = starRingEnd ℂ (starRingEnd ℂ κ * ℓ ^ 2) := by simp
    have hre := Complex.add_conj (starRingEnd ℂ κ * ℓ ^ 2)
    rw [hc, Complex.mul_conj']
    push_cast at hre ⊢
    linear_combination hre
  rw [hY] at hA
  rw [← Complex.hasSum_ofReal]
  convert hA using 1
  · funext n
    rw [← conj_cMatrix]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.normSq_eq_conj_mul_self,
      smul_eq_mul]
  · rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    field_simp

end BosonicLean
