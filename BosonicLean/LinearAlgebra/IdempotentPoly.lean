/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Idempotent polynomials for points with multiplicities

Let `s` be a finite set of points of a field with multiplicities `m μ`. The factors
`(X - μ)^{m μ}` are pairwise coprime, so with `f_μ = ∏_{ν ≠ μ} (X - ν)^{m ν}` there are polynomials
`g_μ` with `Σ_μ g_μ f_μ = 1` when `s` is non-empty. The idempotent polynomials `P_μ = g_μ f_μ`
satisfy `Σ_μ P_μ = 1`, `(X - μ)^{m μ} ∣ P_μ - 1` and `(X - ν)^{m ν} ∣ P_μ` for `ν ≠ μ` in `s`
(Chinese remainder idempotents). Any two families with these divisibility properties agree modulo
`∏_μ (X - μ)^{m μ}` (`BosonicLean.prod_pointFactor_dvd_sub`); only these properties are used. For
the eigenvalues of a matrix with their algebraic multiplicities, any such `P_μ` evaluated at the
matrix is its spectral idempotent (`BosonicLean.aeval_eq_spectralIdempotent`,
`BosonicLean.spectralIdempotent_eq_aeval_idempotentPoly`).

## Main definitions

* `BosonicLean.pointFactor m μ`: `(X - μ)^{m μ}`.
* `BosonicLean.bezoutCoeffOf s m`: polynomials `g_μ` with `Σ_μ g_μ f_μ = 1` (a choice).
* `BosonicLean.idempotentPoly s m μ`: `P_μ = g_μ f_μ` for `μ ∈ s`, `0` otherwise.

## Main results

* `BosonicLean.sum_idempotentPoly`, `BosonicLean.dvd_idempotentPoly_sub_one`,
  `BosonicLean.dvd_idempotentPoly`, `BosonicLean.prod_pointFactor_dvd_sub`.
* `BosonicLean.aeval_X_sub_C_pow_eq`, `BosonicLean.commute_aeval_aeval`: evaluation of `(X - c)^k`;
  polynomials in commuting elements commute.
-/

open Polynomial Finset Function

namespace BosonicLean

variable {𝕜 : Type*} [Field 𝕜] [DecidableEq 𝕜]

/-- The factor `(X - μ)^{m μ}`. -/
noncomputable def pointFactor (m : 𝕜 → ℕ) (μ : 𝕜) : 𝕜[X] := (X - C μ) ^ m μ

omit [DecidableEq 𝕜] in
/-- The factors at distinct points are pairwise coprime. -/
theorem pairwise_isCoprime_pointFactor (s : Finset 𝕜) (m : 𝕜 → ℕ) :
    Pairwise (IsCoprime on fun μ : s => pointFactor m μ) := by
  intro μ ν h
  refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
  exact (sub_ne_zero.mpr fun e => h (Subtype.ext e)).isUnit

/-- Polynomials `g_μ` with `Σ_μ g_μ f_μ = 1`, `f_μ = ∏_{ν ≠ μ} (X - ν)^{m ν}` (a choice), for a
non-empty set of points; `0` for the empty set, where no such family exists. Only
`sum_bezoutCoeffOf_mul` is used about it. -/
noncomputable def bezoutCoeffOf (s : Finset 𝕜) (m : 𝕜 → ℕ) : 𝕜 → 𝕜[X] :=
  if h : s.Nonempty then
    Classical.choose ((exists_sum_eq_one_iff_pairwise_coprime h).mpr
      (pairwise_isCoprime_pointFactor s m))
  else 0

/-- The partition of unity `Σ_μ g_μ f_μ = 1`. -/
theorem sum_bezoutCoeffOf_mul {s : Finset 𝕜} (m : 𝕜 → ℕ) (h : s.Nonempty) :
    ∑ μ ∈ s, bezoutCoeffOf s m μ * ∏ ν ∈ s \ {μ}, pointFactor m ν = 1 := by
  simp only [bezoutCoeffOf, h, ↓reduceDIte]
  exact Classical.choose_spec ((exists_sum_eq_one_iff_pairwise_coprime h).mpr
    (pairwise_isCoprime_pointFactor s m))

/-- The **idempotent polynomial** `P_μ = g_μ f_μ` at a point `μ ∈ s`; `0` for `μ ∉ s`. -/
noncomputable def idempotentPoly (s : Finset 𝕜) (m : 𝕜 → ℕ) (μ : 𝕜) : 𝕜[X] :=
  if μ ∈ s then bezoutCoeffOf s m μ * ∏ ν ∈ s \ {μ}, pointFactor m ν else 0

/-- `Σ_μ P_μ = 1` for a non-empty set of points. -/
theorem sum_idempotentPoly {s : Finset 𝕜} (m : 𝕜 → ℕ) (hs : s.Nonempty) :
    ∑ μ ∈ s, idempotentPoly s m μ = 1 := by
  rw [← sum_bezoutCoeffOf_mul m hs]
  refine sum_congr rfl fun μ hμ => ?_
  simp [idempotentPoly, hμ]

/-- `(X - ν)^{m ν} ∣ P_μ` for `ν ∈ s`, `ν ≠ μ`. -/
theorem dvd_idempotentPoly (s : Finset 𝕜) (m : 𝕜 → ℕ) {μ ν : 𝕜} (hν : ν ∈ s) (hμν : μ ≠ ν) :
    pointFactor m ν ∣ idempotentPoly s m μ := by
  unfold idempotentPoly
  split_ifs
  · exact Dvd.dvd.mul_left (dvd_prod_of_mem _ (mem_sdiff.mpr ⟨hν, by simpa [eq_comm] using hμν⟩)) _
  · exact dvd_zero _

/-- `(X - μ)^{m μ} ∣ P_μ - 1` for `μ ∈ s`. -/
theorem dvd_idempotentPoly_sub_one {s : Finset 𝕜} (m : 𝕜 → ℕ) {μ : 𝕜} (hμ : μ ∈ s) :
    pointFactor m μ ∣ idempotentPoly s m μ - 1 := by
  have h1 := sum_idempotentPoly m ⟨μ, hμ⟩
  rw [← add_sum_erase s _ hμ] at h1
  have : idempotentPoly s m μ - 1 = -∑ ν ∈ s.erase μ, idempotentPoly s m ν := by
    rw [← h1]; ring
  rw [this, dvd_neg]
  exact dvd_sum fun ν hν =>
    dvd_idempotentPoly s m hμ (mem_erase.mp hν).1

/-- Any two families with `(X - ν)^{m ν} ∣ P_μ - δ_μν` on `s` agree modulo
`∏_ν (X - ν)^{m ν}`. -/
theorem prod_pointFactor_dvd_sub {s : Finset 𝕜} (m : 𝕜 → ℕ) {P P' : 𝕜 → 𝕜[X]}
    (hP : ∀ μ ∈ s, ∀ ν ∈ s, pointFactor m ν ∣ P μ - if μ = ν then 1 else 0)
    (hP' : ∀ μ ∈ s, ∀ ν ∈ s, pointFactor m ν ∣ P' μ - if μ = ν then 1 else 0) {μ : 𝕜}
    (hμ : μ ∈ s) : ∏ ν ∈ s, pointFactor m ν ∣ P μ - P' μ := by
  refine Finset.prod_dvd_of_coprime (fun ν _ ν' _ h => ?_) fun ν hν => ?_
  · exact IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit)
  · have := dvd_sub (hP μ hμ ν hν) (hP' μ hμ ν hν)
    rwa [sub_sub_sub_cancel_right] at this

section Evaluation

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- `(X - c)^k` evaluated at an element `x` of an algebra is `(x - c)^k`. -/
theorem aeval_X_sub_C_pow_eq (x : A) (c : R) (k : ℕ) :
    aeval x ((X - C c) ^ k) = (x - c • 1) ^ k := by
  rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- Polynomials in commuting elements commute. -/
theorem commute_aeval_aeval {x y : A} (h : Commute x y) (p q : R[X]) :
    Commute (aeval x p) (aeval y q) := by
  have key : ∀ {x y : A}, Commute x y → ∀ q : R[X], Commute x (aeval y q) := by
    intro x y h q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_right hq
    | monomial k c =>
      rw [aeval_monomial]
      exact (Algebra.commute_algebraMap_left c x).symm.mul_right (h.pow_right k)
  exact (key (key h q).symm p).symm

end Evaluation

end BosonicLean
