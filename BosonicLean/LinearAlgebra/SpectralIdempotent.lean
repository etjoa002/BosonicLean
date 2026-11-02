/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import BosonicLean.LinearAlgebra.IdempotentPoly

/-!
# Spectral idempotents of a square matrix

Over an algebraically closed field `𝕜`, the characteristic polynomial of a square matrix `K`
splits as `χ = ∏_μ (X - μ)^{m_μ}` over the eigenvalues `μ` with algebraic multiplicities `m_μ`.
The factors `(X - μ)^{m_μ}` are pairwise coprime, so with `f_μ = ∏_{μ' ≠ μ} (X - μ')^{m_μ'}` there
are polynomials `g_μ` with `Σ_μ g_μ f_μ = 1`. The spectral idempotent of `K` at `μ` is
`P_μ = (g_μ f_μ)(K)`, the spectral projector (principal idempotent) of `K` at `μ`. The
Cayley–Hamilton theorem gives its properties, and a uniqueness statement shows that it does not
depend on the choice of the `g_μ`. With `R_μ = (K - μ) P_μ`, `K = Σ_μ (μ P_μ + R_μ)` and
`R_μ^p = (K - μ)^p P_μ` for `p ≥ 1`: the decomposition of Tjoa–Cirac, (D1)–(D2). That `P_μ` is the
projector onto the generalized eigenspace of `μ` along the others, and that its rank is `m_μ`, is
standard and not formalized here.

## Main definitions

* `BosonicLean.eigs K`: the eigenvalues of `K`, the roots of its characteristic polynomial.
* `BosonicLean.algMult K μ`: the algebraic multiplicity of `μ`.
* `BosonicLean.spectralIdempotent K μ`: `P_μ`, and `0` when `μ` is not an eigenvalue.
* `BosonicLean.componentMatrix K μ p`: `X_{μ,p} = (K - μ)^p P_μ / p!`, zero for `p ≥ m_μ`.

## Main results

* `BosonicLean.sum_algMult`: `Σ_μ m_μ` is the size of `K`.
* `BosonicLean.sum_spectralIdempotent`: `Σ_μ P_μ = 1`.
* `BosonicLean.spectralIdempotent_mul_self`, `BosonicLean.spectralIdempotent_mul_of_ne`:
  orthogonal idempotents.
* `BosonicLean.commute_spectralIdempotent`: `K P_μ = P_μ K`.
* `BosonicLean.sub_pow_algMult_mul_spectralIdempotent`: `(K - μ)^{m_μ} P_μ = 0`.
* `BosonicLean.eq_spectralIdempotent`: any family `E` with `Σ_μ E_μ = 1` and
  `(K - μ)^{m_μ} E_μ = 0` is the family of spectral idempotents.
* `BosonicLean.sum_smul_add_sub_mul_spectralIdempotent`: `K = Σ_μ (μ P_μ + (K - μ) P_μ)`.
-/

open Polynomial Finset Function

namespace BosonicLean

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜] [IsAlgClosed 𝕜] [DecidableEq 𝕜]

/-- The eigenvalues of a square matrix: the roots of its characteristic polynomial. -/
noncomputable def eigs (K : Matrix n n 𝕜) : Finset 𝕜 := K.charpoly.roots.toFinset

/-- The algebraic multiplicity of `μ` as an eigenvalue of `K`: its multiplicity as a root of the
characteristic polynomial (`0` if `μ` is not an eigenvalue). -/
noncomputable def algMult (K : Matrix n n 𝕜) (μ : 𝕜) : ℕ := K.charpoly.rootMultiplicity μ

/-- The factor `(X - μ)^{m_μ}` of the characteristic polynomial. -/
noncomputable def eigFactor (K : Matrix n n 𝕜) (μ : 𝕜) : 𝕜[X] := (X - C μ) ^ algMult K μ

omit [IsAlgClosed 𝕜] in
/-- The eigenvalues are the points of the spectrum. -/
theorem mem_eigs {K : Matrix n n 𝕜} {μ : 𝕜} : μ ∈ eigs K ↔ μ ∈ spectrum 𝕜 K := by
  rw [eigs, Multiset.mem_toFinset, Matrix.mem_spectrum_iff_isRoot_charpoly,
    mem_roots (Matrix.charpoly_monic K).ne_zero]

/-- The characteristic polynomial is the product of its factors `(X - μ)^{m_μ}`. -/
theorem prod_eigFactor (K : Matrix n n 𝕜) : ∏ μ ∈ eigs K, eigFactor K μ = K.charpoly := by
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic K)
    IsAlgClosed.card_roots_eq_natDegree
  rw [← h, Finset.prod_multiset_map_count]
  refine prod_congr rfl fun μ _ => ?_
  rw [eigFactor, algMult, count_roots]

/-- The algebraic multiplicities add up to the size of the matrix. -/
theorem sum_algMult (K : Matrix n n 𝕜) : ∑ μ ∈ eigs K, algMult K μ = Fintype.card n := by
  rw [eigs]
  simp_rw [algMult, ← count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    Matrix.charpoly_natDegree_eq_dim]

omit [IsAlgClosed 𝕜] in
/-- Every eigenvalue has positive algebraic multiplicity. -/
theorem algMult_pos {K : Matrix n n 𝕜} {μ : 𝕜} (h : μ ∈ eigs K) : 0 < algMult K μ := by
  rw [eigs, Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic K).ne_zero] at h
  exact (rootMultiplicity_pos (Matrix.charpoly_monic K).ne_zero).mpr h

/-- The number of eigenvalues is at most the size of the matrix. -/
theorem card_eigs_le (K : Matrix n n 𝕜) : (eigs K).card ≤ Fintype.card n := by
  rw [← sum_algMult K]
  simpa using card_nsmul_le_sum (eigs K) (algMult K) 1 fun μ hμ => algMult_pos hμ

/-- A nonempty matrix has an eigenvalue. -/
theorem eigs_nonempty (K : Matrix n n 𝕜) (h : 0 < Fintype.card n) : (eigs K).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have := sum_algMult K
  rw [he, sum_empty] at this
  omega

omit [IsAlgClosed 𝕜] in
/-- The factors `(X - μ)^{m_μ}` for distinct eigenvalues are pairwise coprime. -/
theorem pairwise_isCoprime_eigFactor (K : Matrix n n 𝕜) :
    Pairwise (IsCoprime on fun μ : eigs K => eigFactor K μ) := by
  intro μ ν h
  refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
  exact (sub_ne_zero.mpr fun e => h (Subtype.ext e)).isUnit

/-- Polynomials `g_μ` with `Σ_μ g_μ f_μ = 1`, `f_μ = ∏_{μ' ≠ μ} (X - μ')^{m_μ'}` (a choice), for a
matrix with at least one eigenvalue; `0` for the empty matrix, where no such family exists. Its
values off the spectrum are never used. It is the generic `bezoutCoeffOf` for the eigenvalues with
their algebraic multiplicities (B4.1 Step 0). -/
noncomputable def bezoutCoeff (K : Matrix n n 𝕜) : 𝕜 → 𝕜[X] := bezoutCoeffOf (eigs K) (algMult K)

omit [IsAlgClosed 𝕜] in
/-- The partition of unity `Σ_μ g_μ f_μ = 1`, when `K` has an eigenvalue. -/
theorem sum_bezoutCoeff_mul (K : Matrix n n 𝕜) (h : (eigs K).Nonempty) :
    ∑ μ ∈ eigs K, bezoutCoeff K μ * ∏ ν ∈ eigs K \ {μ}, eigFactor K ν = 1 :=
  sum_bezoutCoeffOf_mul (algMult K) h

/-- The **spectral idempotent** `P_μ = (g_μ f_μ)(K)` of `K` at `μ`; `0` if `μ` is not an
eigenvalue. -/
noncomputable def spectralIdempotent (K : Matrix n n 𝕜) (μ : 𝕜) : Matrix n n 𝕜 :=
  if μ ∈ eigs K then aeval K (bezoutCoeff K μ * ∏ ν ∈ eigs K \ {μ}, eigFactor K ν) else 0

omit [IsAlgClosed 𝕜] in
/-- `P_μ = 0` off the spectrum. -/
theorem spectralIdempotent_of_not_mem (K : Matrix n n 𝕜) {μ : 𝕜} (h : μ ∉ eigs K) :
    spectralIdempotent K μ = 0 := by
  simp [spectralIdempotent, h]

omit [IsAlgClosed 𝕜] in
/-- `P_μ = (g_μ f_μ)(K)` on the spectrum. -/
theorem spectralIdempotent_of_mem (K : Matrix n n 𝕜) {μ : 𝕜} (h : μ ∈ eigs K) :
    spectralIdempotent K μ =
      aeval K (bezoutCoeff K μ * ∏ ν ∈ eigs K \ {μ}, eigFactor K ν) := by
  simp [spectralIdempotent, h]

omit [IsAlgClosed 𝕜] [DecidableEq 𝕜] in
/-- `(X - μ)^{m_μ}` evaluated at `K` is `(K - μ)^{m_μ}`. -/
theorem aeval_eigFactor (K : Matrix n n 𝕜) (μ : 𝕜) :
    aeval K (eigFactor K μ) = (K - μ • 1) ^ algMult K μ := by
  rw [eigFactor, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

omit [IsAlgClosed 𝕜] [DecidableEq 𝕜] in
/-- Every polynomial in `K` commutes with `K`. -/
theorem commute_aeval (K : Matrix n n 𝕜) (p : 𝕜[X]) : Commute K (aeval K p) := by
  have h : aeval K (X * p) = aeval K (p * X) := by rw [mul_comm]
  rw [map_mul, map_mul, aeval_X] at h
  exact h

/-- `f_μ (X - μ)^{m_μ} = χ`. -/
theorem prod_sdiff_mul_eigFactor (K : Matrix n n 𝕜) {μ : 𝕜} (h : μ ∈ eigs K) :
    (∏ ν ∈ eigs K \ {μ}, eigFactor K ν) * eigFactor K μ = K.charpoly := by
  rw [sdiff_singleton_eq_erase, mul_comm, mul_prod_erase _ _ h, prod_eigFactor]

omit [IsAlgClosed 𝕜] in
/-- For `μ' ≠ μ`, `f_μ` has the factor `(X - μ')^{m_μ'}`. -/
theorem prod_sdiff_eq_mul (K : Matrix n n 𝕜) {μ μ' : 𝕜} (h' : μ' ∈ eigs K) (hne : μ' ≠ μ) :
    ∏ ν ∈ eigs K \ {μ}, eigFactor K ν =
      (∏ ν ∈ (eigs K \ {μ}).erase μ', eigFactor K ν) * eigFactor K μ' := by
  rw [mul_comm, mul_prod_erase _ _ (by simp [h', hne])]

/-- `Σ_μ P_μ = 1`. -/
theorem sum_spectralIdempotent (K : Matrix n n 𝕜) :
    ∑ μ ∈ eigs K, spectralIdempotent K μ = 1 := by
  rcases (eigs K).eq_empty_or_nonempty with h | h
  · have : IsEmpty n := by
      rw [← Fintype.card_eq_zero_iff, ← sum_algMult K, h, sum_empty]
    rw [h, sum_empty]
    exact Subsingleton.elim _ _
  · rw [sum_congr rfl fun μ hμ => spectralIdempotent_of_mem K hμ, ← map_sum,
      sum_bezoutCoeff_mul K h, map_one]

/-- `(K - μ)^{m_μ} P_μ = 0`. -/
theorem sub_pow_algMult_mul_spectralIdempotent (K : Matrix n n 𝕜) (μ : 𝕜) :
    (K - μ • 1) ^ algMult K μ * spectralIdempotent K μ = 0 := by
  by_cases hμ : μ ∈ eigs K
  · rw [spectralIdempotent_of_mem K hμ, ← aeval_eigFactor, ← map_mul, mul_left_comm,
      mul_comm (eigFactor K μ), prod_sdiff_mul_eigFactor K hμ, map_mul,
      Matrix.aeval_self_charpoly, mul_zero]
  · rw [spectralIdempotent_of_not_mem K hμ, mul_zero]

omit [IsAlgClosed 𝕜]  in
/-- `K P_μ = P_μ K`. -/
theorem commute_spectralIdempotent (K : Matrix n n 𝕜) (μ : 𝕜) :
    Commute K (spectralIdempotent K μ) := by
  by_cases hμ : μ ∈ eigs K
  · rw [spectralIdempotent_of_mem K hμ]
    exact commute_aeval K _
  · rw [spectralIdempotent_of_not_mem K hμ]
    exact Commute.zero_right K

omit [IsAlgClosed 𝕜] in
/-- If `(K - μ')^{m_μ'} E = 0` for an eigenvalue `μ' ≠ μ`, then `P_μ E = 0`. -/
theorem spectralIdempotent_mul_eq_zero (K : Matrix n n 𝕜) {μ μ' : 𝕜} (hne : μ' ≠ μ)
    (h' : μ' ∈ eigs K) {E : Matrix n n 𝕜} (hE : (K - μ' • 1) ^ algMult K μ' * E = 0) :
    spectralIdempotent K μ * E = 0 := by
  by_cases hμ : μ ∈ eigs K
  · rw [spectralIdempotent_of_mem K hμ, prod_sdiff_eq_mul K h' hne, ← mul_assoc, map_mul,
      aeval_eigFactor, mul_assoc, hE, mul_zero]
  · rw [spectralIdempotent_of_not_mem K hμ, zero_mul]

/-- `P_μ P_μ' = 0` for `μ ≠ μ'`. -/
theorem spectralIdempotent_mul_of_ne (K : Matrix n n 𝕜) {μ μ' : 𝕜} (h : μ ≠ μ') :
    spectralIdempotent K μ * spectralIdempotent K μ' = 0 := by
  by_cases h' : μ' ∈ eigs K
  · exact spectralIdempotent_mul_eq_zero K (Ne.symm h) h'
      (sub_pow_algMult_mul_spectralIdempotent K μ')
  · rw [spectralIdempotent_of_not_mem K h', mul_zero]

/-- `P_μ² = P_μ`. -/
theorem spectralIdempotent_mul_self (K : Matrix n n 𝕜) (μ : 𝕜) :
    spectralIdempotent K μ * spectralIdempotent K μ = spectralIdempotent K μ := by
  by_cases hμ : μ ∈ eigs K
  · conv_rhs => rw [← mul_one (spectralIdempotent K μ), ← sum_spectralIdempotent K, mul_sum]
    rw [sum_eq_single μ (fun ν _ hν => spectralIdempotent_mul_of_ne K (Ne.symm hν))
      (fun h => absurd hμ h)]
  · rw [spectralIdempotent_of_not_mem K hμ, mul_zero]

/-- **Uniqueness of the spectral idempotents.** A family `E` with `Σ_μ E_μ = 1` and
`(K - μ)^{m_μ} E_μ = 0` for every eigenvalue `μ` is the family of spectral idempotents. -/
theorem eq_spectralIdempotent (K : Matrix n n 𝕜) (E : 𝕜 → Matrix n n 𝕜)
    (hsum : ∑ μ ∈ eigs K, E μ = 1) (hnil : ∀ μ ∈ eigs K, (K - μ • 1) ^ algMult K μ * E μ = 0)
    {μ : 𝕜} (hμ : μ ∈ eigs K) : E μ = spectralIdempotent K μ := by
  have h1 : spectralIdempotent K μ = spectralIdempotent K μ * E μ := by
    conv_lhs => rw [← mul_one (spectralIdempotent K μ), ← hsum, mul_sum]
    exact sum_eq_single μ (fun ν hν hne => spectralIdempotent_mul_eq_zero K hne hν (hnil ν hν))
      (fun h => absurd hμ h)
  have h2 : E μ = spectralIdempotent K μ * E μ := by
    conv_lhs => rw [← one_mul (E μ), ← sum_spectralIdempotent K, sum_mul]
    exact sum_eq_single μ (fun ν _ hne => spectralIdempotent_mul_eq_zero K (Ne.symm hne) hμ
      (hnil μ hμ)) (fun h => absurd hμ h)
  rw [h2, ← h1]

omit [IsAlgClosed 𝕜] in
/-- The algebraic multiplicity is `0` off the spectrum. -/
theorem algMult_eq_zero_of_not_mem {K : Matrix n n 𝕜} {μ : 𝕜} (h : μ ∉ eigs K) :
    algMult K μ = 0 := by
  rw [eigs, Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic K).ne_zero] at h
  exact rootMultiplicity_eq_zero h

/-- **The decomposition** `K = Σ_μ (μ P_μ + (K - μ) P_μ)` (Tjoa–Cirac, (D1)). -/
theorem sum_smul_add_sub_mul_spectralIdempotent (K : Matrix n n 𝕜) :
    ∑ μ ∈ eigs K, (μ • spectralIdempotent K μ + (K - μ • 1) * spectralIdempotent K μ) = K := by
  have h : ∀ μ, μ • spectralIdempotent K μ + (K - μ • 1) * spectralIdempotent K μ =
      K * spectralIdempotent K μ := fun μ => by
    rw [sub_mul, smul_mul_assoc, one_mul, add_sub_cancel]
  rw [sum_congr rfl fun μ _ => h μ, ← mul_sum, sum_spectralIdempotent, mul_one]

/-- The powers of the nilpotent part: `((K - μ) P_μ)^p = (K - μ)^p P_μ` for `p ≥ 1`
(Tjoa–Cirac, (D2)). -/
theorem sub_mul_spectralIdempotent_pow (K : Matrix n n 𝕜) (μ : 𝕜) {p : ℕ} (hp : 1 ≤ p) :
    ((K - μ • 1) * spectralIdempotent K μ) ^ p = (K - μ • 1) ^ p * spectralIdempotent K μ := by
  have hc : Commute (K - μ • 1) (spectralIdempotent K μ) :=
    (commute_spectralIdempotent K μ).sub_left ((Commute.one_left _).smul_left μ)
  rw [hc.mul_pow]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  induction q with
  | zero => rw [zero_add, pow_one]
  | succ q ih => rw [pow_succ, ih (by omega), spectralIdempotent_mul_self]

omit [IsAlgClosed 𝕜] in
/-- The spectral idempotent is the generic idempotent polynomial of the eigenvalues, with their
algebraic multiplicities, evaluated at `K`. -/
theorem spectralIdempotent_eq_aeval_idempotentPoly (K : Matrix n n 𝕜) (μ : 𝕜) :
    spectralIdempotent K μ = aeval K (idempotentPoly (eigs K) (algMult K) μ) := by
  unfold spectralIdempotent idempotentPoly
  split_ifs <;> simp [bezoutCoeff, eigFactor, pointFactor]

/-- **Any idempotent polynomials give the spectral idempotents.** If `(X - ν)^{m_ν}` divides
`P_μ - δ_μν` for all eigenvalues `μ, ν`, then `P_μ(K)` is the spectral idempotent at `μ`, whatever
the choice of `P`. -/
theorem aeval_eq_spectralIdempotent (K : Matrix n n 𝕜) {P : 𝕜 → 𝕜[X]}
    (hP : ∀ μ ∈ eigs K, ∀ ν ∈ eigs K, eigFactor K ν ∣ P μ - if μ = ν then 1 else 0) {μ : 𝕜}
    (hμ : μ ∈ eigs K) : aeval K (P μ) = spectralIdempotent K μ := by
  have h : ∀ ν ∈ eigs K, aeval K (P μ) * spectralIdempotent K ν =
      if μ = ν then spectralIdempotent K ν else 0 := by
    intro ν hν
    obtain ⟨g, hg⟩ := hP μ hμ ν hν
    have e : P μ = (if μ = ν then 1 else 0) + g * eigFactor K ν := by
      rw [mul_comm g, ← hg]
      ring
    rw [e, map_add, map_mul, add_mul, mul_assoc, aeval_eigFactor,
      sub_pow_algMult_mul_spectralIdempotent, mul_zero, add_zero]
    split_ifs <;> simp
  calc aeval K (P μ) = aeval K (P μ) * ∑ ν ∈ eigs K, spectralIdempotent K ν := by
        rw [sum_spectralIdempotent, mul_one]
    _ = spectralIdempotent K μ := by
        rw [mul_sum, sum_congr rfl h, sum_ite_eq]
        simp only [hμ, ↓reduceIte]

/-! ### Component matrices -/

section Component

/-- The **component matrix** `X_{μ,p} = (K - μ)^p P_μ / p!` of `K` at `μ` (Lancaster–Tismenetsky):
the coefficients of the expansion of a function of `K` over its eigenvalues. Characteristic zero
makes `p!` invertible for every `p`. -/
noncomputable def componentMatrix [CharZero 𝕜] (K : Matrix n n 𝕜) (μ : 𝕜) (p : ℕ) :
    Matrix n n 𝕜 :=
  ((p.factorial : 𝕜)⁻¹) • ((K - μ • 1) ^ p * spectralIdempotent K μ)

/-- `X_{μ,p} = 0` for `p ≥ m_μ`. -/
theorem componentMatrix_eq_zero [CharZero 𝕜] (K : Matrix n n 𝕜) (μ : 𝕜) {p : ℕ}
    (hp : algMult K μ ≤ p) : componentMatrix K μ p = 0 := by
  rw [componentMatrix, ← Nat.sub_add_cancel hp, pow_add, mul_assoc,
    sub_pow_algMult_mul_spectralIdempotent, mul_zero, smul_zero]

end Component

end BosonicLean
