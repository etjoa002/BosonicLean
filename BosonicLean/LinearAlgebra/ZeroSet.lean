/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The kernel of a parent construction

The abstract parent-Hamiltonian construction of Tjoa–Cirac (Sec. IV B), as linear algebra. Let
`(e_j)_{j ∈ ι}` be finitely many vectors of a space `M`, `Q` a linear map with `ker Q = span e`, and
`(F_j)_{j ∈ ι}` linear maps with `F_j e_l = δ_jl Ω`, `Ω ≠ 0` (extraction maps). For a target
`W = span {ψ_μ = Σ_j C_μj e_j}` and a check matrix `R` with `R Cᵀ = 0` and
`rank R + rank C = |ι|`, the common kernel of `Q` and the check maps `O_α = Σ_j R_αj F_j` is `W`.
On `φ = Σ_j x_j e_j`, `O_α φ = (R x)_α Ω`, and `ker R = range Cᵀ` by the rank condition.

The vectors and the rows of `C` are indexed by arbitrary finite types, so that the many-mode
construction can index local states by words and the rows of `C` by matrix units; the rows of `R`
are `Fin k`.

## Main results

* `BosonicLean.linearIndependent_of_extract`: extraction maps force linear independence.
* `BosonicLean.ker_toLin'_eq_range_toLin'_transpose`: `ker R = range Cᵀ`.
* `BosonicLean.ParentConstruction.zero_set_eq_span`: the kernel is `W`.
-/

open Finset Matrix

namespace BosonicLean

variable {𝕜 M M' P : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] [AddCommGroup M']
  [Module 𝕜 M'] [AddCommGroup P] [Module 𝕜 P]
variable {ι μ : Type*} [DecidableEq ι]

/-- Vectors with extraction maps `F_j e_l = δ_jl Ω`, `Ω ≠ 0`, are linearly independent. -/
theorem linearIndependent_of_extract [Finite ι] (e : ι → M) (F : ι → M →ₗ[𝕜] P) {Ω : P}
    (hΩ : Ω ≠ 0) (hF : ∀ j l, F j (e l) = if j = l then Ω else 0) : LinearIndependent 𝕜 e := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro x hx l
  have h := congrArg (F l) hx
  simp only [map_sum, map_smul, hF, smul_ite, smul_zero, sum_ite_eq, mem_univ, ↓reduceIte,
    map_zero] at h
  exact (smul_eq_zero.mp h).resolve_right hΩ

/-- **`ker R = range Cᵀ`** for `R Cᵀ = 0` and `rank R + rank C = |ι|`. -/
theorem ker_toLin'_eq_range_toLin'_transpose [Fintype ι] [Fintype μ] [DecidableEq μ] {k : ℕ}
    (C : Matrix μ ι 𝕜)
    (R : Matrix (Fin k) ι 𝕜) (hRC : R * Cᵀ = 0) (hrank : R.rank + C.rank = Fintype.card ι) :
    LinearMap.ker (Matrix.toLin' R) = LinearMap.range (Matrix.toLin' Cᵀ) := by
  have hle : LinearMap.range (Matrix.toLin' Cᵀ) ≤ LinearMap.ker (Matrix.toLin' R) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, hRC,
      zero_mulVec]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' R)
  have h2 : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Cᵀ)) = C.rank := by
    rw [← Matrix.rank_transpose C, Matrix.rank, Matrix.toLin'_apply']
  have h3 : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' R)) = R.rank := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  simp only [Module.finrank_fintype_fun_eq_card] at h1
  omega

namespace ParentConstruction

/-- The check maps on a combination: `(Σ_j R_αj F_j)(Σ_l x_l e_l) = (R x)_α Ω`. -/
theorem check_apply_sum [Fintype ι] {k : ℕ} (e : ι → M) (F : ι → M →ₗ[𝕜] P) (Ω : P)
    (hF : ∀ j l, F j (e l) = if j = l then Ω else 0) (R : Matrix (Fin k) ι 𝕜) (α : Fin k)
    (x : ι → 𝕜) : (∑ j, R α j • F j) (∑ l, x l • e l) = (R *ᵥ x) α • Ω := by
  rw [map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hF, smul_ite, smul_zero,
    sum_ite_eq', mem_univ, ↓reduceIte, smul_smul, mulVec, dotProduct, sum_smul]
  exact sum_congr rfl fun l _ => by rw [mul_comm]

/-- **The kernel of a parent construction** (Tjoa–Cirac, Sec. IV B, (61)–(72)). With
`ker Q = span e`, extraction maps `F_j e_l = δ_jl Ω`, `Ω ≠ 0`, and a check matrix `R` with
`R Cᵀ = 0` and `rank R + rank C = |ι|`: `Q φ = 0` and `(Σ_j R_αj F_j) φ = 0` for every `α` if and
only if `φ ∈ span {Σ_j C_μj e_j}`. -/
theorem zero_set_eq_span [Fintype ι] [Finite μ] {k : ℕ} (e : ι → M) (C : Matrix μ ι 𝕜)
    (R : Matrix (Fin k) ι 𝕜) (hRC : R * Cᵀ = 0) (hrank : R.rank + C.rank = Fintype.card ι)
    (Q : M →ₗ[𝕜] M') (hQ : LinearMap.ker Q = Submodule.span 𝕜 (Set.range e))
    (F : ι → M →ₗ[𝕜] P) {Ω : P} (hΩ : Ω ≠ 0)
    (hF : ∀ j l, F j (e l) = if j = l then Ω else 0) (φ : M) :
    (Q φ = 0 ∧ ∀ α, (∑ j, R α j • F j) φ = 0) ↔
      φ ∈ Submodule.span 𝕜 (Set.range fun ν => ∑ j, C ν j • e j) := by
  have := Fintype.ofFinite μ
  classical
  have hker := ker_toLin'_eq_range_toLin'_transpose C R hRC hrank
  -- `Σ_ν y_ν ψ_ν = Σ_l (Cᵀ y)_l e_l`
  have hcomb : ∀ y : μ → 𝕜, ∑ ν, y ν • ∑ j, C ν j • e j = ∑ l, (Cᵀ *ᵥ y) l • e l := by
    intro y
    simp only [smul_sum, smul_smul, mulVec, dotProduct, transpose_apply, sum_smul]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => sum_congr rfl fun ν _ => ?_
    rw [mul_comm]
  constructor
  · rintro ⟨hQφ, hO⟩
    have hφ : φ ∈ Submodule.span 𝕜 (Set.range e) := hQ ▸ hQφ
    obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hφ
    have hRx : x ∈ LinearMap.ker (Matrix.toLin' R) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      funext α
      have h := hO α
      rw [check_apply_sum e F Ω hF R α x] at h
      exact (smul_eq_zero.mp h).resolve_right hΩ
    rw [hker] at hRx
    obtain ⟨y, hy⟩ := hRx
    rw [Matrix.toLin'_apply] at hy
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨y, by rw [hcomb, hy]⟩
  · intro hφ
    rw [Submodule.mem_span_range_iff_exists_fun] at hφ
    obtain ⟨y, rfl⟩ := hφ
    rw [hcomb]
    refine ⟨?_, fun α => ?_⟩
    · rw [← LinearMap.mem_ker, hQ]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [check_apply_sum e F Ω hF R α, mulVec_mulVec, hRC, zero_mulVec, Pi.zero_apply, zero_smul]

end ParentConstruction

end BosonicLean
