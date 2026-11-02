/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear isometries from Gram matrices

Let `x : ι → E` and `x' : ι → F` be families in complex inner product spaces, `F` complete, with
the same Gram matrix, `⟪x i, x j⟫ = ⟪x' i, x' j⟫`. If the span of the `x i` is dense, there is
exactly one linear isometry `T : E → F` with `T (x i) = x' i`. On a finite linear combination
`T (Σ aᵢ xᵢ) = Σ aᵢ x'ᵢ`; the Gram matrices make this well defined and isometric, and Mathlib's
`LinearMap.extendOfIsometry` extends it from the dense span.

This is GA-BMPS milestone B5, part B5.4, Lemma 2: the general form of the extension step of
`BosonicLean.Fock.FockSpace.exists_linearIsometry_of_expVec`.

## Main results

* `BosonicLean.exists_unique_linearIsometry_of_inner_eq`: Lemma 2.
-/

open scoped InnerProductSpace

namespace BosonicLean

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

/-- Two families with the same Gram matrix give linear combinations of the same norm. -/
private theorem norm_linearCombination_eq {x : ι → E} {x' : ι → F}
    (hxx' : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪x' i, x' j⟫_ℂ) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ x' c‖ = ‖Finsupp.linearCombination ℂ x c‖ := by
  have h : ⟪Finsupp.linearCombination ℂ x' c, Finsupp.linearCombination ℂ x' c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ x c, Finsupp.linearCombination ℂ x c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hxx']
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h)

/-- **Lemma 2 (extension of a Gram-preserving map).** If two families have the same Gram matrix
and the first spans a dense subspace, there is exactly one linear isometry mapping the first
family to the second. -/
theorem exists_unique_linearIsometry_of_inner_eq [CompleteSpace F] (x : ι → E) (x' : ι → F)
    (hxx' : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪x' i, x' j⟫_ℂ)
    (hx : Dense (Submodule.span ℂ (Set.range x) : Set E)) :
    ∃! T : E →ₗᵢ[ℂ] F, ∀ i, T (x i) = x' i := by
  have hd : DenseRange (Finsupp.linearCombination ℂ x) := by
    rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact hx
  have hn := norm_linearCombination_eq hxx'
  refine ⟨(Finsupp.linearCombination ℂ x').extendOfIsometry hd hn, fun i => ?_, fun T hT => ?_⟩
  · have := LinearMap.extendOfIsometry_eq (Finsupp.linearCombination ℂ x') hd hn
      (Finsupp.single i 1)
    simpa only [Finsupp.linearCombination_single, one_smul] using this
  · refine (LinearMap.extendOfIsometry_unique _ hd hn T ?_).symm
    refine Finsupp.lhom_ext fun i a => ?_
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single,
      LinearIsometry.coe_toLinearMap, map_smul, hT]

end BosonicLean
