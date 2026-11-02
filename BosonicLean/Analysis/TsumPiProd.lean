/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.Option

/-!
# Sums of products over functions on a finite type, in `[0, ∞]`

For a finite type `ι` and functions `gᵢ : α → [0, ∞]`, the sum over all functions `f : ι → α` of
`∏ᵢ gᵢ(f i)` is the product `∏ᵢ ∑ₐ gᵢ(a)` of the sums. This is the `[0, ∞]` version of
`Finset.prod_univ_sum`: no summability is needed, and both sides may be infinite.

## Main results

* `ENNReal.tsum_pi_prod`: `∑_{f : ι → α} ∏ᵢ gᵢ(f i) = ∏ᵢ ∑ₐ gᵢ(a)` for a finite type `ι`.
-/

open scoped ENNReal

namespace ENNReal

/-- A sum over the functions `f : ι → α` on a finite type of the product `∏ᵢ gᵢ(f i)` is the
product of the sums `∏ᵢ ∑ₐ gᵢ(a)`, in `[0, ∞]`. -/
theorem tsum_pi_prod {ι α : Type*} [Fintype ι] (g : ι → α → ℝ≥0∞) :
    ∑' f : ι → α, ∏ i, g i (f i) = ∏ i, ∑' a, g i a := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ g : ι → α → ℝ≥0∞, ∑' f : ι → α, ∏ i, g i (f i) = ∏ i, ∑' a, g i a)
    ?_ ?_ ?_ ι g
  · intro ι ι' _ e h g
    let _ : Fintype ι := Fintype.ofEquiv ι' e.symm
    rw [← (e.arrowCongr (Equiv.refl α)).tsum_eq]
    have hp (f : ι → α) :
        ∏ i', g i' (e.arrowCongr (Equiv.refl α) f i') = ∏ i, g (e i) (f i) :=
      (Fintype.prod_equiv e _ _ fun i => by simp).symm
    simp only [hp, h]
    exact Fintype.prod_equiv e _ _ fun i => rfl
  · intro g
    simp
  · intro ι _ h g
    rw [← (Equiv.piOptionEquivProd (β := fun _ => α)).symm.tsum_eq, ENNReal.tsum_prod',
      Fintype.prod_option]
    simp only [Equiv.piOptionEquivProd_symm_apply, Fintype.prod_option, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_right, h]

end ENNReal
