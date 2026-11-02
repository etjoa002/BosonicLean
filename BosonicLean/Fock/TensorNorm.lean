/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Analysis.TsumPiProd
import BosonicLean.Fock.SqNorm
import BosonicLean.Fock.TensorProduct

/-!
# The squared norm of a product vector

The squared norm of a product vector `⊗ⱼ φⱼ` on finitely many modes is the product of the squared
norms of its factors, `‖⊗ⱼ φⱼ‖² = ∏ⱼ ‖φⱼ‖²`, as an identity in `[0, ∞]`. No summability is
needed: both sides may be infinite. The proof rests on the exchange of a sum over the functions
`ι → α` on a finite type with a product over `ι`, also in `[0, ∞]` (`ENNReal.tsum_pi_prod`). In
particular, a product of square-summable vectors is square-summable.

## Main results

* `BosonicLean.Fock.FormalFock.sqNorm_tensorVec`: `‖⊗ⱼ φⱼ‖² = ∏ⱼ ‖φⱼ‖²`.
* `BosonicLean.Fock.FormalFock.sqNorm_tensorVec_lt_top`: a product of square-summable vectors is
  square-summable.
-/

open scoped ENNReal

namespace BosonicLean.Fock.FormalFock

variable {ι : Type*}

/-- The squared norm of a single-mode vector, with the coefficients indexed by `ℕ`. -/
theorem sqNorm_eq_tsum_single (ψ : FormalFock Unit ℂ) :
    sqNorm ψ = ∑' m : ℕ, (‖ψ.coeff (Finsupp.single () m)‖₊ : ℝ≥0∞) ^ 2 := by
  rw [sqNorm, ← (Finsupp.uniqueEquiv ()).symm.tsum_eq]
  rfl

/-- The squared norm of a product vector is the product of the squared norms. -/
theorem sqNorm_tensorVec [Fintype ι] (φ : ι → FormalFock Unit ℂ) :
    sqNorm (tensorVec φ) = ∏ j, sqNorm (φ j) := by
  rw [sqNorm, ← Finsupp.equivFunOnFinite.symm.tsum_eq]
  simp only [sqNorm_eq_tsum_single, ← ENNReal.tsum_pi_prod]
  congr 1
  funext m
  rw [coeff_tensorVec, nnnorm_prod, ENNReal.ofNNReal_finsetProd, ← Finset.prod_pow]
  rfl

/-- A product of square-summable vectors on finitely many modes is square-summable. -/
theorem sqNorm_tensorVec_lt_top [Fintype ι] {φ : ι → FormalFock Unit ℂ}
    (h : ∀ j, sqNorm (φ j) < ∞) : sqNorm (tensorVec φ) < ∞ := by
  rw [sqNorm_tensorVec]
  exact ENNReal.prod_lt_top fun j _ => h j

end BosonicLean.Fock.FormalFock
