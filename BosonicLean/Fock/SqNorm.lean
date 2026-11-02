/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.Formal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The squared norm of a formal vector

For a vector `ψ` of the formal Fock space with complex coefficients, `‖ψ‖² = Σₙ |ψ(n)|²` with values
in `[0, ∞]`. It is defined for every formal vector, finite exactly on the vectors of Fock space
(square-summable coefficients), where it is the squared Hilbert norm, and it vanishes only at `0`.
Quadratic forms built from it, such as `‖Q φ‖² + Σ_α ‖O_α φ‖²`, are defined on the whole formal Fock
space and need no domain of definition.

## Main definitions

* `BosonicLean.Fock.FormalFock.sqNorm ψ`: `Σₙ |ψ(n)|² ∈ [0, ∞]`.

## Main results

* `BosonicLean.Fock.FormalFock.sqNorm_eq_zero_iff`: `‖ψ‖² = 0 ↔ ψ = 0`.
* `BosonicLean.Fock.FormalFock.sqNorm_lt_top_iff`, `BosonicLean.Fock.FormalFock.sqNorm_eq_ofReal`:
  finite exactly for square-summable coefficients, where it is `Σₙ |ψ(n)|²`.
* `BosonicLean.Fock.FormalFock.sqNorm_single`: `‖c ∣m⟩‖² = |c|²`.
-/

open scoped ENNReal

namespace BosonicLean.Fock.FormalFock

variable {ι : Type*}

/-- The squared norm `‖ψ‖² = Σₙ |ψ(n)|²` of a formal vector, with values in `[0, ∞]`. -/
noncomputable def sqNorm (ψ : FormalFock ι ℂ) : ℝ≥0∞ :=
  ∑' n, (‖ψ.coeff n‖₊ : ℝ≥0∞) ^ 2

/-- `‖ψ‖² = 0` exactly for `ψ = 0`. -/
theorem sqNorm_eq_zero_iff (ψ : FormalFock ι ℂ) : sqNorm ψ = 0 ↔ ψ = 0 := by
  rw [sqNorm, ENNReal.tsum_eq_zero]
  constructor
  · intro h
    apply coeff_injective
    funext n
    have := h n
    simpa using this
  · rintro rfl n
    simp [coeff_zero]

/-- `‖ψ‖²` is finite exactly when the coefficients are square-summable. -/
theorem sqNorm_lt_top_iff (ψ : FormalFock ι ℂ) :
    sqNorm ψ < ∞ ↔ Summable fun n => ‖ψ.coeff n‖ ^ 2 := by
  have h : sqNorm ψ = ∑' n, ((‖ψ.coeff n‖₊ ^ 2 : NNReal) : ℝ≥0∞) := by
    simp [sqNorm, ENNReal.coe_pow]
  rw [h, lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp

/-- On square-summable coefficients, `‖ψ‖²` is the squared Hilbert norm `Σₙ |ψ(n)|²`. -/
theorem sqNorm_eq_ofReal {ψ : FormalFock ι ℂ} (h : Summable fun n => ‖ψ.coeff n‖ ^ 2) :
    sqNorm ψ = ENNReal.ofReal (∑' n, ‖ψ.coeff n‖ ^ 2) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h, sqNorm]
  congr 1
  funext n
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- The squared norm of `c ∣m⟩` is `|c|²`. -/
theorem sqNorm_single [DecidableEq ι] (m : ι →₀ ℕ) (c : ℂ) :
    sqNorm (single m c) = (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  rw [sqNorm, tsum_eq_single m fun n hn => by simp [hn]]
  simp

end BosonicLean.Fock.FormalFock
