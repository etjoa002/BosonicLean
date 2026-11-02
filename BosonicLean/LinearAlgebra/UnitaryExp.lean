/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Unitary matrices are exponentials of Hermitian ones

Every unitary matrix `𝒰` is `e^{iM}` for a Hermitian matrix `M`, and `e^{iM}` is unitary for every
Hermitian `M`. A unitary matrix is normal, so the continuous functional calculus applies to it; its
spectrum is a finite subset of the unit circle, on which every function is continuous, and
`M = arg(𝒰)` (the principal argument applied to `𝒰`) is Hermitian with `e^{iM} = 𝒰`. The matrix
exponential is Mathlib's `NormedSpace.exp`, the sum of the exponential series; the norm used for
the functional calculus is the operator norm on `ℓ²`, which induces the usual topology of matrices.

## Main results

* `BosonicLean.exists_isHermitian_exp_eq`: every unitary matrix is `e^{iM}` with `M` Hermitian.
* `BosonicLean.exp_I_smul_mem_unitaryGroup`: `e^{iM}` is unitary for Hermitian `M`.
-/

open Complex NormedSpace

namespace BosonicLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
/-- **Every unitary matrix is `e^{iM}` with `M` Hermitian**: one may take `M = arg(𝒰)`, the
principal argument applied to `𝒰` through the continuous functional calculus. -/
theorem exists_isHermitian_exp_eq (U : Matrix.unitaryGroup ι ℂ) :
    ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧ exp (I • M) = (U : Matrix ι ι ℂ) := by
  refine ⟨cfc (fun z : ℂ => (z.arg : ℂ)) (U : Matrix ι ι ℂ), IsSelfAdjoint.cfc_arg _, ?_⟩
  have hcont : ContinuousOn (fun z : ℂ => (z.arg : ℂ)) (spectrum ℂ (U : Matrix ι ι ℂ)) :=
    (Matrix.finite_spectrum _).continuousOn _
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (U : Matrix ι ι ℂ)]
  refine cfc_congr fun y hy => ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary U.2 hy
  have hy₀ : y ≠ 0 := by rintro rfl; simp at hy₁
  have : (y.arg : ℂ) * I = log y :=
    Complex.ext (by simp [log_re, hy₁]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, mul_comm I, this] using exp_log hy₀

open scoped Matrix.Norms.L2Operator in
/-- `e^{iM}` is unitary for every Hermitian matrix `M`. -/
theorem exp_I_smul_mem_unitaryGroup {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    exp (I • M) ∈ Matrix.unitaryGroup ι ℂ :=
  (selfAdjoint.expUnitary ⟨M, hM⟩).2

end BosonicLean
