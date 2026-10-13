/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SymplecticGroup

/-! Finite-mode covariance conventions.
The covariance normalization is gamma = 2V, where V is the symmetrized covariance.
These matrix definitions do not construct a Gaussian quantum state.
-/

open scoped ComplexOrder

namespace Gaussian

/-- Coordinates ordered as all position coordinates followed by all momenta. -/
abbrev PhaseIndex (n : ℕ) := Fin n ⊕ Fin n

/-- The paper's canonical symplectic form, with the opposite sign to Mathlib's J. -/
def symplecticForm (n : ℕ) : Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  -Matrix.J (Fin n) ℝ

section Identities

open Matrix

/-- `Ωᵀ = −Ω`. -/
theorem transpose_symplecticForm (n : ℕ) : (symplecticForm n)ᵀ = -symplecticForm n := by
  simp [symplecticForm, Matrix.J_transpose]

/-- `Ω² = −1`. -/
theorem symplecticForm_sq (n : ℕ) : symplecticForm n * symplecticForm n = -1 := by
  simp [symplecticForm, Matrix.J_squared]

/-- `ΩΩᵀ = 1`: the symplectic form is orthogonal. -/
theorem symplecticForm_mul_transpose_self (n : ℕ) :
    symplecticForm n * (symplecticForm n)ᵀ = 1 := by
  rw [transpose_symplecticForm, Matrix.mul_neg, symplecticForm_sq, neg_neg]

/-- `ΩᵀΩ = 1`. -/
theorem transpose_symplecticForm_mul_self (n : ℕ) :
    (symplecticForm n)ᵀ * symplecticForm n = 1 := by
  rw [transpose_symplecticForm, Matrix.neg_mul, symplecticForm_sq, neg_neg]

/-- `Ω⁻¹ = −Ω`. -/
theorem symplecticForm_inv (n : ℕ) : (symplecticForm n)⁻¹ = -symplecticForm n :=
  Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, symplecticForm_sq, neg_neg])

end Identities

/-- Real symmetric covariance satisfying the dimensionless uncertainty condition. -/
def IsAdmissible {n : ℕ} (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) : Prop :=
  γ.transpose = γ ∧
    (γ.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef

end Gaussian
