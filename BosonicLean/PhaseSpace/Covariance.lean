/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.Defs

/-!
# Symplectic covariance congruence

Canonical linear coordinate changes preserve the covariance uncertainty condition.
The conventions are those of Schuch, Wolf and Cirac, arXiv:1201.3945v1, Section 2.
-/

open scoped ComplexOrder
open Matrix

namespace Gaussian

/-- A real symplectic coordinate change preserves admissibility of a covariance. -/
theorem isAdmissible_symplecticCongruence {n : ℕ}
    {γ S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : IsAdmissible γ)
    (hS : S * symplecticForm n * S.transpose = symplecticForm n) :
    IsAdmissible (S * γ * S.transpose) := by
  refine ⟨?_, ?_⟩
  · simp only [transpose_mul, transpose_transpose, hγ.1, Matrix.mul_assoc]
  · have hpos := hγ.2.mul_mul_conjTranspose_same (S.map Complex.ofReal)
    have hstar : (S.map Complex.ofReal).conjTranspose =
        S.transpose.map Complex.ofReal := by
      ext i j
      simp
    have hmap (A B : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
        (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
      exact Matrix.map_mul (f := Complex.ofRealHom)
    rw [hstar, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← hmap, ← hmap, ← hmap, ← hmap, hS] at hpos
    exact hpos

end Gaussian
