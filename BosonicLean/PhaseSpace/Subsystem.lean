/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.Defs

/-!
# Covariance restriction to selected modes

Selecting matching position and momentum coordinates of distinct modes preserves
the covariance uncertainty condition.
-/

open scoped ComplexOrder
open Matrix

namespace Gaussian

/-- Restricting a covariance to selected distinct modes preserves admissibility. -/
theorem isAdmissible_subsystem {m n : ℕ}
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    {e : Fin m → Fin n} (hγ : IsAdmissible γ) (he : Function.Injective e) :
    IsAdmissible (γ.submatrix (Sum.map e e) (Sum.map e e)) := by
  have hΩ : (symplecticForm n).submatrix (Sum.map e e) (Sum.map e e) =
      symplecticForm m := by
    ext i j
    cases i <;> cases j <;>
      simp [symplecticForm, Matrix.J, Matrix.fromBlocks, Matrix.submatrix,
        Matrix.one_apply, he.eq_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    exact congrFun (congrFun hγ.1 ((Sum.map e e) i)) ((Sum.map e e) j)
  · have hpos := hγ.2.submatrix (Sum.map e e)
    simpa only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
      Matrix.submatrix_map,
      hΩ] using hpos

end Gaussian
