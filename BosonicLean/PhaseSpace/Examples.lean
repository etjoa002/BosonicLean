/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.ConstructionDefs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! One-mode diagonal admissibility and vacuum, squeezed and inadmissible examples. -/

open scoped ComplexOrder
open Matrix

namespace Gaussian

private def uncertaintyOne (a b : ℝ) : Matrix (PhaseIndex 1) (PhaseIndex 1) ℂ :=
  (diagonalOne a b).map Complex.ofReal -
    Complex.I • (symplecticForm 1).map Complex.ofReal

private lemma quadratic_one (a b : ℝ) (x : PhaseIndex 1 → ℂ) :
    star x ⬝ᵥ (uncertaintyOne a b *ᵥ x) =
      ⟨a * ((x (Sum.inl 0)).re ^ 2 + (x (Sum.inl 0)).im ^ 2) +
        b * ((x (Sum.inr 0)).re ^ 2 + (x (Sum.inr 0)).im ^ 2) +
        2 * ((x (Sum.inl 0)).re * (x (Sum.inr 0)).im -
          (x (Sum.inl 0)).im * (x (Sum.inr 0)).re), 0⟩ := by
  apply Complex.ext <;>
    simp [uncertaintyOne, diagonalOne, symplecticForm, Matrix.J, Matrix.fromBlocks,
      Matrix.diagonal, Matrix.one_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im] <;> ring_nf

private lemma uncertaintyOne_hermitian (a b : ℝ) : (uncertaintyOne a b).IsHermitian := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [uncertaintyOne, diagonalOne, symplecticForm, Matrix.J, Matrix.fromBlocks,
      Matrix.diagonal, Matrix.conjTranspose]

/-- A diagonal one-mode covariance satisfies exactly the scalar uncertainty bound. -/
theorem isAdmissible_diagonalOne_iff (a b : ℝ) :
    IsAdmissible (diagonalOne a b) ↔ 0 < a ∧ 1 ≤ a * b := by
  constructor
  · rintro ⟨_, h⟩
    change (uncertaintyOne a b).PosSemidef at h
    have hq (z w : ℂ) :
        0 ≤ a * (z.re ^ 2 + z.im ^ 2) + b * (w.re ^ 2 + w.im ^ 2) +
          2 * (z.re * w.im - z.im * w.re) := by
      have hh := h.dotProduct_mulVec_nonneg (Sum.elim (fun _ => z) (fun _ => w))
      rw [quadratic_one] at hh
      simpa [Complex.nonneg_iff] using hh
    have ha : 0 ≤ a := by simpa using hq 1 0
    have hb : 0 ≤ b := by simpa using hq 0 1
    have hapos : 0 < a := by
      by_contra hn
      have hz : a = 0 := le_antisymm (le_of_not_gt hn) ha
      have hh := hq (b + 1) (-Complex.I)
      simp [hz] at hh
      linarith
    refine ⟨hapos, ?_⟩
    have hh := hq Complex.I a
    simp at hh
    nlinarith
  · rintro ⟨ha, hab⟩
    refine ⟨?_, ?_⟩
    · ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        fin_cases i <;> fin_cases j <;> simp [diagonalOne, Matrix.diagonal]
    · change (uncertaintyOne a b).PosSemidef
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (uncertaintyOne_hermitian a b)
      intro x
      rw [quadratic_one, Complex.nonneg_iff]
      simp only [and_true]
      let z := x (Sum.inl 0)
      let w := x (Sum.inr 0)
      change 0 ≤ a * (z.re ^ 2 + z.im ^ 2) + b * (w.re ^ 2 + w.im ^ 2) +
        2 * (z.re * w.im - z.im * w.re)
      have hn : 0 ≤ (a * z.re + w.im) ^ 2 + (a * z.im - w.re) ^ 2 +
          (a * b - 1) * (w.re ^ 2 + w.im ^ 2) :=
        add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
          (mul_nonneg (sub_nonneg.mpr hab) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      have hm : 0 ≤ a * (a * (z.re ^ 2 + z.im ^ 2) + b * (w.re ^ 2 + w.im ^ 2) +
          2 * (z.re * w.im - z.im * w.re)) := by nlinarith only [hn]
      exact nonneg_of_mul_nonneg_right hm ha

/-- The one-mode vacuum covariance is admissible. -/
theorem isAdmissible_vacuumOne : IsAdmissible (diagonalOne 1 1) := by
  rw [isAdmissible_diagonalOne_iff]
  norm_num

/-- Reciprocal positive diagonal entries give an admissible squeezed covariance. -/
theorem isAdmissible_squeezedOne {t : ℝ} (ht : 0 < t) :
    IsAdmissible (diagonalOne t t⁻¹) := by
  exact (isAdmissible_diagonalOne_iff t t⁻¹).2 ⟨ht, by simp [ne_of_gt ht]⟩

/-- A covariance smaller than the vacuum in both quadratures violates uncertainty. -/
theorem not_isAdmissible_smallOne {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ¬ IsAdmissible (diagonalOne c c) := by
  intro h
  have hh := (isAdmissible_diagonalOne_iff c c).1 h
  have hp : 0 < (1 - c) * (1 + c) :=
    mul_pos (sub_pos.mpr hc1) (by linarith only [hc])
  nlinarith

end Gaussian
