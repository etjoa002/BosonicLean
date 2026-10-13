/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import Mathlib.Analysis.Matrix.Order

/-! Strict positivity of admissible Gaussian covariance matrices. -/

open scoped ComplexOrder Matrix

namespace Gaussian

private lemma map_mulVec_ofReal {n : ℕ}
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (x : PhaseIndex n → ℝ) :
    A.map Complex.ofReal *ᵥ (fun i => (x i : ℂ)) =
      fun i => ((A *ᵥ x) i : ℂ) := by
  funext i
  change (A.map (⇑Complex.ofRealHom) *ᵥ (Complex.ofRealHom ∘ x)) i = _
  exact (RingHom.map_mulVec Complex.ofRealHom A x i).symm

private lemma star_dotProduct_map_mulVec_ofReal {n : ℕ}
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (x : PhaseIndex n → ℝ) :
    star (fun i => (x i : ℂ)) ⬝ᵥ
        (A.map Complex.ofReal *ᵥ fun i => (x i : ℂ)) =
      ((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) := by
  rw [map_mulVec_ofReal]
  have hstar : star (fun i => (x i : ℂ)) = fun i => (x i : ℂ) := by
    funext i
    simp
  rw [hstar]
  simpa [Function.comp_def] using
    (RingHom.map_dotProduct Complex.ofRealHom x (A *ᵥ x)).symm

private lemma dotProduct_symplecticForm_self {n : ℕ} (x : PhaseIndex n → ℝ) :
    x ⬝ᵥ (symplecticForm n *ᵥ x) = 0 := by
  have hJ : -(x ⬝ᵥ (Matrix.J (Fin n) ℝ *ᵥ x)) =
      x ⬝ᵥ (Matrix.J (Fin n) ℝ *ᵥ x) := by
    simpa only [Matrix.J_transpose, Matrix.neg_mulVec, dotProduct_neg] using
      Matrix.dotProduct_transpose_mulVec (Matrix.J (Fin n) ℝ) x x
  rw [symplecticForm, Matrix.neg_mulVec, dotProduct_neg]
  linarith

private lemma symplecticForm_mulVec_eq_zero_iff {n : ℕ} (x : PhaseIndex n → ℝ) :
    symplecticForm n *ᵥ x = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun hx => by simp [hx]⟩
  have hsq : symplecticForm n * symplecticForm n =
      (-1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) := by
    simpa [symplecticForm] using (Matrix.J_squared (Fin n) ℝ)
  have hneg : (-1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) *ᵥ x = 0 := by
    rw [← hsq, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  simpa only [Matrix.neg_mulVec, Matrix.one_mulVec, neg_eq_zero] using hneg

/-- Every admissible real covariance matrix is positive definite. -/
theorem IsAdmissible.posDef {n : ℕ} {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : IsAdmissible γ) : γ.PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hγ.1
  · intro x hx
    let xC : PhaseIndex n → ℂ := fun i => x i
    let H : Matrix (PhaseIndex n) (PhaseIndex n) ℂ :=
      γ.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal
    have hquad : star xC ⬝ᵥ (H *ᵥ xC) =
        ((x ⬝ᵥ (γ *ᵥ x) : ℝ) : ℂ) := by
      dsimp only [H, xC]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
        dotProduct_smul, star_dotProduct_map_mulVec_ofReal,
        star_dotProduct_map_mulVec_ofReal, dotProduct_symplecticForm_self]
      simp
    have hnonneg : 0 ≤ x ⬝ᵥ (γ *ᵥ x) := by
      have h := hγ.2.re_dotProduct_nonneg xC
      rw [hquad] at h
      simpa using h
    rcases hnonneg.eq_or_lt with hzero | hpos
    · exfalso
      apply hx
      apply (symplecticForm_mulVec_eq_zero_iff x).mp
      have hH_mul : H *ᵥ xC = 0 :=
        (hγ.2.dotProduct_mulVec_zero_iff (x := xC)).mp (hquad.trans <| by simp [hzero])
      dsimp only [H, xC] at hH_mul
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, map_mulVec_ofReal,
        map_mulVec_ofReal] at hH_mul
      funext i
      have hi := congrArg Complex.im (congrFun hH_mul i)
      simpa using hi
    · exact hpos

end Gaussian
