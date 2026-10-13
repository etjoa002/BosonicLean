/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.ConstructionDefs
import BosonicLean.PhaseSpace.Subsystem

/-! Admissibility of independent covariance sums. -/

open scoped ComplexOrder
open Matrix

namespace Gaussian

private def phaseSplitEquiv (n m : Nat) :
    PhaseIndex (n + m) ≃ PhaseIndex n ⊕ PhaseIndex m :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin n) (Fin m) (Fin n) (Fin m))

private lemma phaseSplitEquiv_coe (n m : Nat) :
    (phaseSplitEquiv n m : PhaseIndex (n + m) → PhaseIndex n ⊕ PhaseIndex m) =
      splitPhase := by
  funext i
  rcases i with i | i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i <;>
    cases j <;> simp [phaseSplitEquiv, splitPhase, Equiv.sumSumSumComm]

private lemma posSemidef_blocks_iff {u v : Type*} [Fintype u] [Fintype v]
    (A : Matrix u u ℂ) (B : Matrix v v ℂ) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · intro h
    constructor
    · convert h.submatrix Sum.inl using 1
      all_goals
        ext i j
        rfl
    · convert h.submatrix Sum.inr using 1
      all_goals
        ext i j
        rfl
  · rintro ⟨hA, hB⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hA.isHermitian.fromBlocks (by simp) hB.isHermitian
    · intro x
      have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      rw [Complex.nonneg_iff] at ha hb ⊢
      simp only [Matrix.fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Complex.add_re, Complex.add_im]
      refine ⟨add_nonneg ha.1 hb.1, ?_⟩
      change 0 = (star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl))).im +
        (star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr))).im
      rw [← ha.2, ← hb.2, add_zero]

private lemma symplecticForm_directSum (n m : Nat) :
    symplecticForm (n + m) = directSumCov (symplecticForm n) (symplecticForm m) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j <;>
    cases i <;> cases j <;>
    simp [directSumCov, splitPhase, symplecticForm, Matrix.J, Matrix.fromBlocks,
      Matrix.submatrix, Matrix.one_apply]
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega

private lemma symmetric_submatrix_iff {u v : Type*}
    (A : Matrix u u ℝ) (e : v ≃ u) :
    (A.submatrix e e).transpose = A.submatrix e e ↔ A.transpose = A := by
  constructor
  · intro h
    ext i j
    have hh := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa [Matrix.submatrix, Matrix.transpose] using hh
  · intro h
    ext i j
    exact congrFun (congrFun h (e i)) (e j)

private lemma uncertainty_directSum {n m : Nat}
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (B : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) :
    (directSumCov A B).map Complex.ofReal -
        Complex.I • (symplecticForm (n + m)).map Complex.ofReal =
      (Matrix.fromBlocks
        (A.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal)
        0 0
        (B.map Complex.ofReal - Complex.I • (symplecticForm m).map Complex.ofReal)).submatrix
        splitPhase splitPhase := by
  rw [symplecticForm_directSum]
  ext i j
  rcases h : splitPhase (n := n) (m := m) i with i' | i' <;>
    rcases k : splitPhase (n := n) (m := m) j with j' | j' <;>
    simp [directSumCov, Matrix.submatrix, Matrix.fromBlocks, h, k]

/-- The independent sum is admissible exactly when both component covariances are. -/
theorem isAdmissible_directSum_iff {n m : Nat}
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (B : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) :
    IsAdmissible (directSumCov A B) ↔ IsAdmissible A ∧ IsAdmissible B := by
  have hs : (directSumCov A B).transpose = directSumCov A B ↔
      A.transpose = A ∧ B.transpose = B := by
    unfold directSumCov
    rw [← phaseSplitEquiv_coe n m, symmetric_submatrix_iff]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_inj]
  unfold IsAdmissible
  rw [hs, uncertainty_directSum, ← phaseSplitEquiv_coe n m,
    Matrix.posSemidef_submatrix_equiv, posSemidef_blocks_iff]
  tauto

end Gaussian
