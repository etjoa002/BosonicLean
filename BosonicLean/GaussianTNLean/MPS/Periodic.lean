/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.Contraction
import Mathlib.LinearAlgebra.Matrix.Block

/-! Periodic assembly and EPR wiring for Gaussian covariance matrices. -/

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

private abbrev PhaseOn (α : Type*) := α ⊕ α

private def symplecticOn (α : Type*) [DecidableEq α] :
    Matrix (PhaseOn α) (PhaseOn α) ℝ :=
  -Matrix.J α ℝ

private abbrev LocalMode (M : ℕ) := (Fin M ⊕ Fin M) ⊕ Fin 1

private def localModeEquiv (M : ℕ) : LocalMode M ≃ Fin (M + M + 1) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

namespace MPS.Internal

/-- Reindexing bridge used by the periodic site-major assembly. -/
def phaseSiteEquiv (N d : ℕ) :
    PhaseIndex (N * d) ≃ PhaseIndex d × Fin N :=
  (Equiv.sumCongr
      (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin N) (Fin d)))
      (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin N) (Fin d)))).trans
    (Equiv.sumProdDistrib (Fin d) (Fin d) (Fin N)).symm

end MPS.Internal

private def phaseModeEquiv (N M : ℕ) :
    PhaseOn (Fin N × LocalMode M) ≃ PhaseIndex (N * (M + M + 1)) :=
  Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (localModeEquiv M)).trans finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (localModeEquiv M)).trans finProdFinEquiv)

private def eliminatedEquiv (N M : ℕ) :
    PhaseOn (Fin N × Fin M) ≃ Fin (N * M + N * M) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

private def wiringRowEquiv (N M : ℕ) :
    PhaseOn (Fin N × Fin M) ⊕ PhaseIndex N ≃
      Fin (N * M + N * M) ⊕ PhaseIndex N :=
  Equiv.sumCongr (eliminatedEquiv N M) (Equiv.refl (PhaseIndex N))

/-- The independent sitewise covariance, with sites before local modes inside each
global position or momentum group. -/
def periodicInput {N M : ℕ}
    (Γ : Fin N → Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :
    Matrix (PhaseIndex (N * (M + M + 1))) (PhaseIndex (N * (M + M + 1))) ℝ :=
  (Matrix.blockDiagonal Γ).submatrix
    (MPS.Internal.phaseSiteEquiv N (M + M + 1))
    (MPS.Internal.phaseSiteEquiv N (M + M + 1))

private def periodicWiringCore (N M : ℕ) :
    Matrix (PhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
      (PhaseOn (Fin N × LocalMode M)) ℝ
  | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inl a)) =>
      if ia = (j, a) then 1 else 0
  | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inr b)) =>
      if ia = (finRotate N j, b) then 1 else 0
  | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inl a)) =>
      if ia = (j, a) then 1 else 0
  | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inr b)) =>
      if ia = (finRotate N j, b) then -1 else 0
  | Sum.inr (Sum.inl i), Sum.inl (j, Sum.inr _) =>
      if i = j then 1 else 0
  | Sum.inr (Sum.inr i), Sum.inr (j, Sum.inr _) =>
      if i = j then 1 else 0
  | _, _ => 0

/-- Periodic wiring: it retains the physical modes and eliminates
`q(A_i) + q(B_{i-1})` and `p(A_i) - p(B_{i-1})`. -/
def periodicWiring (N M : ℕ) :
    Matrix (Fin (N * M + N * M) ⊕ PhaseIndex N)
      (PhaseIndex (N * (M + M + 1))) ℝ :=
  Matrix.reindex (wiringRowEquiv N M) (phaseModeEquiv N M)
    (periodicWiringCore N M)

private lemma posSemidef_blockDiagonal {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : ι → Matrix κ κ ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (Matrix.blockDiagonal A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_blockDiagonal_iff.mpr fun i => (hA i).isHermitian
  · intro x
    have hquad :
        star x ⬝ᵥ Matrix.blockDiagonal A *ᵥ x =
          ∑ i : ι, star (fun k => x (k, i)) ⬝ᵥ A i *ᵥ (fun k => x (k, i)) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
        Matrix.blockDiagonal_apply, Pi.star_apply]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      simp
    rw [hquad]
    exact Finset.sum_nonneg fun i _ => (hA i).dotProduct_mulVec_nonneg _

private lemma isAdmissible_periodicInput {N M : ℕ}
    (Γ : Fin N → Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : ∀ i, IsAdmissible (Γ i)) : IsAdmissible (periodicInput Γ) := by
  let d := M + M + 1
  let e := MPS.Internal.phaseSiteEquiv N d
  let H : Fin N → Matrix (PhaseIndex d) (PhaseIndex d) ℂ := fun i =>
    (Γ i).map Complex.ofReal -
      Complex.I • (symplecticForm d).map Complex.ofReal
  have hsymp :
      (symplecticForm (N * d)).map Complex.ofReal =
        (Matrix.blockDiagonal (fun _ : Fin N =>
          (symplecticForm d).map Complex.ofReal)).submatrix e e := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      obtain ⟨⟨si, a⟩, rfl⟩ := finProdFinEquiv.surjective i <;>
      obtain ⟨⟨sj, b⟩, rfl⟩ := finProdFinEquiv.surjective j <;>
      simp [e, MPS.Internal.phaseSiteEquiv, symplecticForm, Matrix.J,
        Matrix.blockDiagonal_apply, Matrix.one_apply]
    all_goals by_cases hs : si = sj <;> simp [hs]
  have hunc :
      (periodicInput Γ).map Complex.ofReal -
          Complex.I • (symplecticForm (N * d)).map Complex.ofReal =
        (Matrix.blockDiagonal H).submatrix e e := by
    rw [hsymp]
    ext i j
    simp [periodicInput, H, e, d, Matrix.blockDiagonal_apply]
    split <;> simp_all
  constructor
  · exact (Matrix.isHermitian_iff_isSymm.mp
      ((Matrix.isHermitian_blockDiagonal_iff.mpr fun i =>
        Matrix.isHermitian_iff_isSymm.mpr (hΓ i).1).submatrix e)).eq
  · rw [hunc, Matrix.posSemidef_submatrix_equiv]
    exact posSemidef_blockDiagonal H fun i => (hΓ i).2

private lemma periodicWiringCore_injective (N M : ℕ) :
    Function.Injective (periodicWiringCore N M).transpose.mulVec := by
  classical
  intro x y hxy
  funext r
  rcases r with e | c
  · rcases e with e | e
    · obtain ⟨i, a⟩ := e
      have h := congrFun hxy (Sum.inl (i, Sum.inl (Sum.inl a)))
      simpa [periodicWiringCore, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type] using h
    · obtain ⟨i, a⟩ := e
      have h := congrFun hxy (Sum.inr (i, Sum.inl (Sum.inl a)))
      simpa [periodicWiringCore, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type] using h
  · rcases c with i | i
    · have h := congrFun hxy (Sum.inl (i, Sum.inr 0))
      simpa [periodicWiringCore, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type] using h
    · have h := congrFun hxy (Sum.inr (i, Sum.inr 0))
      simpa [periodicWiringCore, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_prod_type] using h

private lemma periodicWiring_injective (N M : ℕ) :
    Function.Injective (periodicWiring N M).transpose.mulVec := by
  classical
  intro x y hxy
  let er := wiringRowEquiv N M
  let ec := phaseModeEquiv N M
  have hcore : x ∘ er = y ∘ er := by
    apply periodicWiringCore_injective N M
    funext c
    have h := congrFun hxy (ec c)
    simpa [periodicWiring, er, ec, Matrix.transpose_reindex,
      Matrix.submatrix_mulVec_equiv] using h
  funext r
  obtain ⟨r, rfl⟩ := er.surjective r
  exact congrFun hcore r

@[simp] private lemma sum_ite_pair {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (i : α) (j : β) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, if i = x ∧ j = y then f x y else 0) = f i j := by
  calc
    _ = ∑ x : α, if i = x then
          (∑ y : β, if j = y then f x y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : i = x <;> simp [hx]
    _ = _ := by simp

@[simp] private lemma sum_ite_pair' {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (i : α) (j : β) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, if x = i ∧ y = j then f x y else 0) = f i j := by
  simp [eq_comm, sum_ite_pair]

@[simp] private lemma sum_ite_equiv_pair {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ α) (i : α) (j : β) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, if i = e x ∧ j = y then f x y else 0) =
      f (e.symm i) j := by
  let ep := Equiv.prodCongr e (Equiv.refl β)
  let g : α × β → ℝ := fun z =>
    if (i, j) = z then f (e.symm z.1) z.2 else 0
  have h := ep.sum_comp g
  simpa [ep, g, Prod.ext_iff, Fintype.sum_prod_type] using h

set_option maxHeartbeats 800000 in
private lemma periodicWiringCore_symplectic (N M : ℕ) :
    periodicWiringCore N M * symplecticOn (Fin N × LocalMode M) *
        (periodicWiringCore N M).transpose =
      Matrix.fromBlocks
        (0 : Matrix (PhaseOn (Fin N × Fin M)) (PhaseOn (Fin N × Fin M)) ℝ)
        0 0 (symplecticOn (Fin N)) := by
  classical
  ext r c
  rcases r with r | r <;> rcases r with r | r <;>
    rcases c with c | c <;> rcases c with c | c <;>
    simp [-finRotate_apply, -finRotate_symm_apply,
      periodicWiringCore, symplecticOn, Matrix.J,
      Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, eq_comm]
  all_goals
    obtain ⟨ri, ra⟩ := r
    obtain ⟨ci, ca⟩ := c
    rw [Finset.sum_add_distrib]
    simp [-finRotate_apply, -finRotate_symm_apply, Prod.ext_iff]

private lemma reindex_symplecticOn {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) :
    Matrix.reindex (Equiv.sumCongr e e) (Equiv.sumCongr e e)
        (symplecticOn α) = symplecticOn β := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := e.surjective i <;>
    obtain ⟨j, rfl⟩ := e.surjective j <;>
    simp [Matrix.reindex_apply, symplecticOn, Matrix.J, Matrix.one_apply]

private lemma periodicWiring_symplectic (N M : ℕ) :
    periodicWiring N M * symplecticForm (N * (M + M + 1)) *
        (periodicWiring N M).transpose =
      Matrix.fromBlocks
        (0 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ)
        0 0 (symplecticForm N) := by
  classical
  let er := wiringRowEquiv N M
  let ec := phaseModeEquiv N M
  let em : Fin N × LocalMode M ≃ Fin (N * (M + M + 1)) :=
    (Equiv.prodCongr (Equiv.refl (Fin N)) (localModeEquiv M)).trans finProdFinEquiv
  have hec : ec = Equiv.sumCongr em em := rfl
  have hΩin :
      symplecticForm (N * (M + M + 1)) =
        Matrix.reindex ec ec (symplecticOn (Fin N × LocalMode M)) := by
    rw [hec, reindex_symplecticOn]
    rfl
  have hΩout :
      Matrix.reindex er er
          (Matrix.fromBlocks
            (0 : Matrix (PhaseOn (Fin N × Fin M)) (PhaseOn (Fin N × Fin M)) ℝ)
            0 0 (symplecticOn (Fin N))) =
        Matrix.fromBlocks
          (0 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ)
          0 0 (symplecticForm N) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [er, wiringRowEquiv, Matrix.reindex_apply, symplecticOn,
        symplecticForm, Matrix.J, Matrix.fromBlocks]
  rw [periodicWiring, hΩin, Matrix.transpose_reindex]
  change
    Matrix.reindex er ec (periodicWiringCore N M) *
          Matrix.reindex ec ec (symplecticOn (Fin N × LocalMode M)) *
          Matrix.reindex ec er (periodicWiringCore N M).transpose = _
  rw [show Matrix.reindex er ec (periodicWiringCore N M) *
        Matrix.reindex ec ec (symplecticOn (Fin N × LocalMode M)) =
      Matrix.reindex er ec
        (periodicWiringCore N M * symplecticOn (Fin N × LocalMode M)) by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℝ ℝ er ec ec
          (periodicWiringCore N M) (symplecticOn (Fin N × LocalMode M))]
  rw [show Matrix.reindex er ec
          (periodicWiringCore N M * symplecticOn (Fin N × LocalMode M)) *
        Matrix.reindex ec er (periodicWiringCore N M).transpose =
      Matrix.reindex er er
        (periodicWiringCore N M * symplecticOn (Fin N × LocalMode M) *
          (periodicWiringCore N M).transpose) by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℝ ℝ er ec er
          (periodicWiringCore N M * symplecticOn (Fin N × LocalMode M))
          (periodicWiringCore N M).transpose]
  rw [periodicWiringCore_symplectic, hΩout]

/-- Periodic EPR wiring has independent rows and the required symplectic
cancellation; therefore its eliminated covariance is positive definite and its
Schur covariance is admissible. -/
theorem periodicCovariance_admissible {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (Γ : Fin N → Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : ∀ i, IsAdmissible (Γ i)) :
    Function.Injective (periodicWiring N M).transpose.mulVec ∧
    periodicWiring N M * symplecticForm (N * (M + M + 1)) *
        (periodicWiring N M).transpose =
      Matrix.fromBlocks
        (0 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ)
        0 0 (symplecticForm N) ∧
    (contractionBlock (periodicInput Γ) (periodicWiring N M)).PosDef ∧
    IsAdmissible (contractCovariance (periodicInput Γ) (periodicWiring N M)) := by
  have hIn := periodicWiring_injective N M
  have hSymp := periodicWiring_symplectic N M
  exact ⟨hIn, hSymp,
    isAdmissible_contractCovariance (periodicWiring N M)
      (isAdmissible_periodicInput Γ hΓ) hIn hSymp⟩

end Gaussian
