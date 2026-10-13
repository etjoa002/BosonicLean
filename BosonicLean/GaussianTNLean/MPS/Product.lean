/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.DirectSum
import BosonicLean.PhaseSpace.Examples
import BosonicLean.GaussianTNLean.MPS.Periodic

/-! Product Gaussian covariances represented by periodic vacuum wiring. -/

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

/-- Independent virtual vacua and a prescribed physical covariance, in q-then-p order. -/
def productResource (M : ℕ)
    (η : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ :=
  directSumCov (1 : Matrix (PhaseIndex (M + M)) (PhaseIndex (M + M)) ℝ) η

/-- Independent site covariances, with all positions before all momenta. -/
def productCovariance {N : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix (PhaseIndex N) (PhaseIndex N) ℝ
  | Sum.inl i, Sum.inl j => if i = j then η i (Sum.inl 0) (Sum.inl 0) else 0
  | Sum.inl i, Sum.inr j => if i = j then η i (Sum.inl 0) (Sum.inr 0) else 0
  | Sum.inr i, Sum.inl j => if i = j then η i (Sum.inr 0) (Sum.inl 0) else 0
  | Sum.inr i, Sum.inr j => if i = j then η i (Sum.inr 0) (Sum.inr 0) else 0

private lemma fin_castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hlt : (Fin.castAdd m i : ℕ) < (Fin.natAdd n j : ℕ) :=
    lt_of_lt_of_le (Fin.castAdd_lt m i) (Fin.le_coe_natAdd n j)
  exact hlt.ne (congrArg Fin.val h)

private lemma fin_natAdd_ne_castAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.natAdd n j ≠ Fin.castAdd m i :=
  (fin_castAdd_ne_natAdd i j).symm

private lemma directSum_one_one (n : ℕ) :
    directSumCov (1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
        (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) =
      (1 : Matrix (PhaseIndex (n + 1)) (PhaseIndex (n + 1)) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).surjective j <;>
    cases i <;> cases j <;>
    simp [directSumCov, splitPhase, Matrix.fromBlocks, Matrix.one_apply,
      fin_castAdd_ne_natAdd, fin_natAdd_ne_castAdd]

private lemma one_eq_diagonalOne :
    (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) = diagonalOne 1 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [diagonalOne, Matrix.diagonal, Matrix.one_apply]

private lemma isAdmissible_one (n : ℕ) :
    IsAdmissible (1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) := by
  induction n with
  | zero =>
      constructor
      · simp
      · have hzero :
            (1 : Matrix (PhaseIndex 0) (PhaseIndex 0) ℝ).map Complex.ofReal -
                Complex.I • (symplecticForm 0).map Complex.ofReal = 0 :=
          Subsingleton.elim _ _
        rw [hzero]
        exact Matrix.PosSemidef.zero
  | succ n ih =>
      rw [← directSum_one_one n]
      exact (isAdmissible_directSum_iff _ _).2
        ⟨ih, one_eq_diagonalOne ▸ isAdmissible_vacuumOne⟩

private abbrev ProductPhaseOn (α : Type*) := α ⊕ α

private abbrev ProductLocalMode (M : ℕ) := (Fin M ⊕ Fin M) ⊕ Fin 1

private def productLocalModeEquiv (M : ℕ) :
    ProductLocalMode M ≃ Fin (M + M + 1) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

private def productPhaseModeEquiv (N M : ℕ) :
    ProductPhaseOn (Fin N × ProductLocalMode M) ≃
      PhaseIndex (N * (M + M + 1)) :=
  Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (productLocalModeEquiv M)).trans
      finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (productLocalModeEquiv M)).trans
      finProdFinEquiv)

private def productPhaseLocalEquiv (M : ℕ) :
    ProductPhaseOn (ProductLocalMode M) ≃ PhaseIndex (M + M + 1) :=
  Equiv.sumCongr (productLocalModeEquiv M) (productLocalModeEquiv M)

private def productEliminatedEquiv (N M : ℕ) :
    ProductPhaseOn (Fin N × Fin M) ≃ Fin (N * M + N * M) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

private def productWiringRowEquiv (N M : ℕ) :
    ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N ≃
      Fin (N * M + N * M) ⊕ PhaseIndex N :=
  Equiv.sumCongr (productEliminatedEquiv N M) (Equiv.refl (PhaseIndex N))

private def productWiringCore (N M : ℕ) :
    Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
      (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ
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

private lemma periodicWiring_eq_productCore (N M : ℕ) :
    periodicWiring N M =
      Matrix.reindex (productWiringRowEquiv N M) (productPhaseModeEquiv N M)
        (productWiringCore N M) := by
  rfl

private def productLocalCovariance {M : ℕ}
    (η : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix (ProductPhaseOn (ProductLocalMode M))
      (ProductPhaseOn (ProductLocalMode M)) ℝ
  | Sum.inl (Sum.inl (Sum.inl a)), Sum.inl (Sum.inl (Sum.inl b)) =>
      if a = b then 1 else 0
  | Sum.inl (Sum.inl (Sum.inr a)), Sum.inl (Sum.inl (Sum.inr b)) =>
      if a = b then 1 else 0
  | Sum.inr (Sum.inl (Sum.inl a)), Sum.inr (Sum.inl (Sum.inl b)) =>
      if a = b then 1 else 0
  | Sum.inr (Sum.inl (Sum.inr a)), Sum.inr (Sum.inl (Sum.inr b)) =>
      if a = b then 1 else 0
  | Sum.inl (Sum.inr a), Sum.inl (Sum.inr b) => η (Sum.inl a) (Sum.inl b)
  | Sum.inl (Sum.inr a), Sum.inr (Sum.inr b) => η (Sum.inl a) (Sum.inr b)
  | Sum.inr (Sum.inr a), Sum.inl (Sum.inr b) => η (Sum.inr a) (Sum.inl b)
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => η (Sum.inr a) (Sum.inr b)
  | _, _ => 0

private def productInputSemantic {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix (ProductPhaseOn (Fin N × ProductLocalMode M))
      (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ
  | Sum.inl (i, a), Sum.inl (j, b) =>
      if i = j then productLocalCovariance (η i) (Sum.inl a) (Sum.inl b) else 0
  | Sum.inl (i, a), Sum.inr (j, b) =>
      if i = j then productLocalCovariance (η i) (Sum.inl a) (Sum.inr b) else 0
  | Sum.inr (i, a), Sum.inl (j, b) =>
      if i = j then productLocalCovariance (η i) (Sum.inr a) (Sum.inl b) else 0
  | Sum.inr (i, a), Sum.inr (j, b) =>
      if i = j then productLocalCovariance (η i) (Sum.inr a) (Sum.inr b) else 0

private lemma productResource_eq_local {M : ℕ}
    (η : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    productResource M η =
      Matrix.reindex (productPhaseLocalEquiv M) (productPhaseLocalEquiv M)
        (productLocalCovariance η) := by
  classical
  ext r c
  obtain ⟨r, rfl⟩ := (productPhaseLocalEquiv M).surjective r
  obtain ⟨c, rfl⟩ := (productPhaseLocalEquiv M).surjective c
  rcases r with ((a | a) | a) | ((a | a) | a) <;>
    rcases c with ((b | b) | b) | ((b | b) | b) <;>
    simp [productResource, productLocalCovariance, productPhaseLocalEquiv,
      productLocalModeEquiv, directSumCov, splitPhase, Matrix.reindex_apply,
      Matrix.fromBlocks, Matrix.one_apply, -Fin.natAdd_eq_addNat,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      fin_castAdd_ne_natAdd, fin_natAdd_ne_castAdd]

private lemma periodicInput_eq_productInputSemantic {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    periodicInput (fun i => productResource M (η i)) =
      Matrix.reindex (productPhaseModeEquiv N M) (productPhaseModeEquiv N M)
        (productInputSemantic η) := by
  classical
  ext r c
  obtain ⟨r, rfl⟩ := (productPhaseModeEquiv N M).surjective r
  obtain ⟨c, rfl⟩ := (productPhaseModeEquiv N M).surjective c
  rcases r with ⟨i, a⟩ | ⟨i, a⟩ <;>
    rcases c with ⟨j, b⟩ | ⟨j, b⟩ <;>
    simp [periodicInput, productResource_eq_local, productInputSemantic,
      productPhaseModeEquiv, productPhaseLocalEquiv,
      MPS.Internal.phaseSiteEquiv, Matrix.reindex_apply,
      Matrix.blockDiagonal_apply]

@[simp] private lemma product_sum_ite_pair {α β : Type*}
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

@[simp] private lemma product_sum_ite_pair' {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (i : α) (j : β) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, if x = i ∧ y = j then f x y else 0) = f i j := by
  simp [eq_comm, product_sum_ite_pair]

@[simp] private lemma product_sum_ite_equiv_pair {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ α) (i : α) (j : β) (f : α → β → ℝ) :
    (∑ x : α, ∑ y : β, if i = e x ∧ j = y then f x y else 0) =
      f (e.symm i) j := by
  let ep := Equiv.prodCongr e (Equiv.refl β)
  let g : α × β → ℝ := fun z =>
    if (i, j) = z then f (e.symm z.1) z.2 else 0
  have h := ep.sum_comp g
  simpa [ep, g, Prod.ext_iff, Fintype.sum_prod_type] using h

private def productWiringInputSemantic {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
      (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ
  | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inl a)) =>
      if ia = (j, a) then 1 else 0
  | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inr b)) =>
      if ia = (finRotate N j, b) then 1 else 0
  | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inl a)) =>
      if ia = (j, a) then 1 else 0
  | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inr b)) =>
      if ia = (finRotate N j, b) then -1 else 0
  | Sum.inr (Sum.inl i), Sum.inl (j, Sum.inr a) =>
      if i = j then η i (Sum.inl 0) (Sum.inl a) else 0
  | Sum.inr (Sum.inl i), Sum.inr (j, Sum.inr a) =>
      if i = j then η i (Sum.inl 0) (Sum.inr a) else 0
  | Sum.inr (Sum.inr i), Sum.inl (j, Sum.inr a) =>
      if i = j then η i (Sum.inr 0) (Sum.inl a) else 0
  | Sum.inr (Sum.inr i), Sum.inr (j, Sum.inr a) =>
      if i = j then η i (Sum.inr 0) (Sum.inr a) else 0
  | _, _ => 0

set_option maxHeartbeats 400000 in
private lemma productWiringCore_mul_input_eliminated_q {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)
    (r : Fin N × Fin M)
    (c : ProductPhaseOn (Fin N × ProductLocalMode M)) :
    (productWiringCore N M * productInputSemantic η :
        Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
          (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ)
        (Sum.inl (Sum.inl r)) c =
      productWiringInputSemantic η (Sum.inl (Sum.inl r)) c := by
  classical
  obtain ⟨ri, ra⟩ := r
  rcases c with ⟨j, ((b | b) | b)⟩ | ⟨j, ((b | b) | b)⟩ <;>
    simp [-finRotate_apply, -finRotate_symm_apply, productWiringCore,
      productInputSemantic, productLocalCovariance, productWiringInputSemantic,
      Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Prod.ext_iff, eq_comm]

set_option maxHeartbeats 400000 in
private lemma productWiringCore_mul_input_eliminated_p {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)
    (r : Fin N × Fin M)
    (c : ProductPhaseOn (Fin N × ProductLocalMode M)) :
    (productWiringCore N M * productInputSemantic η :
        Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
          (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ)
        (Sum.inl (Sum.inr r)) c =
      productWiringInputSemantic η (Sum.inl (Sum.inr r)) c := by
  classical
  obtain ⟨ri, ra⟩ := r
  rcases c with ⟨j, ((b | b) | b)⟩ | ⟨j, ((b | b) | b)⟩ <;>
    simp [-finRotate_apply, -finRotate_symm_apply, productWiringCore,
      productInputSemantic, productLocalCovariance, productWiringInputSemantic,
      Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Prod.ext_iff, eq_comm]

set_option maxHeartbeats 400000 in
private lemma productWiringCore_mul_input_retained_q {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)
    (r : Fin N)
    (c : ProductPhaseOn (Fin N × ProductLocalMode M)) :
    (productWiringCore N M * productInputSemantic η :
        Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
          (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ)
        (Sum.inr (Sum.inl r)) c =
      productWiringInputSemantic η (Sum.inr (Sum.inl r)) c := by
  classical
  rcases c with ⟨j, ((b | b) | b)⟩ | ⟨j, ((b | b) | b)⟩ <;>
    simp [productWiringCore, productInputSemantic, productLocalCovariance,
      productWiringInputSemantic, Matrix.mul_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Prod.ext_iff]
  all_goals by_cases h : r = j <;> simp [h]

set_option maxHeartbeats 400000 in
private lemma productWiringCore_mul_input_retained_p {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)
    (r : Fin N)
    (c : ProductPhaseOn (Fin N × ProductLocalMode M)) :
    (productWiringCore N M * productInputSemantic η :
        Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
          (ProductPhaseOn (Fin N × ProductLocalMode M)) ℝ)
        (Sum.inr (Sum.inr r)) c =
      productWiringInputSemantic η (Sum.inr (Sum.inr r)) c := by
  classical
  rcases c with ⟨j, ((b | b) | b)⟩ | ⟨j, ((b | b) | b)⟩ <;>
    simp [productWiringCore, productInputSemantic, productLocalCovariance,
      productWiringInputSemantic, Matrix.mul_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Prod.ext_iff]
  all_goals by_cases h : r = j <;> simp [h]

private lemma productWiringCore_mul_input {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    productWiringCore N M * productInputSemantic η =
      productWiringInputSemantic η := by
  ext r c
  rcases r with r | r
  · rcases r with r | r
    · exact productWiringCore_mul_input_eliminated_q η r c
    · exact productWiringCore_mul_input_eliminated_p η r c
  · rcases r with r | r
    · exact productWiringCore_mul_input_retained_q η r c
    · exact productWiringCore_mul_input_retained_p η r c

@[simp] private lemma two_smul_one_apply {α : Type*} [DecidableEq α]
    (i j : α) :
    (2 • (1 : Matrix α α ℝ)) i j = if i = j then 2 else 0 := by
  change (2 • (if i = j then (1 : ℝ) else 0)) = _
  by_cases h : i = j <;> simp [h]

@[simp] private lemma product_sum_signed_ite_equiv_pair {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ α) (i k : α) (j l : β) :
    (∑ x : α, ∑ y : β,
      if i = e x ∧ y = j then
        -(if k = e x ∧ y = l then (-1 : ℝ) else 0)
      else 0) =
      if i = k ∧ j = l then 1 else 0 := by
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l
      simp [eq_comm]
    · simp [hj, eq_comm]
  · simp [hi, eq_comm]

set_option maxHeartbeats 800000 in
private lemma productWiringInputSemantic_mul_transpose {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    productWiringInputSemantic η * (productWiringCore N M).transpose =
      Matrix.fromBlocks
        (2 • (1 : Matrix (ProductPhaseOn (Fin N × Fin M))
          (ProductPhaseOn (Fin N × Fin M)) ℝ))
        0 0 (productCovariance η) := by
  classical
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · change
      (productWiringInputSemantic η * (productWiringCore N M).transpose :
        Matrix (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
          (ProductPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N) ℝ)
          (Sum.inl r) (Sum.inl c) =
        (2 • (1 : Matrix (ProductPhaseOn (Fin N × Fin M))
          (ProductPhaseOn (Fin N × Fin M)) ℝ)) r c
    rw [two_smul_one_apply]
    rcases r with r | r <;> rcases c with c | c
    all_goals obtain ⟨ri, ra⟩ := r
    all_goals obtain ⟨ci, ca⟩ := c
    all_goals by_cases hi : ri = ci <;> by_cases ha : ra = ca
    all_goals
      simp [-finRotate_apply, -finRotate_symm_apply,
        productWiringCore, productWiringInputSemantic,
        Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Finset.sum_add_distrib, Prod.ext_iff, hi, ha] <;> norm_num
  · rcases r with r | r <;> rcases c with c | c <;>
      obtain ⟨ri, ra⟩ := r <;>
      simp [productWiringCore, productWiringInputSemantic,
        Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Prod.ext_iff]
  · rcases r with r | r <;> rcases c with c | c <;>
      obtain ⟨ci, ca⟩ := c <;>
      simp [productWiringCore, productWiringInputSemantic,
        Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Prod.ext_iff]
  · rcases r with r | r <;> rcases c with c | c <;>
      simp [productWiringCore, productWiringInputSemantic, productCovariance,
        Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Prod.ext_iff]
    all_goals by_cases h : r = c <;> simp [h]

private lemma productWiringCore_covariance {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    productWiringCore N M * productInputSemantic η *
        (productWiringCore N M).transpose =
      Matrix.fromBlocks
        (2 • (1 : Matrix (ProductPhaseOn (Fin N × Fin M))
          (ProductPhaseOn (Fin N × Fin M)) ℝ))
        0 0 (productCovariance η) := by
  rw [productWiringCore_mul_input]
  exact productWiringInputSemantic_mul_transpose η

private lemma reindex_productCovariance_blocks {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    Matrix.reindex (productWiringRowEquiv N M) (productWiringRowEquiv N M)
        (Matrix.fromBlocks
          (2 • (1 : Matrix (ProductPhaseOn (Fin N × Fin M))
            (ProductPhaseOn (Fin N × Fin M)) ℝ))
          0 0 (productCovariance η)) =
      Matrix.fromBlocks
        (2 • (1 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ))
        0 0 (productCovariance η) := by
  classical
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · change
      (2 • (1 : Matrix (ProductPhaseOn (Fin N × Fin M))
        (ProductPhaseOn (Fin N × Fin M)) ℝ))
          ((productEliminatedEquiv N M).symm r)
          ((productEliminatedEquiv N M).symm c) =
        (2 • (1 : Matrix (Fin (N * M + N * M))
          (Fin (N * M + N * M)) ℝ)) r c
    rw [two_smul_one_apply, two_smul_one_apply]
    simp
  · rfl
  · rfl
  · rfl

private lemma periodicProduct_wired {N M : ℕ}
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :
    periodicWiring N M * periodicInput (fun i => productResource M (η i)) *
        (periodicWiring N M).transpose =
      Matrix.fromBlocks
        (2 • (1 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ))
        0 0 (productCovariance η) := by
  let er := productWiringRowEquiv N M
  let ec := productPhaseModeEquiv N M
  rw [periodicWiring_eq_productCore, periodicInput_eq_productInputSemantic,
    Matrix.transpose_reindex]
  change
    Matrix.reindex er ec (productWiringCore N M) *
          Matrix.reindex ec ec (productInputSemantic η) *
          Matrix.reindex ec er (productWiringCore N M).transpose = _
  rw [show Matrix.reindex er ec (productWiringCore N M) *
        Matrix.reindex ec ec (productInputSemantic η) =
      Matrix.reindex er ec
        (productWiringCore N M * productInputSemantic η) by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℝ ℝ er ec ec
          (productWiringCore N M) (productInputSemantic η)]
  rw [show Matrix.reindex er ec
          (productWiringCore N M * productInputSemantic η) *
        Matrix.reindex ec er (productWiringCore N M).transpose =
      Matrix.reindex er er
        (productWiringCore N M * productInputSemantic η *
          (productWiringCore N M).transpose) by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℝ ℝ er ec er
          (productWiringCore N M * productInputSemantic η)
          (productWiringCore N M).transpose]
  rw [productWiringCore_covariance, reindex_productCovariance_blocks]

private lemma contractCovariance_eq_lowerBlock {n m k : ℕ}
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (W : Matrix (Fin k ⊕ PhaseIndex m) (PhaseIndex n) ℝ)
    (E : Matrix (Fin k) (Fin k) ℝ)
    (G : Matrix (PhaseIndex m) (PhaseIndex m) ℝ)
    (h : W * γ * W.transpose = Matrix.fromBlocks E 0 0 G) :
    contractCovariance γ W = G := by
  unfold contractCovariance
  rw [h]
  change G - (0 : Matrix (PhaseIndex m) (Fin k) ℝ) * E⁻¹ *
      (0 : Matrix (Fin k) (PhaseIndex m) ℝ) = G
  simp

private lemma productCovariance_one {N : ℕ} :
    productCovariance (fun _ : Fin N =>
      (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)) =
      (1 : Matrix (PhaseIndex N) (PhaseIndex N) ℝ) := by
  ext r c
  rcases r with r | r <;> rcases c with c | c <;>
    simp [productCovariance, Matrix.one_apply]

/-- Independent virtual vacua and arbitrary one-mode site covariances give the
prescribed product covariance after periodic contraction. -/
theorem periodicProduct_covariance {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (η : Fin N → Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ)
    (hη : ∀ i, IsAdmissible (η i)) :
    (∀ i, IsAdmissible (productResource M (η i))) ∧
    periodicWiring N M * periodicInput (fun i => productResource M (η i)) *
        (periodicWiring N M).transpose =
      Matrix.fromBlocks
        (2 • (1 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ))
        0 0 (productCovariance η) ∧
    contractCovariance (periodicInput (fun i => productResource M (η i)))
        (periodicWiring N M) = productCovariance η ∧
    IsAdmissible (productCovariance η) := by
  have hresource : ∀ i, IsAdmissible (productResource M (η i)) := by
    intro i
    exact (isAdmissible_directSum_iff _ _).2 ⟨isAdmissible_one _, hη i⟩
  have hwired := periodicProduct_wired (M := M) η
  have hperiodic := periodicCovariance_admissible hN hM _ hresource
  have hcontract :
      contractCovariance (periodicInput (fun i => productResource M (η i)))
          (periodicWiring N M) = productCovariance η :=
    contractCovariance_eq_lowerBlock _ _ _ _ hwired
  exact ⟨hresource, hwired, hcontract, hcontract ▸ hperiodic.2.2.2⟩

/-- Vacuum physical inputs contract to the multimode vacuum covariance. -/
theorem periodicProduct_vacuum {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M) :
    contractCovariance
      (periodicInput (fun _ : Fin N => productResource M 1))
      (periodicWiring N M) = 1 := by
  have hη : ∀ _ : Fin N,
      IsAdmissible (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) :=
    fun _ => isAdmissible_one 1
  exact ((periodicProduct_covariance hN hM _ hη).2.2.1).trans
    productCovariance_one

/-- Positive local squeezings give the corresponding nonuniform product
covariance. -/
theorem periodicProduct_squeezed {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (s : Fin N → ℝ) (hs : ∀ i, 0 < s i) :
    let η := fun i => diagonalOne ((s i)^2) (1 / (s i)^2)
    contractCovariance (periodicInput (fun i => productResource M (η i)))
        (periodicWiring N M) = productCovariance η ∧
    IsAdmissible (productCovariance η) := by
  dsimp only
  have hη : ∀ i, IsAdmissible (diagonalOne ((s i)^2) (1 / (s i)^2)) := by
    intro i
    simpa [one_div] using isAdmissible_squeezedOne (sq_pos_of_pos (hs i))
  exact (periodicProduct_covariance hN hM _ hη).2.2

end Gaussian
