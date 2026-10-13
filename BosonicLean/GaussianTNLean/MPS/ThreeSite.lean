import BosonicLean.GaussianTNLean.MPS.ThreeSiteBlocks
import BosonicLean.PhaseSpace.Covariance
import BosonicLean.PhaseSpace.DirectSum
import BosonicLean.PhaseSpace.Examples

/-! The exact three-site periodic covariance. -/

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

namespace MPS.Internal

def threeSiteWiringInputLiteral : Matrix (Fin 12) (Fin 18) ℝ :=
  threeSiteWiringInputInt.map (Int.castRingHom ℝ)

def threeSiteWiredLiteral : Matrix (Fin 12) (Fin 12) ℝ :=
  threeSiteWiredInt.map (Int.castRingHom ℝ)

private lemma threeSiteWiringLiteral_cast :
    threeSiteWiringLiteralInt.map (Int.castRingHom ℝ) =
      threeSiteWiringLiteral := by
  rfl

private lemma threeSiteInputLiteral_cast :
    threeSiteInputLiteralInt.map (Int.castRingHom ℝ) =
      threeSiteInputLiteral := by
  rfl

lemma threeSiteWiringInputLiteral_mul :
    threeSiteWiringLiteral * threeSiteInputLiteral =
      threeSiteWiringInputLiteral := by
  rw [← threeSiteWiringLiteral_cast, ← threeSiteInputLiteral_cast,
    ← Matrix.map_mul, threeSiteWiringInputInt_eq]
  rfl

lemma threeSiteWiringInputLiteral_mul_transpose :
    threeSiteWiringInputLiteral * threeSiteWiringLiteral.transpose =
      threeSiteWiredLiteral := by
  rw [threeSiteWiringInputLiteral, ← threeSiteWiringLiteral_cast,
    ← Matrix.transpose_map, ← Matrix.map_mul, threeSiteWiredInt_eq]
  rfl

def threeSiteWiredExplicit :
    Matrix (Fin 6 ⊕ PhaseIndex 3) (Fin 6 ⊕ PhaseIndex 3) ℝ :=
  Matrix.reindex threeSiteRowFlatten.symm threeSiteRowFlatten.symm
    threeSiteWiredLiteral

lemma threeSiteWired_eq_explicit :
    periodicWiring 3 1 *
        periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance) *
        (periodicWiring 3 1).transpose =
      threeSiteWiredExplicit := by
  rw [threeSiteWiring_eq_explicit, threeSiteInput_eq_explicit,
    threeSiteWiringExplicit, threeSiteInputExplicit,
    Matrix.transpose_reindex]
  let er := threeSiteRowFlatten.symm
  let ec := threeSitePhaseFlatten.symm
  have hmul₁ :
      Matrix.reindex er ec threeSiteWiringLiteral *
          Matrix.reindex ec ec threeSiteInputLiteral =
        Matrix.reindex er ec
          (threeSiteWiringLiteral * threeSiteInputLiteral) := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      Matrix.reindexLinearEquiv_mul ℝ ℝ er ec ec
        threeSiteWiringLiteral threeSiteInputLiteral
  rw [hmul₁, threeSiteWiringInputLiteral_mul]
  have hmul₂ :
      Matrix.reindex er ec threeSiteWiringInputLiteral *
          Matrix.reindex ec er threeSiteWiringLiteral.transpose =
        Matrix.reindex er er
          (threeSiteWiringInputLiteral * threeSiteWiringLiteral.transpose) := by
    simpa only [Matrix.coe_reindexLinearEquiv] using
      Matrix.reindexLinearEquiv_mul ℝ ℝ er ec er
        threeSiteWiringInputLiteral threeSiteWiringLiteral.transpose
  rw [hmul₂, threeSiteWiringInputLiteral_mul_transpose]
  rfl

end MPS.Internal

lemma threeSiteShear_symplectic :
    threeSiteShear * symplecticForm 3 * threeSiteShear.transpose =
      symplecticForm 3 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [threeSiteShear, threeSiteK, symplecticForm, Matrix.J,
      Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_sum_type]

private def phaseSplitEquivThreeSite (n m : Nat) :
    PhaseIndex (n + m) ≃ PhaseIndex n ⊕ PhaseIndex m :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin n) (Fin m) (Fin n) (Fin m))

private lemma phaseSplitEquivThreeSite_coe (n m : Nat) :
    (phaseSplitEquivThreeSite n m : PhaseIndex (n + m) →
      PhaseIndex n ⊕ PhaseIndex m) = splitPhase := by
  funext i
  rcases i with i | i <;>
    obtain ⟨j, rfl⟩ :=
      (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i <;>
    cases j <;>
    simp [phaseSplitEquivThreeSite, splitPhase, Equiv.sumSumSumComm]

private lemma directSumCov_one (n m : Nat) :
    directSumCov
        (1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
        (1 : Matrix (PhaseIndex m) (PhaseIndex m) ℝ) =
      (1 : Matrix (PhaseIndex (n + m)) (PhaseIndex (n + m)) ℝ) := by
  unfold directSumCov
  rw [← phaseSplitEquivThreeSite_coe n m, Matrix.fromBlocks_one,
    Matrix.submatrix_one_equiv]

lemma threeSiteLocalCovariance_admissible :
    IsAdmissible threeSiteLocalCovariance := by
  have hvac2 : IsAdmissible
      (directSumCov (diagonalOne 1 1) (diagonalOne 1 1)) :=
    (isAdmissible_directSum_iff _ _).2
      ⟨isAdmissible_vacuumOne, isAdmissible_vacuumOne⟩
  have hvac3 : IsAdmissible
      (directSumCov (directSumCov (diagonalOne 1 1) (diagonalOne 1 1))
        (diagonalOne 1 1)) :=
    (isAdmissible_directSum_iff _ _).2 ⟨hvac2, isAdmissible_vacuumOne⟩
  have hone : diagonalOne 1 1 =
      (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [diagonalOne, Matrix.diagonal]
  have hid :
      directSumCov (directSumCov (diagonalOne 1 1) (diagonalOne 1 1))
          (diagonalOne 1 1) =
        (1 : Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ) := by
    rw [hone, directSumCov_one, directSumCov_one]
  rw [hid] at hvac3
  simpa [threeSiteLocalCovariance] using
    isAdmissible_symplecticCongruence hvac3 threeSiteShear_symplectic

private noncomputable def threeSiteEliminatedInverse :
    Matrix (Fin 6) (Fin 6) ℝ :=
  !![(1:ℝ)/2,0,0,0,0,0;
     0,1/2,0,0,0,0;
     0,0,1/2,0,0,0;
     0,0,0,3/10,1/10,1/10;
     0,0,0,1/10,3/10,1/10;
     0,0,0,1/10,1/10,3/10]

private def threeSiteEliminatedBlock : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2,0,0,0,0,0;
     0,2,0,0,0,0;
     0,0,2,0,0,0;
     0,0,0,4,-1,-1;
     0,0,0,-1,4,-1;
     0,0,0,-1,-1,4]

private def threeSiteCrossBlock : Matrix (Fin 6) (PhaseIndex 3) ℝ :=
  Matrix.reindex (Equiv.refl (Fin 6)) finSumFinEquiv.symm
    !![0,0,0,1,0,1;
       0,0,0,1,1,0;
       0,0,0,0,1,1;
       1,0,-1,0,0,0;
       -1,1,0,0,0,0;
       0,-1,1,0,0,0]

private def threeSiteRetainedBlock :
    Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  Matrix.fromBlocks 1 0 0
    !![3,0,0;
       0,3,0;
       0,0,3]

private noncomputable def threeSiteTargetCovariance :
    Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  Matrix.fromBlocks
    (!![(3:ℝ)/5,1/5,1/5;
        1/5,3/5,1/5;
        1/5,1/5,3/5]) 0 0
    (!![(2:ℝ),-1/2,-1/2;
        -1/2,2,-1/2;
        -1/2,-1/2,2])

private lemma threeSiteWired_blocks :
    let V := periodicWiring 3 1 *
      periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance) *
      (periodicWiring 3 1).transpose
    V.submatrix Sum.inl Sum.inl = threeSiteEliminatedBlock ∧
    V.submatrix Sum.inl Sum.inr = threeSiteCrossBlock ∧
    V.submatrix Sum.inr Sum.inl = threeSiteCrossBlock.transpose ∧
    V.submatrix Sum.inr Sum.inr = threeSiteRetainedBlock := by
  rw [MPS.Internal.threeSiteWired_eq_explicit]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [MPS.Internal.threeSiteWiredExplicit,
        MPS.Internal.threeSiteWiredLiteral, MPS.Internal.threeSiteWiredInt,
        MPS.Internal.threeSiteRowFlatten,
        threeSiteEliminatedBlock, Matrix.reindex_apply, finSumFinEquiv,
        Fin.castAdd, Fin.addNat, Fin.castLE]
  constructor
  · ext i j
    fin_cases i
    all_goals rcases j with j | j <;> fin_cases j <;>
      norm_num [MPS.Internal.threeSiteWiredExplicit,
        MPS.Internal.threeSiteWiredLiteral, MPS.Internal.threeSiteWiredInt,
        MPS.Internal.threeSiteRowFlatten,
        threeSiteCrossBlock, Matrix.reindex_apply, finSumFinEquiv,
        Fin.castAdd, Fin.addNat, Fin.castLE]
  constructor
  · ext i j
    rcases i with i | i <;> fin_cases i
    all_goals fin_cases j <;>
      norm_num [MPS.Internal.threeSiteWiredExplicit,
        MPS.Internal.threeSiteWiredLiteral, MPS.Internal.threeSiteWiredInt,
        MPS.Internal.threeSiteRowFlatten,
        threeSiteCrossBlock, Matrix.reindex_apply, Matrix.transpose,
        finSumFinEquiv, Fin.castAdd, Fin.addNat, Fin.castLE]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [MPS.Internal.threeSiteWiredExplicit,
        MPS.Internal.threeSiteWiredLiteral, MPS.Internal.threeSiteWiredInt,
        MPS.Internal.threeSiteRowFlatten,
        threeSiteRetainedBlock, Matrix.reindex_apply, Matrix.fromBlocks,
        Matrix.one_apply, finSumFinEquiv, Fin.castAdd, Fin.addNat, Fin.castLE]

private lemma threeSiteEliminatedInverse_spec :
    threeSiteEliminatedBlock⁻¹ = threeSiteEliminatedInverse := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [threeSiteEliminatedBlock, threeSiteEliminatedInverse,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private lemma threeSite_contractCovariance :
    contractCovariance
        (periodicInput (fun _ : Fin 3 => threeSiteLocalCovariance))
        (periodicWiring 3 1) =
      threeSiteTargetCovariance := by
  let V := periodicWiring 3 1 *
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance) *
    (periodicWiring 3 1).transpose
  have hblocks := threeSiteWired_blocks
  change V.submatrix Sum.inr Sum.inr -
      V.submatrix Sum.inr Sum.inl *
        (V.submatrix Sum.inl Sum.inl)⁻¹ *
        V.submatrix Sum.inl Sum.inr = threeSiteTargetCovariance
  rw [hblocks.2.2.2, hblocks.2.2.1, hblocks.1,
    threeSiteEliminatedInverse_spec, hblocks.2.1]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [threeSiteRetainedBlock, threeSiteCrossBlock,
      threeSiteEliminatedInverse, threeSiteTargetCovariance,
      Matrix.reindex_apply, Matrix.fromBlocks, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, finSumFinEquiv,
      Fin.castAdd, Fin.addNat, Fin.castLE]

/-- The local shear is symplectic, its covariance is admissible, and periodic
contraction gives the stated three-site covariance. -/
theorem threeSite_covariance :
    threeSiteShear * symplecticForm 3 * threeSiteShear.transpose =
        symplecticForm 3 ∧
    IsAdmissible threeSiteLocalCovariance ∧
    contractCovariance (periodicInput (fun _ : Fin 3 => threeSiteLocalCovariance))
      (periodicWiring 3 1) =
      Matrix.fromBlocks
        (!![(3:ℝ)/5,1/5,1/5;1/5,3/5,1/5;1/5,1/5,3/5]) 0 0
        (!![(2:ℝ),-1/2,-1/2;-1/2,2,-1/2;-1/2,-1/2,2]) ∧
    IsAdmissible (contractCovariance
      (periodicInput (fun _ : Fin 3 => threeSiteLocalCovariance))
      (periodicWiring 3 1)) := by
  have hgeneral := periodicCovariance_admissible (N := 3) (M := 1)
    (by norm_num) (by norm_num)
    (fun _ : Fin 3 => threeSiteLocalCovariance)
    (fun _ => threeSiteLocalCovariance_admissible)
  exact ⟨threeSiteShear_symplectic,
    threeSiteLocalCovariance_admissible,
    threeSite_contractCovariance,
    hgeneral.2.2.2⟩

end Gaussian
