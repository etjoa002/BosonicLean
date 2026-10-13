import BosonicLean.GaussianTNLean.MPS.ThreeSiteArithmetic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

def threeSiteK : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
     0, 0, 1;
     1, 1, 0]

def threeSiteShear : Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  Matrix.fromBlocks 1 0 threeSiteK 1

def threeSiteLocalCovariance : Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  threeSiteShear * threeSiteShear.transpose

namespace MPS.Internal

def threeSiteRowFlatten :
    (Fin 6 ⊕ PhaseIndex 3) ≃ Fin 12 :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) finSumFinEquiv).trans finSumFinEquiv

def threeSitePhaseFlatten : PhaseIndex 9 ≃ Fin 18 :=
  finSumFinEquiv

def threeSiteLowerBlock : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2,1,0;
     1,2,0;
     0,0,3]

def threeSiteLocalExplicit :
    Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  Matrix.fromBlocks 1 threeSiteK threeSiteK threeSiteLowerBlock

def threeSiteWiringLiteral : Matrix (Fin 12) (Fin 18) ℝ :=
  threeSiteWiringLiteralInt.map (Int.castRingHom ℝ)

def threeSiteInputLiteral : Matrix (Fin 18) (Fin 18) ℝ :=
  threeSiteInputLiteralInt.map (Int.castRingHom ℝ)

def threeSiteWiringExplicit :
    Matrix (Fin 6 ⊕ PhaseIndex 3) (PhaseIndex 9) ℝ :=
  Matrix.reindex threeSiteRowFlatten.symm threeSitePhaseFlatten.symm
    threeSiteWiringLiteral

def threeSiteInputExplicit : Matrix (PhaseIndex 9) (PhaseIndex 9) ℝ :=
  Matrix.reindex threeSitePhaseFlatten.symm threeSitePhaseFlatten.symm
    threeSiteInputLiteral

lemma threeSiteWiring_eq_explicit :
    periodicWiring 3 1 = threeSiteWiringExplicit := by
  ext i j
  rcases i with i | i
  · fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
      first
      | change (0 : ℝ) = ((0 : ℤ) : ℝ); norm_num
      | change (1 : ℝ) = ((1 : ℤ) : ℝ); norm_num
      | change (-1 : ℝ) = ((-1 : ℤ) : ℝ); norm_num
  · rcases i with i | i <;> fin_cases i <;>
      rcases j with j | j <;> fin_cases j <;>
      first
      | change (0 : ℝ) = ((0 : ℤ) : ℝ); norm_num
      | change (1 : ℝ) = ((1 : ℤ) : ℝ); norm_num
      | change (-1 : ℝ) = ((-1 : ℤ) : ℝ); norm_num

lemma threeSiteLocalCovariance_eq_explicit :
    threeSiteLocalCovariance = threeSiteLocalExplicit := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [threeSiteLocalCovariance, threeSiteLocalExplicit,
      threeSiteLowerBlock, threeSiteShear, threeSiteK,
      Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ]

lemma threeSiteInput_qq (i j : Fin 9) :
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance)
        (Sum.inl i) (Sum.inl j) =
      threeSiteInputExplicit (Sum.inl i) (Sum.inl j) := by
  rw [threeSiteLocalCovariance_eq_explicit]
  fin_cases i <;> fin_cases j <;>
    norm_num [periodicInput, threeSiteInputExplicit, threeSiteInputLiteral,
      threeSiteInputLiteralInt,
      MPS.Internal.phaseSiteEquiv,
      finSumFinEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.castAdd, Fin.addNat, Fin.castLE,
      threeSitePhaseFlatten, threeSiteLocalExplicit, threeSiteLowerBlock,
      threeSiteK, Matrix.fromBlocks,
      Matrix.blockDiagonal_apply, Matrix.reindex_apply,
      Matrix.one_apply, Fintype.sum_sum_type]

lemma threeSiteInput_qp (i j : Fin 9) :
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance)
        (Sum.inl i) (Sum.inr j) =
      threeSiteInputExplicit (Sum.inl i) (Sum.inr j) := by
  rw [threeSiteLocalCovariance_eq_explicit]
  fin_cases i <;> fin_cases j <;>
    norm_num [periodicInput, threeSiteInputExplicit, threeSiteInputLiteral,
      threeSiteInputLiteralInt,
      MPS.Internal.phaseSiteEquiv,
      finSumFinEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.castAdd, Fin.addNat, Fin.castLE,
      threeSitePhaseFlatten, threeSiteLocalExplicit, threeSiteLowerBlock,
      threeSiteK, Matrix.fromBlocks,
      Matrix.blockDiagonal_apply, Matrix.reindex_apply,
      Matrix.one_apply, Fintype.sum_sum_type]

lemma threeSiteInput_pq (i j : Fin 9) :
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance)
        (Sum.inr i) (Sum.inl j) =
      threeSiteInputExplicit (Sum.inr i) (Sum.inl j) := by
  rw [threeSiteLocalCovariance_eq_explicit]
  fin_cases i <;> fin_cases j <;>
    norm_num [periodicInput, threeSiteInputExplicit, threeSiteInputLiteral,
      threeSiteInputLiteralInt,
      MPS.Internal.phaseSiteEquiv,
      finSumFinEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.castAdd, Fin.addNat, Fin.castLE,
      threeSitePhaseFlatten, threeSiteLocalExplicit, threeSiteLowerBlock,
      threeSiteK, Matrix.fromBlocks,
      Matrix.blockDiagonal_apply, Matrix.reindex_apply,
      Matrix.one_apply, Fintype.sum_sum_type]

lemma threeSiteInput_pp (i j : Fin 9) :
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance)
        (Sum.inr i) (Sum.inr j) =
      threeSiteInputExplicit (Sum.inr i) (Sum.inr j) := by
  rw [threeSiteLocalCovariance_eq_explicit]
  fin_cases i <;> fin_cases j <;>
    norm_num [periodicInput, threeSiteInputExplicit, threeSiteInputLiteral,
      threeSiteInputLiteralInt,
      MPS.Internal.phaseSiteEquiv,
      finSumFinEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.castAdd, Fin.addNat, Fin.castLE,
      threeSitePhaseFlatten, threeSiteLocalExplicit, threeSiteLowerBlock,
      threeSiteK, Matrix.fromBlocks,
      Matrix.blockDiagonal_apply, Matrix.reindex_apply,
      Matrix.one_apply, Fintype.sum_sum_type]

lemma threeSiteInput_eq_explicit :
    periodicInput (M := 1) (fun _ : Fin 3 => threeSiteLocalCovariance) =
      threeSiteInputExplicit := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact threeSiteInput_qq i j
  · exact threeSiteInput_qp i j
  · exact threeSiteInput_pq i j
  · exact threeSiteInput_pp i j

end MPS.Internal

end Gaussian
