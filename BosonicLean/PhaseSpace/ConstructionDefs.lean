/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-! Coordinate splitting, independent covariance sums and one-mode diagonal matrices. -/

namespace Gaussian

/-- Split grouped coordinates of n+m modes into the two grouped subsystems. -/
def splitPhase {n m : Nat} : PhaseIndex (n + m) -> PhaseIndex n ⊕ PhaseIndex m
  | Sum.inl i => match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (Sum.inl j)
    | Sum.inr j => Sum.inr (Sum.inl j)
  | Sum.inr i => match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (Sum.inr j)
    | Sum.inr j => Sum.inr (Sum.inr j)

/-- Independent covariance blocks, reordered to grouped position/momentum coordinates. -/
def directSumCov {n m : Nat}
    (A : Matrix (PhaseIndex n) (PhaseIndex n) Real)
    (B : Matrix (PhaseIndex m) (PhaseIndex m) Real) :
    Matrix (PhaseIndex (n + m)) (PhaseIndex (n + m)) Real :=
  (Matrix.fromBlocks A 0 0 B).submatrix splitPhase splitPhase

/-- One-mode covariance with position variance parameter a and momentum parameter b. -/
def diagonalOne (a b : Real) : Matrix (PhaseIndex 1) (PhaseIndex 1) Real :=
  Matrix.diagonal (Sum.elim (fun _ => a) (fun _ => b))

end Gaussian
