import BosonicLean.PhaseSpace.Defs
namespace Gaussian
/-- Eliminated principal block. -/
def contractionBlock {n m k : ℕ}
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (W : Matrix (Fin k ⊕ PhaseIndex m) (PhaseIndex n) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (W * γ * W.transpose).submatrix Sum.inl Sum.inl
/-- Schur complement; admissibility and full row rank ensure invertibility. -/
noncomputable def contractCovariance {n m k : ℕ}
    (γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (W : Matrix (Fin k ⊕ PhaseIndex m) (PhaseIndex n) ℝ) :
    Matrix (PhaseIndex m) (PhaseIndex m) ℝ :=
  let V := W * γ * W.transpose
  V.submatrix Sum.inr Sum.inr -
    V.submatrix Sum.inr Sum.inl * (V.submatrix Sum.inl Sum.inl)⁻¹ *
      V.submatrix Sum.inl Sum.inr
end Gaussian
