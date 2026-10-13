/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Gaussian kernels and finite local resources for cluster-chain examples. -/

open Matrix

namespace Gaussian

/-- The covariance associated with a centered Gaussian kernel `K = X - iY`,
where `X` is positive definite and `Y` is symmetric. -/
noncomputable def kernelCovariance {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  let X : Matrix (Fin n) (Fin n) ℝ := K.map Complex.re
  let Y : Matrix (Fin n) (Fin n) ℝ := -(K.map Complex.im)
  Matrix.fromBlocks X⁻¹ (X⁻¹ * Y) (Y * X⁻¹) (X + Y * X⁻¹ * Y)

/-- The phase adjacency of a cyclic list of edge weights, with the edge from
site `i` to the next site carrying weight `g i`. -/
def clusterAdjacency (N : ℕ) (g : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j = finRotate N i then g i else if i = finRotate N j then g j else 0

/-- Covariance of a finitely squeezed cluster kernel with squeezing `t`. -/
noncomputable def clusterCovariance {N : ℕ} (t : ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (PhaseIndex N) (PhaseIndex N) ℝ :=
  let Q : Matrix (Fin N) (Fin N) ℝ := t⁻¹ • 1
  let C : Matrix (Fin N) (Fin N) ℝ := t⁻¹ • A
  Matrix.fromBlocks Q C C (t • 1 + t⁻¹ • (A * A))

/-- The commuting nullifier coordinates `p - A q`. -/
def clusterNullifierMap {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (PhaseIndex N) ℝ :=
  fun i x => match x with
    | Sum.inl j => -A i j
    | Sum.inr j => if i = j then 1 else 0

/-- The three-mode kernel on left virtual, right virtual and physical modes.
The global bound `g` is used only to select a finite positive virtual width. -/
noncomputable def clusterLocalKernel (t g gi : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let r : ℝ := t / (4 * (1 + g ^ 2))
  let α : ℂ := (r : ℂ) + Complex.I
  let u : ℂ := Complex.I
  let v : ℂ := -2 * (gi : ℂ) * α
  let k : ℂ := (t : ℂ) - 1 / (2 * α) + 2 * (gi : ℂ) ^ 2 * α
  !![α, 0, u; 0, α, v; u, v, k]

/-- The finite three-mode covariance placed at one cluster site. -/
noncomputable def clusterLocalResource (t g gi : ℝ) :
    Matrix (PhaseIndex 3) (PhaseIndex 3) ℝ :=
  kernelCovariance (clusterLocalKernel t g gi)

end Gaussian

