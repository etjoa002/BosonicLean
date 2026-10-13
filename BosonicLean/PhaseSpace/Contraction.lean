/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.PhaseSpace.ContractionDefs
import BosonicLean.PhaseSpace.Positivity

/-! Admissibility of Gaussian covariance contraction. -/

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

/-- Contracting an admissible covariance along independent real constraints preserves
admissibility when the eliminated constraints have zero symplectic form. -/
theorem isAdmissible_contractCovariance {n m k : ℕ}
    (W : Matrix (Fin k ⊕ PhaseIndex m) (PhaseIndex n) ℝ)
    {γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hγ : IsAdmissible γ) (hW : Function.Injective W.transpose.mulVec)
    (hΩ : W * symplecticForm n * W.transpose =
      Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℝ) 0 0 (symplecticForm m)) :
    (contractionBlock γ W).PosDef ∧ IsAdmissible (contractCovariance γ W) := by
  classical
  let V : Matrix (Fin k ⊕ PhaseIndex m) (Fin k ⊕ PhaseIndex m) ℝ :=
    W * γ * W.transpose
  let E : Matrix (Fin k) (Fin k) ℝ := V.submatrix Sum.inl Sum.inl
  let F : Matrix (Fin k) (PhaseIndex m) ℝ := V.submatrix Sum.inl Sum.inr
  let G : Matrix (PhaseIndex m) (PhaseIndex m) ℝ := V.submatrix Sum.inr Sum.inr
  have hV : V.PosDef := by
    have h := hγ.posDef.conjTranspose_mul_mul_same hW
    have hstar : W.transpose.conjTranspose = W := by
      ext i j
      simp [Matrix.conjTranspose]
    rw [hstar] at h
    simpa [V] using h
  have hE : E.PosDef := hV.submatrix Sum.inl_injective
  let _ : Invertible E := hE.isUnit.invertible
  have hV_blocks : (Matrix.fromBlocks E F Fᴴ G).PosSemidef := by
    rw [show Matrix.fromBlocks E F Fᴴ G = V by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · rfl
      · simpa [E, F, G] using hV.isHermitian.apply (Sum.inr i) (Sum.inl j)
      · rfl]
    exact hV.posSemidef
  have hSchurReal : (G - Fᴴ * E⁻¹ * F).PosSemidef :=
    (hE.fromBlocks₁₁ F G).mp hV_blocks
  have hV21 : V.submatrix Sum.inr Sum.inl = Fᴴ := by
    ext i j
    simpa [F, Matrix.conjTranspose] using
      (hV.isHermitian.apply (Sum.inr i) (Sum.inl j)).symm
  have hcontract : contractCovariance γ W = G - Fᴴ * E⁻¹ * F := by
    change V.submatrix Sum.inr Sum.inr -
      V.submatrix Sum.inr Sum.inl * E⁻¹ * V.submatrix Sum.inl Sum.inr = _
    rw [hV21]
  have hcontractPosSemidef : (contractCovariance γ W).PosSemidef := by
    rw [hcontract]
    exact hSchurReal
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · simpa [contractionBlock, E, V] using hE
  · exact (Matrix.isHermitian_iff_isSymm.mp hcontractPosSemidef.isHermitian).eq
  let Q : Matrix (Fin k ⊕ PhaseIndex m) (Fin k ⊕ PhaseIndex m) ℂ :=
    V.map Complex.ofReal - Complex.I •
      (Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℝ) 0 0
        (symplecticForm m)).map Complex.ofReal
  have hQ : Q.PosSemidef := by
    have h := hγ.2.mul_mul_conjTranspose_same (W.map Complex.ofReal)
    have hstar : (W.map Complex.ofReal).conjTranspose =
        W.transpose.map Complex.ofReal := by
      ext i j
      simp
    rw [hstar, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      ] at h
    have hWγmap :
        W.map Complex.ofReal * γ.map Complex.ofReal * W.transpose.map Complex.ofReal =
          V.map Complex.ofReal := by
      ext i j
      simp [V, Matrix.mul_apply]
    have hWΩmap :
        W.map Complex.ofReal * (symplecticForm n).map Complex.ofReal *
            W.transpose.map Complex.ofReal =
          (W * symplecticForm n * W.transpose).map Complex.ofReal := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hWγmap, hWΩmap, hΩ] at h
    simpa [Q, V] using h
  let EC : Matrix (Fin k) (Fin k) ℂ := E.map Complex.ofReal
  let FC : Matrix (Fin k) (PhaseIndex m) ℂ := F.map Complex.ofReal
  let DC : Matrix (PhaseIndex m) (PhaseIndex m) ℂ :=
    G.map Complex.ofReal - Complex.I • (symplecticForm m).map Complex.ofReal
  have hQ11 : Q.toBlocks₁₁ = EC := by
    ext i j
    simp [Q, EC, E, Matrix.toBlocks₁₁]
  have hQ12 : Q.toBlocks₁₂ = FC := by
    ext i j
    simp [Q, FC, F, Matrix.toBlocks₁₂]
  have hQ22 : Q.toBlocks₂₂ = DC := by
    ext i j
    simp [Q, DC, G, Matrix.toBlocks₂₂]
  have hQ21 : Q.toBlocks₂₁ = Q.toBlocks₁₂ᴴ := by
    ext i j
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose] using
      (hQ.isHermitian.apply (Sum.inr i) (Sum.inl j)).symm
  have hQ_blocks : (Matrix.fromBlocks EC FC FCᴴ DC).PosSemidef := by
    rw [← hQ11, ← hQ12, ← hQ22, ← hQ21, Matrix.fromBlocks_toBlocks]
    exact hQ
  have hECPosSemidef : EC.PosSemidef := by
    have h := hQ_blocks.submatrix (Sum.inl : Fin k → Fin k ⊕ PhaseIndex m)
    rw [show (Matrix.fromBlocks EC FC FCᴴ DC).submatrix Sum.inl Sum.inl = EC by
      ext i j
      rfl] at h
    exact h
  have hmapEC : E.map (⇑Complex.ofRealHom) = EC := by
    ext i j
    rfl
  have hECUnit : IsUnit EC := by
    rw [← hmapEC]
    exact hE.isUnit.map (Complex.ofRealHom.mapMatrix :
      Matrix (Fin k) (Fin k) ℝ →+* Matrix (Fin k) (Fin k) ℂ)
  have hEC : EC.PosDef := hECPosSemidef.posDef_iff_isUnit.mpr hECUnit
  let _ : Invertible EC := hECUnit.invertible
  let _ : Invertible ((Complex.ofRealHom.mapMatrix :
      Matrix (Fin k) (Fin k) ℝ →+* Matrix (Fin k) (Fin k) ℂ) E) :=
    Invertible.map (Complex.ofRealHom.mapMatrix :
      Matrix (Fin k) (Fin k) ℝ →+* Matrix (Fin k) (Fin k) ℂ) E
  have hinvHom : E⁻¹.map (⇑Complex.ofRealHom) =
      (E.map (⇑Complex.ofRealHom))⁻¹ := by
    rw [← Matrix.invOf_eq_nonsing_inv E,
      ← Matrix.invOf_eq_nonsing_inv (E.map (⇑Complex.ofRealHom))]
    simpa only [RingHom.mapMatrix_apply] using
      (map_invOf (Complex.ofRealHom.mapMatrix :
        Matrix (Fin k) (Fin k) ℝ →+* Matrix (Fin k) (Fin k) ℂ) E)
  have hinv : E⁻¹.map Complex.ofReal = EC⁻¹ := by
    calc
      E⁻¹.map Complex.ofReal = E⁻¹.map (⇑Complex.ofRealHom) := by ext i j; rfl
      _ = (E.map (⇑Complex.ofRealHom))⁻¹ := hinvHom
      _ = EC⁻¹ := by rw [hmapEC]
  have hFCstar : Fᴴ.map Complex.ofReal = FCᴴ := by
    ext i j
    simp [FC, Matrix.conjTranspose]
  have hSchurComplex : (DC - FCᴴ * EC⁻¹ * FC).PosSemidef :=
    (hEC.fromBlocks₁₁ FC DC).mp hQ_blocks
  have hmapProduct : (Fᴴ * E⁻¹ * F).map Complex.ofReal =
      Fᴴ.map Complex.ofReal * E⁻¹.map Complex.ofReal * F.map Complex.ofReal := by
    ext i j
    simp [Matrix.mul_apply]
  have hmapSub : (G - Fᴴ * E⁻¹ * F).map Complex.ofReal =
      G.map Complex.ofReal - (Fᴴ * E⁻¹ * F).map Complex.ofReal := by
    ext i j
    simp
  rw [hcontract, hmapSub, hmapProduct, hFCstar, hinv]
  change (G.map Complex.ofReal - FCᴴ * EC⁻¹ * FC -
    Complex.I • (symplecticForm m).map Complex.ofReal).PosSemidef
  rw [show G.map Complex.ofReal - FCᴴ * EC⁻¹ * FC -
      Complex.I • (symplecticForm m).map Complex.ofReal =
      DC - FCᴴ * EC⁻¹ * FC by
    dsimp only [DC]
    abel]
  exact hSchurComplex

end Gaussian
