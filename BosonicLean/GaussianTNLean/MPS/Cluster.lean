/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.GaussianTNLean.MPS.ClusterDefs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Basic.Complex.BigOperators
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

open scoped ComplexOrder Matrix
open Matrix

namespace Gaussian

private lemma posSemidef_map_ofReal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : (A.map Complex.ofReal).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have hsymm : A.transpose = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
    simpa [Matrix.conjTranspose] using
      congrArg Complex.ofReal (congr_fun (congr_fun hsymm i) j)
  · intro z
    let zr : Fin n → ℝ := fun i => (z i).re
    let zi : Fin n → ℝ := fun i => (z i).im
    have hsymm : A.transpose = A := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
    have hcross :
        (∑ i, ∑ j, zr i * A i j * zi j) =
          ∑ i, ∑ j, zi i * A i j * zr j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hij : A j i = A i j := congr_fun (congr_fun hsymm i) j
      rw [hij]
      ring
    have hquad :
        star z ⬝ᵥ (A.map Complex.ofReal *ᵥ z) =
          (((zr ⬝ᵥ (A *ᵥ zr)) + zi ⬝ᵥ (A *ᵥ zi) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [dotProduct, Matrix.mulVec, Finset.mul_sum, zr, zi,
          Complex.mul_re, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm]
      · simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum,
          Complex.mul_im, Complex.mul_re, map_apply, Pi.star_apply,
          Complex.star_def,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero,
          sub_zero, Complex.conj_re, Complex.conj_im, neg_mul,
          Complex.ofReal_im]
        simpa [zr, zi, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_neg_distrib, sub_eq_add_neg, mul_assoc] using
          (sub_eq_zero.mpr hcross)
    rw [hquad]
    have hre := hA.dotProduct_mulVec_nonneg zr
    have him := hA.dotProduct_mulVec_nonneg zi
    exact_mod_cast add_nonneg hre him

theorem kernelCovariance_admissible {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : K.transpose = K) (hX : (K.map Complex.re).PosDef) :
    IsAdmissible (kernelCovariance K) := by
  classical
  let X : Matrix (Fin n) (Fin n) ℝ := K.map Complex.re
  let Y : Matrix (Fin n) (Fin n) ℝ := -(K.map Complex.im)
  have hXs : X.transpose = X := by
    ext i j
    exact congrArg Complex.re (congr_fun (congr_fun hK i) j)
  have hYs : Y.transpose = Y := by
    ext i j
    change -(K j i).im = -(K i j).im
    exact congrArg (fun z : ℂ => -z.im) (congr_fun (congr_fun hK i) j)
  have hXdef : (K.map Complex.re).PosDef = X.PosDef := by rfl
  have hX' : X.PosDef := hXdef.mp hX
  let _ : Invertible X := hX'.isUnit.invertible
  have hXiS : (X⁻¹).transpose = X⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hXs]
  let XC : Matrix (Fin n) (Fin n) ℂ := X.map Complex.ofReal
  let YC : Matrix (Fin n) (Fin n) ℂ := Y.map Complex.ofReal
  let XiC : Matrix (Fin n) (Fin n) ℂ := X⁻¹.map Complex.ofReal
  let C : Matrix (Fin n) (Fin n) ℂ := YC - Complex.I • XC
  let B : Matrix (Fin n) (PhaseIndex n) ℂ := fun i x =>
    Sum.elim (fun j => (1 : Matrix (Fin n) (Fin n) ℂ) i j)
      (fun j => C i j) x
  have hXiC : XiC.PosSemidef := by
    exact posSemidef_map_ofReal hX'.inv.posSemidef
  have hXiXC : XiC * XC = 1 := by
    change X⁻¹.map (⇑Complex.ofRealHom) * X.map (⇑Complex.ofRealHom) = 1
    rw [← Matrix.map_mul]
    simp
  have hXXiC : XC * XiC = 1 := by
    change X.map (⇑Complex.ofRealHom) * X⁻¹.map (⇑Complex.ofRealHom) = 1
    rw [← Matrix.map_mul]
    simp
  have hBq (i x : Fin n) :
      B.conjTranspose (Sum.inl i) x =
        (1 : Matrix (Fin n) (Fin n) ℂ) i x := by
    change star (B x (Sum.inl i)) = _
    simp [B, Matrix.one_apply, eq_comm]
  have hBp (i x : Fin n) :
      B.conjTranspose (Sum.inr i) x = YC i x + Complex.I * XC i x := by
    change star (B x (Sum.inr i)) = _
    have hXij : X x i = X i x := congr_fun (congr_fun hXs i) x
    have hYij : Y x i = Y i x := congr_fun (congr_fun hYs i) x
    simp [B, C, XC, YC, Complex.star_def, hXij, hYij]
  have hBprod :
      B.conjTranspose * XiC * B =
        Matrix.fromBlocks XiC (XiC * C)
          ((YC + Complex.I • XC) * XiC)
          ((YC + Complex.I • XC) * XiC * C) := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · simp only [Matrix.mul_apply]
      simp_rw [hBq]
      simp [Matrix.fromBlocks, B, Matrix.one_apply]
    · simp only [Matrix.mul_apply]
      simp_rw [hBq]
      simp [Matrix.fromBlocks, B, Matrix.one_apply]
      change (XiC * C) i j = (XiC * C) i j
      rfl
    · simp only [Matrix.mul_apply]
      simp_rw [hBp]
      simp [Matrix.fromBlocks, B, Matrix.one_apply]
      change ((YC + Complex.I • XC) * XiC) i j =
        ((YC + Complex.I • XC) * XiC) i j
      rfl
    · simp only [Matrix.mul_apply]
      simp_rw [hBp]
      simp [Matrix.fromBlocks, B, Matrix.one_apply]
      change ((YC + Complex.I • XC) * XiC * C) i j =
        ((YC + Complex.I • XC) * XiC * C) i j
      rfl
  have hXiYmap :
      (X⁻¹ * Y).map Complex.ofReal = XiC * YC := by
    ext i j
    simp [XiC, YC, Matrix.mul_apply]
  have hYXimap :
      (Y * X⁻¹).map Complex.ofReal = YC * XiC := by
    ext i j
    simp [XiC, YC, Matrix.mul_apply]
  have hbottommap :
      (X + Y * X⁻¹ * Y).map Complex.ofReal = XC + YC * XiC * YC := by
    ext i j
    simp [XC, YC, XiC, Matrix.mul_apply, Finset.mul_sum]
  have h12 :
      XiC * C = (X⁻¹ * Y).map Complex.ofReal -
        Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp only [C]
    rw [Matrix.mul_sub, Matrix.mul_smul, hXiXC, hXiYmap]
  have h21 :
      (YC + Complex.I • XC) * XiC =
        (Y * X⁻¹).map Complex.ofReal +
          Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.add_mul, Matrix.smul_mul, hXXiC, hYXimap]
  have h22alg :
      (YC + Complex.I • XC) * XiC * C = XC + YC * XiC * YC := by
    dsimp only [C]
    rw [h21, Matrix.add_mul, Matrix.mul_sub]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hXiXC,
      hYXimap]
    simp only [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel
  have hfactor :
      (kernelCovariance K).map Complex.ofReal -
          Complex.I • (symplecticForm n).map Complex.ofReal =
        B.conjTranspose * XiC * B := by
    change (Matrix.fromBlocks X⁻¹ (X⁻¹ * Y) (Y * X⁻¹)
        (X + Y * X⁻¹ * Y)).map Complex.ofReal -
          Complex.I • (symplecticForm n).map Complex.ofReal =
        B.conjTranspose * XiC * B
    rw [hBprod, h22alg, h12, h21, ← hbottommap]
    ext a b
    rcases a with i | i <;> rcases b with j | j
    all_goals
      simp [XiC, symplecticForm, Matrix.J, Matrix.fromBlocks,
        Matrix.one_apply]
    all_goals by_cases hij : i = j <;> simp [hij]
  refine ⟨?_, ?_⟩
  · change (Matrix.fromBlocks X⁻¹ (X⁻¹ * Y) (Y * X⁻¹)
        (X + Y * X⁻¹ * Y)).transpose =
      Matrix.fromBlocks X⁻¹ (X⁻¹ * Y) (Y * X⁻¹) (X + Y * X⁻¹ * Y)
    simp [Matrix.fromBlocks_transpose, Matrix.transpose_mul, Matrix.mul_assoc,
      hXiS, hXs, hYs]
  · rw [hfactor]
    exact hXiC.conjTranspose_mul_mul_same B

theorem clusterLocalResource_admissible (t g gi : ℝ) (ht : 0 < t)
    (hgi : gi = 0 ∨ gi = g) : IsAdmissible (clusterLocalResource t g gi) := by
  classical
  let r : ℝ := t / (4 * (1 + g ^ 2))
  let s : ℝ := t - r / (2 * (1 + r ^ 2)) - 2 * gi ^ 2 * r
  have hgden : 0 < 1 + g ^ 2 := by linarith [sq_nonneg g]
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hrrel : 4 * (1 + g ^ 2) * r = t := by
    dsimp only [r]
    field_simp
  have hfrac : r / (2 * (1 + r ^ 2)) ≤ r / 2 := by
    have hd : 0 < 2 * (1 + r ^ 2) := by positivity
    rw [div_le_iff₀ hd]
    calc
      r ≤ r + r * r ^ 2 := le_add_of_nonneg_right (mul_nonneg hr.le (sq_nonneg r))
      _ = r / 2 * (2 * (1 + r ^ 2)) := by ring
  have hgiSq : gi ^ 2 ≤ g ^ 2 := by
    rcases hgi with rfl | rfl
    · simpa using sq_nonneg g
    · exact le_rfl
  have hgiTerm : 2 * gi ^ 2 * r ≤ 2 * g ^ 2 * r := by
    have hgiSq2 : 2 * gi ^ 2 ≤ 2 * g ^ 2 :=
      mul_le_mul_of_nonneg_left hgiSq (by norm_num)
    exact mul_le_mul_of_nonneg_right hgiSq2 hr.le
  have hbudget : r / 2 + 2 * g ^ 2 * r ≤ t / 2 := by
    linarith [hrrel, hr]
  have hs : 0 < s := by
    dsimp only [s]
    linarith [hfrac, hgiTerm, hbudget]
  have hsymm : (clusterLocalKernel t g gi).transpose =
      clusterLocalKernel t g gi := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [clusterLocalKernel]
  have hrecip :
      (1 / (2 * ((r : ℂ) + Complex.I))).re =
        r / (2 * (1 + r ^ 2)) := by
    rw [one_div, Complex.inv_re]
    simp [Complex.normSq]
    have h2 : 2 + r ^ 2 * 2 ≠ 0 := ne_of_gt (by positivity)
    have h4 : 4 + r ^ 2 * 4 ≠ 0 := ne_of_gt (by positivity)
    field_simp [h2, h4]
    <;> ring
  have hreal :
      (clusterLocalKernel t g gi).map Complex.re =
        !![r, 0, 0;
           0, r, -2 * gi * r;
           0, -2 * gi * r,
             t - r / (2 * (1 + r ^ 2)) + 2 * gi ^ 2 * r] := by
    dsimp only [clusterLocalKernel]
    change
      (!![(r : ℂ) + Complex.I, 0, Complex.I;
          0, (r : ℂ) + Complex.I,
            -2 * (gi : ℂ) * ((r : ℂ) + Complex.I);
          Complex.I, -2 * (gi : ℂ) * ((r : ℂ) + Complex.I),
            (t : ℂ) - 1 / (2 * ((r : ℂ) + Complex.I)) +
              2 * (gi : ℂ) ^ 2 * ((r : ℂ) + Complex.I)] :
        Matrix (Fin 3) (Fin 3) ℂ).map Complex.re = _
    have hden1 : 1 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hden2 : 2 + r ^ 2 * 2 ≠ 0 := ne_of_gt (by positivity)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hrecip, Complex.normSq, pow_two, Complex.mul_re,
        Complex.mul_im]
    all_goals field_simp [hden1, hden2] <;> ring
  change IsAdmissible (kernelCovariance (clusterLocalKernel t g gi))
  apply kernelCovariance_admissible (K := clusterLocalKernel t g gi) hsymm
  rw [hreal]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro x hx
    have hnonzero : x 0 ≠ 0 ∨ x 1 - 2 * gi * x 2 ≠ 0 ∨ x 2 ≠ 0 := by
      by_contra h
      simp only [not_or, not_ne_iff] at h
      apply hx
      have hx1 : x 1 = 0 := by
        have hh := h.2.1
        rw [h.2.2] at hh
        simpa using hh
      funext i
      fin_cases i
      · exact h.1
      · exact hx1
      · exact h.2.2
    have hquad :
        star x ⬝ᵥ
            (!![r, 0, 0;
               0, r, -2 * gi * r;
               0, -2 * gi * r,
                 t - r / (2 * (1 + r ^ 2)) + 2 * gi ^ 2 * r] *ᵥ x) =
          r * (x 0) ^ 2 + r * (x 1 - 2 * gi * x 2) ^ 2 + s * (x 2) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, s]
      ring
    rw [hquad]
    rcases hnonzero with h0 | h1 | h2
    · have hp : 0 < r * (x 0) ^ 2 := mul_pos hr (sq_pos_of_ne_zero h0)
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg hp
          (mul_nonneg hr.le (sq_nonneg (x 1 - 2 * gi * x 2))))
        (mul_nonneg hs.le (sq_nonneg (x 2)))
    · have hp : 0 < r * (x 1 - 2 * gi * x 2) ^ 2 :=
        mul_pos hr (sq_pos_of_ne_zero h1)
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_nonneg_of_pos (mul_nonneg hr.le (sq_nonneg (x 0))) hp)
        (mul_nonneg hs.le (sq_nonneg (x 2)))
    · have hp : 0 < s * (x 2) ^ 2 := mul_pos hs (sq_pos_of_ne_zero h2)
      exact add_pos_of_nonneg_of_pos
        (add_nonneg (mul_nonneg hr.le (sq_nonneg (x 0)))
          (mul_nonneg hr.le (sq_nonneg (x 1 - 2 * gi * x 2)))) hp

private lemma inverse_principal_schur
    {e r : Type*} [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]
    (X : Matrix (e ⊕ r) (e ⊕ r) ℝ) (hX : X.PosDef) :
    let T := X⁻¹
    let P := T.submatrix Sum.inl Sum.inl
    let L := T.submatrix Sum.inl Sum.inr
    let M := T.submatrix Sum.inr Sum.inl
    let N := T.submatrix Sum.inr Sum.inr
    let D := X.submatrix Sum.inr Sum.inr
    N - M * P⁻¹ * L = D⁻¹ := by
  classical
  dsimp only
  let T : Matrix (e ⊕ r) (e ⊕ r) ℝ := X⁻¹
  let P : Matrix e e ℝ := T.submatrix Sum.inl Sum.inl
  let L : Matrix e r ℝ := T.submatrix Sum.inl Sum.inr
  let M : Matrix r e ℝ := T.submatrix Sum.inr Sum.inl
  let N : Matrix r r ℝ := T.submatrix Sum.inr Sum.inr
  let D : Matrix r r ℝ := X.submatrix Sum.inr Sum.inr
  have hT : T.PosDef := by
    dsimp only [T]
    exact hX.inv
  have hP : P.PosDef := hT.submatrix Sum.inl_injective
  have hD : D.PosDef := hX.submatrix Sum.inr_injective
  let _ : Invertible X := hX.isUnit.invertible
  let _ : Invertible T := hT.isUnit.invertible
  let _ : Invertible P := hP.isUnit.invertible
  let _ : Invertible D := hD.isUnit.invertible
  have hblocks : Matrix.fromBlocks P L M N = T := by
    exact Matrix.fromBlocks_toBlocks T
  let _ : Invertible (Matrix.fromBlocks P L M N) :=
    Invertible.copy (inferInstance : Invertible T) _ hblocks
  let Q : Matrix r r ℝ := N - M * ⅟P * L
  let _ : Invertible Q := by
    dsimp only [Q]
    exact Matrix.invertibleOfFromBlocks₁₁Invertible P L M N
  have hinv := Matrix.invOf_fromBlocks₁₁_eq P L M N
  have hbottom : ⅟Q = D := by
    have hfull : (Matrix.fromBlocks P L M N)⁻¹ = X := by
      rw [hblocks]
      dsimp only [T]
      exact Matrix.inv_inv_of_invertible X
    have hfullInvOf : ⅟(Matrix.fromBlocks P L M N) = X := by
      rw [Matrix.invOf_eq_nonsing_inv]
      exact hfull
    rw [hfullInvOf] at hinv
    have := congrArg (fun Z => Z.submatrix Sum.inr Sum.inr) hinv
    change D = ⅟Q at this
    exact this.symm
  have hQ : Q = ⅟D := by
    calc
      Q = ⅟(⅟Q) := (invOf_invOf Q).symm
      _ = ⅟D := Invertible.congr (⅟Q) D hbottom
  rw [← Matrix.invOf_eq_nonsing_inv P, ← Matrix.invOf_eq_nonsing_inv D]
  calc
    N - M * ⅟P * L = Q := rfl
    _ = ⅟D := hQ

private lemma kernelCovariance_position_condition_blocks
    {e r : Type*} [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]
    (X Y : Matrix (e ⊕ r) (e ⊕ r) ℝ) (hX : X.PosDef) :
    let T := X⁻¹
    let P := T.submatrix Sum.inl Sum.inl
    let L := T.submatrix Sum.inl Sum.inr
    let M := T.submatrix Sum.inr Sum.inl
    let N := T.submatrix Sum.inr Sum.inr
    let D := X.submatrix Sum.inr Sum.inr
    let F := Y.submatrix Sum.inl Sum.inr
    let H := Y.submatrix Sum.inr Sum.inl
    let G := Y.submatrix Sum.inr Sum.inr
    let U := P * F + L * G
    let V := M * F + N * G
    let C := H * P + G * M
    let R := H * L + G * N
    let S := D + C * F + R * G
    Matrix.fromBlocks
        (N - M * P⁻¹ * L)
        (V - M * P⁻¹ * U)
        (R - C * P⁻¹ * L)
        (S - C * P⁻¹ * U) =
      Matrix.fromBlocks D⁻¹ (D⁻¹ * G) (G * D⁻¹) (D + G * D⁻¹ * G) := by
  classical
  dsimp only
  let T : Matrix (e ⊕ r) (e ⊕ r) ℝ := X⁻¹
  let P : Matrix e e ℝ := T.submatrix Sum.inl Sum.inl
  let L : Matrix e r ℝ := T.submatrix Sum.inl Sum.inr
  let M : Matrix r e ℝ := T.submatrix Sum.inr Sum.inl
  let N : Matrix r r ℝ := T.submatrix Sum.inr Sum.inr
  let D : Matrix r r ℝ := X.submatrix Sum.inr Sum.inr
  let F : Matrix e r ℝ := Y.submatrix Sum.inl Sum.inr
  let H : Matrix r e ℝ := Y.submatrix Sum.inr Sum.inl
  let G : Matrix r r ℝ := Y.submatrix Sum.inr Sum.inr
  let U : Matrix e r ℝ := P * F + L * G
  let V : Matrix r r ℝ := M * F + N * G
  let C : Matrix r e ℝ := H * P + G * M
  let R : Matrix r r ℝ := H * L + G * N
  let S : Matrix r r ℝ := D + C * F + R * G
  have hT : T.PosDef := by
    dsimp only [T]
    exact hX.inv
  have hP : P.PosDef := hT.submatrix Sum.inl_injective
  let _ : Invertible P := hP.isUnit.invertible
  have hPiP : P⁻¹ * P = 1 := by
    rw [← Matrix.invOf_eq_nonsing_inv]
    exact invOf_mul_self P
  have hPPi : P * P⁻¹ = 1 := by
    rw [← Matrix.invOf_eq_nonsing_inv]
    exact mul_invOf_self P
  have hPiPF : P⁻¹ * (P * F) = F := by
    rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hqq : N - M * P⁻¹ * L = D⁻¹ := by
    exact inverse_principal_schur X hX
  have hMU : M * P⁻¹ * U = M * F + (M * P⁻¹ * L) * G := by
    dsimp only [U]
    rw [Matrix.mul_add]
    rw [Matrix.mul_assoc M P⁻¹ (P * F), hPiPF]
    rw [← Matrix.mul_assoc (M * P⁻¹) L G]
  have hqp : V - M * P⁻¹ * U = D⁻¹ * G := by
    calc
      V - M * P⁻¹ * U = (N - M * P⁻¹ * L) * G := by
        dsimp only [V]
        rw [hMU, Matrix.sub_mul]
        abel
      _ = D⁻¹ * G := by rw [hqq]
  have hCL : C * P⁻¹ * L = H * L + G * (M * P⁻¹ * L) := by
    dsimp only [C]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hPPi, Matrix.mul_one]
  have hpq : R - C * P⁻¹ * L = G * D⁻¹ := by
    calc
      R - C * P⁻¹ * L = G * (N - M * P⁻¹ * L) := by
        dsimp only [R]
        rw [hCL, Matrix.mul_sub]
        abel
      _ = G * D⁻¹ := by rw [hqq]
  have hCU : C * P⁻¹ * U = C * F + (C * P⁻¹ * L) * G := by
    dsimp only [U]
    rw [Matrix.mul_add]
    rw [Matrix.mul_assoc C P⁻¹ (P * F), hPiPF]
    rw [← Matrix.mul_assoc (C * P⁻¹) L G]
  have hpp : S - C * P⁻¹ * U = D + G * D⁻¹ * G := by
    calc
      S - C * P⁻¹ * U = D + (R - C * P⁻¹ * L) * G := by
        dsimp only [S]
        rw [hCU, Matrix.sub_mul]
        abel
      _ = D + G * D⁻¹ * G := by rw [hpq]
  rw [hqq, hqp, hpq, hpp]

private noncomputable def kernelCovarianceBlocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks X⁻¹ (X⁻¹ * Y) (Y * X⁻¹) (X + Y * X⁻¹ * Y)

private def positionConditionSelect {e r : Type*} :
    e ⊕ (r ⊕ r) → (e ⊕ r) ⊕ (e ⊕ r)
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr (Sum.inl i) => Sum.inl (Sum.inr i)
  | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)

private noncomputable def conditionFirstBlock
    {e r : Type*} [Fintype e] [DecidableEq e]
    (V : Matrix (e ⊕ r) (e ⊕ r) ℝ) : Matrix r r ℝ :=
  V.submatrix Sum.inr Sum.inr -
    V.submatrix Sum.inr Sum.inl * (V.submatrix Sum.inl Sum.inl)⁻¹ *
      V.submatrix Sum.inl Sum.inr

private lemma kernelCovariance_condition_position
    {e r : Type*} [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]
    (X Y : Matrix (e ⊕ r) (e ⊕ r) ℝ) (hX : X.PosDef) :
    conditionFirstBlock
        ((kernelCovarianceBlocks X Y).submatrix
          positionConditionSelect positionConditionSelect) =
      kernelCovarianceBlocks
        (X.submatrix Sum.inr Sum.inr) (Y.submatrix Sum.inr Sum.inr) := by
  classical
  let T : Matrix (e ⊕ r) (e ⊕ r) ℝ := X⁻¹
  let P : Matrix e e ℝ := T.submatrix Sum.inl Sum.inl
  let L : Matrix e r ℝ := T.submatrix Sum.inl Sum.inr
  let M : Matrix r e ℝ := T.submatrix Sum.inr Sum.inl
  let N : Matrix r r ℝ := T.submatrix Sum.inr Sum.inr
  let D : Matrix r r ℝ := X.submatrix Sum.inr Sum.inr
  let E : Matrix e e ℝ := Y.submatrix Sum.inl Sum.inl
  let F : Matrix e r ℝ := Y.submatrix Sum.inl Sum.inr
  let H : Matrix r e ℝ := Y.submatrix Sum.inr Sum.inl
  let G : Matrix r r ℝ := Y.submatrix Sum.inr Sum.inr
  let U : Matrix e r ℝ := P * F + L * G
  let W : Matrix r e ℝ := M * E + N * H
  let V : Matrix r r ℝ := M * F + N * G
  let C : Matrix r e ℝ := H * P + G * M
  let R : Matrix r r ℝ := H * L + G * N
  let S : Matrix r r ℝ := D + C * F + R * G
  let Qrow : Matrix e (r ⊕ r) ℝ := fun i x =>
    Sum.elim (fun j => L i j) (fun j => U i j) x
  let Rcol : Matrix (r ⊕ r) e ℝ := fun x i =>
    Sum.elim (fun j => M j i) (fun j => C j i) x
  have hTblocks : Matrix.fromBlocks P L M N = T :=
    Matrix.fromBlocks_toBlocks T
  have hYblocks : Matrix.fromBlocks E F H G = Y :=
    Matrix.fromBlocks_toBlocks Y
  have hTY : T * Y = Matrix.fromBlocks (P * E + L * H) U W V := by
    calc
      T * Y = Matrix.fromBlocks P L M N * Matrix.fromBlocks E F H G := by
        rw [hTblocks, hYblocks]
      _ = Matrix.fromBlocks (P * E + L * H) U W V := by
        rw [Matrix.fromBlocks_multiply]
  have hYT : Y * T =
      Matrix.fromBlocks (E * P + F * M) (E * L + F * N) C R := by
    calc
      Y * T = Matrix.fromBlocks E F H G * Matrix.fromBlocks P L M N := by
        rw [hTblocks, hYblocks]
      _ = Matrix.fromBlocks (E * P + F * M) (E * L + F * N) C R := by
        rw [Matrix.fromBlocks_multiply]
  have hYTY : Y * T * Y =
      Matrix.fromBlocks
        ((E * P + F * M) * E + (E * L + F * N) * H)
        ((E * P + F * M) * F + (E * L + F * N) * G)
        (C * E + R * H) (C * F + R * G) := by
    calc
      Y * T * Y =
          Matrix.fromBlocks (E * P + F * M) (E * L + F * N) C R *
            Matrix.fromBlocks E F H G := by rw [hYT, hYblocks]
      _ = _ := by rw [Matrix.fromBlocks_multiply]
  have hpp : (X + Y * T * Y).submatrix Sum.inr Sum.inr = S := by
    have h22 := congrArg (fun Z => Z.submatrix Sum.inr Sum.inr) hYTY
    change (Y * T * Y).submatrix Sum.inr Sum.inr = C * F + R * G at h22
    ext i j
    change X (Sum.inr i) (Sum.inr j) + (Y * T * Y) (Sum.inr i) (Sum.inr j) =
      (D + C * F + R * G) i j
    rw [show (Y * T * Y) (Sum.inr i) (Sum.inr j) = (C * F + R * G) i j by
      exact congr_fun (congr_fun h22 i) j]
    change D i j + ((C * F) i j + (R * G) i j) =
      (D i j + (C * F) i j) + (R * G) i j
    ring
  have hselected :
      (kernelCovarianceBlocks X Y).submatrix
          positionConditionSelect positionConditionSelect =
        Matrix.fromBlocks P Qrow Rcol (Matrix.fromBlocks N V R S) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · rfl
      · rcases j with j | j
        · rfl
        · exact congr_fun (congr_fun hTY (Sum.inl i)) (Sum.inr j)
    · rcases i with i | i
      · rcases j with j | j
        · rfl
        · rcases j with j | j
          · rfl
          · exact congr_fun (congr_fun hTY (Sum.inr i)) (Sum.inr j)
      · rcases j with j | j
        · exact congr_fun (congr_fun hYT (Sum.inr i)) (Sum.inl j)
        · rcases j with j | j
          · exact congr_fun (congr_fun hYT (Sum.inr i)) (Sum.inr j)
          · exact congr_fun (congr_fun hpp i) j
  have hprod : Rcol * P⁻¹ * Qrow =
      Matrix.fromBlocks
        (M * P⁻¹ * L) (M * P⁻¹ * U)
        (C * P⁻¹ * L) (C * P⁻¹ * U) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hsub :
      Matrix.fromBlocks N V R S -
          Matrix.fromBlocks
            (M * P⁻¹ * L) (M * P⁻¹ * U)
            (C * P⁻¹ * L) (C * P⁻¹ * U) =
        Matrix.fromBlocks
          (N - M * P⁻¹ * L) (V - M * P⁻¹ * U)
          (R - C * P⁻¹ * L) (S - C * P⁻¹ * U) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  unfold conditionFirstBlock
  rw [hselected]
  change Matrix.fromBlocks N V R S - Rcol * P⁻¹ * Qrow =
    kernelCovarianceBlocks D G
  rw [hprod, hsub]
  change _ = Matrix.fromBlocks D⁻¹ (D⁻¹ * G) (G * D⁻¹) (D + G * D⁻¹ * G)
  exact kernelCovariance_position_condition_blocks X Y hX

private def sparsePeriodicCoupling {N : ℕ} (u : ℂ) (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun x j => (if x = j then u else 0) -
    if x = finRotate N j then v j else 0

@[simp] private lemma sum_indicator_mul_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a b : ι) (p q : ℂ) :
    (∑ x : ι, (if x = a then p else 0) * (if x = b then q else 0)) =
      if a = b then p * q else 0 := by
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxa : x = a
    · simp [hxa, hab]
    · simp [hxa]

private lemma sparsePeriodicCoupling_transpose_mul {N : ℕ} (u : ℂ)
    (v : Fin N → ℂ) (hfix : ∀ i, finRotate N i ≠ i)
    (htwo : ∀ i, finRotate N (finRotate N i) ≠ i) :
    (sparsePeriodicCoupling u v).transpose * sparsePeriodicCoupling u v =
      fun i j =>
        if i = j then u ^ 2 + (v i) ^ 2
        else if j = finRotate N i then -u * v i
        else if i = finRotate N j then -u * v j
        else 0 := by
  classical
  ext i j
  change
    (∑ x,
      ((if x = i then u else 0) - if x = finRotate N i then v i else 0) *
      ((if x = j then u else 0) - if x = finRotate N j then v j else 0)) = _
  rw [show
      (∑ x,
        ((if x = i then u else 0) - if x = finRotate N i then v i else 0) *
        ((if x = j then u else 0) - if x = finRotate N j then v j else 0)) =
        (∑ x, (if x = i then u else 0) * (if x = j then u else 0)) -
        (∑ x, (if x = i then u else 0) *
          (if x = finRotate N j then v j else 0)) -
        (∑ x, (if x = finRotate N i then v i else 0) *
          (if x = j then u else 0)) +
        (∑ x, (if x = finRotate N i then v i else 0) *
          (if x = finRotate N j then v j else 0)) by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring]
  simp only [sum_indicator_mul_indicator]
  by_cases hij : i = j
  · subst j
    have hif : i ≠ finRotate N i := (hfix i).symm
    rw [ite_eq_left rfl, ite_eq_right hif, ite_eq_right (hfix i), ite_eq_left rfl,
      ite_eq_left rfl]
    ring
  · by_cases hj : j = finRotate N i
    · subst j
      have hif : i ≠ finRotate N i := (hfix i).symm
      have htwo' : i ≠ finRotate N (finRotate N i) := (htwo i).symm
      have hnext : finRotate N i ≠ finRotate N (finRotate N i) :=
        (hfix (finRotate N i)).symm
      rw [ite_eq_right hif, ite_eq_right htwo', ite_eq_left rfl, ite_eq_right hnext,
        ite_eq_right hif, ite_eq_left rfl]
      ring
    · by_cases hi : i = finRotate N j
      · subst i
        have hjf : finRotate N j ≠ j := hfix j
        have htwo' : finRotate N (finRotate N j) ≠ j := htwo j
        have hnext : finRotate N (finRotate N j) ≠ finRotate N j :=
          hfix (finRotate N j)
        rw [ite_eq_right hjf, ite_eq_left rfl, ite_eq_right htwo', ite_eq_right hnext,
          ite_eq_right hjf, ite_eq_right htwo'.symm, ite_eq_left rfl]
        ring
      · have hsi : finRotate N i ≠ j := fun h => hj h.symm
        have hsij : finRotate N i ≠ finRotate N j := fun h =>
          hij ((finRotate N).injective h)
        rw [ite_eq_right hij, ite_eq_right hi, ite_eq_right hsi, ite_eq_right hsij,
          ite_eq_right hij, ite_eq_right hj, ite_eq_right hi]
        ring

private lemma finRotate_ne_self_of_three {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    finRotate N i ≠ i := by
  have hi : i ∈ (finRotate N).support := by
    rw [support_finRotate_of_le (by omega : 2 ≤ N)]
    exact Finset.mem_univ i
  exact Equiv.Perm.mem_support.mp hi

private lemma finRotate_two_ne_self_of_three {N : ℕ} (hN : 3 ≤ N)
    (i : Fin N) : finRotate N (finRotate N i) ≠ i := by
  let _ : NeZero N := ⟨by omega⟩
  rw [finRotate_apply, finRotate_apply]
  intro h
  have htwo : (1 + 1 : Fin N) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using h
  have hv := congrArg Fin.val htwo
  norm_num [Fin.add_def, Nat.mod_eq_of_lt (by omega : 2 < N)] at hv

private noncomputable def periodicVirtualKernel {N : ℕ} (α : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (2 * α) • 1

private noncomputable def periodicPhysicalKernel {N : ℕ} (t : ℝ) (α : ℂ)
    (g : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    (t : ℂ) - 1 / (2 * α) + 2 * (g i : ℂ) ^ 2 * α

private noncomputable def periodicCouplingKernel {N : ℕ} (α : ℂ)
    (g : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  sparsePeriodicCoupling Complex.I fun i => -2 * (g i : ℂ) * α

private lemma periodic_effectiveKernel {N : ℕ} (hN : 3 ≤ N) (t : ℝ)
    (α : ℂ) (hα : α ≠ 0) (g : Fin N → ℝ) :
    periodicPhysicalKernel t α g -
        (periodicCouplingKernel α g).transpose *
          (periodicVirtualKernel (N := N) α)⁻¹ *
            periodicCouplingKernel α g =
      (t : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        Complex.I • (clusterAdjacency N g).map Complex.ofReal := by
  classical
  let V := periodicCouplingKernel α g
  have hfix : ∀ i, finRotate N i ≠ i := finRotate_ne_self_of_three hN
  have htwo : ∀ i, finRotate N (finRotate N i) ≠ i :=
    finRotate_two_ne_self_of_three hN
  have h2α : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hUinv : (periodicVirtualKernel (N := N) α)⁻¹ =
      (1 / (2 * α)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    apply Matrix.inv_eq_left_inv
    change ((1 / (2 * α)) • (1 : Matrix (Fin N) (Fin N) ℂ)) *
        ((2 * α) • 1) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [div_mul_cancel₀ _ h2α, one_smul]
  have hV : V.transpose * V = fun i j =>
      if i = j then Complex.I ^ 2 + (-2 * (g i : ℂ) * α) ^ 2
      else if j = finRotate N i then -Complex.I * (-2 * (g i : ℂ) * α)
      else if i = finRotate N j then -Complex.I * (-2 * (g j : ℂ) * α)
      else 0 := by
    exact sparsePeriodicCoupling_transpose_mul Complex.I
      (fun i => -2 * (g i : ℂ) * α) hfix htwo
  have hprod : V.transpose *
        ((1 / (2 * α)) • (1 : Matrix (Fin N) (Fin N) ℂ)) * V =
      (1 / (2 * α)) • (V.transpose * V) := by
    simp
  change periodicPhysicalKernel t α g - V.transpose *
      (periodicVirtualKernel (N := N) α)⁻¹ * V = _
  rw [hUinv, hprod]
  ext i j
  simp only [periodicPhysicalKernel, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.map_apply,
    clusterAdjacency]
  change
    (if i = j then
        (t : ℂ) - 1 / (2 * α) + 2 * (g i : ℂ) ^ 2 * α
      else 0) -
      (1 / (2 * α)) * (V.transpose * V) i j =
      (t : ℂ) * (if i = j then 1 else 0) - Complex.I *
        (((if j = finRotate N i then g i
        else if i = finRotate N j then g j else 0) : ℝ) : ℂ)
  rw [show (V.transpose * V) i j =
      (if i = j then Complex.I ^ 2 + (-2 * (g i : ℂ) * α) ^ 2
      else if j = finRotate N i then -Complex.I * (-2 * (g i : ℂ) * α)
      else if i = finRotate N j then -Complex.I * (-2 * (g j : ℂ) * α)
      else 0) by exact congr_fun (congr_fun hV i) j]
  by_cases hij : i = j
  · subst j
    have hif : i ≠ finRotate N i := (hfix i).symm
    simp only [ite_eq_right hif, Complex.I_sq]
    simp
    field_simp [hα] <;> ring
  · by_cases hj : j = finRotate N i
    · simp only [ite_eq_right hij, ite_eq_left hj]
      simp
      field_simp [hα] <;> ring
    · by_cases hi : i = finRotate N j
      · simp only [ite_eq_right hij, ite_eq_right hj, ite_eq_left hi]
        simp
        field_simp [hα] <;> ring
      · simp only [ite_eq_right hij, ite_eq_right hj, ite_eq_right hi]
        norm_num

/-! ## Constructive accretive inverse

A complex matrix whose real part is positive definite is invertible, and the real part of its
inverse is invertible. This supplies the invertibility hypotheses of the partial Fourier
calculation below. -/

private lemma complex_pair_mul
    {n : Type*} [Fintype n]
    (A B C D : Matrix n n ℂ) :
    (A - Complex.I • B) * (C + Complex.I • D) =
      (A * C + B * D) + Complex.I • (A * D - B * C) := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
  match_scalars
  all_goals simp [Complex.I_mul_I]

/-- Constructive inverse for `X - iY`.  Positivity of `X` makes
`M = X + Y X⁻¹ Y` positive definite; its inverse is the real part of the
displayed right inverse. -/
private lemma accretive_inverse_of_parts
    {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.transpose = Y) :
    let XC := X.map Complex.ofReal
    let YC := Y.map Complex.ofReal
    let U := XC - Complex.I • YC
    IsUnit U.det ∧ IsUnit (U⁻¹.map Complex.re) := by
  classical
  dsimp only
  let Xi : Matrix n n ℝ := X⁻¹
  let M : Matrix n n ℝ := X + Y * Xi * Y
  let P : Matrix n n ℝ := M⁻¹
  let R : Matrix n n ℝ := Xi * Y * P
  let XC : Matrix n n ℂ := X.map Complex.ofReal
  let YC : Matrix n n ℂ := Y.map Complex.ofReal
  let PC : Matrix n n ℂ := P.map Complex.ofReal
  let RC : Matrix n n ℂ := R.map Complex.ofReal
  let U : Matrix n n ℂ := XC - Complex.I • YC
  let V : Matrix n n ℂ := PC + Complex.I • RC
  have hterm : (Y * Xi * Y).PosSemidef := by
    have h0 := hX.inv.posSemidef.conjTranspose_mul_mul_same Y
    have hYstar : Y.conjTranspose = Y := by
      ext i j
      have hij := congrFun (congrFun hY i) j
      simpa [Matrix.conjTranspose_apply] using hij
    rw [hYstar] at h0
    exact h0
  have hM : M.PosDef := by
    dsimp only [M, Xi]
    exact hX.add_posSemidef hterm
  have hXXi : X * Xi = 1 := by
    dsimp only [Xi]
    exact Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit)
  have hMP : M * P = 1 := by
    dsimp only [P]
    exact Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)
  have hreal : X * P + Y * R = 1 := by
    calc
      X * P + Y * R = (X + Y * Xi * Y) * P := by
        dsimp only [R]
        noncomm_ring
      _ = M * P := by rfl
      _ = 1 := hMP
  have himag : X * R - Y * P = 0 := by
    calc
      X * R - Y * P = (X * Xi - 1) * Y * P := by
        dsimp only [R]
        noncomm_ring
      _ = 0 := by rw [hXXi]; simp
  have hrealC : XC * PC + YC * RC = 1 := by
    ext i j
    have hij := congrFun (congrFun hreal i) j
    by_cases h : i = j
    · simpa [XC, PC, YC, RC, Matrix.mul_apply, Matrix.one_apply, h] using
        congrArg Complex.ofReal hij
    · simpa [XC, PC, YC, RC, Matrix.mul_apply, Matrix.one_apply, h] using
        congrArg Complex.ofReal hij
  have himagC : XC * RC - YC * PC = 0 := by
    ext i j
    have hij := congrFun (congrFun himag i) j
    simpa [XC, PC, YC, RC, Matrix.mul_apply] using congrArg Complex.ofReal hij
  have hright : U * V = 1 := by
    calc
      U * V = (XC * PC + YC * RC) +
          Complex.I • (XC * RC - YC * PC) := by
            dsimp only [U, V]
            exact complex_pair_mul XC YC PC RC
      _ = 1 := by rw [hrealC, himagC]; simp
  have hV : U⁻¹ = V := Matrix.inv_eq_right_inv hright
  have hVre : V.map Complex.re = P := by
    ext i j
    simp [V, PC, RC, Matrix.map_apply]
  have hUre : U⁻¹.map Complex.re = P := by rw [hV, hVre]
  refine ⟨Matrix.isUnit_det_of_right_inverse hright, ?_⟩
  rw [hUre]
  exact hM.inv.isUnit

/-- A complex matrix with positive-definite real part is invertible, and the
real part of its inverse is invertible. -/
private lemma accretive_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U.transpose = U)
    (hX : (U.map Complex.re).PosDef) :
    IsUnit U.det ∧ IsUnit (U⁻¹.map Complex.re) := by
  classical
  let X : Matrix n n ℝ := U.map Complex.re
  let Y : Matrix n n ℝ := -(U.map Complex.im)
  have hY : Y.transpose = Y := by
    ext i j
    change -(U j i).im = -(U i j).im
    exact congrArg (fun z : ℂ => -z.im) (congrFun (congrFun hU i) j)
  have hparts := accretive_inverse_of_parts X Y hX hY
  let XC : Matrix n n ℂ := X.map Complex.ofReal
  let YC : Matrix n n ℂ := Y.map Complex.ofReal
  have hdecomp : U = XC - Complex.I • YC := by
    ext i j
    apply Complex.ext <;>
      simp [X, Y, XC, YC, Matrix.map_apply]
  change IsUnit (XC - Complex.I • YC).det ∧
    IsUnit ((XC - Complex.I • YC)⁻¹.map Complex.re) at hparts
  rw [← hdecomp] at hparts
  exact hparts

/-! ## Selected partial-Fourier covariance algebra -/

/-! Block-matrix algebra for the partial Fourier step.  The notation is
`U = A - iB`, `V = C - iD`, `U⁻¹ = P - iQ`, and
`(Re H)⁻¹ = [[G,H],[I,J]]`. -/

private lemma partialFourier_candidate_three_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D E P Q G H I J : Matrix n n ℝ)
    (hPA : P * A - Q * B = 1)
    (hPB : P * B + Q * A = 0)
    (hAGCI : A * G + C * I = 1)
    (hAHCJ : A * H + C * J = 0)
    (hCHEJ : C.transpose * H + E * J = 1)
    (hP : P.transpose = P) (hQ : Q.transpose = Q) :
    let R := P * D + Q * C
    let L := P * C - Q * D
    let X₂₂ := E - C.transpose * L + D.transpose * R
    let M₁₁ := A + B * G * B + B * H * D.transpose +
      D * I * B + D * J * D.transpose
    let M₁₂ := B * H + D * J
    let M₂₁ := I * B + J * D.transpose
    (P * M₁₁ - R * M₂₁ = 1) ∧
      (P * M₁₂ - R * J = 0) ∧
      (-R.transpose * M₁₂ + X₂₂ * J = 1) := by
  classical
  dsimp only
  have hCI : C * I = 1 - A * G := by
    calc
      C * I = (A * G + C * I) - A * G := by noncomm_ring
      _ = 1 - A * G := by rw [hAGCI]
  have hCJ : C * J = -A * H := by
    calc
      C * J = (A * H + C * J) - A * H := by noncomm_ring
      _ = -A * H := by rw [hAHCJ]; noncomm_ring
  constructor
  · calc
      P * (A + B * G * B + B * H * D.transpose +
          D * I * B + D * J * D.transpose) -
          (P * D + Q * C) * (I * B + J * D.transpose) =
          P * A + P * B * G * B + P * B * H * D.transpose -
            Q * (C * I) * B - Q * (C * J) * D.transpose := by
              noncomm_ring
      _ =
          (P * A - Q * B) + (P * B + Q * A) * G * B +
            (P * B + Q * A) * H * D.transpose := by
              rw [hCI, hCJ]
              noncomm_ring
      _ = 1 := by rw [hPA, hPB]; simp
  · constructor
    · calc
        P * (B * H + D * J) - (P * D + Q * C) * J =
            P * B * H - Q * (C * J) := by noncomm_ring
        _ =
            (P * B + Q * A) * H := by
              rw [hCJ]
              noncomm_ring
        _ = 0 := by rw [hPB]; simp
    · calc
        -(P * D + Q * C).transpose * (B * H + D * J) +
            (E - C.transpose * (P * C - Q * D) +
              D.transpose * (P * D + Q * C)) * J =
            E * J - D.transpose * P * B * H - C.transpose * Q * B * H -
              C.transpose * P * (C * J) + D.transpose * Q * (C * J) := by
                simp only [Matrix.transpose_add, Matrix.transpose_mul]
                rw [hP, hQ]
                noncomm_ring
        _ =
            (C.transpose * H + E * J) +
              C.transpose * (P * A - Q * B - 1) * H -
              D.transpose * (Q * A + P * B) * H := by
                rw [hCJ]
                noncomm_ring
        _ = 1 := by
          rw [hCHEJ, hPA]
          have hz : Q * A + P * B = 0 := by
            calc
              Q * A + P * B = P * B + Q * A := by abel
              _ = 0 := hPB
          rw [hz]
          simp

/-- The inverse of the position block predicted by partial Fourier transformation
is the selected `(p_x,q_R)` covariance.  The proof verifies the displayed
candidate rather than expanding `Xhat⁻¹`. -/
private lemma partialFourier_re_candidate_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D E P Q G H I J : Matrix n n ℝ)
    (hPA : P * A - Q * B = 1)
    (hPB : P * B + Q * A = 0)
    (hAGCI : A * G + C * I = 1)
    (hAHCJ : A * H + C * J = 0)
    (hCHEJ : C.transpose * H + E * J = 1)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hE : E.transpose = E) (hP : P.transpose = P)
    (hQ : Q.transpose = Q) (hG : G.transpose = G)
    (hJ : J.transpose = J) (hI : I = H.transpose)
    [Invertible P] :
    let R := P * D + Q * C
    let L := P * C - Q * D
    let X₂₂ := E - C.transpose * L + D.transpose * R
    let M₁₁ := A + B * G * B + B * H * D.transpose +
      D * I * B + D * J * D.transpose
    let M₁₂ := B * H + D * J
    let M₂₁ := I * B + J * D.transpose
    let Xhat := Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
    let M := Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J
    Xhat⁻¹ = M := by
  classical
  dsimp only
  let R := P * D + Q * C
  let L := P * C - Q * D
  let X₂₂ := E - C.transpose * L + D.transpose * R
  let M₁₁ := A + B * G * B + B * H * D.transpose +
    D * I * B + D * J * D.transpose
  let M₁₂ := B * H + D * J
  let M₂₁ := I * B + J * D.transpose
  let Xhat : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
  let M : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J
  change Xhat⁻¹ = M
  apply Matrix.inv_eq_left_inv
  obtain ⟨h₁₁, h₁₂, h₂₂⟩ := partialFourier_candidate_three_blocks
    A B C D E P Q G H I J hPA hPB hAGCI hAHCJ hCHEJ hP hQ
  change P * M₁₁ - R * M₂₁ = 1 at h₁₁
  change P * M₁₂ - R * J = 0 at h₁₂
  change -R.transpose * M₁₂ + X₂₂ * J = 1 at h₂₂
  have hX₂₂ : X₂₂.transpose = X₂₂ := by
    dsimp only [X₂₂, L, R]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, hE, hP, hQ]
    noncomm_ring
  have hM₁₁ : M₁₁.transpose = M₁₁ := by
    have hIt : I.transpose = H := by
      calc
        I.transpose = H.transpose.transpose := by rw [hI]
        _ = H := Matrix.transpose_transpose H
    dsimp only [M₁₁]
    simp only [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hA, hB, hG, hJ, hIt, ← hI]
    noncomm_ring
  have hM₂₁ : M₂₁ = M₁₂.transpose := by
    dsimp only [M₂₁, M₁₂]
    simp only [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hB, hJ, ← hI]
  have hXsymm : Xhat.transpose = Xhat := by
    dsimp only [Xhat]
    rw [Matrix.fromBlocks_transpose, hP, hX₂₂]
    simp
  have hMsymm : M.transpose = M := by
    dsimp only [M]
    rw [Matrix.fromBlocks_transpose, hM₁₁, hJ, hM₂₁]
    simp
  let K : Matrix n n ℝ := -R.transpose * M₁₁ + X₂₂ * M₂₁
  have hprod : Xhat * M = Matrix.fromBlocks 1 0 K 1 := by
    dsimp only [Xhat, M]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    dsimp only [K]
    refine ⟨?_, ?_, rfl, ?_⟩
    · simpa [sub_eq_add_neg] using h₁₁
    · simpa [sub_eq_add_neg] using h₁₂
    · simpa [sub_eq_add_neg] using h₂₂
  have hprodT : M * Xhat = Matrix.fromBlocks 1 K.transpose 0 1 := by
    calc
      M * Xhat = (Xhat * M).transpose := by
        rw [Matrix.transpose_mul, hXsymm, hMsymm]
      _ = (Matrix.fromBlocks 1 0 K 1).transpose := by rw [hprod]
      _ = Matrix.fromBlocks 1 K.transpose 0 1 := by
        rw [Matrix.fromBlocks_transpose]
        simp
  have hassoc : (Xhat * M) * Xhat = Xhat * (M * Xhat) :=
    Matrix.mul_assoc Xhat M Xhat
  rw [hprod, hprodT] at hassoc
  simp only [Xhat, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at hassoc
  have hKP : K * P = 0 := by
    rw [Matrix.fromBlocks_inj] at hassoc
    have hcancel : K * P + (-R.transpose) = 0 + (-R.transpose) := by
      simpa using hassoc.2.2.1
    exact add_right_cancel hcancel
  have hK : K = 0 := by
    calc
      K = K * 1 := (Matrix.mul_one K).symm
      _ = K * (P * ⅟P) := by rw [mul_invOf_self]
      _ = (K * P) * ⅟P := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hKP, Matrix.zero_mul]
  rw [hprodT, hK]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- The remaining `p_R` column and diagonal block of the selected covariance.
Together with `partialFourier_re_candidate_inverse`, these are exactly the
`(q_x,q_R,p_R)` rows required by the EPR bridge. -/
private lemma partialFourier_selected_pR_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D E F P Q G H I J : Matrix n n ℝ)
    (hPA : P * A - Q * B = 1)
    (hPB : P * B + Q * A = 0)
    (hAP : A * P - B * Q = 1)
    (hAQ : A * Q + B * P = 0)
    (hAGCI : A * G + C * I = 1)
    (hAHCJ : A * H + C * J = 0)
    (hGACH : G * A + H * C.transpose = 1)
    (hIAJC : I * A + J * C.transpose = 0)
    (hP : P.transpose = P) (hQ : Q.transpose = Q) :
    let R := P * D + Q * C
    let L := P * C - Q * D
    let X₂₂ := E - C.transpose * L + D.transpose * R
    let Y₂₂ := F - C.transpose * R - D.transpose * L
    let S := B * G + D * I
    let N := B * H + D * J
    let M₁₁ := A + S * B + N * D.transpose
    let M₂₁ := I * B + J * D.transpose
    let T₁ := C + S * D + N * F
    let T₂ := I * D + J * F
    (M₁₁ * L + N * Y₂₂ = T₁) ∧
      (M₂₁ * L + J * Y₂₂ = T₂) ∧
      (X₂₂ + L.transpose * T₁ + Y₂₂ * T₂ =
        E + (D.transpose * G + F * I) * D +
          (D.transpose * H + F * J) * F) := by
  classical
  dsimp only
  let R := P * D + Q * C
  let L := P * C - Q * D
  let X₂₂ := E - C.transpose * L + D.transpose * R
  let Y₂₂ := F - C.transpose * R - D.transpose * L
  let S := B * G + D * I
  let N := B * H + D * J
  let M₁₁ := A + S * B + N * D.transpose
  let M₂₁ := I * B + J * D.transpose
  let T₁ := C + S * D + N * F
  let T₂ := I * D + J * F
  have hCI : C * I = 1 - A * G := by
    calc
      C * I = (A * G + C * I) - A * G := by noncomm_ring
      _ = 1 - A * G := by rw [hAGCI]
  have hCJ : C * J = -A * H := by
    calc
      C * J = (A * H + C * J) - A * H := by noncomm_ring
      _ = -A * H := by rw [hAHCJ]; noncomm_ring
  have hJC : J * C.transpose = -I * A := by
    calc
      J * C.transpose = (I * A + J * C.transpose) - I * A := by noncomm_ring
      _ = -I * A := by rw [hIAJC]; noncomm_ring
  have hSA : S * A + N * C.transpose = B := by
    dsimp only [S, N]
    calc
      (B * G + D * I) * A + (B * H + D * J) * C.transpose =
          B * (G * A + H * C.transpose) +
            D * (I * A + J * C.transpose) := by noncomm_ring
      _ = B := by rw [hGACH, hIAJC]; simp
  have hNC : N * C.transpose = B - S * A := by
    calc
      N * C.transpose = (S * A + N * C.transpose) - S * A := by noncomm_ring
      _ = B - S * A := by rw [hSA]
  have hALBR : A * L - B * R = C := by
    dsimp only [L, R]
    calc
      A * (P * C - Q * D) - B * (P * D + Q * C) =
          (A * P - B * Q) * C - (A * Q + B * P) * D := by
            noncomm_ring
      _ = C := by rw [hAP, hAQ]; simp
  have hBLAR : B * L + A * R = D := by
    dsimp only [L, R]
    calc
      B * (P * C - Q * D) + A * (P * D + Q * C) =
          (B * P + A * Q) * C + (A * P - B * Q) * D := by
            noncomm_ring
      _ = D := by
        have hz : B * P + A * Q = 0 := by
          calc
            B * P + A * Q = A * Q + B * P := by abel
            _ = 0 := hAQ
        rw [hz, hAP]
        simp
  have hcross₁ : M₁₁ * L + N * Y₂₂ = T₁ := by
    dsimp only [M₁₁, Y₂₂, T₁]
    calc
      (A + S * B + N * D.transpose) * L +
          N * (F - C.transpose * R - D.transpose * L) =
          A * L + S * B * L + N * F - (N * C.transpose) * R := by
            noncomm_ring
      _ =
          (A * L - B * R) + S * (B * L + A * R) + N * F := by
            rw [hNC]
            noncomm_ring
      _ = C + S * D + N * F := by rw [hALBR, hBLAR]
  have hcross₂ : M₂₁ * L + J * Y₂₂ = T₂ := by
    dsimp only [M₂₁, Y₂₂, T₂]
    calc
      (I * B + J * D.transpose) * L +
          J * (F - C.transpose * R - D.transpose * L) =
          I * B * L + J * F - (J * C.transpose) * R := by
            noncomm_ring
      _ =
          I * (B * L + A * R) + J * F := by
            rw [hJC]
            noncomm_ring
      _ = I * D + J * F := by rw [hBLAR]
  refine ⟨hcross₁, hcross₂, ?_⟩
  let W := C.transpose * R + D.transpose * L
  have hK₀ : -C.transpose * L + D.transpose * R + L.transpose * C =
      R.transpose * D := by
    dsimp only [L, R]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
      hP, hQ, Matrix.transpose_transpose]
    noncomm_ring
  have hKD : L.transpose * S - W * I - D.transpose * G = -R.transpose := by
    dsimp only [L, R, W, S]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, hP, hQ,
      Matrix.transpose_transpose]
    calc
      (C.transpose * P - D.transpose * Q) * (B * G + D * I) -
          (C.transpose * (P * D + Q * C) +
            D.transpose * (P * C - Q * D)) * I - D.transpose * G =
          C.transpose * (P * B * G - Q * (C * I)) -
            D.transpose * (Q * B * G + P * (C * I) + G) := by
              noncomm_ring
      _ =
          C.transpose * ((P * B + Q * A) * G - Q) -
            D.transpose * ((-(P * A - Q * B) + 1) * G + P) := by
              rw [hCI]
              noncomm_ring
      _ = -(P * D + Q * C).transpose := by
        rw [hPB, hPA]
        simp only [Matrix.transpose_add, Matrix.transpose_mul, hP, hQ]
        noncomm_ring
  have hKF : L.transpose * N - W * J - D.transpose * H = 0 := by
    dsimp only [L, R, W, N]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, hP, hQ,
      Matrix.transpose_transpose]
    calc
      (C.transpose * P - D.transpose * Q) * (B * H + D * J) -
          (C.transpose * (P * D + Q * C) +
            D.transpose * (P * C - Q * D)) * J - D.transpose * H =
          C.transpose * (P * B * H - Q * (C * J)) -
            D.transpose * (Q * B * H + P * (C * J) + H) := by
              noncomm_ring
      _ =
          C.transpose * ((P * B + Q * A) * H) -
            D.transpose * ((-(P * A - Q * B) + 1) * H) := by
              rw [hCJ]
              noncomm_ring
      _ = 0 := by rw [hPB, hPA]; simp
  calc
    E - C.transpose * L + D.transpose * R +
          L.transpose * (C + S * D + N * F) +
          (F - C.transpose * R - D.transpose * L) * (I * D + J * F) =
        (E + (D.transpose * G + F * I) * D +
          (D.transpose * H + F * J) * F) +
          (-C.transpose * L + D.transpose * R + L.transpose * C) +
          (L.transpose * S - W * I - D.transpose * G) * D +
          (L.transpose * N - W * J - D.transpose * H) * F := by
            dsimp only [W]
            noncomm_ring
    _ = E + (D.transpose * G + F * I) * D +
          (D.transpose * H + F * J) * F := by
            rw [hK₀, hKD, hKF]
            noncomm_ring

/-- The covariance rows containing all positions and only the retained momenta. -/
private noncomputable def selectedKernelCovariance
    {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix ((n ⊕ n) ⊕ n) ((n ⊕ n) ⊕ n) ℝ :=
  Matrix.fromBlocks X⁻¹
    ((X⁻¹ * Y).submatrix id Sum.inr)
    ((Y * X⁻¹).submatrix Sum.inr id)
    ((X + Y * X⁻¹ * Y).submatrix Sum.inr Sum.inr)

private lemma selectedKernelCovariance_of_blocks
    {n : Type*} [Fintype n] [DecidableEq n]
    (P Q R L X₂₂ Y₂₂ M₁₁ M₁₂ M₂₁ J T₁ T₂ Prr : Matrix n n ℝ)
    (hinv :
      (Matrix.fromBlocks P (-R) (-R.transpose) X₂₂)⁻¹ =
        Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J)
    (hcross₁ : M₁₁ * L + M₁₂ * Y₂₂ = T₁)
    (hcross₂ : M₂₁ * L + J * Y₂₂ = T₂)
    (hpp : X₂₂ + L.transpose * T₁ + Y₂₂ * T₂ = Prr)
    (hM : (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J).transpose =
      Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J)
    (hY : (Matrix.fromBlocks Q L L.transpose Y₂₂).transpose =
      Matrix.fromBlocks Q L L.transpose Y₂₂) :
    let Xhat := Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
    let Yhat := Matrix.fromBlocks Q L L.transpose Y₂₂
    let M := Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J
    let T : Matrix (n ⊕ n) n ℝ := Sum.elim T₁ T₂
    selectedKernelCovariance Xhat Yhat =
      Matrix.fromBlocks M T T.transpose Prr := by
  classical
  dsimp only
  let Xhat : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
  let Yhat : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks Q L L.transpose Y₂₂
  let M : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks M₁₁ M₁₂ M₂₁ J
  let T : Matrix (n ⊕ n) n ℝ := Sum.elim T₁ T₂
  change selectedKernelCovariance Xhat Yhat = Matrix.fromBlocks M T T.transpose Prr
  change Xhat⁻¹ = M at hinv
  change M.transpose = M at hM
  change Yhat.transpose = Yhat at hY
  have hMY : M * Yhat = Matrix.fromBlocks
      (M₁₁ * Q + M₁₂ * L.transpose) T₁
      (M₂₁ * Q + J * L.transpose) T₂ := by
    dsimp only [M, Yhat]
    rw [Matrix.fromBlocks_multiply]
    rw [hcross₁, hcross₂]
  have hYM : Yhat * M = (Matrix.fromBlocks
      (M₁₁ * Q + M₁₂ * L.transpose) T₁
      (M₂₁ * Q + J * L.transpose) T₂).transpose := by
    calc
      Yhat * M = (M * Yhat).transpose := by
        rw [Matrix.transpose_mul, hM, hY]
      _ = _ := by rw [hMY]
  unfold selectedKernelCovariance
  rw [hinv, Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [hMY]
    ext (i | i) j <;> rfl
  · rw [hYM]
    ext i (j | j) <;> rfl
  · rw [Matrix.mul_assoc, hMY, Matrix.fromBlocks_multiply]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Xhat,
      Matrix.fromBlocks_apply₂₂]
    simpa [add_assoc] using congrFun (congrFun hpp i) j

/-- Complete selected-covariance block identity for partial Fourier transform.
The transformed positions `(q_x,q_R)` have the covariance of `(p_x,q_R)`
before transformation, and the retained `p_R` column and diagonal block agree. -/
private lemma partialFourier_selected_covariance
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B C D E F P Q G H I J : Matrix n n ℝ)
    (hPA : P * A - Q * B = 1) (hPB : P * B + Q * A = 0)
    (hAP : A * P - B * Q = 1) (hAQ : A * Q + B * P = 0)
    (hAGCI : A * G + C * I = 1) (hAHCJ : A * H + C * J = 0)
    (hCHEJ : C.transpose * H + E * J = 1)
    (hGACH : G * A + H * C.transpose = 1)
    (hIAJC : I * A + J * C.transpose = 0)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hE : E.transpose = E) (hF : F.transpose = F)
    (hP : P.transpose = P) (hQ : Q.transpose = Q)
    (hG : G.transpose = G) (hJ : J.transpose = J)
    (hI : I = H.transpose) [Invertible P] :
    let R := P * D + Q * C
    let L := P * C - Q * D
    let X₂₂ := E - C.transpose * L + D.transpose * R
    let Y₂₂ := F - C.transpose * R - D.transpose * L
    let S := B * G + D * I
    let N := B * H + D * J
    let M₁₁ := A + S * B + N * D.transpose
    let M₂₁ := I * B + J * D.transpose
    let T₁ := C + S * D + N * F
    let T₂ := I * D + J * F
    let Prr := E + (D.transpose * G + F * I) * D +
      (D.transpose * H + F * J) * F
    let Xhat := Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
    let Yhat := Matrix.fromBlocks Q L L.transpose Y₂₂
    let M := Matrix.fromBlocks M₁₁ N M₂₁ J
    let T : Matrix (n ⊕ n) n ℝ := Sum.elim T₁ T₂
    selectedKernelCovariance Xhat Yhat =
      Matrix.fromBlocks M T T.transpose Prr := by
  classical
  dsimp only
  let R := P * D + Q * C
  let L := P * C - Q * D
  let X₂₂ := E - C.transpose * L + D.transpose * R
  let Y₂₂ := F - C.transpose * R - D.transpose * L
  let S := B * G + D * I
  let N := B * H + D * J
  let M₁₁ := A + S * B + N * D.transpose
  let M₂₁ := I * B + J * D.transpose
  let T₁ := C + S * D + N * F
  let T₂ := I * D + J * F
  let Prr := E + (D.transpose * G + F * I) * D +
    (D.transpose * H + F * J) * F
  let Xhat : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks P (-R) (-R.transpose) X₂₂
  let Yhat : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks Q L L.transpose Y₂₂
  let M : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    Matrix.fromBlocks M₁₁ N M₂₁ J
  let T : Matrix (n ⊕ n) n ℝ := Sum.elim T₁ T₂
  have hinv₀ := partialFourier_re_candidate_inverse A B C D E P Q G H I J
    hPA hPB hAGCI hAHCJ hCHEJ hA hB hE hP hQ hG hJ hI
  have hM₁₁ : A + B * G * B + B * H * D.transpose +
      D * I * B + D * J * D.transpose = M₁₁ := by
    dsimp only [M₁₁, S, N]
    noncomm_ring
  change Xhat⁻¹ = Matrix.fromBlocks
    (A + B * G * B + B * H * D.transpose +
      D * I * B + D * J * D.transpose)
    (B * H + D * J) (I * B + J * D.transpose) J at hinv₀
  rw [hM₁₁] at hinv₀
  change Xhat⁻¹ = M at hinv₀
  obtain ⟨hcross₁, hcross₂, hpp⟩ := partialFourier_selected_pR_blocks
    A B C D E F P Q G H I J hPA hPB hAP hAQ hAGCI hAHCJ hGACH hIAJC hP hQ
  change M₁₁ * L + N * Y₂₂ = T₁ at hcross₁
  change M₂₁ * L + J * Y₂₂ = T₂ at hcross₂
  change X₂₂ + L.transpose * T₁ + Y₂₂ * T₂ = Prr at hpp
  have hMt : M.transpose = M := by
    have hIt : I.transpose = H := by
      calc
        I.transpose = H.transpose.transpose := by rw [hI]
        _ = H := Matrix.transpose_transpose H
    dsimp only [M, M₁₁, M₂₁, N, S]
    rw [Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hA, hB, hG, hJ, hIt, ← hI]
    congr 1 <;> noncomm_ring
  have hYt : Yhat.transpose = Yhat := by
    dsimp only [Yhat]
    rw [Matrix.fromBlocks_transpose, hQ]
    have hY₂₂ : Y₂₂.transpose = Y₂₂ := by
      dsimp only [Y₂₂, L, R]
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, hF, hP, hQ]
      noncomm_ring
    rw [hY₂₂]
    simp
  change selectedKernelCovariance Xhat Yhat = Matrix.fromBlocks M T T.transpose Prr
  exact selectedKernelCovariance_of_blocks P Q R L X₂₂ Y₂₂ M₁₁ N M₂₁ J T₁ T₂ Prr
    hinv₀ hcross₁ hcross₂ hpp hMt hYt

/-! The next two lemmas connect the real block variables used above to the
actual complex inverse `U⁻¹`; they are not independent sign assumptions. -/

private lemma complex_mul_re_negIm
    {n : Type*} [Fintype n] [DecidableEq n]
    (K L : Matrix n n ℂ) :
    let A := K.map Complex.re
    let B := -(K.map Complex.im)
    let P := L.map Complex.re
    let Q := -(L.map Complex.im)
    ((K * L).map Complex.re = A * P - B * Q) ∧
      (-((K * L).map Complex.im) = A * Q + B * P) := by
  classical
  dsimp only
  constructor
  · ext i j
    simp [Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  · ext i j
    simp [Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel

private lemma complex_inverse_re_negIm_relations
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hdet : IsUnit U.det) (hU : U.transpose = U) :
    let A := U.map Complex.re
    let B := -(U.map Complex.im)
    let P := U⁻¹.map Complex.re
    let Q := -(U⁻¹.map Complex.im)
    (A * P - B * Q = 1) ∧ (A * Q + B * P = 0) ∧
      (P * A - Q * B = 1) ∧ (P * B + Q * A = 0) ∧
      (P.transpose = P) ∧ (Q.transpose = Q) := by
  classical
  dsimp only
  obtain ⟨hAP, hAQ⟩ := complex_mul_re_negIm U U⁻¹
  obtain ⟨hPA, hPB⟩ := complex_mul_re_negIm U⁻¹ U
  rw [Matrix.mul_nonsing_inv U hdet] at hAP hAQ
  rw [Matrix.nonsing_inv_mul U hdet] at hPA hPB
  have honeIm : (1 : Matrix n n ℂ).map Complex.im = 0 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, h]
  rw [honeIm] at hAQ hPB
  simp only [neg_zero] at hAQ hPB
  have hinv : U⁻¹.transpose = U⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hU]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hAP.symm
  · simpa using hAQ.symm
  · simpa using hPA.symm
  · simpa using hPB.symm
  · ext i j
    have hij := congrFun (congrFun hinv i) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using congrArg Complex.re hij
  · ext i j
    have hij := congrFun (congrFun hinv i) j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using congrArg Complex.im hij

end Gaussian
