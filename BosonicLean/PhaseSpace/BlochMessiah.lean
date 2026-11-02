/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.PhaseSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Bloch–Messiah decomposition of a real symplectic matrix

Every real symplectic `2n × 2n` matrix factors as `S = O_U Σ(r) O_W`, with `O_U`, `O_W` orthogonal
and symplectic and `Σ(r) = diag(e^{-r₁}, …, e^{-rₙ}, e^{r₁}, …, e^{rₙ})`, `r ≥ 0`
(Tjoa–Cirac, arXiv:2607.28753, (A11)); it is also called the Euler decomposition. Physically,
every linear canonical transformation of `n` modes is a passive interferometer, followed by `n`
single-mode squeezers, followed by a second interferometer.

Coordinates are ordered positions first (`PhaseIndex n = Fin n ⊕ Fin n`) and the symplectic form
is `symplecticForm n = Ω = [[0, 1], [-1, 0]]`, the paper's (A2). Mathlib's `Matrix.J` is `-Ω`;
the symplectic group `Sp(2n, ℝ) = {S | S Ω Sᵀ = Ω}` is Mathlib's `Matrix.symplecticGroup`
(`mem_symplecticGroup_iff`). The orthogonal symplectic matrices are written as the intersection
`symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ` of Mathlib's groups.

## Main definitions

* `Gaussian.orthogonalSymplecticOfUnitary`: the orthogonal symplectic matrix
  `O_U = [[X, -Y], [Y, X]]` of a unitary `U = X + iY`, the matrix of `U` acting on `ℂⁿ ≅ ℝ²ⁿ`,
  `x + ip ↦ (x, p)` (paper (A14));
* `Gaussian.unitaryOfOrthogonalSymplectic`: the inverse, `[[X, -Y], [Y, X]] ↦ X + iY`;
* `Gaussian.orthogonalSymplecticEquivUnitary`: the group isomorphism `Sp(2n, ℝ) ∩ O(2n) ≃* U(n)`;
* `Gaussian.squeezingMatrix`: the squeezing matrix `Σ(r)` (paper (A10)).

## Main statements

* `Gaussian.mem_orthogonalSymplectic_iff`: the orthogonal symplectic matrices are exactly the
  matrices `O_U` of unitary matrices `U` (paper (A14)–(A16));
* `Gaussian.exists_orthogonalSymplectic_diagonalization`: a positive definite symplectic `M` is
  `O Σ(r)² Oᵀ` with `O` orthogonal symplectic and `r ≥ 0` (paper (A8)–(A10));
* `Gaussian.exists_blochMessiah`: the Bloch–Messiah decomposition (paper (A11));
* `Gaussian.singularValues_of_eq`, `Gaussian.exists_perm_of_blochMessiah`: the singular values of
  `S` are the `e^{∓r_k}`, so `r` is unique up to order;
* `Gaussian.polar_decomposition`, `Gaussian.polar_unique`: `P = (S Sᵀ)^{1/2}` (Mathlib's
  `CFC.sqrt`) is positive definite and symplectic and `P⁻¹ S` orthogonal symplectic
  (paper (A4)–(A5)); the polar decomposition is unique.

## Implementation notes

The diagonalization does not take a square root: it diagonalizes `M = S Sᵀ` by choosing, one at a
time, orthonormal eigenvectors `f k` of `M` with eigenvalues in `(0, 1]` and `⟪f j, Ω f k⟫ = 0`,
inside `EuclideanSpace ℝ (PhaseIndex n)`; the columns `f k`, `-Ω f k` then form `O`
(`exists_orthonormal_isotropic_eigenvectors`, `columns_sumElim_neg_symplecticForm`). The polar
decomposition follows as a corollary.

## References

* E. Tjoa and J. I. Cirac, *Gaussian-augmented bosonic matrix-product states: theory and
  applications*, arXiv:2607.28753 (2026), Appendix A.
* S. L. Braunstein, *Squeezing as an irreducible resource*, Phys. Rev. A **71**, 055801 (2005).
-/

open Matrix

namespace Gaussian

variable {n : ℕ}

section Symplectic

/-- The symplectic form in block form, `Ω = [[0, 1], [-1, 0]]`. -/
theorem symplecticForm_eq_fromBlocks :
    symplecticForm n = fromBlocks 0 1 (-1) 0 := by
  simp [symplecticForm, Matrix.J, fromBlocks_neg]

/-- **Lemma 1.** The symplectic group defined with `Ω` is Mathlib's `symplecticGroup`, which is
defined with `J = -Ω`. -/
theorem mem_symplecticGroup_iff {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    S ∈ symplecticGroup (Fin n) ℝ ↔ S * symplecticForm n * Sᵀ = symplecticForm n := by
  rw [SymplecticGroup.mem_iff, symplecticForm, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- **Lemma 1.** `S Ω Sᵀ = Ω` if and only if `Sᵀ Ω S = Ω`. -/
theorem mem_symplecticGroup_iff' {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    S ∈ symplecticGroup (Fin n) ℝ ↔ Sᵀ * symplecticForm n * S = symplecticForm n := by
  rw [SymplecticGroup.mem_iff', symplecticForm, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

end Symplectic

section OrthogonalSymplectic

/-! ### Orthogonal symplectic matrices and unitary matrices

A complex `n × n` matrix `U = X + iY` acts on `ℂⁿ ≅ ℝ²ⁿ`, `x + ip ↦ (x, p)`, as the real matrix
`[[X, -Y], [Y, X]]` (paper (A14)). The block map on all complex matrices only serves the proofs
and is private; the public API is the correspondence between unitary matrices `U` and orthogonal
symplectic matrices `O_U` (Definition 2 restricted to unitary `U`), with the group isomorphism
`orthogonalSymplecticEquivUnitary`. -/

/-- The real `2n × 2n` matrix `[[X, -Y], [Y, X]]` of a complex matrix `U = X + iY`. -/
private def toBlocksReal (U : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  fromBlocks (U.map Complex.re) (-U.map Complex.im) (U.map Complex.im) (U.map Complex.re)

/-- `[[X, -Y], [Y, X]] ↦ X + iY`, read off the left blocks. -/
private noncomputable def ofBlocksReal (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  O.toBlocks₁₁.map Complex.ofReal + Complex.I • O.toBlocks₂₁.map Complex.ofReal

private theorem map_re_mul (U V : Matrix (Fin n) (Fin n) ℂ) :
    (U * V).map Complex.re = U.map Complex.re * V.map Complex.re -
      U.map Complex.im * V.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

private theorem map_im_mul (U V : Matrix (Fin n) (Fin n) ℂ) :
    (U * V).map Complex.im = U.map Complex.re * V.map Complex.im +
      U.map Complex.im * V.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

private theorem toBlocksReal_mul (U V : Matrix (Fin n) (Fin n) ℂ) :
    toBlocksReal (U * V) = toBlocksReal U * toBlocksReal V := by
  simp only [toBlocksReal, fromBlocks_multiply, map_re_mul, map_im_mul, Matrix.neg_mul,
    Matrix.mul_neg]
  congr 1 <;> abel

private theorem toBlocksReal_one : toBlocksReal (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [toBlocksReal, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem toBlocksReal_neg (U : Matrix (Fin n) (Fin n) ℂ) :
    toBlocksReal (-U) = -toBlocksReal U := by
  ext (i | i) (j | j) <;> simp [toBlocksReal]

private theorem toBlocksReal_conjTranspose (U : Matrix (Fin n) (Fin n) ℂ) :
    toBlocksReal Uᴴ = (toBlocksReal U)ᵀ := by
  ext (i | i) (j | j) <;> simp [toBlocksReal]

private theorem toBlocksReal_injective : Function.Injective (toBlocksReal (n := n)) := by
  intro U V h
  obtain ⟨h₁, -, h₃, -⟩ := fromBlocks_inj.1 h
  ext i j
  exact Complex.ext (congr_fun (congr_fun h₁ i) j) (congr_fun (congr_fun h₃ i) j)

private theorem ofBlocksReal_toBlocksReal (U : Matrix (Fin n) (Fin n) ℂ) :
    ofBlocksReal (toBlocksReal U) = U := by
  ext i j
  simp [ofBlocksReal, toBlocksReal, mul_comm Complex.I, Complex.re_add_im]

private theorem toBlocksReal_ofReal (X Y : Matrix (Fin n) (Fin n) ℝ) :
    toBlocksReal (X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal) =
      fromBlocks X (-Y) Y X := by
  ext (i | i) (j | j) <;> simp [toBlocksReal]

/-- **Lemma 4.** An orthogonal matrix is symplectic if and only if it commutes with `Ω`. -/
theorem mem_symplecticGroup_iff_commute {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hO : O ∈ orthogonalGroup (PhaseIndex n) ℝ) :
    O ∈ symplecticGroup (Fin n) ℝ ↔ O * symplecticForm n = symplecticForm n * O := by
  have h₁ : O * Oᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hO
  have h₂ : Oᵀ * O = 1 := (mem_orthogonalGroup_iff' _ _).1 hO
  rw [mem_symplecticGroup_iff]
  constructor
  · intro h
    calc O * symplecticForm n = O * symplecticForm n * (Oᵀ * O) := by rw [h₂, Matrix.mul_one]
      _ = symplecticForm n * O := by rw [← Matrix.mul_assoc, h]
  · intro h
    rw [h, Matrix.mul_assoc, h₁, Matrix.mul_one]

/-- **Lemma 4.** A real `2n × 2n` matrix commutes with `Ω` if and only if it has the block form
`[[X, -Y], [Y, X]]`, that is, it is the matrix of the complex `n × n` matrix `X + iY` acting on
`ℂⁿ ≅ ℝ²ⁿ`. -/
theorem commute_symplecticForm_iff {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    O * symplecticForm n = symplecticForm n * O ↔
      ∃ X Y : Matrix (Fin n) (Fin n) ℝ, O = fromBlocks X (-Y) Y X := by
  constructor
  · intro h
    rw [← fromBlocks_toBlocks O, symplecticForm_eq_fromBlocks, fromBlocks_multiply,
      fromBlocks_multiply] at h
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h
    obtain ⟨h₁, h₂, -, -⟩ := h
    refine ⟨O.toBlocks₁₁, O.toBlocks₂₁, ?_⟩
    conv_lhs => rw [← fromBlocks_toBlocks O]
    rw [fromBlocks_inj]
    exact ⟨rfl, by rw [← h₁, neg_neg], rfl, h₂.symm⟩
  · rintro ⟨X, Y, rfl⟩
    simp only [symplecticForm_eq_fromBlocks, fromBlocks_multiply,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero]

private theorem toBlocksReal_ofBlocksReal {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (h : O * symplecticForm n = symplecticForm n * O) : toBlocksReal (ofBlocksReal O) = O := by
  obtain ⟨X, Y, rfl⟩ := commute_symplecticForm_iff.1 h
  rw [ofBlocksReal, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, toBlocksReal_ofReal]

private theorem mem_orthogonalSymplectic_iff_toBlocksReal
    {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ↔
      ∃ U ∈ unitaryGroup (Fin n) ℂ, O = toBlocksReal U := by
  rw [Submonoid.mem_inf]
  constructor
  · rintro ⟨hS, hO⟩
    have hc := (mem_symplecticGroup_iff_commute hO).1 hS
    refine ⟨ofBlocksReal O, ?_, (toBlocksReal_ofBlocksReal hc).symm⟩
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    apply toBlocksReal_injective
    rw [toBlocksReal_mul, toBlocksReal_conjTranspose, toBlocksReal_one,
      toBlocksReal_ofBlocksReal hc]
    exact (mem_orthogonalGroup_iff' _ _).1 hO
  · rintro ⟨U, hU, rfl⟩
    have hO : toBlocksReal U ∈ orthogonalGroup (PhaseIndex n) ℝ := by
      rw [mem_orthogonalGroup_iff, ← toBlocksReal_conjTranspose, ← toBlocksReal_mul,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hU, toBlocksReal_one]
    exact ⟨(mem_symplecticGroup_iff_commute hO).2
      (commute_symplecticForm_iff.2 ⟨_, _, rfl⟩), hO⟩

/-- **Definition 2** (for unitary `U`). The **orthogonal symplectic matrix** `O_U` of a unitary
`U = X + iY`: the real `2n × 2n` matrix `[[X, -Y], [Y, X]]` of `U` acting on `ℂⁿ ≅ ℝ²ⁿ` under
`x + ip ↦ (x, p)` (paper (A14)). -/
def orthogonalSymplecticOfUnitary (U : unitaryGroup (Fin n) ℂ) :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  fromBlocks ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re)
    (-(U : Matrix (Fin n) (Fin n) ℂ).map Complex.im) ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.im)
    ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re)

private theorem orthogonalSymplecticOfUnitary_eq (U : unitaryGroup (Fin n) ℂ) :
    orthogonalSymplecticOfUnitary U = toBlocksReal (U : Matrix (Fin n) (Fin n) ℂ) :=
  rfl

/-- **Theorem 5(b).** `O_U` is orthogonal and symplectic. -/
theorem orthogonalSymplecticOfUnitary_mem (U : unitaryGroup (Fin n) ℂ) :
    orthogonalSymplecticOfUnitary U ∈
      symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ :=
  mem_orthogonalSymplectic_iff_toBlocksReal.2 ⟨U.1, U.2, rfl⟩

/-- **Theorem 5(b).** A real `2n × 2n` matrix is orthogonal and symplectic if and only if it is
`O_U` for a unitary `U`. -/
theorem mem_orthogonalSymplectic_iff {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ↔
      ∃ U : unitaryGroup (Fin n) ℂ, O = orthogonalSymplecticOfUnitary U := by
  rw [mem_orthogonalSymplectic_iff_toBlocksReal]
  exact ⟨fun ⟨U, hU, h⟩ => ⟨⟨U, hU⟩, h⟩, fun ⟨U, h⟩ => ⟨U.1, U.2, h⟩⟩

/-- **Theorem 5(b)**, in blocks (paper (A14)–(A16)): a real `2n × 2n` matrix is orthogonal and
symplectic if and only if it is `[[X, -Y], [Y, X]]` with `X + iY` unitary. -/
theorem mem_orthogonalSymplectic_iff_fromBlocks {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} :
    O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ↔
      ∃ X Y : Matrix (Fin n) (Fin n) ℝ,
        X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal ∈ unitaryGroup (Fin n) ℂ ∧
          O = fromBlocks X (-Y) Y X := by
  rw [mem_orthogonalSymplectic_iff_toBlocksReal]
  constructor
  · rintro ⟨U, hU, rfl⟩
    refine ⟨U.map Complex.re, U.map Complex.im, ?_, rfl⟩
    have h := ofBlocksReal_toBlocksReal U
    rw [ofBlocksReal, toBlocksReal, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h
    rwa [h]
  · rintro ⟨X, Y, hU, rfl⟩
    exact ⟨_, hU, (toBlocksReal_ofReal X Y).symm⟩

/-- **Theorem 5(a).** `O_{U V} = O_U O_V`. -/
theorem orthogonalSymplecticOfUnitary_mul (U V : unitaryGroup (Fin n) ℂ) :
    orthogonalSymplecticOfUnitary (U * V) =
      orthogonalSymplecticOfUnitary U * orthogonalSymplecticOfUnitary V :=
  toBlocksReal_mul _ _

/-- **Theorem 5(a).** `O_1 = 1`. -/
theorem orthogonalSymplecticOfUnitary_one :
    orthogonalSymplecticOfUnitary (1 : unitaryGroup (Fin n) ℂ) = 1 :=
  toBlocksReal_one

/-- **Theorem 5(a).** `O_{U*} = O_Uᵀ`. -/
theorem orthogonalSymplecticOfUnitary_star (U : unitaryGroup (Fin n) ℂ) :
    orthogonalSymplecticOfUnitary (star U) = (orthogonalSymplecticOfUnitary U)ᵀ := by
  rw [orthogonalSymplecticOfUnitary_eq, Unitary.coe_star, star_eq_conjTranspose,
    toBlocksReal_conjTranspose, orthogonalSymplecticOfUnitary_eq]

/-- **Theorem 5(a).** `U ↦ O_U` is injective. -/
theorem orthogonalSymplecticOfUnitary_injective :
    Function.Injective (orthogonalSymplecticOfUnitary (n := n)) :=
  fun _ _ h => Subtype.ext (toBlocksReal_injective h)

/-- `O_{-U} = -O_U`. -/
theorem orthogonalSymplecticOfUnitary_neg (U : unitaryGroup (Fin n) ℂ) :
    orthogonalSymplecticOfUnitary (-U) = -orthogonalSymplecticOfUnitary U := by
  rw [orthogonalSymplecticOfUnitary_eq, Unitary.coe_neg, toBlocksReal_neg,
    orthogonalSymplecticOfUnitary_eq]

/-- `-Ω` is `O_U` for `U = i • 1`: it is multiplication by `i` on `ℂⁿ`. -/
theorem orthogonalSymplecticOfUnitary_eq_neg_symplecticForm {U : unitaryGroup (Fin n) ℂ}
    (hU : (U : Matrix (Fin n) (Fin n) ℂ) = Complex.I • 1) :
    orthogonalSymplecticOfUnitary U = -symplecticForm n := by
  rw [orthogonalSymplecticOfUnitary_eq, hU, symplecticForm_eq_fromBlocks, fromBlocks_neg,
    toBlocksReal]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h]

/-- **Theorem 5(c).** The unitary matrix `X + iY` of an orthogonal symplectic matrix
`O = [[X, -Y], [Y, X]]`, read off the left blocks. -/
noncomputable def unitaryOfOrthogonalSymplectic
    (O : ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
    unitaryGroup (Fin n) ℂ :=
  ⟨(O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₁₁.map Complex.ofReal +
      Complex.I • (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₂₁.map Complex.ofReal, by
    obtain ⟨U, hU, h⟩ := mem_orthogonalSymplectic_iff_toBlocksReal.1 O.2
    have h' := ofBlocksReal_toBlocksReal U
    rw [← h] at h'
    rw [ofBlocksReal] at h'
    rwa [h']⟩

/-- The unitary matrix of `O = [[X, -Y], [Y, X]]` is `X + iY`. -/
theorem coe_unitaryOfOrthogonalSymplectic
    (O : ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
    (unitaryOfOrthogonalSymplectic O : Matrix (Fin n) (Fin n) ℂ) =
      (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₁₁.map Complex.ofReal +
        Complex.I • (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₂₁.map Complex.ofReal :=
  rfl

/-- The unitary matrix of `O_U` is `U`. -/
@[simp]
theorem unitaryOfOrthogonalSymplectic_orthogonalSymplecticOfUnitary
    (U : unitaryGroup (Fin n) ℂ) :
    unitaryOfOrthogonalSymplectic ⟨_, orthogonalSymplecticOfUnitary_mem U⟩ = U :=
  Subtype.ext (ofBlocksReal_toBlocksReal U.1)

/-- The orthogonal symplectic matrix of the unitary matrix of `O` is `O`. -/
@[simp]
theorem orthogonalSymplecticOfUnitary_unitaryOfOrthogonalSymplectic
    (O : ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
    orthogonalSymplecticOfUnitary (unitaryOfOrthogonalSymplectic O) = O := by
  obtain ⟨U, h⟩ := mem_orthogonalSymplectic_iff.1 O.2
  have hO : O = ⟨_, orthogonalSymplecticOfUnitary_mem U⟩ := Subtype.ext h
  rw [hO, unitaryOfOrthogonalSymplectic_orthogonalSymplecticOfUnitary]

/-- **Theorem 5(c).** The orthogonal symplectic matrices form a group isomorphic to the unitary
group `U(n)`, by `O = [[X, -Y], [Y, X]] ↦ X + iY`, with inverse `U ↦ O_U`. -/
noncomputable def orthogonalSymplecticEquivUnitary :
    ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ) ≃*
      unitaryGroup (Fin n) ℂ where
  toFun := unitaryOfOrthogonalSymplectic
  invFun U := ⟨orthogonalSymplecticOfUnitary U, orthogonalSymplecticOfUnitary_mem U⟩
  left_inv O := Subtype.ext (orthogonalSymplecticOfUnitary_unitaryOfOrthogonalSymplectic O)
  right_inv := unitaryOfOrthogonalSymplectic_orthogonalSymplecticOfUnitary
  map_mul' O₁ O₂ := by
    apply orthogonalSymplecticOfUnitary_injective
    rw [orthogonalSymplecticOfUnitary_mul,
      orthogonalSymplecticOfUnitary_unitaryOfOrthogonalSymplectic,
      orthogonalSymplecticOfUnitary_unitaryOfOrthogonalSymplectic,
      orthogonalSymplecticOfUnitary_unitaryOfOrthogonalSymplectic, Submonoid.coe_mul]

/-- The isomorphism is `unitaryOfOrthogonalSymplectic`. -/
@[simp]
theorem coe_orthogonalSymplecticEquivUnitary :
    ⇑(orthogonalSymplecticEquivUnitary (n := n)) = unitaryOfOrthogonalSymplectic :=
  rfl

/-- The inverse isomorphism is `U ↦ O_U`. -/
@[simp]
theorem coe_orthogonalSymplecticEquivUnitary_symm (U : unitaryGroup (Fin n) ℂ) :
    ((orthogonalSymplecticEquivUnitary.symm U :
      ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
        Matrix (PhaseIndex n) (PhaseIndex n) ℝ) = orthogonalSymplecticOfUnitary U :=
  rfl

/-- **Theorem 5(c)**, in blocks: the isomorphism sends `O = [[X, -Y], [Y, X]]` to `X + iY`. -/
theorem orthogonalSymplecticEquivUnitary_apply
    (O : ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
    (orthogonalSymplecticEquivUnitary O : Matrix (Fin n) (Fin n) ℂ) =
      (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₁₁.map Complex.ofReal +
        Complex.I • (O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ).toBlocks₂₁.map Complex.ofReal :=
  rfl

/-- **Theorem 5(c)**, in blocks: the inverse isomorphism sends `U = X + iY` to
`[[X, -Y], [Y, X]]`. -/
theorem orthogonalSymplecticEquivUnitary_symm_apply (U : unitaryGroup (Fin n) ℂ) :
    ((orthogonalSymplecticEquivUnitary.symm U :
      ↥(symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)) :
        Matrix (PhaseIndex n) (PhaseIndex n) ℝ) =
      fromBlocks ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re)
        (-(U : Matrix (Fin n) (Fin n) ℂ).map Complex.im)
        ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.im)
        ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re) :=
  rfl

end OrthogonalSymplectic

section Squeezing

/-- **Definition 3.** The **squeezing matrix**
`Σ(r) = diag(e^{-r₁}, …, e^{-rₙ}, e^{r₁}, …, e^{rₙ})` (paper (A10)): the positions are squeezed
by `e^{-r_k}` and the momenta stretched by `e^{r_k}`. -/
noncomputable def squeezingMatrix (r : Fin n → ℝ) : Matrix (PhaseIndex n) (PhaseIndex n) ℝ :=
  diagonal (Sum.elim (fun k => Real.exp (-r k)) fun k => Real.exp (r k))

/-- **Definition 3.** The squeezing matrix is symplectic. -/
theorem squeezingMatrix_mem (r : Fin n → ℝ) : squeezingMatrix r ∈ symplecticGroup (Fin n) ℝ := by
  rw [squeezingMatrix, ← fromBlocks_diagonal, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, by simp, ?_⟩
  rw [diagonal_transpose, diagonal_mul_diagonal, Matrix.transpose_zero, Matrix.zero_mul,
    sub_zero, ← diagonal_one]
  congr 1
  ext k
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **Definition 3.** `Σ(r + s) = Σ(r) Σ(s)`. -/
theorem squeezingMatrix_add (r s : Fin n → ℝ) :
    squeezingMatrix (r + s) = squeezingMatrix r * squeezingMatrix s := by
  rw [squeezingMatrix, squeezingMatrix, squeezingMatrix, diagonal_mul_diagonal]
  congr 1
  ext (k | k) <;> simp [Real.exp_add, mul_comm]

/-- **Definition 3.** `Σ(0) = 1`. -/
@[simp]
theorem squeezingMatrix_zero : squeezingMatrix (0 : Fin n → ℝ) = 1 := by
  rw [squeezingMatrix, ← diagonal_one]
  congr 1
  ext (k | k) <;> simp

/-- `Σ(r)` is symmetric. -/
@[simp]
theorem squeezingMatrix_transpose (r : Fin n → ℝ) : (squeezingMatrix r)ᵀ = squeezingMatrix r :=
  diagonal_transpose _

/-- `Σ(r)` is positive definite. -/
theorem posDef_squeezingMatrix (r : Fin n → ℝ) : (squeezingMatrix r).PosDef := by
  rw [squeezingMatrix, posDef_diagonal_iff]
  rintro (k | k) <;> exact Real.exp_pos _

/-- `Σ(-r) Σ(r) = 1`. -/
theorem squeezingMatrix_neg_mul (r : Fin n → ℝ) :
    squeezingMatrix (-r) * squeezingMatrix r = 1 := by
  rw [← squeezingMatrix_add, neg_add_cancel, squeezingMatrix_zero]

/-- `Σ(r) Σ(-r) = 1`. -/
theorem squeezingMatrix_mul_neg (r : Fin n → ℝ) :
    squeezingMatrix r * squeezingMatrix (-r) = 1 := by
  rw [← squeezingMatrix_add, add_neg_cancel, squeezingMatrix_zero]

end Squeezing

section PositiveSymplectic

/-- **Lemma 6.** For symplectic `S`, the matrix `S Sᵀ` is positive definite. -/
theorem posDef_mul_transpose {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) : (S * Sᵀ).PosDef := by
  have hU : IsUnit S := (isUnit_iff_isUnit_det S).2 (SymplecticGroup.symplectic_det hS)
  simpa [conjTranspose_eq_transpose_of_trivial] using
    PosDef.mul_conjTranspose_self S (vecMul_injective_iff_isUnit.2 hU)

/-- **Lemma 6.** For symplectic `S`, the matrix `S Sᵀ` is symplectic. -/
theorem mul_transpose_mem {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) : S * Sᵀ ∈ symplecticGroup (Fin n) ℝ :=
  Submonoid.mul_mem _ hS (SymplecticGroup.transpose_mem hS)

/-- **Lemma 6.** A symmetric symplectic matrix satisfies `M Ω = Ω M⁻¹`. -/
theorem mul_symplecticForm_eq {M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hMt : Mᵀ = M)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) :
    M * symplecticForm n = symplecticForm n * M⁻¹ := by
  have h := mem_symplecticGroup_iff.1 hM
  rw [hMt] at h
  calc M * symplecticForm n = M * symplecticForm n * (M * M⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ (SymplecticGroup.symplectic_det hM), Matrix.mul_one]
    _ = symplecticForm n * M⁻¹ := by rw [← Matrix.mul_assoc, h]

end PositiveSymplectic

section Eigen

variable {M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}

private theorem isUnit_of_mem {M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hM : M ∈ symplecticGroup (Fin n) ℝ) : IsUnit M :=
  (isUnit_iff_isUnit_det M).2 (SymplecticGroup.symplectic_det hM)

private theorem eq_zero_of_mulVec_eq_zero (hM : M ∈ symplecticGroup (Fin n) ℝ)
    {v : PhaseIndex n → ℝ} (hv : M *ᵥ v = 0) : v = 0 :=
  mulVec_injective_iff_isUnit.2 (isUnit_of_mem hM) (by rw [hv, mulVec_zero])

private theorem inv_mulVec_of_mulVec_eq_smul (hM : M ∈ symplecticGroup (Fin n) ℝ) {μ : ℝ}
    {v : PhaseIndex n → ℝ} (hv : M *ᵥ v = μ • v) : M⁻¹ *ᵥ v = μ⁻¹ • v := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [zero_smul] at hv
    rw [eq_zero_of_mulVec_eq_zero hM hv, mulVec_zero, smul_zero]
  · have h : M⁻¹ *ᵥ (M *ᵥ v) = v := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (SymplecticGroup.symplectic_det hM),
        one_mulVec]
    rw [hv, mulVec_smul] at h
    calc M⁻¹ *ᵥ v = μ⁻¹ • μ • M⁻¹ *ᵥ v := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • v := by rw [h]

/-- **Lemma 7.** Every eigenvalue of a symplectic matrix is nonzero. -/
theorem ne_zero_of_hasEigenvalue (hM : M ∈ symplecticGroup (Fin n) ℝ) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (toLin' M) μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  apply hv.2
  apply eq_zero_of_mulVec_eq_zero hM
  simpa using hv.apply_eq_smul

/-- **Lemma 7(i).** For symmetric symplectic `M`, `Ω` maps an eigenvector for `μ` to an
eigenvector for `μ⁻¹`. (For `μ = 0` both sides vanish, since `M` is invertible.) -/
theorem mulVec_symplecticForm_mulVec (hMt : Mᵀ = M) (hM : M ∈ symplecticGroup (Fin n) ℝ)
    {μ : ℝ} {v : PhaseIndex n → ℝ} (hv : M *ᵥ v = μ • v) :
    M *ᵥ (symplecticForm n *ᵥ v) = μ⁻¹ • (symplecticForm n *ᵥ v) := by
  rw [mulVec_mulVec, mul_symplecticForm_eq hMt hM, ← mulVec_mulVec,
    inv_mulVec_of_mulVec_eq_smul hM hv, mulVec_smul]

/-- **Lemma 7(i).** For symmetric symplectic `M`, `Ω` maps the eigenspace of `M` for `μ` onto the
eigenspace for `μ⁻¹`. -/
theorem map_eigenspace_symplecticForm (hMt : Mᵀ = M) (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (μ : ℝ) :
    (Module.End.eigenspace (toLin' M) μ).map (toLin' (symplecticForm n)) =
      Module.End.eigenspace (toLin' M) μ⁻¹ := by
  ext w
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, toLin'_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mulVec_symplecticForm_mulVec hMt hM hv
  · intro hw
    refine ⟨symplecticForm n *ᵥ (-w), ?_, ?_⟩
    · have h : M *ᵥ (-w) = μ⁻¹ • (-w) := by rw [mulVec_neg, hw, smul_neg]
      simpa using mulVec_symplecticForm_mulVec hMt hM h
    · rw [mulVec_mulVec, symplecticForm_sq, mulVec_neg, neg_mulVec, one_mulVec, neg_neg]

private theorem mulVec_dotProduct_of_transpose_eq (hMt : Mᵀ = M) (v u : PhaseIndex n → ℝ) :
    (M *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hMt, dotProduct_comm]

/-- **Lemma 7(ii).** For symmetric symplectic `M`, eigenvectors `v`, `w` for eigenvalues `μ`, `ν`
with `μ ν ≠ 1` are `Ω`-orthogonal: `⟨v, Ω w⟩ = 0`. -/
theorem dotProduct_symplecticForm_eq_zero (hMt : Mᵀ = M) (hM : M ∈ symplecticGroup (Fin n) ℝ)
    {μ ν : ℝ} {v w : PhaseIndex n → ℝ} (hv : M *ᵥ v = μ • v) (hw : M *ᵥ w = ν • w)
    (hμν : μ * ν ≠ 1) : v ⬝ᵥ (symplecticForm n *ᵥ w) = 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · rw [zero_smul] at hw
    rw [eq_zero_of_mulVec_eq_zero hM hw, mulVec_zero, dotProduct_zero]
  have h : μ * (v ⬝ᵥ (symplecticForm n *ᵥ w)) = ν⁻¹ * (v ⬝ᵥ (symplecticForm n *ᵥ w)) := by
    rw [← smul_eq_mul, ← smul_dotProduct, ← hv, mulVec_dotProduct_of_transpose_eq hMt,
      mulVec_symplecticForm_mulVec hMt hM hw, dotProduct_smul, smul_eq_mul]
  have hne : μ - ν⁻¹ ≠ 0 := by
    intro h'
    apply hμν
    rw [sub_eq_zero.1 h', inv_mul_cancel₀ hν]
  have h'' : (μ - ν⁻¹) * (v ⬝ᵥ (symplecticForm n *ᵥ w)) = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 h'').resolve_left hne

/-- **Lemma 7(ii).** For positive definite symplectic `M`, every eigenspace for an eigenvalue
`μ ≠ 1` is isotropic: `⟨v, Ω w⟩ = 0` for all `v`, `w` in it. -/
theorem isotropic_eigenspace (hMp : M.PosDef) (hM : M ∈ symplecticGroup (Fin n) ℝ) {μ : ℝ}
    (hμ : μ ≠ 1) {v w : PhaseIndex n → ℝ} (hv : M *ᵥ v = μ • v) (hw : M *ᵥ w = μ • w) :
    v ⬝ᵥ (symplecticForm n *ᵥ w) = 0 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [zero_dotProduct]
  have hMt : Mᵀ = M := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hMp.isHermitian.eq
  have hpos : 0 < μ := by
    have h₁ := hMp.dotProduct_mulVec_pos hv0
    rw [hv, star_trivial, dotProduct_smul, smul_eq_mul] at h₁
    have h₂ : 0 < v ⬝ᵥ v := by
      simpa [star_trivial] using (dotProduct_self_star_pos_iff (v := v)).2 hv0
    by_contra h
    nlinarith
  refine dotProduct_symplecticForm_eq_zero hMt hM hv hw fun h => ?_
  rcases mul_self_eq_one_iff.1 h with h | h
  · exact hμ h
  · linarith

/-- **Lemma 7(iii).** For symmetric symplectic `M`, the eigenspace for the eigenvalue `1` is
invariant under `Ω`. -/
theorem symplecticForm_mulVec_mem_eigenspace_one (hMt : Mᵀ = M)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) {v : PhaseIndex n → ℝ}
    (hv : v ∈ Module.End.eigenspace (toLin' M) 1) :
    symplecticForm n *ᵥ v ∈ Module.End.eigenspace (toLin' M) 1 := by
  rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hv ⊢
  simpa using mulVec_symplecticForm_mulVec hMt hM hv

end Eigen

section Diagonalization

/-! ### Theorem 8: symplectic diagonalization of a positive definite symplectic matrix

The proof chooses, one at a time, orthonormal eigenvectors `f j` of `M` with eigenvalues in
`(0, 1]` and `⟪f i, Ω f j⟫ = 0`, inside `EuclideanSpace ℝ (PhaseIndex n)`. The claims
`orthonormal_sumElim_neg_symplecticForm` to `columns_sumElim_neg_symplecticForm` are the steps. -/

open scoped InnerProductSpace

variable {M : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}

private theorem toEuclideanLin_eq_smul_iff {A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    {x : EuclideanSpace ℝ (PhaseIndex n)} {c : ℝ} :
    toEuclideanLin A x = c • x ↔ A *ᵥ WithLp.ofLp x = c • WithLp.ofLp x := by
  rw [← (WithLp.ofLp_injective 2).eq_iff]
  simp

private theorem inner_symplecticForm_left (x y : EuclideanSpace ℝ (PhaseIndex n)) :
    ⟪toEuclideanLin (symplecticForm n) x, y⟫_ℝ =
      -⟪x, toEuclideanLin (symplecticForm n) y⟫_ℝ := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial, transpose_symplecticForm, map_neg,
    LinearMap.neg_apply, inner_neg_right]

private theorem symplecticForm_symplecticForm (x : EuclideanSpace ℝ (PhaseIndex n)) :
    toEuclideanLin (symplecticForm n) (toEuclideanLin (symplecticForm n) x) = -x := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, symplecticForm_sq]
  simp

private theorem inner_symplecticForm_symplecticForm (x y : EuclideanSpace ℝ (PhaseIndex n)) :
    ⟪toEuclideanLin (symplecticForm n) x, toEuclideanLin (symplecticForm n) y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [inner_symplecticForm_left, symplecticForm_symplecticForm, inner_neg_right, neg_neg]

private theorem inner_self_symplecticForm (x : EuclideanSpace ℝ (PhaseIndex n)) :
    ⟪x, toEuclideanLin (symplecticForm n) x⟫_ℝ = 0 := by
  have h := inner_symplecticForm_left x x
  have h' := real_inner_comm x (toEuclideanLin (symplecticForm n) x)
  linarith

private theorem norm_symplecticForm (x : EuclideanSpace ℝ (PhaseIndex n)) :
    ‖toEuclideanLin (symplecticForm n) x‖ = ‖x‖ := by
  have h : ‖toEuclideanLin (symplecticForm n) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_symplecticForm_symplecticForm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private theorem toEuclideanLin_symplecticForm_of_eq_smul (hMt : Mᵀ = M)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) {μ : ℝ} {x : EuclideanSpace ℝ (PhaseIndex n)}
    (hx : toEuclideanLin M x = μ • x) :
    toEuclideanLin M (toEuclideanLin (symplecticForm n) x) =
      μ⁻¹ • toEuclideanLin (symplecticForm n) x := by
  rw [toEuclideanLin_eq_smul_iff] at hx ⊢
  simpa using mulVec_symplecticForm_mulVec hMt hM hx

private theorem isSymmetric_of_transpose_eq (hMt : Mᵀ = M) : (toEuclideanLin M).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.2 (by
    change Mᴴ = M
    rwa [conjTranspose_eq_transpose_of_trivial])

private theorem transpose_eq_of_posDef (hMp : M.PosDef) : Mᵀ = M := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hMp.isHermitian.eq

private theorem inner_toEuclideanLin_pos (hMp : M.PosDef) {x : EuclideanSpace ℝ (PhaseIndex n)}
    (hx : x ≠ 0) : 0 < ⟪x, toEuclideanLin M x⟫_ℝ := by
  have h := hMp.dotProduct_mulVec_pos (x := WithLp.ofLp x) (by simpa using hx)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa using h

/-- **Theorem 8, step 1.** If `f₁, …, f_k` are orthonormal with `⟪f i, Ω f j⟫ = 0`, then the `2k`
vectors `f j`, `-Ω f j` are orthonormal. -/
theorem orthonormal_sumElim_neg_symplecticForm {k : ℕ} {f : Fin k → EuclideanSpace ℝ (PhaseIndex n)}
    (hf : Orthonormal ℝ f) (hfΩ : ∀ i j, ⟪f i, toEuclideanLin (symplecticForm n) (f j)⟫_ℝ = 0) :
    Orthonormal ℝ (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j)) := by
  classical
  rw [orthonormal_iff_ite] at hf ⊢
  rintro (i | i) (j | j)
  · simpa using hf i j
  · simp [inner_neg_right, hfΩ]
  · simp [inner_neg_left, inner_symplecticForm_left, hfΩ]
  · simpa [inner_neg_left, inner_neg_right, inner_symplecticForm_symplecticForm] using hf i j

/-- **Theorem 8, step 2.** The span of the `2k` vectors `f j`, `-Ω f j` has dimension `2k`, so its
orthogonal complement has dimension `2n - 2k`. -/
theorem finrank_orthogonal_span_sumElim_neg_symplecticForm {k : ℕ}
    {f : Fin k → EuclideanSpace ℝ (PhaseIndex n)}
    (hf : Orthonormal ℝ f) (hfΩ : ∀ i j, ⟪f i, toEuclideanLin (symplecticForm n) (f j)⟫_ℝ = 0) :
    Module.finrank ℝ (Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ + 2 * k =
      n + n := by
  have h₁ := finrank_span_eq_card (orthonormal_sumElim_neg_symplecticForm hf hfΩ).linearIndependent
  have h₂ := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ
    (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))
  rw [finrank_euclideanSpace, h₁] at h₂
  simp only [Fintype.card_sum, Fintype.card_fin] at h₂
  omega

/-- **Theorem 8, step 3.** For symmetric symplectic `M` and eigenvectors `f j` of `M`, the
orthogonal complement of the span of the `f j`, `-Ω f j` is invariant under `M` and under `Ω`. -/
theorem mapsTo_orthogonal_span_sumElim_neg_symplecticForm (hMt : Mᵀ = M)
    (hM : M ∈ symplecticGroup (Fin n) ℝ)
    {k : ℕ} {f : Fin k → EuclideanSpace ℝ (PhaseIndex n)} {μ : Fin k → ℝ}
    (hfμ : ∀ j, toEuclideanLin M (f j) = μ j • f j) {v : EuclideanSpace ℝ (PhaseIndex n)}
    (hv : v ∈ (Submodule.span ℝ
      (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ) :
    toEuclideanLin M v ∈ (Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ ∧
      toEuclideanLin (symplecticForm n) v ∈ (Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ := by
  have hfK : ∀ j, f j ∈ Submodule.span ℝ
      (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) :=
    fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hgK : ∀ j, -toEuclideanLin (symplecticForm n) (f j) ∈ Submodule.span ℝ
      (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hTK : Submodule.span ℝ
      (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) ≤
      (Submodule.span ℝ (Set.range (Sum.elim f fun j =>
        -toEuclideanLin (symplecticForm n) (f j)))).comap (toEuclideanLin M) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j | j, rfl⟩
    · simpa [hfμ j] using Submodule.smul_mem _ (μ j) (hfK j)
    · simpa [toEuclideanLin_symplecticForm_of_eq_smul hMt hM (hfμ j)] using
        Submodule.smul_mem _ (μ j)⁻¹ (hgK j)
  have hΩK : Submodule.span ℝ
      (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) ≤
      (Submodule.span ℝ (Set.range (Sum.elim f fun j =>
        -toEuclideanLin (symplecticForm n) (f j)))).comap
          (toEuclideanLin (symplecticForm n)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j | j, rfl⟩
    · simpa using Submodule.neg_mem _ (hgK j)
    · simpa [symplecticForm_symplecticForm] using hfK j
  rw [Submodule.mem_orthogonal] at hv
  refine ⟨(Submodule.mem_orthogonal _ _).2 fun u hu => ?_,
    (Submodule.mem_orthogonal _ _).2 fun u hu => ?_⟩
  · rw [← isSymmetric_of_transpose_eq hMt u v]
    exact hv _ (hTK hu)
  · rw [← neg_neg ⟪u, _⟫_ℝ, ← inner_symplecticForm_left, hv _ (hΩK hu), neg_zero]

/-- **Theorem 8, step 4.** A nonzero subspace invariant under a positive definite `M` contains a
unit eigenvector of `M`, with positive eigenvalue. -/
theorem exists_unit_eigenvector_mem (hMp : M.PosDef)
    (W : Submodule ℝ (EuclideanSpace ℝ (PhaseIndex n))) (hW : W ≠ ⊥)
    (hMW : ∀ v ∈ W, toEuclideanLin M v ∈ W) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ ∃ μ : ℝ, 0 < μ ∧ toEuclideanLin M v = μ • v := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
  have hT := (isSymmetric_of_transpose_eq (transpose_eq_of_posDef hMp)).restrict_invariant hMW
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, Module.End.HasEigenvalue ((toEuclideanLin M).restrict hMW) μ :=
    ⟨_, hT.hasEigenvalue_iSup_of_finiteDimensional⟩
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : EuclideanSpace ℝ (PhaseIndex n)) ≠ 0 := by
    simpa using hw.2
  have hTw : toEuclideanLin M w = μ • (w : EuclideanSpace ℝ (PhaseIndex n)) := by
    simpa using congrArg Subtype.val hw.apply_eq_smul
  refine ⟨‖(w : EuclideanSpace ℝ (PhaseIndex n))‖⁻¹ • (w : EuclideanSpace ℝ (PhaseIndex n)),
    W.smul_mem _ w.2, ?_, μ, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  · have hpos := inner_toEuclideanLin_pos hMp hw0
    rw [hTw, inner_smul_right, real_inner_self_eq_norm_sq] at hpos
    exact (pos_iff_pos_of_mul_pos hpos).2 (by positivity)
  · rw [map_smul, hTw, smul_comm]

/-- **Theorem 8, step 5 (the induction).** For positive definite symplectic `M` and `k ≤ n` there
are orthonormal eigenvectors `f₁, …, f_k` of `M` with eigenvalues in `(0, 1]` and
`⟪f i, Ω f j⟫ = 0`. -/
theorem exists_orthonormal_isotropic_eigenvectors (hMp : M.PosDef)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) (k : ℕ) (hk : k ≤ n) :
    ∃ (f : Fin k → EuclideanSpace ℝ (PhaseIndex n)) (μ : Fin k → ℝ), Orthonormal ℝ f ∧
      (∀ i j, ⟪f i, toEuclideanLin (symplecticForm n) (f j)⟫_ℝ = 0) ∧
      ∀ j, 0 < μ j ∧ μ j ≤ 1 ∧ toEuclideanLin M (f j) = μ j • f j := by
  classical
  have hMt := transpose_eq_of_posDef hMp
  induction k with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, orthonormal_iff_ite.2 fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨f, μ, hf, hfΩ, hfμ⟩ := ih (by omega)
    have hdim := finrank_orthogonal_span_sumElim_neg_symplecticForm hf hfΩ
    have hfK : ∀ j, f j ∈ Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) :=
      fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
    have hΩfK : ∀ j, toEuclideanLin (symplecticForm n) (f j) ∈ Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) := by
      intro j
      simpa using Submodule.neg_mem _ (Submodule.subset_span (R := ℝ) (s := Set.range
        (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))) ⟨Sum.inr j, rfl⟩)
    have hne : (Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hdim
      omega
    have hmaps := fun v hv =>
      mapsTo_orthogonal_span_sumElim_neg_symplecticForm hMt hM (fun j => (hfμ j).2.2) (v := v) hv
    obtain ⟨v, hvK, hv1, ν, hν, hvν⟩ :=
      exists_unit_eigenvector_mem hMp _ hne fun v hv => (hmaps v hv).1
    obtain ⟨g, l, hgK, hg1, hl0, hl1, hgl⟩ : ∃ (g : EuclideanSpace ℝ (PhaseIndex n)) (l : ℝ),
        g ∈ (Submodule.span ℝ
        (Set.range (Sum.elim f fun j => -toEuclideanLin (symplecticForm n) (f j))))ᗮ ∧
        ‖g‖ = 1 ∧ 0 < l ∧ l ≤ 1 ∧ toEuclideanLin M g = l • g := by
      by_cases hle : ν ≤ 1
      · exact ⟨v, ν, hvK, hv1, hν, hle, hvν⟩
      · exact ⟨toEuclideanLin (symplecticForm n) v, ν⁻¹, (hmaps v hvK).2,
          by rw [norm_symplecticForm, hv1], inv_pos.2 hν,
          inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hle)),
          toEuclideanLin_symplecticForm_of_eq_smul hMt hM hvν⟩
    have hgf : ∀ j, ⟪g, f j⟫_ℝ = 0 := fun j =>
      Submodule.inner_left_of_mem_orthogonal (hfK j) hgK
    have hgΩf : ∀ j, ⟪g, toEuclideanLin (symplecticForm n) (f j)⟫_ℝ = 0 := fun j =>
      Submodule.inner_left_of_mem_orthogonal (hΩfK j) hgK
    have hfΩg : ∀ j, ⟪f j, toEuclideanLin (symplecticForm n) g⟫_ℝ = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal (hfK j) (hmaps g hgK).2
    refine ⟨Fin.cons g f, Fin.cons l μ, ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hf ⊢
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hg1]
      · simp [hgf j, (Fin.succ_ne_zero j).symm]
      · simp [real_inner_comm, hgf i, Fin.succ_ne_zero i]
      · simpa using hf i j
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using inner_self_symplecticForm g
      · simpa using hgΩf j
      · simpa using hfΩg i
      · simpa using hfΩ i j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using ⟨hl0, hl1, hgl⟩
      · simpa using hfμ j

private theorem transpose_mul_mul_of_apply (b : PhaseIndex n → EuclideanSpace ℝ (PhaseIndex n))
    (A : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (c d : PhaseIndex n) :
    ((Matrix.of fun i c => b c i)ᵀ * A * Matrix.of fun i c => b c i) c d =
      ⟪b c, toEuclideanLin A (b d)⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  simp only [star_trivial, dotProduct, mulVec, Matrix.mul_apply,
    transpose_apply, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Theorem 8, step 6.** For symmetric symplectic `M` and orthonormal eigenvectors
`f₁, …, fₙ` of `M` with `⟪f i, Ω f j⟫ = 0`, the matrix with columns `f₁, …, fₙ, -Ω f₁, …, -Ω fₙ`
is orthogonal and symplectic and satisfies `M O = O diag(μ, μ⁻¹)`. -/
theorem columns_sumElim_neg_symplecticForm (hMt : Mᵀ = M) (hM : M ∈ symplecticGroup (Fin n) ℝ)
    {f : Fin n → EuclideanSpace ℝ (PhaseIndex n)} {μ : Fin n → ℝ} (hf : Orthonormal ℝ f)
    (hfΩ : ∀ i j, ⟪f i, toEuclideanLin (symplecticForm n) (f j)⟫_ℝ = 0)
    (hfμ : ∀ j, toEuclideanLin M (f j) = μ j • f j) :
    (Matrix.of fun i c => Sum.elim f (fun j => -toEuclideanLin (symplecticForm n) (f j)) c i) ∈
        symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ∧
      M * (Matrix.of fun i c =>
          Sum.elim f (fun j => -toEuclideanLin (symplecticForm n) (f j)) c i) =
        (Matrix.of fun i c =>
          Sum.elim f (fun j => -toEuclideanLin (symplecticForm n) (f j)) c i) *
          diagonal (Sum.elim μ fun k => (μ k)⁻¹) := by
  classical
  have ho := orthonormal_iff_ite.1 (orthonormal_sumElim_neg_symplecticForm hf hfΩ)
  have hf' := orthonormal_iff_ite.1 hf
  refine ⟨Submonoid.mem_inf.2 ⟨mem_symplecticGroup_iff'.2 ?_, ?_⟩, ?_⟩
  · ext c d
    rw [transpose_mul_mul_of_apply]
    conv_rhs => rw [symplecticForm_eq_fromBlocks]
    rcases c with i | i <;> rcases d with j | j
    · simp [hfΩ]
    · simp [symplecticForm_symplecticForm, hf', Matrix.one_apply]
    · simp [inner_neg_left, inner_symplecticForm_symplecticForm, hf', Matrix.one_apply]
    · simp [symplecticForm_symplecticForm, inner_neg_left, inner_symplecticForm_left, hfΩ]
  · rw [mem_orthogonalGroup_iff']
    ext c d
    rw [← Matrix.mul_one (Matrix.of _)ᵀ, transpose_mul_mul_of_apply]
    simpa [Matrix.one_apply] using ho c d
  · ext i c
    rw [mul_diagonal]
    have h : (M * Matrix.of fun i c =>
        Sum.elim f (fun j => -toEuclideanLin (symplecticForm n) (f j)) c i) i c =
        toEuclideanLin M (Sum.elim f (fun j => -toEuclideanLin (symplecticForm n) (f j)) c) i := by
      simp [Matrix.mul_apply, Matrix.toLpLin_apply, mulVec, dotProduct]
    rw [h]
    rcases c with j | j
    · simp [hfμ j, mul_comm]
    · simp [toEuclideanLin_symplecticForm_of_eq_smul hMt hM (hfμ j), mul_comm]

/-- **Theorem 8** (paper (A8)–(A10)), with the construction: a positive definite symplectic `M`
is `O Σ(r)² Oᵀ` with `r ≥ 0` and `O` orthogonal symplectic, where `O` may be taken with columns
`f₁, …, fₙ, -Ω f₁, …, -Ω fₙ` for orthonormal `f k` with `M f k = e^{-2 r_k} f k` and
`⟪f j, Ω f k⟫ = 0`. -/
theorem exists_orthogonalSymplectic_diagonalization_columns (hMp : M.PosDef)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) :
    ∃ (f : Fin n → EuclideanSpace ℝ (PhaseIndex n)) (r : Fin n → ℝ), 0 ≤ r ∧ Orthonormal ℝ f ∧
      (∀ j k, ⟪f j, toEuclideanLin (symplecticForm n) (f k)⟫_ℝ = 0) ∧
      (∀ k, toEuclideanLin M (f k) = Real.exp (-2 * r k) • f k) ∧
      (Matrix.of fun i c => Sum.elim f (fun k => -toEuclideanLin (symplecticForm n) (f k)) c i) ∈
        symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ∧
      M = (Matrix.of fun i c =>
          Sum.elim f (fun k => -toEuclideanLin (symplecticForm n) (f k)) c i) *
        squeezingMatrix r ^ 2 * (Matrix.of fun i c =>
          Sum.elim f (fun k => -toEuclideanLin (symplecticForm n) (f k)) c i)ᵀ := by
  have hMt := transpose_eq_of_posDef hMp
  obtain ⟨f, μ, hf, hfΩ, hfμ⟩ := exists_orthonormal_isotropic_eigenvectors hMp hM n le_rfl
  have hexp : ∀ k, Real.exp (-2 * (-Real.log (μ k) / 2)) = μ k := fun k => by
    rw [show -2 * (-Real.log (μ k) / 2) = Real.log (μ k) by ring, Real.exp_log (hfμ k).1]
  have hSq : squeezingMatrix (fun k => -Real.log (μ k) / 2) ^ 2 =
      diagonal (Sum.elim μ fun k => (μ k)⁻¹) := by
    rw [sq, ← squeezingMatrix_add, squeezingMatrix]
    congr 1
    ext (k | k)
    · simp only [Sum.elim_inl, Pi.add_apply]
      convert Real.exp_log (hfμ k).1 using 2
      ring
    · simp only [Sum.elim_inr, Pi.add_apply]
      rw [← Real.exp_log (inv_pos.2 (hfμ k).1), Real.log_inv]
      congr 1
      ring
  obtain ⟨hO, hMO⟩ := columns_sumElim_neg_symplecticForm hMt hM hf hfΩ fun j => (hfμ j).2.2
  refine ⟨f, fun k => -Real.log (μ k) / 2, fun k => ?_, hf, hfΩ,
    fun k => by rw [hexp, (hfμ k).2.2], hO, ?_⟩
  · have := Real.log_nonpos (hfμ k).1.le (hfμ k).2.1
    simp only [Pi.zero_apply]
    linarith
  · rw [hSq, ← hMO, Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 (Submonoid.mem_inf.1 hO).2,
      Matrix.mul_one]

/-- **Theorem 8** (paper (A8)–(A10)). Every positive definite symplectic matrix `M` is
`O Σ(r)² Oᵀ` with `O` orthogonal symplectic and `r ≥ 0`. -/
theorem exists_orthogonalSymplectic_diagonalization (hMp : M.PosDef)
    (hM : M ∈ symplecticGroup (Fin n) ℝ) :
    ∃ O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ, ∃ r : Fin n → ℝ,
      0 ≤ r ∧ M = O * squeezingMatrix r ^ 2 * Oᵀ := by
  obtain ⟨f, r, hr, -, -, -, hO, hMO⟩ := exists_orthogonalSymplectic_diagonalization_columns hMp hM
  exact ⟨_, hO, r, hr, hMO⟩

end Diagonalization

section BlochMessiah

variable {S : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}

/-- **Theorem 9, the step of the proof.** If `S Sᵀ = O_U Σ(r)² O_Uᵀ` with `O_U` orthogonal
symplectic, then `O_W = Σ(-r) O_Uᵀ S` is orthogonal symplectic. -/
theorem blochMessiah_right_mem {OU : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {r : Fin n → ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ)
    (hOU : OU ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)
    (hM : S * Sᵀ = OU * squeezingMatrix r ^ 2 * OUᵀ) :
    squeezingMatrix (-r) * OUᵀ * S ∈
      symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ := by
  obtain ⟨hOUs, hOUo⟩ := Submonoid.mem_inf.1 hOU
  have hOt : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hOUo
  refine Submonoid.mem_inf.2 ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ (squeezingMatrix_mem _)
    (SymplecticGroup.transpose_mem hOUs)) hS, ?_⟩
  rw [mem_orthogonalGroup_iff]
  calc squeezingMatrix (-r) * OUᵀ * S * (squeezingMatrix (-r) * OUᵀ * S)ᵀ
      = squeezingMatrix (-r) * OUᵀ * (S * Sᵀ) * OU * squeezingMatrix (-r) := by
        simp only [transpose_mul, transpose_transpose, squeezingMatrix_transpose,
          Matrix.mul_assoc]
    _ = squeezingMatrix (-r) * (OUᵀ * OU) * squeezingMatrix r * squeezingMatrix r *
          (OUᵀ * OU) * squeezingMatrix (-r) := by
        rw [hM, sq]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hOt]
        simp only [Matrix.mul_one]
        rw [squeezingMatrix_neg_mul, Matrix.one_mul, squeezingMatrix_mul_neg]

/-- **Theorem 9, the Bloch–Messiah decomposition** (paper (A11)). Every real symplectic matrix
is `S = O_U Σ(r) O_W` with `O_U`, `O_W` orthogonal symplectic and `r ≥ 0`. -/
theorem exists_blochMessiah (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    ∃ OU ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ,
    ∃ OW ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ,
    ∃ r : Fin n → ℝ, 0 ≤ r ∧ S = OU * squeezingMatrix r * OW := by
  obtain ⟨OU, hOU, r, hr, hM⟩ :=
    exists_orthogonalSymplectic_diagonalization (posDef_mul_transpose hS) (mul_transpose_mem hS)
  refine ⟨OU, hOU, _, blochMessiah_right_mem hS hOU hM, r, hr, ?_⟩
  have h : OU * OUᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 (Submonoid.mem_inf.1 hOU).2
  calc S = OU * OUᵀ * S := by rw [h, Matrix.one_mul]
    _ = OU * (squeezingMatrix r * squeezingMatrix (-r)) * OUᵀ * S := by
        rw [squeezingMatrix_mul_neg, Matrix.mul_one]
    _ = OU * squeezingMatrix r * (squeezingMatrix (-r) * OUᵀ * S) := by
        simp only [Matrix.mul_assoc]

end BlochMessiah

section SingularValues

open Polynomial

variable {S OU OW : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {r : Fin n → ℝ}

private theorem charpoly_squeezingMatrix_mul_self (r : Fin n → ℝ) :
    (squeezingMatrix r * squeezingMatrix r).charpoly =
      ∏ k, (X - C (Real.exp (-2 * r k))) * (X - C (Real.exp (2 * r k))) := by
  rw [← squeezingMatrix_add, squeezingMatrix, charpoly_diagonal, Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
  rw [show -(r k + r k) = -2 * r k by ring, show r k + r k = 2 * r k by ring]

/-- **Proposition 10(a).** If `S = O₁ Σ(r) O₂` with `O₁`, `O₂` orthogonal, then `S Sᵀ` has the
characteristic polynomial `∏ₖ (t - e^{-2 r_k}) (t - e^{2 r_k})`. -/
theorem charpoly_mul_transpose_of_eq (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = OU * squeezingMatrix r * OW) :
    (S * Sᵀ).charpoly = ∏ k, (X - C (Real.exp (-2 * r k))) * (X - C (Real.exp (2 * r k))) := by
  have hW' : OW * OWᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hW
  have hU' : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hU
  have h : S * Sᵀ = OU * (squeezingMatrix r * (squeezingMatrix r * OUᵀ)) := by
    rw [hS]
    simp only [transpose_mul, squeezingMatrix_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc OW, hW', Matrix.one_mul]
  rw [h, charpoly_mul_comm, ← charpoly_squeezingMatrix_mul_self]
  simp only [Matrix.mul_assoc, hU', Matrix.mul_one]

/-- **Proposition 10(a).** If `S = O₁ Σ(r) O₂` with `O₁`, `O₂` orthogonal, then `Sᵀ S` has the
characteristic polynomial `∏ₖ (t - e^{-2 r_k}) (t - e^{2 r_k})`. -/
theorem charpoly_transpose_mul_of_eq (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = OU * squeezingMatrix r * OW) :
    (Sᵀ * S).charpoly = ∏ k, (X - C (Real.exp (-2 * r k))) * (X - C (Real.exp (2 * r k))) := by
  have hW' : OW * OWᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hW
  have hU' : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hU
  have h : Sᵀ * S = OWᵀ * (squeezingMatrix r * (squeezingMatrix r * OW)) := by
    rw [hS]
    simp only [transpose_mul, squeezingMatrix_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc OUᵀ, hU', Matrix.one_mul]
  rw [h, charpoly_mul_comm, ← charpoly_squeezingMatrix_mul_self]
  simp only [Matrix.mul_assoc, hW', Matrix.mul_one]

private theorem roots_prod_X_sub_C_mul_X_sub_C (a b : Fin n → ℝ) :
    (∏ k, (X - C (a k)) * (X - C (b k))).roots =
      Finset.univ.val.map a + Finset.univ.val.map b := by
  rw [roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun k _ =>
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp_rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C]
  rw [Multiset.bind_add, Multiset.bind_singleton, Multiset.bind_singleton]

private theorem multiset_range_eq (m : ℕ) :
    Multiset.range m = (Finset.univ : Finset (Fin m)).val.map Fin.val := by
  rw [← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val]
  rfl

/-- **Proposition 10(a).** If `S = O₁ Σ(r) O₂` with `O₁`, `O₂` orthogonal, then the singular
values of `S` (Mathlib's `LinearMap.singularValues`, whose first `2n` entries are the square roots
of the eigenvalues of `Sᵀ S` with multiplicity, the later ones being `0`) are
`e^{-r₁}, …, e^{-rₙ}, e^{r₁}, …, e^{rₙ}`. -/
theorem singularValues_of_eq (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = OU * squeezingMatrix r * OW) :
    (Multiset.range (n + n)).map (fun i => (toEuclideanLin S).singularValues i) =
      Finset.univ.val.map (fun k => Real.exp (-r k)) +
        Finset.univ.val.map (fun k => Real.exp (r k)) := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (PhaseIndex n)) = n + n := by
    simp [finrank_euclideanSpace]
  have hsym := (toEuclideanLin S).isSymmetric_adjoint_comp_self
  have hTT : LinearMap.adjoint (toEuclideanLin S) ∘ₗ toEuclideanLin S =
      toEuclideanLin (Sᵀ * S) := by
    rw [Matrix.toLpLin_mul_same, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial]
  have hcp : (LinearMap.adjoint (toEuclideanLin S) ∘ₗ toEuclideanLin S).charpoly =
      (Sᵀ * S).charpoly := by
    rw [hTT, toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
  have hroots := hsym.roots_charpoly_eq_eigenvalues hn
  rw [hcp, charpoly_transpose_mul_of_eq hU hW hS, roots_prod_X_sub_C_mul_X_sub_C,
    RCLike.ofReal_real_eq_id, Function.id_comp] at hroots
  rw [multiset_range_eq, Multiset.map_map]
  have h₁ : ((toEuclideanLin S).singularValues ∘ Fin.val : Fin (n + n) → ℝ) =
      Real.sqrt ∘ hsym.eigenvalues hn := by
    funext i
    exact (toEuclideanLin S).singularValues_fin hn i
  rw [h₁, ← Multiset.map_map Real.sqrt, ← hroots, Multiset.map_add, Multiset.map_map,
    Multiset.map_map]
  congr 1 <;> refine Multiset.map_congr rfl fun k _ => ?_ <;>
    rw [Function.comp_apply, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _),
      ← Real.exp_add] <;>
    congr 1 <;> ring

/-- **Proposition 10(b), intermediate claim.** For `r ≥ 0`, the map `t ↦ |log t| / 2` sends the
roots of `∏ₖ (t - e^{-2 r_k}) (t - e^{2 r_k})` to two copies of the multiset `{r_k}`. -/
theorem roots_map_abs_log (hr : 0 ≤ r) :
    ((∏ k, (X - C (Real.exp (-2 * r k))) * (X - C (Real.exp (2 * r k)))).roots.map
      fun t => |Real.log t| / 2) = 2 • Finset.univ.val.map r := by
  have hrk : ∀ k, 0 ≤ r k := fun k => hr k
  rw [roots_prod_X_sub_C_mul_X_sub_C, Multiset.map_add, Multiset.map_map, Multiset.map_map,
    two_nsmul]
  congr 1 <;> refine Multiset.map_congr rfl fun k _ => ?_ <;> simp only [Function.comp_apply]
  · rw [Real.log_exp, abs_of_nonpos (by linarith [hrk k])]
    ring
  · rw [Real.log_exp, abs_of_nonneg (by linarith [hrk k])]
    ring

/-- **Proposition 10(b).** In two decompositions `S = O_U Σ(r) O_W = O_U' Σ(r') O_W'` with
orthogonal factors and `r, r' ≥ 0`, the multisets of squeezing parameters agree. -/
theorem map_univ_eq_of_blochMessiah {OU' OW' : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    {r' : Fin n → ℝ} (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hU' : OU' ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW' : OW' ∈ orthogonalGroup (PhaseIndex n) ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : S = OU * squeezingMatrix r * OW) (h' : S = OU' * squeezingMatrix r' * OW') :
    Finset.univ.val.map r = Finset.univ.val.map r' := by
  have hp := (charpoly_mul_transpose_of_eq hU hW h).symm.trans
    (charpoly_mul_transpose_of_eq hU' hW' h')
  have h2 := congrArg (fun p : ℝ[X] => p.roots.map fun t => |Real.log t| / 2) hp
  simp only [roots_map_abs_log hr, roots_map_abs_log hr'] at h2
  ext a
  have := congrArg (Multiset.count a) h2
  simp only [Multiset.count_nsmul] at this
  omega

private theorem exists_perm_of_map_univ_eq {r r' : Fin n → ℝ}
    (h : Finset.univ.val.map r = Finset.univ.val.map r') :
    ∃ σ : Equiv.Perm (Fin n), r' = r ∘ σ := by
  classical
  have hcard : ∀ c, Fintype.card {i // r' i = c} = Fintype.card {i // r i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card, Finset.filter_val,
      Finset.filter_val]
    simpa [eq_comm] using this.symm
  refine ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

/-- **Proposition 10(b).** In two decompositions `S = O_U Σ(r) O_W = O_U' Σ(r') O_W'` with
orthogonal factors and `r, r' ≥ 0`, the squeezing parameters differ by a permutation:
`r' = r ∘ σ`. -/
theorem exists_perm_of_blochMessiah {OU' OW' : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    {r' : Fin n → ℝ} (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hU' : OU' ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW' : OW' ∈ orthogonalGroup (PhaseIndex n) ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : S = OU * squeezingMatrix r * OW) (h' : S = OU' * squeezingMatrix r' * OW') :
    ∃ σ : Equiv.Perm (Fin n), r' = r ∘ σ :=
  exists_perm_of_map_univ_eq (map_univ_eq_of_blochMessiah hU hW hU' hW' hr hr' h h')

end SingularValues

section NonUniqueness

variable {S OU OW : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}

/-- **Example 11.** `-1 = O_{-1}` is orthogonal and symplectic. -/
theorem neg_one_mem_orthogonalSymplectic :
    (-1 : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) ∈
      symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ := by
  have h := orthogonalSymplecticOfUnitary_mem (n := n) (-1)
  rwa [orthogonalSymplecticOfUnitary_neg, orthogonalSymplecticOfUnitary_one] at h

/-- **Example 11.** The orthogonal symplectic matrices are closed under negation. -/
theorem neg_mem_orthogonalSymplectic {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hO : O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ) :
    -O ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ := by
  simpa using Submonoid.mul_mem _ neg_one_mem_orthogonalSymplectic hO

/-- **Example 11.** For `n > 0`, an orthogonal matrix differs from its negative. -/
theorem neg_ne_self_of_mem_orthogonalGroup [NeZero n] {O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hO : O ∈ orthogonalGroup (PhaseIndex n) ℝ) : -O ≠ O := by
  intro h
  have h0 : O = 0 := by
    ext i j
    have := congr_fun (congr_fun h i) j
    simp only [Matrix.neg_apply] at this
    simp only [Matrix.zero_apply]
    linarith
  have h1 := (mem_orthogonalGroup_iff _ _).1 hO
  rw [h0, Matrix.zero_mul] at h1
  have : Nonempty (PhaseIndex n) := ⟨Sum.inl 0⟩
  exact zero_ne_one h1

/-- **Example 11.** The orthogonal factors are never unique: `S = O_U Σ(r) O_W` implies
`S = (-O_U) Σ(r) (-O_W)`. -/
theorem eq_neg_mul_squeezingMatrix_mul_neg {r : Fin n → ℝ}
    (h : S = OU * squeezingMatrix r * OW) : S = -OU * squeezingMatrix r * -OW := by
  rw [h, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end NonUniqueness

section Polar

open scoped MatrixOrder

variable {S OU OW : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} {r : Fin n → ℝ}

private theorem posDef_conj_squeezingMatrix (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (r : Fin n → ℝ) : (OU * squeezingMatrix r * OUᵀ).PosDef := by
  have hunit : IsUnit OU := (isUnit_iff_isUnit_det OU).2
    (isUnit_det_of_right_inverse ((mem_orthogonalGroup_iff _ _).1 hU))
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (posDef_squeezingMatrix r).mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.2 hunit)

private theorem conj_squeezingMatrix_mul_self (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = OU * squeezingMatrix r * OW) :
    OU * squeezingMatrix r * OUᵀ * (OU * squeezingMatrix r * OUᵀ) = S * Sᵀ := by
  have hW' : OW * OWᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hW
  have hU' : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hU
  rw [hS]
  simp only [transpose_mul, squeezingMatrix_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc OW, hW', Matrix.one_mul, ← Matrix.mul_assoc OUᵀ, hU', Matrix.one_mul]

private theorem inv_conj_squeezingMatrix (hU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ) :
    (OU * squeezingMatrix r * OUᵀ)⁻¹ = OU * squeezingMatrix (-r) * OUᵀ := by
  have hU' : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hU
  have hU'' : OU * OUᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hU
  refine Matrix.inv_eq_right_inv ?_
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc OUᵀ, hU', Matrix.one_mul, ← Matrix.mul_assoc (squeezingMatrix r),
    squeezingMatrix_mul_neg, Matrix.one_mul, hU'']

/-- **Corollary 12** (paper (A4)–(A10)). For `S = O_U Σ(r) O_W` with orthogonal symplectic
factors, `P = O_U Σ(r) O_Uᵀ` is positive definite and symplectic, `P² = S Sᵀ`,
`Q = P⁻¹ S = O_U O_W` is orthogonal symplectic and `S = P Q`. -/
theorem polar_of_blochMessiah
    (hOU : OU ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)
    (hOW : OW ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ)
    (hS : S = OU * squeezingMatrix r * OW) :
    (OU * squeezingMatrix r * OUᵀ).PosDef ∧
      OU * squeezingMatrix r * OUᵀ ∈ symplecticGroup (Fin n) ℝ ∧
      OU * squeezingMatrix r * OUᵀ * (OU * squeezingMatrix r * OUᵀ) = S * Sᵀ ∧
      (OU * squeezingMatrix r * OUᵀ)⁻¹ * S = OU * OW ∧
      OU * OW ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ∧
      S = OU * squeezingMatrix r * OUᵀ * (OU * OW) := by
  obtain ⟨hUs, hUo⟩ := Submonoid.mem_inf.1 hOU
  obtain ⟨-, hWo⟩ := Submonoid.mem_inf.1 hOW
  have hU' : OUᵀ * OU = 1 := (mem_orthogonalGroup_iff' _ _).1 hUo
  refine ⟨posDef_conj_squeezingMatrix hUo r,
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hUs (squeezingMatrix_mem r))
      (SymplecticGroup.transpose_mem hUs),
    conj_squeezingMatrix_mul_self hUo hWo hS, ?_, Submonoid.mul_mem _ hOU hOW, ?_⟩
  · rw [inv_conj_squeezingMatrix hUo, hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc OUᵀ, hU', Matrix.one_mul, ← Matrix.mul_assoc (squeezingMatrix (-r)),
      squeezingMatrix_neg_mul, Matrix.one_mul]
  · rw [hS]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc OUᵀ, hU', Matrix.one_mul]

/-- **Corollary 12.** For `S = O_U Σ(r) O_W` with orthogonal factors, `O_U Σ(r) O_Uᵀ` is the
positive square root `(S Sᵀ)^{1/2}` (Mathlib's `CFC.sqrt`); in particular it does not depend on
the decomposition. -/
theorem cfcSqrt_mul_transpose_eq (hOU : OU ∈ orthogonalGroup (PhaseIndex n) ℝ)
    (hOW : OW ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = OU * squeezingMatrix r * OW) :
    CFC.sqrt (S * Sᵀ) = OU * squeezingMatrix r * OUᵀ :=
  CFC.sqrt_unique (conj_squeezingMatrix_mul_self hOU hOW hS)
    (posDef_conj_squeezingMatrix hOU r).posSemidef.nonneg

/-- **Corollary 12** (paper (A4)–(A5)). For symplectic `S`, `P = (S Sᵀ)^{1/2}` is positive
definite and symplectic, `Q = P⁻¹ S` is orthogonal symplectic, and `S = P Q`. -/
theorem polar_decomposition (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    (CFC.sqrt (S * Sᵀ)).PosDef ∧ CFC.sqrt (S * Sᵀ) ∈ symplecticGroup (Fin n) ℝ ∧
      (CFC.sqrt (S * Sᵀ))⁻¹ * S ∈ symplecticGroup (Fin n) ℝ ⊓ orthogonalGroup (PhaseIndex n) ℝ ∧
      S = CFC.sqrt (S * Sᵀ) * ((CFC.sqrt (S * Sᵀ))⁻¹ * S) := by
  obtain ⟨OU, hOU, OW, hOW, r, -, h⟩ := exists_blochMessiah hS
  obtain ⟨hP, hPs, -, hQ, hQm, hSPQ⟩ := polar_of_blochMessiah hOU hOW h
  rw [cfcSqrt_mul_transpose_eq (Submonoid.mem_inf.1 hOU).2 (Submonoid.mem_inf.1 hOW).2 h, hQ]
  exact ⟨hP, hPs, hQm, hSPQ⟩

/-- **Corollary 12, uniqueness of the polar decomposition.** If `S = P O` with `P` positive
definite and `O` orthogonal, then `P = (S Sᵀ)^{1/2}` and `O = P⁻¹ S`. -/
theorem polar_unique {P O : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hP : P.PosDef)
    (hO : O ∈ orthogonalGroup (PhaseIndex n) ℝ) (hS : S = P * O) :
    P = CFC.sqrt (S * Sᵀ) ∧ O = (CFC.sqrt (S * Sᵀ))⁻¹ * S := by
  have hPt : Pᵀ = P := transpose_eq_of_posDef hP
  have hO' : O * Oᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hO
  have hPP : P * P = S * Sᵀ := by
    rw [hS, transpose_mul, hPt, Matrix.mul_assoc, ← Matrix.mul_assoc O, hO', Matrix.one_mul]
  have hsq : CFC.sqrt (S * Sᵀ) = P := CFC.sqrt_unique hPP hP.posSemidef.nonneg
  refine ⟨hsq.symm, ?_⟩
  rw [hsq, hS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det P).1 hP.isUnit),
    Matrix.one_mul]

end Polar

end Gaussian
