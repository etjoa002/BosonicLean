/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.Basic

/-!
# Weyl systems

A Weyl system over `(V, σ)` is a unital C*-algebra with unitaries `W u` satisfying the Weyl relation
and generating the algebra. The concrete algebra `CCR σ` is an instance.

## Main definitions

* `BosonicLean.Weyl.WeylSystem σ A`: a Weyl system over `(V, σ)` in `A`.
* `BosonicLean.Weyl.CCR.weylSystem`: `CCR σ` with the Weyl operators.

## Main statements

* `WeylSystem.map_zero`, `WeylSystem.star_eq`, `WeylSystem.mul_comm_phase`,
  `WeylSystem.commute_of_eq_zero`.
-/

noncomputable section

namespace BosonicLean

namespace Weyl

open StarAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Weyl phase `e^{-iσ(u,w)/2}` of the relation (W2). -/
def relPhase (σ : LinearMap.BilinForm ℝ V) (u w : V) : ℂ :=
  Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I)

/-- A Weyl system over `(V, σ)` in the C*-algebra `A`. -/
structure WeylSystem (σ : LinearMap.BilinForm ℝ V) (A : Type*) [CStarAlgebra A] where
  /-- The Weyl elements. -/
  W : V → A
  /-- (W1) each `W u` is unitary. -/
  mem_unitary : ∀ u, W u ∈ unitary A
  /-- (W2) the Weyl relation. -/
  mul_eq : ∀ u w, W u * W w = relPhase σ u w • W (u + w)
  /-- (W3) the Weyl elements generate `A` as a C*-algebra. -/
  generating : (adjoin ℂ (Set.range W)).topologicalClosure = ⊤

namespace WeylSystem

variable {σ : LinearMap.BilinForm ℝ V} {A : Type*} [CStarAlgebra A] (S : WeylSystem σ A)

/-- `W 0 = 1`. -/
theorem map_zero : S.W 0 = 1 := by
  have h0 : S.W 0 * S.W 0 = S.W 0 := by
    rw [S.mul_eq, add_zero]; simp [relPhase]
  have hu := Unitary.mem_iff.1 (S.mem_unitary 0)
  calc S.W 0 = star (S.W 0) * S.W 0 * S.W 0 := by rw [hu.1, one_mul]
    _ = 1 := by rw [mul_assoc, h0, hu.1]

/-- `W(u)* = W(-u)`. -/
theorem star_eq (hσ : σ.IsAlt) (u : V) : star (S.W u) = S.W (-u) := by
  have h1 : S.W u * S.W (-u) = 1 := by
    rw [S.mul_eq, add_neg_cancel, S.map_zero]; simp [relPhase, hσ u]
  have hu := Unitary.mem_iff.1 (S.mem_unitary u)
  calc star (S.W u) = star (S.W u) * (S.W u * S.W (-u)) := by rw [h1, mul_one]
    _ = S.W (-u) := by rw [← mul_assoc, hu.1, one_mul]


/-- `W(u) W(w) = e^{-iσ(u,w)} W(w) W(u)`. -/
theorem mul_comm_phase (hσ : σ.IsAlt) (u w : V) :
    S.W u * S.W w = Complex.exp (((-(σ u w)) : ℝ) * Complex.I) • (S.W w * S.W u) := by
  rw [S.mul_eq, S.mul_eq, add_comm w u, smul_smul, relPhase, relPhase, ← Complex.exp_add,
    isAlt_swap hσ u w]
  congr 2
  push_cast
  ring

/-- If `σ(u,w) = 0`, then `W u` and `W w` commute. -/
theorem commute_of_eq_zero (hσ : σ.IsAlt) {u w : V} (h : σ u w = 0) :
    Commute (S.W u) (S.W w) := by
  have := S.mul_comm_phase hσ u w
  rw [h] at this
  simpa [Commute, SemiconjBy] using this

end WeylSystem

/-- The Weyl operators generate `CCR σ` as a C*-algebra, computed inside the subtype. -/
theorem CCR.topologicalClosure_adjoin_weyl (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) :
    (adjoin ℂ (Set.range (fun u => (CCR.weyl σ hσ u : CCR σ)))).topologicalClosure = ⊤ := by
  have himage : (Subtype.val : CCR σ → L2 V →L[ℂ] L2 V) ''
      (adjoin ℂ (Set.range (fun u => (CCR.weyl σ hσ u : CCR σ))) : Set (CCR σ)) =
        (adjoin ℂ (Set.range (Weyl.weyl σ)) : Set (L2 V →L[ℂ] L2 V)) := by
    change (CCR σ).subtype '' _ = _
    rw [← StarSubalgebra.coe_map, StarAlgHom.map_adjoin, ← Set.range_comp]
    rfl
  refine eq_top_iff.2 fun x _ => ?_
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage,
    himage, ← StarSubalgebra.topologicalClosure_coe]
  exact x.2

/-- `CCR σ` with the Weyl operators is a Weyl system. -/
def CCR.weylSystem (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) : WeylSystem σ (CCR σ) where
  W u := (CCR.weyl σ hσ u : CCR σ)
  mem_unitary u := (CCR.weyl σ hσ u).2
  mul_eq u w := by
    apply Subtype.ext
    change Weyl.weyl σ u * Weyl.weyl σ w = relPhase σ u w • Weyl.weyl σ (u + w)
    exact weyl_mul σ hσ u w
  generating := CCR.topologicalClosure_adjoin_weyl σ hσ

@[simp] theorem CCR.weylSystem_W (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (u : V) :
    ((CCR.weylSystem σ hσ).W u : L2 V →L[ℂ] L2 V) = Weyl.weyl σ u := rfl

end Weyl

end BosonicLean
