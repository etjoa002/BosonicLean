/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.System

/-!
# Pullback of a Weyl system along a symplectic map

A surjective symplectic linear map `T : V → V_S` pulls a Weyl system `W_S` for `σ_S` back to the
Weyl system `W_S ∘ T` for `σ`. Unlike the relabelling of `BosonicLean.Weyl.Relabel`, `T` need not
be injective and the algebra is not changed. The corresponding statement for nets,
`LinearAQFT.Symplectic.generators_pullback`, is in LinearAQFT.

## Main definitions

* `BosonicLean.Weyl.WeylSystem.pullback`: the Weyl system `W_S ∘ T`.

## Main statements

* `BosonicLean.Weyl.relPhase_comp`
-/

namespace BosonicLean

namespace Weyl

variable {V VS : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup VS] [Module ℝ VS]
variable {σ : LinearMap.BilinForm ℝ V} {σS : LinearMap.BilinForm ℝ VS}
variable {A : Type*} [CStarAlgebra A]

/-- A symplectic linear map preserves the Weyl phase. -/
theorem relPhase_comp {T : V →ₗ[ℝ] VS} (hT : ∀ u w, σS (T u) (T w) = σ u w) (u w : V) :
    relPhase σS (T u) (T w) = relPhase σ u w := by
  rw [relPhase, relPhase, hT]

namespace WeylSystem

/-- For a symplectic linear map `T`, onto or not, the elements `W_S (T u)` satisfy the Weyl relation
of `σ`. -/
theorem pullback_mul_eq (S : WeylSystem σS A) {T : V →ₗ[ℝ] VS}
    (hT : ∀ u w, σS (T u) (T w) = σ u w) (u w : V) :
    S.W (T u) * S.W (T w) = relPhase σ u w • S.W (T (u + w)) := by
  rw [S.mul_eq, relPhase_comp hT, map_add]

/-- The pullback `W_S ∘ T` of a Weyl system along a surjective symplectic linear map is a Weyl
system. -/
def pullback (S : WeylSystem σS A) (T : V →ₗ[ℝ] VS) (hT : ∀ u w, σS (T u) (T w) = σ u w)
    (hsurj : Function.Surjective T) : WeylSystem σ A where
  W := S.W ∘ T
  mem_unitary u := S.mem_unitary (T u)
  mul_eq u w := S.pullback_mul_eq hT u w
  generating := by
    rw [hsurj.range_comp]
    exact S.generating

@[simp] theorem pullback_W (S : WeylSystem σS A) (T : V →ₗ[ℝ] VS)
    (hT : ∀ u w, σS (T u) (T w) = σ u w) (hsurj : Function.Surjective T) (u : V) :
    (S.pullback T hT hsurj).W u = S.W (T u) := rfl

end WeylSystem

end Weyl

end BosonicLean
