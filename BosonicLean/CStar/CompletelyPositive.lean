/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Identity and composition of completely positive maps

Mathlib defines completely positive maps between C*-algebras (`CompletelyPositiveMap`, notation
`A₁ →CP A₂`) but provides neither the identity nor composition. They are defined here, under
BosonicLean's own names so that they cannot clash with a later Mathlib API; both are candidates
for Mathlib.

## Main definitions

* `BosonicLean.CStar.cpId`: the identity as a completely positive map;
* `BosonicLean.CStar.cpComp`: the composite of two completely positive maps.
-/

open scoped CStarAlgebra

namespace BosonicLean.CStar

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- Completely positive maps with the same values are equal. -/
@[ext]
theorem cpExt {f g : A →CP B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity is completely positive. (QCALean notes: `prop:ch-cpcomp`) -/
noncomputable def cpId : A →CP A where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' k M hM := by
    exact hM

@[simp]
theorem cpId_apply (x : A) : cpId x = x := rfl

/-- The composite of completely positive maps is completely positive.
(QCALean notes: `prop:ch-cpcomp`) -/
noncomputable def cpComp (g : B →CP C) (f : A →CP B) : A →CP C where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have hf : 0 ≤ M.map f.toLinearMap := f.map_cstarMatrix_nonneg' k M hM
    have hg := g.map_cstarMatrix_nonneg' k (M.map f.toLinearMap) hf
    exact hg

@[simp]
theorem cpComp_apply (g : B →CP C) (f : A →CP B) (x : A) : cpComp g f x = g (f x) := rfl

@[simp]
theorem cpComp_cpId (f : A →CP B) : cpComp f cpId = f := rfl

@[simp]
theorem cpId_cpComp (f : A →CP B) : cpComp cpId f = f := rfl

end BosonicLean.CStar
