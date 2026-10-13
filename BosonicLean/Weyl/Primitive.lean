/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.CStar.Primitive
import BosonicLean.Weyl.Simple

/-!
# Primitivity of the CCR algebra

The CCR algebra of a nondegenerate alternating form is simple (`CCR.isSimpleRing`), so it is
primitive as soon as it has an irreducible representation. The
representation on `ℓ²(V)` is reducible, so it cannot serve; a pure state or a Fock representation
would.

## Main results

* `BosonicLean.Weyl.CCR.isPrimitive`.
-/

namespace BosonicLean.Weyl

universe u

/-- The CCR algebra of a nondegenerate form with an irreducible
representation is primitive (Axiom 2 of Dimock 1980). -/
theorem CCR.isPrimitive {V : Type u} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft)
    (h : HasIrreducibleRep (CCR σ)) : IsPrimitive (CCR σ) :=
  haveI := CCR.isSimpleRing hσ hnd
  isPrimitive_of_isSimpleRing h

end BosonicLean.Weyl
