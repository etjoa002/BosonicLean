/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Irreducible representations and primitive C*-algebras

A representation is irreducible if its commutant is trivial; a C*-algebra is primitive if it has
a faithful irreducible representation on a nonzero Hilbert space. Every representation of a
simple C*-algebra is injective, so a simple C*-algebra with an irreducible representation is
primitive.

## Main definitions and results

* `BosonicLean.IsIrreducibleRep`, `BosonicLean.IsPrimitive`, `BosonicLean.HasIrreducibleRep`.
* `BosonicLean.injective_of_isSimpleRing`, `BosonicLean.isPrimitive_of_isSimpleRing`.
-/

namespace BosonicLean

universe u

/-- A representation `π` of `A` on a Hilbert space is irreducible if its commutant consists of
scalars. -/
def IsIrreducibleRep {A : Type*} [CStarAlgebra A] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1

/-- `A` is primitive: it has a faithful irreducible representation on a nonzero Hilbert space
(Axiom 2 of Dimock 1980 for the algebras of a net). The Hilbert space is taken in the universe of
`A`; this is no restriction. -/
def IsPrimitive (A : Type u) [CStarAlgebra A] : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Nontrivial H ∧ Function.Injective π ∧ IsIrreducibleRep π

/-- `A` has an irreducible representation on a nonzero Hilbert
space in its own universe. -/
def HasIrreducibleRep (A : Type u) [CStarAlgebra A] : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Nontrivial H ∧ IsIrreducibleRep π

/-- Every representation of a simple C*-algebra on a nonzero
Hilbert space is injective. -/
theorem injective_of_isSimpleRing {A : Type*} [CStarAlgebra A] [IsSimpleRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Function.Injective π :=
  (π.toAlgHom : A →+* (H →L[ℂ] H)).injective

/-- A simple C*-algebra with an irreducible representation is primitive; the abstract form of
`BosonicLean.Weyl.CCR.isPrimitive`. -/
theorem isPrimitive_of_isSimpleRing {A : Type u} [CStarAlgebra A] [IsSimpleRing A]
    (h : HasIrreducibleRep A) : IsPrimitive A := by
  obtain ⟨H, _, _, _, π, hH, hπ⟩ := h
  exact ⟨H, _, _, _, π, hH, injective_of_isSimpleRing π, hπ⟩

end BosonicLean
