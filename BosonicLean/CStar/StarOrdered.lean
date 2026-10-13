/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Closed star subalgebras are star-ordered

Let `A` be a C*-algebra whose partial order is star-ordered, and `S` a norm-closed star
subalgebra of `A`. With the order inherited from `A`, an element of `S` is non-negative if and
only if it is `star s * s` for some `s ∈ S`, so `S` is a star-ordered ring. The square root of a
non-negative element is computed by the continuous functional calculus of `A` and stays in `S`
because `S` is closed.

This makes Mathlib's completely positive maps available on BosonicLean's CCR algebra, a closed
star subalgebra of the bounded operators, whose order is then operator positivity.

## Main statements

* `BosonicLean.StarSubalgebra.nonneg_iff_exists_star_mul_self`
* the instance `BosonicLean.StarSubalgebra.starOrderedRing`
-/

namespace BosonicLean

namespace StarSubalgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (S : _root_.StarSubalgebra ℂ A) [IsClosed (S : Set A)]

/-- In a closed star subalgebra, with the inherited order, the non-negative elements are those
of the form `star s * s` with `s` in the subalgebra. (QCALean notes: `prop:ch-starordered`) -/
theorem nonneg_iff_exists_star_mul_self (x : S) : 0 ≤ x ↔ ∃ s : S, x = star s * s := by
  constructor
  · intro hx
    have hx' : (0 : A) ≤ (x : A) := hx
    refine ⟨⟨cfc Real.sqrt (x : A), cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt x.2⟩, ?_⟩
    apply Subtype.ext
    have hsa : IsSelfAdjoint (cfc Real.sqrt (x : A)) := cfc_predicate _ _
    have hsq : CFC.sqrt (x : A) = cfc Real.sqrt (x : A) := by
      rw [CFC.sqrt_eq_real_sqrt (x : A) hx', cfcₙ_eq_cfc]
    change (x : A) = star (cfc Real.sqrt (x : A)) * cfc Real.sqrt (x : A)
    rw [hsa.star_eq, ← hsq, CFC.sqrt_mul_sqrt_self (x : A) hx']
  · rintro ⟨s, rfl⟩
    change (0 : A) ≤ star (s : A) * s
    exact star_mul_self_nonneg _

/-- A closed star subalgebra of a star-ordered C*-algebra is star-ordered.
(QCALean notes: `prop:ch-starordered`) -/
instance starOrderedRing : StarOrderedRing S :=
  StarOrderedRing.of_nonneg_iff'
    (fun {x y} hxy z => by
      change (z : A) + x ≤ (z : A) + y
      exact add_le_add le_rfl (show (x : A) ≤ y from hxy))
    (nonneg_iff_exists_star_mul_self S)

end StarSubalgebra

end BosonicLean
