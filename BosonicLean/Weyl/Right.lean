/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.System
import BosonicLean.CStar.Commute
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Right Weyl operators and the vector state

The right Weyl operator `(R(w)ψ)(v) = e^{-iσ(w,v)/2} ψ(v+w)` is the Weyl operator of `-σ`. It
commutes with every element of `CCR σ`. The vector state `τ(a) = ⟪δ₀, a δ₀⟫` takes the value
`[v = 0]` on `W(v)`. Both enter the proof that the CCR algebra is simple (`Simple.lean`).

## Main definitions

* `BosonicLean.Weyl.rightWeyl σ w`: the right Weyl operator `R(w)`.
* `BosonicLean.Weyl.vectorState σ`: the vector state `τ` on `CCR σ`.

## Main statements

* `star_rightWeyl`, `rightWeyl_mem_unitary`, `rightWeyl_mul`,
  `commute_weyl_rightWeyl`, `commute_rightWeyl_of_mem_CCR`, `rightWeyl_delta_zero`,
  `weyl_delta_zero`: properties of `R(w)`, and the action of `W(u)` and `R(w)` on `δ₀`.
* `vectorState_one`, `vectorState_star_mul_self`, `norm_vectorState_apply_le`,
  `vectorState_weyl`: properties of `τ`.
-/

noncomputable section

namespace BosonicLean

namespace Weyl

open StarAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The right Weyl operator
`(R(w)ψ)(v) = e^{-iσ(w,v)/2} ψ(v+w)`, the Weyl operator of `-σ`. -/
def rightWeyl (σ : LinearMap.BilinForm ℝ V) (w : V) : L2 V →L[ℂ] L2 V := weyl (-σ) w

theorem rightWeyl_apply (σ : LinearMap.BilinForm ℝ V) (w : V) (f : L2 V) (v : V) :
    rightWeyl σ w f v = Complex.exp (((-(σ w v) / 2 : ℝ) : ℂ) * Complex.I) * f (v + w) := by
  simp [rightWeyl, weyl_apply, phase, neg_div]

theorem isAlt_neg {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) : (-σ).IsAlt :=
  LinearMap.BilinForm.isAlt_neg.2 hσ

/-- `R(w)* = R(-w)`. -/
theorem star_rightWeyl (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (w : V) :
    star (rightWeyl σ w) = rightWeyl σ (-w) :=
  star_weyl (-σ) (isAlt_neg hσ) w

/-- Each `R(w)` is unitary. -/
theorem rightWeyl_mem_unitary (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (w : V) :
    rightWeyl σ w ∈ unitary (L2 V →L[ℂ] L2 V) :=
  weyl_mem_unitary (-σ) (isAlt_neg hσ) w

/-- `R(w) R(w') = e^{iσ(w,w')/2} R(w+w')`. -/
theorem rightWeyl_mul (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (w w' : V) :
    rightWeyl σ w * rightWeyl σ w' =
      Complex.exp (((σ w w') / 2 : ℝ) * Complex.I) • rightWeyl σ (w + w') := by
  rw [rightWeyl, rightWeyl, weyl_mul (-σ) (isAlt_neg hσ), rightWeyl]
  simp

/-- `R(w)` commutes with `W(u)`. -/
theorem commute_weyl_rightWeyl (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (u w : V) :
    Commute (weyl σ u) (rightWeyl σ w) := by
  have hwu : σ w u = -σ u w := isAlt_swap hσ u w
  ext f v
  change phase σ u v * (phase (-σ) w (v + u) * f (v + u + w)) =
    phase (-σ) w v * (phase σ u (v + w) * f (v + w + u))
  rw [add_right_comm v w u, ← mul_assoc, ← mul_assoc]
  congr 1
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp only [map_add, LinearMap.neg_apply, hwu]
  push_cast
  ring

/-- `R(w)` commutes with every element of `CCR σ`. -/
theorem commute_rightWeyl_of_mem_CCR (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (w : V)
    {a : L2 V →L[ℂ] L2 V} (ha : a ∈ CCR σ) : Commute a (rightWeyl σ w) := by
  refine commute_of_mem_topologicalClosure_adjoin (s := Set.range (weyl σ))
    (t := {rightWeyl σ w}) ?_ ?_ ha
    (StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ rfl))
  · rintro _ ⟨u, rfl⟩ b rfl
    exact commute_weyl_rightWeyl σ hσ u w
  · rintro _ ⟨u, rfl⟩ b rfl
    rw [star_rightWeyl σ hσ]
    exact commute_weyl_rightWeyl σ hσ u (-w)

variable [DecidableEq V]

/-- The basis vector `δ_v` of `ℓ²(V)`: Mathlib's `lp.single 2 v 1`, named for readability. -/
def delta (v : V) : L2 V := lp.single 2 v (1 : ℂ)

omit [AddCommGroup V] [Module ℝ V] in
theorem delta_apply (v v' : V) : delta v v' = if v' = v then 1 else 0 := by
  simp [delta, lp.single_apply, Pi.single_apply]

/-- `W(u) δ₀ = δ_{-u}`. -/
theorem weyl_delta_zero (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (u : V) :
    weyl σ u (delta 0) = delta (-u) := by
  ext v
  rw [weyl_apply, delta_apply, delta_apply]
  by_cases hv : v = -u
  · subst hv
    simp [phase, hσ u]
  · have : v + u ≠ 0 := fun h => hv (eq_neg_of_add_eq_zero_left h)
    simp [hv, this]

/-- `R(w) δ₀ = δ_{-w}`. -/
theorem rightWeyl_delta_zero (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (w : V) :
    rightWeyl σ w (delta 0) = delta (-w) :=
  weyl_delta_zero (-σ) (isAlt_neg hσ) w

/-- The vector state `τ(a) = ⟪δ₀, a δ₀⟫` on `CCR σ`. -/
def vectorState (σ : LinearMap.BilinForm ℝ V) : CCR σ →L[ℂ] ℂ :=
  (innerSL ℂ (delta (0 : V))).comp
    ((ContinuousLinearMap.apply ℂ (L2 V) (delta (0 : V))).comp
      (CCR σ).toSubalgebra.toSubmodule.subtypeL)

theorem vectorState_apply (σ : LinearMap.BilinForm ℝ V) (a : CCR σ) :
    vectorState σ a = inner ℂ (delta (0 : V)) ((a : L2 V →L[ℂ] L2 V) (delta 0)) := rfl

omit [AddCommGroup V] [Module ℝ V] in
theorem norm_delta (v : V) : ‖delta v‖ = 1 := by
  simp [delta, lp.norm_single]

/-- `τ(1) = 1`. -/
theorem vectorState_one (σ : LinearMap.BilinForm ℝ V) : vectorState σ 1 = 1 := by
  rw [vectorState_apply]
  simp [inner_self_eq_norm_sq_to_K, norm_delta]

/-- `τ(a* a) = ‖a δ₀‖²`. -/
theorem vectorState_star_mul_self (σ : LinearMap.BilinForm ℝ V) (a : CCR σ) :
    vectorState σ (star a * a) = (‖(a : L2 V →L[ℂ] L2 V) (delta 0)‖ ^ 2 : ℝ) := by
  rw [vectorState_apply]
  change inner ℂ (delta 0) ((star (a : L2 V →L[ℂ] L2 V) * a) (delta 0)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- `|τ(a)| ≤ ‖a‖`. -/
theorem norm_vectorState_apply_le (σ : LinearMap.BilinForm ℝ V) (a : CCR σ) :
    ‖vectorState σ a‖ ≤ ‖a‖ := by
  rw [vectorState_apply]
  calc ‖inner ℂ (delta (0 : V)) ((a : L2 V →L[ℂ] L2 V) (delta 0))‖
      ≤ ‖delta (0 : V)‖ * ‖(a : L2 V →L[ℂ] L2 V) (delta 0)‖ := norm_inner_le_norm _ _
    _ ≤ ‖delta (0 : V)‖ * (‖(a : L2 V →L[ℂ] L2 V)‖ * ‖delta (0 : V)‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖a‖ := by rw [norm_delta]; simp

/-- `τ(W(v)) = [v = 0]`. -/
theorem vectorState_weyl (σ : LinearMap.BilinForm ℝ V) (hσ : σ.IsAlt) (v : V) :
    vectorState σ ⟨weyl σ v, weyl_mem_CCR σ v⟩ = if v = 0 then 1 else 0 := by
  rw [vectorState_apply]
  change inner ℂ (delta (0 : V)) (weyl σ v (delta 0)) = _
  rw [weyl_delta_zero σ hσ, delta, lp.inner_single_left, delta_apply]
  by_cases hv : v = 0 <;> simp [hv, eq_comm]

end Weyl

end BosonicLean
