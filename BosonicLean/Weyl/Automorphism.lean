/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.Simple
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Automorphisms that move Weyl operators to Weyl operators

The vector functional `a ↦ (a δ₀)(0)` on the bounded operators of `ℓ²(V)` takes the value `1` on
`W(0)` and `0` on every other Weyl operator. Hence distinct Weyl operators are linearly independent,
and `W(u)` has distance at least one from the closed span of the other Weyl operators (separation).

If a star-automorphism `T` of the CCR algebra maps each `W(u)` to a multiple `c(u) W(Γ u)`, then
`Γ` is a symplectic `ℝ`-linear bijection and `c` a unitary character. This is the statement
behind thesis (4.7), with the character the thesis omits.

## Main results

* `BosonicLean.Weyl.testFun_weyl`, `BosonicLean.Weyl.weyl_eq_of_smul_eq`
* `BosonicLean.Weyl.weyl_separation`
* `BosonicLean.Weyl.weyl_automorphism_of_nondegenerate`,
  `BosonicLean.Weyl.weyl_automorphism_of_separatingLeft`

Relation to `Right.lean` and `Simple.lean`: `vac` is `delta 0` with the classical decidability
instance (`vac_eq_delta`), so that the statements here need no `DecidableEq V`; `evalVac` is the
vector state `vectorState` extended to all bounded operators (`vectorState_eq_evalVac`); the density
argument is `WeylSystem.adjoin_le_span`. The duplicates `weylSpanStar` and `ccrSubtypeL` are
deprecated.
-/

open Matrix
open scoped ComplexConjugate CStarAlgebra

namespace BosonicLean.Weyl

section Separation

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : LinearMap.BilinForm ℝ V)

open scoped Classical in
/-- The unit vector at the origin of `ℓ²(V)`: `delta 0` with the classical decidability
instance. -/
noncomputable def vac : L2 V := lp.single 2 0 1

omit [Module ℝ V] in
theorem vac_eq_delta [DecidableEq V] : (vac : L2 V) = delta 0 := by
  unfold vac delta
  congr
  exact Subsingleton.elim _ _

omit [Module ℝ V] in
theorem norm_vac : ‖(vac : L2 V)‖ = 1 := by
  classical
  rw [vac, lp.norm_single (by norm_num), norm_one]

theorem norm_weyl_le (u : V) : ‖weyl σ u‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (V) in
/-- The vector functional `a ↦ (a δ₀)(0)`. -/
noncomputable def evalVac : (L2 V →L[ℂ] L2 V) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => (a vac : V → ℂ) 0
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl } 1 fun a => by
    calc ‖(a vac : V → ℂ) 0‖ ≤ ‖a vac‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖a‖ * ‖(vac : L2 V)‖ := a.le_opNorm _
      _ = 1 * ‖a‖ := by rw [norm_vac, mul_one, one_mul]

omit [Module ℝ V] in
theorem evalVac_apply (a : L2 V →L[ℂ] L2 V) : evalVac V a = (a vac : V → ℂ) 0 := rfl

omit [Module ℝ V] in
theorem norm_evalVac_le : ‖evalVac V‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem evalVac_weyl [DecidableEq V] (u : V) : evalVac V (weyl σ u) = if u = 0 then 1 else 0 := by
  rw [evalVac_apply, weyl_apply, zero_add]
  have hphase : phase σ u 0 = 1 := by simp [phase]
  rw [hphase, one_mul]
  by_cases h : u = 0
  · subst h; simp [vac, lp.single_apply]
  · simp [h, vac, lp.single_apply]

/-- On the CCR algebra, `evalVac` is the vector state `τ` of `Right.lean`. -/
theorem vectorState_eq_evalVac [DecidableEq V] (a : CCR σ) :
    vectorState σ a = evalVac V (a : L2 V →L[ℂ] L2 V) := by
  rw [vectorState_apply, evalVac_apply, vac_eq_delta, delta, lp.inner_single_left]
  simp

/-- The functional `a ↦ ((W(-b) a) δ₀)(0)`, which detects `W(b)`. -/
noncomputable def testFun (b : V) : (L2 V →L[ℂ] L2 V) →L[ℂ] ℂ :=
  (evalVac V).comp (ContinuousLinearMap.mul ℂ _ (weyl σ (-b)))

theorem norm_testFun_le (b : V) : ‖testFun σ b‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖evalVac V‖ * ‖ContinuousLinearMap.mul ℂ (L2 V →L[ℂ] L2 V) (weyl σ (-b))‖
      ≤ 1 * 1 := by
        gcongr
        · exact norm_evalVac_le
        · exact (ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans (norm_weyl_le σ _)
    _ = 1 := one_mul 1

variable {σ}

theorem testFun_weyl [DecidableEq V] (hσ : σ.IsAlt) (b a : V) :
    testFun σ b (weyl σ a) = if a = b then 1 else 0 := by
  rw [testFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    weyl_mul σ hσ, map_smul, evalVac_weyl, neg_add_eq_sub]
  by_cases h : a = b
  · subst h
    simp [hσ a]
  · simp [h, sub_eq_zero]

theorem weyl_ne_zero (hσ : σ.IsAlt) (a : V) : weyl σ a ≠ 0 := by
  classical
  intro h
  have := testFun_weyl hσ a a
  rw [h, map_zero] at this
  simp at this

/-- Linear independence of Weyl operators, in the form used below: `α W(a) = β W(b)` with
`β ≠ 0` forces `a = b` and `α = β`. (QCALean notes: `lem:separation`) -/
theorem weyl_eq_of_smul_eq (hσ : σ.IsAlt) {a b : V} {α β : ℂ} (hβ : β ≠ 0)
    (h : α • weyl σ a = β • weyl σ b) : a = b ∧ α = β := by
  classical
  have h1 := congrArg (testFun σ b) h
  rw [map_smul, map_smul, testFun_weyl hσ, testFun_weyl hσ] at h1
  by_cases hab : a = b
  · subst hab; simpa using h1
  · simp [hab] at h1; exact absurd h1.symm hβ

/-- Separation: `W(u)` has distance at least one from the closed span of the other Weyl operators.
(QCALean notes: `lem:separation`) -/
theorem weyl_separation (hσ : σ.IsAlt) (u : V) {x : L2 V →L[ℂ] L2 V}
    (hx : x ∈ (Submodule.span ℂ (weyl σ '' {v | v ≠ u})).topologicalClosure) :
    1 ≤ ‖weyl σ u - x‖ := by
  classical
  have hker : (Submodule.span ℂ (weyl σ '' {v | v ≠ u})).topologicalClosure ≤
      LinearMap.ker (testFun σ u : (L2 V →L[ℂ] L2 V) →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (testFun σ u).isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ≠ u := hv
    simp [testFun_weyl hσ, hv']
  have h0 : testFun σ u x = 0 := hker hx
  have h1 : testFun σ u (weyl σ u - x) = 1 := by
    rw [map_sub, h0, testFun_weyl hσ]; simp
  calc (1 : ℝ) = ‖testFun σ u (weyl σ u - x)‖ := by rw [h1, norm_one]
    _ ≤ ‖testFun σ u‖ * ‖weyl σ u - x‖ := (testFun σ u).le_opNorm _
    _ ≤ 1 * ‖weyl σ u - x‖ := by gcongr; exact norm_testFun_le σ u
    _ = ‖weyl σ u - x‖ := one_mul _

end Separation

section Density

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : LinearMap.BilinForm ℝ V}
  {A : Type*} [CStarAlgebra A]

/-- The linear span of the Weyl operators of a Weyl system is a star-subalgebra. Deprecated: see
`WeylSystem.adjoin_le_span`. -/
@[deprecated WeylSystem.adjoin_le_span (since := "2026-09-30")]
noncomputable def weylSpanStar (S : WeylSystem σ A) (hσ : σ.IsAlt) : StarSubalgebra ℂ A :=
  { (Submodule.span ℂ (Set.range S.W)).toSubalgebra
      (by rw [← S.map_zero]; exact Submodule.subset_span ⟨0, rfl⟩)
      (fun x y hx hy => by
        have := Submodule.mul_mem_mul hx hy
        rw [Submodule.span_mul_span] at this
        refine (Submodule.span_le.2 ?_) this
        rintro _ ⟨_, ⟨u, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
        change S.W u * S.W w ∈ _
        rw [S.mul_eq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u + w, rfl⟩)) with
    star_mem' := fun {x} hx => by
      change x ∈ Submodule.span ℂ (Set.range S.W) at hx
      change star x ∈ Submodule.span ℂ (Set.range S.W)
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, rfl⟩ := hx
        rw [S.star_eq hσ]
        exact Submodule.subset_span ⟨-u, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

/-- Every element of the C*-algebra of a Weyl system is a limit of finite linear combinations of
Weyl operators. -/
theorem weyl_mem_closure_span (S : WeylSystem σ A) (hσ : σ.IsAlt) (y : A) :
    y ∈ closure (Submodule.span ℂ (Set.range S.W) : Set A) := by
  have hy : y ∈ ((StarAlgebra.adjoin ℂ (Set.range S.W)).topologicalClosure : Set A) := by
    rw [S.generating]; trivial
  rw [StarSubalgebra.topologicalClosure_coe] at hy
  exact closure_mono (S.adjoin_le_span hσ) hy

end Density

section Main

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : LinearMap.BilinForm ℝ V}

/-- The inclusion of the CCR algebra into the bounded operators, as a continuous linear map.
Deprecated: use `(CCR σ).toSubalgebra.toSubmodule.subtypeL`. -/
@[deprecated "use `(CCR σ).toSubalgebra.toSubmodule.subtypeL`" (since := "2026-09-30")]
noncomputable def ccrSubtypeL (σ : LinearMap.BilinForm ℝ V) : CCR σ →L[ℂ] (L2 V →L[ℂ] L2 V) :=
  ⟨(CCR σ).toSubalgebra.toSubmodule.subtype, continuous_subtype_val⟩

theorem relPhase_ne_zero (u w : V) : relPhase σ u w ≠ 0 := Complex.exp_ne_zero _

/-- The coefficients `c(u)` of `T W(u) = c(u) W(Γ u)` do not vanish. -/
theorem weyl_automorphism_coeff_ne_zero (hσ : σ.IsAlt) (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V)
    (c : V → ℂ)
    (h : ∀ u, (T ⟨weyl σ u, weyl_mem_CCR σ u⟩ : L2 V →L[ℂ] L2 V) = c u • weyl σ (Γ u))
    (u : V) : c u ≠ 0 := by
  intro hu
  have h1 := h u
  rw [hu, zero_smul] at h1
  have h2 : T ⟨weyl σ u, weyl_mem_CCR σ u⟩ = 0 := Subtype.ext h1
  rw [map_eq_zero_iff T T.injective] at h2
  exact weyl_ne_zero hσ u (congrArg Subtype.val h2)

/-- Step 1 of the proof of `weyl_automorphism_of_nondegenerate`: comparing `T(W(u) W(w))` with
`T W(u) · T W(w)` gives additivity of `Γ` together with the coefficient identity
`c(u) c(w) e^{iσ(Γu,Γw)/2} = e^{iσ(u,w)/2} c(u+w)`. -/
theorem weyl_automorphism_add (hσ : σ.IsAlt) (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V) (c : V → ℂ)
    (h : ∀ u, (T ⟨weyl σ u, weyl_mem_CCR σ u⟩ : L2 V →L[ℂ] L2 V) = c u • weyl σ (Γ u))
    (u w : V) : Γ (u + w) = Γ u + Γ w ∧
      c u * c w * relPhase σ (Γ u) (Γ w) = relPhase σ u w * c (u + w) := by
  set S := CCR.weylSystem σ hσ with hS
  have hW : ∀ u, (S.W u : L2 V →L[ℂ] L2 V) = weyl σ u := fun u => rfl
  have hT : ∀ u, T (S.W u) = c u • S.W (Γ u) := fun u => Subtype.ext (h u)
  have hc0 := weyl_automorphism_coeff_ne_zero hσ T Γ c h
  have e := congrArg (fun x : CCR σ => (x : L2 V →L[ℂ] L2 V)) (map_mul T (S.W u) (S.W w))
  simp only [S.mul_eq, map_smul, hT, smul_mul_smul_comm, smul_smul] at e
  have e' : (relPhase σ u w * c (u + w)) • weyl σ (Γ (u + w)) =
      (c u * c w * relPhase σ (Γ u) (Γ w)) • weyl σ (Γ u + Γ w) := by
    simpa [hW] using e
  obtain ⟨h1, h2⟩ := weyl_eq_of_smul_eq hσ
    (mul_ne_zero (mul_ne_zero (hc0 u) (hc0 w)) (relPhase_ne_zero _ _)) e'
  exact ⟨h1, h2.symm⟩

/-- Step 2 of the proof of `weyl_automorphism_of_nondegenerate`: the coefficient identity of step 1,
used for `(u, w)` and `(w, u)`, forces `σ(u, w) - σ(Γ u, Γ w) ∈ 2πℤ`. -/
theorem exists_int_of_relPhase (hσ : σ.IsAlt) {Γ : V → V} {c : V → ℂ} (hc0 : ∀ u, c u ≠ 0)
    (hph : ∀ u w, c u * c w * relPhase σ (Γ u) (Γ w) = relPhase σ u w * c (u + w))
    (u w : V) : ∃ k : ℤ, σ u w - σ (Γ u) (Γ w) = 2 * Real.pi * k := by
  have h1 := hph u w
  have h2 := hph w u
  rw [add_comm w u] at h2
  have hne : c u * c w ≠ 0 := mul_ne_zero (hc0 u) (hc0 w)
  have h3 : relPhase σ (Γ u) (Γ w) * relPhase σ w u =
      relPhase σ (Γ w) (Γ u) * relPhase σ u w := by
    apply mul_left_cancel₀ hne
    calc c u * c w * (relPhase σ (Γ u) (Γ w) * relPhase σ w u)
        = relPhase σ u w * c (u + w) * relPhase σ w u := by rw [← h1]; ring
      _ = c w * c u * relPhase σ (Γ w) (Γ u) * relPhase σ u w := by rw [h2]; ring
      _ = _ := by ring
  set d : ℝ := σ u w - σ (Γ u) (Γ w) with hd
  have hne2 : relPhase σ (Γ w) (Γ u) * relPhase σ u w ≠ 0 :=
    mul_ne_zero (relPhase_ne_zero _ _) (relPhase_ne_zero _ _)
  have hexp : Complex.exp ((d : ℂ) * Complex.I) = 1 := by
    have : Complex.exp ((d : ℂ) * Complex.I) = relPhase σ (Γ u) (Γ w) * relPhase σ w u /
        (relPhase σ (Γ w) (Γ u) * relPhase σ u w) := by
      simp only [relPhase, ← Complex.exp_add, ← Complex.exp_sub]
      congr 1
      have hs1 := isAlt_swap hσ u w
      have hs2 := isAlt_swap hσ (Γ u) (Γ w)
      rw [hd]
      push_cast
      rw [hs1, hs2]
      push_cast
      ring
    rw [this, h3, div_self hne2]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨k, ?_⟩
  have hk' : ((d : ℂ)) = ((2 * Real.pi * k : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hk]; push_cast; ring
  exact_mod_cast hk'

/-- Step 2b of the proof of `weyl_automorphism_of_nondegenerate` (divisibility): an additive `Γ`
with `σ(u, w) - σ(Γ u, Γ w) ∈ 2πℤ` for all `u, w` preserves `σ`. Apply the hypothesis to `u / m`
with `m > |k|`. -/
theorem symplectic_of_exists_int {Γ : V → V} (hadd : ∀ u w, Γ (u + w) = Γ u + Γ w)
    (h2 : ∀ u w, ∃ k : ℤ, σ u w - σ (Γ u) (Γ w) = 2 * Real.pi * k) (u w : V) :
    σ (Γ u) (Γ w) = σ u w := by
  let ΓA : V →+ V := AddMonoidHom.mk' Γ hadd
  have hnsmul : ∀ (m : ℕ) (x : V), Γ ((m : ℝ) • x) = (m : ℝ) • Γ x := by
    intro m x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact map_nsmul ΓA m x
  obtain ⟨k, hk⟩ := h2 u w
  set m : ℕ := k.natAbs + 1 with hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  obtain ⟨j, hj⟩ := h2 ((m : ℝ)⁻¹ • u) w
  have hu : (m : ℝ) • ((m : ℝ)⁻¹ • u) = u := by rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]
  have hD : σ u w - σ (Γ u) (Γ w) =
      (m : ℝ) * (σ ((m : ℝ)⁻¹ • u) w - σ (Γ ((m : ℝ)⁻¹ • u)) (Γ w)) := by
    conv_lhs => rw [← hu, hnsmul]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hk, hj] at hD
  have hkj : (k : ℝ) = (m : ℝ) * j := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2pi
    linear_combination hD
  have hkj' : k = (m : ℤ) * j := by exact_mod_cast hkj
  have hj0 : j = 0 := by
    by_contra hj0
    have : k.natAbs = m * j.natAbs := by rw [hkj', Int.natAbs_mul]; simp
    have : m ≤ k.natAbs := by
      rw [this]; exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 hj0)
    omega
  rw [hj0, mul_zero] at hkj'
  rw [hkj'] at hk
  simp only [Int.cast_zero, mul_zero, sub_eq_zero] at hk
  exact hk.symm

/-- Step 3 of the proof of `weyl_automorphism_of_nondegenerate`: `Γ` is surjective. A Weyl operator
`W(v')` outside the image of `Γ` would lie in the closed span of the other Weyl operators,
contradicting separation. -/
theorem weyl_automorphism_surjective (hσ : σ.IsAlt) (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V)
    (c : V → ℂ)
    (h : ∀ u, (T ⟨weyl σ u, weyl_mem_CCR σ u⟩ : L2 V →L[ℂ] L2 V) = c u • weyl σ (Γ u)) :
    Function.Surjective Γ := by
  classical
  set S := CCR.weylSystem σ hσ with hS
  have hT : ∀ u, T (S.W u) = c u • S.W (Γ u) := fun u => Subtype.ext (h u)
  intro v'
  by_contra hv
  push Not at hv
  let P := Submodule.span ℂ (S.W '' {v | v ≠ v'})
  have hmap : ∀ y ∈ Submodule.span ℂ (Set.range S.W), T y ∈ P := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hT]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Γ u, hv u, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact P.smul_mem a hx
  have hy := weyl_mem_closure_span S hσ (T.symm (S.W v'))
  have hTy : T (T.symm (S.W v')) ∈ closure (P : Set (CCR σ)) :=
    image_closure_subset_closure_image (map_continuous T)
      ⟨_, hy, rfl⟩ |> closure_mono (by rintro _ ⟨y, hy, rfl⟩; exact hmap y hy)
  rw [StarAlgEquiv.apply_symm_apply] at hTy
  let ψ := (testFun σ v').comp (CCR σ).toSubalgebra.toSubmodule.subtypeL
  have hψ : ∀ z ∈ closure (P : Set (CCR σ)), ψ z = 0 := by
    have hle : P ≤ LinearMap.ker (ψ : CCR σ →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨v, hv', rfl⟩
      have hv'' : v ≠ v' := hv'
      change testFun σ v' (weyl σ v) = 0
      rw [testFun_weyl hσ]; simp [hv'']
    intro z hz
    exact (closure_minimal hle ψ.isClosed_ker) hz
  have h1 := hψ _ hTy
  change testFun σ v' (weyl σ v') = 0 at h1
  rw [testFun_weyl hσ] at h1
  simp at h1

/-- Step 4 of the proof of `weyl_automorphism_of_nondegenerate`: for nondegenerate `σ`, an additive
surjection preserving `σ` is `ℝ`-linear and injective, hence a linear equivalence. -/
theorem exists_linearEquiv_of_symplectic (hnd : σ.Nondegenerate) {Γ : V → V}
    (hadd : ∀ u w, Γ (u + w) = Γ u + Γ w) (hsymp : ∀ u w, σ (Γ u) (Γ w) = σ u w)
    (hsurj : Function.Surjective Γ) : ∃ L : V ≃ₗ[ℝ] V, ⇑L = Γ := by
  let ΓA : V →+ V := AddMonoidHom.mk' Γ hadd
  have hsub : ∀ a b, Γ (a - b) = Γ a - Γ b := fun a b => map_sub ΓA a b
  have hsmul : ∀ (t : ℝ) (u : V), Γ (t • u) = t • Γ u := by
    intro t u
    have := hnd.1 (Γ (t • u) - t • Γ u) fun z => by
      obtain ⟨w, rfl⟩ := hsurj z
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hsymp, sub_self]
    exact sub_eq_zero.1 this
  have hinj : Function.Injective Γ := by
    intro a b hab
    have := hnd.1 (a - b) fun w => by
      rw [← hsymp, hsub, hab, sub_self, map_zero, LinearMap.zero_apply]
    exact sub_eq_zero.1 this
  let Lin : V →ₗ[ℝ] V := { toFun := Γ, map_add' := hadd, map_smul' := hsmul }
  exact ⟨LinearEquiv.ofBijective Lin ⟨hinj, hsurj⟩, rfl⟩

/-- For an alternating nondegenerate form: a star-automorphism of the CCR algebra that maps each
Weyl operator to a multiple of a Weyl operator, `T W(u) = c(u) W(Γ u)`, comes from a symplectic
`ℝ`-linear bijection `Γ`, and `c` is a unitary character. (QCALean notes: `thm:weyl-type`) -/
theorem weyl_automorphism_of_nondegenerate (hσ : σ.IsAlt)
    (hnd : σ.Nondegenerate) (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V) (c : V → ℂ)
    (h : ∀ u, (T ⟨weyl σ u, weyl_mem_CCR σ u⟩ : L2 V →L[ℂ] L2 V) = c u • weyl σ (Γ u)) :
    (∃ L : V ≃ₗ[ℝ] V, ⇑L = Γ) ∧ (∀ u w, σ (Γ u) (Γ w) = σ u w) ∧
      (∀ u w, c (u + w) = c u * c w) ∧ (∀ u, ‖c u‖ = 1) := by
  set S := CCR.weylSystem σ hσ with hS
  have hT : ∀ u, T (S.W u) = c u • S.W (Γ u) := fun u => Subtype.ext (h u)
  have step1 := weyl_automorphism_add hσ T Γ c h
  have hadd : ∀ u w, Γ (u + w) = Γ u + Γ w := fun u w => (step1 u w).1
  have hsymp : ∀ u w, σ (Γ u) (Γ w) = σ u w := symplectic_of_exists_int hadd
    (exists_int_of_relPhase hσ (weyl_automorphism_coeff_ne_zero hσ T Γ c h)
      fun u w => (step1 u w).2)
  refine ⟨exists_linearEquiv_of_symplectic hnd hadd hsymp
    (weyl_automorphism_surjective hσ T Γ c h), hsymp, ?_, ?_⟩
  -- Step 5: the character
  · intro u w
    have h2 := (step1 u w).2
    have hE : relPhase σ (Γ u) (Γ w) = relPhase σ u w := by simp [relPhase, hsymp]
    rw [hE] at h2
    apply mul_left_cancel₀ (relPhase_ne_zero (σ := σ) u w)
    linear_combination -1 * h2
  · intro u
    have hone : (1 : CCR σ) ≠ 0 := by
      intro h1
      have := congrArg (fun x : CCR σ => (x : L2 V →L[ℂ] L2 V)) h1
      simp only [OneMemClass.coe_one, ZeroMemClass.coe_zero] at this
      exact weyl_ne_zero hσ 0 (by rw [weyl_zero]; exact this)
    have : Nontrivial (CCR σ) := nontrivial_of_ne 1 0 hone
    have h1 : ‖T (S.W u)‖ = ‖S.W u‖ := StarAlgEquiv.norm_map T _
    rw [hT, norm_smul, CStarRing.norm_of_mem_unitary (S.mem_unitary _),
      CStarRing.norm_of_mem_unitary (S.mem_unitary _), mul_one] at h1
    exact h1

/-- `weyl_automorphism_of_nondegenerate` with nondegeneracy in the form `σ.SeparatingLeft` used
elsewhere in this library (for an alternating form it implies `σ.Nondegenerate`). -/
theorem weyl_automorphism_of_separatingLeft (hσ : σ.IsAlt)
    (hnd : σ.SeparatingLeft) (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V) (c : V → ℂ)
    (h : ∀ u, (T ⟨weyl σ u, weyl_mem_CCR σ u⟩ : L2 V →L[ℂ] L2 V) = c u • weyl σ (Γ u)) :
    (∃ L : V ≃ₗ[ℝ] V, ⇑L = Γ) ∧ (∀ u w, σ (Γ u) (Γ w) = σ u w) ∧
      (∀ u w, c (u + w) = c u * c w) ∧ (∀ u, ‖c u‖ = 1) :=
  weyl_automorphism_of_nondegenerate hσ
    ⟨hnd, fun y hy => hnd y fun x => by rw [isAlt_swap hσ x y, hy x, neg_zero]⟩ T Γ c h

end Main

end BosonicLean.Weyl
