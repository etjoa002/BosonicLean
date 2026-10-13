/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.System

/-!
# Relabelling by symplectic isomorphisms

A linear bijection `T : V ≃ₗ[ℝ] V'` with `σ' (T u) (T v) = σ u v` acts on `ℓ²` by
`(U_T ψ)(v') = ψ(T⁻¹ v')`. Conjugation by `U_T` sends `W(u)` to `W'(T u)` and restricts to a
star-algebra isomorphism `CCR σ ≃⋆ₐ[ℂ] CCR σ'`, strictly functorial in `T`.

## Main definitions

* `BosonicLean.Weyl.relabel T`: the unitary `U_T`, a linear isometry equivalence.
* `BosonicLean.Weyl.CCR.relabel hT`: the star-algebra isomorphism `α_T`, `a ↦ U_T a U_T*`.

## Main statements

* `relabel_refl`, `relabel_trans`, `relabel_symm`, `adjoint_relabel`: functoriality and the
  adjoint `U_T* = U_{T⁻¹}`.
* `conj_relabel_weyl`: `U_T W(u) U_T* = W'(T u)`.
* `CCR.relabel_weyl`, `CCR.relabel_refl`, `CCR.relabel_trans`: `α_T (W u) = W' (T u)`, and
  functoriality of `α_T`.
-/

open scoped ENNReal

noncomputable section

namespace BosonicLean

namespace Weyl

open StarAlgebra

universe u₁ u₂ u₃

variable {V : Type u₁} {V' : Type u₂} {V'' : Type u₃}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V'] [AddCommGroup V'']
  [Module ℝ V'']

/-- `ℓ²` is invariant under reindexing by a bijection. -/
theorem memℓp_comp_equiv {X Y : Type*} (e : Y ≃ X) {f : X → ℂ} (hf : Memℓp f 2) :
    Memℓp (f ∘ e) 2 := by
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  exact (e.summable_iff (f := fun v => ‖f v‖ ^ (2 : ℝ≥0∞).toReal)).2 hf

@[deprecated (since := "2026-09-30")] alias memlp_comp_equiv := memℓp_comp_equiv

/-- Reindexing `ℓ²(V) → ℓ²(V')`, `ψ ↦ ψ ∘ e`, along a bijection `e : V' ≃ V`. -/
def reindex (e : V' ≃ V) : L2 V →ₗ[ℂ] L2 V' where
  toFun f := ⟨(f : V → ℂ) ∘ e, memℓp_comp_equiv e f.2⟩
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

omit [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V'] in
theorem norm_reindex (e : V' ≃ V) (f : L2 V) : ‖reindex e f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (E := fun _ : V' => ℂ) (by norm_num),
    lp.norm_eq_tsum_rpow (E := fun _ : V => ℂ) (by norm_num)]
  congr 1
  exact e.tsum_eq (fun v => ‖(f : V → ℂ) v‖ ^ (2 : ℝ≥0∞).toReal)

/-- The relabelling unitary `(U_T ψ)(v') = ψ(T⁻¹ v')`. -/
def relabel (T : V ≃ₗ[ℝ] V') : L2 V ≃ₗᵢ[ℂ] L2 V' where
  toFun := reindex T.symm.toEquiv
  invFun := reindex T.toEquiv
  map_add' := (reindex T.symm.toEquiv).map_add
  map_smul' := (reindex T.symm.toEquiv).map_smul
  left_inv f := by ext v; simp [reindex]
  right_inv f := by ext v; simp [reindex]
  norm_map' := norm_reindex T.symm.toEquiv

theorem relabel_apply (T : V ≃ₗ[ℝ] V') (f : L2 V) (v' : V') :
    relabel T f v' = f (T.symm v') := rfl

theorem relabel_symm_apply (T : V ≃ₗ[ℝ] V') (f : L2 V') (v : V) :
    (relabel T).symm f v = f (T v) := rfl

/-- `U_id = 1`. -/
theorem relabel_refl : relabel (LinearEquiv.refl ℝ V) = LinearIsometryEquiv.refl ℂ (L2 V) := by
  ext f v; rfl

/-- `U_{T₂ T₁} = U_{T₂} U_{T₁}`. -/
theorem relabel_trans (T₁ : V ≃ₗ[ℝ] V') (T₂ : V' ≃ₗ[ℝ] V'') :
    relabel (T₁.trans T₂) = (relabel T₁).trans (relabel T₂) := by
  ext f v; rfl

/-- `U_T* = U_{T⁻¹}`. -/
theorem relabel_symm (T : V ≃ₗ[ℝ] V') : relabel T.symm = (relabel T).symm := by
  ext f v; rfl

/-- The Hilbert adjoint `U_T* = U_{T⁻¹}`. -/
theorem adjoint_relabel (T : V ≃ₗ[ℝ] V') :
    ContinuousLinearMap.adjoint (relabel T : L2 V →L[ℂ] L2 V') =
      (relabel T.symm : L2 V' →L[ℂ] L2 V) := by
  rw [relabel_symm]
  exact LinearIsometryEquiv.adjoint_eq_symm (relabel T)

variable {σ : LinearMap.BilinForm ℝ V} {σ' : LinearMap.BilinForm ℝ V'}
  {σ'' : LinearMap.BilinForm ℝ V''}

/-- `U_T W(u) U_T* = W'(T u)` for symplectic `T`. -/
theorem conj_relabel_weyl {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v) (u : V) :
    (relabel T).conjStarAlgEquiv (weyl σ u) = weyl σ' (T u) := by
  ext f v'
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change phase σ u (T.symm v') * f (T (T.symm v' + u)) = phase σ' (T u) v' * f (v' + T u)
  rw [map_add, LinearEquiv.apply_symm_apply, phase, phase, ← hT, LinearEquiv.apply_symm_apply]

theorem symplectic_symm {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v) :
    ∀ u v, σ (T.symm u) (T.symm v) = σ' u v := by
  intro u v
  rw [← hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem continuous_conjStarAlgEquiv {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (e : H ≃ₗᵢ[ℂ] K) : Continuous e.conjStarAlgEquiv :=
  e.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous

/-- Conjugation by `U_T` maps `CCR σ` into `CCR σ'`. -/
theorem conj_relabel_mem_CCR {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v)
    {a : L2 V →L[ℂ] L2 V} (ha : a ∈ CCR σ) :
    (relabel T).conjStarAlgEquiv a ∈ CCR σ' := by
  set φ : (L2 V →L[ℂ] L2 V) →⋆ₐ[ℂ] (L2 V' →L[ℂ] L2 V') :=
    (relabel T).conjStarAlgEquiv.toStarAlgHom
  have hle : CCR σ ≤ (CCR σ').comap φ := by
    apply StarSubalgebra.topologicalClosure_minimal
    · rw [StarAlgebra.adjoin_le_iff]
      rintro _ ⟨u, rfl⟩
      change (relabel T).conjStarAlgEquiv (weyl σ u) ∈ CCR σ'
      rw [conj_relabel_weyl hT]
      exact weyl_mem_CCR σ' (T u)
    · exact (inferInstance : IsClosed ((CCR σ' : Set (L2 V' →L[ℂ] L2 V')))).preimage
        (continuous_conjStarAlgEquiv (relabel T))
  exact hle ha

/-- The star-algebra isomorphism `α_T : CCR σ ≃ CCR σ'`, `a ↦ U_T a U_T*`. -/
def CCR.relabel {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v) :
    CCR σ ≃⋆ₐ[ℂ] CCR σ' where
  toFun a := ⟨(Weyl.relabel T).conjStarAlgEquiv a, conj_relabel_mem_CCR hT a.2⟩
  invFun b := ⟨(Weyl.relabel T).conjStarAlgEquiv.symm b, by
    have h := conj_relabel_mem_CCR (T := T.symm) (symplectic_symm hT) b.2
    rwa [Weyl.relabel_symm] at h⟩
  left_inv a := Subtype.ext ((Weyl.relabel T).conjStarAlgEquiv.symm_apply_apply a)
  right_inv b := Subtype.ext ((Weyl.relabel T).conjStarAlgEquiv.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul (Weyl.relabel T).conjStarAlgEquiv (a : L2 V →L[ℂ] L2 V) b)
  map_add' a b := Subtype.ext (map_add (Weyl.relabel T).conjStarAlgEquiv (a : L2 V →L[ℂ] L2 V) b)
  map_star' a := Subtype.ext (map_star (Weyl.relabel T).conjStarAlgEquiv (a : L2 V →L[ℂ] L2 V))
  map_smul' c a := Subtype.ext (map_smul (Weyl.relabel T).conjStarAlgEquiv c (a : L2 V →L[ℂ] L2 V))

theorem CCR.coe_relabel_apply {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v)
    (a : CCR σ) :
    (CCR.relabel hT a : L2 V' →L[ℂ] L2 V') = (Weyl.relabel T).conjStarAlgEquiv a := rfl

/-- `α_T (W u) = W' (T u)`. -/
theorem CCR.relabel_weyl {T : V ≃ₗ[ℝ] V'} (hT : ∀ u v, σ' (T u) (T v) = σ u v)
    (u : V) : CCR.relabel hT ⟨Weyl.weyl σ u, weyl_mem_CCR σ u⟩ =
      ⟨Weyl.weyl σ' (T u), weyl_mem_CCR σ' _⟩ :=
  Subtype.ext (conj_relabel_weyl hT u)

/-- `α_id = id`. -/
theorem CCR.relabel_refl :
    CCR.relabel (σ := σ) (σ' := σ) (T := LinearEquiv.refl ℝ V) (fun _ _ => rfl) =
      StarAlgEquiv.refl (R := ℂ) (A := CCR σ) := by
  ext a f v
  rfl

/-- `α_{T₂ T₁} = α_{T₂} α_{T₁}`. -/
theorem CCR.relabel_trans {T₁ : V ≃ₗ[ℝ] V'} {T₂ : V' ≃ₗ[ℝ] V''}
    (h₁ : ∀ u v, σ' (T₁ u) (T₁ v) = σ u v) (h₂ : ∀ u v, σ'' (T₂ u) (T₂ v) = σ' u v) :
    CCR.relabel (T := T₁.trans T₂) (fun u v => (h₂ _ _).trans (h₁ u v)) =
      (CCR.relabel h₁).trans (CCR.relabel h₂) := by
  ext a f v
  simp only [CCR.coe_relabel_apply, StarAlgEquiv.trans_apply]
  rfl

end Weyl

end BosonicLean
