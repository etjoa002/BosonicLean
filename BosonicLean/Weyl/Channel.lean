/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.CStar.StarOrdered
import BosonicLean.CStar.CompletelyPositive
import BosonicLean.Weyl.Relabel
import BosonicLean.Weyl.State
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Gaussian channels on the CCR algebra

The definitions and results follow Krüger's thesis, §4.3, (4.32)–(4.35), and its Lemma 4.12 at the
level of covariances. A Gaussian channel on `CCR(V, σ)` is a completely positive map `T` with
`T(W(u)) = exp(i μ(u) − ν(u,u)/4) W(L u)` for a linear map `L`, a symmetric noise form `ν` and a
displacement form `μ`, whose data satisfy the condition (4.34): `ν + iσ − iσ(L·, L·) ≥ 0` on every
finite family. Complete positivity is a structure field; the theorem that (4.34) implies it
(Demoen–Vanheuverzwijn–Verbeure 1977, thesis Thm. 2.6) is not formalized.

## Main definitions

* `BosonicLean.Weyl.GaussianChannel`, its dissipation form `GaussianChannel.dissipation`;
* `GaussianChannel.ofRelabel`: the reversible case, a symplectic relabelling;
* `GaussianChannel.comp`: concatenation;
* `GaussianChannel.stateMap`: the action `ω ↦ ω ∘ T` on Gaussian states;
* `sumForm`, `dilA`, `dilC`: system and ancilla blocks of a dilation.

## Main statements

* `clm_ext_weyl`, `cp_ext_weyl`: maps out of `CCR(V, σ)` are determined by the Weyl operators;
* `GaussianChannel.ext_of_data`: a Gaussian channel is determined by its data;
* `GaussianChannel.map_weyl_mul`: the product formula (4.35);
* `GaussianChannel.map_eq_ofRelabel`: a noiseless channel with bijective `L` is the relabelling;
* `GaussianChannel.dissipation_comp`: the dissipation form of a concatenation;
* `dilation_isStateConditionC`, `dilation_cov`: dilation data satisfy (4.34), and (4.40).
-/

open scoped CStarAlgebra ComplexOrder

namespace BosonicLean.Weyl

open BosonicLean.CStar

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Extensionality

variable {σ : LinearMap.BilinForm ℝ V}

/-- Continuous linear maps out of `CCR(V, σ)` that agree on all Weyl operators are equal. (QCALean
notes: `lem:ch-unit`) -/
theorem clm_ext_weyl (hσ : σ.IsAlt) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : CCR σ →L[ℂ] E} (h : ∀ u, f (wCCR σ u) = g (wCCR σ u)) : f = g := by
  have hW : Set.EqOn f g (Set.range (CCR.weylSystem σ hσ).W) := by
    rintro _ ⟨u, rfl⟩; exact h u
  have hcl := (LinearMap.eqOn_span' (f := f.toLinearMap) (g := g.toLinearMap)
    hW).closure f.continuous g.continuous
  exact ContinuousLinearMap.ext fun y => hcl (weyl_mem_closure_span _ hσ y)

/-- Completely positive maps of `CCR(V, σ)` that agree on all Weyl operators are equal. (QCALean
notes: `lem:ch-unit`) -/
theorem cp_ext_weyl (hσ : σ.IsAlt) {f g : CCR σ →CP CCR σ}
    (h : ∀ u, f (wCCR σ u) = g (wCCR σ u)) : f = g := by
  have := clm_ext_weyl hσ (f := ⟨f.toLinearMap, map_continuous f⟩)
    (g := ⟨g.toLinearMap, map_continuous g⟩) h
  exact cpExt fun x => congrArg (fun F : CCR σ →L[ℂ] CCR σ => F x) this

end Extensionality

section Channel

variable (σ : LinearMap.BilinForm ℝ V)

/-- A Gaussian channel on `CCR(V, σ)` (thesis (4.32), with the displacement of the standard
definition). The completely positive map `map` sends `W(u)` to `exp(i μ(u) − ν(u,u)/4) W(L u)`, and
the data satisfy the condition (4.34), stated as the state condition for `ν` and the alternating
form `σ − σ(L·, L·)`. (QCALean notes: `def:ch-channel`) -/
structure GaussianChannel where
  /-- The linear map `L` of phase space (the thesis's `Γ`). -/
  lin : V →ₗ[ℝ] V
  /-- The noise form `ν` (the thesis's `g`). -/
  noise : LinearMap.BilinForm ℝ V
  /-- The noise form is symmetric. -/
  noise_isSymm : noise.IsSymm
  /-- The displacement form `μ`. -/
  disp : V →ₗ[ℝ] ℝ
  /-- The condition (4.34), `ν + iσ − iσ(L·, L·) ≥ 0`. -/
  cond : IsStateConditionC noise (σ - σ.comp lin lin)
  /-- The completely positive map on the CCR algebra. -/
  map : CCR σ →CP CCR σ
  /-- The action on Weyl operators, `T(W(u)) = exp(i μ(u) − ν(u,u)/4) W(L u)`. -/
  map_weyl : ∀ u, map (wCCR σ u) =
    Complex.exp (Complex.I * (disp u : ℂ) - (noise u u : ℂ) / 4) • wCCR σ (lin u)

namespace GaussianChannel

variable {σ}

/-- The dissipation form `C(u,w) = ν(u,w) + iσ(u,w) − iσ(Lu, Lw)` of (4.34).
(QCALean notes: `def:ch-channel`) -/
noncomputable def dissipation (T : GaussianChannel σ) (u w : V) : ℂ :=
  (T.noise u w : ℂ) + Complex.I * ((σ u w : ℂ) - (σ (T.lin u) (T.lin w) : ℂ))

@[simp]
theorem dissipation_apply (T : GaussianChannel σ) (u w : V) :
    T.dissipation u w =
      (T.noise u w : ℂ) + Complex.I * ((σ u w : ℂ) - (σ (T.lin u) (T.lin w) : ℂ)) := rfl

/-- A Gaussian channel is unital. (QCALean notes: `lem:ch-unit`) -/
@[simp]
theorem map_one (T : GaussianChannel σ) : T.map 1 = 1 := by
  rw [← wCCR_zero, T.map_weyl]
  simp [wCCR_zero]

/-- The underlying map of a Gaussian channel, as a continuous linear map (positive linear maps
between C*-algebras are continuous). -/
noncomputable def toCLM (T : GaussianChannel σ) : CCR σ →L[ℂ] CCR σ :=
  ⟨T.map.toLinearMap, map_continuous T.map⟩

@[simp]
theorem toCLM_apply (T : GaussianChannel σ) (a : CCR σ) : T.toCLM a = T.map a := rfl

@[deprecated BosonicLean.Weyl.clm_ext_weyl (since := "2026-10-01")]
alias clm_ext_weyl := BosonicLean.Weyl.clm_ext_weyl

@[deprecated BosonicLean.Weyl.cp_ext_weyl (since := "2026-10-01")]
alias cp_ext_weyl := BosonicLean.Weyl.cp_ext_weyl

/-- Two Gaussian channels with the same data and the same map are equal. -/
@[ext]
theorem ext {T T' : GaussianChannel σ} (hlin : T.lin = T'.lin) (hnoise : T.noise = T'.noise)
    (hdisp : T.disp = T'.disp) (hmap : T.map = T'.map) : T = T' := by
  cases T; cases T'; cases hlin; cases hnoise; cases hdisp; cases hmap; rfl

/-- A Gaussian channel is determined by its data `(L, ν, μ)`: the map is fixed on the Weyl
operators, hence everywhere. -/
theorem ext_of_data (hσ : σ.IsAlt) {T T' : GaussianChannel σ} (hlin : T.lin = T'.lin)
    (hnoise : T.noise = T'.noise) (hdisp : T.disp = T'.disp) : T = T' :=
  ext hlin hnoise hdisp (BosonicLean.Weyl.cp_ext_weyl hσ fun u => by
    rw [T.map_weyl, T'.map_weyl, hlin, hnoise, hdisp])

/-- The product formula (4.35), `T(W(u) W(w)) = e^{−C(u,w)/2} T(W(u)) T(W(w))`. (QCALean notes:
`prop:ch-product`) -/
theorem map_weyl_mul (hσ : σ.IsAlt) (T : GaussianChannel σ) (u w : V) :
    T.map (wCCR σ u * wCCR σ w) =
      Complex.exp (-T.dissipation u w / 2) • (T.map (wCCR σ u) * T.map (wCCR σ w)) := by
  rw [wCCR_mul hσ, map_smul, T.map_weyl, smul_smul, T.map_weyl, T.map_weyl, smul_mul_smul_comm,
    wCCR_mul hσ, smul_smul, smul_smul, map_add]
  congr 1
  · simp only [dissipation_apply, map_add, LinearMap.add_apply, ← Complex.exp_add]
    congr 1
    have hs : T.noise w u = T.noise u w := T.noise_isSymm.eq w u
    rw [hs]
    push_cast
    ring
  · rw [map_add]

/-- The images of two Weyl operators under a Gaussian channel multiply to a non-zero multiple of
a Weyl operator. -/
theorem map_wCCR_mul_map_wCCR (hσ : σ.IsAlt) (T : GaussianChannel σ) (u w : V) :
    ∃ k : ℂ, k ≠ 0 ∧
      T.map (wCCR σ u) * T.map (wCCR σ w) = k • wCCR σ (T.lin u + T.lin w) := by
  rw [T.map_weyl, T.map_weyl, smul_mul_smul_comm, wCCR_mul hσ, smul_smul]
  exact ⟨_, mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (Complex.exp_ne_zero _), rfl⟩

/-- If a Gaussian channel is multiplicative on a pair of Weyl operators, the dissipation factor
of the product formula is one. -/
theorem exp_dissipation_eq_one (hσ : σ.IsAlt) (T : GaussianChannel σ) {u w : V}
    (h : T.map (wCCR σ u * wCCR σ w) = T.map (wCCR σ u) * T.map (wCCR σ w)) :
    Complex.exp (-T.dissipation u w / 2) = 1 := by
  rw [T.map_weyl_mul hσ] at h
  obtain ⟨k, hk, hkW⟩ := map_wCCR_mul_map_wCCR hσ T u w
  rw [hkW, smul_smul] at h
  have h' := congrArg Subtype.val h
  simp only [SetLike.val_smul] at h'
  have := (weyl_eq_of_smul_eq hσ hk h').2
  exact (mul_eq_right₀ hk).1 this

/-- The dissipation form is linear in its first argument. -/
theorem dissipation_smul_left (T : GaussianChannel σ) (t : ℝ) (u w : V) :
    T.dissipation (t • u) w = t * T.dissipation u w := by
  simp only [dissipation_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end GaussianChannel

end Channel

section SpecialCases

variable {σ : LinearMap.BilinForm ℝ V}

/-- If the noise vanishes, (4.34) forces `L` to preserve `σ`. (QCALean notes: `prop:ch-special`) -/
theorem preserves_of_noise_eq_zero (hσ : σ.IsAlt) {L : V →ₗ[ℝ] V}
    (h : IsStateConditionC 0 (σ - σ.comp L L)) : ∀ u w, σ (L u) (L w) = σ u w := by
  have halt : (σ - σ.comp L L).IsAlt := fun u => by
    simp [hσ u, hσ (L u)]
  have hsymm : (0 : LinearMap.BilinForm ℝ V).IsSymm := ⟨fun _ _ => rfl⟩
  have h' := ((isStateConditionC_iff hsymm halt).1 h).2
  intro u w
  have := h' u w
  simp only [LinearMap.zero_apply, mul_zero, LinearMap.sub_apply,
    LinearMap.BilinForm.comp_apply] at this
  nlinarith [sq_nonneg (σ u w - σ (L u) (L w))]

/-- For `σ`-preserving `L`, the condition (4.34) says that `ν` is positive semidefinite. (QCALean
notes: `prop:ch-special`) -/
theorem isStateConditionC_iff_of_preserves {L : V →ₗ[ℝ] V}
    (hL : ∀ u w, σ (L u) (L w) = σ u w) {ν : LinearMap.BilinForm ℝ V} (hν : ν.IsSymm) :
    IsStateConditionC ν (σ - σ.comp L L) ↔ ∀ u, 0 ≤ ν u u := by
  have h0 : σ - σ.comp L L = 0 := by
    ext u w; simp [hL u w]
  rw [h0, isStateConditionC_iff hν (fun _ => rfl)]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun u w => by simpa using mul_nonneg (h u) (h w)⟩

/-- For `L = 0`, the condition (4.34) is the state condition `ν + iσ ≥ 0`. (QCALean notes:
`prop:ch-special`) -/
theorem isStateConditionC_zero_lin (ν : LinearMap.BilinForm ℝ V) :
    IsStateConditionC ν (σ - σ.comp 0 0) ↔ IsStateConditionC ν σ := by
  have h0 : σ - σ.comp 0 0 = σ := by
    ext u w; simp
  rw [h0]

end SpecialCases

namespace GaussianChannel

variable {σ : LinearMap.BilinForm ℝ V}

variable (σ) in
/-- The reversible case. A linear bijection preserving `σ`, with no noise and no displacement, is a
Gaussian channel whose map is the relabelling automorphism `α_L = CCR.relabel`. (QCALean notes:
`prop:ch-reversible`) -/
noncomputable def ofRelabel {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v) :
    GaussianChannel σ where
  lin := L.toLinearMap
  noise := 0
  noise_isSymm := ⟨fun _ _ => rfl⟩
  disp := 0
  cond := by
    have h0 : σ - σ.comp L.toLinearMap L.toLinearMap = 0 := by
      ext u w; simp [hL u w]
    rw [h0]
    intro m u
    simp only [LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, add_zero]
    exact Matrix.PosSemidef.zero
  map := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CCR.relabel hL : CCR σ ≃⋆ₐ[ℂ] CCR σ)
  map_weyl u := by
    simp only [LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, zero_div, sub_zero,
      Complex.exp_zero, one_smul, LinearEquiv.coe_coe]
    exact CCR.relabel_weyl hL u

@[simp]
theorem ofRelabel_lin {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v) :
    (ofRelabel σ hL).lin = L.toLinearMap := rfl

@[simp]
theorem ofRelabel_noise {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v) :
    (ofRelabel σ hL).noise = 0 := rfl

@[simp]
theorem ofRelabel_disp {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v) :
    (ofRelabel σ hL).disp = 0 := rfl

@[simp]
theorem ofRelabel_map_apply {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v)
    (a : CCR σ) : (ofRelabel σ hL).map a = CCR.relabel hL a := rfl

/-- Every Gaussian channel with no noise, no displacement and bijective `L` is the relabelling
`α_L`. (QCALean notes: `prop:ch-reversible`) -/
theorem map_eq_ofRelabel (hσ : σ.IsAlt) (T : GaussianChannel σ) (hν : T.noise = 0)
    (hd : T.disp = 0) {L : V ≃ₗ[ℝ] V} (hL : ∀ u v, σ (L u) (L v) = σ u v)
    (hlin : L.toLinearMap = T.lin) : T.map = (ofRelabel σ hL).map := by
  apply BosonicLean.Weyl.cp_ext_weyl hσ
  intro u
  rw [T.map_weyl, ofRelabel_map_apply, hν, hd, ← hlin]
  simp only [LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, zero_div, sub_zero,
    Complex.exp_zero, one_smul, LinearEquiv.coe_coe]
  exact (CCR.relabel_weyl hL u).symm

/-- (Thesis p. 96) The concatenation `T₂ ∘ T₁`, with `L = L₂ L₁`, `ν = ν₁ + ν₂(L₁·, L₁·)` and
`μ = μ₁ + μ₂ ∘ L₁`. (QCALean notes: `prop:ch-comp`) -/
noncomputable def comp (T₂ T₁ : GaussianChannel σ) : GaussianChannel σ where
  lin := T₂.lin ∘ₗ T₁.lin
  noise := T₁.noise + T₂.noise.comp T₁.lin T₁.lin
  noise_isSymm := ⟨fun u w => by
    simp [T₁.noise_isSymm.eq u w, T₂.noise_isSymm.eq (T₁.lin u) (T₁.lin w)]⟩
  disp := T₁.disp + T₂.disp ∘ₗ T₁.lin
  cond := by
    convert T₁.cond.add (T₂.cond.comp T₁.lin) using 1
    ext u w
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.BilinForm.comp_apply,
      LinearMap.coe_comp, Function.comp_apply]
    ring
  map := cpComp T₂.map T₁.map
  map_weyl u := by
    rw [cpComp_apply, T₁.map_weyl, map_smul, T₂.map_weyl, smul_smul, ← Complex.exp_add]
    congr 2
    simp only [LinearMap.add_apply, LinearMap.BilinForm.comp_apply, LinearMap.coe_comp,
      Function.comp_apply]
    push_cast
    ring

@[simp]
theorem comp_lin (T₂ T₁ : GaussianChannel σ) : (comp T₂ T₁).lin = T₂.lin ∘ₗ T₁.lin := rfl

@[simp]
theorem comp_noise (T₂ T₁ : GaussianChannel σ) :
    (comp T₂ T₁).noise = T₁.noise + T₂.noise.comp T₁.lin T₁.lin := rfl

@[simp]
theorem comp_disp (T₂ T₁ : GaussianChannel σ) :
    (comp T₂ T₁).disp = T₁.disp + T₂.disp ∘ₗ T₁.lin := rfl

@[simp]
theorem comp_map_apply (T₂ T₁ : GaussianChannel σ) (a : CCR σ) :
    (comp T₂ T₁).map a = T₂.map (T₁.map a) := rfl

/-- The dissipation form of a concatenation is `C₁ + C₂(L₁·, L₁·)`. (QCALean notes: `prop:ch-comp`)
-/
theorem dissipation_comp (T₂ T₁ : GaussianChannel σ) (u w : V) :
    (comp T₂ T₁).dissipation u w =
      T₁.dissipation u w + T₂.dissipation (T₁.lin u) (T₁.lin w) := by
  simp only [dissipation_apply, comp_lin, comp_noise, LinearMap.add_apply,
    LinearMap.BilinForm.comp_apply, LinearMap.coe_comp, Function.comp_apply]
  push_cast
  ring

/-- ((4.33), sign corrected) The action of a Gaussian channel on a Gaussian state, `ω ↦ ω ∘ T`, with
covariance `γ(L·, L·) + ν` and displacement `d ∘ L + μ`. (QCALean notes: `prop:ch-states`) -/
noncomputable def stateMap (T : GaussianChannel σ) (ω : GaussianState σ) : GaussianState σ where
  toState :=
    { toCLM := ω.toCLM.comp T.toCLM
      map_one := by
        change ω.toCLM (T.map 1) = 1
        rw [map_one]; exact ω.map_one
      nonneg := fun a => by
        change 0 ≤ ω.toCLM (T.map (star a * a))
        have hpos : 0 ≤ T.map (star a * a) := map_nonneg T.map (star_mul_self_nonneg a)
        obtain ⟨b, hb⟩ :=
          (BosonicLean.StarSubalgebra.nonneg_iff_exists_star_mul_self (CCR σ) _).1 hpos
        rw [hb]
        exact ω.nonneg b }
  cov := ω.cov.comp T.lin T.lin + T.noise
  isSymm := ⟨fun u w => by
    simp [ω.isSymm.eq (T.lin u) (T.lin w), T.noise_isSymm.eq u w]⟩
  disp := ω.disp ∘ₗ T.lin + T.disp
  charFun_eq u := by
    change ω.toCLM (T.map (wCCR σ u)) = _
    rw [T.map_weyl, map_smul, smul_eq_mul]
    have hω := ω.charFun_eq (T.lin u)
    change ω.toCLM (wCCR σ (T.lin u)) = _ at hω
    rw [hω, ← Complex.exp_add]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.BilinForm.comp_apply, LinearMap.coe_comp,
      Function.comp_apply]
    push_cast
    ring

/-- `(ω ∘ T)(a) = ω(T a)`. (QCALean notes: `prop:ch-states`) -/
@[simp]
theorem stateMap_apply (T : GaussianChannel σ) (ω : GaussianState σ) (a : CCR σ) :
    (T.stateMap ω).toCLM a = ω.toCLM (T.map a) := rfl

@[simp]
theorem stateMap_cov (T : GaussianChannel σ) (ω : GaussianState σ) :
    (T.stateMap ω).cov = ω.cov.comp T.lin T.lin + T.noise := rfl

@[simp]
theorem stateMap_disp (T : GaussianChannel σ) (ω : GaussianState σ) :
    (T.stateMap ω).disp = ω.disp ∘ₗ T.lin + T.disp := rfl

end GaussianChannel

section Dilation

variable {V' : Type*} [AddCommGroup V'] [Module ℝ V']

/-- The direct sum `β ⊕ β'` of two bilinear forms, on `V × V'`. -/
def sumForm (β : LinearMap.BilinForm ℝ V) (β' : LinearMap.BilinForm ℝ V') :
    LinearMap.BilinForm ℝ (V × V') :=
  β.comp (LinearMap.fst ℝ V V') (LinearMap.fst ℝ V V') +
    β'.comp (LinearMap.snd ℝ V V') (LinearMap.snd ℝ V V')

@[simp]
theorem sumForm_apply (β : LinearMap.BilinForm ℝ V) (β' : LinearMap.BilinForm ℝ V')
    (x y : V × V') : sumForm β β' x y = β x.1 y.1 + β' x.2 y.2 := rfl

/-- The system block `A u = P₁ S(u, 0)` of a map of system plus ancilla. -/
def dilA (S : V × V' →ₗ[ℝ] V × V') : V →ₗ[ℝ] V :=
  LinearMap.fst ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V'

/-- The ancilla block `C u = P₂ S(u, 0)` of a map of system plus ancilla. -/
def dilC (S : V × V' →ₗ[ℝ] V × V') : V →ₗ[ℝ] V' :=
  LinearMap.snd ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V'

@[simp]
theorem dilA_apply (S : V × V' →ₗ[ℝ] V × V') (u : V) : dilA S u = (S (u, 0)).1 := rfl

@[simp]
theorem dilC_apply (S : V × V' →ₗ[ℝ] V × V') (u : V) : dilC S u = (S (u, 0)).2 := rfl

variable {σ : LinearMap.BilinForm ℝ V} {σ' : LinearMap.BilinForm ℝ V'}

/-- `σ(Au, Aw) + σ'(Cu, Cw) = σ(u, w)` for `S` preserving `σ ⊕ σ'`. (QCALean notes:
`prop:ch-dilation`) -/
theorem dilation_preserves (S : V × V' →ₗ[ℝ] V × V')
    (hS : ∀ x y, sumForm σ σ' (S x) (S y) = sumForm σ σ' x y) (u w : V) :
    σ (dilA S u) (dilA S w) + σ' (dilC S u) (dilC S w) = σ u w := by
  simpa using hS (u, 0) (w, 0)

/-- The dilation data `(A, γ'(C·, C·))` satisfy the condition (4.34), since
`γ'(C·, C·) + iσ − iσ(A·, A·) = (γ' + iσ')(C·, C·)`. (QCALean notes: `prop:ch-dilation`) -/
theorem dilation_isStateConditionC (S : V × V' →ₗ[ℝ] V × V')
    (hS : ∀ x y, sumForm σ σ' (S x) (S y) = sumForm σ σ' x y)
    {γ' : LinearMap.BilinForm ℝ V'} (hγ' : IsStateConditionC γ' σ') :
    IsStateConditionC (γ'.comp (dilC S) (dilC S)) (σ - σ.comp (dilA S) (dilA S)) := by
  intro m u
  convert hγ' m (fun j => dilC S (u j)) using 1
  ext j k
  have h := dilation_preserves S hS (u j) (u k)
  simp only [Matrix.of_apply, LinearMap.BilinForm.comp_apply, LinearMap.sub_apply]
  rw [← h]
  push_cast
  ring

/-- (Thesis (4.40)) The reduced covariance, `(γ ⊕ γ')(S(u,0), S(w,0)) = γ(Au, Aw) + γ'(Cu, Cw)`.
(QCALean notes: `prop:ch-dilation`) -/
theorem dilation_cov (S : V × V' →ₗ[ℝ] V × V') (γ : LinearMap.BilinForm ℝ V)
    (γ' : LinearMap.BilinForm ℝ V') :
    (sumForm γ γ').comp (S ∘ₗ LinearMap.inl ℝ V V') (S ∘ₗ LinearMap.inl ℝ V V') =
      γ.comp (dilA S) (dilA S) + γ'.comp (dilC S) (dilC S) := by
  ext u w
  simp

end Dilation

end BosonicLean.Weyl
