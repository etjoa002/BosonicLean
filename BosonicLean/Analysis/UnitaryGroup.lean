/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# One-parameter unitary groups and their generators

A strongly continuous one-parameter unitary group on a complex Hilbert space `E` is a map
`t ↦ U t` from `ℝ` to the unitary operators with `U 0 = 1`, `U (s + t) = U s * U t` and
`t ↦ U t ψ` continuous for every `ψ`. An operator `A` (a `LinearPMap`) is its generator,
`U t = e^{-itA}`, if `dom A` is the set of `ψ` at which `t ↦ U t ψ` is differentiable at `0`, and
the derivative there is `-iAψ`.

We prove the elementary half of Stone's theorem without the spectral theorem: a generator is
densely defined and self-adjoint, it commutes with the group, two groups with the same generator
are equal, and a self-adjoint operator generates every group whose derivative it gives on a core.

## Main definitions

* `BosonicLean.IsUnitaryGroup U`: `U` is a strongly continuous one-parameter unitary group.
* `BosonicLean.IsGenerator A U`: `A` is the generator of `U`.

## Main results

* `BosonicLean.IsGenerator.apply_mem_domain`, `.apply_comm`, `.hasDerivAt_apply`: Theorem 2(a).
* `BosonicLean.IsGenerator.dense_domain`, `.isSelfAdjoint`: Theorem 2(b).
* `BosonicLean.IsGenerator.unique`: Theorem 2(c).
* `BosonicLean.IsGenerator.of_core`: Theorem 2(d).
* `BosonicLean.isSelfAdjoint_of_isClosed`: a closed, densely defined symmetric operator `A` with
  `A.adjointφ = ±iφ ⇒ φ = 0` is self-adjoint (the basic criterion).

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*, Academic Press (1980), §VIII.
-/

open scoped InnerProductSpace
open Filter Topology Complex

namespace BosonicLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Definition 1(a).** `U` is a strongly continuous one-parameter unitary group. -/
structure IsUnitaryGroup (U : ℝ → unitary (E →L[ℂ] E)) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = U s * U t
  continuous_apply : ∀ ψ, Continuous fun t => (U t : E →L[ℂ] E) ψ

/-- **Definition 1(b).** `A` is the generator of `U`, `U t = e^{-itA}`: the domain of `A` is the
set of `ψ` at which `t ↦ U t ψ` is differentiable at `0`, and the derivative there is `-iAψ`. -/
structure IsGenerator (A : E →ₗ.[ℂ] E) (U : ℝ → unitary (E →L[ℂ] E)) : Prop where
  isUnitaryGroup : IsUnitaryGroup U
  mem_domain_iff : ∀ ψ, ψ ∈ A.domain ↔ ∃ v, HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) v 0
  hasDerivAt : ∀ ψ : A.domain,
    HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) (-(I • A ψ)) 0

namespace IsUnitaryGroup

variable {U : ℝ → unitary (E →L[ℂ] E)} (hU : IsUnitaryGroup U)
include hU

theorem apply_apply (s t : ℝ) (ψ : E) :
    (U s : E →L[ℂ] E) ((U t : E →L[ℂ] E) ψ) = (U (s + t) : E →L[ℂ] E) ψ := by
  rw [hU.map_add]; rfl

theorem apply_zero (ψ : E) : (U 0 : E →L[ℂ] E) ψ = ψ := by
  rw [hU.map_zero]; rfl

theorem apply_neg_apply (t : ℝ) (ψ : E) :
    (U (-t) : E →L[ℂ] E) ((U t : E →L[ℂ] E) ψ) = ψ := by
  rw [hU.apply_apply, neg_add_cancel, hU.apply_zero]

theorem apply_apply_neg (t : ℝ) (ψ : E) :
    (U t : E →L[ℂ] E) ((U (-t) : E →L[ℂ] E) ψ) = ψ := by
  rw [hU.apply_apply, add_neg_cancel, hU.apply_zero]

theorem comm_apply (s t : ℝ) (ψ : E) :
    (U s : E →L[ℂ] E) ((U t : E →L[ℂ] E) ψ) = (U t : E →L[ℂ] E) ((U s : E →L[ℂ] E) ψ) := by
  rw [hU.apply_apply, hU.apply_apply, add_comm]

omit hU in
theorem norm_apply (t : ℝ) (ψ : E) : ‖(U t : E →L[ℂ] E) ψ‖ = ‖ψ‖ :=
  Unitary.norm_map (U t) ψ

omit hU in
theorem inner_apply_apply (t : ℝ) (ψ φ : E) :
    ⟪(U t : E →L[ℂ] E) ψ, (U t : E →L[ℂ] E) φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
  Unitary.inner_map_map (U t) ψ φ

/-- `⟪U t ψ, φ⟫ = ⟪ψ, U (-t) φ⟫`. -/
theorem inner_apply_left (t : ℝ) (ψ φ : E) :
    ⟪(U t : E →L[ℂ] E) ψ, φ⟫_ℂ = ⟪ψ, (U (-t) : E →L[ℂ] E) φ⟫_ℂ := by
  conv_lhs => rw [← hU.apply_apply_neg t φ]
  exact IsUnitaryGroup.inner_apply_apply t ψ _

end IsUnitaryGroup

/-- A scalar function with `g' = c g` for a real `c ≠ 0` that is bounded on `ℝ` vanishes at `0`. -/
theorem eq_zero_of_hasDerivAt_mul_of_bounded {g : ℝ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (hg : ∀ t, HasDerivAt g (c * g t) t) {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M) : g 0 = 0 := by
  -- `h t = e^{-ct} g t` has derivative `0`, so `g t = e^{ct} g 0`.
  set h : ℝ → ℂ := fun t => (Real.exp (-(c * t)) : ℂ) * g t with hh
  have hd : ∀ t, HasDerivAt h 0 t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => ((Real.exp (-(c * t)) : ℝ) : ℂ))
        (((Real.exp (-(c * t)) * -(c * 1) : ℝ)) : ℂ) t :=
      (((hasDerivAt_id t).const_mul c).neg.exp).ofReal_comp
    convert h1.mul (hg t) using 1
    push_cast
    ring
  have hconst : ∀ t, h t = h 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hgt : ∀ t, g t = (Real.exp (c * t) : ℂ) * g 0 := fun t => by
    have := hconst t
    simp only [hh, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] at this
    rw [← this, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  by_contra h0
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 h0
  -- choose `t` with `c t` large
  obtain ⟨t, ht⟩ : ∃ t : ℝ, M / ‖g 0‖ < c * t := by
    refine ⟨(|M / ‖g 0‖| + 1) / c, ?_⟩
    rw [mul_div_cancel₀ _ hc]
    linarith [le_abs_self (M / ‖g 0‖)]
  have hle := hM t
  rw [hgt t, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hle
  have : M / ‖g 0‖ < Real.exp (c * t) :=
    ht.trans_le (by linarith [Real.add_one_le_exp (c * t)])
  rw [div_lt_iff₀ hpos] at this
  linarith

/-- **The basic criterion.** A densely defined, closed, symmetric operator `A` such that
`A.adjointφ = iφ` and `A.adjointφ = -iφ` force `φ = 0` is self-adjoint. -/
theorem isSelfAdjoint_of_isClosed {A : E →ₗ.[ℂ] E} (hd : Dense (A.domain : Set E))
    (hcl : A.IsClosed) (hsym : ∀ x y : A.domain, ⟪A x, y⟫_ℂ = ⟪(x : E), A y⟫_ℂ)
    (hker : ∀ s : ℂ, (s = I ∨ s = -I) → ∀ φ : A.adjoint.domain, A.adjoint φ = s • (φ : E) → (φ : E) = 0) :
    IsSelfAdjoint A := by
  have hle : A ≤ A.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd fun x y => hsym x y
  -- `L = A - i` on `dom A`
  set L : A.domain →ₗ[ℂ] E := A.toFun - I • A.domain.subtype with hL
  have hLapply : ∀ x : A.domain, L x = A x - I • (x : E) := fun x => rfl
  -- `‖Lx‖² = ‖Ax‖² + ‖x‖²`
  have hnorm : ∀ x : A.domain, ‖(x : E)‖ ≤ ‖L x‖ := fun x => by
    have hre : (⟪A x, (x : E)⟫_ℂ).im = 0 := by
      have h := hsym x x
      have h2 := inner_conj_symm (𝕜 := ℂ) (A x) (x : E)
      rw [h] at h2
      have := congrArg Complex.im h2
      simp only [Complex.conj_im] at this
      rw [h]
      linarith
    have h2 : ‖L x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
      rw [hLapply, @norm_sub_sq ℂ, norm_smul, Complex.norm_I, one_mul, inner_smul_right]
      have : RCLike.re (I * ⟪A x, (x : E)⟫_ℂ) = 0 := by
        simp [hre]
      rw [this]
      ring
    nlinarith [norm_nonneg (A x), norm_nonneg (L x), norm_nonneg (x : E)]
  -- the range of `L` is closed
  have hclosed : IsClosed (LinearMap.range L : Set E) := by
    refine isClosed_of_closure_subset fun y hy => ?_
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hy
    choose x hx using fun n => (hu n)
    have hcx : CauchySeq fun n => ((x n : A.domain) : E) := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
      refine ⟨N, fun n hn => ?_⟩
      have := hnorm (x n - x N)
      rw [map_sub, hx, hx] at this
      rw [dist_eq_norm]
      exact this.trans_lt (by simpa [dist_eq_norm] using hN n hn)
    obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hcx
    have hAx : Tendsto (fun n => A (x n)) atTop (𝓝 (y + I • x₀)) := by
      have : (fun n => A (x n)) = fun n => u n + I • ((x n : A.domain) : E) := funext fun n => by
        rw [← hx, hLapply]; abel
      rw [this]
      exact hlim.add (hx₀.const_smul I)
    have hmem : (x₀, y + I • x₀) ∈ A.graph := by
      have hg : IsClosed (A.graph : Set (E × E)) := hcl
      refine hg.mem_of_tendsto (hx₀.prodMk_nhds hAx) (Eventually.of_forall fun n => ?_)
      exact (LinearPMap.mem_graph_iff _).2 ⟨x n, rfl, rfl⟩
    obtain ⟨x', hx'1, hx'2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
    refine ⟨x', ?_⟩
    rw [hLapply, hx'2, hx'1]
    simp
  -- the range of `L` is dense: its orthogonal complement is `0`
  have hperp : (LinearMap.range L)ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have hφ' : ∀ x : A.domain, ⟪φ, A x⟫_ℂ = ⟪-(I • φ), (x : E)⟫_ℂ := fun x => by
      have h0 : ⟪φ, L x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal' _ _).1 hφ _ (LinearMap.mem_range_self L x)
      rw [hLapply, inner_sub_right, inner_smul_right, sub_eq_zero] at h0
      rw [h0, inner_neg_left, inner_smul_left, Complex.conj_I]
      ring
    have hmem : φ ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨-(I • φ), fun x => (hφ' x).symm⟩
    have hval : A.adjoint ⟨φ, hmem⟩ = -(I • φ) :=
      LinearPMap.adjoint_apply_eq hd _ fun x => (hφ' x).symm
    exact hker (-I) (Or.inr rfl) ⟨φ, hmem⟩ (by rw [hval, neg_smul])
  have htop : LinearMap.range L = ⊤ := by
    have : CompleteSpace (LinearMap.range L) := hclosed.completeSpace_coe
    exact Submodule.orthogonal_eq_bot_iff.1 hperp
  -- `A.adjoint ≤ A`
  refine le_antisymm ?_ hle
  have hdom : A.adjoint.domain ≤ A.domain := fun φ hφ => by
    obtain ⟨x, hx⟩ : (A.adjoint ⟨φ, hφ⟩ - I • φ) ∈ LinearMap.range L := by rw [htop]; trivial
    have hxle : ((x : A.domain) : E) ∈ A.adjoint.domain := hle.1 x.2
    have hAx : A.adjoint ⟨x, hxle⟩ = A x := (hle.2 rfl).symm
    have hφeq : A.adjoint ⟨φ, hφ⟩ = A x - I • (x : E) + I • φ := by
      rw [← hLapply, hx]; abel
    -- `A.adjoint (φ - x) = i (φ - x)`
    have hdiff : A.adjoint (⟨φ, hφ⟩ - ⟨x, hxle⟩) = I • ((φ : E) - x) := by
      rw [A.adjoint.map_sub, hAx, hφeq, smul_sub]; abel
    have h0 := hker I (Or.inl rfl) (⟨φ, hφ⟩ - ⟨x, hxle⟩) (by rw [hdiff]; rfl)
    have : φ = x := sub_eq_zero.1 h0
    rw [this]; exact x.2
  exact ⟨hdom, fun φ ψ hφψ => (hle.2 hφψ.symm).symm⟩

/-- If `B ≤ C` and `dom B` is dense, then `C† ≤ B†`. -/
theorem adjoint_le_adjoint {B C : E →ₗ.[ℂ] E} (hB : Dense (B.domain : Set E)) (h : B ≤ C) :
    C.adjoint ≤ B.adjoint := by
  have hC : Dense (C.domain : Set E) := hB.mono h.1
  have key : ∀ y : C.adjoint.domain, ∀ x : B.domain,
      ⟪C.adjoint y, (x : E)⟫_ℂ = ⟪(y : E), B x⟫_ℂ := fun y x => by
    rw [LinearPMap.adjoint_isFormalAdjoint hC y ⟨x, h.1 x.2⟩,
      h.2 (x := x) (y := ⟨x, h.1 x.2⟩) rfl]
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists _
    ⟨C.adjoint ⟨y, hy⟩, fun x => key ⟨y, hy⟩ x⟩, fun y z hyz => ?_⟩
  refine (LinearPMap.adjoint_apply_eq hB z fun x => ?_).symm
  rw [← hyz]
  exact key y x

/-- If `f ≤ g` with `g` closed, then the closure of `f` is `≤ g`. -/
theorem closure_le_of_isClosed {f g : E →ₗ.[ℂ] E} (hg : g.IsClosed) (h : f ≤ g) :
    f.closure ≤ g := by
  have hf : f.IsClosable := hg.isClosable.leIsClosable h
  refine LinearPMap.le_of_le_graph ?_
  rw [← hf.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le h) hg

/-- The adjoint of a closable operator is `≤` the adjoint of its closure. -/
theorem adjoint_le_adjoint_closure {T : E →ₗ.[ℂ] E}
    (hT : T.IsClosable) (hd : Dense (T.domain : Set E)) :
    T.adjoint ≤ T.closure.adjoint := by
  have hcd : Dense (T.closure.domain : Set E) := hd.mono (T.le_closure.1)
  -- for `y ∈ dom T†`, `⟪T†y, x⟫ = ⟪y, T̄ x⟫` on `dom T̄`
  have key : ∀ (y : T.adjoint.domain) (x : T.closure.domain),
      ⟪T.adjoint y, (x : E)⟫_ℂ = ⟪(y : E), T.closure x⟫_ℂ :=
    fun y x => by
    set S : Set (E × E) :=
      {p | ⟪T.adjoint y, p.1⟫_ℂ = ⟪(y : E), p.2⟫_ℂ}
    have hS : IsClosed S := isClosed_eq (by fun_prop) (by fun_prop)
    have hgr : (T.graph : Set _) ⊆ S := fun p hp => by
      obtain ⟨z, h1, h2⟩ := (LinearPMap.mem_graph_iff T).1 hp
      simp only [S, Set.mem_setOf_eq, ← h1, ← h2]
      exact LinearPMap.adjoint_isFormalAdjoint hd y z
    have hcl : ((x : E), T.closure x) ∈ T.closure.graph :=
      (LinearPMap.mem_graph_iff _).2 ⟨x, rfl, rfl⟩
    rw [← hT.graph_closure_eq_closure_graph] at hcl
    exact closure_minimal hgr hS hcl
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists _
    ⟨T.adjoint ⟨y, hy⟩, fun x => key ⟨y, hy⟩ x⟩, fun y z hyz => ?_⟩
  refine (LinearPMap.adjoint_apply_eq hcd z fun x => ?_).symm
  rw [← hyz]
  exact key y x

namespace IsGenerator

variable {A : E →ₗ.[ℂ] E} {U : ℝ → unitary (E →L[ℂ] E)} (hA : IsGenerator A U)
include hA

/-- `h ↦ U t (U h ψ)` has derivative `U t (-iAψ)` at `0`. -/
theorem hasDerivAt_apply_comp (ψ : A.domain) (t : ℝ) :
    HasDerivAt (fun h : ℝ => (U t : E →L[ℂ] E) ((U h : E →L[ℂ] E) ψ))
      ((U t : E →L[ℂ] E) (-(I • A ψ))) 0 :=
  (((U t : E →L[ℂ] E).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 (hA.hasDerivAt ψ)

/-- **Theorem 2(a).** `U t` maps `dom A` into itself. -/
theorem apply_mem_domain (ψ : A.domain) (t : ℝ) : (U t : E →L[ℂ] E) ψ ∈ A.domain := by
  have h := (hA.hasDerivAt_apply_comp ψ t).congr_of_eventuallyEq
    (Eventually.of_forall fun h => hA.isUnitaryGroup.comm_apply h t ψ)
  exact (hA.mem_domain_iff _).2 ⟨_, h⟩

/-- **Theorem 2(a).** `A U t ψ = U t A ψ`. -/
theorem apply_comm (ψ : A.domain) (t : ℝ) :
    A ⟨(U t : E →L[ℂ] E) ψ, hA.apply_mem_domain ψ t⟩ = (U t : E →L[ℂ] E) (A ψ) := by
  have h1 := hA.hasDerivAt ⟨(U t : E →L[ℂ] E) ψ, hA.apply_mem_domain ψ t⟩
  have h2 := (hA.hasDerivAt_apply_comp ψ t).congr_of_eventuallyEq
    (Eventually.of_forall fun h => hA.isUnitaryGroup.comm_apply h t ψ)
  have := h1.unique h2
  rw [map_neg, map_smul, neg_inj] at this
  exact smul_right_injective E I_ne_zero this

/-- **Theorem 2(a).** `t ↦ U t ψ` is differentiable with derivative `-i U t A ψ`. -/
theorem hasDerivAt_apply (ψ : A.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (U s : E →L[ℂ] E) ψ) (-(I • (U t : E →L[ℂ] E) (A ψ))) t := by
  have h0 : HasDerivAt (fun h : ℝ => (U t : E →L[ℂ] E) ((U h : E →L[ℂ] E) ψ))
      ((U t : E →L[ℂ] E) (-(I • A ψ))) (t - t) := by
    rw [sub_self]; exact hA.hasDerivAt_apply_comp ψ t
  have h := HasDerivAt.comp_sub_const t t h0
  rw [map_neg, map_smul] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only
  rw [hA.isUnitaryGroup.apply_apply, add_sub_cancel]

/-- **Theorem 2(b)**, symmetry: `⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`. -/
theorem inner_map_self (ψ φ : A.domain) : ⟪A ψ, (φ : E)⟫_ℂ = ⟪(ψ : E), A φ⟫_ℂ := by
  have h := (hA.hasDerivAt ψ).inner ℂ (hA.hasDerivAt φ)
  have hc : (fun t : ℝ => ⟪(U t : E →L[ℂ] E) ψ, (U t : E →L[ℂ] E) φ⟫_ℂ) =
      fun _ => ⟪(ψ : E), (φ : E)⟫_ℂ :=
    funext fun t => IsUnitaryGroup.inner_apply_apply t _ _
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const 0 _)
  simp only [hA.isUnitaryGroup.apply_zero, inner_neg_right, inner_neg_left, inner_smul_right,
    inner_smul_left, Complex.conj_I] at h0
  have : I * (⟪A ψ, (φ : E)⟫_ℂ - ⟪(ψ : E), A φ⟫_ℂ) = 0 := by linear_combination h0
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left I_ne_zero)

/-- The integral `∫₀^ε U s ψ ds` lies in `dom A`. -/
theorem integral_mem_domain (ψ : E) (ε : ℝ) :
    (∫ s in (0 : ℝ)..ε, (U s : E →L[ℂ] E) ψ) ∈ A.domain := by
  have hc := hA.isUnitaryGroup.continuous_apply ψ
  set G : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, (U s : E →L[ℂ] E) ψ with hG
  have hGd : ∀ x, HasDerivAt G ((U x : E →L[ℂ] E) ψ) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => (U s : E →L[ℂ] E) ψ) MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have key : ∀ h : ℝ, (U h : E →L[ℂ] E) (G ε) = G (h + ε) - G h := fun h => by
    simp only [hG]
    rw [← (U h : E →L[ℂ] E).intervalIntegral_comp_comm (hint 0 ε)]
    simp only [hA.isUnitaryGroup.apply_apply]
    rw [intervalIntegral.integral_comp_add_left (fun s => (U s : E →L[ℂ] E) ψ) h, add_zero,
      intervalIntegral.integral_interval_sub_left (hint 0 (h + ε)) (hint 0 h)]
  refine (hA.mem_domain_iff _).2 ⟨(U ε : E →L[ℂ] E) ψ - ψ, ?_⟩
  have hd : HasDerivAt (fun h => G (h + ε) - G h) ((U ε : E →L[ℂ] E) ψ - ψ) 0 := by
    have h1 := (hGd (0 + ε)).comp_add_const 0 ε
    have h2 := hGd 0
    rw [zero_add] at h1
    have := h1.sub h2
    rw [hA.isUnitaryGroup.apply_zero] at this
    exact this
  exact hd.congr_of_eventuallyEq (Eventually.of_forall key)

/-- **Theorem 2(b).** The domain of a generator is dense. -/
theorem dense_domain : Dense (A.domain : Set E) := by
  refine fun ψ => ?_
  have hc := hA.isUnitaryGroup.continuous_apply ψ
  set G : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, (U s : E →L[ℂ] E) ψ with hG
  have hd : HasDerivAt G ψ 0 := by
    have := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
    rwa [hA.isUnitaryGroup.apply_zero] at this
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, hG, intervalIntegral.integral_same, sub_zero] at ht
  refine mem_closure_of_tendsto ht (Eventually.of_forall fun t => ?_)
  exact A.domain.smul_mem _ (hA.integral_mem_domain ψ t)

/-- **Theorem 2(b).** A generator is closed. -/
theorem isClosed : A.IsClosed := by
  have hU := hA.isUnitaryGroup
  -- `U h ψ - ψ = ∫₀ʰ U s (-iAψ) ds` on `dom A`
  have hint : ∀ (z : E) (a b : ℝ),
      IntervalIntegrable (fun s => (U s : E →L[ℂ] E) z) MeasureTheory.volume a b :=
    fun z a b => (hU.continuous_apply z).intervalIntegrable a b
  have hftc : ∀ (ψ : A.domain) (h : ℝ),
      (U h : E →L[ℂ] E) ψ - ψ = ∫ s in (0 : ℝ)..h, (U s : E →L[ℂ] E) (-(I • A ψ)) := fun ψ h => by
    have hd : ∀ x, HasDerivAt (fun s : ℝ => (U s : E →L[ℂ] E) ψ)
        ((U x : E →L[ℂ] E) (-(I • A ψ))) x := fun x => by
      rw [map_neg, map_smul]; exact hA.hasDerivAt_apply ψ x
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := h)
      (fun x _ => hd x) (hint (-(I • A ψ)) 0 h)
    rw [this, hU.apply_zero]
  have hbound : ∀ (z : E) (h : ℝ), ‖∫ s in (0 : ℝ)..h, (U s : E →L[ℂ] E) z‖ ≤ ‖z‖ * |h - 0| :=
    fun z h => intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => by
      rw [IsUnitaryGroup.norm_apply]
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose x hx using fun n => (LinearPMap.mem_graph_iff A).1 (hq n)
  have h1 : Tendsto (fun n => ((x n : A.domain) : E)) atTop (𝓝 p.1) := by
    have : (fun n => ((x n : A.domain) : E)) = fun n => (q n).1 := funext fun n => (hx n).1
    rw [this]; exact (continuous_fst.tendsto p).comp hlim
  have h2 : Tendsto (fun n => A (x n)) atTop (𝓝 p.2) := by
    have : (fun n => A (x n)) = fun n => (q n).2 := funext fun n => (hx n).2
    rw [this]; exact (continuous_snd.tendsto p).comp hlim
  -- the limit relation
  have hrel : ∀ h : ℝ, (U h : E →L[ℂ] E) p.1 - p.1 =
      ∫ s in (0 : ℝ)..h, (U s : E →L[ℂ] E) (-(I • p.2)) := fun h => by
    have hl : Tendsto (fun n => (U h : E →L[ℂ] E) (x n) - (x n : E)) atTop
        (𝓝 ((U h : E →L[ℂ] E) p.1 - p.1)) :=
      (((U h : E →L[ℂ] E).continuous.tendsto _).comp h1).sub h1
    have hr : Tendsto (fun n => ∫ s in (0 : ℝ)..h, (U s : E →L[ℂ] E) (-(I • A (x n)))) atTop
        (𝓝 (∫ s in (0 : ℝ)..h, (U s : E →L[ℂ] E) (-(I • p.2)))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hz : Tendsto (fun n => ‖-(I • A (x n)) - -(I • p.2)‖ * |h - 0|) atTop (𝓝 (0 * |h - 0|)) :=
        ((tendsto_iff_norm_sub_tendsto_zero.1 ((h2.const_smul I).neg)).mul_const _)
      rw [zero_mul] at hz
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hz
      rw [← intervalIntegral.integral_sub (hint _ 0 h) (hint _ 0 h)]
      simp_rw [← map_sub]
      exact hbound _ h
    exact tendsto_nhds_unique (hl.congr fun n => hftc (x n) h) hr
  -- differentiate at `0`
  have hd : HasDerivAt (fun h : ℝ => (U h : E →L[ℂ] E) p.1) (-(I • p.2)) 0 := by
    have hc := hU.continuous_apply (-(I • p.2))
    have := ((hc.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add p.1
    rw [hU.apply_zero] at this
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)
    simp only
    rw [← hrel h]; abel
  have hmem : p.1 ∈ A.domain := (hA.mem_domain_iff _).2 ⟨_, hd⟩
  have hval : A ⟨p.1, hmem⟩ = p.2 := by
    have := (hA.hasDerivAt ⟨p.1, hmem⟩).unique hd
    rw [neg_inj] at this
    exact smul_right_injective E I_ne_zero this
  exact (LinearPMap.mem_graph_iff A).2 ⟨⟨p.1, hmem⟩, rfl, hval⟩

/-- **Theorem 2(b).** A generator is self-adjoint. -/
theorem isSelfAdjoint : IsSelfAdjoint A := by
  refine isSelfAdjoint_of_isClosed hA.dense_domain hA.isClosed hA.inner_map_self ?_
  intro s hs φ hφ
  refine hA.dense_domain.eq_zero_of_inner_left ℂ fun ψ hψ => ?_
  -- `g t = ⟪φ, U t ψ⟫` satisfies `g' = c g` with `c = ±1`
  set c : ℝ := if s = I then -1 else 1 with hcdef
  have hIne : (-I : ℂ) ≠ I := fun h => by
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have hcs : -I * (starRingEnd ℂ) s = (c : ℂ) := by
    rcases hs with rfl | rfl
    · simp [hcdef]
    · rw [hcdef, if_neg hIne]; simp
  have hc0 : c ≠ 0 := by rw [hcdef]; split_ifs <;> norm_num
  let g : ℝ → ℂ := fun t => ⟪(φ : E), (U t : E →L[ℂ] E) ψ⟫_ℂ
  have hg : ∀ t, HasDerivAt g (c * g t) t := fun t => by
    have h := (hasDerivAt_const t (φ : E)).inner ℂ (hA.hasDerivAt_apply ⟨ψ, hψ⟩ t)
    convert h using 1
    simp only [inner_zero_left, add_zero, inner_neg_right, inner_smul_right, g]
    rw [← hA.apply_comm ⟨ψ, hψ⟩ t, ← LinearPMap.adjoint_isFormalAdjoint hA.dense_domain φ, hφ,
      inner_smul_left, ← hcs]
    ring
  have hb : ∀ t, ‖g t‖ ≤ ‖(φ : E)‖ * ‖ψ‖ := fun t => by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [IsUnitaryGroup.norm_apply]
  have := eq_zero_of_hasDerivAt_mul_of_bounded hc0 hg hb
  simpa [g, hA.isUnitaryGroup.apply_zero] using this

/-- **Theorem 2(c).** Two groups with the same generator are equal. -/
theorem unique {V : ℝ → unitary (E →L[ℂ] E)} (hV : IsGenerator A V) : U = V := by
  funext t
  have hdense := hA.dense_domain
  -- `U t = V t` on `dom A`
  have hdom : ∀ ψ : A.domain, (U t : E →L[ℂ] E) ψ = (V t : E →L[ℂ] E) ψ := fun ψ => by
    refine sub_eq_zero.1 (hdense.eq_zero_of_inner_right ℂ fun χ hχ => ?_)
    -- `⟪V t φ, U t ψ⟫ = ⟪φ, ψ⟫` for `φ ∈ dom A`
    have hconst : ∀ φ : A.domain, ⟪(V t : E →L[ℂ] E) φ, (U t : E →L[ℂ] E) ψ⟫_ℂ = ⟪(φ : E), ψ⟫_ℂ :=
      fun φ => by
        let g : ℝ → ℂ := fun s => ⟪(V s : E →L[ℂ] E) φ, (U s : E →L[ℂ] E) ψ⟫_ℂ
        have hg : ∀ s, HasDerivAt g 0 s := fun s => by
          have h := (hV.hasDerivAt_apply φ s).inner ℂ (hA.hasDerivAt_apply ψ s)
          convert h using 1
          simp only [inner_neg_right, inner_smul_right, inner_neg_left, inner_smul_left,
            Complex.conj_I]
          rw [← hA.apply_comm ψ s, ← hV.apply_comm φ s,
            hA.inner_map_self ⟨_, hV.apply_mem_domain φ s⟩ ⟨_, hA.apply_mem_domain ψ s⟩]
          ring
        have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
          (fun s => (hg s).deriv) t 0
        simpa [g, hA.isUnitaryGroup.apply_zero, hV.isUnitaryGroup.apply_zero] using this
    have hχ' := hV.apply_mem_domain ⟨χ, hχ⟩ (-t)
    have h1 := hconst ⟨_, hχ'⟩
    simp only [hV.isUnitaryGroup.apply_apply_neg] at h1
    have h2 : ⟪χ, (V t : E →L[ℂ] E) ψ⟫_ℂ = ⟪(V (-t) : E →L[ℂ] E) χ, ψ⟫_ℂ := by
      rw [hV.isUnitaryGroup.inner_apply_left (-t) χ ψ, neg_neg]
    rw [inner_sub_right, h1, h2, sub_self]
  have : (U t : E →L[ℂ] E) = (V t : E →L[ℂ] E) := by
    refine ContinuousLinearMap.ext_on (s := (A.domain : Set E)) ?_ fun ψ hψ => hdom ⟨ψ, hψ⟩
    rwa [Submodule.span_eq]
  exact Subtype.ext this

end IsGenerator

/-- The generator of a strongly continuous one-parameter unitary group: the vectors at which
`t ↦ U t ψ` is differentiable at `0`, mapped to `i` times the derivative. -/
private noncomputable def generatorOf (U : ℝ → unitary (E →L[ℂ] E)) : E →ₗ.[ℂ] E where
  domain :=
    { carrier := {ψ | ∃ v, HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) v 0}
      add_mem' := fun ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v + w,
        (hv.add hw).congr_of_eventuallyEq (Eventually.of_forall fun t => by simp)⟩
      zero_mem' := ⟨0, (hasDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq
        (Eventually.of_forall fun t => by simp)⟩
      smul_mem' := fun c ψ ⟨v, hv⟩ => ⟨c • v,
        (hv.const_smul c).congr_of_eventuallyEq (Eventually.of_forall fun t => by simp)⟩ }
  toFun :=
    { toFun := fun ψ => I • deriv (fun t : ℝ => (U t : E →L[ℂ] E) ψ) 0
      map_add' := fun ψ φ => by
        obtain ⟨v, hv⟩ := ψ.2
        obtain ⟨w, hw⟩ := φ.2
        simp only [Submodule.coe_add, map_add]
        show I • deriv ((fun t : ℝ => (U t : E →L[ℂ] E) ψ) + fun t => (U t : E →L[ℂ] E) φ) 0 = _
        rw [deriv_add hv.differentiableAt hw.differentiableAt, smul_add]
      map_smul' := fun c ψ => by
        obtain ⟨v, hv⟩ := ψ.2
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply]
        show I • deriv (c • fun t : ℝ => (U t : E →L[ℂ] E) ψ) 0 = _
        rw [deriv_const_smul c hv.differentiableAt, smul_comm] }

private theorem isGenerator_generatorOf {U : ℝ → unitary (E →L[ℂ] E)} (hU : IsUnitaryGroup U) :
    IsGenerator (generatorOf U) U where
  isUnitaryGroup := hU
  mem_domain_iff := fun _ => Iff.rfl
  hasDerivAt := fun ψ => by
    obtain ⟨v, hv⟩ := ψ.2
    show HasDerivAt _ (-(I • I • deriv (fun t : ℝ => (U t : E →L[ℂ] E) ψ) 0)) 0
    rw [hv.deriv, smul_smul, I_mul_I, neg_one_smul, neg_neg]
    exact hv

/-- **Theorem 2(d).** Let `B` be self-adjoint with core `E₀`, and `V` a strongly continuous
one-parameter unitary group with derivative `-iBψ` at `0` for `ψ ∈ E₀`. Then `B` generates `V`. -/
theorem IsGenerator.of_core {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B) {E₀ : Submodule ℂ E}
    (hE₀ : E₀ ≤ B.domain) (hcore : (B.domRestrict E₀).closure = B)
    {V : ℝ → unitary (E →L[ℂ] E)} (hV : IsUnitaryGroup V)
    (hder : ∀ ψ : E₀, HasDerivAt (fun t : ℝ => (V t : E →L[ℂ] E) ψ)
      (-(I • B ⟨ψ, hE₀ ψ.2⟩)) 0) :
    IsGenerator B V := by
  have hC := isGenerator_generatorOf hV
  set C := generatorOf V
  -- `B|E₀ ≤ C`
  have hle0 : B.domRestrict E₀ ≤ C := by
    refine ⟨fun ψ hψ => (hC.mem_domain_iff ψ).2 ⟨_, hder ⟨ψ, hψ.1⟩⟩, fun x y hxy => ?_⟩
    have h1 := hC.hasDerivAt y
    have h2 := hder ⟨x, x.2.1⟩
    rw [← hxy] at h1
    have := h1.unique h2
    rw [neg_inj] at this
    exact (smul_right_injective E I_ne_zero this).symm
  have hBC : B ≤ C := hcore ▸ closure_le_of_isClosed hC.isClosed hle0
  have hBd : Dense (B.domain : Set E) := hB.dense_domain
  have hCC : C ≤ C.adjoint := (LinearPMap.isSelfAdjoint_def.1 hC.isSelfAdjoint).symm.le
  have hCB : C.adjoint ≤ B.adjoint := adjoint_le_adjoint hBd hBC
  have hBB : B.adjoint = B := hB
  have : C = B := le_antisymm (hCC.trans (hCB.trans hBB.le)) hBC
  rw [← this]
  exact hC

/-! ### Theorem 2(e): conjugation and constant shifts -/

/-- `Z* A Z` on `Z* dom A = {ψ : Zψ ∈ dom A}`. -/
noncomputable def unitaryConj (A : E →ₗ.[ℂ] E) (Z : unitary (E →L[ℂ] E)) : E →ₗ.[ℂ] E where
  domain := A.domain.comap (Z : E →L[ℂ] E).toLinearMap
  toFun := (star (Z : E →L[ℂ] E)).toLinearMap ∘ₗ A.toFun ∘ₗ
    ((Z : E →L[ℂ] E).toLinearMap.restrict fun _ hx => hx)

theorem unitaryConj_apply (A : E →ₗ.[ℂ] E) (Z : unitary (E →L[ℂ] E))
    (ψ : (unitaryConj A Z).domain) :
    unitaryConj A Z ψ = (star (Z : E →L[ℂ] E)) (A ⟨(Z : E →L[ℂ] E) ψ, ψ.2⟩) := rfl

/-- `A + c` on `dom A`, for real `c`. -/
def addConst (A : E →ₗ.[ℂ] E) (c : ℝ) : E →ₗ.[ℂ] E :=
  ⟨A.domain, A.toFun + (c : ℂ) • A.domain.subtype⟩

theorem addConst_apply (A : E →ₗ.[ℂ] E) (c : ℝ) (ψ : (addConst A c).domain) :
    addConst A c ψ = A ψ + (c : ℂ) • (ψ : E) := rfl

theorem exp_ofReal_mul_I_mem_unitary (c : ℝ) : Complex.exp (c * I) ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, RCLike.star_def, Complex.conj_mul', norm_exp_ofReal_mul_I]
  norm_num

/-- The scalar unitary `e^{ic}`. -/
noncomputable def phaseUnitary (c : ℝ) : unitary (E →L[ℂ] E) :=
  ⟨Complex.exp (c * I) • (1 : E →L[ℂ] E),
    Unitary.smul_mem_of_mem (exp_ofReal_mul_I_mem_unitary c) (one_mem _)⟩

theorem phaseUnitary_apply (c : ℝ) (ψ : E) :
    ((phaseUnitary c : unitary (E →L[ℂ] E)) : E →L[ℂ] E) ψ = Complex.exp (c * I) • ψ := rfl

/-- `s ↦ e^{isk}` has derivative `e^{itk} (ik)`. -/
theorem hasDerivAt_exp_mul_I (k t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((s * k : ℝ) : ℂ) * I))
      (Complex.exp (((t * k : ℝ) : ℂ) * I) * ((k : ℂ) * I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s * k : ℝ) : ℂ) * I) ((k : ℂ) * I) t := by
    have := ((hasDerivAt_id t).mul_const k).ofReal_comp.mul_const I
    simpa using this
  exact h1.cexp

namespace IsGenerator

variable {A : E →ₗ.[ℂ] E} {U : ℝ → unitary (E →L[ℂ] E)}

/-- **Theorem 2(e).** `Z* A Z` generates `Z* U t Z`. -/
theorem unitaryConj (hA : IsGenerator A U) (Z : unitary (E →L[ℂ] E)) :
    IsGenerator (BosonicLean.unitaryConj A Z) (fun t => star Z * U t * Z) := by
  have hU := hA.isUnitaryGroup
  have hZZ : ∀ ψ, (Z : E →L[ℂ] E) ((star (Z : E →L[ℂ] E)) ψ) = ψ := fun ψ => by
    show ((Z : E →L[ℂ] E) * star (Z : E →L[ℂ] E)) ψ = ψ
    rw [Unitary.mul_star_self_of_mem Z.2]; rfl
  have hSd : ∀ (ψ : E) (v : E),
      HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ((Z : E →L[ℂ] E) ψ)) v 0 →
      HasDerivAt (fun t : ℝ => ((star Z * U t * Z : unitary (E →L[ℂ] E)) : E →L[ℂ] E) ψ)
        ((star (Z : E →L[ℂ] E)) v) 0 := fun ψ v hv =>
    ((star (Z : E →L[ℂ] E)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
  refine ⟨⟨?_, fun s t => ?_, fun ψ => ?_⟩, fun ψ => ⟨fun hψ => ?_, fun ⟨v, hv⟩ => ?_⟩,
    fun ψ => ?_⟩
  · rw [hU.map_zero, mul_one, Unitary.star_mul_self]
  · ext ψ
    rw [hU.map_add]
    exact congrArg (fun x => (star (Z : E →L[ℂ] E)) x)
      (congrArg (fun x => (U s : E →L[ℂ] E) x)
        (hZZ ((U t : E →L[ℂ] E) ((Z : E →L[ℂ] E) ψ))).symm)
  · exact (star (Z : E →L[ℂ] E)).continuous.comp (hU.continuous_apply _)
  · obtain ⟨v, hv⟩ := (hA.mem_domain_iff _).1 hψ
    exact ⟨_, hSd ψ v hv⟩
  · show (Z : E →L[ℂ] E) ψ ∈ A.domain
    refine (hA.mem_domain_iff _).2 ⟨(Z : E →L[ℂ] E) v, ?_⟩
    have := ((Z : E →L[ℂ] E).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact (hZZ _).symm
  · have := hSd ψ _ (hA.hasDerivAt ⟨(Z : E →L[ℂ] E) ψ, ψ.2⟩)
    rw [map_neg, map_smul] at this
    exact this

/-- **Theorem 2(e).** `A + c` generates `e^{-itc} U t`. -/
theorem addConst (hA : IsGenerator A U) (c : ℝ) :
    IsGenerator (BosonicLean.addConst A c) (fun t => phaseUnitary (t * -c) * U t) := by
  have hU := hA.isUnitaryGroup
  have happ : ∀ (k t : ℝ) ψ, ((phaseUnitary (t * k) * U t : unitary (E →L[ℂ] E)) :
      E →L[ℂ] E) ψ = Complex.exp (((t * k : ℝ) : ℂ) * I) • (U t : E →L[ℂ] E) ψ :=
    fun _ _ _ => rfl
  -- `t ↦ e^{itk} U t ψ` has derivative `v + ik ψ` when `t ↦ U t ψ` has derivative `v`
  have hd : ∀ (k : ℝ) (ψ : E) (v : E), HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) v 0 →
      HasDerivAt (fun t : ℝ => Complex.exp (((t * k : ℝ) : ℂ) * I) • (U t : E →L[ℂ] E) ψ)
        (v + ((k : ℂ) * I) • ψ) 0 := fun k ψ v hv => by
    have := (hasDerivAt_exp_mul_I k 0).smul hv
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_smul, one_mul,
      hU.apply_zero] at this
    exact this
  refine ⟨⟨?_, fun s t => ?_, fun ψ => ?_⟩, fun ψ => ⟨fun hψ => ?_, fun ⟨v, hv⟩ => ?_⟩,
    fun ψ => ?_⟩
  · ext ψ
    rw [happ]
    simp [hU.apply_zero]
  · ext ψ
    show Complex.exp ((((s + t) * -c : ℝ) : ℂ) * I) • (U (s + t) : E →L[ℂ] E) ψ =
      Complex.exp (((s * -c : ℝ) : ℂ) * I) • (U s : E →L[ℂ] E)
        (Complex.exp (((t * -c : ℝ) : ℂ) * I) • (U t : E →L[ℂ] E) ψ)
    rw [map_smul, smul_smul, hU.apply_apply, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · exact (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_mul_I (-c) t).continuousAt).smul
      (hU.continuous_apply ψ)
  · obtain ⟨v, hv⟩ := (hA.mem_domain_iff _).1 hψ
    exact ⟨_, hd (-c) ψ v hv⟩
  · have h2 := (hasDerivAt_exp_mul_I c 0).smul hv
    refine (hA.mem_domain_iff _).2 ⟨_, h2.congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)⟩
    show (U t : E →L[ℂ] E) ψ = Complex.exp (((t * c : ℝ) : ℂ) * I) •
      Complex.exp (((t * -c : ℝ) : ℂ) * I) • (U t : E →L[ℂ] E) ψ
    rw [smul_smul, ← Complex.exp_add]
    push_cast
    rw [show (t : ℂ) * c * I + t * -c * I = 0 by ring, Complex.exp_zero, one_smul]
  · have := hd (-c) ψ _ (hA.hasDerivAt ψ)
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun t => happ (-c) t ψ)).congr_deriv ?_
    rw [addConst_apply]
    push_cast
    module

end IsGenerator

/-- The unitary `exp(-itT)` of a bounded self-adjoint `T`. -/
noncomputable def expUnitaryOfSelfAdjoint {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) (t : ℝ) :
    unitary (E →L[ℂ] E) :=
  ⟨NormedSpace.exp (t • (-(I • T))), by
    let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
    refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_
    rw [skewAdjoint.mem_iff, star_smul, star_neg, star_smul, hT.star_eq, Complex.star_def,
      Complex.conj_I, star_trivial, neg_smul, neg_neg, smul_neg, neg_neg]⟩

/-- **Theorem 2(f).** A bounded self-adjoint `T` generates `t ↦ exp(-itT)`. -/
theorem isGenerator_exp {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) :
    IsGenerator ((T : E →ₗ[ℂ] E).toPMap ⊤) (expUnitaryOfSelfAdjoint hT) := by
  set X : E →L[ℂ] E := -(I • T) with hX
  have hd : ∀ (t : ℝ) (ψ : E), HasDerivAt (fun s : ℝ =>
      ((expUnitaryOfSelfAdjoint hT s : unitary (E →L[ℂ] E)) : E →L[ℂ] E) ψ)
      ((NormedSpace.exp (t • X) * X) ψ) t := fun t ψ => by
    let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
    exact (((ContinuousLinearMap.apply ℂ E ψ).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t this
  have hmul : ∀ s t : ℝ, expUnitaryOfSelfAdjoint hT (s + t) =
      expUnitaryOfSelfAdjoint hT s * expUnitaryOfSelfAdjoint hT t := fun s t => by
    let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
    ext1
    show NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X)
    rw [add_smul, NormedSpace.exp_add_of_commute ((Commute.refl X).smul_left s |>.smul_right t)]
  refine ⟨⟨?_, hmul, fun ψ => continuous_iff_continuousAt.2 fun t => (hd t ψ).continuousAt⟩,
    fun ψ => ⟨fun _ => ⟨_, hd 0 ψ⟩, fun _ => trivial⟩, fun ψ => ?_⟩
  · ext1
    show NormedSpace.exp ((0 : ℝ) • X) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  · have := hd 0 ψ
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    convert this using 1
    simp [hX]
    rfl


/-! ### Theorem 3: analytic vectors with a common radius

The local operators `V t = ∑ (-it)ⁿ Aⁿ / n!` on `E₀`, `|t| ≤ ρ`, extend to isometries of `E` with
`V s V t = V (s + t)` for `|s| + |t| ≤ ρ`; the global group is `U t = V (t / m) ^ m`.
-/

/-- The operator `A : E₀ → E₀` on the subspace `E₀`, as an operator on `E`. -/
def onSubspace (E₀ : Submodule ℂ E) (A : E₀ →ₗ[ℂ] E₀) : E →ₗ.[ℂ] E :=
  ⟨E₀, E₀.subtype ∘ₗ A⟩

/-! ### Scalar series -/

/-- `∑_{m + n = k} uᵐ/m! vⁿ/n! = (u + v)ᵏ/k!`. -/
theorem sum_antidiagonal_pow_div_factorial {K : Type*} [Field K] [CharZero K] (u v : K) (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, u ^ p.1 / (p.1.factorial : K) * (v ^ p.2 / (p.2.factorial : K)) =
      (u + v) ^ k / (k.factorial : K) := by
  rw [(Commute.all u v).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  subst hp
  rw [nsmul_eq_mul, Nat.cast_choose K (Nat.le_add_right p.1 p.2), Nat.add_sub_cancel_left]
  have h1 : (p.1.factorial : K) ≠ 0 := by exact_mod_cast p.1.factorial_ne_zero
  have h2 : (p.2.factorial : K) ≠ 0 := by exact_mod_cast p.2.factorial_ne_zero
  have h3 : ((p.1 + p.2).factorial : K) ≠ 0 := by exact_mod_cast (p.1 + p.2).factorial_ne_zero
  field_simp

/-- A series on `ℕ × ℕ` summed along the antidiagonals. -/
theorem HasSum.sum_antidiagonal {X : Type*} [NormedAddCommGroup X] {F : ℕ × ℕ → X} {s : X}
    (h : HasSum F s) : HasSum (fun k => ∑ p ∈ Finset.antidiagonal k, F p) s := by
  have h' := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := F)).2 h
  refine h'.sigma fun k => ?_
  have := hasSum_fintype (fun c : Finset.antidiagonal k => F c.1)
  rwa [Finset.sum_coe_sort (Finset.antidiagonal k) F] at this

/-- A nonnegative family on `ℕ × ℕ` with summable antidiagonal sums is summable. -/
private theorem summable_of_summable_sum_antidiagonal {F : ℕ × ℕ → ℝ} (hF : ∀ p, 0 ≤ F p)
    (h : Summable fun k => ∑ p ∈ Finset.antidiagonal k, F p) : Summable F := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  refine (summable_sigma_of_nonneg fun _ => hF _).2 ⟨fun k => Summable.of_finite, ?_⟩
  convert h using 2 with k
  rw [tsum_fintype]
  exact Finset.sum_coe_sort (Finset.antidiagonal k) F

/-- The coefficient `(-it)ⁿ/n!`. -/
noncomputable def expCoeff (t : ℝ) (n : ℕ) : ℂ := (-(t : ℂ) * I) ^ n / (n.factorial : ℂ)

theorem norm_expCoeff (t : ℝ) (n : ℕ) : ‖expCoeff t n‖ = |t| ^ n / n.factorial := by
  simp [expCoeff]

private theorem star_expCoeff (t : ℝ) (n : ℕ) : starRingEnd ℂ (expCoeff t n) = expCoeff (-t) n := by
  simp [expCoeff, map_div₀, map_pow]

private theorem sum_expCoeff_mul (t s : ℝ) (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, expCoeff t p.1 * expCoeff s p.2 = expCoeff (t + s) k := by
  simp only [expCoeff]
  rw [sum_antidiagonal_pow_div_factorial]
  congr 2
  push_cast
  ring

private theorem expCoeff_zero_left (n : ℕ) : expCoeff 0 n = if n = 0 then 1 else 0 := by
  rcases n with _ | n <;> simp [expCoeff]

omit [CompleteSpace E] in
/-- `⟪∑ fₘ, w⟫ = ∑ ⟪fₘ, w⟫`. -/
private theorem hasSum_inner_left {ι : Type*} {f : ι → E} {a : E} (hf : HasSum f a) (w : E) :
    HasSum (fun m => ⟪f m, w⟫_ℂ) ⟪a, w⟫_ℂ := by
  have := (hf.mapL (innerSL ℂ w)).star
  simpa [innerSL_apply_apply, inner_conj_symm] using this

/-! ### The exponential series on `E₀` -/

section Series

variable {E₀ : Submodule ℂ E} {A : E₀ →ₗ[ℂ] E₀}

/-- The term `(-it)ⁿ/n! • Aⁿx` of the exponential series. -/
private noncomputable def expTerm (A : E₀ →ₗ[ℂ] E₀) (t : ℝ) (x : E₀) (n : ℕ) : E :=
  expCoeff t n • ((A ^ n) x : E)

omit [CompleteSpace E] in
private theorem norm_expTerm (t : ℝ) (x : E₀) (n : ℕ) :
    ‖expTerm A t x n‖ = |t| ^ n / n.factorial * ‖((A ^ n) x : E)‖ := by
  rw [expTerm, norm_smul, norm_expCoeff]

omit [CompleteSpace E] in
private theorem expTerm_add (t : ℝ) (x y : E₀) (n : ℕ) :
    expTerm A t (x + y) n = expTerm A t x n + expTerm A t y n := by
  simp [expTerm, smul_add]

omit [CompleteSpace E] in
private theorem expTerm_smul (t : ℝ) (c : ℂ) (x : E₀) (n : ℕ) :
    expTerm A t (c • x) n = c • expTerm A t x n := by
  simp [expTerm, smul_comm c]

open Classical in
/-- The exponential series `x ↦ ∑ (-it)ⁿ/n! Aⁿx`, as a linear map `E₀ → E` when it converges on all
of `E₀` (and `0` otherwise). -/
private noncomputable def seriesMap (A : E₀ →ₗ[ℂ] E₀) (t : ℝ) : E₀ →ₗ[ℂ] E :=
  if h : ∀ x, Summable (expTerm A t x) then
    { toFun := fun x => ∑' n, expTerm A t x n
      map_add' := fun x y => by
        simp only [expTerm_add]
        exact (h x).tsum_add (h y)
      map_smul' := fun c x => by
        simp only [expTerm_smul, RingHom.id_apply]
        exact (h x).tsum_const_smul c }
  else 0

omit [CompleteSpace E] in
private theorem hasSum_seriesMap {t : ℝ} (h : ∀ x, Summable (expTerm A t x)) (x : E₀) :
    HasSum (expTerm A t x) (seriesMap A t x) := by
  rw [seriesMap, dite_eq_left h]
  exact (h x).hasSum

omit [CompleteSpace E] in
/-- `⟪Aᵐx, Aⁿy⟫ = ⟪x, Aᵐ⁺ⁿy⟫` for symmetric `A`. -/
private theorem inner_pow_apply_pow_apply
    (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ) (m n : ℕ) (x y : E₀) :
    ⟪((A ^ m) x : E), ((A ^ n) y : E)⟫_ℂ = ⟪(x : E), ((A ^ (m + n)) y : E)⟫_ℂ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, pow_succ, Module.End.mul_apply, ih, hA,
      ← Module.End.mul_apply, ← pow_succ']

variable {ρ : ℝ} (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖)
include han

omit [CompleteSpace E] in
private theorem summable_norm_expTerm {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) :
    Summable fun n => ‖expTerm A t x n‖ :=
  (han x).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    rw [norm_expTerm]
    gcongr

private theorem summable_expTerm {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) : Summable (expTerm A t x) :=
  (summable_norm_expTerm han ht x).of_norm

private theorem hasSum_seriesMap_of_le {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) :
    HasSum (expTerm A t x) (seriesMap A t x) :=
  hasSum_seriesMap (fun y => summable_expTerm han ht y) x

/-- The exponential series is isometric on `E₀`: `⟪V t x, V t y⟫ = ⟪x, y⟫`. -/
private theorem inner_seriesMap (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ)
    {t : ℝ} (ht : |t| ≤ ρ) (x y : E₀) :
    ⟪seriesMap A t x, seriesMap A t y⟫_ℂ = ⟪(x : E), (y : E)⟫_ℂ := by
  have hx := hasSum_seriesMap_of_le han ht x
  have hy := hasSum_seriesMap_of_le han ht y
  set F : ℕ × ℕ → ℂ := fun p => ⟪expTerm A t x p.1, expTerm A t y p.2⟫_ℂ with hF
  have hFs : Summable F := by
    refine Summable.of_norm_bounded ((summable_norm_expTerm han ht x).mul_of_nonneg
      (summable_norm_expTerm han ht y) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      fun p => norm_inner_le_norm _ _
  obtain ⟨σ, hσ⟩ := hFs
  have h1 : HasSum (fun m => ⟪expTerm A t x m, seriesMap A t y⟫_ℂ) σ :=
    hσ.prod_fiberwise fun m => by
      simpa [innerSL_apply_apply] using hy.mapL (innerSL ℂ (expTerm A t x m))
  have h2 := hasSum_inner_left hx (seriesMap A t y)
  rw [h2.unique h1]
  have h3 := HasSum.sum_antidiagonal hσ
  have h4 : (fun k => ∑ p ∈ Finset.antidiagonal k, F p) =
      fun k => if k = 0 then ⟪(x : E), (y : E)⟫_ℂ else 0 := by
    funext k
    have : ∀ p ∈ Finset.antidiagonal k, F p =
        (expCoeff (-t) p.1 * expCoeff t p.2) * ⟪(x : E), ((A ^ k) y : E)⟫_ℂ := fun p hp => by
      rw [Finset.mem_antidiagonal] at hp
      simp only [hF, expTerm, inner_smul_left, inner_smul_right, star_expCoeff,
        inner_pow_apply_pow_apply hA, hp]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_expCoeff_mul, neg_add_cancel,
      expCoeff_zero_left]
    split_ifs with hk
    · subst hk; simp
    · simp
  rw [h4] at h3
  exact h3.unique (hasSum_ite_eq 0 _)

private theorem norm_seriesMap (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ)
    {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) : ‖seriesMap A t x‖ = ‖(x : E)‖ := by
  have h := inner_seriesMap han hA ht x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖seriesMap A t x‖ ^ 2 = ‖(x : E)‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'

end Series

/-! ### The local operators -/

section Local

variable {E₀ : Submodule ℂ E} {A : E₀ →ₗ[ℂ] E₀}

/-- The local operator `V t` on `E`: the extension of the exponential series from `E₀`. -/
private noncomputable def localOp (A : E₀ →ₗ[ℂ] E₀) (t : ℝ) : E →L[ℂ] E :=
  (seriesMap A t).extendOfNorm E₀.subtype

open Classical in
/-- `V t` as a unitary (and `1` when `V t` is not unitary). -/
private noncomputable def localUnitary (A : E₀ →ₗ[ℂ] E₀) (t : ℝ) : unitary (E →L[ℂ] E) :=
  if h : localOp A t ∈ unitary (E →L[ℂ] E) then ⟨localOp A t, h⟩ else 1

omit [CompleteSpace E] in
/-- Two bounded operators that agree on a dense subspace are equal. -/
private theorem ext_of_dense (hE₀ : Dense (E₀ : Set E)) {f g : E →L[ℂ] E} (h : ∀ x : E₀, f x = g x) :
    f = g :=
  ContinuousLinearMap.ext_on (s := (E₀ : Set E)) (by rwa [Submodule.span_eq])
    fun x hx => h ⟨x, hx⟩

variable {ρ : ℝ} (hE₀ : Dense (E₀ : Set E))
  (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ) (hρ : 0 < ρ)
  (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖)
include hE₀ hA hρ han

private theorem localOp_apply {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) : localOp A t x = seriesMap A t x :=
  LinearMap.extendOfNorm_eq (e := E₀.subtype) hE₀.denseRange_val
    ⟨1, fun y => by simp [norm_seriesMap han hA ht]⟩ x

private theorem hasSum_localOp {t : ℝ} (ht : |t| ≤ ρ) (x : E₀) :
    HasSum (expTerm A t x) (localOp A t x) := by
  rw [localOp_apply hE₀ hA hρ han ht]
  exact hasSum_seriesMap_of_le han ht x

private theorem norm_localOp {t : ℝ} (ht : |t| ≤ ρ) (ψ : E) : ‖localOp A t ψ‖ = ‖ψ‖ := by
  refine hE₀.denseRange_val.induction_on (p := fun ψ => ‖localOp A t ψ‖ = ‖ψ‖) ψ
    (isClosed_eq (localOp A t).continuous.norm continuous_norm) fun x => ?_
  rw [localOp_apply hE₀ hA hρ han ht, norm_seriesMap han hA ht]

private theorem localOp_zero : localOp A 0 = 1 := by
  refine ext_of_dense hE₀ fun x => ?_
  have h := hasSum_localOp hE₀ hA hρ han (t := 0) (by simpa using hρ.le) x
  have h0 : ∀ n ≠ 0, expTerm A 0 x n = 0 := fun n hn => by
    simp [expTerm, expCoeff_zero_left, hn]
  have h2 := hasSum_single 0 h0
  have h3 : expTerm A 0 x 0 = x := by simp [expTerm, expCoeff_zero_left]
  rw [h3] at h2
  exact h.unique h2

/-- **The local group law** on `E₀`: `V s (V t x) = V (s + t) x` for `|s| + |t| ≤ ρ`. -/
private theorem localOp_apply_localOp {s t : ℝ} (hst : |s| + |t| ≤ ρ) (x : E₀) :
    localOp A s (localOp A t x) = localOp A (s + t) x := by
  have hs : |s| ≤ ρ := by linarith [abs_nonneg t]
  have ht : |t| ≤ ρ := by linarith [abs_nonneg s]
  have hst' : |s + t| ≤ ρ := (abs_add_le s t).trans hst
  have h1 := (hasSum_localOp hE₀ hA hρ han ht x).mapL (localOp A s)
  set F : ℕ × ℕ → E :=
    fun p => (expCoeff t p.1 * expCoeff s p.2) • ((A ^ (p.1 + p.2)) x : E) with hF
  have hfib : ∀ m, HasSum (fun n => F (m, n)) (localOp A s (expTerm A t x m)) := fun m => by
    have := (hasSum_localOp hE₀ hA hρ han hs ((A ^ m) x)).const_smul (expCoeff t m)
    rw [expTerm, map_smul]
    convert this using 1
    funext n
    show (expCoeff t m * expCoeff s n) • ((A ^ (m + n)) x : E) =
      expCoeff t m • (expCoeff s n • ((A ^ n) ((A ^ m) x) : E))
    rw [smul_smul, add_comm m n, pow_add, Module.End.mul_apply]
  have hG : Summable fun p : ℕ × ℕ => |t| ^ p.1 / p.1.factorial * (|s| ^ p.2 / p.2.factorial) *
      ‖((A ^ (p.1 + p.2)) x : E)‖ := by
    refine summable_of_summable_sum_antidiagonal (fun p => by positivity) ?_
    refine (han x).of_nonneg_of_le (fun k => Finset.sum_nonneg fun p _ => by positivity)
      fun k => ?_
    have : ∀ p ∈ Finset.antidiagonal k, |t| ^ p.1 / p.1.factorial * (|s| ^ p.2 / p.2.factorial) *
        ‖((A ^ (p.1 + p.2)) x : E)‖ =
        |t| ^ p.1 / p.1.factorial * (|s| ^ p.2 / p.2.factorial) * ‖((A ^ k) x : E)‖ :=
      fun p hp => by rw [Finset.mem_antidiagonal.1 hp]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_antidiagonal_pow_div_factorial]
    gcongr
    linarith
  have hFs : Summable F := hG.of_norm_bounded fun p => by
    rw [hF]
    simp only
    rw [norm_smul, norm_mul, norm_expCoeff, norm_expCoeff]
  obtain ⟨σ, hσ⟩ := hFs
  have h2 := hσ.prod_fiberwise hfib
  have h3 := HasSum.sum_antidiagonal hσ
  have h4 : (fun k => ∑ p ∈ Finset.antidiagonal k, F p) = expTerm A (s + t) x := by
    funext k
    have : ∀ p ∈ Finset.antidiagonal k,
        F p = (expCoeff t p.1 * expCoeff s p.2) • ((A ^ k) x : E) := fun p hp => by
      rw [hF]
      simp only
      rw [Finset.mem_antidiagonal.1 hp]
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul, sum_expCoeff_mul, add_comm t s]
    rfl
  rw [h4] at h3
  rw [h1.unique h2]
  exact h3.unique (hasSum_localOp hE₀ hA hρ han hst' x)

private theorem localOp_mul {s t : ℝ} (hst : |s| + |t| ≤ ρ) :
    localOp A s * localOp A t = localOp A (s + t) :=
  ext_of_dense hE₀ fun x => by
    exact localOp_apply_localOp hE₀ hA hρ han hst x

private theorem localOp_mem_unitary {a : ℝ} (ha : |a| ≤ ρ / 2) : localOp A a ∈ unitary (E →L[ℂ] E) := by
  have h2a : |a| + |-a| ≤ ρ := by rw [abs_neg]; linarith
  have h2a' : |-a| + |a| ≤ ρ := by rw [abs_neg]; linarith
  have h1 : localOp A a * localOp A (-a) = 1 := by
    rw [localOp_mul hE₀ hA hρ han h2a, add_neg_cancel, localOp_zero hE₀ hA hρ han]
  have h2 : localOp A (-a) * localOp A a = 1 := by
    rw [localOp_mul hE₀ hA hρ han h2a', neg_add_cancel, localOp_zero hE₀ hA hρ han]
  have h3 : star (localOp A a) * localOp A a = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1
      (norm_localOp hE₀ hA hρ han (by linarith))
  exact (IsUnit.mem_unitary_iff_star_mul_self ⟨⟨_, _, h1, h2⟩, rfl⟩).2 h3

private theorem coe_localUnitary {a : ℝ} (ha : |a| ≤ ρ / 2) :
    (localUnitary A a : E →L[ℂ] E) = localOp A a := by
  rw [localUnitary, dite_eq_left (localOp_mem_unitary hE₀ hA hρ han ha)]

private theorem localUnitary_zero : localUnitary A 0 = 1 := by
  apply Subtype.ext
  rw [coe_localUnitary hE₀ hA hρ han (by rw [abs_zero]; positivity), localOp_zero hE₀ hA hρ han]
  rfl

private theorem localUnitary_mul {a b : ℝ} (ha : |a| ≤ ρ / 2) (hb : |b| ≤ ρ / 2) (hab : |a + b| ≤ ρ / 2) :
    localUnitary A a * localUnitary A b = localUnitary A (a + b) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, coe_localUnitary hE₀ hA hρ han ha, coe_localUnitary hE₀ hA hρ han hb,
    coe_localUnitary hE₀ hA hρ han hab, localOp_mul hE₀ hA hρ han (by linarith)]

private theorem localUnitary_pow (k : ℕ) {a : ℝ} (ha : k * |a| ≤ ρ / 2) :
    localUnitary A a ^ k = localUnitary A (k * a) := by
  induction k with
  | zero => simp [localUnitary_zero hE₀ hA hρ han]
  | succ k ih =>
    push_cast at ha
    have h0 : 0 ≤ |a| := abs_nonneg a
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (k : ℝ) * |a| ≤ ρ / 2 := by nlinarith
    rw [pow_succ, ih h1, localUnitary_mul hE₀ hA hρ han]
    · congr 1; push_cast; ring
    · rw [abs_mul, abs_of_nonneg hk]; exact h1
    · nlinarith
    · rw [show (k : ℝ) * a + a = (k + 1) * a by ring, abs_mul, abs_of_nonneg (by linarith)]
      exact ha

private theorem localUnitary_div_pow {t : ℝ} {m : ℕ} (m' : ℕ) (hm : 0 < m) (hm' : 0 < m')
    (h : |t| / m ≤ ρ / 2) :
    localUnitary A (t / m) ^ m = localUnitary A (t / ((m * m' : ℕ) : ℝ)) ^ (m * m') := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hmr' : (0 : ℝ) < m' := Nat.cast_pos.2 hm'
  have hstep : localUnitary A (t / m) = localUnitary A (t / ((m * m' : ℕ) : ℝ)) ^ m' := by
    rw [localUnitary_pow hE₀ hA hρ han m']
    · congr 1; push_cast; field_simp
    · rw [abs_div, Nat.abs_cast]
      push_cast
      calc (m' : ℝ) * (|t| / (m * m')) = |t| / m := by field_simp
        _ ≤ ρ / 2 := h
  rw [hstep, ← pow_mul, mul_comm m' m]

end Local

/-! ### The global group -/

section Global

variable {E₀ : Submodule ℂ E} {A : E₀ →ₗ[ℂ] E₀}

/-- The number of steps `m = ⌈2|t|/ρ⌉ + 1`, so that `|t|/m ≤ ρ/2`. -/
private noncomputable def numSteps (ρ t : ℝ) : ℕ := ⌈2 * |t| / ρ⌉₊ + 1

/-- The global group `U t = V (t/m)ᵐ`, `m = numSteps ρ t`. -/
private noncomputable def globalUnitary (A : E₀ →ₗ[ℂ] E₀) (ρ t : ℝ) : unitary (E →L[ℂ] E) :=
  localUnitary A (t / numSteps ρ t) ^ numSteps ρ t

private theorem abs_div_numSteps_le {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) : |t| / numSteps ρ t ≤ ρ / 2 := by
  have hm : (0 : ℝ) < numSteps ρ t := by unfold numSteps; positivity
  have h := Nat.le_ceil (2 * |t| / ρ)
  rw [div_le_iff₀ hρ] at h
  rw [div_le_iff₀ hm]
  unfold numSteps
  push_cast
  nlinarith [abs_nonneg t]

variable {ρ : ℝ} (hE₀ : Dense (E₀ : Set E))
  (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ) (hρ : 0 < ρ)
  (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖)
include hE₀ hA hρ han

/-- `U t = V (t/m)ᵐ` for every `m ≥ 1` with `|t|/m ≤ ρ/2`. -/
private theorem globalUnitary_eq {t : ℝ} {m : ℕ} (hm : 0 < m) (h : |t| / m ≤ ρ / 2) :
    globalUnitary A ρ t = localUnitary A (t / m) ^ m := by
  have hn : 0 < numSteps ρ t := Nat.succ_pos _
  rw [globalUnitary, localUnitary_div_pow hE₀ hA hρ han (m := numSteps ρ t) m hn hm
    (abs_div_numSteps_le hρ t), localUnitary_div_pow hE₀ hA hρ han (m := m) (numSteps ρ t) hm
    hn h, mul_comm (numSteps ρ t) m]

private theorem globalUnitary_zero : globalUnitary A ρ 0 = 1 := by
  rw [globalUnitary_eq hE₀ hA hρ han (m := 1) one_pos (by simp; positivity)]
  simp [localUnitary_zero hE₀ hA hρ han]

private theorem globalUnitary_add (s t : ℝ) :
    globalUnitary A ρ (s + t) = globalUnitary A ρ s * globalUnitary A ρ t := by
  obtain ⟨m, hm, h⟩ : ∃ m : ℕ, 0 < m ∧ (|s| + |t|) / m ≤ ρ / 2 := by
    refine ⟨numSteps ρ (|s| + |t|), Nat.succ_pos _, ?_⟩
    have := abs_div_numSteps_le hρ (|s| + |t|)
    rwa [abs_of_nonneg (by positivity)] at this
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hs : |s| / m ≤ ρ / 2 := le_trans (by gcongr; linarith [abs_nonneg t]) h
  have ht : |t| / m ≤ ρ / 2 := le_trans (by gcongr; linarith [abs_nonneg s]) h
  have hst : |s + t| / m ≤ ρ / 2 := le_trans (by gcongr; exact abs_add_le s t) h
  have habs : ∀ r : ℝ, |r / m| = |r| / m := fun r => by rw [abs_div, Nat.abs_cast]
  rw [globalUnitary_eq hE₀ hA hρ han hm hst, globalUnitary_eq hE₀ hA hρ han hm hs,
    globalUnitary_eq hE₀ hA hρ han hm ht, add_div]
  have hst' : |s / m + t / m| ≤ ρ / 2 := by rw [← add_div, habs]; exact hst
  have hts' : |t / m + s / m| ≤ ρ / 2 := by rw [add_comm]; exact hst'
  rw [← localUnitary_mul hE₀ hA hρ han (by rw [habs]; exact hs) (by rw [habs]; exact ht) hst']
  refine Commute.mul_pow ?_ m
  rw [Commute, SemiconjBy, localUnitary_mul hE₀ hA hρ han (by rw [habs]; exact hs)
    (by rw [habs]; exact ht) hst', localUnitary_mul hE₀ hA hρ han (by rw [habs]; exact ht)
    (by rw [habs]; exact hs) hts', add_comm]

/-- `U t = V t` for `|t| ≤ ρ`. -/
private theorem coe_globalUnitary {t : ℝ} (ht : |t| ≤ ρ) :
    (globalUnitary A ρ t : E →L[ℂ] E) = localOp A t := by
  have h2 : |t / 2| ≤ ρ / 2 := by rw [abs_div, abs_two]; linarith
  rw [globalUnitary_eq hE₀ hA hρ han (m := 2) two_pos (by push_cast; linarith),
    SubmonoidClass.coe_pow, coe_localUnitary hE₀ hA hρ han (by push_cast; exact h2), pow_two,
    localOp_mul hE₀ hA hρ han (by push_cast; linarith)]
  congr 1
  push_cast
  ring

private theorem globalUnitary_zero_apply (ψ : E) : (globalUnitary A ρ 0 : E →L[ℂ] E) ψ = ψ := by
  rw [globalUnitary_zero hE₀ hA hρ han]
  rfl

/-- On `E₀`, `t ↦ U t x` has derivative `-iAx` at `0`. -/
private theorem hasDerivAt_globalUnitary (x : E₀) :
    HasDerivAt (fun t => (globalUnitary A ρ t : E →L[ℂ] E) x) (-(I • (A x : E))) 0 := by
  set M := ∑' n : ℕ, ρ ^ (n + 2) / (n + 2).factorial * ‖((A ^ (n + 2)) x : E)‖ with hM
  have hbound : ∀ t : ℝ, |t| ≤ ρ → ‖(globalUnitary A ρ t : E →L[ℂ] E) x - x -
      t • (-(I • (A x : E)))‖ ≤ M / ρ ^ 2 * ‖t ^ 2‖ := by
    intro t ht
    rw [coe_globalUnitary hE₀ hA hρ han ht]
    have h := hasSum_localOp hE₀ hA hρ han ht x
    rw [← hasSum_nat_add_iff' 2] at h
    have hr : ∑ i ∈ Finset.range 2, expTerm A t x i = (x : E) + t • (-(I • (A x : E))) := by
      simp [Finset.sum_range_succ, expTerm, expCoeff]
      rw [mul_smul, Complex.coe_smul]
    have hg : HasSum (fun n : ℕ => t ^ 2 / ρ ^ 2 *
        (ρ ^ (n + 2) / (n + 2).factorial * ‖((A ^ (n + 2)) x : E)‖)) (t ^ 2 / ρ ^ 2 * M) :=
      ((summable_nat_add_iff 2).2 (han x)).hasSum.mul_left _
    have := h.norm_le_of_bounded hg fun n => by
      rw [norm_expTerm]
      have hp : |t| ^ (n + 2) ≤ t ^ 2 * ρ ^ n := by
        rw [pow_add, sq_abs, mul_comm]
        gcongr
      have he : t ^ 2 / ρ ^ 2 * (ρ ^ (n + 2) / (n + 2).factorial * ‖((A ^ (n + 2)) x : E)‖) =
          t ^ 2 * ρ ^ n / (n + 2).factorial * ‖((A ^ (n + 2)) x : E)‖ := by
        field_simp
        ring
      rw [he]
      gcongr
    rw [hr, ← sub_sub] at this
    rw [norm_pow, Real.norm_eq_abs, sq_abs]
    calc _ ≤ t ^ 2 / ρ ^ 2 * M := this
      _ = M / ρ ^ 2 * t ^ 2 := by ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, globalUnitary_zero_apply hE₀ hA hρ han]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (M / ρ ^ 2) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hρ] with h hh
  exact hbound h (by simpa [Real.dist_eq] using hh)

private theorem tendsto_globalUnitary_zero (ψ : E) :
    Tendsto (fun t => (globalUnitary A ρ t : E →L[ℂ] E) ψ) (𝓝 0) (𝓝 ψ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx, hxψ⟩ := hE₀.exists_dist_lt ψ (by positivity : (0 : ℝ) < ε / 3)
  have hc := (hasDerivAt_globalUnitary hE₀ hA hρ han ⟨x, hx⟩).continuousAt
  rw [ContinuousAt, globalUnitary_zero_apply hE₀ hA hρ han] at hc
  filter_upwards [Metric.tendsto_nhds.1 hc (ε / 3) (by positivity)] with t ht
  have h1 : dist ((globalUnitary A ρ t : E →L[ℂ] E) ψ) ((globalUnitary A ρ t : E →L[ℂ] E) x) =
      dist ψ x := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, Unitary.norm_map]
  have h2 : dist ((globalUnitary A ρ t : E →L[ℂ] E) x) x < ε / 3 := ht
  have h3 : dist x ψ < ε / 3 := by rw [dist_comm]; exact hxψ
  linarith [dist_triangle4 ((globalUnitary A ρ t : E →L[ℂ] E) ψ)
    ((globalUnitary A ρ t : E →L[ℂ] E) x) x ψ]

/-- `U` is a strongly continuous one-parameter unitary group. -/
private theorem isUnitaryGroup_globalUnitary : IsUnitaryGroup (globalUnitary A ρ) where
  map_zero := globalUnitary_zero hE₀ hA hρ han
  map_add := globalUnitary_add hE₀ hA hρ han
  continuous_apply ψ := continuous_iff_continuousAt.2 fun t₀ => by
    have h1 : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 0) := by
      have := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at this
    have h2 := ((globalUnitary A ρ t₀ : E →L[ℂ] E).continuous.tendsto ψ).comp
      ((tendsto_globalUnitary_zero hE₀ hA hρ han ψ).comp h1)
    refine h2.congr fun t => ?_
    have := congrArg (fun u : unitary (E →L[ℂ] E) => (u : E →L[ℂ] E) ψ)
      (globalUnitary_add hE₀ hA hρ han t₀ (t - t₀))
    simp only [add_sub_cancel] at this
    rw [this]
    rfl

end Global

/-! ### Self-adjointness of the closure and the generator -/

section Closure

variable {E₀ : Submodule ℂ E} {A : E₀ →ₗ[ℂ] E₀}

omit [CompleteSpace E] in
theorem closure_onSubspace_apply (x : E₀) (hx : (x : E) ∈ (onSubspace E₀ A).closure.domain) :
    (onSubspace E₀ A).closure ⟨x, hx⟩ = (A x : E) :=
  ((LinearPMap.le_closure (onSubspace E₀ A)).2 (x := x) (y := ⟨x, hx⟩) rfl).symm

omit [CompleteSpace E] in
theorem dense_closure_domain (hE₀ : Dense (E₀ : Set E)) :
    Dense ((onSubspace E₀ A).closure.domain : Set E) :=
  hE₀.mono (LinearPMap.le_closure _).1

variable (hE₀ : Dense (E₀ : Set E))
  (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ)

include hE₀ hA in
theorem onSubspace_le_adjoint : onSubspace E₀ A ≤ (onSubspace E₀ A).adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hE₀ fun x y => hA x y

include hE₀ hA in
theorem isClosable_onSubspace : (onSubspace E₀ A).IsClosable :=
  (LinearPMap.adjoint_isClosed hE₀).isClosable.leIsClosable (onSubspace_le_adjoint hE₀ hA)

include hE₀ hA in
/-- The closure of `A` is symmetric. -/
theorem closure_onSubspace_symm (x y : (onSubspace E₀ A).closure.domain) :
    ⟪(onSubspace E₀ A).closure x, (y : E)⟫_ℂ = ⟪(x : E), (onSubspace E₀ A).closure y⟫_ℂ := by
  have hcl := isClosable_onSubspace hE₀ hA
  have hTd : Dense ((onSubspace E₀ A).domain : Set E) := hE₀
  have hle : (onSubspace E₀ A).closure ≤ (onSubspace E₀ A).adjoint :=
    closure_le_of_isClosed (LinearPMap.adjoint_isClosed hTd) (onSubspace_le_adjoint hE₀ hA)
  -- `⟪B x, z⟫ = ⟪x, A z⟫` on `E₀`, since `B ≤ A†`
  have h1 : ∀ z : (onSubspace E₀ A).domain,
      ⟪(onSubspace E₀ A).closure x, (z : E)⟫_ℂ = ⟪(x : E), onSubspace E₀ A z⟫_ℂ := fun z => by
    rw [hle.2 (x := x) (y := ⟨x, hle.1 x.2⟩) rfl]
    exact LinearPMap.adjoint_isFormalAdjoint hTd ⟨x, hle.1 x.2⟩ z
  -- the closed set `{(z, w) | ⟪B x, z⟫ = ⟪x, w⟫}` contains the graph of `A`, hence that of `B`
  let S : Set (E × E) := {p | ⟪(onSubspace E₀ A).closure x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ}
  have hS : IsClosed S :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : ((onSubspace E₀ A).graph : Set (E × E)) ⊆ S := by
    rintro p hp
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff (onSubspace E₀ A)).1 hp
    simp only [S, Set.mem_ofPred_eq, ← hz1, ← hz2]
    exact h1 z
  have hmem : ((y : E), (onSubspace E₀ A).closure y) ∈
      ((onSubspace E₀ A).closure.graph : Set (E × E)) := LinearPMap.mem_graph _ y
  rw [← hcl.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe] at hmem
  exact closure_minimal hsub hS hmem

include hE₀ in
/-- For `B†φ = sφ` (`B` the closure of `A`): `⟪φ, Aⁿx⟫ = s̄ⁿ⟪φ, x⟫`. -/
private theorem inner_pow_of_adjoint_eq {s : ℂ} (φ : (onSubspace E₀ A).closure.adjoint.domain)
    (hφ : (onSubspace E₀ A).closure.adjoint φ = s • (φ : E)) (n : ℕ) (x : E₀) :
    ⟪(φ : E), ((A ^ n) x : E)⟫_ℂ = starRingEnd ℂ s ^ n * ⟪(φ : E), (x : E)⟫_ℂ := by
  have hBd := dense_closure_domain (A := A) hE₀
  have h1 : ∀ y : E₀, ⟪(φ : E), (A y : E)⟫_ℂ = starRingEnd ℂ s * ⟪(φ : E), (y : E)⟫_ℂ :=
    fun y => by
      have hy : (y : E) ∈ (onSubspace E₀ A).closure.domain := (LinearPMap.le_closure _).1 y.2
      rw [← closure_onSubspace_apply y hy, ← LinearPMap.adjoint_isFormalAdjoint hBd φ ⟨y, hy⟩,
        hφ, inner_smul_left]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, h1, ih, pow_succ]; ring

variable {ρ : ℝ} (hρ : 0 < ρ)
  (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖)
include hE₀ hA hρ han

private theorem inner_localOp_of_adjoint_eq {s : ℂ} (φ : (onSubspace E₀ A).closure.adjoint.domain)
    (hφ : (onSubspace E₀ A).closure.adjoint φ = s • (φ : E)) {a : ℝ} (ha : |a| ≤ ρ) (χ : E) :
    ⟪(φ : E), localOp A a χ⟫_ℂ =
      Complex.exp (-(a : ℂ) * I * starRingEnd ℂ s) * ⟪(φ : E), χ⟫_ℂ := by
  have hcont : Continuous fun χ => ⟪(φ : E), localOp A a χ⟫_ℂ :=
    continuous_const.inner (localOp A a).continuous
  have hcont' : Continuous fun χ =>
      Complex.exp (-(a : ℂ) * I * starRingEnd ℂ s) * ⟪(φ : E), χ⟫_ℂ :=
    continuous_const.mul (continuous_const.inner continuous_id)
  refine congrFun (hcont.ext_on hE₀ hcont' fun χ hχ => ?_) χ
  have h1 := (hasSum_localOp hE₀ hA hρ han ha ⟨χ, hχ⟩).mapL (innerSL ℂ (φ : E))
  have h2 : HasSum (fun n : ℕ => (-(a : ℂ) * I * starRingEnd ℂ s) ^ n / (n.factorial : ℂ) *
      ⟪(φ : E), χ⟫_ℂ) (Complex.exp (-(a : ℂ) * I * starRingEnd ℂ s) * ⟪(φ : E), χ⟫_ℂ) := by
    have := NormedSpace.expSeries_div_hasSum_exp (-(a : ℂ) * I * starRingEnd ℂ s)
    rw [← Complex.exp_eq_exp_ℂ] at this
    exact this.mul_right _
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp only [innerSL_apply_apply, expTerm, expCoeff, inner_smul_right]
  rw [inner_pow_of_adjoint_eq hE₀ φ hφ n ⟨χ, hχ⟩, mul_pow]
  ring

private theorem inner_globalUnitary_of_adjoint_eq {s : ℂ}
    (φ : (onSubspace E₀ A).closure.adjoint.domain)
    (hφ : (onSubspace E₀ A).closure.adjoint φ = s • (φ : E)) (t : ℝ) (χ : E) :
    ⟪(φ : E), (globalUnitary A ρ t : E →L[ℂ] E) χ⟫_ℂ =
      Complex.exp (-(t : ℂ) * I * starRingEnd ℂ s) * ⟪(φ : E), χ⟫_ℂ := by
  have hn : (0 : ℝ) < numSteps ρ t := Nat.cast_pos.2 (Nat.succ_pos _)
  have hnc : ((numSteps ρ t : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : |t / numSteps ρ t| ≤ ρ / 2 := by
    rw [abs_div, Nat.abs_cast]; exact abs_div_numSteps_le hρ t
  have hpow : ∀ (k : ℕ) (χ : E), ⟪(φ : E), (localOp A (t / numSteps ρ t) ^ k) χ⟫_ℂ =
      Complex.exp (-((t / numSteps ρ t : ℝ) : ℂ) * I * starRingEnd ℂ s) ^ k *
        ⟪(φ : E), χ⟫_ℂ := by
    intro k
    induction k with
    | zero => intro χ; simp
    | succ k ih =>
      intro χ
      rw [pow_succ', mul_apply_eq_comp,
        inner_localOp_of_adjoint_eq hE₀ hA hρ han φ hφ (by linarith) , ih, pow_succ]
      ring
  rw [globalUnitary, SubmonoidClass.coe_pow, coe_localUnitary hE₀ hA hρ han ha, hpow,
    ← Complex.exp_nat_mul]
  congr 2
  push_cast
  field_simp

/-- **Self-adjointness**: the closure of `A` is self-adjoint. -/
theorem isSelfAdjoint_closure_onSubspace : IsSelfAdjoint (onSubspace E₀ A).closure := by
  refine isSelfAdjoint_of_isClosed (dense_closure_domain hE₀)
    (isClosable_onSubspace hE₀ hA).closure_isClosed (closure_onSubspace_symm hE₀ hA) ?_
  intro s hs φ hφ
  obtain ⟨c, hc0, hcs⟩ : ∃ c : ℝ, c ≠ 0 ∧ -I * starRingEnd ℂ s = c := by
    rcases hs with rfl | rfl
    · exact ⟨-1, by norm_num, by simp⟩
    · exact ⟨1, one_ne_zero, by simp⟩
  have key : ∀ t : ℝ, ⟪(φ : E), (globalUnitary A ρ t : E →L[ℂ] E) φ⟫_ℂ =
      Complex.exp ((c * t : ℝ) : ℂ) * ⟪(φ : E), (φ : E)⟫_ℂ := fun t => by
    rw [inner_globalUnitary_of_adjoint_eq hE₀ hA hρ han φ hφ t φ]
    congr 2
    push_cast
    rw [← hcs]
    ring
  let g : ℝ → ℂ := fun t => Complex.exp ((c * t : ℝ) : ℂ) * ⟪(φ : E), (φ : E)⟫_ℂ
  have hg : ∀ t, HasDerivAt g (c * g t) t := fun t => by
    have hd : HasDerivAt (fun t : ℝ => ((c * t : ℝ) : ℂ)) (c : ℂ) t := by
      simpa using ((hasDerivAt_id t).const_mul c).ofReal_comp
    convert hd.cexp.mul_const ⟪(φ : E), (φ : E)⟫_ℂ using 1
    simp only [g]
    ring
  have hb : ∀ t, ‖g t‖ ≤ ‖(φ : E)‖ * ‖(φ : E)‖ := fun t => by
    simp only [g]
    rw [← key t]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [Unitary.norm_map]
  have := eq_zero_of_hasDerivAt_mul_of_bounded hc0 hg hb
  simp only [g, mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul] at this
  exact inner_self_eq_zero.1 this

/-- **The generator**: the closure of `A` generates `U`. -/
private theorem isGenerator_globalUnitary :
    IsGenerator (onSubspace E₀ A).closure (globalUnitary A ρ) :=
  IsGenerator.of_core (isSelfAdjoint_closure_onSubspace hE₀ hA hρ han)
    (LinearPMap.le_closure _).1 (LinearPMap.closureHasCore _).closure_eq
    (isUnitaryGroup_globalUnitary hE₀ hA hρ han) fun ψ => by
      rw [closure_onSubspace_apply (A := A) ψ]
      exact hasDerivAt_globalUnitary hE₀ hA hρ han ψ

end Closure

/-- **Theorem 3** (analytic vectors with a common radius). -/
theorem isSelfAdjoint_closure_and_isGenerator_of_analytic (E₀ : Submodule ℂ E)
    (hE₀ : Dense (E₀ : Set E)) (A : E₀ →ₗ[ℂ] E₀)
    (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖) :
    IsSelfAdjoint (onSubspace E₀ A).closure ∧
      (∃! U : ℝ → unitary (E →L[ℂ] E), IsGenerator (onSubspace E₀ A).closure U) ∧
      ∀ U : ℝ → unitary (E →L[ℂ] E), IsGenerator (onSubspace E₀ A).closure U →
        ∀ t : ℝ, |t| < ρ → ∀ x : E₀,
          HasSum (fun n : ℕ => ((-(t : ℂ) * I) ^ n / (n.factorial : ℂ)) • ((A ^ n) x : E))
            ((U t : E →L[ℂ] E) x) := by
  have hgen := isGenerator_globalUnitary hE₀ hA hρ han
  refine ⟨isSelfAdjoint_closure_onSubspace hE₀ hA hρ han,
    ⟨globalUnitary A ρ, hgen, fun V hV => hV.unique hgen⟩, fun V hV t ht x => ?_⟩
  rw [hV.unique hgen, coe_globalUnitary hE₀ hA hρ han ht.le]
  exact hasSum_localOp hE₀ hA hρ han ht.le x

end BosonicLean
