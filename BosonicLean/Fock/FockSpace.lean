/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.SqNorm
import BosonicLean.Fock.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Finsupp.Interval
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Bosonic Fock space and forms of coefficient-finite operators

The bosonic Fock space `Γ_s(ι) = ℓ²(ℕ^(ι))` is the Hilbert space of square-summable coefficient
families over occupation-number configurations; it sits in the formal Fock space as the vectors of
finite squared norm, a subspace containing the number states. A linear map `T` of the formal Fock
space is *coefficient-finite* if each coefficient `(T ψ)(n)` depends only on finitely many
coefficients of `ψ`. The ladder operators are of this kind, and so is a coefficient-finite
single-mode operator acting on one mode (`IsCoeffFinite.onMode`). The exponential of an operator
that raises the particle number is coefficient-finite when the operator is (`IsCoeffFinite.exp`);
on finitely many modes every operator that raises the particle number is coefficient-finite
(`RaisesParticleNumber.isCoeffFinite`). For coefficient-finite `T` the coefficients of `T ψ` are
continuous on `Γ_s`, so the maximal realization of `T` on `Γ_s`, with domain
`{ψ ∈ Γ_s : T ψ ∈ Γ_s}`, is a closed operator.

For finitely many coefficient-finite `T_k`, the form `q(ψ) = Σ_k ‖T_k ψ‖²` restricted to `Γ_s` has
the form domain `{ψ ∈ Γ_s : T_k ψ ∈ Γ_s for every k}` and the sesquilinear form
`q(φ, ψ) = Σ_k ⟨T_k φ, T_k ψ⟩` on it, Hermitian and non-negative. It is closed in Kato's sense: a
sequence converging in `Γ_s` and Cauchy for `q` converges in `q` to a vector of the form domain.

A bounded operator `T` on the single-mode Fock space has the matrix elements `⟨i∣T∣j⟩`, bounded by
`‖T‖`, and `(T ψ)(i) = Σⱼ ⟨i∣T∣j⟩ ψ(j)`.

## Main definitions

* `BosonicLean.Fock.FockSpace ι`: the bosonic Fock space `ℓ²(ℕ^(ι))`.
* `BosonicLean.Fock.FockSpace.toFormal`: its embedding into the formal Fock space.
* `BosonicLean.Fock.FockSpace.matrixElement T i j`: the matrix element `⟨i∣T∣j⟩` of a bounded
  operator on the single-mode Fock space.
* `BosonicLean.Fock.FormalFock.IsCoeffFinite T`: `T` is coefficient-finite.
* `BosonicLean.Fock.FockSpace.maxRealization T`: the maximal realization of `T` on `Γ_s`.
* `BosonicLean.Fock.FockSpace.formDomain T`, `BosonicLean.Fock.FockSpace.formInner T`: the form
  domain and the sesquilinear form of a finite family `T`.

## Main results

* `FockSpace.mem_range_toFormal_iff`: a formal vector lies in `Γ_s` iff its squared norm is finite.
* `FockSpace.dense_span_single`: the finitely supported vectors are dense in `Γ_s`.
* `FockSpace.norm_matrixElement_le`, `FockSpace.hasSum_matrixElement_mul`: `|⟨i∣T∣j⟩| ≤ ‖T‖` and
  `(T ψ)(i) = Σⱼ ⟨i∣T∣j⟩ ψ(j)`.
* `FormalFock.IsCoeffFinite.continuous_coeff_comp`, `FormalFock.IsCoeffFinite.continuous_coeff`:
  the coefficients of `T ψ` depend continuously on those of `ψ`, and on `ψ ∈ Γ_s`.
* `FormalFock.sqNorm_add_lt_top`, `.sqNorm_smul_lt_top`, `.sqNorm_sum_lt_top`: the square-summable
  vectors form a subspace; `FormalFock.sqNorm_numberState_lt_top`: it contains the number states.
* `FormalFock.IsCoeffFinite.add`, `.mul`, `.aeval`, `.onMode`, `.exp`,
  `FormalFock.RaisesParticleNumber.isCoeffFinite`: closure properties.
* `FockSpace.isClosed_maxRealization`: the maximal realization is closed.
* `FockSpace.mem_formDomain_iff`, `FockSpace.formInner_self`, `FockSpace.formInner_self_nonneg`,
  `FockSpace.conj_formInner`.
* `FockSpace.form_closed`: the form is closed (Kato, *Perturbation Theory for Linear Operators*,
  VI §1.3).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), Ch. VI.
-/

open scoped ENNReal InnerProductSpace ComplexConjugate
open Filter Topology

namespace BosonicLean.Fock

/-- The **bosonic Fock space** `Γ_s(ι) = ℓ²(ℕ^(ι))`: the square-summable families of complex
coefficients over occupation-number configurations, a Hilbert space. -/
noncomputable abbrev FockSpace (ι : Type*) := lp (fun _ : ι →₀ ℕ => ℂ) 2

namespace FockSpace

variable {ι : Type*}

/-- The embedding of the Fock space into the formal Fock space. -/
noncomputable def toFormal : FockSpace ι →ₗ[ℂ] FormalFock ι ℂ where
  toFun ψ := ⟨⇑ψ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeff_toFormal (ψ : FockSpace ι) (n : ι →₀ ℕ) : (toFormal ψ).coeff n = ψ n := rfl

theorem toFormal_injective : Function.Injective (toFormal (ι := ι)) := fun _ _ h =>
  lp.ext (funext fun n => congrArg (FormalFock.coeff · n) h)

theorem summable_sq (ψ : FockSpace ι) : Summable fun n => ‖ψ n‖ ^ 2 := by
  have := (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using this

theorem norm_sq_eq_tsum (ψ : FockSpace ι) : ‖ψ‖ ^ 2 = ∑' n, ‖ψ n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ψ
  simpa using this

/-- On the Fock space, the squared norm of the formal vector is the squared Hilbert norm. -/
theorem sqNorm_toFormal (ψ : FockSpace ι) :
    FormalFock.sqNorm (toFormal ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [FormalFock.sqNorm_eq_ofReal (by simpa using summable_sq ψ), norm_sq_eq_tsum]
  simp only [coeff_toFormal]

private theorem memlp_two_iff_sqNorm_lt_top (ψ : FormalFock ι ℂ) :
    Memℓp ψ.coeff 2 ↔ FormalFock.sqNorm ψ < ∞ := by
  rw [FormalFock.sqNorm_lt_top_iff, memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp

/-- A formal vector lies in the Fock space exactly when its squared norm is finite. -/
theorem mem_range_toFormal_iff (ψ : FormalFock ι ℂ) :
    ψ ∈ LinearMap.range (toFormal (ι := ι)) ↔ FormalFock.sqNorm ψ < ∞ := by
  constructor
  · rintro ⟨φ, rfl⟩
    rw [sqNorm_toFormal]
    exact ENNReal.ofReal_lt_top
  · intro h
    exact ⟨⟨ψ.coeff, (memlp_two_iff_sqNorm_lt_top ψ).2 h⟩, rfl⟩

/-- The finitely supported vectors are dense in the Fock space. -/
theorem dense_span_single [DecidableEq ι] :
    Dense (Submodule.span ℂ (Set.range fun m : ι →₀ ℕ => lp.single 2 m (1 : ℂ)) :
      Set (FockSpace ι)) := by
  intro ψ
  have hψ := lp.hasSum_single (E := fun _ : ι →₀ ℕ => ℂ) (by simp) ψ
  refine mem_closure_of_tendsto hψ (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun m _ => ?_
  have : lp.single (E := fun _ : ι →₀ ℕ => ℂ) 2 m (ψ m) =
      ψ m • lp.single (E := fun _ : ι →₀ ℕ => ℂ) 2 m 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-! ### Matrix elements of bounded single-mode operators -/

/-- The **matrix element** `⟨i∣T∣j⟩ = (T∣j⟩)(i)` of a bounded operator `T` on the single-mode Fock
space `Γ_s = ℓ²(ℕ)`: the coefficient at the number state `∣i⟩` of the image of `∣j⟩`. Equivalently
`⟨i∣T∣j⟩ = ⟪∣i⟫, T∣j⟩⟫` (`lp.inner_single_left`). -/
noncomputable def matrixElement (T : FockSpace Unit →L[ℂ] FockSpace Unit) (i j : ℕ) : ℂ :=
  T (lp.single 2 (Finsupp.single () j) 1) (Finsupp.single () i)

/-- `|⟨i∣T∣j⟩| ≤ ‖T‖`. -/
theorem norm_matrixElement_le (T : FockSpace Unit →L[ℂ] FockSpace Unit) (i j : ℕ) :
    ‖matrixElement T i j‖ ≤ ‖T‖ := by
  refine (lp.norm_apply_le_norm two_ne_zero _ _).trans ((T.le_opNorm _).trans ?_)
  rw [lp.norm_single two_pos, norm_one, mul_one]

/-- The coefficients of `T ψ` through the matrix elements: `(T ψ)(i) = Σⱼ ⟨i∣T∣j⟩ ψ(j)`. -/
theorem hasSum_matrixElement_mul (T : FockSpace Unit →L[ℂ] FockSpace Unit) (ψ : FockSpace Unit)
    (i : ℕ) :
    HasSum (fun j => matrixElement T i j * ψ (Finsupp.single () j))
      (T ψ (Finsupp.single () i)) := by
  have h := ((lp.hasSum_single (E := fun _ : Unit →₀ ℕ => ℂ) (by norm_num) ψ).mapL
    ((lp.evalCLM ℂ (E := fun _ : Unit →₀ ℕ => ℂ) (p := 2) (Finsupp.single () i)).comp T))
  let e : ℕ ≃ (Unit →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm
  have he : ∀ j, e j = Finsupp.single () j := fun j => by
    ext
    simp [e]
  rw [← e.hasSum_iff] at h
  refine h.congr_fun fun j => ?_
  simp only [Function.comp_apply, he, ContinuousLinearMap.comp_apply]
  have hsm : (lp.single 2 (Finsupp.single () j) (ψ (Finsupp.single () j)) : FockSpace Unit) =
      ψ (Finsupp.single () j) • (lp.single 2 (Finsupp.single () j) 1 : FockSpace Unit) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  erw [hsm, map_smul, map_smul]
  rw [smul_eq_mul, mul_comm]
  rfl

end FockSpace

namespace FormalFock

variable {ι : Type*}

/-! ### Square-summable vectors -/

theorem sqNorm_add_lt_top {ψ φ : FormalFock ι ℂ} (hψ : sqNorm ψ < ∞) (hφ : sqNorm φ < ∞) :
    sqNorm (ψ + φ) < ∞ := by
  rw [← FockSpace.mem_range_toFormal_iff] at hψ hφ ⊢
  exact Submodule.add_mem _ hψ hφ

theorem sqNorm_smul_lt_top {ψ : FormalFock ι ℂ} (hψ : sqNorm ψ < ∞) (c : ℂ) :
    sqNorm (c • ψ) < ∞ := by
  rw [← FockSpace.mem_range_toFormal_iff] at hψ ⊢
  exact Submodule.smul_mem _ c hψ

theorem sqNorm_sum_lt_top {κ : Type*} (s : Finset κ) {ψ : κ → FormalFock ι ℂ}
    (h : ∀ k ∈ s, sqNorm (ψ k) < ∞) : sqNorm (∑ k ∈ s, ψ k) < ∞ := by
  simp_rw [← FockSpace.mem_range_toFormal_iff] at h ⊢
  exact Submodule.sum_mem _ h

/-- The number state `∣m⟩` has squared norm `1`. -/
@[simp]
theorem sqNorm_numberState (m : ℕ) : sqNorm (numberState m) = 1 := by
  rw [numberState, sqNorm_single, nnnorm_one, ENNReal.coe_one, one_pow]

/-- Number states are square-summable. -/
theorem sqNorm_numberState_lt_top (m : ℕ) : sqNorm (numberState m) < ∞ := by
  rw [sqNorm_numberState]
  exact ENNReal.one_lt_top

/-! ### Coefficient-finite operators -/

/-- `T` is **coefficient-finite**: each coefficient `(T ψ)(n)` depends only on the coefficients of
`ψ` in a finite set of configurations. Since `T` is linear, `(T ψ)(n)` is then a fixed finite
linear combination of these coefficients. -/
def IsCoeffFinite (T : Module.End ℂ (FormalFock ι ℂ)) : Prop :=
  ∀ n, ∃ s : Finset (ι →₀ ℕ), ∀ ψ φ : FormalFock ι ℂ,
    (∀ m ∈ s, ψ.coeff m = φ.coeff m) → (T ψ).coeff n = (T φ).coeff n

namespace IsCoeffFinite

variable {S T : Module.End ℂ (FormalFock ι ℂ)}

theorem zero : IsCoeffFinite (0 : Module.End ℂ (FormalFock ι ℂ)) := fun _ =>
  ⟨∅, fun _ _ _ => rfl⟩

theorem one : IsCoeffFinite (1 : Module.End ℂ (FormalFock ι ℂ)) := fun n =>
  ⟨{n}, fun _ _ h => h n (Finset.mem_singleton_self n)⟩

theorem add (hS : IsCoeffFinite S) (hT : IsCoeffFinite T) : IsCoeffFinite (S + T) := by
  intro n
  obtain ⟨s, hs⟩ := hS n
  obtain ⟨t, ht⟩ := hT n
  classical
  refine ⟨s ∪ t, fun ψ φ h => ?_⟩
  simp only [LinearMap.add_apply, coeff_add]
  rw [hs ψ φ fun m hm => h m (Finset.mem_union_left _ hm),
    ht ψ φ fun m hm => h m (Finset.mem_union_right _ hm)]

theorem smul (hT : IsCoeffFinite T) (c : ℂ) : IsCoeffFinite (c • T) := by
  intro n
  obtain ⟨s, hs⟩ := hT n
  exact ⟨s, fun ψ φ h => by simp only [LinearMap.smul_apply, coeff_smul, hs ψ φ h]⟩

theorem mul (hS : IsCoeffFinite S) (hT : IsCoeffFinite T) : IsCoeffFinite (S * T) := by
  intro n
  obtain ⟨s, hs⟩ := hS n
  choose t ht using hT
  classical
  refine ⟨s.biUnion t, fun ψ φ h => hs _ _ fun m hm => ?_⟩
  exact ht m ψ φ fun m' hm' => h m' (Finset.mem_biUnion.2 ⟨m, hm, hm'⟩)

theorem pow (hT : IsCoeffFinite T) (k : ℕ) : IsCoeffFinite (T ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ]; exact ih.mul hT

theorem sum {κ : Type*} (s : Finset κ) {T : κ → Module.End ℂ (FormalFock ι ℂ)}
    (hT : ∀ k ∈ s, IsCoeffFinite (T k)) : IsCoeffFinite (∑ k ∈ s, T k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (hT k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => hT k' (Finset.mem_insert_of_mem hk'))

/-- A polynomial in a coefficient-finite operator is coefficient-finite. -/
theorem aeval (hT : IsCoeffFinite T) (p : Polynomial ℂ) : IsCoeffFinite (Polynomial.aeval T p) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact sum _ fun k _ => (hT.pow k).smul _

end IsCoeffFinite

theorem isCoeffFinite_annihilate (j : ι) :
    IsCoeffFinite (annihilate (R := ℂ) j : Module.End ℂ (FormalFock ι ℂ)) := fun n =>
  ⟨{n + Finsupp.single j 1}, fun ψ φ h => by
    rw [coeff_annihilate, coeff_annihilate, h _ (Finset.mem_singleton_self _)]⟩

theorem isCoeffFinite_create (j : ι) :
    IsCoeffFinite (create (R := ℂ) j : Module.End ℂ (FormalFock ι ℂ)) := fun n =>
  ⟨{n - Finsupp.single j 1}, fun ψ φ h => by
    rw [coeff_create, coeff_create, h _ (Finset.mem_singleton_self _)]⟩

/-- A coefficient-finite single-mode operator acting on mode `j` is coefficient-finite. -/
theorem IsCoeffFinite.onMode {T : Module.End ℂ (FormalFock Unit ℂ)} (hT : IsCoeffFinite T)
    (j : ι) : IsCoeffFinite (FormalFock.onMode j T) := by
  intro n
  obtain ⟨s, hs⟩ := hT (Finsupp.single () (n j))
  classical
  refine ⟨s.image fun m => n.update j (m ()), fun ψ φ h => ?_⟩
  rw [coeff_onMode, coeff_onMode]
  exact hs _ _ fun m hm => by
    rw [coeff_fiber, coeff_fiber]
    exact h _ (Finset.mem_image_of_mem _ hm)

/-- On finitely many modes, an operator that raises the particle number is coefficient-finite:
`(T ψ)(n)` depends only on the coefficients with fewer than `∣n∣` particles. -/
theorem RaisesParticleNumber.isCoeffFinite [Finite ι] {T : Module.End ℂ (FormalFock ι ℂ)}
    (hT : RaisesParticleNumber T) : IsCoeffFinite T := by
  intro n
  classical
  have hfin : {m : ι →₀ ℕ | m.degree < n.degree}.Finite := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun _ => n.degree)).subset ?_
    intro m hm i
    simpa using (Finsupp.le_degree i m).trans (le_of_lt hm)
  exact ⟨hfin.toFinset, fun ψ φ h =>
    hT.coeff_eq_of_agree fun m hm => h m (hfin.mem_toFinset.2 hm)⟩

/-- The exponential of a coefficient-finite operator that raises the particle number is
coefficient-finite. -/
theorem IsCoeffFinite.exp {T : NumberRaisingOp ι ℂ} (hT : IsCoeffFinite T.op) :
    IsCoeffFinite T.exp := by
  intro n
  choose s hs using fun k : ℕ => (hT.pow k) n
  classical
  refine ⟨(Finset.range (n.degree + 1)).biUnion s, fun ψ φ h => ?_⟩
  rw [NumberRaisingOp.coeff_exp, NumberRaisingOp.coeff_exp]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hs k ψ φ fun m hm => h m (Finset.mem_biUnion.2 ⟨k, hk, hm⟩)]

/-- **Composition with a coefficient-finite operator.** If the coefficients of `F x` depend
continuously on `x`, so do those of `T (F x)`, for a coefficient-finite `T`. -/
theorem IsCoeffFinite.continuous_coeff_comp {T : Module.End ℂ (FormalFock ι ℂ)}
    (hT : IsCoeffFinite T) {X : Type*} [TopologicalSpace X] {F : X → FormalFock ι ℂ}
    (hF : ∀ k, Continuous fun x => (F x).coeff k) (n : ι →₀ ℕ) :
    Continuous fun x => (T (F x)).coeff n := by
  classical
  obtain ⟨s, hs⟩ := hT n
  have key : ∀ x, (T (F x)).coeff n = ∑ m ∈ s, (F x).coeff m * (T (single m 1)).coeff n := by
    intro x
    have hagree : ∀ m ∈ s, (F x).coeff m = (∑ m' ∈ s, (F x).coeff m' • single m' (1 : ℂ)).coeff m :=
      fun m hm => by
        rw [coeff_sum]
        simp only [coeff_smul, coeff_single, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, hm, ↓reduceIte]
    rw [hs _ _ hagree, map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, coeff_smul, smul_eq_mul]
  simp_rw [key]
  exact continuous_finsetSum _ fun m _ => (hF m).mul continuous_const

/-- The coefficients of `T ψ` depend continuously on `ψ` in the Fock space. -/
theorem IsCoeffFinite.continuous_coeff {T : Module.End ℂ (FormalFock ι ℂ)}
    (hT : IsCoeffFinite T) (n : ι →₀ ℕ) :
    Continuous fun ψ : FockSpace ι => (T (FockSpace.toFormal ψ)).coeff n :=
  hT.continuous_coeff_comp (fun k => (lp.lipschitzWith_one_eval 2 k).continuous) n

end FormalFock

namespace FockSpace

open FormalFock

variable {ι : Type*}

/-- The domain `{ψ ∈ Γ_s : T ψ ∈ Γ_s}` of the maximal realization. -/
noncomputable def maxDomain (T : Module.End ℂ (FormalFock ι ℂ)) : Submodule ℂ (FockSpace ι) where
  carrier := {ψ | Memℓp (T (toFormal ψ)).coeff 2}
  add_mem' {ψ φ} hψ hφ := by
    change Memℓp (T (toFormal (ψ + φ))).coeff 2
    rw [map_add, map_add]
    exact hψ.add hφ
  zero_mem' := by
    change Memℓp (T (toFormal 0)).coeff 2
    rw [map_zero, map_zero]
    exact zero_memℓp
  smul_mem' c ψ hψ := by
    change Memℓp (T (toFormal (c • ψ))).coeff 2
    rw [map_smul, map_smul]
    exact hψ.const_smul c

/-- The **maximal realization** of `T` on the Fock space: `ψ ↦ T ψ` on
`{ψ ∈ Γ_s : T ψ ∈ Γ_s}`. -/
noncomputable def maxRealization (T : Module.End ℂ (FormalFock ι ℂ)) :
    FockSpace ι →ₗ.[ℂ] FockSpace ι where
  domain := maxDomain T
  toFun :=
    { toFun := fun ψ => ⟨(T (toFormal ψ)).coeff, ψ.2⟩
      map_add' := fun ψ φ => by ext n; simp [map_add]; rfl
      map_smul' := fun c ψ => by ext n; simp [map_smul, Pi.smul_apply] }

theorem coe_maxRealization (T : Module.End ℂ (FormalFock ι ℂ)) (ψ : (maxRealization T).domain) :
    ⇑(maxRealization T ψ) = (T (toFormal ψ)).coeff := rfl

theorem mem_domain_maxRealization (T : Module.End ℂ (FormalFock ι ℂ)) (ψ : FockSpace ι) :
    ψ ∈ (maxRealization T).domain ↔ sqNorm (T (toFormal ψ)) < ∞ :=
  memlp_two_iff_sqNorm_lt_top _

theorem toFormal_maxRealization (T : Module.End ℂ (FormalFock ι ℂ))
    (ψ : (maxRealization T).domain) : toFormal (maxRealization T ψ) = T (toFormal ψ) := rfl

/-- **The maximal realization of a coefficient-finite operator is closed.** -/
theorem isClosed_maxRealization {T : Module.End ℂ (FormalFock ι ℂ)} (hT : IsCoeffFinite T) :
    (maxRealization T).IsClosed := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  have h1 : Tendsto (fun r => (u r).1) atTop (𝓝 x.1) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun r => (u r).2) atTop (𝓝 x.2) := (continuous_snd.tendsto _).comp hlim
  -- coefficientwise, `T x.1 = x.2`
  have hcoeff : ∀ n, (T (toFormal x.1)).coeff n = x.2 n := by
    intro n
    refine tendsto_nhds_unique ((hT.continuous_coeff n).continuousAt.tendsto.comp h1) ?_
    have hev : ((fun ψ : FockSpace ι => (T (toFormal ψ)).coeff n) ∘ fun r => (u r).1) =
        fun r => (u r).2 n := by
      funext r
      obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 (hu r)
      rw [Function.comp_apply, ← hy1, ← hy2, coe_maxRealization]
    rw [hev]
    exact ((lp.lipschitzWith_one_eval 2 n).continuous.tendsto _).comp h2
  have hmem : x.1 ∈ (maxRealization T).domain := by
    change Memℓp (T (toFormal x.1)).coeff 2
    rw [show (T (toFormal x.1)).coeff = ⇑x.2 from funext hcoeff]
    exact lp.memℓp x.2
  refine (LinearPMap.mem_graph_iff _).2 ⟨⟨x.1, hmem⟩, rfl, ?_⟩
  ext n
  exact hcoeff n

/-! ### Forms of finitely many coefficient-finite operators -/

variable {κ : Type*}

/-- The **form domain** `{ψ ∈ Γ_s : T_k ψ ∈ Γ_s for every k}` of a finite family `T`. -/
noncomputable def formDomain (T : κ → Module.End ℂ (FormalFock ι ℂ)) : Submodule ℂ (FockSpace ι) :=
  ⨅ k, (maxRealization (T k)).domain

/-- The form domain consists of the vectors where the formal form `Σ_k ‖T_k ψ‖²` is finite. -/
theorem mem_formDomain_iff [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ)) (ψ : FockSpace ι) :
    ψ ∈ formDomain T ↔ ∑ k, sqNorm (T k (toFormal ψ)) < ∞ := by
  simp only [formDomain, Submodule.mem_iInf, mem_domain_maxRealization,
    ENNReal.sum_lt_top, Finset.mem_univ, true_implies]

theorem formDomain_le (T : κ → Module.End ℂ (FormalFock ι ℂ)) (k : κ) :
    formDomain T ≤ (maxRealization (T k)).domain :=
  iInf_le _ k

/-- `T_k` on the form domain, as a linear map into the Fock space. -/
noncomputable def formComponent (T : κ → Module.End ℂ (FormalFock ι ℂ)) (k : κ) :
    formDomain T →ₗ[ℂ] FockSpace ι :=
  (maxRealization (T k)).toFun.comp (Submodule.inclusion (formDomain_le T k))

theorem toFormal_formComponent (T : κ → Module.End ℂ (FormalFock ι ℂ)) (k : κ)
    (ψ : formDomain T) : toFormal (formComponent T k ψ) = T k (toFormal ψ) := rfl

/-- The **sesquilinear form** `q(φ, ψ) = Σ_k ⟨T_k φ, T_k ψ⟩` on the form domain. -/
noncomputable def formInner [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ)) :
    formDomain T →ₗ⋆[ℂ] formDomain T →ₗ[ℂ] ℂ :=
  ∑ k, ((innerₛₗ ℂ).comp (formComponent T k)).compl₂ (formComponent T k)

theorem formInner_apply [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ)) (φ ψ : formDomain T) :
    formInner T φ ψ = ∑ k, ⟪formComponent T k φ, formComponent T k ψ⟫_ℂ := by
  simp [formInner]

/-- The form is Hermitian. -/
theorem conj_formInner [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ)) (φ ψ : formDomain T) :
    conj (formInner T φ ψ) = formInner T ψ φ := by
  simp only [formInner_apply, map_sum, inner_conj_symm]

/-- On the diagonal the form is real and equals the formal form `Σ_k ‖T_k ψ‖²`. -/
theorem formInner_self [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ)) (ψ : formDomain T) :
    ENNReal.ofReal (formInner T ψ ψ).re = ∑ k, sqNorm (T k (toFormal ψ)) ∧
      (formInner T ψ ψ).im = 0 := by
  have h : formInner T ψ ψ = ((∑ k, ‖formComponent T k ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [formInner_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  refine ⟨?_, by rw [h, Complex.ofReal_im]⟩
  rw [h, Complex.ofReal_re, ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← toFormal_formComponent, sqNorm_toFormal]

/-- The form is non-negative on the diagonal. -/
theorem formInner_self_nonneg [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ))
    (ψ : formDomain T) : 0 ≤ (formInner T ψ ψ).re := by
  rw [formInner_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun k _ => by
    simpa only [RCLike.re_to_complex] using inner_self_nonneg (𝕜 := ℂ) (x := formComponent T k ψ)

/-- **The form is closed** (Kato, VI §1.3). If `ψ_r` lie in the form domain, `ψ_r → ψ` in `Γ_s`,
and `q(ψ_r - ψ_s) → 0`, then `ψ` lies in the form domain and `q(ψ_r - ψ) → 0`. -/
theorem form_closed [Fintype κ] {T : κ → Module.End ℂ (FormalFock ι ℂ)}
    (hT : ∀ k, IsCoeffFinite (T k))
    {ψs : ℕ → FockSpace ι} {ψ : FockSpace ι} (hdom : ∀ r, ψs r ∈ formDomain T)
    (hlim : Tendsto ψs atTop (𝓝 ψ))
    (hcauchy : Tendsto (fun p : ℕ × ℕ => ∑ k, sqNorm (T k (toFormal (ψs p.1 - ψs p.2))))
      atTop (𝓝 0)) :
    ψ ∈ formDomain T ∧
      Tendsto (fun r => ∑ k, sqNorm (T k (toFormal (ψs r - ψ)))) atTop (𝓝 0) := by
  -- the images `y k r = T_k ψ_r` in the Fock space
  set y : κ → ℕ → FockSpace ι := fun k r =>
    maxRealization (T k) ⟨ψs r, formDomain_le T k (hdom r)⟩ with hy
  have hyT : ∀ k r, toFormal (y k r) = T k (toFormal (ψs r)) := fun _ _ => rfl
  have hsub : ∀ k (r s : ℕ), T k (toFormal (ψs r - ψs s)) = toFormal (y k r - y k s) := by
    intro k r s
    rw [map_sub, map_sub, map_sub, hyT, hyT]
  -- each term of the Cauchy condition tends to zero
  have hterm : ∀ k, Tendsto (fun p : ℕ × ℕ => sqNorm (T k (toFormal (ψs p.1 - ψs p.2))))
      atTop (𝓝 0) := fun k =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcauchy (fun _ => zero_le)
      fun p => Finset.single_le_sum (f := fun k => sqNorm (T k (toFormal (ψs p.1 - ψs p.2))))
        (fun _ _ => zero_le) (Finset.mem_univ k)
  -- so each `y k` is Cauchy, hence convergent
  have hnorm : ∀ k, Tendsto (fun p : ℕ × ℕ => ‖y k p.1 - y k p.2‖) atTop (𝓝 0) := by
    intro k
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hterm k)
    simp only [Function.comp_def, hsub, sqNorm_toFormal, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (sq_nonneg _)] at h
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hcs : ∀ k, CauchySeq (y k) := by
    intro k
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    simpa [dist_eq_norm] using hnorm k
  choose z hz using fun k => cauchySeq_tendsto_of_complete (hcs k)
  -- by closedness, `ψ ∈ dom T_k` and `T_k ψ = z k`
  have hgraph : ∀ k, (ψ, z k) ∈ (maxRealization (T k)).graph := by
    intro k
    refine (isClosed_maxRealization (hT k)).mem_of_tendsto (hlim.prodMk_nhds (hz k))
      (Eventually.of_forall fun r => ?_)
    exact (LinearPMap.mem_graph_iff _).2 ⟨⟨ψs r, formDomain_le T k (hdom r)⟩, rfl, rfl⟩
  have hmem : ∀ k, ψ ∈ (maxRealization (T k)).domain := fun k =>
    (LinearPMap.mem_domain_of_mem_graph (hgraph k))
  have hval : ∀ k, T k (toFormal ψ) = toFormal (z k) := by
    intro k
    obtain ⟨w, hw1, hw2⟩ := (LinearPMap.mem_graph_iff _).1 (hgraph k)
    dsimp only at hw1 hw2
    rw [← hw2, toFormal_maxRealization, hw1]
  refine ⟨Submodule.mem_iInf _ |>.2 hmem, ?_⟩
  rw [show (0 : ℝ≥0∞) = ∑ _k : κ, 0 by simp]
  refine tendsto_finsetSum _ fun k _ => ?_
  have hd : Tendsto (fun r => ‖y k r - z k‖) atTop (𝓝 0) := by
    have := (hz k).sub_const (z k)
    rw [sub_self] at this
    simpa using this.norm
  have : Tendsto (fun r => ENNReal.ofReal (‖y k r - z k‖ ^ 2)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun r => ‖y k r - z k‖ ^ 2) atTop (𝓝 0) := by simpa using hd.pow 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    simpa [Function.comp_def] using this
  refine this.congr fun r => ?_
  rw [map_sub, map_sub, hval, ← hyT, ← map_sub, sqNorm_toFormal]

end FockSpace

end BosonicLean.Fock
