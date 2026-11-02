/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Fock.NumberRaisingExp
import BosonicLean.Fock.NumberState
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Product vectors and operators on one mode

The formal Fock space on finitely many modes `ι` contains the product vectors
`(⊗ⱼ φⱼ)(n) = ∏ⱼ φⱼ(nⱼ)` of single-mode vectors. The map `φ ↦ ⊗ⱼ φⱼ` is multilinear; it is not
an isomorphism from a tensor product of single-mode formal Fock spaces, and product vectors do not
span the formal Fock space.

A single-mode operator `T` acts on mode `j` as `T_j`: fixing the occupations of the other modes,
a formal vector restricts to a single-mode vector along mode `j` (its fiber), and `onMode j T`
applies `T` to every fiber. The map `T ↦ T_j` is an algebra map, acts on product vectors factor by
factor, and sends
`a`, `a†` and `e^{c a†}` to `aⱼ`, `aⱼ†` and `e^{c aⱼ†}`. No continuity is needed: `T_j` is
defined for every linear map.

## Main definitions

* `BosonicLean.Fock.FormalFock.tensorVec`: the product vector `⊗ⱼ φⱼ`.
* `BosonicLean.Fock.FormalFock.fiber`: the fiber of a formal vector along a mode.
* `BosonicLean.Fock.FormalFock.onMode`: the single-mode operator `T` acting on mode `j`;
  `onModeAlgHom`, the map `T ↦ T_j` as an algebra map.

## Main results

* `onMode_tensorVec`: on product vectors `T_j` acts on factor `j`.
* `onMode_annihilate`, `onMode_create`, `onMode_exp_gen`: the ladder operators and the
  exponentials of operators on mode `j` that raise the particle number are the single-mode ones
  acting on mode `j`.
* `commute_annihilate_exp`: `aⱼ` commutes with `e^{c aₖ†}` for `k ≠ j`.
* `mem_span_numberStates_of_annihilate_pow`: a vector killed by `aⱼ^{mⱼ}` for every `j` is a
  combination of number states with `nⱼ < mⱼ`.
* `mem_span_tensorVec_of_fiber_mem`: a vector whose fibers along every mode lie in a
  finite-dimensional space is a combination of product vectors.
-/

open Finset

namespace BosonicLean.Fock.FormalFock

variable {ι : Type*}

/-! ### Product vectors -/

/-- The **product vector** `⊗ⱼ φⱼ` of single-mode vectors: `(⊗ⱼ φⱼ)(n) = ∏ⱼ φⱼ(nⱼ)`. -/
noncomputable def tensorVec [Fintype ι] (φ : ι → FormalFock Unit ℂ) : FormalFock ι ℂ :=
  ⟨fun n => ∏ j, (φ j).coeff (Finsupp.single () (n j))⟩

theorem coeff_tensorVec [Fintype ι] (φ : ι → FormalFock Unit ℂ) (n : ι →₀ ℕ) :
    (tensorVec φ).coeff n = ∏ j, (φ j).coeff (Finsupp.single () (n j)) :=
  rfl

/-- A coefficient of a product vector with one factor singled out. -/
theorem coeff_tensorVec_update [Fintype ι] [DecidableEq ι] (φ : ι → FormalFock Unit ℂ) (j : ι)
    (x : FormalFock Unit ℂ) (n : ι →₀ ℕ) :
    (tensorVec (Function.update φ j x)).coeff n =
      x.coeff (Finsupp.single () (n j)) *
        ∏ k ∈ univ.erase j, (φ k).coeff (Finsupp.single () (n k)) := by
  rw [coeff_tensorVec, ← mul_prod_erase univ _ (mem_univ j), Function.update_self]
  congr 1
  exact prod_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]

/-- The product vector is additive in each factor. -/
theorem tensorVec_update_add [Fintype ι] [DecidableEq ι] (φ : ι → FormalFock Unit ℂ) (j : ι)
    (x y : FormalFock Unit ℂ) :
    tensorVec (Function.update φ j (x + y)) =
      tensorVec (Function.update φ j x) + tensorVec (Function.update φ j y) := by
  ext n
  simp only [coeff_add, coeff_tensorVec_update, add_mul]

/-- The product vector is homogeneous in each factor. -/
theorem tensorVec_update_smul [Fintype ι] [DecidableEq ι] (φ : ι → FormalFock Unit ℂ) (j : ι)
    (c : ℂ)
    (x : FormalFock Unit ℂ) :
    tensorVec (Function.update φ j (c • x)) = c • tensorVec (Function.update φ j x) := by
  ext n
  simp only [coeff_smul, coeff_tensorVec_update, smul_eq_mul, mul_assoc]

/-- A product of number states is a number state. -/
theorem tensorVec_numberState [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    tensorVec (fun j => numberState (m j)) = single (Finsupp.equivFunOnFinite.symm m) 1 := by
  ext n
  simp only [coeff_tensorVec, coeff_numberState, coeff_single]
  rw [prod_boole]
  congr 1
  refine propext ⟨fun h => ?_, fun h j => ?_⟩
  · ext j
    simpa using h j (mem_univ j)
  · subst h
    simp

/-- The product of vacua is the vacuum. -/
theorem tensorVec_vacuum [Fintype ι] [DecidableEq ι] :
    tensorVec (fun _ : ι => numberState 0) = single 0 1 := by
  rw [tensorVec_numberState]
  congr
  ext j
  simp

/-! ### Operators on one mode -/

/-- The **fiber** (mode-`j` fiber: all occupations fixed except that of mode `j`; Kolda–Bader,
*SIAM Rev.* 51 (2009)) of a formal vector along mode `j` at the occupations `n` of the other modes:
the single-mode vector `m ↦ ψ(n with nⱼ replaced by m)`. -/
noncomputable def fiber (j : ι) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) : FormalFock Unit ℂ :=
  ⟨fun m => ψ.coeff (n.update j (m ()))⟩

theorem coeff_fiber (j : ι) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) (m : Unit →₀ ℕ) :
    (fiber j ψ n).coeff m = ψ.coeff (n.update j (m ())) :=
  rfl

/-- The fiber does not depend on the occupation of mode `j` itself. -/
theorem fiber_update (j : ι) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) (b : ℕ) :
    fiber j ψ (n.update j b) = fiber j ψ n := by
  ext m
  rw [coeff_fiber, coeff_fiber, Finsupp.update_idem]

/-- The coefficient of the fiber at the occupation of mode `j` is the coefficient of the vector. -/
theorem coeff_fiber_self (j : ι) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    (fiber j ψ n).coeff (Finsupp.single () (n j)) = ψ.coeff n := by
  classical
  rw [coeff_fiber, Finsupp.single_eq_same, Finsupp.update_self]

/-- **A single-mode operator acting on mode `j`**: `(T_j ψ)(n) = (T ψ_n)(nⱼ)`, with `ψ_n` the
fiber of `ψ` along mode `j` at `n`. -/
noncomputable def onMode (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ)) :
    Module.End ℂ (FormalFock ι ℂ) where
  toFun ψ := ⟨fun n => (T (fiber j ψ n)).coeff (Finsupp.single () (n j))⟩
  map_add' ψ φ := by
    ext n
    have h : fiber j (ψ + φ) n = fiber j ψ n + fiber j φ n := rfl
    simp only [h, map_add, coeff_add]
  map_smul' c ψ := by
    ext n
    have h : fiber j (c • ψ) n = c • fiber j ψ n := rfl
    simp only [h, map_smul, coeff_smul, RingHom.id_apply]

theorem coeff_onMode (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ)) (ψ : FormalFock ι ℂ)
    (n : ι →₀ ℕ) : (onMode j T ψ).coeff n = (T (fiber j ψ n)).coeff (Finsupp.single () (n j)) :=
  rfl

/-- The fibers of `T_j ψ` along mode `j` are the images under `T` of the fibers of `ψ`. -/
theorem fiber_onMode (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ))
    (ψ : FormalFock ι ℂ)
    (n : ι →₀ ℕ) : fiber j (onMode j T ψ) n = T (fiber j ψ n) := by
  classical
  ext m
  rw [coeff_fiber, coeff_onMode, fiber_update, Finsupp.coe_update, Function.update_self,
    ← Finsupp.unique_single m]

theorem onMode_one (j : ι) :
    onMode j (1 : Module.End ℂ (FormalFock Unit ℂ)) = 1 := by
  classical
  ext ψ n
  rw [coeff_onMode, Module.End.one_apply, coeff_fiber_self, Module.End.one_apply]

theorem onMode_mul (j : ι) (S T : Module.End ℂ (FormalFock Unit ℂ)) :
    onMode j (S * T) = onMode j S * onMode j T := by
  classical
  ext ψ n
  rw [Module.End.mul_apply, coeff_onMode, coeff_onMode, fiber_onMode, Module.End.mul_apply]

theorem onMode_add (j : ι) (S T : Module.End ℂ (FormalFock Unit ℂ)) :
    onMode j (S + T) = onMode j S + onMode j T := by
  ext ψ n
  simp only [coeff_onMode, LinearMap.add_apply, coeff_add]

theorem onMode_smul (j : ι) (c : ℂ) (T : Module.End ℂ (FormalFock Unit ℂ)) :
    onMode j (c • T) = c • onMode j T := by
  ext ψ n
  simp only [coeff_onMode, LinearMap.smul_apply, coeff_smul]

/-- The map `T ↦ T_j` as an algebra map. -/
noncomputable def onModeAlgHom (j : ι) :
    Module.End ℂ (FormalFock Unit ℂ) →ₐ[ℂ] Module.End ℂ (FormalFock ι ℂ) where
  toFun := onMode j
  map_one' := onMode_one j
  map_mul' := onMode_mul j
  map_zero' := by
    ext ψ n
    rw [coeff_onMode, LinearMap.zero_apply, coeff_zero, LinearMap.zero_apply, coeff_zero]
  map_add' := onMode_add j
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, onMode_smul, onMode_one]

@[simp]
theorem onModeAlgHom_apply (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ)) :
    onModeAlgHom j T = onMode j T :=
  rfl

theorem onMode_pow (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ)) (k : ℕ) :
    onMode j (T ^ k) = onMode j T ^ k :=
  map_pow (onModeAlgHom j) T k

theorem onMode_aeval (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ))
    (p : Polynomial ℂ) :
    onMode j (Polynomial.aeval T p) = Polynomial.aeval (onMode j T) p :=
  (Polynomial.aeval_algHom_apply (onModeAlgHom j) T p).symm

/-- **On product vectors `T_j` acts on factor `j`.** -/
theorem onMode_tensorVec [Fintype ι] [DecidableEq ι] (j : ι) (T : Module.End ℂ (FormalFock Unit ℂ))
    (φ : ι → FormalFock Unit ℂ) :
    onMode j T (tensorVec φ) = tensorVec (Function.update φ j (T (φ j))) := by
  have hs : ∀ n, fiber j (tensorVec φ) n =
      (∏ k ∈ univ.erase j, (φ k).coeff (Finsupp.single () (n k))) • φ j := fun n => by
    ext m
    rw [coeff_fiber, ← Function.update_eq_self j φ, coeff_tensorVec_update, Function.update_eq_self,
      coeff_smul, smul_eq_mul, Finsupp.coe_update, Function.update_self, ← Finsupp.unique_single m,
      mul_comm]
    congr 1
    refine prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hk)]
  ext n
  rw [coeff_onMode, hs, map_smul, coeff_smul, smul_eq_mul, coeff_tensorVec_update, mul_comm]

theorem onMode_annihilate (j : ι) :
    onMode j (annihilate ()) = (annihilate j : Module.End ℂ (FormalFock ι ℂ)) := by
  classical
  ext ψ n
  rw [coeff_onMode, coeff_annihilate, coeff_annihilate, coeff_fiber, Finsupp.single_eq_same,
    Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  congr 2
  ext k
  rw [Finsupp.update_apply, Finsupp.add_apply]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

theorem onMode_create (j : ι) :
    onMode j (create ()) = (create j : Module.End ℂ (FormalFock ι ℂ)) := by
  classical
  ext ψ n
  rw [coeff_onMode, coeff_create, coeff_create, Finsupp.single_eq_same]
  split_ifs with h
  · rw [coeff_fiber]
    congr 2
    ext k
    rw [Finsupp.update_apply, Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    split_ifs with hk
    · subst hk
      simp
    · simp [Ne.symm hk]
  · rfl

theorem onMode_lmul (j : ι) (c : ℂ) :
    onMode j (lmul c) = (lmul c : Module.End ℂ (FormalFock ι ℂ)) := by
  classical
  ext ψ n
  rw [coeff_onMode, coeff_lmul, coeff_lmul, coeff_fiber_self]

/-- The generator `c (a†)^p` acting on mode `j` is `c (aⱼ†)^p`. -/
theorem onMode_gen_op (c : ℂ) (j : ι) {p : ℕ} (hp : 1 ≤ p) :
    onMode j (gen c () p hp).op = (gen c j p hp).op := by
  classical
  rw [gen, gen, onMode_mul, onMode_lmul, onMode_pow, onMode_create]

/-- The exponential of an operator acting on mode `j` (one that raises the particle number) is
that operator's single-mode exponential acting on mode `j`. -/
theorem onMode_exp (j : ι) (T : NumberRaisingOp Unit ℂ) (T' : NumberRaisingOp ι ℂ)
    (h : onMode j T.op = T'.op) : onMode j T.exp = T'.exp := by
  classical
  ext ψ n
  rw [NumberRaisingOp.coeff_exp, coeff_onMode, NumberRaisingOp.coeff_exp_eq_sum T _ (M := n.degree)
    (by rw [Finsupp.degree_single]; exact Finsupp.le_degree j n)]
  refine sum_congr rfl fun k _ => ?_
  rw [← h, ← onMode_pow, coeff_onMode]

/-- **`e^{c aⱼ†}` is `e^{c a†}` acting on mode `j`.** -/
theorem onMode_exp_gen (c : ℂ) (j : ι) {p : ℕ} (hp : 1 ≤ p) :
    onMode j ((gen c () p hp).exp) = (gen c j p hp).exp :=
  onMode_exp j _ _ (onMode_gen_op c j hp)

/-- The vacuum is not zero. -/
theorem single_zero_one_ne_zero [DecidableEq ι] :
    (FormalFock.single 0 1 : FormalFock ι ℂ) ≠ 0 := fun h => by
  have := congrArg (fun ψ : FormalFock ι ℂ => ψ.coeff 0) h
  simp [coeff_single] at this

/-- A product vector with a zero factor is zero. -/
theorem tensorVec_eq_zero [Fintype ι] {φ : ι → FormalFock Unit ℂ} {k : ι} (h : φ k = 0) :
    tensorVec φ = 0 := by
  ext n
  rw [coeff_tensorVec, coeff_zero]
  exact prod_eq_zero (mem_univ k) (by rw [h, coeff_zero])

/-- **Operators on distinct modes act on product vectors factor by factor:** the ordered product of
`T_r` on the modes `w r` replaces the factor at `w r` by `T_r φ_{w r}`. -/
theorem list_prod_onMode_tensorVec [Fintype ι] {l : ℕ} {w : Fin l → ι}
    (hw : Function.Injective w) (T : Fin l → Module.End ℂ (FormalFock Unit ℂ))
    (φ : ι → FormalFock Unit ℂ) :
    (List.ofFn fun r => onMode (w r) (T r)).prod (tensorVec φ) =
      tensorVec (Function.extend w (fun r => T r (φ (w r))) φ) := by
  classical
  induction l with
  | zero =>
    rw [List.ofFn_zero, List.prod_nil, Module.End.one_apply]
    congr 1
    funext k
    exact (Function.extend_apply' _ _ _ fun ⟨r, _⟩ => r.elim0).symm
  | succ l ih =>
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (w := fun i => w i.succ) (fun a b h => Fin.succ_injective l (hw h)) (fun i => T i.succ),
      onMode_tensorVec]
    have h0 : Function.extend (fun i : Fin l => w i.succ)
        (fun r : Fin l => T r.succ (φ (w r.succ))) φ (w 0) = φ (w 0) :=
      Function.extend_apply' _ _ _ fun ⟨r, hr⟩ => Fin.succ_ne_zero r (hw hr)
    rw [h0]
    congr 1
    funext k
    by_cases hk : k = w 0
    · subst hk
      rw [Function.update_self, hw.extend_apply]
    · rw [Function.update_of_ne hk]
      by_cases hr : ∃ r, w r = k
      · obtain ⟨r, rfl⟩ := hr
        cases r using Fin.cases with
        | zero => exact absurd rfl hk
        | succ r =>
          rw [hw.extend_apply, (show Function.Injective fun i : Fin l => w i.succ from
            fun a b h => Fin.succ_injective l (hw h)).extend_apply
            (fun r => T r.succ (φ (w r.succ))) φ r]
      · rw [Function.extend_apply' _ _ _ hr, Function.extend_apply' _ _ _ fun ⟨r, h⟩ => hr ⟨_, h⟩]

/-! ### Identities on many modes -/

/-- Annihilation operators commute. -/
theorem commute_annihilate_annihilate (j k : ι) :
    Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) (annihilate k) :=
  commute_iff_lie_eq.mpr (lie_annihilate_annihilate j k)

/-- An annihilation operator commuting with an operator that raises the particle number commutes
with its exponential. -/
theorem commute_annihilate_exp_of_commute (j : ι) (T : NumberRaisingOp ι ℂ)
    (h : Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) T.op) :
    Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) T.exp := by
  ext ψ n
  have hd : n.degree ≤ n.degree + 1 := Nat.le_succ _
  have hd' : (n + Finsupp.single j 1).degree ≤ n.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [Module.End.mul_apply, Module.End.mul_apply, coeff_annihilate,
    NumberRaisingOp.coeff_exp_eq_sum T _ hd', NumberRaisingOp.coeff_exp_eq_sum T _ hd, smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← Module.End.mul_apply (T.op ^ k), ← (h.pow_right k).eq, Module.End.mul_apply,
    coeff_annihilate, smul_comm]

/-- **`aⱼ` commutes with `e^{c aₖ†}` for `k ≠ j`.** -/
theorem commute_annihilate_exp {j k : ι} (hjk : j ≠ k) (c : ℂ) :
    Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) ((gen c k 1 le_rfl).exp) := by
  classical
  refine commute_annihilate_exp_of_commute j _ ?_
  have hc : Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) (create k) := by
    have := lie_annihilate_create (R := ℂ) j k
    simp only [hjk, ↓reduceIte] at this
    exact commute_iff_lie_eq.mpr this
  have hl : Commute (annihilate j : Module.End ℂ (FormalFock ι ℂ)) (lmul c) :=
    LinearMap.ext fun ψ => by
      ext n
      simp only [Module.End.mul_apply, coeff_annihilate, coeff_lmul, smul_eq_mul]
      ring
  exact hl.mul_right (hc.pow_right 1)

/-- **A vector killed by `aⱼ^{mⱼ}` for every `j` is a combination of number states** with
`nⱼ < mⱼ`. -/
theorem mem_span_numberStates_of_annihilate_pow [Fintype ι] (m : ι → ℕ)
    (ψ : FormalFock ι ℂ)
    (h : ∀ j, (annihilate j ^ m j : Module.End ℂ (FormalFock ι ℂ)) ψ = 0) :
    ψ ∈ Submodule.span ℂ (Set.range fun n : (j : ι) → Fin (m j) =>
      tensorVec fun j => numberState (n j)) := by
  classical
  -- the coefficients with some `nⱼ ≥ mⱼ` vanish
  have hpow : ∀ (j : ι) (r : ℕ) (n : ι →₀ ℕ),
      ((annihilate j ^ r : Module.End ℂ (FormalFock ι ℂ)) ψ).coeff n =
        (∏ s ∈ range r, sqrtC (n j + s + 1)) * ψ.coeff (n + Finsupp.single j r) := by
    intro j r
    induction r with
    | zero => intro n; simp
    | succ r ih =>
      intro n
      rw [pow_succ', Module.End.mul_apply, coeff_annihilate, ih, prod_range_succ', smul_eq_mul]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, add_zero]
      rw [show n + Finsupp.single j 1 + Finsupp.single j r = n + Finsupp.single j (r + 1) by
          rw [add_assoc, ← Finsupp.single_add, add_comm 1 r]]
      have : ∀ s ∈ range r, sqrtC (n j + 1 + s + 1) = sqrtC (n j + (s + 1) + 1) := fun s _ => by
        congr 1; ring
      rw [prod_congr rfl this]
      ring
  have hzero : ∀ n : ι →₀ ℕ, (∃ j, m j ≤ n j) → ψ.coeff n = 0 := by
    rintro n ⟨j, hj⟩
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hj
    have h1 := congrArg (fun φ => φ.coeff (n - Finsupp.single j (m j))) (h j)
    simp only [hpow, coeff_zero] at h1
    have hn : n - Finsupp.single j (m j) + Finsupp.single j (m j) = n :=
      tsub_add_cancel_of_le (by rw [Finsupp.single_le_iff]; exact hj)
    rw [hn] at h1
    refine (mul_eq_zero.mp h1).resolve_left (prod_ne_zero_iff.mpr fun s _ => sqrtC_ne_zero ?_)
    omega
  -- `ψ` is the combination of its coefficients below `m`
  have hsum : ψ = ∑ n : (j : ι) → Fin (m j),
      ψ.coeff (Finsupp.equivFunOnFinite.symm fun j => (n j : ℕ)) •
        tensorVec fun j => numberState (n j) := by
    ext p
    simp only [coeff_sum, coeff_smul, tensorVec_numberState, coeff_single, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hp : ∀ j, p j < m j
    · rw [sum_eq_single (fun j => ⟨p j, hp j⟩)]
      · simp
      · intro n _ hn
        rw [ite_eq_right_iff]
        intro e
        exfalso
        apply hn
        funext j
        ext
        simpa using (congrArg (fun q : ι →₀ ℕ => q j) e).symm
      · simp
    · simp only [not_forall, not_lt] at hp
      rw [hzero p hp]
      refine (sum_eq_zero fun n _ => ?_).symm
      rw [ite_eq_right_iff]
      rintro rfl
      exfalso
      obtain ⟨j, hj⟩ := hp
      have hj' : m j ≤ (n j : ℕ) := by simpa using hj
      exact absurd (n j).2 (not_lt.mpr hj')
  rw [hsum]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-! ### Fibers of sums and of product vectors -/

theorem fiber_sub {ι : Type*} (j : ι) (ψ φ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    fiber j (ψ - φ) n = fiber j ψ n - fiber j φ n :=
  rfl

theorem fiber_smul {ι : Type*} (j : ι) (c : ℂ) (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ) :
    fiber j (c • ψ) n = c • fiber j ψ n :=
  rfl

theorem fiber_sum {ι α : Type*} (j : ι) (s : Finset α) (f : α → FormalFock ι ℂ)
    (n : ι →₀ ℕ) : fiber j (∑ a ∈ s, f a) n = ∑ a ∈ s, fiber j (f a) n := by
  ext m
  simp only [coeff_fiber, coeff_sum]

/-- The fiber of a product vector along mode `j` is a multiple of its `j`-th factor. -/
theorem fiber_tensorVec {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    (φ : ι → FormalFock Unit ℂ) (n : ι →₀ ℕ) :
    fiber j (tensorVec φ) n =
      (∏ k ∈ univ.erase j, (φ k).coeff (Finsupp.single () (n k))) • φ j := by
  ext m
  rw [coeff_fiber, ← Function.update_eq_self j φ, coeff_tensorVec_update, Function.update_eq_self,
    coeff_smul, smul_eq_mul, Finsupp.coe_update, Function.update_self, ← Finsupp.unique_single m,
    mul_comm]
  congr 1
  refine prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

/-! ### Interpolation in a finite-dimensional space of single-mode vectors -/

/-- **Interpolation nodes**: a finite-dimensional space `V` of single-mode formal vectors has
occupations `k₁, …, k_t` such that restriction to them is injective on `V`, together with
vectors `b₁, …, b_t ∈ V` dual to them, `b_p(k_q) = δ_{pq}`. -/
theorem exists_interpolation (V : Submodule ℂ (FormalFock Unit ℂ)) [FiniteDimensional ℂ V] :
    ∃ (t : ℕ) (k : Fin t → ℕ) (b : Fin t → FormalFock Unit ℂ), (∀ p, b p ∈ V) ∧
      (∀ p q, (b p).coeff (Finsupp.single () (k q)) = if p = q then 1 else 0) ∧
      ∀ v ∈ V, (∀ q, v.coeff (Finsupp.single () (k q)) = 0) → v = 0 := by
  classical
  -- the coefficient functionals on `V`
  let ev : ℕ → Module.Dual ℂ V := fun m =>
    { toFun := fun v => (v : FormalFock Unit ℂ).coeff (Finsupp.single () m)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ m v, ev m v = (v : FormalFock Unit ℂ).coeff (Finsupp.single () m) :=
    fun _ _ => rfl
  -- a vector of `V` with all coefficients zero is zero
  have hzero : ∀ v : V, (∀ m, ev m v = 0) → v = 0 := fun v hv => by
    ext1
    ext m
    rw [Finsupp.unique_single m]
    exact (hev _ v).symm.trans (hv _)
  -- the coefficient functionals span the dual
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hzero v fun m => ?_
      exact (Submodule.mem_dualCoannihilator v).mp hv _ (Submodule.subset_span ⟨m, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)),
      hco, Submodule.dualAnnihilator_bot]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ ev
  have : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  let σ := Fintype.equivFin κ
  let k : Fin (Fintype.card κ) → ℕ := fun q => a (σ.symm q)
  let R : V →ₗ[ℂ] Fin (Fintype.card κ) → ℂ := LinearMap.pi fun q => ev (k q)
  have hR : ∀ v q, R v q = (v : FormalFock Unit ℂ).coeff (Finsupp.single () (k q)) :=
    fun _ _ => rfl
  have hinj : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ v]
    intro φ
    have hle : Submodule.span ℂ (Set.range (ev ∘ a)) ≤
        LinearMap.ker (Module.Dual.eval ℂ V v) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have := congrFun (LinearMap.mem_ker.mp hv) (σ x)
      simpa [R, k] using this
    exact hle (by rw [hsp, hspan]; trivial)
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (Fin (Fintype.card κ) → ℂ) := by
    rw [Module.finrank_fin_fun, ← Subspace.dual_finrank_eq,
      Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp, hspan]))]
  have hsurj : Function.Surjective R :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let E := LinearEquiv.ofBijective R ⟨hinj, hsurj⟩
  refine ⟨Fintype.card κ, k, fun p => (E.symm (Pi.single p 1) : V), fun p => (E.symm _).2,
    fun p q => ?_, fun v hv h => ?_⟩
  · rw [← hR]
    change E (E.symm (Pi.single p 1)) q = _
    rw [LinearEquiv.apply_symm_apply, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  · have : R ⟨v, hv⟩ = 0 := funext fun q => (hR _ q).trans (h q)
    have h0 : (⟨v, hv⟩ : V) = 0 := hinj (this.trans (map_zero R).symm)
    exact congrArg Subtype.val h0

/-! ### Vanishing from the values on the nodes -/

/-- A formal vector whose fibers lie in a space `V` on which restriction to the occupations
`k₁, …, k_t` is injective vanishes if it vanishes at every occupation with all `nⱼ` among the
`k_q`. -/
theorem eq_zero_of_fiber_mem {ι : Type*} [Finite ι]
    {V : Submodule ℂ (FormalFock Unit ℂ)} {t : ℕ} {k : Fin t → ℕ}
    (hk : ∀ v ∈ V, (∀ q, v.coeff (Finsupp.single () (k q)) = 0) → v = 0)
    {Ψ : FormalFock ι ℂ} (h : ∀ j n, fiber j Ψ n ∈ V)
    (hz : ∀ n : ι →₀ ℕ, (∀ j, n j ∈ Set.range k) → Ψ.coeff n = 0) :
    Ψ = 0 := by
  classical
  have := Fintype.ofFinite ι
  -- `Ψ(n) = 0` whenever `nⱼ` is a node for every mode `j` outside `s`
  have key : ∀ s : Finset ι, ∀ n : ι →₀ ℕ, (∀ j ∉ s, n j ∈ Set.range k) → Ψ.coeff n = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun n hn => hz n fun j => hn j (notMem_empty j)
    | insert a s _ ih =>
      intro n hn
      have hg : fiber a Ψ n = 0 := by
        refine hk _ (h a n) fun q => ?_
        rw [coeff_fiber, Finsupp.single_eq_same]
        refine ih _ fun j hj => ?_
        rw [Finsupp.coe_update]
        by_cases hja : j = a
        · subst hja
          rw [Function.update_self]
          exact ⟨q, rfl⟩
        · rw [Function.update_of_ne hja]
          exact hn j (by simp [hja, hj])
      rw [← coeff_fiber_self a, hg, coeff_zero]
  ext n
  exact key univ n fun j hj => absurd (mem_univ j) hj

/-! ### Product vectors of combinations -/

/-- A product vector of elements of `span {e_1, …, e_d}` is a combination of the product vectors
`⊗ⱼ e_{Jⱼ}`. -/
theorem tensorVec_mem_span {ι : Type*} [Fintype ι] {d : ℕ} {e : Fin d → FormalFock Unit ℂ}
    {φ : ι → FormalFock Unit ℂ} (hφ : ∀ j, φ j ∈ Submodule.span ℂ (Set.range e)) :
    tensorVec φ ∈ Submodule.span ℂ (Set.range fun J : ι → Fin d => tensorVec fun j => e (J j)) := by
  classical
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hφ j)
  have hsum : tensorVec φ =
      ∑ J : ι → Fin d, (∏ j, c j (J j)) • tensorVec fun j => e (J j) := by
    ext n
    simp only [coeff_sum, coeff_smul, coeff_tensorVec, smul_eq_mul, ← hc]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, prod_mul_distrib]
  rw [hsum]
  exact Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)

/-! ### The main result -/

/-- **Fibers in a finite-dimensional space**: a formal vector whose fibers along every mode lie in
the span of `e_1, …, e_d` is a combination of the product vectors `⊗ⱼ e_{Jⱼ}`. -/
theorem mem_span_tensorVec_of_fiber_mem {ι : Type*} [Fintype ι] {d : ℕ}
    {e : Fin d → FormalFock Unit ℂ} {Ψ : FormalFock ι ℂ}
    (h : ∀ j n, fiber j Ψ n ∈ Submodule.span ℂ (Set.range e)) :
    Ψ ∈ Submodule.span ℂ (Set.range fun J : ι → Fin d => tensorVec fun j => e (J j)) := by
  classical
  set V := Submodule.span ℂ (Set.range e)
  have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  obtain ⟨t, k, b, hbV, hbk, hk⟩ := exists_interpolation V
  -- the occupation with `nⱼ = k_{Kⱼ}`
  let occ : (ι → Fin t) → ι →₀ ℕ := fun K => Finsupp.equivFunOnFinite.symm fun j => k (K j)
  let Φ : FormalFock ι ℂ := ∑ K : ι → Fin t, Ψ.coeff (occ K) • tensorVec fun j => b (K j)
  have hΦ : Ψ = Φ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_fiber_mem hk (fun j n => ?_) (fun n hn => ?_)
    · rw [fiber_sub, fiber_sum]
      refine V.sub_mem (h j n) (V.sum_mem fun K _ => ?_)
      rw [fiber_smul, fiber_tensorVec]
      exact V.smul_mem _ (V.smul_mem _ (hbV _))
    · choose K' hK' using hn
      have hn' : n = occ K' := by
        ext j
        simp [occ, hK']
      rw [coeff_sub, coeff_sum, sum_eq_single K', hn', coeff_smul, coeff_tensorVec]
      · simp only [occ, Finsupp.coe_equivFunOnFinite_symm, hbk, ↓reduceIte,
          prod_const_one, smul_eq_mul, mul_one, sub_self]
      · intro K _ hK
        rw [hn', coeff_smul, coeff_tensorVec, prod_eq_zero_iff.mpr, smul_zero]
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hK
        refine ⟨j, mem_univ j, ?_⟩
        simp only [occ, Finsupp.coe_equivFunOnFinite_symm, hbk, hj, ↓reduceIte]
      · exact fun hK => absurd (mem_univ K') hK
  rw [hΦ]
  exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (tensorVec_mem_span fun j => hbV _)

end BosonicLean.Fock.FormalFock

/-! Deprecated names (B4.5, decision 5: standard terminology). -/

namespace BosonicLean.Fock.FormalFock

@[deprecated onMode_exp (since := "2026-10-19")]
alias onMode_raisingExp := onMode_exp
@[deprecated onMode_exp_gen (since := "2026-10-19")]
alias onMode_raisingExp_gen := onMode_exp_gen
@[deprecated commute_annihilate_exp_of_commute (since := "2026-10-19")]
alias commute_annihilate_raisingExp_of_commute := commute_annihilate_exp_of_commute
@[deprecated commute_annihilate_exp (since := "2026-10-19")]
alias commute_annihilate_raisingExp := commute_annihilate_exp

end BosonicLean.Fock.FormalFock
