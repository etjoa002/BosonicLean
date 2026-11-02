/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Analysis.UnitaryGroup
import BosonicLean.Weyl.GaussianUnitary

/-!
# Quadratic Hamiltonians on the bosonic Fock space

For a real symmetric `2N × 2N` matrix `K` and `f ∈ ℝ^{2N}`, the quadratic Hamiltonian
`H = ½ R̂ᵀ K R̂ + fᵀ R̂` acts on the formal Fock space. On the finitely supported vectors `𝒟` it
raises the particle number by at most two, with `‖Hψ‖ ≤ C_H (ν + 2) ‖ψ‖` for `ψ` vanishing above
`ν`, `C_H = Σ |K_kl| + √2 Σ |f_k|`; so the exponential series converges on `𝒟` with a radius
`1/(2C_H)` that does not depend on the vector. It is formally symmetric, and the adjoint of its
restriction to `𝒟` is its maximal realization `H̄`.

## Main definitions

* `BosonicLean.Fock.FockSpace.finiteSupport`: the finitely supported vectors `𝒟`.
* `BosonicLean.Fock.FockSpace.quadraticHamiltonian K f`: `H = ½ R̂ᵀ K R̂ + fᵀ R̂`.

## Main results

* Lemma 5 of the QH proposal: particle bounds, norm bounds, commutators, `(H|𝒟)† = H̄`.
-/

open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open Finset Matrix Gaussian Filter Topology

namespace BosonicLean.Fock

namespace FormalFock

variable {ι : Type*}

/-- `aⱼ` preserves a particle bound. -/
theorem VanishesAbove.annihilate {e : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove e ψ) (j : ι) :
    VanishesAbove e (annihilate j ψ) := by
  classical
  intro m hm
  rw [coeff_annihilate, h _ (by rw [map_add, Finsupp.degree_single]; omega), smul_zero]

/-- On a vector vanishing above `μ`, `‖aⱼψ‖² ≤ μ ‖ψ‖²`. -/
theorem sqNorm_annihilate_le {μ : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove μ ψ) (j : ι) :
    sqNorm (annihilate j ψ) ≤ μ * sqNorm ψ := by
  rw [FormalFock.sqNorm_annihilate, sqNorm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  by_cases hm : ψ.coeff m = 0
  · simp [hm]
  · have hdeg : m.degree ≤ μ := by
      by_contra hlt
      exact hm (h m (by omega))
    have hj : m j ≤ m.degree := by
      classical
      show m j ≤ ∑ i ∈ m.support, m i
      by_cases hjs : j ∈ m.support
      · exact Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) hjs
      · simp [Finsupp.notMem_support_iff.1 hjs]
    gcongr
    exact_mod_cast hj.trans hdeg

/-- On a vector vanishing above `μ`, `‖aⱼ†ψ‖² ≤ (μ + 1) ‖ψ‖²`. -/
theorem sqNorm_create_le {μ : ℕ} {ψ : FormalFock ι ℂ} (h : VanishesAbove μ ψ) (j : ι) :
    sqNorm (create j ψ) ≤ (μ + 1 : ℕ) * sqNorm ψ := by
  rw [FormalFock.sqNorm_create]
  calc sqNorm (annihilate j ψ) + sqNorm ψ ≤ μ * sqNorm ψ + sqNorm ψ := by
        gcongr; exact sqNorm_annihilate_le h j
    _ = (μ + 1 : ℕ) * sqNorm ψ := by push_cast; ring

end FormalFock

namespace FockSpace

open FormalFock

variable {n : ℕ}

/-- The **finitely supported vectors** `𝒟 ⊆ Γ_s`, spanned by the number states. -/
noncomputable def finiteSupport (ι : Type*) : Submodule ℂ (FockSpace ι) where
  carrier := {ψ | (Function.support ψ).Finite}
  add_mem' {ψ φ} hψ hφ := (hψ.union hφ).subset fun m hm => by
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hm (by rw [lp.coeFn_add, Pi.add_apply, h.1, h.2, add_zero])
  zero_mem' := by rw [Set.mem_setOf_eq, lp.coeFn_zero]; simp
  smul_mem' c ψ hψ := hψ.subset fun m hm => by
    by_contra h
    simp only [Function.mem_support, not_not] at h
    exact hm (by rw [lp.coeFn_smul, Pi.smul_apply, h, smul_zero])

theorem mem_finiteSupport_iff (ψ : FockSpace (Fin n)) :
    ψ ∈ finiteSupport (Fin n) ↔ ∃ e, VanishesAbove e (toFormal ψ) :=
  ⟨exists_vanishesAbove_of_finite, fun ⟨_, h⟩ => h.finite_support⟩

/-- A linear map `T` of the formal Fock space that keeps vectors with finitely many particles
with finitely many particles, as a map of `𝒟`. -/
theorem exists_onFinite (T : Module.End ℂ (FormalFock (Fin n) ℂ))
    (hT : ∀ e ψ, VanishesAbove e ψ → ∃ e', VanishesAbove e' (T ψ))
    (ψ : finiteSupport (Fin n)) :
    ∃ φ : FockSpace (Fin n), φ ∈ finiteSupport (Fin n) ∧ toFormal φ = T (toFormal ψ) := by
  obtain ⟨e, he⟩ := (mem_finiteSupport_iff _).1 ψ.2
  obtain ⟨e', he'⟩ := hT _ _ he
  obtain ⟨φ, hφ⟩ := exists_toFormal_eq_of_vanishesAbove he'
  exact ⟨φ, (mem_finiteSupport_iff _).2 ⟨e', hφ ▸ he'⟩, hφ⟩

/-- A linear map `T` of the formal Fock space that keeps vectors with finitely many particles
with finitely many particles, as a map of `𝒟`. -/
noncomputable def onFinite (T : Module.End ℂ (FormalFock (Fin n) ℂ))
    (hT : ∀ e ψ, VanishesAbove e ψ → ∃ e', VanishesAbove e' (T ψ)) :
    finiteSupport (Fin n) →ₗ[ℂ] finiteSupport (Fin n) where
  toFun ψ := ⟨(exists_onFinite T hT ψ).choose, (exists_onFinite T hT ψ).choose_spec.1⟩
  map_add' ψ φ := by
    refine Subtype.ext (toFormal_injective ?_)
    show toFormal (exists_onFinite T hT (ψ + φ)).choose =
      toFormal ((exists_onFinite T hT ψ).choose + (exists_onFinite T hT φ).choose)
    rw [map_add, (exists_onFinite T hT (ψ + φ)).choose_spec.2,
      (exists_onFinite T hT ψ).choose_spec.2, (exists_onFinite T hT φ).choose_spec.2,
      Submodule.coe_add, map_add, map_add]
  map_smul' c ψ := by
    refine Subtype.ext (toFormal_injective ?_)
    show toFormal (exists_onFinite T hT (c • ψ)).choose =
      toFormal (c • (exists_onFinite T hT ψ).choose)
    rw [map_smul, (exists_onFinite T hT (c • ψ)).choose_spec.2,
      (exists_onFinite T hT ψ).choose_spec.2, SetLike.val_smul, map_smul, map_smul]

theorem toFormal_onFinite (T : Module.End ℂ (FormalFock (Fin n) ℂ))
    (hT : ∀ e ψ, VanishesAbove e ψ → ∃ e', VanishesAbove e' (T ψ))
    (ψ : finiteSupport (Fin n)) :
    toFormal (onFinite T hT ψ : FockSpace (Fin n)) = T (toFormal ψ) :=
  (exists_onFinite T hT ψ).choose_spec.2

/-- The quadratures raise a particle bound by one. -/
theorem vanishesAbove_quadrature {e : ℕ} {ψ : FormalFock (Fin n) ℂ} (h : VanishesAbove e ψ)
    (k : PhaseIndex n) : VanishesAbove (e + 1) (FockSpace.quadrature k ψ) := by
  rcases k with j | j
  · simp only [FockSpace.quadrature, LinearMap.smul_apply, LinearMap.add_apply]
    exact (((h.annihilate j).mono (Nat.le_succ e)).add (h.create j)).smul _
  · simp only [FockSpace.quadrature, LinearMap.smul_apply, LinearMap.sub_apply]
    have h2 := ((h.create j).add (((h.annihilate j).mono (Nat.le_succ e)).smul (-1))).smul
      (Complex.I / (Real.sqrt 2 : ℂ))
    rwa [neg_one_smul, ← sub_eq_add_neg] at h2

/-! ### Norm bounds on particle-number sectors -/

/-- `T` maps each `χ ∈ Γ_s` vanishing above `μ` to a vector of `Γ_s` vanishing above `μ + k`,
of norm at most `c μ ‖χ‖`. -/
private def SectorBound (T : Module.End ℂ (FormalFock (Fin n) ℂ)) (k : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ (μ : ℕ) (χ : FockSpace (Fin n)), VanishesAbove μ (toFormal χ) →
    ∃ φ : FockSpace (Fin n), toFormal φ = T (toFormal χ) ∧ VanishesAbove (μ + k) (toFormal φ) ∧
      ‖φ‖ ≤ c μ * ‖χ‖

/-- From a bound of squared norms in `[0, ∞]` to a bound of norms. -/
theorem norm_le_of_sqNorm_le {φ χ : FockSpace (Fin n)} {c : ℝ} (hc : 0 ≤ c)
    (h : sqNorm (toFormal φ) ≤ ENNReal.ofReal c * sqNorm (toFormal χ)) :
    ‖φ‖ ≤ Real.sqrt c * ‖χ‖ := by
  rw [sqNorm_toFormal, sqNorm_toFormal, ← ENNReal.ofReal_mul hc,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg φ), ← Real.sqrt_sq (norm_nonneg χ), ← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt h

private theorem sectorBound_annihilate (j : Fin n) :
    SectorBound (annihilate j) 0 (fun μ => Real.sqrt μ) := fun μ χ hχ => by
  obtain ⟨φ, hφ⟩ := exists_toFormal_eq_of_vanishesAbove (hχ.annihilate j)
  refine ⟨φ, hφ, by rw [hφ, add_zero]; exact hχ.annihilate j, norm_le_of_sqNorm_le
    (Nat.cast_nonneg μ) ?_⟩
  rw [hφ, ENNReal.ofReal_natCast]
  exact sqNorm_annihilate_le hχ j

private theorem sectorBound_create (j : Fin n) :
    SectorBound (create j) 1 (fun μ => Real.sqrt (μ + 1)) := fun μ χ hχ => by
  obtain ⟨φ, hφ⟩ := exists_toFormal_eq_of_vanishesAbove (hχ.create j)
  refine ⟨φ, hφ, by rw [hφ]; exact hχ.create j, norm_le_of_sqNorm_le (by positivity) ?_⟩
  rw [hφ, show ((μ : ℝ) + 1) = ((μ + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  exact sqNorm_create_le hχ j

namespace SectorBound

variable {S T : Module.End ℂ (FormalFock (Fin n) ℂ)} {k k' : ℕ} {c c' : ℕ → ℝ}

private theorem mono (h : SectorBound T k c) (hk : k ≤ k') (hc : ∀ μ, c μ ≤ c' μ) :
    SectorBound T k' c' := fun μ χ hχ => by
  obtain ⟨φ, h1, h2, h3⟩ := h μ χ hχ
  exact ⟨φ, h1, h2.mono (by omega), h3.trans (by gcongr; exact hc μ)⟩

private theorem add (hS : SectorBound S k c) (hT : SectorBound T k c') :
    SectorBound (S + T) k (c + c') := fun μ χ hχ => by
  obtain ⟨φ, h1, h2, h3⟩ := hS μ χ hχ
  obtain ⟨φ', h1', h2', h3'⟩ := hT μ χ hχ
  refine ⟨φ + φ', by rw [map_add, h1, h1', LinearMap.add_apply], by
    rw [map_add]; exact h2.add h2', (norm_add_le _ _).trans ?_⟩
  rw [Pi.add_apply, add_mul]
  exact add_le_add h3 h3'

private theorem smul (hT : SectorBound T k c) (z : ℂ) :
    SectorBound (z • T) k (fun μ => ‖z‖ * c μ) := fun μ χ hχ => by
  obtain ⟨φ, h1, h2, h3⟩ := hT μ χ hχ
  refine ⟨z • φ, by rw [map_smul, h1, LinearMap.smul_apply], by
    rw [map_smul]; exact h2.smul z, ?_⟩
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 (norm_nonneg z)

private theorem zero : SectorBound (0 : Module.End ℂ (FormalFock (Fin n) ℂ)) k 0 := fun μ χ _ =>
  ⟨0, by simp, by rw [map_zero]; exact fun _ _ => rfl, by simp⟩

private theorem sum {κ : Type*} (s : Finset κ) {T : κ → Module.End ℂ (FormalFock (Fin n) ℂ)}
    {c : κ → ℕ → ℝ} (h : ∀ i ∈ s, SectorBound (T i) k (c i)) :
    SectorBound (∑ i ∈ s, T i) k (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (k := k))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem mul (hS : SectorBound S k c) (hT : SectorBound T k' c') (hc : ∀ μ, 0 ≤ c μ) :
    SectorBound (S * T) (k' + k) (fun μ => c (μ + k') * c' μ) := fun μ χ hχ => by
  obtain ⟨φ, h1, h2, h3⟩ := hT μ χ hχ
  obtain ⟨ψ, h1', h2', h3'⟩ := hS (μ + k') φ h2
  refine ⟨ψ, by rw [h1', h1, Module.End.mul_apply], by rw [← add_assoc]; exact h2', ?_⟩
  calc ‖ψ‖ ≤ c (μ + k') * ‖φ‖ := h3'
    _ ≤ c (μ + k') * (c' μ * ‖χ‖) := mul_le_mul_of_nonneg_left h3 (hc _)
    _ = c (μ + k') * c' μ * ‖χ‖ := by ring

private theorem pow (hT : SectorBound T k c) (hc : ∀ μ, 0 ≤ c μ) (m : ℕ) :
    SectorBound (T ^ m) (k * m) (fun μ => ∏ j ∈ range m, c (μ + k * j)) := by
  induction m with
  | zero => exact fun μ χ hχ => ⟨χ, by simp, by simpa using hχ, by simp⟩
  | succ m ih =>
    rw [pow_succ']
    refine (hT.mul ih hc).mono (by ring_nf; omega) fun μ => ?_
    rw [prod_range_succ, mul_comm]

/-- A sector bound gives the hypothesis of `onFinite`. -/
private theorem exists_vanishesAbove (hT : SectorBound T k c) (e : ℕ) (ψ : FormalFock (Fin n) ℂ)
    (hψ : VanishesAbove e ψ) : ∃ e', VanishesAbove e' (T ψ) := by
  obtain ⟨χ, hχ⟩ := exists_toFormal_eq_of_vanishesAbove hψ
  obtain ⟨φ, h1, h2, -⟩ := hT e χ (hχ ▸ hψ)
  exact ⟨e + k, by rw [← hχ, ← h1]; exact h2⟩

end SectorBound

private theorem sectorBound_quadrature (k : PhaseIndex n) :
    SectorBound (quadrature k) 1 (fun μ => Real.sqrt 2 * Real.sqrt (μ + 1)) := by
  have hs2 : ‖((Real.sqrt 2 : ℂ))⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have hs2' : ‖Complex.I / (Real.sqrt 2 : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
      one_div]
  have key : ∀ μ : ℕ, (Real.sqrt 2)⁻¹ * (Real.sqrt μ + Real.sqrt (μ + 1)) ≤
      Real.sqrt 2 * Real.sqrt (μ + 1) := fun μ => by
    have h1 : Real.sqrt μ ≤ Real.sqrt (μ + 1) := Real.sqrt_le_sqrt (by linarith)
    have h2 : 0 < Real.sqrt 2 := by positivity
    rw [inv_mul_le_iff₀ h2, ← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  rcases k with j | j
  · have ha := (sectorBound_annihilate j).mono (Nat.zero_le 1) (fun _ => le_refl _)
    have h := (ha.add (sectorBound_create j)).smul ((Real.sqrt 2 : ℂ)⁻¹)
    refine h.mono le_rfl fun μ => ?_
    simp only [Pi.add_apply, hs2]
    exact key μ
  · have ha := ((sectorBound_annihilate j).mono (Nat.zero_le 1) (fun _ => le_refl _)).smul (-1)
    have h := ((sectorBound_create j).add ha).smul (Complex.I / (Real.sqrt 2 : ℂ))
    have heq : (quadrature (Sum.inr j) : Module.End ℂ (FormalFock (Fin n) ℂ)) =
        (Complex.I / (Real.sqrt 2 : ℂ)) • (create j + (-1 : ℂ) • annihilate j) := by
      simp [quadrature, sub_eq_add_neg]
    rw [heq]
    refine h.mono le_rfl fun μ => ?_
    simp only [Pi.add_apply, hs2', norm_neg, norm_one, one_mul]
    rw [add_comm]
    exact key μ

/-! ### The quadratic Hamiltonian -/

/-- **Definition 4.** The quadratic Hamiltonian `H = ½ R̂ᵀ K R̂ + fᵀ R̂` on the formal Fock space. -/
noncomputable def quadraticHamiltonian (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : Module.End ℂ (FormalFock (Fin n) ℂ) :=
  ∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l) + ∑ k, (f k : ℂ) • quadrature k

/-- The constant `C_H = Σ |K_kl| + √2 Σ |f_k|` of Lemma 5(a). -/
noncomputable def quadraticBound (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : ℝ :=
  ∑ k, ∑ l, |K k l| + Real.sqrt 2 * ∑ k, |f k|

theorem quadraticBound_nonneg (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : 0 ≤ quadraticBound K f := by
  unfold quadraticBound; positivity

/-- **Lemma 5(a).** `H` raises a particle bound by two, with `‖Hψ‖ ≤ C_H (ν + 2) ‖ψ‖`. -/
private theorem sectorBound_quadraticHamiltonian (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) :
    SectorBound (quadraticHamiltonian K f) 2 (fun μ => quadraticBound K f * (μ + 2)) := by
  have hq : ∀ k : PhaseIndex n, SectorBound (quadrature k) 1
      (fun μ => Real.sqrt 2 * Real.sqrt (μ + 1)) := sectorBound_quadrature
  have hpos : ∀ μ : ℕ, 0 ≤ Real.sqrt 2 * Real.sqrt (μ + 1) := fun _ => by positivity
  -- the quadratic terms
  have hkl : ∀ k l, SectorBound (((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l)) 2
      (fun μ => |K k l| * (μ + 2)) := fun k l => by
    refine ((hq k).mul (hq l) hpos).smul _ |>.mono le_rfl fun μ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
    have h : Real.sqrt 2 * Real.sqrt (↑(μ + 1) + 1) * (Real.sqrt 2 * Real.sqrt (↑μ + 1)) ≤
        2 * (μ + 2) := by
      have e1 : Real.sqrt 2 * Real.sqrt (↑(μ + 1) + 1) * (Real.sqrt 2 * Real.sqrt (↑μ + 1)) =
          2 * (Real.sqrt (↑(μ + 1) + 1) * Real.sqrt (↑μ + 1)) := by
        rw [show Real.sqrt 2 * Real.sqrt (↑(μ + 1) + 1) * (Real.sqrt 2 * Real.sqrt (↑μ + 1)) =
          (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt (↑(μ + 1) + 1) * Real.sqrt (↑μ + 1)) by ring,
          Real.mul_self_sqrt (by norm_num)]
      rw [e1]
      have h2 : Real.sqrt (↑(μ + 1) + 1) * Real.sqrt (↑μ + 1) ≤ μ + 2 := by
        rw [← Real.sqrt_mul (by positivity)]
        refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
        push_cast; nlinarith
      linarith
    calc |K k l| / 2 * (Real.sqrt 2 * Real.sqrt (↑(μ + 1) + 1) * (Real.sqrt 2 * Real.sqrt (↑μ + 1)))
        ≤ |K k l| / 2 * (2 * (μ + 2)) := by gcongr
      _ = |K k l| * (μ + 2) := by ring
  -- the linear terms
  have hk : ∀ k, SectorBound ((f k : ℂ) • quadrature k) 2
      (fun μ => Real.sqrt 2 * |f k| * (μ + 2)) := fun k => by
    refine ((hq k).smul _).mono (by norm_num) fun μ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h : Real.sqrt (μ + 1) ≤ μ + 2 := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith
    calc |f k| * (Real.sqrt 2 * Real.sqrt (μ + 1)) ≤ |f k| * (Real.sqrt 2 * (μ + 2)) := by gcongr
      _ = Real.sqrt 2 * |f k| * (μ + 2) := by ring
  have h := (SectorBound.sum univ fun k _ => SectorBound.sum univ fun l _ => hkl k l).add
    (SectorBound.sum univ fun k _ => hk k)
  refine h.mono le_rfl fun μ => le_of_eq ?_
  simp only [Pi.add_apply, Finset.sum_apply, quadraticBound]
  rw [add_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.sum_mul]

/-- The quadratures keep vectors with finitely many particles with finitely many particles. -/
theorem exists_vanishesAbove_quadrature (k : PhaseIndex n) (e : ℕ) (ψ : FormalFock (Fin n) ℂ)
    (h : VanishesAbove e ψ) : ∃ e', VanishesAbove e' (quadrature k ψ) :=
  ⟨e + 1, vanishesAbove_quadrature h k⟩

/-- **Lemma 5(a).** If `ψ ∈ Γ_s` vanishes above `ν` particles, then `Hψ = φ` for some `φ ∈ Γ_s`
vanishing above `ν + 2` with `‖φ‖ ≤ C_H (ν + 2) ‖ψ‖`. -/
theorem exists_toFormal_eq_quadraticHamiltonian (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) {ν : ℕ} {ψ : FockSpace (Fin n)} (hψ : VanishesAbove ν (toFormal ψ)) :
    ∃ φ : FockSpace (Fin n), toFormal φ = quadraticHamiltonian K f (toFormal ψ) ∧
      VanishesAbove (ν + 2) (toFormal φ) ∧ ‖φ‖ ≤ quadraticBound K f * (ν + 2) * ‖ψ‖ :=
  sectorBound_quadraticHamiltonian K f ν ψ hψ

/-- `Π_{j<m} (μ + 2j + 2) ≤ 2^m m! (μ+m choose m)`. -/
private theorem prod_le_choose (μ m : ℕ) :
    (∏ j ∈ range m, ((μ : ℝ) + 2 * j + 2)) ≤
      2 ^ m * (m.factorial : ℝ) * ((m + μ).choose μ : ℝ) := by
  have h1 : (∏ j ∈ range m, ((μ : ℝ) + 2 * j + 2)) ≤ ∏ j ∈ range m, (2 * ((μ : ℝ) + 1 + j)) :=
    Finset.prod_le_prod₀ (h0 := fun _ _ => by positivity) (h1 := fun j _ => by
      have : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
      linarith)
  have h2 : (∏ j ∈ range m, (2 * ((μ : ℝ) + 1 + j))) =
      2 ^ m * ((μ + 1).ascFactorial m : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Nat.ascFactorial_eq_prod_range]
    push_cast
    ring_nf
  have hc : (μ + m).choose m = (m + μ).choose μ := by rw [Nat.add_comm μ m, Nat.choose_symm_add]
  rw [h2, Nat.ascFactorial_eq_factorial_mul_choose, hc] at h1
  push_cast at h1
  linarith

end FockSpace

/-! ### Formal symmetry -/

namespace FormalFock

variable {ι : Type*}

/-- `⟨aⱼ φ, ψ⟩ = ⟨φ, aⱼ† ψ⟩` for finitely supported `φ` and every `ψ`. -/
theorem pairing_annihilate (j : ι) {φ : FormalFock ι ℂ}
    (hφ : (Function.support φ.coeff).Finite) (ψ : FormalFock ι ℂ) :
    pairing (annihilate j φ) ψ = pairing φ (create j ψ) := by
  classical
  set s := hφ.toFinset
  have hs : Function.support φ.coeff ⊆ s := by simp [s]
  set t := (s.filter fun m => 0 < m j).image (· - Finsupp.single j 1)
  have ht : Function.support (annihilate j φ).coeff ⊆ t := by
    intro n hn
    rw [Function.mem_support, coeff_annihilate] at hn
    have h0 : φ.coeff (n + Finsupp.single j 1) ≠ 0 := fun h => hn (by rw [h, smul_zero])
    refine mem_image.2 ⟨n + Finsupp.single j 1, mem_filter.2 ⟨hs h0, by simp⟩,
      add_single_sub_single n j⟩
  have hinj : Set.InjOn (· - Finsupp.single j 1) (s.filter fun m => 0 < m j) :=
    fun a ha b hb hab => by
      have ha' := (mem_filter.1 ha).2
      have hb' := (mem_filter.1 hb).2
      rw [← sub_single_add_single ha', ← sub_single_add_single hb']
      exact congrArg (· + Finsupp.single j 1) hab
  rw [pairing_eq_sum ht, pairing_eq_sum hs, sum_image hinj, ← sum_filter_add_sum_filter_not s
    (fun m => 0 < m j)]
  have hzero : ∑ m ∈ s.filter (fun m => ¬0 < m j), conj (φ.coeff m) * (create j ψ).coeff m = 0 :=
    sum_eq_zero fun m hm => by rw [coeff_create, if_neg (mem_filter.1 hm).2, mul_zero]
  rw [hzero, add_zero]
  refine sum_congr rfl fun m hm => ?_
  have hpos := (mem_filter.1 hm).2
  have hj : (m - Finsupp.single j 1 : ι →₀ ℕ) j + 1 = m j := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
  rw [coeff_annihilate, sub_single_add_single hpos, hj, coeff_create, if_pos hpos, smul_eq_mul,
    smul_eq_mul, map_mul, sqrtC, Complex.conj_ofReal]
  ring

/-- `S` and `T` are formal adjoints of each other on finitely supported vectors: `S` keeps them
finitely supported, and `⟨Sφ, ψ⟩ = ⟨φ, Tψ⟩` for finitely supported `φ` and every `ψ`. -/
private def PairingAdjoint (S T : Module.End ℂ (FormalFock ι ℂ)) : Prop :=
  ∀ φ : FormalFock ι ℂ, (Function.support φ.coeff).Finite →
    (Function.support (S φ).coeff).Finite ∧ ∀ ψ, pairing (S φ) ψ = pairing φ (T ψ)

namespace PairingAdjoint

variable {S S' T T' : Module.End ℂ (FormalFock ι ℂ)}

private theorem create (j : ι) :
    PairingAdjoint (FormalFock.create j) (FormalFock.annihilate j : Module.End ℂ _) :=
  fun _ hφ => ⟨finite_support_create j hφ, pairing_create j hφ⟩

private theorem annihilate (j : ι) :
    PairingAdjoint (FormalFock.annihilate j) (FormalFock.create j : Module.End ℂ _) :=
  fun φ hφ => ⟨(hφ.image (· - Finsupp.single j 1)).subset fun n hn => by
      classical
      rw [Function.mem_support, coeff_annihilate] at hn
      exact ⟨n + Finsupp.single j 1, fun h => hn (by rw [h, smul_zero]),
        add_single_sub_single n j⟩,
    pairing_annihilate j hφ⟩

private theorem add (h : PairingAdjoint S T) (h' : PairingAdjoint S' T') :
    PairingAdjoint (S + S') (T + T') := fun φ hφ => by
  obtain ⟨h1, h2⟩ := h φ hφ
  obtain ⟨h1', h2'⟩ := h' φ hφ
  refine ⟨finite_support_add h1 h1', fun ψ => ?_⟩
  rw [LinearMap.add_apply, LinearMap.add_apply, pairing_add_left h1 h1', h2, h2',
    pairing_add_right hφ]

private theorem smul (h : PairingAdjoint S T) (c : ℂ) : PairingAdjoint (c • S) (conj c • T) :=
  fun φ hφ => by
  obtain ⟨h1, h2⟩ := h φ hφ
  refine ⟨finite_support_smul c h1, fun ψ => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, pairing_smul_left c h1, h2,
    pairing_smul_right hφ]

private theorem mul (h : PairingAdjoint S T) (h' : PairingAdjoint S' T') :
    PairingAdjoint (S * S') (T' * T) := fun φ hφ => by
  obtain ⟨h1', h2'⟩ := h' φ hφ
  obtain ⟨h1, h2⟩ := h (S' φ) h1'
  exact ⟨h1, fun ψ => by rw [Module.End.mul_apply, h2, h2', Module.End.mul_apply]⟩

private theorem zero : PairingAdjoint (0 : Module.End ℂ (FormalFock ι ℂ)) 0 := fun φ _ =>
  ⟨by
    rw [LinearMap.zero_apply]
    exact Set.finite_empty.subset fun n hn => hn (coeff_zero n),
   fun ψ => by simp [pairing]⟩

private theorem sum {κ : Type*} (s : Finset κ) {S T : κ → Module.End ℂ (FormalFock ι ℂ)}
    (h : ∀ i ∈ s, PairingAdjoint (S i) (T i)) :
    PairingAdjoint (∑ i ∈ s, S i) (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

end PairingAdjoint

end FormalFock

namespace FockSpace

open FormalFock

variable {n : ℕ}

private theorem pairingAdjoint_quadrature (k : PhaseIndex n) :
    PairingAdjoint (quadrature k) (quadrature k) := by
  have hs : conj ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rcases k with j | j
  · have h := ((PairingAdjoint.annihilate j).add (PairingAdjoint.create j)).smul
      ((Real.sqrt 2 : ℂ)⁻¹)
    rw [hs, add_comm (create j : Module.End ℂ _)] at h
    exact h
  · have h := ((PairingAdjoint.create j).add
      ((PairingAdjoint.annihilate j).smul (-1))).smul (Complex.I / (Real.sqrt 2 : ℂ))
    have e1 : conj (Complex.I / (Real.sqrt 2 : ℂ)) = -(Complex.I / (Real.sqrt 2 : ℂ)) := by
      rw [map_div₀, Complex.conj_I, Complex.conj_ofReal, neg_div]
    have e2 : (quadrature (Sum.inr j) : Module.End ℂ (FormalFock (Fin n) ℂ)) =
        (Complex.I / (Real.sqrt 2 : ℂ)) • (create j + (-1 : ℂ) • annihilate j) := by
      simp [quadrature, sub_eq_add_neg]
    rw [e1, map_neg, map_one] at h
    rw [e2]
    convert h using 1
    module

/-- **Lemma 5(a)**, formal symmetry: `⟨Hφ, ψ⟩ = ⟨φ, Hψ⟩` for finitely supported `φ`. -/
private theorem pairingAdjoint_quadraticHamiltonian {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ) :
    PairingAdjoint (quadraticHamiltonian K f) (quadraticHamiltonian K f) := by
  have hq := pairingAdjoint_quadrature (n := n)
  have h1 : ∀ k l : PhaseIndex n, PairingAdjoint
      (((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l))
      (conj (((K k l / 2 : ℝ) : ℂ)) • (quadrature l * quadrature k)) := fun k l =>
    ((hq k).mul (hq l)).smul _
  have h2 : ∀ k : PhaseIndex n, PairingAdjoint ((f k : ℂ) • quadrature k)
      (conj (f k : ℂ) • quadrature k) := fun k => (hq k).smul _
  have h := (PairingAdjoint.sum (univ : Finset (PhaseIndex n)) fun k _ =>
    PairingAdjoint.sum (univ : Finset (PhaseIndex n)) fun l _ => h1 k l).add
    (PairingAdjoint.sum (univ : Finset (PhaseIndex n)) fun k _ => h2 k)
  simp only [Complex.conj_ofReal] at h
  have heq : quadraticHamiltonian K f = ∑ x : PhaseIndex n, ∑ y : PhaseIndex n,
      ((K x y / 2 : ℝ) : ℂ) • (quadrature y * quadrature x) + ∑ k, (f k : ℂ) • quadrature k := by
    rw [show (∑ x : PhaseIndex n, ∑ y : PhaseIndex n, ((K x y / 2 : ℝ) : ℂ) •
        (quadrature y * quadrature x : Module.End ℂ (FormalFock (Fin n) ℂ))) =
        ∑ y : PhaseIndex n, ∑ x : PhaseIndex n, ((K x y / 2 : ℝ) : ℂ) •
        (quadrature y * quadrature x : Module.End ℂ (FormalFock (Fin n) ℂ)) from Finset.sum_comm]
    simp only [quadraticHamiltonian, add_left_inj]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hK.apply k l]
  rw [← heq] at h
  exact h

/-- For finitely supported `x`, the inner product is the pairing of formal vectors. -/
theorem inner_eq_pairing {ι : Type*} {x : FockSpace ι} (hx : (Function.support x).Finite)
    (y : FockSpace ι) : ⟪x, y⟫_ℂ = pairing (toFormal x) (toFormal y) := by
  classical
  have hs : Function.support (toFormal x).coeff ⊆ hx.toFinset := by simp
  rw [pairing_eq_sum hs, lp.inner_eq_tsum, tsum_eq_sum (s := hx.toFinset) fun m hm => by
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hm
    rw [hm, inner_zero_left]]
  exact Finset.sum_congr rfl fun m _ => RCLike.inner_apply' _ _

theorem finite_support_coe {ι : Type*} (ψ : finiteSupport ι) :
    (Function.support (ψ : FockSpace ι)).Finite := ψ.2

theorem finite_support_toFormal_coe {ι : Type*} (ψ : finiteSupport ι) :
    (Function.support (toFormal (ψ : FockSpace ι)).coeff).Finite := ψ.2

/-! ### `H` on the finitely supported vectors -/

/-- `H` as a linear map of `𝒟`. -/
noncomputable def quadraticHamiltonianOnFinite (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : finiteSupport (Fin n) →ₗ[ℂ] finiteSupport (Fin n) :=
  onFinite (quadraticHamiltonian K f) (sectorBound_quadraticHamiltonian K f).exists_vanishesAbove

theorem toFormal_quadraticHamiltonianOnFinite_pow (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) (m : ℕ) (χ : finiteSupport (Fin n)) :
    toFormal ((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n)) =
      (quadraticHamiltonian K f ^ m) (toFormal χ) := by
  induction m generalizing χ with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, quadraticHamiltonianOnFinite, toFormal_onFinite,
      ← quadraticHamiltonianOnFinite, ih, pow_succ', Module.End.mul_apply]

/-- **Lemma 5(a)**, symmetry on `𝒟`. -/
theorem inner_quadraticHamiltonianOnFinite {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ) (x y : finiteSupport (Fin n)) :
    ⟪(quadraticHamiltonianOnFinite K f x : FockSpace (Fin n)), (y : FockSpace (Fin n))⟫_ℂ =
      ⟪(x : FockSpace (Fin n)), (quadraticHamiltonianOnFinite K f y : FockSpace (Fin n))⟫_ℂ := by
  have h1 := toFormal_quadraticHamiltonianOnFinite_pow K f 1 x
  have h2 := toFormal_quadraticHamiltonianOnFinite_pow K f 1 y
  rw [pow_one, pow_one] at h1 h2
  rw [inner_eq_pairing (finite_support_coe _), inner_eq_pairing (finite_support_coe x), h1, h2]
  exact ((pairingAdjoint_quadraticHamiltonian hK f) _ (finite_support_toFormal_coe x)).2 _

/-- **Lemma 5(a)**, the common radius: for `0 ≤ ρ` with `2 C_H ρ < 1`, the exponential series
of `H` converges absolutely at `ρ` on every finitely supported vector. -/
theorem summable_quadraticHamiltonianOnFinite (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : 2 * quadraticBound K f * ρ < 1)
    (χ : finiteSupport (Fin n)) :
    Summable fun m : ℕ => ρ ^ m / m.factorial *
      ‖((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n))‖ := by
  set C := quadraticBound K f
  have hC := quadraticBound_nonneg K f
  obtain ⟨μ, hμ⟩ := (mem_finiteSupport_iff _).1 χ.2
  have hbound : ∀ m : ℕ, ‖((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n))‖ ≤
      C ^ m * (2 ^ m * (m.factorial : ℝ) * ((m + μ).choose μ : ℝ)) * ‖(χ : FockSpace (Fin n))‖ :=
    fun m => by
    obtain ⟨φ, h1, -, h3⟩ := ((sectorBound_quadraticHamiltonian K f).pow
      (fun μ => by positivity) m) μ χ hμ
    have hφ : φ = ((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n)) :=
      toFormal_injective (by rw [h1, toFormal_quadraticHamiltonianOnFinite_pow])
    rw [← hφ]
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    show (∏ j ∈ range m, quadraticBound K f * (((μ + 2 * j : ℕ) : ℝ) + 2)) ≤ _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    gcongr
    refine le_of_eq_of_le (Finset.prod_congr rfl fun j _ => ?_) (prod_le_choose μ m)
    push_cast; ring
  have hs := (summable_choose_mul_geometric_of_norm_lt_one μ
    (r := 2 * C * ρ) (by rw [Real.norm_of_nonneg (by positivity)]; exact h)).mul_right
    ‖(χ : FockSpace (Fin n))‖
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  calc ρ ^ m / m.factorial * ‖((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n))‖
      ≤ ρ ^ m / m.factorial * (C ^ m * (2 ^ m * (m.factorial : ℝ) * ((m + μ).choose μ : ℝ)) *
        ‖(χ : FockSpace (Fin n))‖) := by gcongr; exact hbound m
    _ = ((m + μ).choose μ : ℝ) * (2 * C * ρ) ^ m * ‖(χ : FockSpace (Fin n))‖ := by
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- **Lemma 5(c)**, one inclusion: on `dom H̄`, `⟪H̄ψ, φ⟫ = ⟪ψ, Hφ⟫` for `φ ∈ 𝒟`. -/
theorem inner_maxRealization_quadraticHamiltonian {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    (ψ : (maxRealization (quadraticHamiltonian K f)).domain) (φ : finiteSupport (Fin n)) :
    ⟪maxRealization (quadraticHamiltonian K f) ψ, (φ : FockSpace (Fin n))⟫_ℂ =
      ⟪(ψ : FockSpace (Fin n)), (quadraticHamiltonianOnFinite K f φ : FockSpace (Fin n))⟫_ℂ := by
  have h1 := toFormal_quadraticHamiltonianOnFinite_pow K f 1 φ
  rw [pow_one] at h1
  calc ⟪maxRealization (quadraticHamiltonian K f) ψ, (φ : FockSpace (Fin n))⟫_ℂ
      = conj ⟪(φ : FockSpace (Fin n)), maxRealization (quadraticHamiltonian K f) ψ⟫_ℂ :=
        (inner_conj_symm _ _).symm
    _ = conj (pairing (quadraticHamiltonian K f (toFormal (φ : FockSpace (Fin n))))
          (toFormal (ψ : FockSpace (Fin n)))) := by
        rw [inner_eq_pairing (finite_support_coe φ), toFormal_maxRealization,
          ((pairingAdjoint_quadraticHamiltonian hK f) _ (finite_support_toFormal_coe φ)).2]
    _ = conj ⟪(quadraticHamiltonianOnFinite K f φ : FockSpace (Fin n)),
          (ψ : FockSpace (Fin n))⟫_ℂ := by
        rw [inner_eq_pairing (finite_support_coe _), h1, pow_one]
    _ = _ := inner_conj_symm _ _

/-! ### Lemma 5(b): commutators -/

section Commutators

local notation "𝔼" => Module.End ℂ (FormalFock (Fin n) ℂ)

theorem annihilate_mul_create (i j : Fin n) :
    (annihilate i : 𝔼) * create j = create j * annihilate i + if i = j then 1 else 0 := by
  have h := lie_annihilate_create (R := ℂ) i j
  rw [Ring.lie_def] at h
  rw [← h]; abel

theorem annihilate_mul_annihilate (i j : Fin n) :
    (annihilate i : 𝔼) * annihilate j = annihilate j * annihilate i := by
  have h := lie_annihilate_annihilate (R := ℂ) i j
  rwa [Ring.lie_def, sub_eq_zero] at h

theorem create_mul_create (i j : Fin n) :
    (create i : 𝔼) * create j = create j * create i := by
  have h := lie_create_create (R := ℂ) i j
  rwa [Ring.lie_def, sub_eq_zero] at h

/-- **Lemma 5(b)**, the canonical commutation relations `[R̂_k, R̂_l] = iΩ_kl`. -/
theorem quadrature_mul_sub (k l : PhaseIndex n) :
    (quadrature k : 𝔼) * quadrature l - quadrature l * quadrature k =
      (Complex.I * (symplecticForm n k l : ℂ)) • 1 := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs' : (Complex.I / (Real.sqrt 2 : ℂ)) * (Complex.I / (Real.sqrt 2 : ℂ)) = -1 / 2 := by
    rw [div_mul_div_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs'' : ((Real.sqrt 2 : ℂ))⁻¹ * (Complex.I / (Real.sqrt 2 : ℂ)) = Complex.I / 2 := by
    rw [mul_div_assoc', inv_mul_eq_div, div_div, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs''' : (Complex.I / (Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ))⁻¹ = Complex.I / 2 := by
    rw [mul_comm, hs'']
  rw [symplecticForm_eq_fromBlocks]
  rcases k with i | i <;> rcases l with j | j <;>
    simp only [quadrature, smul_mul_smul_comm, hs, hs', hs'', hs''', fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.one_apply, Matrix.neg_apply, add_mul, mul_add, sub_mul, mul_sub,
      annihilate_mul_create, annihilate_mul_annihilate i j, create_mul_create i j] <;>
    by_cases hij : i = j <;> simp [hij, eq_comm (a := j), annihilate_mul_create] <;> module

/-- The field `Φ_v = σ(v, R̂) = Σ_k (Ωᵀv)_k R̂_k`, with `D(α(v)) = e^{-iΦ_v}`. -/
noncomputable def field (v : PhaseIndex n → ℝ) : 𝔼 :=
  ∑ k, ((((symplecticForm n)ᵀ *ᵥ v) k : ℝ) : ℂ) • quadrature k

/-- The commutator with a sum of multiples is the sum of multiples of commutators. -/
theorem mul_sum_smul_sub {κ : Type*} (s : Finset κ) (X : 𝔼) (c : κ → ℂ) (Y : κ → 𝔼) :
    X * (∑ i ∈ s, c i • Y i) - (∑ i ∈ s, c i • Y i) * X = ∑ i ∈ s, c i • (X * Y i - Y i * X) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem sum_smul_mul_sub {κ : Type*} (s : Finset κ) (X : 𝔼) (c : κ → ℂ) (Y : κ → 𝔼) :
    (∑ i ∈ s, c i • Y i) * X - X * (∑ i ∈ s, c i • Y i) = ∑ i ∈ s, c i • (Y i * X - X * Y i) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- `Σ_k (Ωᵀv)_k Ω_kl = -v_l`. -/
theorem sum_transpose_mulVec_mul_symplecticForm (v : PhaseIndex n → ℝ) (l : PhaseIndex n) :
    ∑ k, ((symplecticForm n)ᵀ *ᵥ v) k * symplecticForm n k l = -v l := by
  have h1 : ∑ k, ((symplecticForm n)ᵀ *ᵥ v) k * symplecticForm n k l =
      ((symplecticForm n)ᵀ *ᵥ ((symplecticForm n)ᵀ *ᵥ v)) l := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h1, Matrix.mulVec_mulVec, transpose_symplecticForm, neg_mul_neg, symplecticForm_sq,
    Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply]

/-- `[Φ_v, R̂_l] = -i v_l`. -/
theorem field_mul_quadrature_sub (v : PhaseIndex n → ℝ) (l : PhaseIndex n) :
    field v * quadrature l - quadrature l * field v = (-Complex.I * (v l : ℂ)) • 1 := by
  rw [field, sum_smul_mul_sub]
  simp only [quadrature_mul_sub, smul_smul, ← Finset.sum_smul]
  congr 1
  have h := sum_transpose_mulVec_mul_symplecticForm v l
  have h' : ∑ k, ((((symplecticForm n)ᵀ *ᵥ v) k : ℝ) : ℂ) * (symplecticForm n k l : ℂ) =
      -(v l : ℂ) := by exact_mod_cast h
  rw [show ∑ k, ((((symplecticForm n)ᵀ *ᵥ v) k : ℝ) : ℂ) * (Complex.I * (symplecticForm n k l : ℂ))
      = Complex.I * ∑ k, ((((symplecticForm n)ᵀ *ᵥ v) k : ℝ) : ℂ) * (symplecticForm n k l : ℂ) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, h']
  ring

theorem mul_sum_sub {κ : Type*} (s : Finset κ) (X : 𝔼) (Y : κ → 𝔼) :
    X * (∑ i ∈ s, Y i) - (∑ i ∈ s, Y i) * X = ∑ i ∈ s, (X * Y i - Y i * X) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- `Φ_w = Σ_m (Ωᵀw)_m R̂_m`; for `w = ΩKv` this is `Σ_m (Kv)_m R̂_m`. -/
theorem field_symplecticForm_mul_mulVec (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (v : PhaseIndex n → ℝ) :
    field ((symplecticForm n * K) *ᵥ v) = ∑ m, (((K *ᵥ v) m : ℝ) : ℂ) • quadrature m := by
  rw [field, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, transpose_symplecticForm, neg_mul,
    symplecticForm_sq, neg_neg, Matrix.one_mul]

/-- **Lemma 5(b).** `[Φ_v, H] = -i (Φ_{ΩKv} + fᵀv)`. -/
theorem field_mul_quadraticHamiltonian_sub {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}
    (hK : K.IsSymm) (f : PhaseIndex n → ℝ) (v : PhaseIndex n → ℝ) :
    field v * quadraticHamiltonian K f - quadraticHamiltonian K f * field v =
      (-Complex.I) • (field ((symplecticForm n * K) *ᵥ v) + ((f ⬝ᵥ v : ℝ) : ℂ) • 1) := by
  have hX := field_mul_quadrature_sub (n := n) v
  have hprod : ∀ k l : PhaseIndex n, field v * (quadrature k * quadrature l) -
      (quadrature k * quadrature l) * field v =
      (-Complex.I * (v k : ℂ)) • quadrature l + (-Complex.I * (v l : ℂ)) • quadrature k :=
    fun k l => by
    have e : field v * (quadrature k * quadrature l) - (quadrature k * quadrature l) * field v =
        (field v * quadrature k - quadrature k * field v) * quadrature l +
          quadrature k * (field v * quadrature l - quadrature l * field v) := by noncomm_ring
    rw [e, hX, hX, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, add_comm]
  have hS2 : field v * (∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l)) -
      (∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l)) * field v =
      ∑ m, (-Complex.I * ((K *ᵥ v) m : ℂ)) • quadrature m := by
    rw [mul_sum_sub]
    simp only [mul_sum_smul_sub, hprod, smul_add, smul_smul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => (((K k l / 2 : ℝ) : ℂ) * (-Complex.I * (v k : ℂ))) •
      quadrature l)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul, ← Finset.sum_smul, ← add_smul]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show K k m = K m k from (hK.apply k m).symm ▸ rfl]
    ring
  have hS1 : field v * (∑ k, (f k : ℂ) • quadrature k) - (∑ k, (f k : ℂ) • quadrature k) *
      field v = (-Complex.I * ((f ⬝ᵥ v : ℝ) : ℂ)) • 1 := by
    rw [mul_sum_smul_sub]
    simp only [hX, smul_smul, ← Finset.sum_smul]
    congr 1
    simp only [dotProduct]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e : field v * quadraticHamiltonian K f - quadraticHamiltonian K f * field v =
      (field v * (∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l)) -
        (∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (quadrature k * quadrature l)) * field v) +
      (field v * (∑ k, (f k : ℂ) • quadrature k) - (∑ k, (f k : ℂ) • quadrature k) *
        field v) := by
    rw [quadraticHamiltonian]; noncomm_ring
  rw [e, hS2, hS1, field_symplecticForm_mul_mulVec, smul_add, Finset.smul_sum, smul_smul]
  simp only [smul_smul]

end Commutators

/-! ### Theorem 6: essential self-adjointness and the unitary group -/

theorem isCoeffFinite_quadrature (k : PhaseIndex n) : IsCoeffFinite (quadrature k) := by
  rcases k with j | j
  · exact ((isCoeffFinite_annihilate j).add (isCoeffFinite_create j)).smul _
  · have e : (quadrature (Sum.inr j) : Module.End ℂ (FormalFock (Fin n) ℂ)) =
        (Complex.I / (Real.sqrt 2 : ℂ)) • (create j + (-1 : ℂ) • annihilate j) := by
      simp [quadrature, sub_eq_add_neg]
    rw [e]
    exact ((isCoeffFinite_create j).add ((isCoeffFinite_annihilate j).smul (-1))).smul _

theorem isCoeffFinite_quadraticHamiltonian (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : IsCoeffFinite (quadraticHamiltonian K f) :=
  (IsCoeffFinite.sum _ fun k _ => IsCoeffFinite.sum _ fun l _ =>
    ((isCoeffFinite_quadrature k).mul (isCoeffFinite_quadrature l)).smul _).add
    (IsCoeffFinite.sum _ fun k _ => (isCoeffFinite_quadrature k).smul _)

theorem dense_finiteSupport : Dense (finiteSupport (Fin n) : Set (FockSpace (Fin n))) := by
  classical
  refine (dense_span_single (ι := Fin n)).mono ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨m, rfl⟩
  exact (Set.finite_singleton m).subset fun k hk => by
    by_contra h
    rw [Set.mem_singleton_iff] at h
    exact hk (by simp [lp.single_apply, h])

/-- `H` on `𝒟`, as an operator on `Γ_s`. -/
noncomputable abbrev quadraticHamiltonianMin (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : FockSpace (Fin n) →ₗ.[ℂ] FockSpace (Fin n) :=
  onSubspace (finiteSupport (Fin n)) (quadraticHamiltonianOnFinite K f)

theorem quadraticHamiltonianMin_le (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ)
    (f : PhaseIndex n → ℝ) : quadraticHamiltonianMin K f ≤ maxRealization (quadraticHamiltonian K f) := by
  have hmem : ∀ χ : finiteSupport (Fin n), (χ : FockSpace (Fin n)) ∈
      (maxRealization (quadraticHamiltonian K f)).domain := fun χ => by
    have h : toFormal (quadraticHamiltonianOnFinite K f χ : FockSpace (Fin n)) =
        quadraticHamiltonian K f (toFormal (χ : FockSpace (Fin n))) := toFormal_onFinite _ _ χ
    show Memℓp (quadraticHamiltonian K f (toFormal (χ : FockSpace (Fin n)))).coeff 2
    rw [← h]
    exact (quadraticHamiltonianOnFinite K f χ : FockSpace (Fin n)).2
  refine ⟨fun χ hχ => hmem ⟨χ, hχ⟩, fun x y hxy => ?_⟩
  apply toFormal_injective
  have h : toFormal (quadraticHamiltonianOnFinite K f x : FockSpace (Fin n)) =
      quadraticHamiltonian K f (toFormal (x : FockSpace (Fin n))) := toFormal_onFinite _ _ x
  change toFormal (quadraticHamiltonianOnFinite K f x : FockSpace (Fin n)) = _
  rw [h, toFormal_maxRealization, ← hxy]

/-- The common radius: some `ρ > 0` with `2 C_H ρ < 1` and `|t| < ρ`, when `2 C_H |t| < 1`. -/
private theorem exists_radius (C t : ℝ) (hC : 0 ≤ C) (ht : 2 * C * |t| < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * C * ρ < 1 ∧ |t| < ρ := by
  set ε := (1 - 2 * C * |t|) / (2 * (2 * C + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> nlinarith [abs_nonneg t]
  refine ⟨|t| + ε, by positivity, ?_, by linarith⟩
  have h1 : 2 * C * ε ≤ (1 - 2 * C * |t|) / 2 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg t]
  nlinarith

variable {K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ}

/-- **Theorem 6(a).** `H̄` is self-adjoint, it is the closure of `H` on `𝒟`, and it is the
adjoint of `H` on `𝒟` (Lemma 5(c)). -/
theorem quadraticHamiltonian_closure_eq (hK : K.IsSymm) (f : PhaseIndex n → ℝ) :
    IsSelfAdjoint (maxRealization (quadraticHamiltonian K f)) ∧
      (quadraticHamiltonianMin K f).closure = maxRealization (quadraticHamiltonian K f) ∧
      (quadraticHamiltonianMin K f).adjoint = maxRealization (quadraticHamiltonian K f) := by
  set C := quadraticBound K f
  have hC := quadraticBound_nonneg K f
  obtain ⟨ρ, hρ, hρC, -⟩ := exists_radius C 0 hC (by simp)
  have hA := inner_quadraticHamiltonianOnFinite hK f
  have han := summable_quadraticHamiltonianOnFinite K f hρ.le hρC
  have hsa := isSelfAdjoint_closure_onSubspace dense_finiteSupport hA hρ han
  have hcl := isClosable_onSubspace dense_finiteSupport hA
  set A := quadraticHamiltonianMin K f
  set Hm := maxRealization (quadraticHamiltonian K f)
  -- `closure ≤ H̄ ≤ A† ≤ closure† = closure`
  have h1 : A.closure ≤ Hm := closure_le_of_isClosed
    (isClosed_maxRealization (isCoeffFinite_quadraticHamiltonian K f))
    (quadraticHamiltonianMin_le K f)
  have h2 : Hm ≤ A.adjoint := by
    refine ⟨fun ψ hψ => LinearPMap.mem_adjoint_domain_of_exists _
      ⟨Hm ⟨ψ, hψ⟩, fun x => inner_maxRealization_quadraticHamiltonian hK f ⟨ψ, hψ⟩ x⟩,
      fun ψ y hψy => ?_⟩
    refine (LinearPMap.adjoint_apply_eq dense_finiteSupport y fun x => ?_).symm
    rw [← hψy]
    exact inner_maxRealization_quadraticHamiltonian hK f ψ x
  have h3 : A.adjoint ≤ A.closure := by
    have := adjoint_le_adjoint_closure hcl dense_finiteSupport
    rwa [LinearPMap.isSelfAdjoint_def.1 hsa] at this
  have heq : A.closure = Hm := le_antisymm h1 (h2.trans h3)
  refine ⟨heq ▸ hsa, heq, le_antisymm (h3.trans h1) h2⟩

/-- **Theorem 6(b), (c).** `H̄` generates exactly one strongly continuous one-parameter unitary
group `e^{-itH̄}`, and for `ψ ∈ 𝒟` and `2 C_H |t| < 1`, `e^{-itH̄} ψ = Σ (-it)ⁿ Hⁿψ / n!`. -/
theorem existsUnique_isGenerator_quadraticHamiltonian (hK : K.IsSymm) (f : PhaseIndex n → ℝ) :
    (∃! U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
      IsGenerator (maxRealization (quadraticHamiltonian K f)) U) ∧
    ∀ U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
      IsGenerator (maxRealization (quadraticHamiltonian K f)) U →
      ∀ t : ℝ, 2 * quadraticBound K f * |t| < 1 → ∀ χ : finiteSupport (Fin n),
        HasSum (fun m : ℕ => ((-(t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) •
          ((quadraticHamiltonianOnFinite K f ^ m) χ : FockSpace (Fin n)))
          ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) χ) := by
  have hC := quadraticBound_nonneg K f
  have hA := inner_quadraticHamiltonianOnFinite hK f
  have heq := (quadraticHamiltonian_closure_eq hK f).2.1
  refine ⟨?_, fun U hU t ht χ => ?_⟩
  · obtain ⟨ρ, hρ, hρC, -⟩ := exists_radius _ 0 hC (by simp)
    have h := (isSelfAdjoint_closure_and_isGenerator_of_analytic _ dense_finiteSupport _ hA hρ
      (summable_quadraticHamiltonianOnFinite K f hρ.le hρC)).2.1
    rwa [← heq]
  · obtain ⟨ρ, hρ, hρC, htρ⟩ := exists_radius _ t hC ht
    have h := (isSelfAdjoint_closure_and_isGenerator_of_analytic _ dense_finiteSupport _ hA hρ
      (summable_quadraticHamiltonianOnFinite K f hρ.le hρC)).2.2
    exact h U (by rwa [← heq] at hU) t htρ χ

/-- `H̄` restricted to `𝒟` is `H` on `𝒟`. -/
theorem domRestrict_maxRealization_quadraticHamiltonian
    (K : Matrix (PhaseIndex n) (PhaseIndex n) ℝ) (f : PhaseIndex n → ℝ) :
    (maxRealization (quadraticHamiltonian K f)).domRestrict (finiteSupport (Fin n)) =
      quadraticHamiltonianMin K f := by
  have hle := quadraticHamiltonianMin_le K f
  refine LinearPMap.ext (inf_of_le_left hle.1) fun x hx hx' => ?_
  exact (LinearPMap.domRestrict_apply (x := ⟨x, hx⟩) (y := ⟨x, hx.2⟩) rfl).trans
    (hle.2 (x := ⟨x, hx'⟩) (y := ⟨x, hx.2⟩) rfl).symm

/-- **Theorem 2(d) for `H̄`.** A strongly continuous one-parameter unitary group whose derivative
at `0` on `𝒟` is `-iH̄` is generated by `H̄`. -/
theorem isGenerator_of_hasDerivAt (hK : K.IsSymm) (f : PhaseIndex n → ℝ)
    {V : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))} (hV : IsUnitaryGroup V)
    (hder : ∀ ψ : finiteSupport (Fin n), HasDerivAt
      (fun t : ℝ => (V t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ)
      (-(Complex.I • (quadraticHamiltonianOnFinite K f ψ : FockSpace (Fin n)))) 0) :
    IsGenerator (maxRealization (quadraticHamiltonian K f)) V := by
  obtain ⟨hsa, hcl, -⟩ := quadraticHamiltonian_closure_eq hK f
  have hle := quadraticHamiltonianMin_le K f
  refine IsGenerator.of_core hsa (E₀ := finiteSupport (Fin n)) hle.1 ?_ hV fun ψ => ?_
  · rw [domRestrict_maxRealization_quadraticHamiltonian, hcl]
  · have e : maxRealization (quadraticHamiltonian K f) ⟨ψ, hle.1 ψ.2⟩ =
        (quadraticHamiltonianOnFinite K f ψ : FockSpace (Fin n)) :=
      (hle.2 (x := ψ) (y := ⟨ψ, hle.1 ψ.2⟩) rfl).symm
    rw [e]
    exact hder ψ

/-- `Φ_v = H_{0, Ωᵀv}`. -/
theorem field_eq_quadraticHamiltonian (v : PhaseIndex n → ℝ) :
    field v = quadraticHamiltonian 0 ((symplecticForm n)ᵀ *ᵥ v) := by
  simp [field, quadraticHamiltonian]

end FockSpace

end BosonicLean.Fock
