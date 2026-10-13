/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean.Weyl.Right
import Mathlib.Analysis.Real.Cardinality
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Simplicity of the CCR algebra

For an alternating form `σ` that is nondegenerate (`LinearMap.SeparatingLeft`), the CCR algebra
`CCR σ` is a simple ring.

The averages `M_n^u(a) = (1/n) Σ_{k<n} W(ku) a W(ku)*` are defined for any Weyl system; they
multiply `W v` by the geometric mean of `e^{-ikσ(u,v)}`. On the CCR algebra they approximate
`τ(a) · 1`, where `τ` is the faithful vector state `vectorState` of `Right.lean`. An ideal
containing `a ≠ 0` then contains an element within distance `1` of `1`, hence `1`.

## Main results

* `WeylSystem.conj_W`: `W(x) W(v) W(x)* = e^{-iσ(x,v)} W(v)`.
* `WeylSystem.average`, `norm_average_le`, `average_mem`, `average_W`.
* `tendsto_geomMean`, `exists_generic`.
* `WeylSystem.adjoin_le_span`, `WeylSystem.exists_average_near`.
* `CCR.eq_zero_of_apply_delta_zero`, `CCR.vectorState_star_mul_self_pos`, `CCR.isSimpleRing`.
-/

noncomputable section

open Filter Topology

namespace BosonicLean

namespace Weyl

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Geometric means -/

/-- The phase `e^{-iθ}`. -/
def expNegI (θ : ℝ) : ℂ := Complex.exp (-(θ : ℂ) * Complex.I)

/-- `e^{-iθ} = 1` exactly when `θ ∈ 2πℤ`. -/
theorem expNegI_eq_one_iff (θ : ℝ) : expNegI θ = 1 ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  rw [expNegI, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h := congrArg Complex.im hn
    simp at h
    push_cast
    linarith
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    push_cast
    ring

/-- `e^{-iθ} ≠ 1` exactly when `θ ∉ 2πℤ` (the form of the notes, Lemmas 6.5 and 6.6). -/
theorem expNegI_ne_one_iff (θ : ℝ) : expNegI θ ≠ 1 ↔ ∀ k : ℤ, θ ≠ 2 * Real.pi * k := by
  rw [ne_eq, expNegI_eq_one_iff]
  push Not
  rfl

theorem norm_expNegI (θ : ℝ) : ‖expNegI θ‖ = 1 := by
  rw [expNegI, show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The geometric mean `(1/n) Σ_{k<n} z^k`. -/
def geomMean (z : ℂ) (n : ℕ) : ℂ := (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, z ^ k

/-- `|(1/n) Σ_{k<n} z^k| ≤ 2 / (n |z - 1|)` for `|z| = 1`, `z ≠ 1`. -/
theorem norm_geomMean_le {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (n : ℕ) :
    ‖geomMean z n‖ ≤ 2 / ‖z - 1‖ * (n : ℝ)⁻¹ := by
  have hz1 : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h1)
  rw [geomMean, geom_sum_eq h1, norm_mul, norm_div, norm_inv, Complex.norm_natCast, mul_comm]
  gcongr
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

/-- The geometric mean tends to `0` for `|z| = 1`, `z ≠ 1`. -/
theorem tendsto_geomMean {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    Tendsto (geomMean z) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 2 / ‖z - 1‖ * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (2 / ‖z - 1‖)
  exact squeeze_zero_norm (fun n => norm_geomMean_le hz h1 n) h

/-! ### Generic vectors -/

/-- For a nondegenerate alternating form and finitely many nonzero vectors, some `u` has
`σ(u,v) ∉ 2πℤ`, that is `e^{-iσ(u,v)} ≠ 1`, for each of them. -/
theorem exists_generic {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft)
    (s : Finset V) (hs : ∀ v ∈ s, v ≠ 0) : ∃ u : V, ∀ v ∈ s, expNegI (σ u v) ≠ 1 := by
  classical
  -- a vector off the finitely many proper subspaces `{u | σ(u,v) = 0}`
  have hproper : ∀ v ∈ s, LinearMap.ker (σ.flip v) ≠ ⊤ := by
    intro v hv htop
    apply hs v hv
    refine hnd v fun w => ?_
    have hw : σ w v = 0 := by
      have : w ∈ LinearMap.ker (σ.flip v) := htop ▸ Submodule.mem_top
      simpa using this
    rw [isAlt_swap hσ, hw, neg_zero]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, ∀ v ∈ s, σ u₀ v ≠ 0 := by
    have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℝ) (E := V)
      (s := s.image fun v => LinearMap.ker (σ.flip v)) (by
        simp only [Finset.mem_image, not_exists, not_and]
        exact fun v hv h => hproper v hv h)
    obtain ⟨u₀, hu₀⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
    refine ⟨u₀, fun v hv h => hu₀ (Set.mem_iUnion₂.2 ⟨_, Finset.mem_image_of_mem _ hv, ?_⟩)⟩
    simpa using h
  -- a real multiple of `u₀` avoiding the countably many bad scalings
  let bad : Set ℝ := ⋃ v ∈ s, Set.range fun m : ℤ => 2 * Real.pi * m / σ u₀ v
  have hbad : bad.Countable :=
    (s.countable_toSet).biUnion fun v _ => Set.countable_range _
  obtain ⟨t, ht⟩ : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hbad.mono fun t _ => h t)
  refine ⟨t • u₀, fun v hv h1 => ht ?_⟩
  rw [expNegI, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have hm' : t * σ u₀ v = 2 * Real.pi * (-m : ℤ) := by
    have := congrArg Complex.im hm
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    push_cast at this ⊢
    simp at this
    linarith
  refine Set.mem_biUnion hv ⟨-m, ?_⟩
  simp only
  rw [← hm', mul_div_assoc, div_self (hu₀ v hv), mul_one]

/-! ### Averages over conjugations in a Weyl system -/

namespace WeylSystem

variable {σ : LinearMap.BilinForm ℝ V} {A : Type*} [CStarAlgebra A] (S : WeylSystem σ A)

/-- `W(x) W(v) W(x)* = e^{-iσ(x,v)} W(v)`. -/
theorem conj_W (hσ : σ.IsAlt) (x v : V) :
    S.W x * S.W v * star (S.W x) = expNegI (σ x v) • S.W v := by
  rw [S.mul_comm_phase hσ, smul_mul_assoc, mul_assoc, (Unitary.mem_iff.1 (S.mem_unitary x)).2,
    mul_one, expNegI]
  congr 2
  push_cast
  ring

/-- The average `M_n^u(a) = (1/n) Σ_{k<n} W(ku) a W(ku)*`. -/
def average (u : V) (n : ℕ) : A →ₗ[ℂ] A :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n,
    (LinearMap.mulLeft ℂ (S.W ((k : ℕ) • u))).comp
      (LinearMap.mulRight ℂ (star (S.W ((k : ℕ) • u))))

theorem average_apply (u : V) (n : ℕ) (a : A) :
    S.average u n a =
      (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, S.W ((k : ℕ) • u) * a * star (S.W ((k : ℕ) • u)) := by
  simp [average, LinearMap.sum_apply, mul_assoc]

/-- The average is a contraction. -/
theorem norm_average_le (u : V) (n : ℕ) (a : A) : ‖S.average u n a‖ ≤ ‖a‖ := by
  rw [average_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hterm : ∀ k : ℕ, ‖S.W (k • u) * a * star (S.W (k • u))‖ = ‖a‖ := fun k => by
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (S.mem_unitary _)),
      CStarRing.norm_mem_unitary_mul _ (S.mem_unitary _)]
  calc ‖(n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, S.W (k • u) * a * star (S.W (k • u))‖
      ≤ ‖(n : ℂ)⁻¹‖ * ∑ k ∈ Finset.range n, ‖S.W (k • u) * a * star (S.W (k • u))‖ := by
        rw [norm_smul]; gcongr; exact norm_sum_le _ _
    _ = ‖a‖ := by
        simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, norm_inv,
          Complex.norm_natCast]
        field_simp

/-- The average is unital. -/
theorem average_one (u : V) {n : ℕ} (hn : n ≠ 0) : S.average u n 1 = 1 := by
  rw [average_apply]
  simp only [mul_one, (Unitary.mem_iff.1 (S.mem_unitary _)).2, Finset.sum_const,
    Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

/-- The average maps a two-sided ideal into itself. -/
theorem average_mem (u : V) (n : ℕ) {I : TwoSidedIdeal A} {a : A} (ha : a ∈ I) :
    S.average u n a ∈ I := by
  rw [average_apply, Algebra.smul_def]
  exact I.mul_mem_left _ _ (sum_mem fun k _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ ha))

/-- `M_n^u(W v) = μ_n(σ(u,v)) W v`. -/
theorem average_W (hσ : σ.IsAlt) (u v : V) (n : ℕ) :
    S.average u n (S.W v) = geomMean (expNegI (σ u v)) n • S.W v := by
  rw [average_apply, geomMean, mul_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.conj_W hσ, map_nsmul, LinearMap.smul_apply, expNegI, expNegI, nsmul_eq_mul,
    ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The `*`-algebra generated by the Weyl elements is contained in their linear span. -/
theorem adjoin_le_span (hσ : σ.IsAlt) :
    ((StarAlgebra.adjoin ℂ (Set.range S.W)) : Set A) ⊆ Submodule.span ℂ (Set.range S.W) := by
  have hstar : ∀ y ∈ Submodule.span ℂ (Set.range S.W),
      star y ∈ Submodule.span ℂ (Set.range S.W) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, rfl⟩ := hy
      rw [S.star_eq hσ]
      exact Submodule.subset_span ⟨-u, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [star_add]; exact add_mem hy hz
    | smul c y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  intro x hx
  induction hx using StarAlgebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span hx
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, ← S.map_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_le.2 ?_ hxy
    rintro _ ⟨_, ⟨u, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
    change S.W u * S.W w ∈ Submodule.span ℂ (Set.range S.W)
    rw [S.mul_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u + w, rfl⟩)
  | star x _ hx => exact hstar x hx

/-- For any Weyl system with a contractive functional `τ` that reads off the coefficient of `1`
(`τ(W v) = [v = 0]`): for every `a` and `ε > 0` there are `u` and `n ≥ 1` with
`‖M_n^u(a) - τ(a) 1‖ < ε`. -/
theorem exists_average_near [DecidableEq V] (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a, ‖τ a‖ ≤ ‖a‖) (hτW : ∀ v, τ (S.W v) = if v = 0 then 1 else 0) (a : A) {ε : ℝ}
    (hε : 0 < ε) : ∃ u n, n ≠ 0 ∧ ‖S.average u n a - τ a • 1‖ < ε := by
  classical
  -- a finite combination of Weyl elements within `ε/3` of `a`
  have ha : a ∈ closure (StarAlgebra.adjoin ℂ (Set.range S.W) : Set A) := by
    rw [← StarSubalgebra.topologicalClosure_coe, S.generating]; trivial
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 ha (ε / 3) (by linarith)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (S.adjoin_le_span hσ hb)
  -- a generic `u` for the nonzero vectors of the combination
  obtain ⟨u, hu⟩ := exists_generic hσ hnd (c.support.erase 0) fun v hv => Finset.ne_of_mem_erase hv
  -- the error term of the combination, term by term
  let err : ℕ → A := fun n => ∑ v ∈ c.support,
    (c v * (geomMean (expNegI (σ u v)) n - if v = 0 then 1 else 0)) • S.W v
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [show (0 : A) = ∑ v ∈ c.support, (0 : A) by simp]
    refine tendsto_finsetSum _ fun v hv => ?_
    by_cases hv0 : v = 0
    · subst hv0
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [geomMean, expNegI, hn]
    · have hz := tendsto_geomMean (norm_expNegI (σ u v))
        (hu v (Finset.mem_erase.2 ⟨hv0, hv⟩))
      simpa [hv0] using ((hz.const_mul (c v)).smul_const (S.W v))
  have hsum : ∀ n, n ≠ 0 →
      S.average u n (c.sum fun v r => r • S.W v) - τ (c.sum fun v r => r • S.W v) • 1 =
        err n := by
    intro n hn
    simp only [Finsupp.sum, map_sum, map_smul, S.average_W hσ, hτW, err, smul_smul,
      Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv0 : v = 0
    · subst hv0; simp [S.map_zero, mul_sub, sub_smul]
    · simp [hv0]
  have herr' := herr.norm
  rw [norm_zero] at herr'
  obtain ⟨n, hn, hn0⟩ := ((herr'.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 3))).and
    (eventually_ne_atTop 0)).exists
  refine ⟨u, n, hn0, ?_⟩
  set b := c.sum fun v r => r • S.W v
  have h1 : ‖S.average u n (a - b)‖ < ε / 3 :=
    (S.norm_average_le u n _).trans_lt (by rw [← dist_eq_norm]; exact hab)
  have h3 : ‖(τ b - τ a) • (1 : A)‖ < ε / 3 := by
    rw [norm_smul, ← map_sub]
    calc ‖τ (b - a)‖ * ‖(1 : A)‖ ≤ ‖b - a‖ * 1 := by
          gcongr
          · exact hτ _
          · rcases subsingleton_or_nontrivial A with h | h
            · simp [Subsingleton.elim (1 : A) 0]
            · simp
      _ < ε / 3 := by rw [mul_one, ← dist_eq_norm, dist_comm]; exact hab
  have hsplit : S.average u n a - τ a • 1 =
      S.average u n (a - b) + err n + (τ b - τ a) • (1 : A) := by
    rw [← hsum n hn0, map_sub, sub_smul]; abel
  rw [hsplit]
  calc ‖S.average u n (a - b) + err n + (τ b - τ a) • (1 : A)‖
      ≤ ‖S.average u n (a - b)‖ + ‖err n‖ + ‖(τ b - τ a) • (1 : A)‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end WeylSystem

/-! ### The CCR algebra -/

instance CCR.nontrivial {σ : LinearMap.BilinForm ℝ V} : Nontrivial (CCR σ) := by
  classical
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (fun a : CCR σ => (a : L2 V →L[ℂ] L2 V) (delta 0)) h
  simp only [OneMemClass.coe_one, one_apply_eq_self, ZeroMemClass.coe_zero,
    zero_apply] at this
  simpa [norm_delta] using congrArg norm this

variable [DecidableEq V] {σ : LinearMap.BilinForm ℝ V}

/-- An element of `CCR σ` with `a δ₀ = 0` is zero. -/
theorem CCR.eq_zero_of_apply_delta_zero (hσ : σ.IsAlt) {a : L2 V →L[ℂ] L2 V} (ha : a ∈ CCR σ)
    (h0 : a (delta 0) = 0) : a = 0 := by
  have hall : ∀ w : V, a (delta w) = 0 := fun w => by
    have hc := (commute_rightWeyl_of_mem_CCR σ hσ (-w) ha).eq
    calc a (delta w) = a (rightWeyl σ (-w) (delta 0)) := by rw [rightWeyl_delta_zero σ hσ, neg_neg]
      _ = rightWeyl σ (-w) (a (delta 0)) := congrArg (fun T => T (delta 0)) hc
      _ = 0 := by rw [h0, map_zero]
  ext1 f
  rw [zero_apply]
  have hs := (lp.hasSum_single (E := fun _ : V => ℂ) (p := 2) ENNReal.ofNat_ne_top f).mapL a
  refine hs.unique ?_
  convert hasSum_zero with v
  rw [show lp.single 2 v (f v) = f v • delta v by
    rw [delta, ← lp.single_smul, smul_eq_mul, mul_one], map_smul, hall, smul_zero]

/-- The vector state is faithful, `τ(a* a) > 0` for `a ≠ 0`. -/
theorem CCR.vectorState_star_mul_self_pos (hσ : σ.IsAlt) {a : CCR σ} (ha : a ≠ 0) :
    0 < (vectorState σ (star a * a)).re := by
  rw [vectorState_star_mul_self, Complex.ofReal_re]
  refine pow_pos (norm_pos_iff.2 fun h => ha ?_) 2
  exact Subtype.ext (CCR.eq_zero_of_apply_delta_zero hσ a.2 h)

theorem CCR.vectorState_W (hσ : σ.IsAlt) (v : V) :
    vectorState σ ((CCR.weylSystem σ hσ).W v) = if v = 0 then 1 else 0 :=
  vectorState_weyl σ hσ v

omit [DecidableEq V] in
/-- For a nondegenerate alternating form, `CCR σ` is a simple ring. -/
theorem CCR.isSimpleRing (hσ : σ.IsAlt) (hnd : σ.SeparatingLeft) : IsSimpleRing (CCR σ) := by
  classical
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.2 fun hI => ?_
  obtain ⟨a, haI, ha⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (eq_bot_iff.2 fun x hx => (TwoSidedIdeal.mem_bot _).2 (h x hx))
  have hxI : star a * a ∈ I := I.mul_mem_left _ _ haI
  obtain ⟨l, hl, hτx⟩ : ∃ l : ℝ, 0 < l ∧ vectorState σ (star a * a) = (l : ℂ) :=
    ⟨_, CCR.vectorState_star_mul_self_pos hσ ha, by
      rw [vectorState_star_mul_self, Complex.ofReal_re]⟩
  obtain ⟨u, n, -, hun⟩ := (CCR.weylSystem σ hσ).exists_average_near hσ hnd (vectorState σ)
    (norm_vectorState_apply_le σ) (CCR.vectorState_W hσ) (star a * a) hl
  rw [hτx] at hun
  have hMI := (CCR.weylSystem σ hσ).average_mem u n hxI
  generalize (CCR.weylSystem σ hσ).average u n (star a * a) = y at hun hMI
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  have hy : (l : ℂ)⁻¹ • y ∈ TwoSidedIdeal.asIdeal I := by
    rw [TwoSidedIdeal.mem_asIdeal, Algebra.smul_def]
    exact I.mul_mem_left _ _ hMI
  have hid : 1 - (l : ℂ)⁻¹ • y = (l : ℂ)⁻¹ • ((l : ℂ) • 1 - y) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hnorm : ‖1 - (l : ℂ)⁻¹ • y‖ < 1 := by
    rw [hid, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hl.le, norm_sub_rev,
      inv_mul_lt_iff₀ hl, mul_one]
    exact hun
  have htop := Ideal.eq_top_of_norm_lt_one _ hy hnorm
  have h1 : (1 : CCR σ) ∈ TwoSidedIdeal.asIdeal I := by rw [htop]; exact Submodule.mem_top
  exact (TwoSidedIdeal.one_mem_iff I).1 (TwoSidedIdeal.mem_asIdeal.1 h1)

end Weyl

end BosonicLean
