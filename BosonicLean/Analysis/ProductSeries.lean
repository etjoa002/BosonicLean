/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ordered products of absolutely convergent series

In a complete normed ring, let `f₁, …, f_N : ℕ → A` be absolutely convergent series. Then the
series of ordered products `f₁(n₁) ⋯ f_N(n_N)` over multi-indices `n ∈ ℕ^N` converges absolutely,
and its sum is the ordered product `(Σ f₁) ⋯ (Σ f_N)`; the order of the factors is kept, so no
commutativity is needed. For a bosonic MPS this turns `Σₙ |Ψ(n)|²` into a product of transfer
matrices.

## Main results

* `BosonicLean.hasSum_list_ofFn_prod`: absolute convergence and the value of the product series.
-/

namespace BosonicLean

variable {A : Type*} [NormedRing A] [CompleteSpace A]

/-- **Ordered product of absolutely convergent series.** If each `fⱼ` is summable in norm, then
`n ↦ f₁(n₁) ⋯ f_N(n_N)` is summable in norm over `ℕ^N` and sums to `(Σ f₁) ⋯ (Σ f_N)`. -/
theorem hasSum_list_ofFn_prod :
    ∀ {N : ℕ} (f : Fin N → ℕ → A), (∀ j, Summable fun k => ‖f j k‖) →
      (Summable fun n : Fin N → ℕ => ‖(List.ofFn fun j => f j (n j)).prod‖) ∧
        HasSum (fun n : Fin N → ℕ => (List.ofFn fun j => f j (n j)).prod)
          (List.ofFn fun j => ∑' k, f j k).prod
  | 0, f, _ => by
    have h0 : ∀ n : Fin 0 → ℕ, n = finZeroElim := fun n => funext fun i => i.elim0
    simp only [List.ofFn_zero, List.prod_nil]
    exact ⟨(hasSum_single finZeroElim fun b hb => absurd (h0 b) hb).summable,
      hasSum_single (f := fun _ : Fin 0 → ℕ => (1 : A)) finZeroElim
        fun b hb => absurd (h0 b) hb⟩
  | N + 1, f, hf => by
    obtain ⟨hs, hh⟩ := hasSum_list_ofFn_prod (fun j : Fin N => f j.succ) (fun j => hf j.succ)
    set F : (Fin N → ℕ) → A := fun t => (List.ofFn fun j => f j.succ (t j)).prod with hF
    have key : ∀ p : ℕ × (Fin N → ℕ),
        (List.ofFn fun j => f j (Fin.consEquiv (fun _ => ℕ) p j)).prod = f 0 p.1 * F p.2 := by
      intro p
      simp [List.ofFn_succ, Fin.consEquiv, hF]
    have hnorm : Summable fun p : ℕ × (Fin N → ℕ) => ‖f 0 p.1 * F p.2‖ := (hf 0).mul_norm hs
    have hsum : HasSum (fun p : ℕ × (Fin N → ℕ) => f 0 p.1 * F p.2)
        ((∑' k, f 0 k) * ∑' t, F t) := by
      rw [tsum_mul_tsum_of_summable_norm (hf 0) hs]
      exact (summable_mul_of_summable_norm (hf 0) hs).hasSum
    refine ⟨?_, ?_⟩
    · rw [← (Fin.consEquiv fun _ => ℕ).summable_iff]
      simpa only [Function.comp_def, key] using hnorm
    · rw [← (Fin.consEquiv fun _ => ℕ).hasSum_iff, List.ofFn_succ, List.prod_cons, ← hh.tsum_eq]
      simpa only [Function.comp_def, key] using hsum

end BosonicLean
