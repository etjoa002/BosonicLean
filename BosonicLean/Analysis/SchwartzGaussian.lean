import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# The real Gaussian as a Schwartz function

The proofs use Mathlib's Hermite derivative formula and its decay estimates for the Gaussian.
-/

open Filter
open scoped Topology
namespace Gaussian

private theorem pow_mul_standardGaussian_bounded (m : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ m * Real.exp (-(x ^ 2 / 2)) ≤ C := by
  let g : ℝ → ℝ := fun x => |x| ^ m * Real.exp (-(x ^ 2 / 2))
  have hg0 : Tendsto g (cocompact ℝ) (𝓝 0) := by
    convert tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 / 2 : ℝ)) (by positivity) (m : ℝ) using 1
    ext x
    simp only [g, Real.rpow_natCast]
    congr 1
    ring
  have hgb : Bornology.IsBounded (Set.range g) :=
    (show Continuous g by fun_prop).isBounded_range_iff_isBigO.mpr (hg0.isBigO_one ℝ)
  obtain ⟨C, hC⟩ := hgb.exists_norm_le
  refine ⟨C, fun x => ?_⟩
  have hx := hC (g x) ⟨x, rfl⟩
  simpa only [g, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g x)] using hx

private theorem polynomial_mul_standardGaussian_bounded (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x|^k * |p.eval x * Real.exp (-(x^2 / 2))| ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C, hC⟩ := hp
    obtain ⟨D, hD⟩ := hq
    refine ⟨C + D, fun x => ?_⟩
    calc
      _ ≤ |x|^k * (|p.eval x * Real.exp (-(x^2 / 2))| +
          |q.eval x * Real.exp (-(x^2 / 2))|) := by
        rw [Polynomial.eval_add, add_mul]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC x) (hD x)
  | monomial n a =>
    obtain ⟨C, hC⟩ := pow_mul_standardGaussian_bounded (k+n)
    refine ⟨|a| * C, fun x => ?_⟩
    calc
      _ = |a| * (|x|^(k+n) * Real.exp (-(x^2 / 2))) := by
        simp only [Polynomial.eval_monomial, abs_mul, abs_pow,
          abs_of_pos (Real.exp_pos _), pow_add]
        ring
      _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg a)

/-- The standard real Gaussian, with exponent `-x²/2`, in Schwartz space. -/
noncomputable def standardGaussianReal : SchwartzMap ℝ ℝ where
  toFun x := Real.exp (-(x^2 / 2))
  smooth' := by fun_prop
  decay' k n := by
    let p : Polynomial ℝ := (Polynomial.hermite n).map (algebraMap ℤ ℝ)
    obtain ⟨C, hC⟩ := polynomial_mul_standardGaussian_bounded p k
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
    simpa [p, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Real.norm_eq_abs, abs_mul, abs_pow] using hC x

@[simp] theorem standardGaussianReal_apply (x : ℝ) :
    standardGaussianReal x = Real.exp (-(x^2 / 2)) := rfl

end Gaussian
