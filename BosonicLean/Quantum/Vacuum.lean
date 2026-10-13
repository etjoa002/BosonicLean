import BosonicLean.Quantum.Defs
import BosonicLean.Analysis.SchwartzGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# One-mode Gaussian vacuum

The real Gaussian `ψ(x) = (√π s)^{-1/2} e^{-x²/(2s²)}` of width `s > 0` and the action of
position and momentum on it, on their common Schwartz domain.
-/

open MeasureTheory
namespace Gaussian

@[simp] theorem oneModePosition_apply (f : OneModeDomain) (x : ℝ) :
    oneModePosition f x = (x : ℂ) * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) f x

@[simp] theorem oneModeMomentum_apply (h : ℝ) (f : OneModeDomain) (x : ℝ) :
    oneModeMomentum h f x = (-Complex.I * (h : ℂ)) * deriv f x := rfl

theorem oneModeEmbed_inner (f g : OneModeDomain) :
    inner ℂ (oneModeEmbed f) (oneModeEmbed g) =
      ∫ x : ℝ, inner ℂ (f x) (g x) :=
  SchwartzMap.inner_toL2_toL2_eq f g

theorem isVacuum_unique {s : ℝ} {ψ φ : OneModeState}
    (hψ : IsVacuum s ψ) (hφ : IsVacuum s φ) : ψ = φ := by
  have hf : ψ.function = φ.function := SchwartzMap.ext fun x => (hψ x).trans (hφ x).symm
  cases ψ
  cases φ
  cases hf
  rfl

theorem hasDerivAt_vacuumFunction (s x : ℝ) :
    HasDerivAt (vacuumFunction s) (-((x : ℂ) / (s : ℂ)^2) * vacuumFunction s x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const (2 * s^2)).exp.const_mul
    (1 / Real.sqrt (Real.sqrt Real.pi * s))
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one] at hd
  have hder : 1 / Real.sqrt (Real.sqrt Real.pi * s) *
      (Real.exp (-x^2 / (2 * s^2)) * (-(2 * x) / (2 * s^2))) =
      -(x / s^2) * (1 / Real.sqrt (Real.sqrt Real.pi * s) *
        Real.exp (-x^2 / (2 * s^2))) := by ring
  rw [hder] at hd
  have hc := hd.ofReal_comp
  change HasDerivAt (vacuumFunction s) _ x at hc
  convert! hc using 1
  simp only [vacuumFunction, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_pow]

theorem vacuum_momentum_action {s : ℝ} (h : ℝ) (ψ : OneModeState)
    (hψ : IsVacuum s ψ) :
    oneModeMomentum h ψ.function =
      (Complex.I * (h : ℂ) / (s : ℂ)^2) • oneModePosition ψ.function := by
  have hf : (ψ.function : ℝ → ℂ) = vacuumFunction s := funext hψ
  ext x
  simp only [oneModeMomentum_apply, hf, (hasDerivAt_vacuumFunction s x).deriv,
    smul_apply, oneModePosition_apply, smul_eq_mul, hψ x]
  ring

theorem oneModeEmbed_norm_sq (f : OneModeDomain) :
    ‖oneModeEmbed f‖^2 = ∫ x : ℝ, ‖f x‖^2 := by
  have h := oneModeEmbed_inner f f
  simp only [inner_self_eq_norm_sq_to_K, integral_ofReal] at h
  exact_mod_cast h

theorem norm_vacuumFunction_sq {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖vacuumFunction s x‖^2 =
      (1 / (Real.sqrt Real.pi * s)) * Real.exp (-(s^2)⁻¹ * x^2) := by
  have hc : 0 < Real.sqrt Real.pi * s := mul_pos (Real.sqrt_pos.2 Real.pi_pos) hs
  rw [vacuumFunction, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    div_pow, one_pow, Real.sq_sqrt hc.le, pow_two, ← Real.exp_add]
  congr 2
  ring

theorem integral_norm_vacuumFunction_sq {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, ‖vacuumFunction s x‖^2) = 1 := by
  simp_rw [norm_vacuumFunction_sq hs]
  rw [integral_const_mul, integral_gaussian]
  have hc : Real.sqrt Real.pi * s ≠ 0 := ne_of_gt
    (mul_pos (Real.sqrt_pos.2 Real.pi_pos) hs)
  rw [div_inv_eq_mul, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hs.le]
  simpa only [one_div] using inv_mul_cancel₀ hc

theorem vacuum_normalized {s : ℝ} (hs : 0 < s) (f : OneModeDomain)
    (hf : ∀ x, f x = vacuumFunction s x) : ‖oneModeEmbed f‖ = 1 := by
  have h := oneModeEmbed_norm_sq f
  simp_rw [hf] at h
  rw [integral_norm_vacuumFunction_sq hs] at h
  nlinarith [norm_nonneg (oneModeEmbed f)]

/-- The normalized real Gaussian as a complex Schwartz function. -/
noncomputable def vacuumSchwartz (s : ℝ) (hs : 0 < s) : OneModeDomain :=
  ((1 / Real.sqrt (Real.sqrt Real.pi * s)) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 s⁻¹ (inv_ne_zero hs.ne')))
      standardGaussianReal)).postcompCLM Complex.ofRealCLM

@[simp] theorem vacuumSchwartz_apply (s : ℝ) (hs : 0 < s) (x : ℝ) :
    vacuumSchwartz s hs x = vacuumFunction s x := by
  change ((1 / Real.sqrt (Real.sqrt Real.pi * s) *
    Real.exp (-((s⁻¹ * x)^2 / 2)) : ℝ) : ℂ) = vacuumFunction s x
  unfold vacuumFunction
  congr 2
  congr 1
  ring

theorem vacuum_exists_unique {s : ℝ} (hs : 0 < s) :
    ∃! ψ : OneModeState, IsVacuum s ψ := by
  let ψ : OneModeState := ⟨vacuumSchwartz s hs,
    vacuum_normalized hs _ (vacuumSchwartz_apply s hs)⟩
  have hψ : IsVacuum s ψ := vacuumSchwartz_apply s hs
  exact ⟨ψ, hψ, fun φ hφ => isVacuum_unique hφ hψ⟩

theorem vacuum_position_inner {s : ℝ} (ψ : OneModeState) (hψ : IsVacuum s ψ) :
    inner ℂ (oneModeEmbed ψ.function) (oneModeEmbed (oneModePosition ψ.function)) = 0 := by
  have heven (x : ℝ) : ψ.function (-x) = ψ.function x := by
    rw [hψ, hψ]
    simp only [vacuumFunction, neg_sq]
  let F : ℝ → ℂ := fun x => inner ℂ (ψ.function x) (oneModePosition ψ.function x)
  have ho (x : ℝ) : F (-x) = -F x := by
    simp [F, oneModePosition_apply, heven]
  have hi := integral_neg_eq_self F volume
  simp_rw [ho, integral_neg] at hi
  rw [oneModeEmbed_inner]
  exact CharZero.neg_eq_self_iff.mp hi

theorem vacuum_position_mean {s : ℝ} (ψ : OneModeState) (hψ : IsVacuum s ψ) :
    oneModeMean ψ oneModePosition = 0 := by
  simp [oneModeMean, vacuum_position_inner ψ hψ]

theorem oneModePosition_apply_real (f : OneModeDomain) (x : ℝ) :
    oneModePosition f x = x • f x := by
  simp [oneModePosition_apply, Complex.real_smul]

theorem oneModePosition_deriv (f : OneModeDomain) (x : ℝ) :
    deriv (oneModePosition f) x = f x + x • deriv f x := by
  have h := ((hasDerivAt_id x).ofReal_comp.mul (f.hasDerivAt x)).deriv
  rw [show (oneModePosition f : ℝ → ℂ) = (fun y : ℝ => (y : ℂ) * f y) from
    funext (oneModePosition_apply f)]
  simpa only [Pi.mul_def, id_eq, Complex.ofReal_one, one_mul, Complex.real_smul] using h

theorem vacuum_deriv_real {s : ℝ} (ψ : OneModeState) (hψ : IsVacuum s ψ) (x : ℝ) :
    deriv ψ.function x = (-(x / s^2)) • ψ.function x := by
  have hf : (ψ.function : ℝ → ℂ) = vacuumFunction s := funext hψ
  rw [hf, (hasDerivAt_vacuumFunction s x).deriv]
  simp [Complex.real_smul]

theorem oneMode_norm_sq_integrable (f : OneModeDomain) :
    Integrable (fun x : ℝ => ‖f x‖^2) := by
  have hi := (SchwartzMap.pairing (innerSL ℝ) f f).integrable (μ := volume)
  have hp : (⇑(SchwartzMap.pairing (innerSL ℝ) f f)) = (fun x : ℝ => ‖f x‖^2) := by
    funext x
    exact real_inner_self_eq_norm_sq (f x)
  rw [hp] at hi
  exact hi

theorem vacuum_position_secondMoment {s : ℝ} (hs : 0 < s)
    (ψ : OneModeState) (hψ : IsVacuum s ψ) :
    ‖oneModeEmbed (oneModePosition ψ.function)‖^2 = s^2 / 2 := by
  let f := ψ.function
  let g := oneModePosition f
  have hd (x : ℝ) : deriv f x = (-(x / s^2)) • f x := vacuum_deriv_real ψ hψ x
  have hL (x : ℝ) : inner ℝ (f x) (deriv g x) =
      ‖f x‖^2 - (s^2)⁻¹ * ‖g x‖^2 := by
    dsimp only [g]
    rw [oneModePosition_deriv, hd]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      oneModePosition_apply_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hR (x : ℝ) : inner ℝ (deriv f x) (g x) =
      -(s^2)⁻¹ * ‖g x‖^2 := by
    dsimp only [g]
    rw [hd]
    simp only [oneModePosition_apply_real, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hi := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left f g (innerSL ℝ)
  change (∫ x : ℝ, inner ℝ (f x) (deriv g x)) =
    -∫ x : ℝ, inner ℝ (deriv f x) (g x) at hi
  simp_rw [hL, hR] at hi
  rw [integral_sub (oneMode_norm_sq_integrable f)
    ((oneMode_norm_sq_integrable g).const_mul _), integral_const_mul,
    integral_const_mul] at hi
  have hf : (∫ x : ℝ, ‖f x‖^2) = 1 := by
    rw [← oneModeEmbed_norm_sq, show f = ψ.function from rfl, ψ.normalized]
    norm_num
  rw [hf, ← oneModeEmbed_norm_sq g] at hi
  have hs2 : s^2 ≠ 0 := pow_ne_zero 2 hs.ne'
  field_simp at hi
  dsimp only [g, f] at hi
  nlinarith

theorem vacuum_action_moments {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    (ψ : OneModeState) (hψ : IsVacuum s ψ) :
    oneModeMomentum h ψ.function =
        (Complex.I * (h : ℂ) / (s : ℂ)^2) • oneModePosition ψ.function ∧
    oneModeMean ψ oneModePosition = 0 ∧
    oneModeMean ψ (oneModeMomentum h) = 0 ∧
    ‖oneModeEmbed (oneModePosition ψ.function)‖^2 = s^2 / 2 ∧
    ‖oneModeEmbed (oneModeMomentum h ψ.function)‖^2 = h^2 / (2 * s^2) ∧
    inner ℂ (oneModeEmbed (oneModePosition ψ.function))
      (oneModeEmbed (oneModeMomentum h ψ.function)) = Complex.I * (h : ℂ) / 2 := by
  have ha := vacuum_momentum_action h ψ hψ
  have hx := vacuum_position_secondMoment hs ψ hψ
  refine ⟨ha, vacuum_position_mean ψ hψ, ?_, hx, ?_, ?_⟩
  · unfold oneModeMean
    rw [ha, map_smul, inner_smul_right, vacuum_position_inner ψ hψ]
    simp
  · rw [ha, map_smul, norm_smul, mul_pow, hx]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hh]
    field_simp
  · rw [ha, map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow, hx, RCLike.ofReal_eq_complex_ofReal]
    push_cast
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp [hsC]

theorem vacuum_covariance {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    (ψ : OneModeState) (hψ : IsVacuum s ψ) :
    oneModeCovariance h ψ = diagonalOne (s^2) (h^2 / s^2) ∧
    vacuumUnits s h * oneModeCovariance h ψ * (vacuumUnits s h).transpose = 1 ∧
    IsAdmissible (vacuumUnits s h * oneModeCovariance h ψ * (vacuumUnits s h).transpose) := by
  obtain ⟨_, hx0, hp0, hx2, hp2, hxp⟩ := vacuum_action_moments hs hh ψ hψ
  have hxp0 : (inner ℂ (oneModeEmbed (oneModePosition ψ.function))
      (oneModeEmbed (oneModeMomentum h ψ.function))).re = 0 := by rw [hxp]; simp
  have hpx0 : (inner ℂ (oneModeEmbed (oneModeMomentum h ψ.function))
      (oneModeEmbed (oneModePosition ψ.function))).re = 0 := by
    exact (inner_re_symm (𝕜 := ℂ) _ _).trans hxp0
  have hxx : (inner ℂ (oneModeEmbed (oneModePosition ψ.function))
      (oneModeEmbed (oneModePosition ψ.function))).re = s^2 / 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm.trans hx2
  have hpp : (inner ℂ (oneModeEmbed (oneModeMomentum h ψ.function))
      (oneModeEmbed (oneModeMomentum h ψ.function))).re = h^2 / (2 * s^2) :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm.trans hp2
  have hc : oneModeCovariance h ψ = diagonalOne (s^2) (h^2 / s^2) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [oneModeCovariance, oneModeObservable, oneModeCentered, hx0, hp0,
        hxx, hpp, hxp0, hpx0, diagonalOne, Matrix.diagonal,
        -inner_self_eq_norm_sq_to_K] <;>
      ring
  have hu : vacuumUnits s h * oneModeCovariance h ψ * (vacuumUnits s h).transpose = 1 := by
    rw [hc]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [vacuumUnits, diagonalOne, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.diagonal, Matrix.transpose_apply, Matrix.one_apply, hs.ne', hh.ne'] <;>
      field_simp
  refine ⟨hc, hu, ?_⟩
  rw [hu]
  have hI : diagonalOne 1 1 = (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [diagonalOne, Matrix.diagonal, Matrix.one_apply]
  rw [← hI]
  exact isAdmissible_vacuumOne

theorem vacuum_physicalCovariance {m ω h : ℝ} (hm : 0 < m) (hω : 0 < ω) (hh : 0 < h)
    (ψ : OneModeState) (hψ : IsVacuum (Real.sqrt (h / (m * ω))) ψ) :
    oneModeCovariance h ψ = diagonalOne (h / (m * ω)) (h * m * ω) := by
  have hr : 0 < h / (m * ω) := div_pos hh (mul_pos hm hω)
  rw [(vacuum_covariance (Real.sqrt_pos.2 hr) hh ψ hψ).1, Real.sq_sqrt hr.le]
  congr 1
  field_simp


end Gaussian
