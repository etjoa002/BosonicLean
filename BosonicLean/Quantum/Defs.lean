import BosonicLean.PhaseSpace.Examples
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# One-mode states on a common Schwartz domain

Position and momentum act on Schwartz functions, and `oneModeEmbed` maps Schwartz functions into
`L²(ℝ)`. The operators are continuous for the Schwartz topology. The covariance
`γⱼₖ = 2 Re⟨Aⱼψ − mⱼψ, Aₖψ − mₖψ⟩`, with `mⱼ` the mean of `Aⱼ`, is twice the symmetrized
covariance.
-/

open MeasureTheory
open scoped ComplexOrder
namespace Gaussian
abbrev OneModeDomain := SchwartzMap ℝ ℂ
noncomputable def oneModeEmbed : OneModeDomain →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume
noncomputable def oneModePosition : OneModeDomain →L[ℂ] OneModeDomain :=
  SchwartzMap.smulLeftCLM ℂ Complex.ofReal
noncomputable def oneModeMomentum (h : ℝ) : OneModeDomain →L[ℂ] OneModeDomain :=
  (-Complex.I * (h : ℂ)) • SchwartzMap.derivCLM ℂ ℂ
structure OneModeState where
  function : OneModeDomain
  normalized : ‖oneModeEmbed function‖ = 1
noncomputable def vacuumFunction (s x : ℝ) : ℂ :=
  ((1 / Real.sqrt (Real.sqrt Real.pi * s) * Real.exp (-x ^ 2 / (2 * s ^ 2)) : ℝ) : ℂ)
def IsVacuum (s : ℝ) (ψ : OneModeState) : Prop :=
  ∀ x, ψ.function x = vacuumFunction s x
noncomputable def oneModeMean (ψ : OneModeState)
    (A : OneModeDomain →L[ℂ] OneModeDomain) : ℝ :=
  (inner ℂ (oneModeEmbed ψ.function) (oneModeEmbed (A ψ.function))).re
noncomputable def oneModeCentered (ψ : OneModeState)
    (A : OneModeDomain →L[ℂ] OneModeDomain) : Lp ℂ 2 (volume : Measure ℝ) :=
  oneModeEmbed (A ψ.function) - (oneModeMean ψ A : ℂ) • oneModeEmbed ψ.function
noncomputable def oneModeObservable (h : ℝ) (i : PhaseIndex 1) :
    OneModeDomain →L[ℂ] OneModeDomain :=
  Sum.elim (fun _ => oneModePosition) (fun _ => oneModeMomentum h) i
noncomputable def oneModeCovariance (h : ℝ) (ψ : OneModeState) :
    Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ :=
  fun i j => 2 * (inner ℂ (oneModeCentered ψ (oneModeObservable h i))
    (oneModeCentered ψ (oneModeObservable h j))).re
noncomputable def vacuumUnits (s h : ℝ) : Matrix (PhaseIndex 1) (PhaseIndex 1) ℝ :=
  diagonalOne s⁻¹ (s / h)
end Gaussian
