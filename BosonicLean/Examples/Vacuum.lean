import BosonicLean
/-! Two examples that use the library through its root file: the normalized Gaussian wave
function of a second width with its covariance, and the admissible one-mode vacuum covariance. -/

open Gaussian

-- The Gaussian of width `s = 2` is a normalized state, with covariance `diag(4, 1/4)` for `ħ = 1`.
example : ∃ ψ : OneModeState, IsVacuum 2 ψ ∧
    oneModeCovariance 1 ψ = diagonalOne 4 (1 / 4) := by
  obtain ⟨ψ, hψ, _⟩ := vacuum_exists_unique (s := 2) (by norm_num)
  refine ⟨ψ, hψ, ?_⟩
  have hc := (vacuum_covariance (s := 2) (h := 1) (by norm_num) (by norm_num) ψ hψ).1
  norm_num at hc
  exact hc

-- The one-mode vacuum covariance `diag(1, 1)` is admissible.
example : IsAdmissible (diagonalOne 1 1) := isAdmissible_vacuumOne
