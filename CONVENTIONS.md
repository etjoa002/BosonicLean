# Conventions

## Mathematics

### Phase space and covariance matrices

- Coordinates of `n` modes list all positions before all momenta, `(q₁, …, qₙ, p₁, …, pₙ)`. The
  symplectic matrix is `Ω = [[0, I], [−I, 0]]`, the negative of Mathlib's `Matrix.J`; it satisfies
  `Ωᵀ = −Ω = Ω⁻¹`.
- A covariance matrix is twice the symmetrized covariance, `γ = 2V`, so that a dimensionless vacuum
  has `γ = I`. A real matrix is admissible when it is symmetric and `γ − iΩ ≥ 0`; this is
  equivalent to `γ + iΩ ≥ 0` by complex conjugation, and for `V = γ/2` to `V − (i/2)Ω ≥ 0`. The
  mode-by-mode ordering `(q₁, p₁, …, qₙ, pₙ)` of much of the literature differs by a permutation of
  coordinates, which leaves admissibility unchanged.
- Admissibility is a statement about matrices. A Gaussian state is constructed only where stated:
  the one-mode Gaussian wave functions, and the Gaussian states of the CCR algebra.
- One-mode wave functions are Schwartz functions inside `L²(ℝ)`; position acts by `x`, momentum by
  `−iħ d/dx`.

### The CCR algebra

- `V` is a real vector space and `σ` an alternating bilinear form on it, nondegenerate only where a
  theorem says so. The Weyl operator acts on `ℓ²(V)` (with `V` discrete) by
  `(W(u)ψ)(v) = e^{iσ(u,v)/2} ψ(v+u)`, and `W(u) W(w) = e^{−iσ(u,w)/2} W(u+w)`.
- A Gaussian state has characteristic function `χ(u) = ω(W(u)) = exp(i d(u) − γ(u,u)/4)`, and its
  covariance form satisfies `γ + iσ ≥ 0` on every finite family of vectors. For finitely many modes
  this is the complex conjugate of the matrix condition above; the two conventions are converted in
  one place (`PhaseSpace/Channel`).
- A Gaussian channel sends `W(u)` to `exp(i μ(u) − ν(u,u)/4) W(Lu)`; complete positivity is part of
  its definition. Automorphisms and channels compose as `T₂ ∘ T₁`.

### The formal Fock space

- Number states `∣n⟩ = (a†)ⁿ∣0⟩/√(n!)`, so that `a†∣n⟩ = √(n+1)∣n+1⟩` and `a∣n⟩ = √n∣n−1⟩`. For
  several modes, `n` is a finitely supported family of occupation numbers, `n! = ∏ᵢ nᵢ!`, and the
  total particle number is `∣n∣ = Σᵢ nᵢ`.
- The formal Fock space consists of all coefficient families `n ↦ ψ(n)`, with no summability
  condition; the bosonic Fock space `Γₛ` is its square-summable part, and the finite-particle space
  its finitely supported part. Coefficients may lie in any `ℂ`-algebra, in particular in a matrix
  algebra, which need not be commutative.
- An exponential `e^T` is defined for order-raising `T` (a vector with no component below `k`
  particles is sent to one with no component below `k + 1`) as a finite sum at each coefficient.
- The Bargmann map sends `∣n⟩` to `zⁿ/√(n!)`, onto formal power series.

### Analysis

- Matrix norms in `Analysis/` are the `ℓ^∞` operator norm (largest absolute row sum). A power
  bound `(C, r)` of `X` means `‖Xᵐ‖ ≤ C rᵐ` for all `m`; in a complex Banach algebra one exists for
  every `r` above the spectral radius, which does not depend on the norm.
- Inner products are linear in the second argument.

## Lean

- One definition per concept; libraries that build on this one import it rather than redefine it.
  A declaration lives in the most general library that can state it.
- Namespaces: `Gaussian` for the finite-mode covariance theory, `BosonicLean.Weyl` for the CCR
  algebra, `BosonicLean.Fock` for the formal Fock space, `BosonicLean` and `BosonicLean.CStar` for
  general analysis and C*-algebra facts.
- Declaration names are ASCII and follow Mathlib's naming and style.
- No unfinished proofs, no added axioms, no unchecked computation, no blanket import of Mathlib;
  assumptions are hypotheses or structure fields.
- Imports: Mathlib only.
