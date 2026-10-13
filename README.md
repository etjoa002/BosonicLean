# BosonicLean

The mathematics of bosonic quantum systems, formalized in Lean 4 over Mathlib: Gaussian covariance
matrices, the algebra of the canonical commutation relations (CCR) with its states and Gaussian
channels, and the formal Fock space with its ladder operators and Bargmann picture.

For `n` bosonic modes with positions and momenta `(q₁, …, qₙ, p₁, …, pₙ)`, a Gaussian state is
fixed by its first moments and its covariance matrix `γ` (twice the symmetrized covariance, so
that the vacuum has `γ = I`). A real symmetric matrix is the covariance matrix of a quantum state
exactly when it obeys the uncertainty relation

```
γ − iΩ ≥ 0,      Ω = [[0, I], [−I, 0]],
```

and much of the library proves that this condition, **admissibility**, is preserved by the
operations that build Gaussian states: symplectic changes of coordinates, restriction to
subsystems, independent sums, contraction of virtual modes, and the periodic assembly of Gaussian
matrix product states. Over a general real symplectic space `(V, σ)` the theory is stated for the Weyl
operators, `W(u) W(w) = e^{−iσ(u,w)/2} W(u+w)`, and for the states and Gaussian channels of the
C*-algebra they generate.

## What is proved

| | Statement | Lean files | Notes |
|---|---|---|---|
| Covariance matrices | Admissibility `γ − iΩ ≥ 0` is preserved by symplectic congruence `γ ↦ SγSᵀ` and by restriction to a set of modes; an independent sum `γ₁ ⊕ γ₂` is admissible exactly when both summands are; a one-mode diagonal matrix `diag(a, b)` is admissible exactly when `a > 0` and `ab ≥ 1`; vacuum, squeezed and inadmissible examples; admissible matrices are positive definite | `PhaseSpace/Defs`, `Covariance`, `Subsystem`, `DirectSum`, `Examples`, `Positivity` | BosonicLean §1 |
| Gaussian wave functions | For a width `s > 0`, the Gaussian `ψ(x) = (√π s)^{−1/2} e^{−x²/(2s²)}` is a Schwartz function of norm 1; its first and second moments under position and momentum on a common Schwartz domain; its covariance `diag(s², ħ²/s²)`, which is the vacuum covariance `I` in dimensionless units; for `s² = ħ/(mω)`, the covariance `diag(ħ/(mω), ħmω)` | `Quantum/Defs`, `Quantum/Vacuum`, `Analysis/SchwartzGaussian` | BosonicLean §2 |
| Contraction and Gaussian MPS | Contraction of virtual modes as a Schur complement: for admissible `γ` and a real matrix `K` with `Kᵀ` injective and `KΩKᵀ = diag(0, Ω)`, the eliminated block is positive definite and the output covariance is admissible; periodic chains of `N ≥ 3` sites with EPR wiring give admissible covariances; an explicit correlated three-site covariance; the Fourier block diagonalization of homogeneous periodic covariances and their reconstruction; product covariances as periodic contractions with `M` virtual modes per bond; the covariances of Gaussian kernels `K` (symmetric, with positive definite real part) are admissible; the local resources of the finitely squeezed cluster chain are admissible for `t > 0` and `gᵢ ∈ {0, g}` | `PhaseSpace/Contraction`, `GaussianTNLean/MPS/*` | BosonicLean §3–5 |
| The CCR algebra | Weyl operators on `ℓ²(V)` for an alternating form `σ`: unitarity, the Weyl relation, the CCR algebra `CCR(V, σ)` they generate, Weyl systems; the pullback of a Weyl system along a linear map compatible with the forms, a Weyl system again when the map is onto; relabelling by a symplectic isomorphism as a star isomorphism between the two CCR algebras, functorial in the map; for nondegenerate `σ` the CCR algebra is simple, and every representation on a nonzero Hilbert space is injective; a star automorphism with `T W(u) = c(u) W(Γu)` has `Γ` a symplectic linear bijection and `c` a character of modulus one | `Weyl/Basic`, `System`, `Pullback`, `Relabel`, `Right`, `Simple`, `Primitive`, `Automorphism` | — |
| States and Gaussian states | States on `CCR(V, σ)` and their characteristic functions `χ(u) = ω(W(u))`: positive semidefinite twisted kernels, determination of the state by `χ`, the bound `\|ω(a)\| ≤ ‖a‖`; Gaussian states `χ(u) = exp(i d(u) − γ(u,u)/4)`, whose covariance form satisfies the state condition `γ + iσ ≥ 0` (a necessary condition), in three equivalent forms; no Gaussian state is constructed; the vector state of `δ₀` is constructed | `Weyl/State` | — |
| Gaussian channels | For a given completely positive map with `T(W(u)) = exp(i μ(u) − ν(u,u)/4) W(Lu)` whose data satisfy `ν + iσ − iσ(L·, L·) ≥ 0`: the product formula, concatenation, the noiseless case as a relabelling, the dilation identities at the level of covariances; the data `(d, γ)` of a given Gaussian state transform to `(d∘L + μ, γ(L·, L·) + ν)`; the identity channel and the relabellings by symplectic bijections, with data `(L, 0, 0)`, are examples; for finitely many modes, channel matrices `(X, Y)` with `Y − iΩ + iXΩXᵀ ≥ 0` preserve admissibility; closed unital star subalgebras of a star-ordered C*-algebra are star-ordered, and completely positive maps compose | `Weyl/Channel`, `PhaseSpace/Channel`, `CStar/*` | — |
| The formal Fock space | All coefficient families `ψ(n)` over occupation numbers `n`, with coefficients in any `ℂ`-algebra; the ladder operators and the canonical commutation relations `[aᵢ, aⱼ†] = δᵢⱼ`, without domain conditions; exponentials of operators that raise the particle number, finite sums at each coefficient, with the exponential law `e^{S+T} = e^S e^T` for commuting `S, T`; the Bargmann map, a linear bijection onto formal power series that turns `aⱼ†` into multiplication by `zⱼ` and `aⱼ` into `∂/∂zⱼ` | `Fock/*` | BosonicLean §6 |

No proof is left unfinished, no axiom is added, and no step is delegated to unchecked computation.
The main statements can be checked without reading any proof (see Verification).

## Verification

The core of the library is stated in 67 theorems, listed in [`verify/CORE.md`](verify/CORE.md)
(also `verify/core.pdf`); together they state every result in the table above. Forty-three of them
are main results from the table. Fourteen describe, in terms of Mathlib's definitions, the
definitions of this library on which the statements depend: the symplectic matrix, admissibility,
the contraction, the input and the wiring of a periodic chain, the Weyl operators and the CCR
algebra, the formal Fock space with its ladder operators, raising operators with their
exponential, the Bargmann map, the symbols of a homogeneous periodic chain, the product resource
and the product covariance, the covariance of a Gaussian kernel, the local resource of a cluster
chain, and the relabelling maps. The other ten are examples in which the hypotheses of the main
results hold and the objects are not degenerate: the vacuum, a squeezed and an inadmissible
covariance, the attenuator channel, an explicit three-site chain, the plane `ℝ²` with its
symplectic form and the vacuum data on it, the creation operator as a raising operator, the
identity channel and identity automorphism, the defining representation of the CCR algebra on
`ℓ²(V)`, and a state of the CCR algebra. Entries 1–36 form the first part of the core; entries
37–67 complete it to the whole table and are appended so that the numbers 1–36 are unchanged. By
row of the table, the entries are: covariance matrices 1–7; Gaussian wave functions 8 and 37–40;
contraction and Gaussian matrix product states 9–13 and 41–49 (the Fourier block diagonalization
and reconstruction 41–43, product covariances 44–45, Gaussian kernels and cluster resources
46–49); the CCR algebra 14–18 and 50–55 (Weyl systems and their pullback 50–52, functoriality of
relabelling 53–54, injectivity of representations 55); states and Gaussian states 19–20 and
56–58; Gaussian channels 21–22 and 59–65 (the product formula 59, channels and Gaussian states 60,
the noiseless case 61–62, the dilation identities 63, star-ordered subalgebras 64, composition of
completely positive maps 65); the formal Fock space 23–28; examples 29–36 and 66–67. The Gaussian
state condition (entry 20) is stated as a necessary condition: every Gaussian state satisfies it;
entry 58 states the equivalence of its three forms. No Gaussian state is constructed; entry 60
takes one as given. These statements therefore determine what the library asserts about the
results of the table.

The file `verify/Challenge.lean` states the same 67 theorems in Lean without proofs, and
`verify/core.pdf` is generated from it; `verify/Solution.lean` proves them from the library. The
command

```
lake comparator --config verify/comparator.json --paranoid
```

checks that each theorem proved in `Solution.lean` has exactly the statement given in
`Challenge.lean`, that the proofs use no axioms other than `propext`, `Classical.choice` and
`Quot.sound`, and that Lean's kernel and four independently written proof checkers all accept
the proofs. To accept these results it is therefore enough to read the 67 statements. On Linux the
command compiles the code in a sandbox; on other systems the option `--inadvisably-no-sandbox` is
needed, and the compiled code then runs without that isolation. The scripts
`verify/check_same_statements.py` and `verify/make_core_page.py --check` confirm, in a few
seconds, that the two Lean files state the same theorems and that the page is generated from the
current `Challenge.lean`. The same checks run on GitHub's machines at every change
(`.github/workflows/comparator.yml`).

`lake comparator` is the proof judge maintained by the Lean developers
([leanprover/comparator](https://github.com/leanprover/comparator)), available as a command of
Lean's build tool `lake` from Lean 4.35. It is meant for proofs whose author is not trusted. The
Lean reference manual, in its chapter
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator),
presents it as the strongest of its levels of checking, intended among other cases for proofs
produced by AI. The judge takes the statements from a file fixed in advance (here
`Challenge.lean`), exports the declarations of both files to a plain text format, and compares
them there; it does not load the compiled library into its own process. With `--paranoid` it also
runs four further proof checkers, written independently of Lean's kernel, among them lean4lean
([digama0/lean4lean](https://github.com/digama0/lean4lean)), written in Lean, and nanoda
([ammkrn/nanoda_lib](https://github.com/ammkrn/nanoda_lib)), written in Rust; a proof is accepted
only if every checker accepts it. The judge takes as given what `Challenge.lean` imports: Lean's
own library, Mathlib, and the definitions of this library on which the statements depend, which
is why the statements include descriptions of those definitions in Mathlib's terms. Two facts
that carry no data are also taken from the library: the CCR algebra, with the order of operators,
is a star-ordered ring (so that completely positive maps apply to it; entry 64 states this
property for every norm-closed unital star subalgebra of a star-ordered C*-algebra), and it is not
the zero algebra.

## Methods of proof

Admissibility is the positivity of a Hermitian matrix, and each operation on Gaussian states acts
on it by a congruence, a direct sum or a Schur complement, all of which preserve positivity; the
contraction of the virtual modes of a Gaussian matrix product state, physically a projection onto
EPR pairs, is proved as a Schur complement of the covariance matrix, and the periodic chain is
assembled from it. The CCR algebra is realized concretely on `ℓ²(V)` with `V` discrete, where Weyl
operators are translations weighted by a phase. On the formal Fock space, the exponential of an
operator that raises the particle number is defined coefficient by coefficient, and every
coefficient is a finite sum, so no question of convergence arises; the Bargmann map turns creation
into multiplication by `zⱼ` and annihilation into `∂/∂zⱼ`, and turns the exponential of
`X (aⱼ†)ᵖ` into multiplication by a power series in `zⱼ`.

## The notes

The notes give the readable account, with proofs, examples and a dictionary to the physics
literature. [`docs/lecture-notes/BosonicLean.pdf`](docs/lecture-notes/BosonicLean.pdf) covers
covariance matrices (§1), normalized Gaussian wave functions (§2), contraction and periodic
Gaussian matrix product states (§3), homogeneous periodic covariances and their Fourier transform
(§4), product covariances (§5), and the formal Fock space with the Bargmann picture (§6). A tag
beside a theorem links to the Lean declaration that proves it. The CCR algebra, its states and
the Gaussian channels are documented in the Lean files, and their main statements in
`verify/CORE.md`.

## Library layout

Each Lean file and the library files it imports:

<!-- depgraph:start -->
- `BosonicLean/`
  - `PhaseSpace/`
    - `PhaseSpace/Channel` imports `PhaseSpace/Defs`, `Weyl/State`
    - `PhaseSpace/ConstructionDefs` imports `PhaseSpace/Defs`
    - `PhaseSpace/Contraction` imports `PhaseSpace/ContractionDefs`, `PhaseSpace/Positivity`
    - `PhaseSpace/ContractionDefs` imports `PhaseSpace/Defs`
    - `PhaseSpace/Covariance` imports `PhaseSpace/Defs`
    - `PhaseSpace/Defs` imports Mathlib only
    - `PhaseSpace/DirectSum` imports `PhaseSpace/ConstructionDefs`, `PhaseSpace/Subsystem`
    - `PhaseSpace/Examples` imports `PhaseSpace/ConstructionDefs`
    - `PhaseSpace/OneMode` imports `PhaseSpace/Defs`
    - `PhaseSpace/Positivity` imports `PhaseSpace/Defs`
    - `PhaseSpace/Subsystem` imports `PhaseSpace/Defs`
  - `Quantum/`
    - `Quantum/Defs` imports `PhaseSpace/Examples`
    - `Quantum/Vacuum` imports `Quantum/Defs`, `Analysis/SchwartzGaussian`
  - `Analysis/`
    - `Analysis/BinomialSqrt` imports `Analysis/PowerBound`
    - `Analysis/ExpGenSeries` imports Mathlib only
    - `Analysis/Kronecker` imports `Analysis/PowerBound`
    - `Analysis/Majorant` imports Mathlib only
    - `Analysis/PowerBound` imports Mathlib only
    - `Analysis/ProductSeries` imports Mathlib only
    - `Analysis/SchwartzGaussian` imports Mathlib only
  - `CStar/`
    - `CStar/Commute` imports Mathlib only
    - `CStar/CompletelyPositive` imports Mathlib only
    - `CStar/Examples` imports `CStar/Commute`
    - `CStar/Primitive` imports Mathlib only
    - `CStar/StarOrdered` imports Mathlib only
  - `Weyl/`
    - `Weyl/Automorphism` imports `Weyl/Simple`
    - `Weyl/Basic` imports Mathlib only
    - `Weyl/Channel` imports `CStar/StarOrdered`, `CStar/CompletelyPositive`, `Weyl/Relabel`, `Weyl/State`
    - `Weyl/Primitive` imports `CStar/Primitive`, `Weyl/Simple`
    - `Weyl/Pullback` imports `Weyl/System`
    - `Weyl/Relabel` imports `Weyl/System`
    - `Weyl/Right` imports `Weyl/System`, `CStar/Commute`
    - `Weyl/Simple` imports `Weyl/Right`
    - `Weyl/State` imports `Weyl/Automorphism`
    - `Weyl/System` imports `Weyl/Basic`
  - `GaussianTNLean/`
    - `GaussianTNLean/MPS/Cluster` imports `GaussianTNLean/MPS/ClusterDefs`
    - `GaussianTNLean/MPS/ClusterDefs` imports `PhaseSpace/Defs`
    - `GaussianTNLean/MPS/Fourier` imports `GaussianTNLean/MPS/Periodic`
    - `GaussianTNLean/MPS/Periodic` imports `PhaseSpace/Contraction`
    - `GaussianTNLean/MPS/Product` imports `PhaseSpace/DirectSum`, `PhaseSpace/Examples`, `GaussianTNLean/MPS/Periodic`
    - `GaussianTNLean/MPS/ThreeSite` imports `GaussianTNLean/MPS/ThreeSiteBlocks`, `PhaseSpace/Covariance`, `PhaseSpace/DirectSum`, `PhaseSpace/Examples`
    - `GaussianTNLean/MPS/ThreeSiteArithmetic` imports `GaussianTNLean/MPS/Periodic`
    - `GaussianTNLean/MPS/ThreeSiteBlocks` imports `GaussianTNLean/MPS/ThreeSiteArithmetic`
  - `Fock/`
    - `Fock/Bargmann` imports `Fock/RaisingExp`
    - `Fock/Formal` imports Mathlib only
    - `Fock/Ladder` imports `Fock/Formal`
    - `Fock/RaisingExp` imports `Fock/Ladder`
  - `Examples/`
    - `Examples/Vacuum` imports `BosonicLean.lean`
- `Verify/`
  - `Verify/Challenge` imports `BosonicLean.lean`
  - `Verify/Solution` imports `BosonicLean.lean`
<!-- depgraph:end -->

`PhaseSpace/` finite modes and covariance matrices; `Quantum/` one-mode wave functions;
`Analysis/` the analysis the bosonic theory needs (the Schwartz Gaussian, power bounds, majorant
and binomial series, Kronecker products, products of series); `CStar/` general C*-algebra facts;
`Weyl/` the CCR algebra, states, Gaussian states and channels over a general symplectic space;
`GaussianTNLean/` Gaussian matrix product states; `Fock/` the formal Fock space; `Examples/` a
small usage example (not part of `lake build BosonicLean`); `verify/` the 67 statements and their
proofs (see Verification).

## Dependencies

| Library | Role | Version fixed in |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | mathematics library of Lean | `lakefile.toml`, `lake-manifest.json` |

The Lean version is fixed in `lean-toolchain`. The libraries that build on this one
([LinearAQFT](https://github.com/etjoa002/LinearAQFT), [QCALean](https://github.com/etjoa002/QCALean),
[LocalityLean](https://github.com/etjoa002/LocalityLean)) fix the same versions, and the versions
are only ever changed together.

## Build and verify

With the Lean installer `elan` (which reads the Lean version from `lean-toolchain`):

```
git clone https://github.com/etjoa002/BosonicLean
cd BosonicLean
lake exe cache get          # download the precompiled Mathlib
lake build BosonicLean
lake comparator --config verify/comparator.json --paranoid   # see "Verification"
```

The precompiled Mathlib saves hours of compilation.

## Conventions

Coordinates list all positions before all momenta, `Ω = [[0, I], [−I, 0]]`, and covariance
matrices are twice the symmetrized covariance (vacuum `I`), with admissibility `γ − iΩ ≥ 0`. On a
general symplectic space a Gaussian state has `χ(u) = exp(i d(u) − γ(u,u)/4)`, and its covariance
form satisfies the state condition `γ + iσ ≥ 0`, the complex conjugate form of admissibility. The
formal Fock space carries no summability condition; the Hilbert space `Γₛ` is its square-summable part. See
`CONVENTIONS.md`.

## Scope

The constructions of Gaussian states from other Gaussian states (restriction, independent sums,
contraction, periodic chains, channel matrices) are theorems about covariance matrices; on
Hilbert space, the one-mode Gaussian wave function is a Schwartz function of norm 1. A Gaussian
channel is a completely positive map by definition, and its data satisfy the channel condition.
For Gaussian states of the CCR algebra the state condition is proved necessary; no Gaussian state
of the CCR algebra is constructed, and the one state constructed outright is the vector state of
`δ₀`. On the formal Fock space,
exponentials are defined for operators that raise the particle number.

## Status

The library is under development, and this repository is updated as the work progresses. Problem
reports and suggestions are welcome; see `CONTRIBUTING.md`. Planned next are notes for the CCR
algebra, its states and the Gaussian channels; two-dimensional Gaussian tensor networks and matrix
product operators; and the connection between the covariance-matrix picture and the formal Fock
space. Candidates for later theorems: the existence of a Gaussian state for every covariance form
that satisfies the state condition; that data satisfying the channel condition always define a
completely positive map (Demoen–Vanheuverzwijn–Verbeure); exponentials of operators that lower the
particle number, such as displacement and squeezing operators; continuous-variable measurements
and the Choi representation of Gaussian channels. Bosonic matrix product states built on the
formal Fock space (Tjoa and Cirac, arXiv:2607.28753) are formalized in a companion library that
is not yet public.

## Citation and licence

Erickson Tjoa, *BosonicLean: bosonic quantum mathematics in Lean*, 2026,
https://github.com/etjoa002/BosonicLean. The mathematical sources are cited in the notes and in
the Lean files.

Apache 2.0 (`LICENSE`, `NOTICE`; `NOTICE` lists the files that originate in the TNLean project).
`CITATION.cff` gives this reference in machine-readable form; GitHub shows it as "Cite this
repository".

Developed with AI assistance. The author approved every definition and theorem statement and is
responsible for the content; every proof is checked by Lean.
