# BosonicLean

The mathematics of bosonic quantum systems, formalized in Lean 4 over Mathlib: Gaussian covariance
matrices, the algebra of the canonical commutation relations (CCR) with its states and Gaussian
channels, and the formal Fock space.

For `n` modes with coordinates `(q₁, …, qₙ, p₁, …, pₙ)`, a real symmetric matrix `γ` is the
covariance matrix of a quantum state exactly when it is **admissible**,

```
γ − iΩ ≥ 0,      Ω = [[0, I], [−I, 0]],
```

with the normalization in which the vacuum has `γ = I`. Much of the library proves that the
operations which build Gaussian states preserve admissibility. Over a general real symplectic
space `(V, σ)` the theory is stated for the Weyl operators, `W(u) W(w) = e^{−iσ(u,w)/2} W(u+w)`,
and the C*-algebra they generate.

## What is proved

| | Main results | Notes |
|---|---|---|
| Covariance matrices | Admissibility is preserved by symplectic congruence and restriction to subsystems; `γ₁ ⊕ γ₂` is admissible exactly when both summands are; admissible matrices are positive definite | §1 |
| Gaussian wave functions | The one-mode Gaussian is a normalized Schwartz function whose covariance is `diag(s², ħ²/s²)`, the vacuum covariance for `s² = ħ/(mω)` | §2 |
| Gaussian matrix product states | Contraction of virtual modes, as a Schur complement, preserves admissibility; periodic chains, their Fourier block diagonalization, product covariances, Gaussian kernels and the finitely squeezed cluster chain | §3–5 |
| The CCR algebra | Weyl operators on `ℓ²(V)` and the Weyl relation; Weyl systems and their pullback; relabelling by symplectic isomorphisms; for nondegenerate `σ` the algebra is simple, and its automorphisms of Weyl form are symplectic | |
| States and Gaussian states | States are determined by their characteristic functions `χ(u) = ω(W(u))`; the covariance form of a Gaussian state satisfies `γ + iσ ≥ 0` | |
| Gaussian channels | The transformation of Gaussian data under a channel, concatenation, the noiseless case and the dilation identities; for finitely many modes, channel matrices preserve admissibility | |
| The formal Fock space | Ladder operators with `[aᵢ, aⱼ†] = δᵢⱼ`; exponentials of operators that raise the particle number; the Bargmann map to formal power series, with `aⱼ† ↦ zⱼ` and `aⱼ ↦ ∂/∂zⱼ` | §6 |

The precise statements are the 67 theorems of [`verify/CORE.md`](verify/CORE.md), grouped by the
rows of this table. The condition `γ + iσ ≥ 0` is proved necessary for a Gaussian state; a Gaussian
channel is a completely positive map by definition. Conventions are listed in `CONVENTIONS.md`.

## Verification

The 67 theorems of the core are 43 main results, fourteen statements that describe the
library's definitions in Mathlib's terms, and ten examples (the vacuum, a squeezed covariance, the
attenuator channel, a state of the CCR algebra, and others) in which the hypotheses hold and the
objects are not degenerate. `verify/Challenge.lean` states them without proofs, and
`verify/Solution.lean` proves them from the library. The command

```
lake comparator --config verify/comparator.json --paranoid
```

checks that every proved theorem has exactly the stated form, that no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` are used, and that Lean's kernel and four independently
written proof checkers accept every proof. A reader who accepts the 67 statements therefore need
not read any proof. Besides the definitions described in the core, two properties of the CCR
algebra are taken from the library: it is a star-ordered ring, and it is not the zero algebra. The
same check runs on GitHub at every change.

`lake comparator` is the proof judge maintained by the Lean developers for proofs whose author is
not trusted, including proofs produced by AI; see
[leanprover/comparator](https://github.com/leanprover/comparator) and the chapter
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator)
of the Lean reference manual. Among its checkers are
[lean4lean](https://github.com/digama0/lean4lean) and [nanoda](https://github.com/ammkrn/nanoda_lib).
On Linux it isolates the compiled code in a sandbox; elsewhere it needs the option
`--inadvisably-no-sandbox`.

## Build and verify

With the Lean installer `elan`:

```
git clone https://github.com/etjoa002/BosonicLean
cd BosonicLean
lake exe cache get          # download the precompiled Mathlib
lake build BosonicLean
lake comparator --config verify/comparator.json --paranoid
```

The library depends only on [Mathlib](https://github.com/leanprover-community/mathlib4); the
versions of Lean and Mathlib are fixed in `lean-toolchain` and `lake-manifest.json`, and the
libraries built on this one fix the same versions.

## Methods of proof

Each operation on Gaussian states acts on the admissibility matrix by a congruence, a direct sum
or a Schur complement, all of which preserve positivity; the contraction of virtual modes,
physically a projection onto EPR pairs, is a Schur complement. The CCR algebra is realized on
`ℓ²(V)` with `V` discrete, where Weyl operators are phase-weighted translations. On the formal
Fock space every coefficient of an exponential is a finite sum, so no question of convergence
arises.

## The notes

[`docs/lecture-notes/BosonicLean.pdf`](docs/lecture-notes/BosonicLean.pdf) gives the account with
proofs, examples and a dictionary to the physics literature, in the sections listed in the table
above. A tag beside a theorem links to the Lean declaration that proves it.

## Library layout

`PhaseSpace/` covariance matrices; `Quantum/` one-mode wave functions; `Analysis/` supporting
analysis; `CStar/` C*-algebra facts; `Weyl/` the CCR algebra, its states and channels;
`GaussianTNLean/` Gaussian matrix product states; `Fock/` the formal Fock space; `verify/` the core.

<details>
<summary>Lean files and their imports</summary>

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

</details>

## Status

The library is under development, and this repository is updated as the work progresses; see
`CONTRIBUTING.md` for problem reports and suggestions. Planned next are notes for the CCR algebra
and its states and channels, two-dimensional Gaussian tensor networks, and the connection between
covariance matrices and the formal Fock space. Candidates for later theorems: a Gaussian state for
every covariance form satisfying `γ + iσ ≥ 0`; complete positivity of every map whose data satisfy
the channel condition (Demoen–Vanheuverzwijn–Verbeure); exponentials of operators that lower the
particle number, such as displacement and squeezing; the Choi representation of Gaussian channels.

## Citation and licence

Erickson Tjoa, *BosonicLean: bosonic quantum mathematics in Lean*, 2026,
https://github.com/etjoa002/BosonicLean. Apache 2.0 (`LICENSE`, `NOTICE`; `NOTICE` lists the files
that originate in the TNLean project); `CITATION.cff` gives the reference in machine-readable form.

Developed with AI assistance. The author approved every definition and theorem statement and is
responsible for the content; every proof is checked by Lean.
