/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean

/-!
# The core statements of BosonicLean

This file states, without proofs, the main theorems of BosonicLean on bosonic Gaussian systems:
admissible covariance matrices and the operations that preserve admissibility, the normalized
Gaussian wave function and its covariance, the contraction of virtual modes and periodic Gaussian
matrix product states, the CCR algebra of the Weyl operators on $\ell^2(V)$, its states and Gaussian
states, Gaussian channels, and the formal Fock space with its ladder operators, the exponential
of operators that raise the particle number and the Bargmann map, followed by a section of
examples. Further sections,
appended after the examples so that the numbering of entries 1 to 36 stays fixed, state the
other results listed in the table of results on the front page of the library: the Schwartz
domain, the moments and the units of the Gaussian wave function, the Fourier analysis of
homogeneous periodic chains, product covariances, Gaussian kernels and cluster resources, Weyl
systems, the functoriality of relabelling, the injectivity of representations, the twisted
kernels and the norm bound of states, the three forms of the state condition, the product
formula, the action on Gaussian states, the noiseless case and the dilations of Gaussian
channels, star-ordered subalgebras and the composition of completely positive maps, with two
further examples.

The statements are written in Mathlib's vocabulary as far as possible: states, Gaussian states
and Gaussian channels are stated through their defining properties (continuous functionals,
completely positive maps of Mathlib, explicit characteristic functions), not through the
library's structures. The statements still use these definitions of the library, each fixed in
Mathlib's terms by a theorem below: the symplectic matrix (entry 1), admissibility (entry 2),
the contraction (entry 9), the input and the wiring of a periodic chain (entries 11 and 12),
the Weyl operators and the CCR algebra (entry 14), the formal Fock space with its linear
structure and the ladder operators, by their coefficient formulas (entry 23), operators that
raise the particle number
and their exponential (entries 25 and 26), the Bargmann map (entry 27), the eliminated and the
covariance symbols of a homogeneous chain (entry 41), the product resource and the product
covariance (entry 44), the kernel covariance (entry 46), the local resource of a cluster chain
(entry 47), and the relabelling unitary and relabelling isomorphism (entry 53). The library also
supplies two instances that carry no data: the CCR algebra, a closed star subalgebra of the
bounded operators with the order of operators, is a star-ordered ring (needed for completely
positive maps; entry 64 states this property for every norm-closed unital star subalgebra of a
star-ordered C*-algebra), and it is not the zero algebra.

Sections appended after entry 67 state the results of the later chapters of the lecture notes:
anti-normal ordering for one mode, the bosonic Fock space with its closed maximal realizations and
closed forms, second quantization, the Bloch–Messiah and polar decompositions of symplectic
matrices, exponential vectors and the displacement and squeezing operators, Gaussian unitaries on
Fock space and pure Gaussian states, followed by examples. They use these further definitions of
the library, each fixed in Mathlib's terms by a theorem below: the Fock space, its embedding into
the formal Fock space and the squared norm of formal vectors (entry 69), the maximal realization
(entry 70), the second quantization (entry 72), its unitary on the Fock space (entry 74) and the
generator (entry 75), the squeezing matrix and the orthogonal symplectic matrix of a unitary
(entry 77), the exponential vectors (entry 82), the displacement and squeezing operators (entries
84 and 88; their values or matrix elements on exponential vectors determine them by entry 83), the
Weyl operators on Fock space (entry 90), Gaussian unitaries (entry 91), the quadratures (entry 95)
and Gaussian characteristic functions (entry 97).

Two sections appended after entry 105 state the existence of pure Gaussian states for every
admissible symplectic covariance matrix, and the results of the chapter on quadratic Hamiltonians:
one-parameter unitary groups and their generators, analytic vectors with a common radius, the
essential self-adjointness of a quadratic Hamiltonian on the finitely supported vectors, the
Gaussian unitaries it generates, and Eqs. (1) and (5) of Tjoa and Cirac. They use these further
definitions of the library, each fixed in Mathlib's terms by a theorem below: strongly continuous
one-parameter unitary groups and their generators (entry 107), the finitely supported vectors and
the quadratic Hamiltonian (entry 111), and the Hamiltonian of Eq. (1) of Tjoa and Cirac with its
real matrix (entry 115).

Every statement here is closed by `sorry`. The file `Solution.lean` in this folder repeats each
statement with the identical text and proves it. The tool `lake comparator`, configured by
`comparator.json` in this folder, checks that each theorem named there has exactly the same
statement in both files and that its proof in `Solution.lean` uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. The script `check_same_statements.py` checks the
same correspondence on the text of the two files.

Conventions. Phase-space coordinates of $n$ modes are indexed by the disjoint union of two
copies of $\{1, \dots, n\}$, positions before momenta. The covariance matrix is normalized so
that the vacuum is the identity, and admissibility is $\gamma - i\Omega \ge 0$. The Weyl
relation carries the sign $W(u) W(w) = e^{-i\sigma(u,w)/2} W(u+w)$. A complex matrix is
positive semidefinite as defined in the first section, and $0 \le z$ for a complex number
$z$ means that $z$ is real and non-negative.
-/

open Gaussian BosonicLean.Weyl BosonicLean.Fock BosonicLean.Fock.FormalFock

open scoped Matrix ComplexOrder ComplexConjugate CStarAlgebra

namespace Sealed

/-! ## Covariance matrices

A phase-space index of $n$ modes is an element of $\mathrm{Fin}\, n \oplus \mathrm{Fin}\, n$: the
positions $q_1, \dots, q_n$ followed by the momenta $p_1, \dots, p_n$.
A real matrix is regarded as a complex matrix entrywise, and a complex matrix $H$ is positive
semidefinite, $H \ge 0$, when it is Hermitian with $\bar x^T H x \ge 0$ for every complex
vector $x$. -/

/-- The standard symplectic matrix on $n$ modes is $\Omega = \begin{pmatrix} 0 & 1 \\ -1 & 0
\end{pmatrix}$ in the blocks of positions and momenta. -/
theorem symplecticForm_eq (n : ℕ) :
    symplecticForm n = Matrix.fromBlocks 0 1 (-1) 0 := sorry

/-- A real $2n \times 2n$ matrix $\gamma$ is an admissible covariance matrix if and only if it is
symmetric and $\gamma - i\Omega \ge 0$. -/
theorem isAdmissible_iff {n : ℕ} (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    IsAdmissible γ ↔ γᵀ = γ ∧
      (γ.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef := sorry

/-- Symplectic congruence: a real $2n \times 2n$ matrix $S$ is symplectic when
$S \Omega S^T = \Omega$. If $\gamma$ is admissible and $S$ is symplectic, then $S \gamma S^T$ is
admissible. -/
theorem isAdmissible_symplectic_congr {n : ℕ}
    {γ S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hγ : IsAdmissible γ)
    (hS : S * symplecticForm n * Sᵀ = symplecticForm n) : IsAdmissible (S * γ * Sᵀ) := sorry

/-- Restriction to a set of modes: if $\gamma$ is admissible on $n$ modes and $e$ is an injective
map from $m$ modes to the $n$ modes, the matrix with entries $\gamma(e(a), e(b))$, positions
going to positions and momenta to momenta, is admissible on $m$ modes. -/
theorem isAdmissible_restrict {m n : ℕ} {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    {e : Fin m → Fin n} (hγ : IsAdmissible γ) (he : Function.Injective e) :
    IsAdmissible (γ.submatrix (Sum.map e e) (Sum.map e e)) := sorry

/-- Independent sums: for $\gamma_1$ on $n$ modes and $\gamma_2$ on $m$ modes, the block-diagonal
matrix $\gamma_1 \oplus \gamma_2$ on $n + m$ modes, in which the first $n$ modes carry $\gamma_1$
and the last $m$ modes carry $\gamma_2$, is admissible if and only if $\gamma_1$ and $\gamma_2$
are. -/
theorem isAdmissible_directSum_iff {n m : ℕ} (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    IsAdmissible ((Matrix.fromBlocks A 0 0 B).submatrix
        (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
          (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)))
        (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
          (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)))) ↔
      IsAdmissible A ∧ IsAdmissible B := sorry

/-- One mode: the diagonal matrix $\mathrm{diag}(a, b)$ is admissible if and only if $a > 0$ and
$ab \ge 1$. -/
theorem isAdmissible_diagonal_iff (a b : ℝ) :
    IsAdmissible (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))) ↔
      0 < a ∧ 1 ≤ a * b := sorry

/-- Every admissible matrix $\gamma$ is positive definite: $x^T \gamma x > 0$ for every
nonzero real vector $x$. -/
theorem posDef_of_isAdmissible {n : ℕ} {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hγ : IsAdmissible γ) : γ.PosDef := sorry

/-! ## The Gaussian wave function

Admissibility, $\gamma - i\Omega \ge 0$, is the uncertainty relation in units with $\hbar = 1$.
By entry 6, the covariance $\mathrm{diag}(s^2, \hbar^2/s^2)$ of the next entry is admissible
exactly when $\hbar \ge 1$; with $\hbar = 1$ it is $\mathrm{diag}(s^2, 1/s^2)$, admissible for
every $s > 0$. -/

/-- Let $s > 0$, $\hbar > 0$ and $\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}$ on
$\mathbb R$. Then $\int |\psi|^2\, dx = 1$. Let $A_q \psi = x\psi$ and $A_p \psi = -i\hbar\psi'$
be the position and momentum applied to $\psi$, $m_j = \mathrm{Re} \int \bar\psi\, A_j\psi\, dx$
their means, and $\gamma_{jk} = 2\, \mathrm{Re} \int \overline{(A_j\psi - m_j\psi)}\,
(A_k\psi - m_k\psi)\, dx$ for $j, k \in \{q, p\}$. Then
$\gamma = \mathrm{diag}(s^2, \hbar^2/s^2)$. -/
theorem gaussian_wave_function {s ħ : ℝ} (hs : 0 < s) (hħ : 0 < ħ) (ψ : ℝ → ℂ)
    (hψ : ∀ x, ψ x = ((1 / Real.sqrt (Real.sqrt Real.pi * s) *
      Real.exp (-x ^ 2 / (2 * s ^ 2)) : ℝ) : ℂ))
    (A : Fin 1 ⊕ Fin 1 → ℝ → ℂ)
    (hA : ∀ x, A (Sum.inl 0) x = x * ψ x ∧ A (Sum.inr 0) x = -Complex.I * ħ * deriv ψ x) :
    ∫ x, ‖ψ x‖ ^ 2 = 1 ∧
      Matrix.of (fun j k => 2 * (∫ x,
          conj (A j x - ((∫ y, conj (ψ y) * A j y).re : ℂ) * ψ x) *
            (A k x - ((∫ y, conj (ψ y) * A k y).re : ℂ) * ψ x)).re) =
        Matrix.diagonal (Sum.elim (fun _ => s ^ 2) (fun _ => ħ ^ 2 / s ^ 2)) := sorry

/-! ## Contraction and periodic chains

A Gaussian matrix product state is obtained from an independent covariance matrix of physical
and virtual modes by eliminating the virtual modes, which is a Schur complement. -/

/-- The contraction: for a real $2n \times 2n$ matrix $\gamma$ and a real matrix $K$ with
$k + 2m$ rows and $2n$ columns, let $V = K \gamma K^T$ with blocks $E$ (the first $k$ rows and
columns), $F$ (the first $k$ rows, the last $2m$ columns), $F'$ (the last $2m$ rows, the first
$k$ columns) and $G$ (the last $2m$ rows and columns). The contracted covariance is the Schur
complement $G - F' E^{-1} F$, where $E^{-1}$ is the matrix inverse ($E$ is invertible by the next
statement). -/
theorem contractCovariance_eq {n m k : ℕ} (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (W : Matrix (Fin k ⊕ (Fin m ⊕ Fin m)) (Fin n ⊕ Fin n) ℝ) :
    contractCovariance γ W =
      (W * γ * Wᵀ).submatrix Sum.inr Sum.inr -
        (W * γ * Wᵀ).submatrix Sum.inr Sum.inl * ((W * γ * Wᵀ).submatrix Sum.inl Sum.inl)⁻¹ *
          (W * γ * Wᵀ).submatrix Sum.inl Sum.inr := sorry

/-- Contraction preserves admissibility: let $\gamma$ be admissible on $n$ modes and $K$ a real
matrix with $k + 2m$ rows and $2n$ columns whose rows are linearly independent ($K^T$ is
injective) and with $K \Omega K^T = \begin{pmatrix} 0 & 0 \\ 0 & \Omega \end{pmatrix}$, the
lower right block being the symplectic matrix of $m$ modes. Then the block $E$ of
$K\gamma K^T$ is positive definite and the contracted covariance is admissible on $m$ modes. -/
theorem isAdmissible_contractCovariance {n m k : ℕ}
    (W : Matrix (Fin k ⊕ (Fin m ⊕ Fin m)) (Fin n ⊕ Fin n) ℝ)
    {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hγ : IsAdmissible γ)
    (hW : Function.Injective Wᵀ.mulVec)
    (hΩ : W * symplecticForm n * Wᵀ =
      Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℝ) 0 0 (symplecticForm m)) :
    ((W * γ * Wᵀ).submatrix Sum.inl Sum.inl).PosDef ∧ IsAdmissible (contractCovariance γ W) := sorry

/-- The input of a periodic chain: $N$ sites, each with $2M + 1$ local modes, and real
$2(2M+1) \times 2(2M+1)$ matrices $\Gamma_j$, one for each site $j$. Mode $l$ of site $j$ is the
global mode $(2M+1) j + l$. The input matrix is block diagonal: its entry between the global
coordinates of the local coordinates $u$ of site $j$ and $v$ of site $j'$ is $\Gamma_j(u, v)$ if
$j = j'$ and $0$ otherwise. -/
theorem periodicInput_apply {N M : ℕ}
    (Γ : Fin N → Matrix (Fin (M + M + 1) ⊕ Fin (M + M + 1)) (Fin (M + M + 1) ⊕ Fin (M + M + 1)) ℝ)
    (j j' : Fin N) (u v : Fin (M + M + 1) ⊕ Fin (M + M + 1)) :
    periodicInput Γ
        (Sum.map (fun l => finProdFinEquiv (j, l)) (fun l => finProdFinEquiv (j, l)) u)
        (Sum.map (fun l => finProdFinEquiv (j', l)) (fun l => finProdFinEquiv (j', l)) v) =
      if j = j' then Γ j u v else 0 := sorry

/-- The wiring of a periodic chain: each site $i$ of $N$ has $M$ virtual modes $A_{i,a}$ (local
modes $0, \dots, M-1$), $M$ virtual modes $B_{i,a}$ (local modes $M, \dots, 2M-1$) and one
physical mode $C_i$ (local mode $2M$), numbered globally as for the input. The wiring matrix $K$
has $2NM$ rows to be eliminated followed by $2N$ rows for the physical modes. Write $e_x$ for the
standard basis vector of the global coordinate $x$, and $i - 1$ for the site before $i$, cyclically
(the inverse of the rotation $j \mapsto j + 1 \bmod N$). For each site $i$ and
$a < M$, the row $Mi + a$ of $K$ is $e_{q(A_{i,a})} + e_{q(B_{i-1,a})}$ and the row $NM + Mi + a$
is $e_{p(A_{i,a})} - e_{p(B_{i-1,a})}$ (each bond is wired as a maximally entangled pair); the
rows of the physical mode of site $i$ are $e_{q(C_i)}$ and $e_{p(C_i)}$. -/
theorem periodicWiring_rows (N M : ℕ) :
    (∀ (i : Fin N) (a : Fin M),
      periodicWiring N M (Sum.inl (Fin.castAdd (N * M) (finProdFinEquiv (i, a)))) =
          Pi.single (Sum.inl (finProdFinEquiv (i, Fin.castAdd 1 (Fin.castAdd M a)))) 1 +
            Pi.single (Sum.inl (finProdFinEquiv ((finRotate N).symm i,
              Fin.castAdd 1 (Fin.natAdd M a)))) 1 ∧
      periodicWiring N M (Sum.inl (Fin.natAdd (N * M) (finProdFinEquiv (i, a)))) =
          Pi.single (Sum.inr (finProdFinEquiv (i, Fin.castAdd 1 (Fin.castAdd M a)))) 1 -
            Pi.single (Sum.inr (finProdFinEquiv ((finRotate N).symm i,
              Fin.castAdd 1 (Fin.natAdd M a)))) 1) ∧
    ∀ i : Fin N,
      periodicWiring N M (Sum.inr (Sum.inl i)) =
          Pi.single (Sum.inl (finProdFinEquiv (i, Fin.natAdd (M + M) 0))) 1 ∧
      periodicWiring N M (Sum.inr (Sum.inr i)) =
          Pi.single (Sum.inr (finProdFinEquiv (i, Fin.natAdd (M + M) 0))) 1 := sorry

/-- Periodic chains: let $N \ge 3$ and $M \ge 1$, and let every $\Gamma_j$ be admissible on
$2M + 1$ modes. Then the wiring $K$ has linearly independent rows and satisfies
$K \Omega K^T = \begin{pmatrix} 0 & 0 \\ 0 & \Omega \end{pmatrix}$ (the symplectic matrix of the
$N$ physical modes in the lower right block), the eliminated block of $K \gamma K^T$ for the
input matrix $\gamma$ is positive definite, and the contracted covariance of the $N$ physical
modes is admissible. -/
theorem isAdmissible_periodic {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (Γ : Fin N → Matrix (Fin (M + M + 1) ⊕ Fin (M + M + 1)) (Fin (M + M + 1) ⊕ Fin (M + M + 1)) ℝ)
    (hΓ : ∀ j, IsAdmissible (Γ j)) :
    Function.Injective (periodicWiring N M)ᵀ.mulVec ∧
      periodicWiring N M * symplecticForm (N * (M + M + 1)) * (periodicWiring N M)ᵀ =
        Matrix.fromBlocks (0 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ) 0 0
          (symplecticForm N) ∧
      ((periodicWiring N M * periodicInput Γ * (periodicWiring N M)ᵀ).submatrix
        Sum.inl Sum.inl).PosDef ∧
      IsAdmissible (contractCovariance (periodicInput Γ) (periodicWiring N M)) := sorry

/-! ## The CCR algebra

$V$ is a real vector space and $\sigma$ a real bilinear form on $V$. The form $\sigma$ is
alternating when $\sigma(u, u) = 0$ for every $u$. It is nondegenerate when
$\sigma(u, \cdot) = 0$ only for $u = 0$ and $\sigma(\cdot, w) = 0$ only for $w = 0$; for
alternating $\sigma$ the two conditions coincide. The Hilbert space $\ell^2(V)$ consists of the
functions $f : V \to \mathbb C$ with $\sum_{v \in V} |f(v)|^2 < \infty$, that is, $\ell^2$ of $V$
with the discrete topology; bounded operators carry the operator norm and the adjoint as star.
The matrix $\Omega$ of the covariance sections is the matrix of $\sigma$ in the coordinates
$(q, p)$ of $V = \mathbb R^{2n}$, $\sigma(u, w) = u^T \Omega w$ with $\Omega$ as in entry 1; on one
mode this is the form $\sigma(u, w) = u_1 w_2 - u_2 w_1$ of entry 32. -/

/-- The Weyl operators and the CCR algebra: let $\sigma$ be any real bilinear form on $V$. For
$u \in V$ the Weyl operator $W(u)$ is the bounded operator on $\ell^2(V)$ with
$(W(u) f)(v) = e^{i\sigma(u, v)/2} f(v + u)$, and the CCR algebra $\mathrm{CCR}(V, \sigma)$ is the
norm closure of the star subalgebra generated by the Weyl operators. -/
theorem weyl_apply_and_CCR_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    (∀ (u : V) (f : lp (fun _ : V => ℂ) 2) (v : V),
      weyl σ u f v = Complex.exp (((σ u v / 2 : ℝ) : ℂ) * Complex.I) * f (v + u)) ∧
    CCR σ = (StarAlgebra.adjoin ℂ (Set.range (weyl σ))).topologicalClosure := sorry

/-- For alternating $\sigma$, every Weyl operator is unitary, $W(u)^* = W(-u)$, and the Weyl
relation $W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$ holds. -/
theorem weyl_relations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    (∀ u, weyl σ u ∈ unitary (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)) ∧
    (∀ u, star (weyl σ u) = weyl σ (-u)) ∧
    ∀ u w, weyl σ u * weyl σ w =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • weyl σ (u + w) := sorry

/-- Relabelling: let $\sigma$ and $\sigma'$ be any real bilinear forms on $V$ and $V'$. For a
linear bijection $T : V \to V'$ with $\sigma'(Tu, Tv) = \sigma(u, v)$ there is a $\mathbb C$-linear
star isomorphism $\varphi : \mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')$ with
$\varphi(W(u)) = W'(Tu)$ for every $u \in V$. -/
theorem exists_starAlgEquiv_relabel {V V' : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] {σ : LinearMap.BilinForm ℝ V}
    {σ' : LinearMap.BilinForm ℝ V'} (T : V ≃ₗ[ℝ] V') (hT : ∀ u v, σ' (T u) (T v) = σ u v) :
    ∃ φ : CCR σ ≃⋆ₐ[ℂ] CCR σ', ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (φ a : lp (fun _ : V' => ℂ) 2 →L[ℂ] lp (fun _ : V' => ℂ) 2) = weyl σ' (T u) := sorry

/-- Simplicity: for alternating nondegenerate $\sigma$, the CCR algebra is a simple ring: its
only two-sided ideals are $0$ and the whole algebra, and these differ. -/
theorem isSimpleRing_CCR {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.Nondegenerate) :
    IsSimpleRing (CCR σ) := sorry

/-- Automorphisms of Weyl type: let $\sigma$ be alternating and nondegenerate, $T$ a
$\mathbb C$-linear star automorphism of $\mathrm{CCR}(V, \sigma)$, $\Gamma : V \to V$ and
$c : V \to \mathbb C$ with $T(W(u)) = c(u) W(\Gamma u)$ for every $u$. Then $\Gamma$ is a
real-linear bijection preserving $\sigma$, and $c$ is a character of modulus one:
$c(u + w) = c(u) c(w)$ and $|c(u)| = 1$. -/
theorem weyl_automorphism {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.Nondegenerate)
    (T : CCR σ ≃⋆ₐ[ℂ] CCR σ) (Γ : V → V) (c : V → ℂ)
    (h : ∀ (u : V) (a : CCR σ), (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u →
        (T a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = c u • weyl σ (Γ u)) :
    (∃ L : V ≃ₗ[ℝ] V, ⇑L = Γ) ∧ (∀ u w, σ (Γ u) (Γ w) = σ u w) ∧
      (∀ u w, c (u + w) = c u * c w) ∧ ∀ u, ‖c u‖ = 1 := sorry

/-! ## States and Gaussian states

A state on $\mathrm{CCR}(V, \sigma)$ is a continuous complex-linear functional $\omega$ with
$\omega(1) = 1$ and $\omega(a^* a) \ge 0$ for every $a$ (a real non-negative number). Its
characteristic function is $u \mapsto \omega(W(u))$. -/

/-- Determination by the characteristic function: let $\sigma$ be alternating. Two continuous
complex-linear functionals on $\mathrm{CCR}(V, \sigma)$, in particular two states, that agree on
every Weyl operator are equal; so a state is determined by its characteristic function. -/
theorem eq_of_charFun {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : LinearMap.BilinForm ℝ V}
    (hσ : σ.IsAlt) (ω ω' : CCR σ →L[ℂ] ℂ)
    (h : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u → ω a = ω' a) :
    ω = ω' := sorry

/-- A necessary condition for Gaussian states: let $\sigma$ be alternating and $\omega$ a state
on $\mathrm{CCR}(V, \sigma)$ that is Gaussian with symmetric covariance form $\gamma$ and linear
displacement $d$, that is $\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4)$ for every $u$. Then
the data $(d, \gamma)$ satisfy all three of the following: (i) $\gamma + i\sigma \ge 0$, that is,
for every finite family $u_1, \dots, u_m$ of vectors the complex matrix
$(\gamma(u_j, u_k) + i \sigma(u_j, u_k))_{jk}$ is positive semidefinite; (ii) $\gamma(u, u) \ge 0$
for every $u$; (iii) $\sigma(u, w)^2 \le \gamma(u, u) \gamma(w, w)$ for all $u, w$. Conditions
(ii) and (iii) follow from (i) with $m = 1$ and $m = 2$. The condition is necessary: every
Gaussian state has data satisfying it. The existence of a Gaussian state for data satisfying the
condition is a candidate for a later theorem. -/
theorem gaussian_state_condition {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (ω : CCR σ →L[ℂ] ℂ) (h1 : ω 1 = 1)
    (hpos : ∀ a, 0 ≤ ω (star a * a)) (γ : LinearMap.BilinForm ℝ V) (hγ : γ.IsSymm)
    (d : V →ₗ[ℝ] ℝ)
    (hω : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        ω a = Complex.exp (Complex.I * (d u : ℂ) - (γ u u : ℂ) / 4)) :
    (∀ (m : ℕ) (u : Fin m → V),
      (Matrix.of fun j k => (γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)).PosSemidef) ∧
    (∀ u, 0 ≤ γ u u) ∧ ∀ u w, σ u w ^ 2 ≤ γ u u * γ w w := sorry

/-! ## Gaussian channels

A Gaussian channel on $\mathrm{CCR}(V, \sigma)$ has data $(L, \nu, \mu)$: a linear map
$L : V \to V$, a symmetric bilinear form $\nu$ and a linear form $\mu$, satisfying the channel
condition $\nu + i\sigma - i\sigma(L\cdot, L\cdot) \ge 0$ (every finite Gram matrix positive
semidefinite), together with a completely positive map $f$ of the CCR algebra with
$f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu)$. A complex-linear map $f$ of the CCR algebra is
completely positive when every matrix amplification
$(a_{jk}) \mapsto (f(a_{jk}))$ on $k \times k$ matrices with entries in the CCR algebra is
positive. The order on the CCR algebra is that of the bounded operators.
Complete positivity of the maps is a hypothesis. -/

/-- Composition: let $\sigma$ be any real bilinear form on $V$, and let
$(L_1, \nu_1, \mu_1, f_1)$ and $(L_2, \nu_2, \mu_2, f_2)$ be Gaussian channels. Then
$a \mapsto f_2(f_1(a))$ is completely positive and is the Gaussian channel with data
$L = L_2 L_1$, $\nu = \nu_1 + \nu_2(L_1\cdot, L_1\cdot)$ and $\mu = \mu_1 + \mu_2 \circ L_1$:
$\nu$ is symmetric, the data satisfy the channel condition, and
$f_2(f_1(W(u))) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu)$. -/
theorem gaussianChannel_comp {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (L₁ L₂ : V →ₗ[ℝ] V) (ν₁ ν₂ : LinearMap.BilinForm ℝ V)
    (hν₁ : ν₁.IsSymm) (hν₂ : ν₂.IsSymm) (μ₁ μ₂ : V →ₗ[ℝ] ℝ)
    (hc₁ : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => (ν₁ (u j) (u k) : ℂ) +
      Complex.I * ((σ (u j) (u k) - σ (L₁ (u j)) (L₁ (u k)) : ℝ) : ℂ)).PosSemidef)
    (hc₂ : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => (ν₂ (u j) (u k) : ℂ) +
      Complex.I * ((σ (u j) (u k) - σ (L₂ (u j)) (L₂ (u k)) : ℝ) : ℂ)).PosSemidef)
    (f₁ f₂ : CCR σ →CP CCR σ)
    (hf₁ : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f₁ a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          Complex.exp (Complex.I * (μ₁ u : ℂ) - (ν₁ u u : ℂ) / 4) • weyl σ (L₁ u))
    (hf₂ : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f₂ a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          Complex.exp (Complex.I * (μ₂ u : ℂ) - (ν₂ u u : ℂ) / 4) • weyl σ (L₂ u)) :
    (∃ f : CCR σ →CP CCR σ, ∀ a, f a = f₂ (f₁ a)) ∧
    (ν₁ + ν₂.comp L₁ L₁).IsSymm ∧
    (∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => ((ν₁ + ν₂.comp L₁ L₁) (u j) (u k) : ℂ) +
      Complex.I * ((σ (u j) (u k) - σ ((L₂ ∘ₗ L₁) (u j)) ((L₂ ∘ₗ L₁) (u k)) : ℝ) :
        ℂ)).PosSemidef) ∧
    ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f₂ (f₁ a) : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          Complex.exp (Complex.I * ((μ₁ + μ₂ ∘ₗ L₁) u : ℂ) - ((ν₁ + ν₂.comp L₁ L₁) u u : ℂ) / 4) •
            weyl σ ((L₂ ∘ₗ L₁) u) := sorry

/-- Channel matrices: for $n$ modes, let $X$ and $Y$ be real $2n \times 2n$ matrices with $Y$
symmetric and $Y - i\Omega + iX\Omega X^T \ge 0$. Then $X \gamma X^T + Y$ is admissible for every
admissible $\gamma$. -/
theorem isAdmissible_channel {n : ℕ} {X Y γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hY : Yᵀ = Y)
    (hXY : (Y.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal +
      Complex.I • (X * symplecticForm n * Xᵀ).map Complex.ofReal).PosSemidef)
    (hγ : IsAdmissible γ) : IsAdmissible (X * γ * Xᵀ + Y) := sorry

/-! ## The formal Fock space

The modes form a type $\iota$, an occupation-number configuration is a finitely supported
$n : \iota \to \mathbb N$ (finitely supported), with $|n| = \sum_i n_i$ and
$n! = \prod_i n_i!$, and $e_i$ is the configuration with one particle in mode $i$. The
coefficients lie in a complex vector space $R$, which for the Bargmann map and in entry 34 is a
ring and a complex algebra. A complex-linear map $T$ of the formal Fock space raises the
particle number if $\psi(n) = 0$ for all $|n| < k$ implies $(T\psi)(n) = 0$ for all
$|n| < k + 1$. Entry 25 characterizes these maps and defines their exponential. -/

/-- The formal Fock space is the space of all coefficient families: $\psi \mapsto (\psi(n))_n$
is a complex-linear bijection from the formal Fock space onto all functions from
occupation numbers to $R$, with no summability condition. The creation operator is
$(a_i^\dagger \psi)(n) = \sqrt{n_i}\, \psi(n - e_i)$ if $n_i > 0$ and $0$ otherwise, and the
annihilation operator is $(a_i \psi)(n) = \sqrt{n_i + 1}\, \psi(n + e_i)$. -/
theorem formalFock_and_ladder {ι R : Type*} [AddCommGroup R] [Module ℂ R] :
    (∃ e : FormalFock ι R ≃ₗ[ℂ] ((ι →₀ ℕ) → R), ∀ ψ, e ψ = ψ.coeff) ∧
    ∀ (i : ι) (ψ : FormalFock ι R) (n : ι →₀ ℕ),
      (create i ψ).coeff n = (if 0 < n i then
        ((Real.sqrt (n i : ℝ) : ℝ) : ℂ) • ψ.coeff (n - Finsupp.single i 1) else 0) ∧
      (annihilate i ψ).coeff n =
        ((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) • ψ.coeff (n + Finsupp.single i 1) := sorry

/-- The canonical commutation relations on the whole formal Fock space:
$[a_i, a_j^\dagger] = \delta_{ij}$, $[a_i, a_j] = 0$ and $[a_i^\dagger, a_j^\dagger] = 0$. -/
theorem ccr_ladder {ι R : Type*} [AddCommGroup R] [Module ℂ R] [DecidableEq ι] (i j : ι) :
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ =
        (if i = j then 1 else 0) ∧
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), annihilate (R := R) j⁆ = 0 ∧
    ⁅(create (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ = 0 := sorry

/-- Operators that raise the particle number, and their exponential: a linear map $T$ of the
formal Fock space raises the particle number if and only if, whenever
$\psi(n) = 0$ for all $|n| < k$, also $(T\psi)(n) = 0$ for all $|n| < k + 1$. For such an
operator $T$ the exponential is $(e^T \psi)(n) = \sum_{k=0}^{|n|} (T^k \psi)(n) / k!$, a finite
sum. -/
theorem numberRaisingOp_and_exp {ι R : Type*} [AddCommGroup R] [Module ℂ R] :
    (∀ T : Module.End ℂ (FormalFock ι R), (∃ S : NumberRaisingOp ι R, S.op = T) ↔
      ∀ (k : ℕ) (ψ : FormalFock ι R), (∀ n : ι →₀ ℕ, n.degree < k → ψ.coeff n = 0) →
        ∀ n : ι →₀ ℕ, n.degree < k + 1 → (T ψ).coeff n = 0) ∧
    ∀ (T : NumberRaisingOp ι R) (ψ : FormalFock ι R) (n : ι →₀ ℕ),
      (T.exp ψ).coeff n =
        ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n := sorry

/-- The exponential law: for operators $S$ and $T$ that raise the particle number and whose
underlying maps commute, the operator $S + T$ has as underlying map the sum of theirs, and
$e^{S+T} = e^S e^T$. -/
theorem numberRaisingOp_exp_add {ι R : Type*} [AddCommGroup R] [Module ℂ R]
    (S T : NumberRaisingOp ι R)
    (hST : Commute S.op T.op) :
    (S + T).op = S.op + T.op ∧ (S + T).exp = S.exp * T.exp := sorry

/-- The Bargmann map $\mathfrak B$ sends $\psi$ to the formal power series
$\sum_n \psi(n)\, z^n / \sqrt{n!}$; it is, by its type, a complex-linear bijection onto all formal
power series in variables $z_i$ ($i \in \iota$) with coefficients in $R$. -/
theorem coeff_toBargmann {ι R : Type*} [Ring R] [Algebra ℂ R] (ψ : FormalFock ι R)
    (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (toBargmann ψ) =
      ((Real.sqrt ((n.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • ψ.coeff n := sorry

/-- The Bargmann map turns $a_j^\dagger$ into multiplication by $z_j$ and $a_j$ into the partial
derivative $\partial_j = \partial / \partial z_j$ defined
on coefficients by $(\partial_j f)_n = (n_j + 1)\, f_{n + e_j}$. -/
theorem toBargmann_ladder {ι R : Type*} [Ring R] [Algebra ℂ R] (j : ι) (ψ : FormalFock ι R) :
    toBargmann (create j ψ) = MvPowerSeries.X j * toBargmann ψ ∧
      toBargmann (annihilate j ψ) = MvPowerSeries.pderivFun j (toBargmann ψ) := sorry

/-! ## Examples

These examples show that the hypotheses of the main theorems can be met and that the objects are
not degenerate. -/

/-- The vacuum $\gamma = 1$ is admissible on every number of modes; on one mode the squeezed
matrix $\mathrm{diag}(r, 1/r)$ is admissible for every $r > 0$, and
$\mathrm{diag}(1/2, 1/2)$ is not admissible. -/
theorem witness_admissible :
    (∀ n : ℕ, IsAdmissible (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) ∧
    (∀ r : ℝ, 0 < r →
      IsAdmissible (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => r) (fun _ : Fin 1 => r⁻¹)))) ∧
    ¬ IsAdmissible (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ : Fin 1 => (1 / 2 : ℝ)))) := sorry

/-- The attenuator: for $0 \le \eta \le 1$ the matrices $X = \sqrt\eta\, 1$ and
$Y = (1 - \eta)\, 1$ on $n$ modes satisfy the hypotheses of the channel-matrix statement:
$Y$ is symmetric and $Y - i\Omega + iX\Omega X^T \ge 0$. -/
theorem witness_attenuator (n : ℕ) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ((1 - η) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))ᵀ =
        (1 - η) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) ∧
    (((1 - η) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).map Complex.ofReal -
      Complex.I • (symplecticForm n).map Complex.ofReal +
      Complex.I • ((Real.sqrt η • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) *
        symplecticForm n * (Real.sqrt η • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))ᵀ).map
          Complex.ofReal).PosSemidef := sorry

/-- An explicit three-site chain: with $C = \begin{pmatrix} 0 & 0 & 1 \\ 0 & 0 & 1 \\ 1 & 1 & 0
\end{pmatrix}$ and $S = \begin{pmatrix} 1 & 0 \\ C & 1 \end{pmatrix}$, every site of the periodic
chain with $N = 3$ and $M = 1$ carries the local matrix $S S^T$, and the contracted covariance of
the three physical modes is $\Gamma_q \oplus \Gamma_p$, with the position block
$\Gamma_q = \frac15 \begin{pmatrix} 3 & 1 & 1 \\ 1 & 3 & 1 \\ 1 & 1 & 3 \end{pmatrix}$ and the
momentum block
$\Gamma_p = \begin{pmatrix} 2 & -1/2 & -1/2 \\ -1/2 & 2 & -1/2 \\ -1/2 & -1/2 & 2
\end{pmatrix}$; it is admissible. -/
theorem witness_three_site :
    contractCovariance
        (periodicInput (fun _ : Fin 3 =>
          Matrix.fromBlocks 1 0 !![(0 : ℝ), 0, 1; 0, 0, 1; 1, 1, 0] 1 *
            (Matrix.fromBlocks 1 0 !![(0 : ℝ), 0, 1; 0, 0, 1; 1, 1, 0] 1)ᵀ))
        (periodicWiring 3 1) =
      Matrix.fromBlocks (!![(3 : ℝ) / 5, 1 / 5, 1 / 5; 1 / 5, 3 / 5, 1 / 5; 1 / 5, 1 / 5, 3 / 5])
        0 0 (!![(2 : ℝ), -1 / 2, -1 / 2; -1 / 2, 2, -1 / 2; -1 / 2, -1 / 2, 2]) ∧
    IsAdmissible (contractCovariance
        (periodicInput (fun _ : Fin 3 =>
          Matrix.fromBlocks 1 0 !![(0 : ℝ), 0, 1; 0, 0, 1; 1, 1, 0] 1 *
            (Matrix.fromBlocks 1 0 !![(0 : ℝ), 0, 1; 0, 0, 1; 1, 1, 0] 1)ᵀ))
        (periodicWiring 3 1)) := sorry

/-- On $V = \mathbb R^2$ the form $\sigma(u, w) = u_1 w_2 - u_2 w_1$ is alternating and
nondegenerate, so the simplicity statement applies to it, and its CCR algebra is not the zero
algebra. -/
theorem witness_nondegenerate_plane :
    (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0]).IsAlt ∧
    (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0]).Nondegenerate ∧
    Nontrivial (CCR (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0])) := sorry

/-- The vacuum data satisfy the state condition: on $V = \mathbb R^2$ with
$\sigma(u, w) = u_1 w_2 - u_2 w_1$, the form $\gamma(u, w) = u_1 w_1 + u_2 w_2$ is symmetric and
$\gamma + i\sigma \ge 0$ on every finite family of vectors. -/
theorem witness_vacuum_state_condition :
    (Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm ∧
    ∀ (m : ℕ) (u : Fin m → Fin 2 → ℝ),
      (Matrix.of fun j k => (Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℝ) (u j) (u k) : ℂ) +
        Complex.I * (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0] (u j) (u k) : ℂ)).PosSemidef := sorry

/-- The creation operator $a_j^\dagger$ raises the particle number. -/
theorem witness_create_raisesParticleNumber {ι R : Type*} [Ring R] [Algebra ℂ R] (j : ι) :
    ∃ S : NumberRaisingOp ι R, S.op = create j := sorry

/-- The identity channel: let $\sigma$ be any real bilinear form on $V$. The data
$L = \mathrm{id}$, $\nu = 0$, $\mu = 0$ satisfy the hypotheses that entry 21 places on each
channel: $\nu$ is symmetric, the channel condition holds (every Gram matrix is $0$), and the
identity map $f(a) = a$ of $\mathrm{CCR}(V, \sigma)$ is completely positive with
$f(W(u)) = \exp(i\mu(u) - \nu(u, u)/4)\, W(Lu) = W(u)$. -/
theorem witness_identity_channel {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    (0 : LinearMap.BilinForm ℝ V).IsSymm ∧
    (∀ (m : ℕ) (u : Fin m → V),
      (Matrix.of fun j k => ((0 : LinearMap.BilinForm ℝ V) (u j) (u k) : ℂ) +
        Complex.I * ((σ (u j) (u k) - σ ((LinearMap.id : V →ₗ[ℝ] V) (u j))
          ((LinearMap.id : V →ₗ[ℝ] V) (u k)) : ℝ) : ℂ)).PosSemidef) ∧
    ∃ f : CCR σ →CP CCR σ, (∀ a, f a = a) ∧
      ∀ (u : V) (a : CCR σ),
        (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
          (f a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
            Complex.exp (Complex.I * ((0 : V →ₗ[ℝ] ℝ) u : ℂ) -
              ((0 : LinearMap.BilinForm ℝ V) u u : ℂ) / 4) •
                weyl σ ((LinearMap.id : V →ₗ[ℝ] V) u) := sorry

/-- The identity automorphism: let $\sigma$ be any real bilinear form on $V$. The identity
$\mathbb C$-linear star automorphism $T$ of $\mathrm{CCR}(V, \sigma)$, with $\Gamma = \mathrm{id}$
and $c = 1$, satisfies $T(W(u)) = c(u)\, W(\Gamma u)$ for every $u$. Together with
entry 32 it gives an instance of the hypotheses of entry 18. -/
theorem witness_identity_automorphism {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    ∀ (u : V) (a : CCR σ), (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u →
        (StarAlgEquiv.refl ℂ (CCR σ) a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          (1 : V → ℂ) u • weyl σ (id u) := sorry

/-! ## The Gaussian wave function: Schwartz domain, moments and units

A Schwartz function is a smooth function $\mathbb R \to \mathbb C$ whose derivatives of every
order decay faster than every power of $|x|$; it is square integrable, and its class in
$L^2(\mathbb R)$ carries the $L^2$ norm. The Schwartz functions form a common domain for the
position $x\psi$ and the momentum $-i\hbar\psi'$. Throughout this section
$\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}$ is the Gaussian of entry 8, of width
$s > 0$. -/

/-- Let $s > 0$ and $\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}$. Then $\psi$ is a
Schwartz function (exactly one Schwartz function equals $\psi$ at every point), and its class in
$L^2(\mathbb R)$ has norm $1$. -/
theorem gaussian_schwartz_unique {s : ℝ} (hs : 0 < s) (ψ : ℝ → ℂ)
    (hψ : ∀ x, ψ x = ((1 / Real.sqrt (Real.sqrt Real.pi * s) *
      Real.exp (-x ^ 2 / (2 * s ^ 2)) : ℝ) : ℂ)) :
    (∃! φ : SchwartzMap ℝ ℂ, ∀ x, φ x = ψ x) ∧
    ∀ φ : SchwartzMap ℝ ℂ, (∀ x, φ x = ψ x) →
      ‖SchwartzMap.toLpCLM ℂ ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) φ‖ = 1 := sorry

/-- Moments: let $s > 0$, $\hbar > 0$ and $\psi(x) = (\sqrt{\pi}\, s)^{-1/2} e^{-x^2/(2s^2)}$.
Then $x\psi$ and $-i\hbar\psi'$ are Schwartz functions, and
$-i\hbar\psi'(x) = (i\hbar/s^2)\, x\psi(x)$ for every $x$. The first moments vanish,
$\int \bar\psi\, x\psi\, dx = 0$ and $\int \bar\psi\, (-i\hbar\psi')\, dx = 0$, and the second
moments are $\int |x\psi|^2\, dx = s^2/2$, $\int |{-i\hbar\psi'}|^2\, dx = \hbar^2/(2s^2)$ and
$\int \overline{x\psi}\, (-i\hbar\psi')\, dx = i\hbar/2$. -/
theorem gaussian_moments {s ħ : ℝ} (hs : 0 < s) (hħ : 0 < ħ) (ψ : ℝ → ℂ)
    (hψ : ∀ x, ψ x = ((1 / Real.sqrt (Real.sqrt Real.pi * s) *
      Real.exp (-x ^ 2 / (2 * s ^ 2)) : ℝ) : ℂ)) :
    (∃ Q P : SchwartzMap ℝ ℂ, ∀ x, Q x = x * ψ x ∧ P x = -Complex.I * ħ * deriv ψ x) ∧
    (∀ x, -Complex.I * ħ * deriv ψ x = Complex.I * ħ / s ^ 2 * (x * ψ x)) ∧
    ∫ x, conj (ψ x) * (x * ψ x) = 0 ∧
    ∫ x, conj (ψ x) * (-Complex.I * ħ * deriv ψ x) = 0 ∧
    ∫ x, ‖x * ψ x‖ ^ 2 = s ^ 2 / 2 ∧
    ∫ x, ‖-Complex.I * ħ * deriv ψ x‖ ^ 2 = ħ ^ 2 / (2 * s ^ 2) ∧
    ∫ x, conj (x * ψ x) * (-Complex.I * ħ * deriv ψ x) = Complex.I * ħ / 2 := sorry

/-- Dimensionless units: for $s > 0$ and $\hbar > 0$ let $D = \mathrm{diag}(1/s, s/\hbar)$, the
rescaling $q \mapsto q/s$, $p \mapsto sp/\hbar$ of position and momentum. Then
$D\, \mathrm{diag}(s^2, \hbar^2/s^2)\, D^T = 1$: in these units the covariance of entry 8 is the
vacuum covariance $1$. -/
theorem gaussian_dimensionless {s ħ : ℝ} (hs : 0 < s) (hħ : 0 < ħ) :
    Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s⁻¹) (fun _ : Fin 1 => s / ħ)) *
        Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s ^ 2) (fun _ : Fin 1 => ħ ^ 2 / s ^ 2)) *
        (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s⁻¹) (fun _ : Fin 1 => s / ħ)))ᵀ =
      1 := sorry

/-- The width $s^2 = \hbar/(m\omega)$: let $m > 0$, $\omega > 0$, $\hbar > 0$ and
$s = \sqrt{\hbar/(m\omega)}$. Let $\psi$, $A_q\psi = x\psi$, $A_p\psi = -i\hbar\psi'$ and the
matrix $\gamma$ be as in entry 8 for this $s$. Then
$\gamma = \mathrm{diag}(\hbar/(m\omega), \hbar m\omega)$. -/
theorem gaussian_oscillator {m ω ħ : ℝ} (hm : 0 < m) (hω : 0 < ω) (hħ : 0 < ħ) (ψ : ℝ → ℂ)
    (hψ : ∀ x, ψ x = ((1 / Real.sqrt (Real.sqrt Real.pi * Real.sqrt (ħ / (m * ω))) *
      Real.exp (-x ^ 2 / (2 * Real.sqrt (ħ / (m * ω)) ^ 2)) : ℝ) : ℂ))
    (A : Fin 1 ⊕ Fin 1 → ℝ → ℂ)
    (hA : ∀ x, A (Sum.inl 0) x = x * ψ x ∧ A (Sum.inr 0) x = -Complex.I * ħ * deriv ψ x) :
    Matrix.of (fun j k => 2 * (∫ x,
        conj (A j x - ((∫ y, conj (ψ y) * A j y).re : ℂ) * ψ x) *
          (A k x - ((∫ y, conj (ψ y) * A k y).re : ℂ) * ψ x)).re) =
      Matrix.diagonal (Sum.elim (fun _ => ħ / (m * ω)) (fun _ => ħ * m * ω)) := sorry

/-! ## Fourier analysis, product covariances and Gaussian kernels

A periodic chain is homogeneous when every site carries the same local matrix $\Gamma$; its
contracted covariance $\gamma$ is that of entries 9 and 13 with input matrix of entry 11. The
sites are $x, y \in \{0, \dots, N - 1\}$, and $a_x$ for $a \in \{q, p\}$ denotes the position or
momentum coordinate of the physical mode of site $x$. For $k \in \{0, \dots, N - 1\}$ the
character of $\mathbb Z/N$ is $\chi_k(x) = e^{-2\pi i k x/N}$. A complex matrix $E$ is positive
definite when it is Hermitian with $\bar z^T E z > 0$ for every nonzero complex vector $z$, and
$H^*$ is the conjugate transpose of $H$. -/

/-- The symbols of a homogeneous chain: let $\Gamma$ be a real $2(2M+1) \times 2(2M+1)$ matrix,
regarded as complex, and $\Gamma_{VV}$, $\Gamma_{VC}$, $\Gamma_{CC}$ its blocks on the coordinates
of the virtual modes and of the physical mode: the virtual coordinates are listed as the positions
and then the momenta of the modes $A_a$ (local mode $a < M$), followed by the positions and then
the momenta of the modes $B_a$ (local mode $M + a$); the physical coordinates are those of local
mode $2M$. For $k$ let $\tau$ be the diagonal $2M \times 2M$ matrix with entries $1$ on positions
and $-1$ on momenta, and $S_k = (1 \mid e^{-2\pi i k/N}\tau)$ the $2M \times 4M$ matrix whose first
$2M$ columns, those of the coordinates of the modes $A_a$, form the identity matrix and whose last
$2M$ columns, those of the coordinates of the modes $B_a$, form $e^{-2\pi i k/N}\tau$. The
eliminated symbol is $E_k = S_k \Gamma_{VV} S_k^*$, and the covariance
symbol is the $2 \times 2$ complex matrix
$\Sigma_k = \Gamma_{CC} - (S_k\Gamma_{VC})^* E_k^{-1} (S_k\Gamma_{VC})$, where $E_k^{-1}$ is the
matrix inverse. -/
theorem covarianceSymbol_eq {N M : ℕ}
    (Γ : Matrix (Fin (M + M + 1) ⊕ Fin (M + M + 1)) (Fin (M + M + 1) ⊕ Fin (M + M + 1)) ℝ)
    (k : Fin N) :
    MPS.Fourier.eliminatedSymbol Γ k =
        (Matrix.of fun a => Sum.elim ((1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ) a)
            ((Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) / N) •
              Matrix.diagonal (Sum.elim (fun _ : Fin M => (1 : ℂ)) (fun _ => -1))) a)) *
          (Γ.map Complex.ofReal).submatrix
            (Sum.elim (Sum.map (fun a => Fin.castAdd 1 (Fin.castAdd M a))
                (fun a => Fin.castAdd 1 (Fin.castAdd M a)))
              (Sum.map (fun a => Fin.castAdd 1 (Fin.natAdd M a))
                (fun a => Fin.castAdd 1 (Fin.natAdd M a))))
            (Sum.elim (Sum.map (fun a => Fin.castAdd 1 (Fin.castAdd M a))
                (fun a => Fin.castAdd 1 (Fin.castAdd M a)))
              (Sum.map (fun a => Fin.castAdd 1 (Fin.natAdd M a))
                (fun a => Fin.castAdd 1 (Fin.natAdd M a)))) *
          (Matrix.of fun a => Sum.elim ((1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ) a)
            ((Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) / N) •
              Matrix.diagonal (Sum.elim (fun _ : Fin M => (1 : ℂ)) (fun _ => -1))) a))ᴴ ∧
    MPS.Fourier.covarianceSymbol Γ k =
      (Γ.map Complex.ofReal).submatrix
          (Sum.map (fun _ : Fin 1 => Fin.natAdd (M + M) 0) (fun _ : Fin 1 => Fin.natAdd (M + M) 0))
          (Sum.map (fun _ : Fin 1 => Fin.natAdd (M + M) 0)
            (fun _ : Fin 1 => Fin.natAdd (M + M) 0)) -
        ((Matrix.of fun a => Sum.elim ((1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ) a)
            ((Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) / N) •
              Matrix.diagonal (Sum.elim (fun _ : Fin M => (1 : ℂ)) (fun _ => -1))) a)) *
          (Γ.map Complex.ofReal).submatrix
            (Sum.elim (Sum.map (fun a => Fin.castAdd 1 (Fin.castAdd M a))
                (fun a => Fin.castAdd 1 (Fin.castAdd M a)))
              (Sum.map (fun a => Fin.castAdd 1 (Fin.natAdd M a))
                (fun a => Fin.castAdd 1 (Fin.natAdd M a))))
            (Sum.map (fun _ : Fin 1 => Fin.natAdd (M + M) 0)
              (fun _ : Fin 1 => Fin.natAdd (M + M) 0)))ᴴ *
        (MPS.Fourier.eliminatedSymbol Γ k)⁻¹ *
        ((Matrix.of fun a => Sum.elim ((1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ) a)
            ((Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) / N) •
              Matrix.diagonal (Sum.elim (fun _ : Fin M => (1 : ℂ)) (fun _ => -1))) a)) *
          (Γ.map Complex.ofReal).submatrix
            (Sum.elim (Sum.map (fun a => Fin.castAdd 1 (Fin.castAdd M a))
                (fun a => Fin.castAdd 1 (Fin.castAdd M a)))
              (Sum.map (fun a => Fin.castAdd 1 (Fin.natAdd M a))
                (fun a => Fin.castAdd 1 (Fin.natAdd M a))))
            (Sum.map (fun _ : Fin 1 => Fin.natAdd (M + M) 0)
              (fun _ : Fin 1 => Fin.natAdd (M + M) 0))) := sorry

/-- Fourier block diagonalization: let $N \ge 3$, $M \ge 1$, $\Gamma$ admissible on $2M + 1$
modes, and $\gamma$ the contracted covariance of the homogeneous periodic chain with local matrix
$\Gamma$ at every site. Then $\gamma$ is invariant under the rotation $x \mapsto x + 1 \bmod N$ of
the sites, $\gamma(a_{x+1}, b_{y+1}) = \gamma(a_x, b_y)$ for $a, b \in \{q, p\}$; every eliminated
symbol $E_k$ is positive definite; and the Fourier transform of $\gamma$ is block diagonal with the
covariance symbols as blocks:
$\frac1N \sum_{x, y} \chi_k(x)\, \gamma(a_x, b_y)\, \overline{\chi_l(y)} = \delta_{kl}\,
\Sigma_k(a, b)$ for all $k, l$ and $a, b \in \{q, p\}$. -/
theorem fourier_block_diagonal {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (Γ : Matrix (Fin (M + M + 1) ⊕ Fin (M + M + 1)) (Fin (M + M + 1) ⊕ Fin (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ) :
    (∀ (a b : Fin 1 ⊕ Fin 1) (i j : Fin N),
      contractCovariance (periodicInput fun _ : Fin N => Γ) (periodicWiring N M)
          (Sum.map (fun _ => finRotate N i) (fun _ => finRotate N i) a)
          (Sum.map (fun _ => finRotate N j) (fun _ => finRotate N j) b) =
        contractCovariance (periodicInput fun _ : Fin N => Γ) (periodicWiring N M)
          (Sum.map (fun _ => i) (fun _ => i) a) (Sum.map (fun _ => j) (fun _ => j) b)) ∧
    (∀ k : Fin N, (MPS.Fourier.eliminatedSymbol Γ k).PosDef) ∧
    ∀ (k l : Fin N) (a b : Fin 1 ⊕ Fin 1),
      (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
          Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) * (i : ℕ) / N) *
            (contractCovariance (periodicInput fun _ : Fin N => Γ) (periodicWiring N M)
              (Sum.map (fun _ => i) (fun _ => i) a) (Sum.map (fun _ => j) (fun _ => j) b) : ℂ) *
            conj (Complex.exp (-2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) =
        if k = l then MPS.Fourier.covarianceSymbol Γ k a b else 0 := sorry

/-- Fourier reconstruction: under the hypotheses of entry 42,
$\gamma(a_x, b_y) = \frac1N \sum_k \overline{\chi_k(x)}\, \Sigma_k(a, b)\, \chi_k(y)$ for all sites
$x, y$ and $a, b \in \{q, p\}$; every covariance symbol satisfies $\Sigma_k - i\Omega \ge 0$, with
$\Omega$ the symplectic matrix of one mode; and $\Sigma_l$ is the entrywise complex conjugate of
$\Sigma_k$ whenever $k + l \equiv 0 \pmod N$. -/
theorem fourier_reconstruction {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (Γ : Matrix (Fin (M + M + 1) ⊕ Fin (M + M + 1)) (Fin (M + M + 1) ⊕ Fin (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ) :
    (∀ (a b : Fin 1 ⊕ Fin 1) (i j : Fin N),
      (contractCovariance (periodicInput fun _ : Fin N => Γ) (periodicWiring N M)
          (Sum.map (fun _ => i) (fun _ => i) a) (Sum.map (fun _ => j) (fun _ => j) b) : ℂ) =
        (N : ℂ)⁻¹ * ∑ k : Fin N,
          conj (Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) * (i : ℕ) / N)) *
            MPS.Fourier.covarianceSymbol Γ k a b *
            Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) * (j : ℕ) / N)) ∧
    (∀ k : Fin N, (MPS.Fourier.covarianceSymbol Γ k -
      Complex.I • (symplecticForm 1).map Complex.ofReal).PosSemidef) ∧
    ∀ k l : Fin N, ((k : ℕ) + (l : ℕ)) % N = 0 →
      MPS.Fourier.covarianceSymbol Γ l = (MPS.Fourier.covarianceSymbol Γ k).map conj := sorry

/-- Product resources and product covariances: for a real $2 \times 2$ matrix $\theta$ on one
mode, the product resource on $2M + 1$ local modes is the independent sum, as in entry 5, of the
vacuum $1$ on the first $2M$ local modes (the virtual modes) and $\theta$ on the last local mode
(the physical mode). For real $2 \times 2$ matrices $\eta_x$, one for each site $x$ of $N$, the
product covariance on $N$ modes has the entry $\eta_x(a, b)$ between the coordinates $a_x$ and
$b_x$ of the same mode and $0$ between coordinates of different modes. -/
theorem productCovariance_eq {N M : ℕ} (θ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
    (η : Fin N → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) :
    productResource M θ =
      (Matrix.fromBlocks (1 : Matrix (Fin (M + M) ⊕ Fin (M + M)) (Fin (M + M) ⊕ Fin (M + M)) ℝ)
          0 0 θ).submatrix
        (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
          (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)))
        (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
          (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i))) ∧
    ∀ (i j : Fin N) (a b : Fin 1 ⊕ Fin 1),
      productCovariance η (Sum.map (fun _ => i) (fun _ => i) a)
          (Sum.map (fun _ => j) (fun _ => j) b) =
        if i = j then η i a b else 0 := sorry

/-- Product covariances as periodic contractions: let $N \ge 3$, $M \ge 1$ and let every
$\eta_x$ be admissible on one mode. Take as input of the periodic chain with $M$ virtual modes on
each side of every bond (entries 11 to 13) the product resources with physical matrices $\eta_x$.
Then every product resource is admissible; the matrix $K\gamma K^T$, for the wiring $K$ and the
input $\gamma$, is block diagonal with $2 \cdot 1$ on the $2NM$ eliminated rows and the product
covariance $\eta$ on the physical rows; the contracted covariance equals $\eta$; and $\eta$ is
admissible. -/
theorem isAdmissible_product {N M : ℕ} (hN : 3 ≤ N) (hM : 1 ≤ M)
    (η : Fin N → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) (hη : ∀ i, IsAdmissible (η i)) :
    (∀ i, IsAdmissible (productResource M (η i))) ∧
    periodicWiring N M * periodicInput (fun i => productResource M (η i)) *
        (periodicWiring N M)ᵀ =
      Matrix.fromBlocks (2 • (1 : Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ))
        0 0 (productCovariance η) ∧
    contractCovariance (periodicInput (fun i => productResource M (η i))) (periodicWiring N M) =
      productCovariance η ∧
    IsAdmissible (productCovariance η) := sorry

/-- The covariance of a Gaussian kernel: for a complex $n \times n$ matrix $K$ with real part
$X$ and imaginary part $-Y$, so that $K = X - iY$, the kernel covariance is the real
$2n \times 2n$ matrix $\begin{pmatrix} X^{-1} & X^{-1}Y \\ YX^{-1} & X + YX^{-1}Y \end{pmatrix}$
in the blocks of positions and momenta, with $X^{-1}$ the matrix inverse. -/
theorem kernelCovariance_eq {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) :
    kernelCovariance K =
      Matrix.fromBlocks (K.map Complex.re)⁻¹ ((K.map Complex.re)⁻¹ * -(K.map Complex.im))
        (-(K.map Complex.im) * (K.map Complex.re)⁻¹)
        (K.map Complex.re + -(K.map Complex.im) * (K.map Complex.re)⁻¹ *
          -(K.map Complex.im)) := sorry

/-- The local resource of a finitely squeezed cluster chain: for real $t$, $g$ and $g_i$ let
$r = t/(4(1 + g^2))$ and $\alpha = r + i$. The local resource is the kernel covariance (entry 46)
of the three-mode kernel $\begin{pmatrix} \alpha & 0 & i \\ 0 & \alpha & -2g_i\alpha \\ i &
-2g_i\alpha & t - 1/(2\alpha) + 2g_i^2\alpha \end{pmatrix}$ on the left virtual, the right virtual
and the physical mode. -/
theorem clusterLocalResource_eq (t g gi : ℝ) :
    clusterLocalResource t g gi =
      kernelCovariance !![((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I, 0, Complex.I;
        0, ((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I,
          -2 * (gi : ℂ) * (((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I);
        Complex.I, -2 * (gi : ℂ) * (((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I),
          (t : ℂ) - 1 / (2 * (((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I)) +
            2 * (gi : ℂ) ^ 2 * (((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I)] := sorry

/-- Gaussian kernels give admissible covariances: if the complex $n \times n$ matrix $K$ is
symmetric, $K^T = K$, and its real part $X$ is positive definite ($x^T X x > 0$ for every nonzero
real vector $x$, $X$ symmetric), then the kernel covariance of $K$ is admissible. -/
theorem isAdmissible_kernelCovariance {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (hK : Kᵀ = K)
    (hX : (K.map Complex.re).PosDef) : IsAdmissible (kernelCovariance K) := sorry

/-- Finitely squeezed cluster chains: for $t > 0$ and $g_i \in \{0, g\}$ the local resource of
entry 47 is admissible on three modes. -/
theorem isAdmissible_clusterLocalResource (t g gi : ℝ) (ht : 0 < t) (hgi : gi = 0 ∨ gi = g) :
    IsAdmissible (clusterLocalResource t g gi) := sorry

/-! ## Weyl systems, relabelling and representations

Let $\mathcal A$ be a unital C*-algebra. A Weyl system for $(V, \sigma)$ in $\mathcal A$ is a map
$W : V \to \mathcal A$ such that every $W(u)$ is unitary, the Weyl relation
$W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$ holds, and the $W(u)$ generate $\mathcal A$: the norm
closure of the star subalgebra generated by them is $\mathcal A$. A representation of a
C*-algebra $\mathcal A$ on a complex Hilbert space $H$ is a $\mathbb C$-linear unital star
homomorphism $\pi$ from $\mathcal A$ to the bounded operators on $H$. -/

/-- Let $\sigma$ be alternating and $W$ a Weyl system for $(V, \sigma)$ in a unital C*-algebra
$\mathcal A$. Then $W(0) = 1$, $W(u)^* = W(-u)$,
$W(u) W(w) = e^{-i\sigma(u, w)} W(w) W(u)$ for all $u, w$, and $W(u)$ and $W(w)$ commute
whenever $\sigma(u, w) = 0$. -/
theorem weylSystem_relations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) {A : Type*} [CStarAlgebra A] (W : V → A)
    (hu : ∀ u, W u ∈ unitary A)
    (hW : ∀ u w, W u * W w = Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (u + w))
    (hgen : (StarAlgebra.adjoin ℂ (Set.range W)).topologicalClosure = ⊤) :
    W 0 = 1 ∧ (∀ u, star (W u) = W (-u)) ∧
    (∀ u w, W u * W w = Complex.exp (((-(σ u w)) : ℝ) * Complex.I) • (W w * W u)) ∧
    ∀ u w, σ u w = 0 → Commute (W u) (W w) := sorry

/-- The CCR algebra is a Weyl system: for alternating $\sigma$ the Weyl operators $W(u)$, as
elements of $\mathrm{CCR}(V, \sigma)$, form a Weyl system for $(V, \sigma)$ in
$\mathrm{CCR}(V, \sigma)$. -/
theorem weylSystem_CCR {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    ∃ W : V → CCR σ, (∀ u, (W u : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
        weyl σ u) ∧
      (∀ u, W u ∈ unitary (CCR σ)) ∧
      (∀ u w, W u * W w = Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (u + w)) ∧
      (StarAlgebra.adjoin ℂ (Set.range W)).topologicalClosure = ⊤ := sorry

/-- Pullback of a Weyl system: let $\sigma$ and $\sigma_0$ be real bilinear forms on $V$ and
$V_0$, $W$ a Weyl system for $(V_0, \sigma_0)$ in a unital C*-algebra $\mathcal A$, and
$T : V \to V_0$ a linear map with $\sigma_0(Tu, Tw) = \sigma(u, w)$. Then every $W(Tu)$ is
unitary and $u \mapsto W(Tu)$ satisfies the Weyl relation of $\sigma$; if $T$ is surjective, the
$W(Tu)$ generate $\mathcal A$, so that $u \mapsto W(Tu)$ is a Weyl system for $(V, \sigma)$. -/
theorem weylSystem_pullback {V V₀ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V₀]
    [Module ℝ V₀] {σ : LinearMap.BilinForm ℝ V} {σ₀ : LinearMap.BilinForm ℝ V₀}
    {A : Type*} [CStarAlgebra A] (W : V₀ → A) (hu : ∀ u, W u ∈ unitary A)
    (hW : ∀ u w, W u * W w = Complex.exp (((-(σ₀ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (u + w))
    (hgen : (StarAlgebra.adjoin ℂ (Set.range W)).topologicalClosure = ⊤)
    (T : V →ₗ[ℝ] V₀) (hT : ∀ u w, σ₀ (T u) (T w) = σ u w) :
    (∀ u, W (T u) ∈ unitary A) ∧
    (∀ u w, W (T u) * W (T w) =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (T (u + w))) ∧
    (Function.Surjective T →
      (StarAlgebra.adjoin ℂ (Set.range fun u => W (T u))).topologicalClosure = ⊤) := sorry

/-- The relabelling maps: let $\sigma$ and $\sigma'$ be real bilinear forms on $V$ and $V'$, and
$T : V \to V'$ a linear bijection with $\sigma'(Tu, Tv) = \sigma(u, v)$. The relabelling unitary
$U_T$, a linear isometric bijection $\ell^2(V) \to \ell^2(V')$, is
$(U_T f)(v') = f(T^{-1}v')$, and the relabelling $\alpha_T$, a $\mathbb C$-linear star
isomorphism $\mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')$, is
$\alpha_T(a) = U_T\, a\, U_T^{-1}$. -/
theorem relabel_eq {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] {σ : LinearMap.BilinForm ℝ V} {σ' : LinearMap.BilinForm ℝ V'}
    (T : V ≃ₗ[ℝ] V') (hT : ∀ u v, σ' (T u) (T v) = σ u v) :
    (∀ (f : lp (fun _ : V => ℂ) 2) (v' : V'), BosonicLean.Weyl.relabel T f v' = f (T.symm v')) ∧
    ∀ a : CCR σ, (CCR.relabel hT a : lp (fun _ : V' => ℂ) 2 →L[ℂ] lp (fun _ : V' => ℂ) 2) =
      (BosonicLean.Weyl.relabel T).conjStarAlgEquiv a := sorry

/-- Relabelling is functorial: let $\sigma$, $\sigma'$, $\sigma''$ be real bilinear forms on $V$,
$V'$, $V''$, and $T_1 : V \to V'$, $T_2 : V' \to V''$ linear bijections with
$\sigma'(T_1u, T_1v) = \sigma(u, v)$ and $\sigma''(T_2u', T_2v') = \sigma'(u', v')$. Then
$\alpha_{T_1}(W(u)) = W'(T_1u)$ for every $u \in V$, the relabelling by the identity of $V$ is the
identity of $\mathrm{CCR}(V, \sigma)$, and $\alpha_{T_2 T_1} = \alpha_{T_2} \circ \alpha_{T_1}$. -/
theorem relabel_functorial {V V' V'' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] [AddCommGroup V''] [Module ℝ V''] {σ : LinearMap.BilinForm ℝ V}
    {σ' : LinearMap.BilinForm ℝ V'} {σ'' : LinearMap.BilinForm ℝ V''}
    (T₁ : V ≃ₗ[ℝ] V') (T₂ : V' ≃ₗ[ℝ] V'') (h₁ : ∀ u v, σ' (T₁ u) (T₁ v) = σ u v)
    (h₂ : ∀ u v, σ'' (T₂ u) (T₂ v) = σ' u v) :
    (∀ (u : V) (a : CCR σ), (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u →
        (CCR.relabel h₁ a : lp (fun _ : V' => ℂ) 2 →L[ℂ] lp (fun _ : V' => ℂ) 2) =
          weyl σ' (T₁ u)) ∧
    CCR.relabel (σ := σ) (σ' := σ) (T := LinearEquiv.refl ℝ V) (fun _ _ => rfl) =
      StarAlgEquiv.refl (R := ℂ) (A := CCR σ) ∧
    CCR.relabel (T := T₁.trans T₂) (fun u v => (h₂ (T₁ u) (T₁ v)).trans (h₁ u v)) =
      (CCR.relabel h₁).trans (CCR.relabel h₂) := sorry

/-- Injectivity of representations: let $\sigma$ be alternating and nondegenerate. Every
representation of $\mathrm{CCR}(V, \sigma)$ on a nonzero complex Hilbert space is injective. -/
theorem injective_representation {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.Nondegenerate) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (π : CCR σ →⋆ₐ[ℂ] (H →L[ℂ] H)) : Function.Injective π := sorry

/-! ## States and the state condition

States and characteristic functions are as in the section on states and Gaussian states. -/

/-- Twisted positivity: let $\sigma$ be alternating, $\omega$ a state on $\mathrm{CCR}(V, \sigma)$
and $\chi(u) = \omega(W(u))$ its characteristic function. For every finite family
$u_1, \dots, u_m$ of vectors the twisted kernel
$\big(e^{i\sigma(u_j, u_k)/2}\, \chi(u_k - u_j)\big)_{jk}$ is positive semidefinite. -/
theorem twistedKernel_posSemidef {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (ω : CCR σ →L[ℂ] ℂ) (h1 : ω 1 = 1)
    (hpos : ∀ a, 0 ≤ ω (star a * a)) (χ : V → ℂ)
    (hχ : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u → ω a = χ u)
    (m : ℕ) (u : Fin m → V) :
    (Matrix.of fun j k =>
      Complex.exp (Complex.I * (σ (u j) (u k) : ℂ) / 2) * χ (u k - u j)).PosSemidef := sorry

/-- The norm bound: let $\sigma$ be any real bilinear form on $V$ and $\omega$ a state on
$\mathrm{CCR}(V, \sigma)$. Then $|\omega(a)| \le \|a\|$ for every $a$. -/
theorem norm_state_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (ω : CCR σ →L[ℂ] ℂ) (h1 : ω 1 = 1)
    (hpos : ∀ a, 0 ≤ ω (star a * a)) (a : CCR σ) : ‖ω a‖ ≤ ‖a‖ := sorry

/-- The three forms of the state condition: let $\gamma$ be a symmetric and $\sigma$ an
alternating real bilinear form on $V$. The conditions (a) $\gamma + i\sigma \ge 0$, that is, the
complex matrix $(\gamma(u_j, u_k) + i\sigma(u_j, u_k))_{jk}$ is positive semidefinite for every
finite family $u_1, \dots, u_m$; (b) $2\sigma(a, b) \le \gamma(a, a) + \gamma(b, b)$ for all
$a, b$; and (c) $\gamma(u, u) \ge 0$ and $\sigma(u, w)^2 \le \gamma(u, u)\gamma(w, w)$ for all
$u, w$, are equivalent: (a) holds if and only if (b) holds, and (b) if and only if (c). -/
theorem state_condition_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    {γ σ : LinearMap.BilinForm ℝ V} (hγ : γ.IsSymm) (hσ : σ.IsAlt) :
    ((∀ (m : ℕ) (u : Fin m → V),
      (Matrix.of fun j k => (γ (u j) (u k) : ℂ) + Complex.I * (σ (u j) (u k) : ℂ)).PosSemidef) ↔
      ∀ a b, 2 * σ a b ≤ γ a a + γ b b) ∧
    ((∀ a b, 2 * σ a b ≤ γ a a + γ b b) ↔
      (∀ u, 0 ≤ γ u u) ∧ ∀ u w, σ u w ^ 2 ≤ γ u u * γ w w) := sorry

/-! ## Gaussian channels: product formula, special cases and dilations

Gaussian channels $(L, \nu, \mu, f)$ are as in the section on Gaussian channels; their
dissipation form is $C(u, w) = \nu(u, w) + i\sigma(u, w) - i\sigma(Lu, Lw)$. A C*-algebra with a
partial order is star-ordered when $a \le b$ holds exactly if
$b = a + p$ for a finite sum $p$ of elements of the form $s^* s$. -/

/-- The product formula: let $\sigma$ be alternating and $(L, \nu, \mu, f)$ a Gaussian channel
on $\mathrm{CCR}(V, \sigma)$. Then $f(W(u) W(w)) = e^{-C(u, w)/2}\, f(W(u))\, f(W(w))$ for all
$u, w \in V$. -/
theorem gaussianChannel_product {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (L : V →ₗ[ℝ] V)
    (ν : LinearMap.BilinForm ℝ V) (hν : ν.IsSymm) (μ : V →ₗ[ℝ] ℝ)
    (hc : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => (ν (u j) (u k) : ℂ) +
      Complex.I * ((σ (u j) (u k) - σ (L (u j)) (L (u k)) : ℝ) : ℂ)).PosSemidef)
    (f : CCR σ →CP CCR σ)
    (hf : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          Complex.exp (Complex.I * (μ u : ℂ) - (ν u u : ℂ) / 4) • weyl σ (L u)) :
    ∀ (u w : V) (a b : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
      (b : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ w →
        f (a * b) = Complex.exp (-((ν u w : ℂ) +
          Complex.I * ((σ u w : ℂ) - (σ (L u) (L w) : ℂ))) / 2) • (f a * f b) := sorry

/-- Channels and Gaussian states: let $\sigma$ be any real bilinear form on $V$,
$(L, \nu, \mu, f)$ a Gaussian channel on $\mathrm{CCR}(V, \sigma)$, and $\omega$ a given state that
is Gaussian with symmetric covariance form $\gamma$ and linear displacement $d$, that is
$\omega(W(u)) = \exp(i d(u) - \gamma(u, u)/4)$. Then $\omega'(a) = \omega(f(a))$ defines a
state $\omega'$, and $\omega'$ is Gaussian with the symmetric covariance form
$\gamma(L\cdot, L\cdot) + \nu$ and the displacement $d \circ L + \mu$:
$\omega'(W(u)) = \exp(i (d(Lu) + \mu(u)) - (\gamma(Lu, Lu) + \nu(u, u))/4)$. The statement
assumes the Gaussian state $\omega$; the library constructs no Gaussian state, and the existence
of Gaussian states is a candidate for a later theorem, as in entry 20. Apart from states obtained
from given ones, as here, the only state constructed is the vector state of entry 67, which is
not Gaussian for $V \ne 0$, since its characteristic function vanishes away from $0$. -/
theorem gaussianChannel_state {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (L : V →ₗ[ℝ] V)
    (ν : LinearMap.BilinForm ℝ V) (hν : ν.IsSymm) (μ : V →ₗ[ℝ] ℝ)
    (hc : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => (ν (u j) (u k) : ℂ) +
      Complex.I * ((σ (u j) (u k) - σ (L (u j)) (L (u k)) : ℝ) : ℂ)).PosSemidef)
    (f : CCR σ →CP CCR σ)
    (hf : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          Complex.exp (Complex.I * (μ u : ℂ) - (ν u u : ℂ) / 4) • weyl σ (L u))
    (ω : CCR σ →L[ℂ] ℂ) (h1 : ω 1 = 1) (hpos : ∀ a, 0 ≤ ω (star a * a))
    (γ : LinearMap.BilinForm ℝ V) (hγ : γ.IsSymm) (d : V →ₗ[ℝ] ℝ)
    (hω : ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        ω a = Complex.exp (Complex.I * (d u : ℂ) - (γ u u : ℂ) / 4)) :
    ∃ ω' : CCR σ →L[ℂ] ℂ, (∀ a, ω' a = ω (f a)) ∧ ω' 1 = 1 ∧
      (∀ a, 0 ≤ ω' (star a * a)) ∧ (γ.comp L L + ν).IsSymm ∧
      ∀ (u : V) (a : CCR σ),
        (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
          ω' a = Complex.exp (Complex.I * ((d ∘ₗ L + μ) u : ℂ) -
            ((γ.comp L L + ν) u u : ℂ) / 4) := sorry

/-- No noise: let $\sigma$ be alternating and $L : V \to V$ a linear map such that the data
$(L, 0)$ satisfy the channel condition, that is, the complex matrix
$(i\sigma(u_j, u_k) - i\sigma(Lu_j, Lu_k))_{jk}$ is positive semidefinite for every finite
family $u_1, \dots, u_m$. Then $L$ preserves $\sigma$: $\sigma(Lu, Lw) = \sigma(u, w)$. -/
theorem noiseless_preserves {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (L : V →ₗ[ℝ] V)
    (hc : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => ((0 : LinearMap.BilinForm ℝ V)
      (u j) (u k) : ℂ) + Complex.I * ((σ (u j) (u k) - σ (L (u j)) (L (u k)) : ℝ) :
        ℂ)).PosSemidef) :
    ∀ u w, σ (L u) (L w) = σ u w := sorry

/-- The noiseless channel as a relabelling: let $\sigma$ be alternating and $L : V \to V$ a
linear bijection with $\sigma(Lu, Lv) = \sigma(u, v)$. The relabelling $\alpha_L$ of entry 53 is
completely positive, and every completely positive map $f$ of $\mathrm{CCR}(V, \sigma)$ with
$f(W(u)) = W(Lu)$ for every $u$, that is, every Gaussian channel with data $(L, 0, 0)$, equals
$\alpha_L$. -/
theorem noiseless_channel_relabel {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (L : V ≃ₗ[ℝ] V)
    (hL : ∀ u v, σ (L u) (L v) = σ u v) :
    (∃ g : CCR σ →CP CCR σ, ∀ a, g a = CCR.relabel hL a) ∧
    ∀ f : CCR σ →CP CCR σ, (∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (f a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ (L u)) →
      ∀ a, f a = CCR.relabel hL a := sorry

/-- Dilations at the level of covariances: let $\sigma$ and $\sigma'$ be real bilinear forms on
$V$ (the system) and $V'$ (the ancilla), and $S : V \times V' \to V \times V'$ a linear map
preserving $\sigma \oplus \sigma'$:
$\sigma(S(x)_1, S(y)_1) + \sigma'(S(x)_2, S(y)_2) = \sigma(x_1, y_1) + \sigma'(x_2, y_2)$. Write
$Au = S(u, 0)_1$ and $Cu = S(u, 0)_2$, and let $\gamma$, $\gamma'$ be real bilinear forms on $V$,
$V'$. Then (i) $\sigma(Au, Aw) + \sigma'(Cu, Cw) = \sigma(u, w)$; (ii) if
$\gamma' + i\sigma' \ge 0$ on every finite family, the data $(A, \gamma'(C\cdot, C\cdot))$
satisfy the channel condition $\gamma'(C\cdot, C\cdot) + i\sigma - i\sigma(A\cdot, A\cdot) \ge 0$
on every finite family; (iii) the reduced covariance is
$(\gamma \oplus \gamma')(S(u, 0), S(w, 0)) = \gamma(Au, Aw) + \gamma'(Cu, Cw)$, as an identity of
bilinear forms. -/
theorem dilation_identities {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] {σ : LinearMap.BilinForm ℝ V} {σ' : LinearMap.BilinForm ℝ V'}
    (S : V × V' →ₗ[ℝ] V × V')
    (hS : ∀ x y, σ (S x).1 (S y).1 + σ' (S x).2 (S y).2 = σ x.1 y.1 + σ' x.2 y.2)
    (γ : LinearMap.BilinForm ℝ V) (γ' : LinearMap.BilinForm ℝ V') :
    (∀ u w, σ (S (u, 0)).1 (S (w, 0)).1 + σ' (S (u, 0)).2 (S (w, 0)).2 = σ u w) ∧
    ((∀ (m : ℕ) (v : Fin m → V'),
      (Matrix.of fun j k => (γ' (v j) (v k) : ℂ) + Complex.I * (σ' (v j) (v k) : ℂ)).PosSemidef) →
      ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k =>
        (γ' (S (u j, 0)).2 (S (u k, 0)).2 : ℂ) + Complex.I *
          ((σ (u j) (u k) - σ (S (u j, 0)).1 (S (u k, 0)).1 : ℝ) : ℂ)).PosSemidef) ∧
    (γ.comp (LinearMap.fst ℝ V V') (LinearMap.fst ℝ V V') +
        γ'.comp (LinearMap.snd ℝ V V') (LinearMap.snd ℝ V V')).comp
          (S ∘ₗ LinearMap.inl ℝ V V') (S ∘ₗ LinearMap.inl ℝ V V') =
      γ.comp (LinearMap.fst ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V')
          (LinearMap.fst ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V') +
        γ'.comp (LinearMap.snd ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V')
          (LinearMap.snd ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V') := sorry

/-- Closed star subalgebras are star-ordered: let $\mathcal A$ be a unital C*-algebra with a
partial order for which it is star-ordered, and $\mathcal S$ a norm-closed unital star subalgebra
of $\mathcal A$ with the order inherited from $\mathcal A$. Then an element $x$ of $\mathcal S$
satisfies $x \ge 0$ if and only if $x = s^* s$ for some $s \in \mathcal S$, and $\mathcal S$ is
star-ordered. -/
theorem starOrdered_of_isClosed {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A)) :
    (∀ x : S, (0 : A) ≤ x ↔ ∃ s : S, (x : A) = star (s : A) * s) ∧ StarOrderedRing S := sorry

/-- Completely positive maps compose: let $\mathcal A$, $\mathcal B$, $\mathcal C$ be unital
C*-algebras, each with a partial order for which it is star-ordered, and
$f : \mathcal A \to \mathcal B$ and $g : \mathcal B \to \mathcal C$ completely positive maps. Then
$a \mapsto g(f(a))$ is completely positive, and so is the identity of $\mathcal A$. -/
theorem cp_comp {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] (f : A →CP B) (g : B →CP C) :
    (∃ h : A →CP C, ∀ x, h x = g (f x)) ∧ ∃ i : A →CP A, ∀ x, i x = x := sorry

/-! ## Further examples

These examples show that the hypotheses of entries 55, 56 and 57 can be met. -/

/-- A representation: let $\sigma$ be any real bilinear form on $V$. The Hilbert space
$\ell^2(V)$ is nonzero, and the inclusion of $\mathrm{CCR}(V, \sigma)$ in the bounded operators on
$\ell^2(V)$ is a representation. With entry 32 it gives an instance of the hypotheses of
entry 55. -/
theorem witness_inclusion_representation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    Nontrivial (lp (fun _ : V => ℂ) 2) ∧
    ∃ π : CCR σ →⋆ₐ[ℂ] (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2), ∀ a, π a = a := sorry

/-- A state: let $\sigma$ be alternating. There is a state $\omega$ on $\mathrm{CCR}(V, \sigma)$
with characteristic function $\omega(W(u)) = 1$ for $u = 0$ and $\omega(W(u)) = 0$ for $u \ne 0$
(the vector state $a \mapsto \langle \delta_0, a\, \delta_0 \rangle$ of the basis vector at
$0$). -/
theorem witness_vector_state {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    ∃ ω : CCR σ →L[ℂ] ℂ, ω 1 = 1 ∧ (∀ a, 0 ≤ ω (star a * a)) ∧
      ∀ (u : V) (a : CCR σ),
        (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
          ω a = if u = 0 then 1 else 0 := sorry

open scoped InnerProductSpace

/-! ## The formal Fock space of one mode

For one mode the set of modes $\iota$ has one element, and $a$, $a^\dagger$ are the annihilation and
creation operators of entry 23 on the formal Fock space with complex coefficients. -/

/-- Anti-normal ordering and the number operator: the monomials $a^m (a^\dagger)^k$ with
$m, k \in \mathbb N$, in which every annihilation operator stands to the left of every creation
operator, span the algebra generated by $a$ and $a^\dagger$ as a complex vector space of linear
maps of the formal Fock space; and the number operator $\hat n = a^\dagger a$ satisfies
$\hat n^2 = a^2 (a^\dagger)^2 - 3\, a a^\dagger + 1$. -/
theorem antinormal_span_and_number_sq :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ
      {(annihilate () : Module.End ℂ (FormalFock Unit ℂ)), create ()}) =
      Submodule.span ℂ (Set.range fun p : ℕ × ℕ =>
        (annihilate () : Module.End ℂ (FormalFock Unit ℂ)) ^ p.1 * create () ^ p.2) ∧
    ((create () : Module.End ℂ (FormalFock Unit ℂ)) * annihilate ()) ^ 2 =
      annihilate () ^ 2 * create () ^ 2 - 3 • (annihilate () * create ()) + 1 := sorry

/-! ## The bosonic Fock space

The bosonic Fock space $\Gamma_s(\iota)$ of the modes $\iota$ is the Hilbert space $\ell^2$ of the
occupation-number configurations $n$, with the inner product
$\langle\varphi, \psi\rangle = \sum_n \overline{\varphi(n)}\, \psi(n)$; the number state
$|m\rangle$ is the basis vector at $m$, and the vacuum $|0\rangle$ is the basis vector at the
configuration $0$. The embedding $\jmath$ sends $\psi \in \Gamma_s(\iota)$ to the formal vector with
the same coefficients. A linear map $T$ of the formal Fock space $\mathcal F(\iota, \mathbb C)$ is
coefficient-finite when for every $n$ there is a finite set $s$ of configurations such that
$(T\varphi)(n) = (T\varphi')(n)$ whenever $\varphi(m) = \varphi'(m)$ for all $m \in s$. -/

/-- The Fock space and the embedding: (definition) $\Gamma_s(\iota)$ is $\ell^2$ of the
configurations, and the embedding keeps the coefficients, $(\jmath\psi)(n) = \psi(n)$. The
embedding is injective, and a formal vector $\varphi$ lies in its image if and only if
$\sum_n |\varphi(n)|^2 < \infty$. (Definition) The squared norm of a formal vector is
$\|\varphi\|^2 = \sum_n |\varphi(n)|^2 \in [0, \infty]$. Moreover $\|\jmath\psi\|^2$ is the
squared Hilbert norm of $\psi$, and the number states span a dense subspace of
$\Gamma_s(\iota)$. -/
theorem fockSpace_eq (ι : Type*) [DecidableEq ι] :
    FockSpace ι = lp (fun _ : ι →₀ ℕ => ℂ) 2 ∧
    (∀ (ψ : FockSpace ι) (n : ι →₀ ℕ), (FockSpace.toFormal ψ).coeff n = ψ n) ∧
    Function.Injective (FockSpace.toFormal (ι := ι)) ∧
    (∀ φ : FormalFock ι ℂ, (∃ ψ : FockSpace ι, FockSpace.toFormal ψ = φ) ↔
      Summable fun n => ‖φ.coeff n‖ ^ 2) ∧
    (∀ φ : FormalFock ι ℂ, FormalFock.sqNorm φ = ∑' n, (‖φ.coeff n‖₊ : ENNReal) ^ 2) ∧
    (∀ ψ : FockSpace ι,
      FormalFock.sqNorm (FockSpace.toFormal ψ) = ENNReal.ofReal (‖ψ‖ ^ 2)) ∧
    Dense (Submodule.span ℂ (Set.range fun m : ι →₀ ℕ => lp.single 2 m (1 : ℂ)) :
      Set (FockSpace ι)) := sorry

/-- Maximal realizations: (definition) for a linear map $T$ of $\mathcal F(\iota, \mathbb C)$,
the maximal realization $\bar T$ is the operator of $\Gamma_s(\iota)$ with the domain of the $\psi$
for which $T\jmath\psi$ is square-summable, and with $\jmath \bar T\psi = T\jmath\psi$. If $T$ is
coefficient-finite, then $\bar T$ is closed: its graph is closed in
$\Gamma_s(\iota) \times \Gamma_s(\iota)$. -/
theorem maxRealization_isClosed {ι : Type*} (T : Module.End ℂ (FormalFock ι ℂ)) :
    (∀ ψ : FockSpace ι,
      ψ ∈ FockSpace.maxDomain T ↔ Memℓp (T (FockSpace.toFormal ψ)).coeff 2) ∧
    (FockSpace.maxRealization T).domain = FockSpace.maxDomain T ∧
    (∀ ψ : (FockSpace.maxRealization T).domain,
      FockSpace.toFormal (FockSpace.maxRealization T ψ) = T (FockSpace.toFormal ψ)) ∧
    ((∀ n, ∃ s : Finset (ι →₀ ℕ), ∀ φ φ' : FormalFock ι ℂ,
      (∀ m ∈ s, φ.coeff m = φ'.coeff m) → (T φ).coeff n = (T φ').coeff n) →
      (FockSpace.maxRealization T).IsClosed) := sorry

/-- Closed forms: let $T_k$, $k$ in a finite index set, be coefficient-finite linear maps of
$\mathcal F(\iota, \mathbb C)$, and let $\psi_r \to \psi$ in $\Gamma_s(\iota)$ with every
$T_k\jmath\psi_r$ square-summable and $\sum_k \|T_k\jmath(\psi_r - \psi_s)\|^2 \to 0$ as
$r, s \to \infty$. Then every $T_k\jmath\psi$ is square-summable and
$\sum_k \|T_k\jmath(\psi_r - \psi)\|^2 \to 0$: the form with the diagonal
$\sum_k \|\bar T_k\psi\|^2$ on the intersection of the domains of the $\bar T_k$ is closed. -/
theorem form_closed {ι κ : Type*} [Fintype κ] (T : κ → Module.End ℂ (FormalFock ι ℂ))
    (hT : ∀ k n, ∃ s : Finset (ι →₀ ℕ), ∀ φ φ' : FormalFock ι ℂ,
      (∀ m ∈ s, φ.coeff m = φ'.coeff m) → (T k φ).coeff n = (T k φ').coeff n)
    (ψs : ℕ → FockSpace ι) (ψ : FockSpace ι)
    (hdom : ∀ r k, Memℓp (T k (FockSpace.toFormal (ψs r))).coeff 2)
    (hlim : Filter.Tendsto ψs Filter.atTop (nhds ψ))
    (hcauchy : Filter.Tendsto (fun p : ℕ × ℕ =>
      ∑ k, FormalFock.sqNorm (T k (FockSpace.toFormal (ψs p.1 - ψs p.2))))
        Filter.atTop (nhds 0)) :
    (∀ k, Memℓp (T k (FockSpace.toFormal ψ)).coeff 2) ∧
    Filter.Tendsto (fun r => ∑ k, FormalFock.sqNorm (T k (FockSpace.toFormal (ψs r - ψ))))
      Filter.atTop (nhds 0) := sorry

/-! ## Second quantization

The set of modes $\iota$ is finite, and matrices are indexed by the modes. A complex matrix
$\mathcal U$ is unitary when $\mathcal U^* \mathcal U = \mathcal U \mathcal U^* = 1$, and the
exponential of a matrix is $e^h = \sum_{k \ge 0} h^k / k!$. -/

/-- Second quantization (definition): for a complex matrix $g$, $\Gamma(g)$ is the linear map of
$\mathcal F(\iota, \mathbb C)$ that becomes, under the Bargmann map of entry 27, the substitution of
the linear forms $(g^T z)_j = \sum_k g_{kj} z_k$ for the variables:
$\mathfrak B\, \Gamma(g)\psi = (\mathfrak B\psi)(g^T z)$. Since $\mathfrak B$ is a bijection, this
determines $\Gamma(g)$. -/
theorem secondQuant_eq {ι : Type*} [Fintype ι] (g : Matrix ι ι ℂ) (ψ : FormalFock ι ℂ) :
    toBargmann (secondQuant g ψ) =
      MvPowerSeries.subst (fun j => ∑ k, g k j • (MvPowerSeries.X k : MvPowerSeries ι ℂ))
        (toBargmann ψ) := sorry

/-- Representation and intertwining: $\Gamma(1) = 1$ and $\Gamma(g g') = \Gamma(g)\Gamma(g')$ for
all complex matrices $g$, $g'$, and on the whole formal Fock space
$\Gamma(g)\, a_j^\dagger = \big(\sum_k g_{kj} a_k^\dagger\big)\Gamma(g)$ and
$a_j\, \Gamma(g) = \Gamma(g) \sum_k g_{jk} a_k$. -/
theorem secondQuant_representation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g g' : Matrix ι ι ℂ) (j : ι) :
    secondQuant (1 : Matrix ι ι ℂ) = 1 ∧ secondQuant (g * g') = secondQuant g * secondQuant g' ∧
    secondQuant g * create j = (∑ k, g k j • create k) * secondQuant g ∧
    annihilate j * secondQuant g = secondQuant g * ∑ k, g j k • annihilate k := sorry

/-- Unitarity and strong continuity: for a unitary matrix $\mathcal U$,
$\|\Gamma(\mathcal U)\varphi\|^2 = \|\varphi\|^2$ in $[0, \infty]$ for every formal vector
$\varphi$, and on the whole formal Fock space
$\Gamma(\mathcal U^*)\, a_j\, \Gamma(\mathcal U) = \sum_k \mathcal U_{jk} a_k$. (Definition) The
unitary operator $\mathsf U_{\mathcal U}$ of $\Gamma_s(\iota)$ is the restriction of
$\Gamma(\mathcal U)$: $\jmath\, \mathsf U_{\mathcal U}\psi = \Gamma(\mathcal U)\jmath\psi$. The map
$\mathcal U \mapsto \mathsf U_{\mathcal U}$ is a group homomorphism from the unitary matrices to the
unitary operators of $\Gamma_s(\iota)$, with
$\mathsf U_{\mathcal U}^* = \mathsf U_{\mathcal U^*}$, and $\mathcal U \mapsto \mathsf
U_{\mathcal U}\psi$ is continuous for every $\psi \in \Gamma_s(\iota)$. -/
theorem secondQuant_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ (U : Matrix.unitaryGroup ι ℂ) (φ : FormalFock ι ℂ),
      FormalFock.sqNorm (secondQuant (U : Matrix ι ι ℂ) φ) = FormalFock.sqNorm φ) ∧
    (∀ (U : Matrix.unitaryGroup ι ℂ) (j : ι),
      secondQuant (U : Matrix ι ι ℂ)ᴴ * annihilate j * secondQuant (U : Matrix ι ι ℂ) =
        ∑ k, (U : Matrix ι ι ℂ) j k • annihilate k) ∧
    (∀ (U : Matrix.unitaryGroup ι ℂ) (ψ : FockSpace ι),
      FockSpace.toFormal ((FockSpace.secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ) =
        secondQuant (U : Matrix ι ι ℂ) (FockSpace.toFormal ψ)) ∧
    (∀ U V : Matrix.unitaryGroup ι ℂ,
      FockSpace.secondQuantRep (U * V) = FockSpace.secondQuantRep U * FockSpace.secondQuantRep V) ∧
    (∀ U : Matrix.unitaryGroup ι ℂ,
      star (FockSpace.secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) =
        FockSpace.secondQuantRep (star U)) ∧
    ∀ ψ : FockSpace ι, Continuous fun U : Matrix.unitaryGroup ι ℂ =>
      (FockSpace.secondQuantRep U : FockSpace ι →L[ℂ] FockSpace ι) ψ := sorry

/-- The exponential form: (definition) for a complex matrix $h$ let
$\mathrm d\Gamma(h) = \sum_{j, k} h_{jk}\, a_j^\dagger a_k$. For every formal vector $\psi$ and
every $n$ the series $\sum_{r \ge 0} (\mathrm d\Gamma(h)^r\psi)(n)/r!$ converges, with sum
$(\Gamma(e^h)\psi)(n)$: $\Gamma(e^h) = e^{\mathrm d\Gamma(h)}$, the exponential taken
coefficientwise. -/
theorem secondQuant_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) :
    dSecondQuant h = ∑ j, ∑ k, h j k • (create j * annihilate k) ∧
    ∀ (ψ : FormalFock ι ℂ) (n : ι →₀ ℕ),
      HasSum (fun r : ℕ => ((r.factorial : ℂ)⁻¹) * ((dSecondQuant h ^ r) ψ).coeff n)
        ((secondQuant (NormedSpace.exp h) ψ).coeff n) := sorry

/-- Unitary matrices are exponentials: every unitary matrix is $e^{iM}$ for a Hermitian matrix
$M$, and $e^{iM}$ is unitary for every Hermitian $M$. So entry 75 applies to every
$\Gamma(\mathcal U)$, with $h = iM$. -/
theorem unitary_eq_exp {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ U : Matrix.unitaryGroup ι ℂ, ∃ M : Matrix ι ι ℂ, M.IsHermitian ∧
      NormedSpace.exp (Complex.I • M) = (U : Matrix ι ι ℂ)) ∧
    ∀ M : Matrix ι ι ℂ, M.IsHermitian →
      NormedSpace.exp (Complex.I • M) ∈ Matrix.unitaryGroup ι ℂ := sorry

/-! ## Symplectic matrices: the Bloch–Messiah decomposition

A real $2n \times 2n$ matrix $S$, indexed by positions and momenta as in the first section, is
symplectic when $S \Omega S^T = \Omega$, and orthogonal when $S^T S = 1$. A real matrix $P$ is
symmetric positive definite when $P^T = P$ and $x^T P x > 0$ for every nonzero real vector $x$. A
vector $r \in \mathbb R^n$ satisfies $r \ge 0$ when $r_k \ge 0$ for every $k$. -/

/-- The squeezing matrix and the orthogonal symplectic matrix of a unitary (definitions): for
$r \in \mathbb R^n$, $\Sigma(r) = \mathrm{diag}(e^{-r_1}, \dots, e^{-r_n}, e^{r_1}, \dots,
e^{r_n})$; for a unitary $n \times n$ matrix $\mathcal U = X + iY$ with $X$, $Y$ real,
$O_{\mathcal U} = \begin{pmatrix} X & -Y \\ Y & X \end{pmatrix}$. Both are symplectic, and
$O_{\mathcal U}$ is orthogonal. -/
theorem squeezingMatrix_eq {n : ℕ} (r : Fin n → ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    squeezingMatrix r =
      Matrix.diagonal (Sum.elim (fun k => Real.exp (-r k)) fun k => Real.exp (r k)) ∧
    orthogonalSymplecticOfUnitary U =
      Matrix.fromBlocks ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re)
        (-(U : Matrix (Fin n) (Fin n) ℂ).map Complex.im)
        ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.im)
        ((U : Matrix (Fin n) (Fin n) ℂ).map Complex.re) ∧
    squeezingMatrix r * symplecticForm n * (squeezingMatrix r)ᵀ = symplecticForm n ∧
    orthogonalSymplecticOfUnitary U ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
    orthogonalSymplecticOfUnitary U * symplecticForm n * (orthogonalSymplecticOfUnitary U)ᵀ =
      symplecticForm n := sorry

/-- Orthogonal symplectic matrices and unitaries: a real $2n \times 2n$ matrix $O$ is orthogonal
and symplectic if and only if $O = O_{\mathcal U}$ for a unitary $\mathcal U$; and
$O_{\mathcal U \mathcal V} = O_{\mathcal U} O_{\mathcal V}$, $O_1 = 1$,
$O_{\mathcal U^*} = O_{\mathcal U}^T$. -/
theorem orthogonalSymplectic_iff {n : ℕ} (O : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (O ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧ O * symplecticForm n * Oᵀ = symplecticForm n ↔
      ∃ U : Matrix.unitaryGroup (Fin n) ℂ, O = orthogonalSymplecticOfUnitary U) ∧
    (∀ U V : Matrix.unitaryGroup (Fin n) ℂ, orthogonalSymplecticOfUnitary (U * V) =
      orthogonalSymplecticOfUnitary U * orthogonalSymplecticOfUnitary V) ∧
    orthogonalSymplecticOfUnitary (1 : Matrix.unitaryGroup (Fin n) ℂ) = 1 ∧
    ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      orthogonalSymplecticOfUnitary (star U) = (orthogonalSymplecticOfUnitary U)ᵀ := sorry

/-- The Bloch–Messiah decomposition: for every symmetric positive definite symplectic matrix $M$
there are a unitary $\mathcal U$ and $r \ge 0$ with
$M = O_{\mathcal U} \Sigma(r)^2 O_{\mathcal U}^T$; for every symplectic matrix $S$ there are
unitaries $\mathcal U$, $\mathcal V$ and $r \ge 0$ with
$S = O_{\mathcal U} \Sigma(r) O_{\mathcal V}$. -/
theorem blochMessiah {n : ℕ} :
    (∀ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, M.PosDef →
      M * symplecticForm n * Mᵀ = symplecticForm n →
      ∃ (U : Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℝ), 0 ≤ r ∧
        M = orthogonalSymplecticOfUnitary U * squeezingMatrix r ^ 2 *
          (orthogonalSymplecticOfUnitary U)ᵀ) ∧
    ∀ S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      S * symplecticForm n * Sᵀ = symplecticForm n →
      ∃ (U V : Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℝ), 0 ≤ r ∧
        S = orthogonalSymplecticOfUnitary U * squeezingMatrix r *
          orthogonalSymplecticOfUnitary V := sorry

/-- The squeezing parameters are unique up to order: if
$O_1 \Sigma(r) O_2 = O_3 \Sigma(r') O_4$ with orthogonal $O_1, \dots, O_4$ and $r, r' \ge 0$, then
$r' = r \circ \pi$ for a permutation $\pi$ of $\{1, \dots, n\}$. -/
theorem blochMessiah_squeezing_unique {n : ℕ}
    {O₁ O₂ O₃ O₄ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {r r' : Fin n → ℝ}
    (h₁ : O₁ ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ)
    (h₂ : O₂ ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ)
    (h₃ : O₃ ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ)
    (h₄ : O₄ ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : O₁ * squeezingMatrix r * O₂ = O₃ * squeezingMatrix r' * O₄) :
    ∃ π : Equiv.Perm (Fin n), r' = r ∘ π := sorry

open scoped MatrixOrder in
/-- The polar decomposition: for symplectic $S$, the positive semidefinite square root
$P = (S S^T)^{1/2}$ is symmetric positive definite and symplectic, $P^{-1} S$ is orthogonal and
symplectic, and $S = P\, (P^{-1} S)$. For every real $2n \times 2n$ matrix $S$, if $S = P' O'$
with $P'$ symmetric positive definite and $O'$ orthogonal, then $P' = (S S^T)^{1/2}$ and
$O' = P'^{-1} S$. -/
theorem polar_decomposition_symplectic {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (S * symplecticForm n * Sᵀ = symplecticForm n →
      (CFC.sqrt (S * Sᵀ)).PosDef ∧
      CFC.sqrt (S * Sᵀ) * symplecticForm n * (CFC.sqrt (S * Sᵀ))ᵀ = symplecticForm n ∧
      (CFC.sqrt (S * Sᵀ))⁻¹ * S ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
      (CFC.sqrt (S * Sᵀ))⁻¹ * S * symplecticForm n * ((CFC.sqrt (S * Sᵀ))⁻¹ * S)ᵀ =
        symplecticForm n ∧
      S = CFC.sqrt (S * Sᵀ) * ((CFC.sqrt (S * Sᵀ))⁻¹ * S)) ∧
    ∀ P O : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, P.PosDef →
      O ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ → S = P * O →
        P = CFC.sqrt (S * Sᵀ) ∧ O = (CFC.sqrt (S * Sᵀ))⁻¹ * S := sorry

/-! ## Exponential vectors, displacement and squeezing

The set of modes $\iota$ is finite. For $w, z \in \mathbb C^\iota$, $\langle w, z\rangle$ denotes
$\sum_j \bar w_j z_j$ and $|z|^2$ denotes $\sum_j |z_j|^2$; for a configuration $m$, $z^m$ denotes
$\prod_j z_j^{m_j}$ and $m!$ denotes $\prod_j m_j!$. Operators are bounded operators of
$\Gamma_s(\iota)$, with the adjoint as star; $|0\rangle$ is the vacuum. -/

/-- Exponential vectors: (definition) for $z \in \mathbb C^\iota$ the exponential vector
$\varepsilon(z) \in \Gamma_s(\iota)$ has the coefficients $\varepsilon(z)(m) = z^m/\sqrt{m!}$; and
$\langle \varepsilon(w), \varepsilon(z)\rangle = e^{\langle w, z\rangle}$. -/
theorem expVec_apply {ι : Type*} [Fintype ι] (w z : ι → ℂ) (n : ι →₀ ℕ) :
    FockSpace.expVec z n =
      (∏ j, z j ^ n j) / ((Real.sqrt ((n.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) ∧
    ⟪FockSpace.expVec w, FockSpace.expVec z⟫_ℂ = Complex.exp (∑ j, conj (w j) * z j) := sorry

/-- Totality: the exponential vectors span a dense subspace of $\Gamma_s(\iota)$. Hence a vector
$\psi$ is determined by the inner products $\langle \varepsilon(w), \psi\rangle$,
$w \in \mathbb C^\iota$, and a continuous linear map from $\Gamma_s(\iota)$ to a Hausdorff
topological vector space is determined by its values on the exponential vectors. -/
theorem totality {ι : Type*} [Fintype ι] :
    Dense (Submodule.span ℂ (Set.range (FockSpace.expVec (ι := ι))) : Set (FockSpace ι)) ∧
    (∀ ψ ψ' : FockSpace ι,
      (∀ w, ⟪FockSpace.expVec w, ψ⟫_ℂ = ⟪FockSpace.expVec w, ψ'⟫_ℂ) → ψ = ψ') ∧
    ∀ {E : Type*} [TopologicalSpace E] [T2Space E] [AddCommGroup E] [Module ℂ E]
      (f g : FockSpace ι →L[ℂ] E), (∀ z, f (FockSpace.expVec z) = g (FockSpace.expVec z)) →
        f = g := sorry

/-- Displacement operators: for $\alpha \in \mathbb C^\iota$, $D(\alpha)$ is a unitary operator of
$\Gamma_s(\iota)$ with $D(\alpha)\varepsilon(z) = e^{-|\alpha|^2/2 - \langle\alpha, z\rangle}
\varepsilon(z + \alpha)$ for every $z$, which determines it by entry 83; this is the normal-ordered
form of $\exp\big(\sum_j (\alpha_j a_j^\dagger - \bar\alpha_j a_j)\big)$ (an identification that is
not part of the statement). Moreover
$D(\alpha)^* = D(-\alpha)$, $D(0) = 1$, and $D(\alpha)|0\rangle = e^{-|\alpha|^2/2}
\varepsilon(\alpha)$, the coherent state. -/
theorem displacement_expVec {ι : Type*} [Fintype ι] [DecidableEq ι] (α z : ι → ℂ) :
    (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) (FockSpace.expVec z) =
      Complex.exp (-((∑ j, ‖α j‖ ^ 2 : ℝ) : ℂ) / 2 - ∑ j, conj (α j) * z j) •
        FockSpace.expVec (z + α) ∧
    star (FockSpace.displacement α) = FockSpace.displacement (-α) ∧
    FockSpace.displacement (0 : ι → ℂ) = 1 ∧
    (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) (lp.single 2 0 1) =
      ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ) • FockSpace.expVec α := sorry

/-- The Weyl relation and strong continuity: $D(\alpha) D(\beta) = \exp\big(\frac12 \sum_j
(\alpha_j \bar\beta_j - \bar\alpha_j \beta_j)\big) D(\alpha + \beta)$; along a ray the
displacements form a one-parameter group, $D(t\alpha) D(s\alpha) = D((t + s)\alpha)$ for real $t$,
$s$; and $\alpha \mapsto D(\alpha)\psi$ is continuous for every $\psi$. -/
theorem displacement_mul {ι : Type*} [Fintype ι] :
    (∀ α β : ι → ℂ,
      (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) * FockSpace.displacement β =
        Complex.exp ((∑ j, (α j * conj (β j) - conj (α j) * β j)) / 2) •
          (FockSpace.displacement (α + β) : FockSpace ι →L[ℂ] FockSpace ι)) ∧
    (∀ (α : ι → ℂ) (t s : ℝ),
      (FockSpace.displacement ((t : ℂ) • α) : FockSpace ι →L[ℂ] FockSpace ι) *
          FockSpace.displacement ((s : ℂ) • α) =
        FockSpace.displacement (((t + s : ℝ) : ℂ) • α)) ∧
    ∀ ψ : FockSpace ι,
      Continuous fun α : ι → ℂ =>
        (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ := sorry

/-- Displacement of the ladder operators: let $\psi, \varphi \in \Gamma_s(\iota)$. If
$a_j\jmath\psi = \jmath\varphi$, then $a_j \jmath D(\alpha)\psi = \jmath D(\alpha)\varphi +
\alpha_j\, \jmath D(\alpha)\psi$; if $a_j^\dagger\jmath\psi = \jmath\varphi$, then
$a_j^\dagger \jmath D(\alpha)\psi = \jmath D(\alpha)\varphi + \bar\alpha_j\, \jmath
D(\alpha)\psi$; and $D(\alpha)\psi$ lies in the domain of the maximal realization of $a_j$ if
and only if $\psi$ does. So $D(\alpha)^* a_j D(\alpha) = a_j + \alpha_j$ and
$D(\alpha)^* a_j^\dagger D(\alpha) = a_j^\dagger + \bar\alpha_j$ on these vectors. -/
theorem displacement_ladder {ι : Type*} [Fintype ι] (α : ι → ℂ) (j : ι)
    (ψ φ : FockSpace ι) :
    (annihilate j (FockSpace.toFormal ψ) = FockSpace.toFormal φ →
      annihilate j (FockSpace.toFormal
          ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
        FockSpace.toFormal ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) φ) +
          α j • FockSpace.toFormal
            ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) ∧
    (create j (FockSpace.toFormal ψ) = FockSpace.toFormal φ →
      create j (FockSpace.toFormal
          ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) =
        FockSpace.toFormal ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) φ) +
          conj (α j) • FockSpace.toFormal
            ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ)) ∧
    ((FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) ψ ∈
        FockSpace.maxDomain (annihilate j) ↔ ψ ∈ FockSpace.maxDomain (annihilate j)) := sorry

/-- Irreducibility: a bounded operator $T$ of $\Gamma_s(\iota)$ that commutes with every
$D(\alpha)$ is $T = \langle 0|T|0\rangle\, 1$, and a closed subspace that every $D(\alpha)$ maps
into itself is $0$ or $\Gamma_s(\iota)$. -/
theorem displacement_irreducible {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ T : FockSpace ι →L[ℂ] FockSpace ι, (∀ α : ι → ℂ,
      Commute T (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι)) →
        T = ⟪(lp.single 2 0 1 : FockSpace ι), T (lp.single 2 0 1)⟫_ℂ • 1) ∧
    ∀ K : Submodule ℂ (FockSpace ι), IsClosed (K : Set (FockSpace ι)) →
      (∀ α : ι → ℂ, ∀ x ∈ K, (FockSpace.displacement α : FockSpace ι →L[ℂ] FockSpace ι) x ∈ K) →
        K = ⊥ ∨ K = ⊤ := sorry

/-- Squeezing operators: (definition) for $\zeta \in \mathbb C$ let
$\tau(\zeta) = \zeta \tanh|\zeta| / |\zeta|$, with $\tau(0) = 0$. For $\zeta \in \mathbb C^\iota$
write $c_j = \cosh|\zeta_j|$ and $\tau_j = \tau(\zeta_j)$. The squeezing operator
$\mathsf S(\zeta)$ is a unitary operator of $\Gamma_s(\iota)$ with
$\langle \varepsilon(w), \mathsf S(\zeta)\varepsilon(z)\rangle = (\prod_j c_j)^{-1/2}
\exp\big(\sum_j \bar\tau_j z_j^2/2\big) \exp\big(\sum_j (-\tau_j \bar w_j^2/2 + z_j \bar w_j /
c_j)\big)$ for all $w$, $z$, which determines it by entry 83. This is the normal-ordered form of
the product $\prod_j \exp\big(\frac12 (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})\big)$ of
one-mode squeezers (an identification that is not part of the statement); for real
$\zeta_j = r_j > 0$ it squeezes $\hat q_j$ (entries 93 and 105). Moreover
$\mathsf S(\zeta)^* = \mathsf S(-\zeta)$ and $\mathsf S(0) = 1$. -/
theorem squeeze_inner_expVec {ι : Type*} [Fintype ι] [DecidableEq ι] (ζ w z : ι → ℂ) :
    (∀ x : ℂ, tanhPhase x = if x = 0 then 0 else x * ((Real.tanh ‖x‖ / ‖x‖ : ℝ) : ℂ)) ∧
    ⟪FockSpace.expVec w,
        (FockSpace.squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) (FockSpace.expVec z)⟫_ℂ =
      (((∏ j, Real.cosh ‖ζ j‖) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (∑ j, conj (tanhPhase (ζ j)) * z j ^ 2 / 2) *
        Complex.exp (∑ j, (-tanhPhase (ζ j) / 2 * conj (w j) ^ 2 +
          z j / (Real.cosh ‖ζ j‖ : ℂ) * conj (w j))) ∧
    star (FockSpace.squeeze ζ) = FockSpace.squeeze (-ζ) ∧
    FockSpace.squeeze (0 : ι → ℂ) = 1 := sorry

/-- Squeezing and displacements: $\mathsf S(\zeta) D(\beta) = D(L_\zeta\beta)\, \mathsf S(\zeta)$
for every $\beta$, with $(L_\zeta\beta)_j = \cosh|\zeta_j|\, \beta_j - e^{i\phi_j}
\sinh|\zeta_j|\, \bar\beta_j$, where $e^{i\phi_j} = \zeta_j/|\zeta_j|$ (read as $0$ when
$\zeta_j = 0$). Along a ray the squeezing operators form a one-parameter group,
$\mathsf S(t\zeta) \mathsf S(s\zeta) = \mathsf S((t + s)\zeta)$ for real $t$, $s$, and
$\zeta \mapsto \mathsf S(\zeta)\psi$ is continuous for every $\psi$. -/
theorem squeeze_mul_displacement {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ ζ β : ι → ℂ,
      (FockSpace.squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) * FockSpace.displacement β =
        (FockSpace.displacement (fun j => (Real.cosh ‖ζ j‖ : ℂ) * β j -
            (if ζ j = 0 then 0 else ζ j / (‖ζ j‖ : ℂ)) * (Real.sinh ‖ζ j‖ : ℂ) * conj (β j)) :
          FockSpace ι →L[ℂ] FockSpace ι) * FockSpace.squeeze ζ) ∧
    (∀ (ζ : ι → ℂ) (t s : ℝ),
      (FockSpace.squeeze ((t : ℂ) • ζ) : FockSpace ι →L[ℂ] FockSpace ι) *
          FockSpace.squeeze ((s : ℂ) • ζ) =
        FockSpace.squeeze (((t + s : ℝ) : ℂ) • ζ)) ∧
    ∀ ψ : FockSpace ι,
      Continuous fun ζ : ι → ℂ => (FockSpace.squeeze ζ : FockSpace ι →L[ℂ] FockSpace ι) ψ := sorry

/-! ## Gaussian unitaries

There are $n$ modes, and $\Gamma_s(n)$ is the Fock space of the modes $\{1, \dots, n\}$. A
phase-space vector $u = (q, p) \in \mathbb R^{2n}$ is indexed as in the first section, and
$\sigma(u, v) = u^T \Omega v$. The quadratures $\hat q_j$ and $\hat p_j$ are the linear maps
$(a_j + a_j^\dagger)/\sqrt2$ and $i(a_j^\dagger - a_j)/\sqrt2$ of the formal Fock space, and
$\hat R = (\hat q, \hat p)$. -/

/-- Weyl operators on Fock space: (definition) for $u = (q, p)$, $W(u) = D(\alpha(u))$ with
$\alpha(u)_j = (q_j + i p_j)/\sqrt2$; formally $W(u) = \exp(i(p \cdot \hat q - q \cdot \hat p))$,
an identification that is not part of the statement. They satisfy the Weyl relation
$W(u) W(v) = e^{-i\sigma(u, v)/2} W(u + v)$, $W(u)^* = W(-u)$, and
$\langle 0|W(u)|0\rangle = e^{-|u|^2/4}$. -/
theorem weylOp_eq {n : ℕ} (u v : Fin n ⊕ Fin n → ℝ) :
    FockSpace.weylOp u = FockSpace.displacement (fun j =>
      ((u (Sum.inl j) : ℂ) + (u (Sum.inr j) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)) ∧
    (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * FockSpace.weylOp v =
      Complex.exp (((-(u ⬝ᵥ symplecticForm n *ᵥ v) / 2 : ℝ) : ℂ) * Complex.I) •
        (FockSpace.weylOp (u + v) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ∧
    star (FockSpace.weylOp u) = FockSpace.weylOp (-u) ∧
    ⟪(lp.single 2 0 1 : FockSpace (Fin n)),
        (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)⟫_ℂ =
      ((Real.exp (-(∑ i, u i ^ 2) / 4) : ℝ) : ℂ) := sorry

/-- Gaussian unitaries (definition): a unitary operator $U$ of $\Gamma_s(n)$ is Gaussian with
symplectic matrix $M$ and displacement vector $d \in \mathbb R^{2n}$, or with data $(M, d)$, when
$M$ is symplectic and $U^* W(u) U = e^{-i\sigma(u, d)} W(M^{-1}u)$ for every
$u \in \mathbb R^{2n}$, the exponentiated form of $U^* \hat R U = M \hat R + d$ (entry 95). -/
theorem isGaussianUnitary_iff {n : ℕ} (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ) :
    FockSpace.IsGaussianUnitary U M d ↔ M * symplecticForm n * Mᵀ = symplecticForm n ∧
      ∀ u, (star U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) * FockSpace.weylOp u * U =
        Complex.exp (-((u ⬝ᵥ symplecticForm n *ᵥ d : ℝ) : ℂ) * Complex.I) •
          (FockSpace.weylOp (M⁻¹ *ᵥ u) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) := sorry

/-- Composition, adjoint and uniqueness: if $U_1$, $U_2$ are Gaussian with data $(M_1, d_1)$,
$(M_2, d_2)$, then $U_1 U_2$ is Gaussian with data $(M_1 M_2, d_1 + M_1 d_2)$; if $U$ is Gaussian
with data $(M, d)$, then $U^*$ is Gaussian with data $(M^{-1}, -M^{-1} d)$; the data of a Gaussian
unitary are unique; and two Gaussian unitaries with the same data differ by a factor $\lambda$
with $|\lambda| = 1$. -/
theorem isGaussianUnitary_mul {n : ℕ} :
    (∀ (U₁ U₂ : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M₁ M₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d₁ d₂ : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U₁ M₁ d₁ → FockSpace.IsGaussianUnitary U₂ M₂ d₂ →
        FockSpace.IsGaussianUnitary (U₁ * U₂) (M₁ * M₂) (d₁ + M₁ *ᵥ d₂)) ∧
    (∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d → FockSpace.IsGaussianUnitary (star U) M⁻¹ (-(M⁻¹ *ᵥ d))) ∧
    (∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d d' : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d → FockSpace.IsGaussianUnitary U M' d' → M = M' ∧ d = d') ∧
    ∀ (U V : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d → FockSpace.IsGaussianUnitary V M d →
        ∃ c : ℂ, ‖c‖ = 1 ∧ (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
          c • (V : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) := sorry

/-- Examples and existence: $D(\alpha)$ is Gaussian with data $(1, \delta(\alpha))$, where
$\delta(\alpha) = \sqrt2\, (\mathrm{Re}\, \alpha, \mathrm{Im}\, \alpha)$;
$\mathsf U_{\mathcal U}$ is Gaussian with data $(O_{\mathcal U}, 0)$ for every unitary
$\mathcal U$; $\mathsf S(r)$ with real squeezing parameters $r \in \mathbb R^n$ is Gaussian with
data $(\Sigma(r), 0)$; and for every symplectic $M$ and every $d \in \mathbb R^{2n}$ there is a
Gaussian unitary with data $(M, d)$. -/
theorem isGaussianUnitary_examples {n : ℕ} :
    (∀ α : Fin n → ℂ, FockSpace.IsGaussianUnitary (FockSpace.displacement α) 1
      (Sum.elim (fun j => Real.sqrt 2 * (α j).re) fun j => Real.sqrt 2 * (α j).im)) ∧
    (∀ U : Matrix.unitaryGroup (Fin n) ℂ, FockSpace.IsGaussianUnitary (FockSpace.secondQuantRep U)
      (orthogonalSymplecticOfUnitary U) 0) ∧
    (∀ r : Fin n → ℝ, FockSpace.IsGaussianUnitary (FockSpace.squeeze fun j => (r j : ℂ))
      (squeezingMatrix r) 0) ∧
    ∀ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, M * symplecticForm n * Mᵀ = symplecticForm n →
      ∀ d : Fin n ⊕ Fin n → ℝ, ∃ U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
        FockSpace.IsGaussianUnitary U M d := sorry

/-- Factorization, Proposition 5 of Tjoa and Cirac, arXiv:2607.28753: let $U$ be Gaussian with data $(M, d)$. If
$M = O_{\mathcal U} \Sigma(r) O_{\mathcal V}$ with unitaries $\mathcal U$, $\mathcal V$ and
$r \in \mathbb R^n$, then $U = \lambda\, \mathsf U_{\mathcal U} D(\alpha) \mathsf S(r) \mathsf
U_{\mathcal V}$ with $|\lambda| = 1$ and $\alpha = \alpha(O_{\mathcal U}^T d)$, the complex vector
of $O_{\mathcal U}^T d$ as for the Weyl operators. Such a decomposition of $M$ exists with
$r \ge 0$: there are unitaries $\mathcal U$, $\mathcal V$, $r \ge 0$ and $\lambda$ with
$|\lambda| = 1$ such that $M = O_{\mathcal U} \Sigma(r) O_{\mathcal V}$ and
$U = \lambda\, \mathsf U_{\mathcal U} D(\alpha(O_{\mathcal U}^T d)) \mathsf S(r) \mathsf
U_{\mathcal V}$. -/
theorem gaussianUnitary_factorization {n : ℕ}
    (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ)
    (hU : FockSpace.IsGaussianUnitary U M d) :
    (∀ (𝒰 𝒱 : Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℝ),
      M = orthogonalSymplecticOfUnitary 𝒰 * squeezingMatrix r * orthogonalSymplecticOfUnitary 𝒱 →
      ∃ c : ℂ, ‖c‖ = 1 ∧ (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
        c • ((FockSpace.secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
          FockSpace.displacement (fun j =>
            ((((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d) (Sum.inl j) : ℂ) +
              (((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d) (Sum.inr j) : ℂ) * Complex.I) /
                (Real.sqrt 2 : ℂ)) *
          FockSpace.squeeze (fun j => (r j : ℂ)) * FockSpace.secondQuantRep 𝒱)) ∧
    ∃ (c : ℂ) (𝒰 𝒱 : Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℝ),
      0 ≤ r ∧ ‖c‖ = 1 ∧
      M = orthogonalSymplecticOfUnitary 𝒰 * squeezingMatrix r * orthogonalSymplecticOfUnitary 𝒱 ∧
      (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
        c • ((FockSpace.secondQuantRep 𝒰 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) *
          FockSpace.displacement (fun j =>
            ((((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d) (Sum.inl j) : ℂ) +
              (((orthogonalSymplecticOfUnitary 𝒰)ᵀ *ᵥ d) (Sum.inr j) : ℂ) * Complex.I) /
                (Real.sqrt 2 : ℂ)) *
          FockSpace.squeeze (fun j => (r j : ℂ)) * FockSpace.secondQuantRep 𝒱) := sorry

/-- Action on the quadratures: (definition) the quadratures $\hat q_j$ and $\hat p_j$ are
$(a_j + a_j^\dagger)/\sqrt2$ and $i(a_j^\dagger - a_j)/\sqrt2$. Let $U$ be Gaussian with data
$(M, d)$, and let $\mathcal Q$ be the set of $\psi \in \Gamma_s(n)$ in the domain of the maximal
realization of every $a_j$. Then $U\psi \in \mathcal Q$ if and only if $\psi \in \mathcal Q$. For
$\psi \in \mathcal Q$ and every phase-space index $k$ there is $\xi \in \Gamma_s(n)$ with
$\jmath\xi = \sum_l M_{kl} \hat R_l \jmath\psi + d_k \jmath\psi$, and for every such $\xi$,
$\hat R_k \jmath U\psi = \jmath U\xi$: $U^* \hat R_k U = \sum_l M_{kl} \hat R_l + d_k$ on
$\mathcal Q$. -/
theorem gaussianUnitary_quadratures {n : ℕ} :
    (∀ j : Fin n, FockSpace.quadrature (Sum.inl j) =
        ((Real.sqrt 2 : ℂ)⁻¹) • (annihilate j + create j) ∧
      FockSpace.quadrature (Sum.inr j) =
        (Complex.I / (Real.sqrt 2 : ℂ)) • (create j - annihilate j)) ∧
    ∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d → ∀ ψ : FockSpace (Fin n),
        ((∀ j, (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ ∈
            FockSpace.maxDomain (annihilate j)) ↔ ∀ j, ψ ∈ FockSpace.maxDomain (annihilate j)) ∧
        ((∀ j, ψ ∈ FockSpace.maxDomain (annihilate j)) → ∀ k : Fin n ⊕ Fin n,
          (∃ ξ : FockSpace (Fin n), FockSpace.toFormal ξ =
            (∑ l, (M k l : ℂ) • FockSpace.quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ))
              (FockSpace.toFormal ψ) + (d k : ℂ) • FockSpace.toFormal ψ) ∧
          ∀ ξ : FockSpace (Fin n), FockSpace.toFormal ξ =
            (∑ l, (M k l : ℂ) • FockSpace.quadrature l : Module.End ℂ (FormalFock (Fin n) ℂ))
              (FockSpace.toFormal ψ) + (d k : ℂ) • FockSpace.toFormal ψ →
            FockSpace.quadrature k
                (FockSpace.toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ)) =
              FockSpace.toFormal ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ξ)) := sorry

/-! ## Pure Gaussian states

The characteristic function of $\psi \in \Gamma_s(n)$ is $\chi_\psi(u) = \langle \psi,
W(u)\psi\rangle$, $u \in \mathbb R^{2n}$. A pure Gaussian state is a vector $U|0\rangle$ with $U$ a
Gaussian unitary. The covariance matrix $\gamma$ is normalized as twice the symmetrized covariance,
$\gamma_{kl} = \langle \{\hat R_k - d_k, \hat R_l - d_l\}\rangle$, so that the vacuum has
$\gamma = 1$ (entry 103); the matrix $\Gamma$ of Eq. (13) of Tjoa and Cirac is $\gamma/2$. -/

/-- A vector is determined up to a phase by its characteristic function: if $\psi \ne 0$ and
$\chi_\varphi = \chi_\psi$, then $\varphi = \lambda\psi$ with $|\lambda| = 1$. If $U$ is Gaussian
with data $(M, d)$, then $\chi_{U\psi}(u) = e^{-i\sigma(u, d)} \chi_\psi(M^{-1}u)$. -/
theorem charFun_determines {n : ℕ} :
    (∀ ψ φ : FockSpace (Fin n), ψ ≠ 0 →
      (∀ u : Fin n ⊕ Fin n → ℝ,
        ⟪φ, (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) φ⟫_ℂ =
          ⟪ψ, (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ⟫_ℂ) →
        ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ) ∧
    ∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d → ∀ (ψ : FockSpace (Fin n)) (u : Fin n ⊕ Fin n → ℝ),
        ⟪(U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ,
            (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
              ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ)⟫_ℂ =
          Complex.exp (-((u ⬝ᵥ symplecticForm n *ᵥ d : ℝ) : ℂ) * Complex.I) *
            ⟪ψ, (FockSpace.weylOp (M⁻¹ *ᵥ u) : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))
              ψ⟫_ℂ := sorry

/-- Gaussian characteristic functions (definition): $\psi \in \Gamma_s(n)$ has the Gaussian
characteristic function with displacement vector $d \in \mathbb R^{2n}$ and covariance matrix
$\gamma$ when $\gamma^T = \gamma$ and
$\chi_\psi(u) = \exp\big(-i\sigma(u, d) - \frac14 u^T \Omega \gamma \Omega^T u\big)$ for every
$u$. -/
theorem hasGaussianCharFun_iff {n : ℕ} (ψ : FockSpace (Fin n)) (d : Fin n ⊕ Fin n → ℝ)
    (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    FockSpace.HasGaussianCharFun ψ d γ ↔ γᵀ = γ ∧ ∀ u : Fin n ⊕ Fin n → ℝ,
      ⟪ψ, (FockSpace.weylOp u : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ⟫_ℂ =
        Complex.exp (-((u ⬝ᵥ symplecticForm n *ᵥ d : ℝ) : ℂ) * Complex.I -
          ((u ⬝ᵥ (symplecticForm n * γ * (symplecticForm n)ᵀ) *ᵥ u : ℝ) : ℂ) / 4) := sorry

/-- Properties of Gaussian characteristic functions: if $\psi$ has the Gaussian characteristic
function with $(d, \gamma)$, then $\|\psi\| = 1$; the data $(d, \gamma)$ are unique; $\gamma$ is
admissible; $\gamma$ is symplectic, $\gamma \Omega \gamma^T = \Omega$; and every $\varphi$ with the
Gaussian characteristic function with the same $(d, \gamma)$ is $\varphi = \lambda\psi$ with
$|\lambda| = 1$. -/
theorem hasGaussianCharFun_props {n : ℕ} {ψ : FockSpace (Fin n)} {d : Fin n ⊕ Fin n → ℝ}
    {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (h : FockSpace.HasGaussianCharFun ψ d γ) :
    ‖ψ‖ = 1 ∧
    (∀ (d' : Fin n ⊕ Fin n → ℝ) (γ' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      FockSpace.HasGaussianCharFun ψ d' γ' → d = d' ∧ γ = γ') ∧
    IsAdmissible γ ∧ γ * symplecticForm n * γᵀ = symplecticForm n ∧
    ∀ φ : FockSpace (Fin n), FockSpace.HasGaussianCharFun φ d γ →
      ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := sorry

/-- Gaussian unitaries on the vacuum: if $U$ is Gaussian with data $(M, d)$, then $U|0\rangle$ has
the Gaussian characteristic function with displacement vector $d$ and covariance matrix $M M^T$.
Its moments, Eq. (13) of Tjoa and Cirac: there are $\phi_k \in \Gamma_s(n)$, one for each phase-space index
$k$, with $\hat R_k \jmath U|0\rangle = \jmath\phi_k$, $\langle U|0\rangle, \phi_k\rangle = d_k$ and
$\langle \phi_k - d_k U|0\rangle, \phi_l - d_l U|0\rangle\rangle = \frac12 ((M M^T)_{kl} +
i\Omega_{kl})$. So twice the real part of the left side, the symmetrized covariance
$\langle\{\hat R_k - d_k, \hat R_l - d_l\}\rangle$, is $\gamma_{kl}$ with $\gamma = M M^T$, and the
$\Gamma$ of Tjoa and Cirac is $\gamma/2$. -/
theorem gaussianUnitary_vacuum {n : ℕ} (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ)
    (hU : FockSpace.IsGaussianUnitary U M d) :
    FockSpace.HasGaussianCharFun
      ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)) d (M * Mᵀ) ∧
    ∃ φ : Fin n ⊕ Fin n → FockSpace (Fin n),
      (∀ k, FockSpace.quadrature k (FockSpace.toFormal
        ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1))) =
          FockSpace.toFormal (φ k)) ∧
      (∀ k, ⟪(U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1), φ k⟫_ℂ =
        (d k : ℂ)) ∧
      ∀ k l, ⟪φ k - (d k : ℂ) • (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1),
          φ l - (d l : ℂ) • (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)⟫_ℂ =
        (((M * Mᵀ) k l : ℂ) + Complex.I * (symplecticForm n k l : ℂ)) / 2 := sorry

/-- The two definitions of pure Gaussian states agree: $\psi = U|0\rangle$ for a Gaussian unitary
$U$ if and only if $\psi$ has the Gaussian characteristic function with some $(d, \gamma)$. If
$\psi$ has it with $(d, \gamma)$ and $M$ is symplectic with $\gamma = M M^T$, then
$\psi = U|0\rangle$ for a Gaussian unitary $U$ with data $(M, d)$. -/
theorem isPureGaussian_iff {n : ℕ} (ψ : FockSpace (Fin n)) :
    ((∃ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
        (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
        FockSpace.IsGaussianUnitary U M d ∧
          ψ = (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)) ↔
      ∃ (d : Fin n ⊕ Fin n → ℝ) (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        FockSpace.HasGaussianCharFun ψ d γ) ∧
    ∀ (d : Fin n ⊕ Fin n → ℝ) (γ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      FockSpace.HasGaussianCharFun ψ d γ → M * symplecticForm n * Mᵀ = symplecticForm n →
        γ = M * Mᵀ → ∃ U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
          FockSpace.IsGaussianUnitary U M d ∧
            ψ = (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1) := sorry

/-- The vacuum component: every pure Gaussian state $\psi = U|0\rangle$ has a nonzero coefficient
$\psi(0)$ at the vacuum configuration, its component along $|0\rangle$. Hence a nonzero $\Phi$
with $\Phi(0) = 0$, for example a number state $|m\rangle$ with $m \ne 0$, is not a multiple
$c\psi$ of a pure Gaussian state $\psi$. -/
theorem pureGaussian_vacuum_ne_zero {n : ℕ} :
    (∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
      FockSpace.IsGaussianUnitary U M d →
        (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1) 0 ≠ 0) ∧
    (∀ Φ : FockSpace (Fin n), Φ ≠ 0 → Φ 0 = 0 →
      ∀ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
        (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n ⊕ Fin n → ℝ),
        FockSpace.IsGaussianUnitary U M d → ∀ c : ℂ,
          Φ ≠ c • (U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)) := sorry

/-! ## Further examples: Fock space and pure Gaussian states

These examples show that the hypotheses of entries 70 and 71, and the hypothesis of a Gaussian
characteristic function in entries 97 to 101, can be met; Gaussian unitaries exist by entry 93. -/

/-- The ladder operators are coefficient-finite, so that entries 70 and 71 apply to $a_j$ and
$a_j^\dagger$. -/
theorem witness_ladder_coeffFinite {ι : Type*} (j : ι) :
    (∀ n, ∃ s : Finset (ι →₀ ℕ), ∀ φ φ' : FormalFock ι ℂ,
      (∀ m ∈ s, φ.coeff m = φ'.coeff m) → (annihilate j φ).coeff n = (annihilate j φ').coeff n) ∧
    ∀ n, ∃ s : Finset (ι →₀ ℕ), ∀ φ φ' : FormalFock ι ℂ,
      (∀ m ∈ s, φ.coeff m = φ'.coeff m) → (create j φ).coeff n = (create j φ').coeff n := sorry

/-- The vacuum: on $n$ modes the vacuum $|0\rangle$ has the Gaussian characteristic function with
$d = 0$ and $\gamma = 1$. -/
theorem witness_vacuum (n : ℕ) :
    FockSpace.HasGaussianCharFun (lp.single 2 0 1 : FockSpace (Fin n)) 0 1 := sorry

/-- A coherent state: for $\alpha \in \mathbb C^n$ the coherent state $D(\alpha)|0\rangle$ has the
coefficients $(D(\alpha)|0\rangle)(m) = e^{-|\alpha|^2/2} \alpha^m/\sqrt{m!}$ and the Gaussian
characteristic function with the displacement vector
$\delta(\alpha) = \sqrt2\, (\mathrm{Re}\, \alpha, \mathrm{Im}\, \alpha)$ and the vacuum covariance
$\gamma = 1$. -/
theorem witness_coherent_state {n : ℕ} (α : Fin n → ℂ) :
    (∀ m : Fin n →₀ ℕ,
      (FockSpace.displacement α : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1) m =
        ((Real.exp (-(∑ j, ‖α j‖ ^ 2) / 2) : ℝ) : ℂ) * ((∏ j, α j ^ m j) /
          ((Real.sqrt ((m.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ))) ∧
    FockSpace.HasGaussianCharFun
      ((FockSpace.displacement α : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1))
      (Sum.elim (fun j => Real.sqrt 2 * (α j).re) fun j => Real.sqrt 2 * (α j).im) 1 := sorry

/-- A squeezed vacuum: on one mode, for real $r$, the squeezed vacuum $\mathsf S(r)|0\rangle$ has
the Gaussian characteristic function with $d = 0$ and the covariance matrix
$\gamma = \mathrm{diag}(e^{-2r}, e^{2r})$. For $r > 0$ the position quadrature is squeezed,
$\gamma_{qq} = e^{-2r} < 1$; $r$ may have either sign. -/
theorem witness_squeezed_vacuum (r : ℝ) :
    FockSpace.HasGaussianCharFun
      ((FockSpace.squeeze (fun _ : Fin 1 => (r : ℂ)) : FockSpace (Fin 1) →L[ℂ] FockSpace (Fin 1))
        (lp.single 2 0 1)) 0
      (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => Real.exp (-2 * r))
        fun _ => Real.exp (2 * r))) := sorry

/-! ## Existence of pure Gaussian states

The notation is that of the section on pure Gaussian states. -/

/-- Every admissible symplectic covariance matrix occurs: let $\gamma$ be admissible and
symplectic, $\gamma \Omega \gamma^T = \Omega$, and let $d \in \mathbb R^{2n}$. There is a
Gaussian unitary $U$, with data $(M, d)$ for some symplectic $M$, such that $U|0\rangle$ has the
Gaussian characteristic function with displacement vector $d$ and covariance matrix $\gamma$.
Hence a vector with the Gaussian characteristic function with $(d, \gamma)$ exists if and only if
$\gamma$ is admissible and symplectic. -/
theorem exists_hasGaussianCharFun_iff {n : ℕ} (d : Fin n ⊕ Fin n → ℝ)
    (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (IsAdmissible γ → γ * symplecticForm n * γᵀ = symplecticForm n →
      ∃ (U : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)))
        (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ), FockSpace.IsGaussianUnitary U M d ∧
          FockSpace.HasGaussianCharFun
            ((U : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) (lp.single 2 0 1)) d γ) ∧
    ((∃ ψ : FockSpace (Fin n), FockSpace.HasGaussianCharFun ψ d γ) ↔
      IsAdmissible γ ∧ γ * symplecticForm n * γᵀ = symplecticForm n) := sorry

/-! ## Quadratic Hamiltonians

Here $E$ is a complex Hilbert space, with the inner product linear in the second argument. An
operator $A$ on $E$ is a linear map defined on a subspace $\mathrm{dom}\, A$ of $E$; $A^*$ is its
adjoint, $\overline A$ its closure, the operator whose graph is the closure of the graph of $A$,
and $A \restriction E_0$ its restriction to a subspace $E_0$. An operator $A$ is self-adjoint when
$A^* = A$, domains included. A one-parameter group generated by $A$ carries the physicist's sign,
$U_t = e^{-itA}$. On Fock space there are $n$ modes, $\hat R = (\hat q, \hat p)$ are the
quadratures of entry 95, normalized so that $[\hat R_k, \hat R_l] = i\Omega_{kl}$, and $\bar T$
is the maximal realization of a linear map $T$ of the formal Fock space (entry 70). For a
configuration $m$, $|m| = \sum_j m_j$ is its number of particles. -/

/-- One-parameter unitary groups and their generators (definitions): a map $t \mapsto U_t$ from
$\mathbb R$ to the unitary operators of $E$ is a strongly continuous one-parameter unitary group
when $U_0 = 1$, $U_{s+t} = U_s U_t$ for all real $s$, $t$, and $t \mapsto U_t\psi$ is continuous
for every $\psi$. An operator $A$ generates $U$, written $U_t = e^{-itA}$, when $U$ is such a
group, $\mathrm{dom}\, A$ is the set of the $\psi$ at which $t \mapsto U_t\psi$ is differentiable
at $t = 0$, and $\frac{d}{dt} U_t\psi\big|_{t=0} = -iA\psi$ for these $\psi$. -/
theorem isGenerator_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →ₗ.[ℂ] E) (U : ℝ → unitary (E →L[ℂ] E)) :
    (BosonicLean.IsUnitaryGroup U ↔ U 0 = 1 ∧ (∀ s t, U (s + t) = U s * U t) ∧
      ∀ ψ, Continuous fun t => (U t : E →L[ℂ] E) ψ) ∧
    (BosonicLean.IsGenerator A U ↔ BosonicLean.IsUnitaryGroup U ∧
      (∀ ψ, ψ ∈ A.domain ↔ ∃ v, HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) v 0) ∧
      ∀ ψ : A.domain,
        HasDerivAt (fun t : ℝ => (U t : E →L[ℂ] E) ψ) (-(Complex.I • A ψ)) 0) := sorry

/-- Generators, first properties: let $A$ generate $U$. For $\psi \in \mathrm{dom}\, A$ and every
real $t$, $U_t\psi \in \mathrm{dom}\, A$ with $AU_t\psi = U_tA\psi$, and
$\frac{d}{dt} U_t\psi = -iU_tA\psi$. The domain of $A$ is dense, and $A$ is self-adjoint. If $A$
also generates $V$, then $U = V$. -/
theorem isGenerator_props {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} {U : ℝ → unitary (E →L[ℂ] E)}
    (hA : BosonicLean.IsGenerator A U) :
    (∀ (ψ : A.domain) (t : ℝ), ∃ φ : A.domain, (φ : E) = (U t : E →L[ℂ] E) ψ ∧
      A φ = (U t : E →L[ℂ] E) (A ψ) ∧
      HasDerivAt (fun s : ℝ => (U s : E →L[ℂ] E) ψ) (-(Complex.I • (U t : E →L[ℂ] E) (A ψ))) t) ∧
    Dense (A.domain : Set E) ∧ IsSelfAdjoint A ∧
    ∀ V : ℝ → unitary (E →L[ℂ] E), BosonicLean.IsGenerator A V → U = V := sorry

/-- Generators from a core, conjugates, shifts and bounded generators. Let $B$ be self-adjoint and
$E_0 \subseteq \mathrm{dom}\, B$ a subspace with $\overline{B \restriction E_0} = B$ (a core for
$B$). If $V$ is a strongly continuous one-parameter unitary group with
$\frac{d}{dt} V_t\psi\big|_{t=0} = -iB\psi$ for every $\psi \in E_0$, then $B$ generates $V$. Let
$A$ generate $U$. For a unitary $Z$, the operator $Z^*AZ$ with domain
$\{\psi : Z\psi \in \mathrm{dom}\, A\}$ generates $t \mapsto Z^*U_tZ$; for real $c$, the operator
$A + c$ with domain $\mathrm{dom}\, A$ generates $t \mapsto e^{-itc}U_t$. A bounded self-adjoint
operator $T$ generates $t \mapsto e^{-itT} = \sum_{k \ge 0} (-itT)^k/k!$. -/
theorem isGenerator_of_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    (∀ B : E →ₗ.[ℂ] E, IsSelfAdjoint B → ∀ (E₀ : Submodule ℂ E) (hE₀ : E₀ ≤ B.domain),
      (B.domRestrict E₀).closure = B → ∀ V : ℝ → unitary (E →L[ℂ] E),
        BosonicLean.IsUnitaryGroup V →
        (∀ ψ : E₀, HasDerivAt (fun t : ℝ => (V t : E →L[ℂ] E) ψ)
          (-(Complex.I • B ⟨ψ, hE₀ ψ.2⟩)) 0) → BosonicLean.IsGenerator B V) ∧
    (∀ (A B : E →ₗ.[ℂ] E) (U : ℝ → unitary (E →L[ℂ] E)) (Z : unitary (E →L[ℂ] E)),
      BosonicLean.IsGenerator A U → (∀ ψ, ψ ∈ B.domain ↔ (Z : E →L[ℂ] E) ψ ∈ A.domain) →
      (∀ (ψ : B.domain) (φ : A.domain), (φ : E) = (Z : E →L[ℂ] E) ψ →
        B ψ = (star (Z : E →L[ℂ] E)) (A φ)) →
      BosonicLean.IsGenerator B fun t => star Z * U t * Z) ∧
    (∀ (A B : E →ₗ.[ℂ] E) (U V : ℝ → unitary (E →L[ℂ] E)) (c : ℝ),
      BosonicLean.IsGenerator A U → B.domain = A.domain →
      (∀ (ψ : B.domain) (φ : A.domain), (φ : E) = ψ → B ψ = A φ + (c : ℂ) • (ψ : E)) →
      (∀ t : ℝ, (V t : E →L[ℂ] E) =
        Complex.exp (-((t * c : ℝ) : ℂ) * Complex.I) • (U t : E →L[ℂ] E)) →
      BosonicLean.IsGenerator B V) ∧
    ∀ T : E →L[ℂ] E, IsSelfAdjoint T → ∃ V : ℝ → unitary (E →L[ℂ] E),
      (∀ t : ℝ, (V t : E →L[ℂ] E) = NormedSpace.exp ((-(t : ℂ) * Complex.I) • T)) ∧
      BosonicLean.IsGenerator ((T : E →ₗ[ℂ] E).toPMap ⊤) V := sorry

/-- Analytic vectors with a common radius: let $E_0 \subseteq E$ be a dense subspace,
$A : E_0 \to E_0$ linear and symmetric, $\langle Ax, y\rangle = \langle x, Ay\rangle$ for
$x, y \in E_0$, and $\rho > 0$ with $\sum_n \rho^n \|A^n x\|/n! < \infty$ for every $x \in E_0$.
Regard $A$ as an operator on $E$ with domain $E_0$. Then its closure $\overline A$ is self-adjoint,
$\overline A$ generates exactly one strongly continuous one-parameter unitary group $U$, and
$U_t x = \sum_n (-it)^n A^n x/n!$ for $|t| < \rho$ and $x \in E_0$. -/
theorem analytic_vectors {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (E₀ : Submodule ℂ E) (hE₀ : Dense (E₀ : Set E)) (A : E₀ →ₗ[ℂ] E₀)
    (hA : ∀ x y : E₀, ⟪(A x : E), (y : E)⟫_ℂ = ⟪(x : E), (A y : E)⟫_ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (han : ∀ x : E₀, Summable fun n : ℕ => ρ ^ n / n.factorial * ‖((A ^ n) x : E)‖) :
    IsSelfAdjoint (⟨E₀, E₀.subtype ∘ₗ A⟩ : E →ₗ.[ℂ] E).closure ∧
      (∃! U : ℝ → unitary (E →L[ℂ] E),
        BosonicLean.IsGenerator (⟨E₀, E₀.subtype ∘ₗ A⟩ : E →ₗ.[ℂ] E).closure U) ∧
      ∀ U : ℝ → unitary (E →L[ℂ] E),
        BosonicLean.IsGenerator (⟨E₀, E₀.subtype ∘ₗ A⟩ : E →ₗ.[ℂ] E).closure U →
        ∀ t : ℝ, |t| < ρ → ∀ x : E₀,
          HasSum (fun n : ℕ => ((-(t : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)) • ((A ^ n) x : E))
            ((U t : E →L[ℂ] E) x) := sorry

/-- The quadratic Hamiltonian (definitions) and its first properties: $\mathcal D$ is the subspace of the finitely supported
vectors of $\Gamma_s(n)$, the $\psi$ with $\psi(m) \ne 0$ for only finitely many configurations
$m$. For a real $2n \times 2n$ matrix $K$ and $f \in \mathbb R^{2n}$, the quadratic Hamiltonian is
the linear map $H = \sum_{k,l} \frac12 K_{kl} \hat R_k \hat R_l + \sum_k f_k \hat R_k$ of the
formal Fock space. Let $C_H = \sum_{k,l} |K_{kl}| + \sqrt2 \sum_k |f_k|$. If $\psi \in
\Gamma_s(n)$ vanishes above $\nu$ particles, $\psi(m) = 0$ whenever $|m| > \nu$, then $H\jmath\psi
= \jmath\varphi$ for a $\varphi \in \Gamma_s(n)$ that vanishes above $\nu + 2$ particles, with
$\|\varphi\| \le C_H(\nu + 2)\|\psi\|$. For $\psi \in \mathcal D$ and $\rho \ge 0$ with
$2C_H\rho < 1$ there are $\psi_r \in \Gamma_s(n)$, $r \in \mathbb N$, with
$\jmath\psi_r = H^r\jmath\psi$ and $\sum_r \rho^r \|\psi_r\|/r! < \infty$. If $K$ is symmetric,
$H$ is symmetric on $\mathcal D$: for $\psi, \varphi \in \mathcal D$,
$\langle H\psi, \varphi\rangle = \langle \psi, H\varphi\rangle$, where $H\psi$ is the vector
$\psi'$ with $\jmath\psi' = H\jmath\psi$. -/
theorem quadraticHamiltonian_eq {n : ℕ} (K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (f : Fin n ⊕ Fin n → ℝ) :
    (∀ ψ : FockSpace (Fin n),
      ψ ∈ FockSpace.finiteSupport (Fin n) ↔ (Function.support ψ).Finite) ∧
    FockSpace.quadraticHamiltonian K f =
      ∑ k, ∑ l, ((K k l / 2 : ℝ) : ℂ) • (FockSpace.quadrature k * FockSpace.quadrature l) +
        ∑ k, (f k : ℂ) • FockSpace.quadrature k ∧
    (∀ (ν : ℕ) (ψ : FockSpace (Fin n)), (∀ m : Fin n →₀ ℕ, ν < m.degree → ψ m = 0) →
      ∃ φ : FockSpace (Fin n),
        FockSpace.toFormal φ = FockSpace.quadraticHamiltonian K f (FockSpace.toFormal ψ) ∧
        (∀ m : Fin n →₀ ℕ, ν + 2 < m.degree → φ m = 0) ∧
        ‖φ‖ ≤ (∑ k, ∑ l, |K k l| + Real.sqrt 2 * ∑ k, |f k|) * (ν + 2) * ‖ψ‖) ∧
    (∀ ψ ∈ FockSpace.finiteSupport (Fin n), ∀ ρ : ℝ, 0 ≤ ρ →
      2 * (∑ k, ∑ l, |K k l| + Real.sqrt 2 * ∑ k, |f k|) * ρ < 1 →
      ∃ ψs : ℕ → FockSpace (Fin n), (∀ r, FockSpace.toFormal (ψs r) =
          (FockSpace.quadraticHamiltonian K f ^ r) (FockSpace.toFormal ψ)) ∧
        Summable fun r : ℕ => ρ ^ r / r.factorial * ‖ψs r‖) ∧
    (Kᵀ = K → ∀ ψ φ ψ' φ' : FockSpace (Fin n), ψ ∈ FockSpace.finiteSupport (Fin n) →
      φ ∈ FockSpace.finiteSupport (Fin n) →
      FockSpace.toFormal ψ' = FockSpace.quadraticHamiltonian K f (FockSpace.toFormal ψ) →
      FockSpace.toFormal φ' = FockSpace.quadraticHamiltonian K f (FockSpace.toFormal φ) →
      ⟪ψ', φ⟫_ℂ = ⟪ψ, φ'⟫_ℂ) := sorry

/-- Commutators: on the formal Fock space $[\hat R_k, \hat R_l] = i\Omega_{kl}$. Let $K$ be
symmetric. Then $[\hat R_k, H] = i\big(\sum_m (\Omega K)_{km} \hat R_m + (\Omega f)_k\big)$, and
for $v \in \mathbb R^{2n}$ the field $\Phi_v = \sigma(v, \hat R) = \sum_i (\Omega^T v)_i \hat R_i$
satisfies $[\Phi_v, H] = -i(\Phi_{\Omega K v} + f^T v)$. -/
theorem quadraticHamiltonian_commutators {n : ℕ} (K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (f : Fin n ⊕ Fin n → ℝ) (k l : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → ℝ) :
    FockSpace.quadrature k * FockSpace.quadrature l -
        FockSpace.quadrature l * FockSpace.quadrature k =
      (Complex.I * (symplecticForm n k l : ℂ)) • 1 ∧
    (Kᵀ = K →
      FockSpace.quadrature k * FockSpace.quadraticHamiltonian K f -
          FockSpace.quadraticHamiltonian K f * FockSpace.quadrature k =
        Complex.I • (∑ m, (((symplecticForm n * K) k m : ℝ) : ℂ) • FockSpace.quadrature m +
          (((symplecticForm n *ᵥ f) k : ℝ) : ℂ) • 1) ∧
      (∑ i, ((((symplecticForm n)ᵀ *ᵥ v) i : ℝ) : ℂ) • FockSpace.quadrature i) *
            FockSpace.quadraticHamiltonian K f -
          FockSpace.quadraticHamiltonian K f *
            ∑ i, ((((symplecticForm n)ᵀ *ᵥ v) i : ℝ) : ℂ) • FockSpace.quadrature i =
        (-Complex.I) •
          (∑ i, ((((symplecticForm n)ᵀ *ᵥ ((symplecticForm n * K) *ᵥ v)) i : ℝ) : ℂ) •
            FockSpace.quadrature i + ((f ⬝ᵥ v : ℝ) : ℂ) • 1)) := sorry

/-- Essential self-adjointness and the unitary group: let $K$ be symmetric, let $\bar H$ be the
maximal realization of $H$, and $\bar H \restriction \mathcal D$ its restriction to the finitely
supported vectors. Then $\bar H$ is self-adjoint and is the closure of
$\bar H \restriction \mathcal D$, and $(\bar H \restriction \mathcal D)^* = \bar H$. The operator
$\bar H$ generates exactly one strongly continuous one-parameter unitary group,
$t \mapsto e^{-it\bar H}$. For $\psi \in \mathcal D$ and $2C_H|t| < 1$,
$e^{-it\bar H}\psi = \sum_r (-it)^r \psi_r/r!$, with $C_H$ and the vectors $\psi_r$,
$\jmath\psi_r = H^r\jmath\psi$, of entry 111. -/
theorem quadraticHamiltonian_isSelfAdjoint {n : ℕ}
    {K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hK : Kᵀ = K) (f : Fin n ⊕ Fin n → ℝ) :
    IsSelfAdjoint (FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)) ∧
    ((FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)).domRestrict
        (FockSpace.finiteSupport (Fin n))).closure =
      FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f) ∧
    ((FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)).domRestrict
        (FockSpace.finiteSupport (Fin n))).adjoint =
      FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f) ∧
    (∃! U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
      BosonicLean.IsGenerator (FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)) U) ∧
    ∀ U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
      BosonicLean.IsGenerator (FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)) U →
      ∀ t : ℝ, 2 * (∑ k, ∑ l, |K k l| + Real.sqrt 2 * ∑ k, |f k|) * |t| < 1 →
      ∀ (ψ : FockSpace (Fin n)) (ψs : ℕ → FockSpace (Fin n)), ψ ∈ FockSpace.finiteSupport (Fin n) →
        (∀ r, FockSpace.toFormal (ψs r) =
          (FockSpace.quadraticHamiltonian K f ^ r) (FockSpace.toFormal ψ)) →
        HasSum (fun r : ℕ => ((-(t : ℂ) * Complex.I) ^ r / (r.factorial : ℂ)) • ψs r)
          ((U t : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) ψ) := sorry

/-- Quadratic Hamiltonians generate Gaussian unitaries: let $K$ be symmetric and
$U_t = e^{-it\bar H}$ the group generated by $\bar H$ (entry 113). Let $M(t) = e^{t\Omega K}$ and
$d(t) = \int_0^t M(s)\Omega f\, ds$; these give the flow $x(t) = M(t)x(0) + d(t)$ of the
classical equations of motion $\dot x = \Omega K x + \Omega f$ of the Hamilton function
$\frac12 x^T K x + f^T x$ (a remark that is not part of the statement). For every real $t$,
$U_t$ is a Gaussian unitary with data $(M(t), d(t))$:
$e^{it\bar H} W(u) e^{-it\bar H} = e^{-i\sigma(u, d(t))} W(M(t)^{-1}u)$ for every
$u \in \mathbb R^{2n}$. In particular $e^{-i\bar H}$ has data $(e^{\Omega K}, d(1))$, and by
entry 95 $e^{i\bar H} \hat R e^{-i\bar H} = e^{\Omega K} \hat R + d(1)$ on the vectors in the
domain of every $\bar a_j$, Eq. (3) of Tjoa and Cirac. -/
theorem quadraticHamiltonian_isGaussianUnitary {n : ℕ}
    {K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hK : Kᵀ = K) (f : Fin n ⊕ Fin n → ℝ)
    {U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))}
    (hU : BosonicLean.IsGenerator (FockSpace.maxRealization (FockSpace.quadraticHamiltonian K f)) U)
    (t : ℝ) :
    FockSpace.IsGaussianUnitary (U t) (NormedSpace.exp (t • (symplecticForm n * K)))
      (∫ s in (0 : ℝ)..t,
        NormedSpace.exp (s • (symplecticForm n * K)) *ᵥ (symplecticForm n *ᵥ f)) := sorry

/-- Eqs. (1) and (5) of Tjoa and Cirac. (Definitions) For complex $n \times n$ matrices $h$,
$\Delta$ and $\eta \in \mathbb C^n$, the Hamiltonian of Eq. (1) is the linear map
$H_G = \sum_{i,j} h_{ij} a_i^\dagger a_j + \frac12 \sum_{i,j} (\Delta_{ij} a_i^\dagger a_j^\dagger
+ \bar\Delta_{ij} a_i a_j) + \sum_j (\eta_j a_j^\dagger + \bar\eta_j a_j)$ of the formal Fock space,
and its matrix is $K = \begin{pmatrix} \mathrm{Re}\, h + \mathrm{Re}\, \Delta & \mathrm{Im}\,
\Delta - \mathrm{Im}\, h \\ \mathrm{Im}\, \Delta + \mathrm{Im}\, h & \mathrm{Re}\, h -
\mathrm{Re}\, \Delta \end{pmatrix}$. Let $h$ be Hermitian and $\Delta$ symmetric, and let $H$
be the quadratic Hamiltonian of $K$ and $f = \delta(\eta)$, with
$\delta(\eta) = \sqrt2\, (\mathrm{Re}\, \eta, \mathrm{Im}\, \eta)$ as in entry 93. Then $K$ is
symmetric and $H_G = H - \frac12 \mathrm{tr}\, h$. The maximal realization $\bar H_G$ is
self-adjoint and generates exactly one strongly continuous one-parameter unitary group, and for
every real $\theta$ the operator $e^{i\theta} e^{-i\bar H_G}$ is a Gaussian unitary with data
$(e^{\Omega K}, d(1))$, where $d(1) = \int_0^1 e^{s\Omega K}\Omega f\, ds$. For
$\alpha, \zeta \in \mathbb C^n$, the maximal realizations $A_\alpha$ of
$i \sum_j (\alpha_j a_j^\dagger - \bar\alpha_j a_j)$ and $B_\zeta$ of
$\frac i2 \sum_j (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})$ generate $s \mapsto D(s\alpha)$
and $s \mapsto \mathsf S(s\zeta)$: $D(\alpha) = e^{-iA_\alpha}$ and
$\mathsf S(\zeta) = e^{-iB_\zeta}$, which Eq. (5) writes as
$e^{\alpha \cdot a^\dagger - \bar\alpha \cdot a}$ and
$e^{\frac12 \sum_j (\bar\zeta_j a_j^2 - \zeta_j a_j^{\dagger 2})}$. -/
theorem ladderHamiltonian_isGaussianUnitary {n : ℕ} :
    (∀ (h Δ : Matrix (Fin n) (Fin n) ℂ) (η : Fin n → ℂ),
      FockSpace.ladderHamiltonian h Δ η =
        ∑ i, ∑ j, h i j • (create i * annihilate j : Module.End ℂ (FormalFock (Fin n) ℂ)) +
          (1 / 2 : ℂ) • ∑ i, ∑ j, (Δ i j • (create i * create j) +
            conj (Δ i j) • (annihilate i * annihilate j)) +
          ∑ j, (η j • create j + conj (η j) • annihilate j) ∧
      FockSpace.ladderMatrix h Δ =
        Matrix.fromBlocks (h.map Complex.re + Δ.map Complex.re)
          (Δ.map Complex.im - h.map Complex.im) (Δ.map Complex.im + h.map Complex.im)
          (h.map Complex.re - Δ.map Complex.re)) ∧
    (∀ (h Δ : Matrix (Fin n) (Fin n) ℂ) (η : Fin n → ℂ), h.IsHermitian → Δᵀ = Δ →
      (FockSpace.ladderMatrix h Δ)ᵀ = FockSpace.ladderMatrix h Δ ∧
      FockSpace.ladderHamiltonian h Δ η =
        FockSpace.quadraticHamiltonian (FockSpace.ladderMatrix h Δ)
          (Sum.elim (fun j => Real.sqrt 2 * (η j).re) fun j => Real.sqrt 2 * (η j).im) -
          (Matrix.trace h / 2) • 1 ∧
      IsSelfAdjoint (FockSpace.maxRealization (FockSpace.ladderHamiltonian h Δ η)) ∧
      (∃! U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
        BosonicLean.IsGenerator (FockSpace.maxRealization (FockSpace.ladderHamiltonian h Δ η)) U) ∧
      ∀ U : ℝ → unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)),
        BosonicLean.IsGenerator (FockSpace.maxRealization (FockSpace.ladderHamiltonian h Δ η)) U →
        ∀ (θ : ℝ) (V : unitary (FockSpace (Fin n) →L[ℂ] FockSpace (Fin n))),
          (V : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) =
            Complex.exp (θ * Complex.I) • (U 1 : FockSpace (Fin n) →L[ℂ] FockSpace (Fin n)) →
          FockSpace.IsGaussianUnitary V
            (NormedSpace.exp (symplecticForm n * FockSpace.ladderMatrix h Δ))
            (∫ s in (0 : ℝ)..1,
              NormedSpace.exp (s • (symplecticForm n * FockSpace.ladderMatrix h Δ)) *ᵥ
                (symplecticForm n *ᵥ
                Sum.elim (fun j => Real.sqrt 2 * (η j).re) fun j => Real.sqrt 2 * (η j).im))) ∧
    (∀ α : Fin n → ℂ, BosonicLean.IsGenerator
      (FockSpace.maxRealization (Complex.I • ∑ j, (α j • create j - conj (α j) • annihilate j) :
        Module.End ℂ (FormalFock (Fin n) ℂ)))
      (fun s : ℝ => FockSpace.displacement ((s : ℂ) • α))) ∧
    ∀ ζ : Fin n → ℂ, BosonicLean.IsGenerator
      (FockSpace.maxRealization ((Complex.I / 2) • ∑ j, (conj (ζ j) • annihilate j ^ 2 -
        ζ j • create j ^ 2) : Module.End ℂ (FormalFock (Fin n) ℂ)))
      (fun s : ℝ => FockSpace.squeeze ((s : ℂ) • ζ)) := sorry

end Sealed
