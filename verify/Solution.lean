/-
Copyright (c) 2026 BosonicLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BosonicLean contributors
-/
import BosonicLean

/-!
# Proofs of the core statements of BosonicLean

This file repeats every statement of `Challenge.lean` in this folder with the identical text and
proves it from the theorems of the library. It imports the library, not the challenge. The tool
`lake comparator`, configured by `comparator.json` in this folder, checks the correspondence of
the two files and the axioms used; see the header of `Challenge.lean`.
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
    symplecticForm n = Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [symplecticForm, Matrix.J, Matrix.fromBlocks_neg]
  simp

/-- A real $2n \times 2n$ matrix $\gamma$ is an admissible covariance matrix if and only if it is
symmetric and $\gamma - i\Omega \ge 0$. -/
theorem isAdmissible_iff {n : ℕ} (γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    IsAdmissible γ ↔ γᵀ = γ ∧
      (γ.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal).PosSemidef :=
  Iff.rfl

/-- Symplectic congruence: a real $2n \times 2n$ matrix $S$ is symplectic when
$S \Omega S^T = \Omega$. If $\gamma$ is admissible and $S$ is symplectic, then $S \gamma S^T$ is
admissible. -/
theorem isAdmissible_symplectic_congr {n : ℕ}
    {γ S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hγ : IsAdmissible γ)
    (hS : S * symplecticForm n * Sᵀ = symplecticForm n) : IsAdmissible (S * γ * Sᵀ) :=
  isAdmissible_symplecticCongruence hγ hS

/-- Restriction to a set of modes: if $\gamma$ is admissible on $n$ modes and $e$ is an injective
map from $m$ modes to the $n$ modes, the matrix with entries $\gamma(e(a), e(b))$, positions
going to positions and momenta to momenta, is admissible on $m$ modes. -/
theorem isAdmissible_restrict {m n : ℕ} {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    {e : Fin m → Fin n} (hγ : IsAdmissible γ) (he : Function.Injective e) :
    IsAdmissible (γ.submatrix (Sum.map e e) (Sum.map e e)) :=
  isAdmissible_subsystem hγ he

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
      IsAdmissible A ∧ IsAdmissible B := by
  have h : (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
      (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)) :
        Fin (n + m) ⊕ Fin (n + m) → (Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin m)) = splitPhase := by
    funext x
    rcases x with i | i <;>
      obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i <;>
      rcases i with i | i <;> simp [splitPhase]
  rw [h]
  exact Gaussian.isAdmissible_directSum_iff A B

/-- One mode: the diagonal matrix $\mathrm{diag}(a, b)$ is admissible if and only if $a > 0$ and
$ab \ge 1$. -/
theorem isAdmissible_diagonal_iff (a b : ℝ) :
    IsAdmissible (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))) ↔
      0 < a ∧ 1 ≤ a * b :=
  isAdmissible_diagonalOne_iff a b

/-- Every admissible matrix $\gamma$ is positive definite: $x^T \gamma x > 0$ for every
nonzero real vector $x$. -/
theorem posDef_of_isAdmissible {n : ℕ} {γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hγ : IsAdmissible γ) : γ.PosDef :=
  hγ.posDef

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
        Matrix.diagonal (Sum.elim (fun _ => s ^ 2) (fun _ => ħ ^ 2 / s ^ 2)) := by
  set φ := vacuumSchwartz s hs
  have hφ : (φ : ℝ → ℂ) = ψ := funext fun x => (vacuumSchwartz_apply s hs x).trans (hψ x).symm
  let Ψ : OneModeState := ⟨φ, vacuum_normalized hs _ (vacuumSchwartz_apply s hs)⟩
  have hΨ : IsVacuum s Ψ := vacuumSchwartz_apply s hs
  refine ⟨?_, ?_⟩
  · rw [← hφ]
    exact (integral_norm_vacuumFunction_sq hs ▸ by
      simp_rw [show ∀ x, φ x = vacuumFunction s x from vacuumSchwartz_apply s hs])
  · have hobs : ∀ (j : Fin 1 ⊕ Fin 1) x, oneModeObservable ħ j φ x = A j x := by
      intro j x
      rcases j with j | j <;> obtain rfl := Subsingleton.elim j 0
      · rw [(hA x).1, ← hφ]
        exact oneModePosition_apply φ x
      · rw [(hA x).2, ← hφ]
        simp [oneModeObservable, oneModeMomentum, SchwartzMap.derivCLM_apply]
    have hmean : ∀ j : Fin 1 ⊕ Fin 1,
        oneModeMean Ψ (oneModeObservable ħ j) = (∫ y, conj (ψ y) * A j y).re := by
      intro j
      simp only [oneModeMean, Ψ, oneModeEmbed_inner, ← hφ, ← hobs j, RCLike.inner_apply']
    have hcov := (vacuum_covariance hs hħ Ψ hΨ).1
    rw [diagonalOne] at hcov
    rw [← hcov]
    ext j k
    simp only [Matrix.of_apply, oneModeCovariance, oneModeCentered, ← hmean]
    congr 2
    have hc : ∀ i : Fin 1 ⊕ Fin 1, oneModeEmbed (oneModeObservable ħ i Ψ.function) -
        ((oneModeMean Ψ (oneModeObservable ħ i) : ℝ) : ℂ) • oneModeEmbed Ψ.function =
        oneModeEmbed (oneModeObservable ħ i Ψ.function -
          ((oneModeMean Ψ (oneModeObservable ħ i) : ℝ) : ℂ) • Ψ.function) := by
      intro i
      rw [map_sub, map_smul]
    rw [hc, hc, oneModeEmbed_inner]
    congr 1
    funext x
    simp only [sub_apply, smul_apply, hobs, smul_eq_mul, Ψ, hφ, RCLike.inner_apply']

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
          (W * γ * Wᵀ).submatrix Sum.inl Sum.inr :=
  rfl

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
    ((W * γ * Wᵀ).submatrix Sum.inl Sum.inl).PosDef ∧ IsAdmissible (contractCovariance γ W) :=
  Gaussian.isAdmissible_contractCovariance W hγ hW hΩ

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
      if j = j' then Γ j u v else 0 := by
  rcases u with u | u <;> rcases v with v | v <;>
    simp [periodicInput, MPS.Internal.phaseSiteEquiv, Matrix.blockDiagonal_apply]

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
          Pi.single (Sum.inr (finProdFinEquiv (i, Fin.natAdd (M + M) 0))) 1 := by
  -- copies of the library's index bijections and wiring core, equal to them by `rfl`
  let L : (Fin M ⊕ Fin M) ⊕ Fin 1 ≃ Fin (M + M + 1) :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv
  let colE : (Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1)) ⊕ (Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1)) ≃
      Fin (N * (M + M + 1)) ⊕ Fin (N * (M + M + 1)) :=
    Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin N)) L).trans finProdFinEquiv)
      ((Equiv.prodCongr (Equiv.refl (Fin N)) L).trans finProdFinEquiv)
  let rowE : ((Fin N × Fin M) ⊕ (Fin N × Fin M)) ⊕ (Fin N ⊕ Fin N) ≃
      Fin (N * M + N * M) ⊕ (Fin N ⊕ Fin N) :=
    Equiv.sumCongr ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)
      (Equiv.refl (Fin N ⊕ Fin N))
  let core : Matrix (((Fin N × Fin M) ⊕ (Fin N × Fin M)) ⊕ (Fin N ⊕ Fin N))
      ((Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1)) ⊕ (Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1))) ℝ :=
    fun r c => match r, c with
    | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inl a)) =>
        if ia = (j, a) then 1 else 0
    | Sum.inl (Sum.inl ia), Sum.inl (j, Sum.inl (Sum.inr b)) =>
        if ia = (finRotate N j, b) then 1 else 0
    | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inl a)) =>
        if ia = (j, a) then 1 else 0
    | Sum.inl (Sum.inr ia), Sum.inr (j, Sum.inl (Sum.inr b)) =>
        if ia = (finRotate N j, b) then -1 else 0
    | Sum.inr (Sum.inl i), Sum.inl (j, Sum.inr _) =>
        if i = j then 1 else 0
    | Sum.inr (Sum.inr i), Sum.inr (j, Sum.inr _) =>
        if i = j then 1 else 0
    | _, _ => 0
  have hW : periodicWiring N M = Matrix.reindex rowE colE core := rfl
  have hrow : ∀ (r : ((Fin N × Fin M) ⊕ (Fin N × Fin M)) ⊕ (Fin N ⊕ Fin N)),
      periodicWiring N M (rowE r) = fun c => core r (colE.symm c) := by
    intro r
    funext c
    rw [hW, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hsingle : ∀ (x : (Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1)) ⊕
      (Fin N × ((Fin M ⊕ Fin M) ⊕ Fin 1))) (c : Fin (N * (M + M + 1)) ⊕ Fin (N * (M + M + 1))),
      (Pi.single (colE x) (1 : ℝ) : _ → ℝ) c = if colE.symm c = x then 1 else 0 := by
    intro x c
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  have hLa : ∀ a : Fin M, Fin.castAdd 1 (Fin.castAdd M a) = L (Sum.inl (Sum.inl a)) := by
    intro a
    simp [L]
  have hLb : ∀ a : Fin M, Fin.castAdd 1 (Fin.natAdd M a) = L (Sum.inl (Sum.inr a)) := by
    intro a
    simp [L]
  have hLc : Fin.natAdd (M + M) (0 : Fin 1) = L (Sum.inr 0) := by
    simp [L]
  have hq : ∀ (j : Fin N) (x : (Fin M ⊕ Fin M) ⊕ Fin 1),
      (Sum.inl (finProdFinEquiv (j, L x)) : Fin (N * (M + M + 1)) ⊕ Fin (N * (M + M + 1))) =
        colE (Sum.inl (j, x)) := fun _ _ => rfl
  have hp : ∀ (j : Fin N) (x : (Fin M ⊕ Fin M) ⊕ Fin 1),
      (Sum.inr (finProdFinEquiv (j, L x)) : Fin (N * (M + M + 1)) ⊕ Fin (N * (M + M + 1))) =
        colE (Sum.inr (j, x)) := fun _ _ => rfl
  have hr1 : ∀ (i : Fin N) (a : Fin M),
      (Sum.inl (Fin.castAdd (N * M) (finProdFinEquiv (i, a))) :
        Fin (N * M + N * M) ⊕ (Fin N ⊕ Fin N)) = rowE (Sum.inl (Sum.inl (i, a))) := by
    intro i a
    simp [rowE]
  have hr2 : ∀ (i : Fin N) (a : Fin M),
      (Sum.inl (Fin.natAdd (N * M) (finProdFinEquiv (i, a))) :
        Fin (N * M + N * M) ⊕ (Fin N ⊕ Fin N)) = rowE (Sum.inl (Sum.inr (i, a))) := by
    intro i a
    simp [rowE]
  refine ⟨fun i a => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [hr1, hrow, hLa, hLb, hq, hq]
    funext c
    obtain ⟨c, rfl⟩ := colE.surjective c
    simp only [Pi.add_apply, hsingle, Equiv.symm_apply_apply]
    rcases c with ⟨j, (b | b) | b⟩ | ⟨j, (b | b) | b⟩ <;>
      (try simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Equiv.eq_symm_apply]) <;>
      simp [core, eq_comm, Fin.fin_one_eq_zero]
  · rw [hr2, hrow, hLa, hLb, hp, hp]
    funext c
    obtain ⟨c, rfl⟩ := colE.surjective c
    simp only [Pi.sub_apply, hsingle, Equiv.symm_apply_apply]
    rcases c with ⟨j, (b | b) | b⟩ | ⟨j, (b | b) | b⟩ <;>
      (try simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Equiv.eq_symm_apply]) <;>
      simp [core, eq_comm, neg_ite, Fin.fin_one_eq_zero]
  · rw [show (Sum.inr (Sum.inl i) : Fin (N * M + N * M) ⊕ (Fin N ⊕ Fin N)) =
      rowE (Sum.inr (Sum.inl i)) from rfl, hrow, hLc, hq]
    funext c
    obtain ⟨c, rfl⟩ := colE.surjective c
    simp only [hsingle, Equiv.symm_apply_apply]
    rcases c with ⟨j, (b | b) | b⟩ | ⟨j, (b | b) | b⟩ <;>
      (try simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq]) <;>
      simp [core, eq_comm, Fin.fin_one_eq_zero]
  · rw [show (Sum.inr (Sum.inr i) : Fin (N * M + N * M) ⊕ (Fin N ⊕ Fin N)) =
      rowE (Sum.inr (Sum.inr i)) from rfl, hrow, hLc, hp]
    funext c
    obtain ⟨c, rfl⟩ := colE.surjective c
    simp only [hsingle, Equiv.symm_apply_apply]
    rcases c with ⟨j, (b | b) | b⟩ | ⟨j, (b | b) | b⟩ <;>
      (try simp only [Sum.inr.injEq, Prod.mk.injEq]) <;>
      simp [core, eq_comm, Fin.fin_one_eq_zero]

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
      IsAdmissible (contractCovariance (periodicInput Γ) (periodicWiring N M)) :=
  periodicCovariance_admissible hN hM Γ hΓ

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
    CCR σ = (StarAlgebra.adjoin ℂ (Set.range (weyl σ))).topologicalClosure :=
  ⟨fun _ _ _ => rfl, rfl⟩

/-- For alternating $\sigma$, every Weyl operator is unitary, $W(u)^* = W(-u)$, and the Weyl
relation $W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$ holds. -/
theorem weyl_relations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    (∀ u, weyl σ u ∈ unitary (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)) ∧
    (∀ u, star (weyl σ u) = weyl σ (-u)) ∧
    ∀ u w, weyl σ u * weyl σ w =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • weyl σ (u + w) :=
  ⟨weyl_mem_unitary σ hσ, star_weyl σ hσ, weyl_mul σ hσ⟩

/-- Relabelling: let $\sigma$ and $\sigma'$ be any real bilinear forms on $V$ and $V'$. For a
linear bijection $T : V \to V'$ with $\sigma'(Tu, Tv) = \sigma(u, v)$ there is a $\mathbb C$-linear
star isomorphism $\varphi : \mathrm{CCR}(V, \sigma) \to \mathrm{CCR}(V', \sigma')$ with
$\varphi(W(u)) = W'(Tu)$ for every $u \in V$. -/
theorem exists_starAlgEquiv_relabel {V V' : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] {σ : LinearMap.BilinForm ℝ V}
    {σ' : LinearMap.BilinForm ℝ V'} (T : V ≃ₗ[ℝ] V') (hT : ∀ u v, σ' (T u) (T v) = σ u v) :
    ∃ φ : CCR σ ≃⋆ₐ[ℂ] CCR σ', ∀ (u : V) (a : CCR σ),
      (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
        (φ a : lp (fun _ : V' => ℂ) 2 →L[ℂ] lp (fun _ : V' => ℂ) 2) = weyl σ' (T u) := by
  refine ⟨CCR.relabel hT, fun u a ha => ?_⟩
  rw [CCR.coe_relabel_apply, ha]
  exact conj_relabel_weyl hT u

/-- Simplicity: for alternating nondegenerate $\sigma$, the CCR algebra is a simple ring: its
only two-sided ideals are $0$ and the whole algebra, and these differ. -/
theorem isSimpleRing_CCR {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.Nondegenerate) :
    IsSimpleRing (CCR σ) :=
  CCR.isSimpleRing hσ hnd.1

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
      (∀ u w, c (u + w) = c u * c w) ∧ ∀ u, ‖c u‖ = 1 :=
  weyl_automorphism_of_nondegenerate hσ hnd T Γ c fun u => h u _ rfl

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
    ω = ω' :=
  clm_ext_weyl hσ fun u => h u _ rfl

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
    (∀ u, 0 ≤ γ u u) ∧ ∀ u w, σ u w ^ 2 ≤ γ u u * γ w w := by
  let G : GaussianState σ :=
    { toCLM := ω
      map_one := h1
      nonneg := hpos
      cov := γ
      isSymm := hγ
      disp := d
      charFun_eq := fun u => hω u _ rfl }
  have hC : IsStateConditionC γ σ := G.isStateConditionC hσ
  exact ⟨hC, (isStateConditionC_iff hγ hσ).1 hC⟩

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
            weyl σ ((L₂ ∘ₗ L₁) u) := by
  have cond : ∀ (L : V →ₗ[ℝ] V) (ν : LinearMap.BilinForm ℝ V),
      (∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => (ν (u j) (u k) : ℂ) +
        Complex.I * ((σ (u j) (u k) - σ (L (u j)) (L (u k)) : ℝ) : ℂ)).PosSemidef) ↔
      IsStateConditionC ν (σ - σ.comp L L) := by
    intro L ν
    refine forall_congr' fun m => forall_congr' fun u => ?_
    simp only [LinearMap.sub_apply, LinearMap.BilinForm.comp_apply]
  let T₁ : GaussianChannel σ :=
    { lin := L₁, noise := ν₁, noise_isSymm := hν₁, disp := μ₁, cond := (cond L₁ ν₁).1 hc₁,
      map := f₁, map_weyl := fun u => Subtype.ext (hf₁ u _ rfl) }
  let T₂ : GaussianChannel σ :=
    { lin := L₂, noise := ν₂, noise_isSymm := hν₂, disp := μ₂, cond := (cond L₂ ν₂).1 hc₂,
      map := f₂, map_weyl := fun u => Subtype.ext (hf₂ u _ rfl) }
  let T := GaussianChannel.comp T₂ T₁
  refine ⟨⟨T.map, fun a => rfl⟩, T.noise_isSymm, (cond _ _).2 T.cond, fun u a ha => ?_⟩
  have hT := congrArg Subtype.val (T.map_weyl u)
  have hau : a = wCCR σ u := Subtype.ext ha
  subst hau
  exact hT

/-- Channel matrices: for $n$ modes, let $X$ and $Y$ be real $2n \times 2n$ matrices with $Y$
symmetric and $Y - i\Omega + iX\Omega X^T \ge 0$. Then $X \gamma X^T + Y$ is admissible for every
admissible $\gamma$. -/
theorem isAdmissible_channel {n : ℕ} {X Y γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hY : Yᵀ = Y)
    (hXY : (Y.map Complex.ofReal - Complex.I • (symplecticForm n).map Complex.ofReal +
      Complex.I • (X * symplecticForm n * Xᵀ).map Complex.ofReal).PosSemidef)
    (hγ : IsAdmissible γ) : IsAdmissible (X * γ * Xᵀ + Y) :=
  Gaussian.isAdmissible_channel ⟨hY, hXY⟩ hγ

/-! ## The formal Fock space

The modes form a type $\iota$, an occupation-number configuration is a finitely supported
$n : \iota \to \mathbb N$ (finitely supported), with $|n| = \sum_i n_i$ and
$n! = \prod_i n_i!$, and $e_i$ is the configuration with one particle in mode $i$. The
coefficients lie in a complex vector space $R$, which for the Bargmann map and in entry 34 is a
ring and a complex algebra. A raising operator is a complex-linear map $T$ of the formal Fock
space that raises the degree of vanishing: if $\psi(n) = 0$ for all $|n| < k$, then
$(T\psi)(n) = 0$ for all $|n| < k + 1$. Entry 25 characterizes these maps and defines their
exponential. -/

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
        ((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) • ψ.coeff (n + Finsupp.single i 1) := by
  let e : FormalFock ι R ≃ₗ[ℂ] ((ι →₀ ℕ) → R) :=
    { toFun := FormalFock.coeff
      invFun := FormalFock.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨⟨e, fun _ => rfl⟩, fun i ψ n => ⟨rfl, ?_⟩⟩
  rw [coeff_annihilate, sqrtC]
  push_cast
  rfl

/-- The canonical commutation relations on the whole formal Fock space:
$[a_i, a_j^\dagger] = \delta_{ij}$, $[a_i, a_j] = 0$ and $[a_i^\dagger, a_j^\dagger] = 0$. -/
theorem ccr_ladder {ι R : Type*} [AddCommGroup R] [Module ℂ R] [DecidableEq ι] (i j : ι) :
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ =
        (if i = j then 1 else 0) ∧
    ⁅(annihilate (R := R) i : Module.End ℂ (FormalFock ι R)), annihilate (R := R) j⁆ = 0 ∧
    ⁅(create (R := R) i : Module.End ℂ (FormalFock ι R)), create (R := R) j⁆ = 0 :=
  ⟨lie_annihilate_create i j, lie_annihilate_annihilate i j, lie_create_create i j⟩

/-- Raising operators and their exponential: a linear map $T$ of the formal Fock space is a
raising operator if and only if, whenever
$\psi(n) = 0$ for all $|n| < k$, also $(T\psi)(n) = 0$ for all $|n| < k + 1$. For a raising
operator $T$ the exponential is $(e^T \psi)(n) = \sum_{k=0}^{|n|} (T^k \psi)(n) / k!$, a finite
sum. -/
theorem raisingOp_and_raisingExp {ι R : Type*} [AddCommGroup R] [Module ℂ R] :
    (∀ T : Module.End ℂ (FormalFock ι R), (∃ S : RaisingOp ι R, S.op = T) ↔
      ∀ (k : ℕ) (ψ : FormalFock ι R), (∀ n : ι →₀ ℕ, n.degree < k → ψ.coeff n = 0) →
        ∀ n : ι →₀ ℕ, n.degree < k + 1 → (T ψ).coeff n = 0) ∧
    ∀ (T : RaisingOp ι R) (ψ : FormalFock ι R) (n : ι →₀ ℕ),
      (raisingExp T ψ).coeff n =
        ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : ℂ)⁻¹) • ((T.op ^ k) ψ).coeff n :=
  ⟨fun T => ⟨fun ⟨S, hS⟩ => hS ▸ S.isRaising, fun h => ⟨⟨T, h⟩, rfl⟩⟩, fun _ _ _ => rfl⟩

/-- The exponential law: for raising operators $S$ and $T$ whose underlying maps commute, the
raising operator $S + T$ has as underlying map the sum of theirs, and $e^{S+T} = e^S e^T$. -/
theorem raisingExp_add {ι R : Type*} [AddCommGroup R] [Module ℂ R] (S T : RaisingOp ι R)
    (hST : Commute S.op T.op) :
    (S + T).op = S.op + T.op ∧ raisingExp (S + T) = raisingExp S * raisingExp T :=
  ⟨rfl, FormalFock.raisingExp_add S T hST⟩

/-- The Bargmann map $\mathfrak B$ sends $\psi$ to the formal power series
$\sum_n \psi(n)\, z^n / \sqrt{n!}$; it is, by its type, a complex-linear bijection onto all formal
power series in variables $z_i$ ($i \in \iota$) with coefficients in $R$. -/
theorem coeff_toBargmann {ι R : Type*} [Ring R] [Algebra ℂ R] (ψ : FormalFock ι R)
    (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (toBargmann ψ) =
      ((Real.sqrt ((n.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • ψ.coeff n :=
  rfl

/-- The Bargmann map turns $a_j^\dagger$ into multiplication by $z_j$ and $a_j$ into the partial
derivative $\partial_j = \partial / \partial z_j$ defined
on coefficients by $(\partial_j f)_n = (n_j + 1)\, f_{n + e_j}$. -/
theorem toBargmann_ladder {ι R : Type*} [Ring R] [Algebra ℂ R] (j : ι) (ψ : FormalFock ι R) :
    toBargmann (create j ψ) = MvPowerSeries.X j * toBargmann ψ ∧
      toBargmann (annihilate j ψ) = MvPowerSeries.pderivFun j (toBargmann ψ) :=
  ⟨toBargmann_create j ψ, toBargmann_annihilate j ψ⟩

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
      (fun _ : Fin 1 => (1 / 2 : ℝ)))) := by
  have hinj : ∀ k l : ℕ, Function.Injective
      (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
        (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)) :
          Fin (k + l) ⊕ Fin (k + l) → (Fin k ⊕ Fin k) ⊕ (Fin l ⊕ Fin l)) := by
    intro k l x y h
    rcases x with x | x <;> rcases y with y | y <;>
      obtain ⟨x, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).surjective x <;>
      obtain ⟨y, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).surjective y <;>
      rcases x with x | x <;> rcases y with y | y <;> simp_all
  have hone : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) =
      Matrix.diagonal (Sum.elim (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext x
    rcases x with x | x <;> rfl
  refine ⟨fun n => ?_, fun r hr => (isAdmissible_diagonal_iff r r⁻¹).2 ⟨hr, by
    rw [mul_inv_cancel₀ hr.ne']⟩, fun h => ?_⟩
  · induction n with
    | zero =>
      refine ⟨by simp, ?_⟩
      have hzero : (1 : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℝ).map Complex.ofReal -
          Complex.I • (symplecticForm 0).map Complex.ofReal = 0 := Subsingleton.elim _ _
      rw [hzero]
      exact Matrix.PosSemidef.zero
    | succ n ih =>
      have h1 : IsAdmissible (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) := by
        rw [hone, isAdmissible_diagonal_iff]
        norm_num
      have h := (isAdmissible_directSum_iff (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
        (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)).2 ⟨ih, h1⟩
      rwa [Matrix.fromBlocks_one, Matrix.submatrix_one _ (hinj n 1)] at h
  · have h' := (isAdmissible_diagonal_iff (1 / 2) (1 / 2)).1 h
    norm_num at h'

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
          Complex.ofReal).PosSemidef := by
  have hv := (witness_admissible.1 n).2
  have hsq : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt h0
  refine ⟨by rw [Matrix.transpose_smul, Matrix.transpose_one], ?_⟩
  have key : ((1 - η) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).map Complex.ofReal -
      Complex.I • (symplecticForm n).map Complex.ofReal +
      Complex.I • ((Real.sqrt η • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) *
        symplecticForm n * (Real.sqrt η • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))ᵀ).map
          Complex.ofReal =
      (1 - η) • ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ).map Complex.ofReal -
        Complex.I • (symplecticForm n).map Complex.ofReal) := by
    rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hsq]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hv.smul (by linarith)

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
        (periodicWiring 3 1)) := by
  have h := threeSite_covariance
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- On $V = \mathbb R^2$ the form $\sigma(u, w) = u_1 w_2 - u_2 w_1$ is alternating and
nondegenerate, so the simplicity statement applies to it, and its CCR algebra is not the zero
algebra. -/
theorem witness_nondegenerate_plane :
    (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0]).IsAlt ∧
    (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0]).Nondegenerate ∧
    Nontrivial (CCR (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0])) := by
  refine ⟨fun x => ?_,
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ ?_, inferInstance⟩
  · simp [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.det_fin_two_of]

/-- The vacuum data satisfy the state condition: on $V = \mathbb R^2$ with
$\sigma(u, w) = u_1 w_2 - u_2 w_1$, the form $\gamma(u, w) = u_1 w_1 + u_2 w_2$ is symmetric and
$\gamma + i\sigma \ge 0$ on every finite family of vectors. -/
theorem witness_vacuum_state_condition :
    (Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm ∧
    ∀ (m : ℕ) (u : Fin m → Fin 2 → ℝ),
      (Matrix.of fun j k => (Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℝ) (u j) (u k) : ℂ) +
        Complex.I * (Matrix.toBilin' !![(0 : ℝ), 1; -1, 0] (u j) (u k) : ℂ)).PosSemidef := by
  have hγ : (Matrix.toBilin' (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  refine ⟨hγ, (isStateConditionC_iff hγ witness_nondegenerate_plane.1).2
    ⟨fun x => ?_, fun x y => ?_⟩⟩
  · simp [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  · simp [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 * y 0 + x 1 * y 1)]

/-- The creation operator $a_j^\dagger$ is a raising operator. -/
theorem witness_create_raising {ι R : Type*} [Ring R] [Algebra ℂ R] (j : ι) :
    ∃ S : RaisingOp ι R, S.op = create j :=
  ⟨⟨create j, isRaising_create j⟩, rfl⟩

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
                weyl σ ((LinearMap.id : V →ₗ[ℝ] V) u) := by
  refine ⟨⟨fun _ _ => rfl⟩, fun m u => ?_, ⟨BosonicLean.CStar.cpId, fun _ => rfl, fun u a ha => ?_⟩⟩
  · have h0 : (Matrix.of fun j k => ((0 : LinearMap.BilinForm ℝ V) (u j) (u k) : ℂ) +
        Complex.I * ((σ (u j) (u k) - σ ((LinearMap.id : V →ₗ[ℝ] V) (u j))
          ((LinearMap.id : V →ₗ[ℝ] V) (u k)) : ℝ) : ℂ)) = 0 := by
      ext j k
      simp
    rw [h0]
    exact Matrix.PosSemidef.zero
  · simp [ha]

/-- The identity automorphism: let $\sigma$ be any real bilinear form on $V$. The identity
$\mathbb C$-linear star automorphism $T$ of $\mathrm{CCR}(V, \sigma)$, with $\Gamma = \mathrm{id}$
and $c = 1$, satisfies $T(W(u)) = c(u)\, W(\Gamma u)$ for every $u$. Together with
entry 32 it gives an instance of the hypotheses of entry 18. -/
theorem witness_identity_automorphism {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    ∀ (u : V) (a : CCR σ), (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u →
        (StarAlgEquiv.refl ℂ (CCR σ) a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
          (1 : V → ℂ) u • weyl σ (id u) := by
  intro u a ha
  simp [ha]

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
      ‖SchwartzMap.toLpCLM ℂ ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) φ‖ = 1 := by
  refine ⟨⟨vacuumSchwartz s hs, fun x => (vacuumSchwartz_apply s hs x).trans (hψ x).symm,
    fun φ hφ => SchwartzMap.ext fun x =>
      (hφ x).trans ((hψ x).trans (vacuumSchwartz_apply s hs x).symm)⟩, fun φ hφ => ?_⟩
  exact vacuum_normalized hs φ fun x => (hφ x).trans (hψ x)

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
    ∫ x, conj (x * ψ x) * (-Complex.I * ħ * deriv ψ x) = Complex.I * ħ / 2 := by
  set φ := vacuumSchwartz s hs
  have hφ : (φ : ℝ → ℂ) = ψ := funext fun x => (vacuumSchwartz_apply s hs x).trans (hψ x).symm
  let Ψ : OneModeState := ⟨φ, vacuum_normalized hs _ (vacuumSchwartz_apply s hs)⟩
  have hΨ : IsVacuum s Ψ := vacuumSchwartz_apply s hs
  obtain ⟨hact, -, -, hx2, hp2, hxp⟩ := vacuum_action_moments hs hħ Ψ hΨ
  have hx0 := vacuum_position_inner Ψ hΨ
  have hQ : ∀ x, oneModePosition φ x = (x : ℂ) * ψ x := fun x => by
    rw [oneModePosition_apply, hφ]
  have hP : ∀ x, oneModeMomentum ħ φ x = -Complex.I * ħ * deriv ψ x := fun x => by
    rw [oneModeMomentum_apply, hφ]
  have hp0 : inner ℂ (oneModeEmbed φ) (oneModeEmbed (oneModeMomentum ħ φ)) = 0 := by
    change inner ℂ (oneModeEmbed Ψ.function) (oneModeEmbed (oneModeMomentum ħ Ψ.function)) = 0
    rw [hact, map_smul, inner_smul_right, hx0, mul_zero]
  have hint : ∀ f g : SchwartzMap ℝ ℂ, inner ℂ (oneModeEmbed f) (oneModeEmbed g) =
      ∫ x, conj (f x) * g x := fun f g => by
    rw [oneModeEmbed_inner]
    congr 1
    funext x
    rw [RCLike.inner_apply]
    try ring
  refine ⟨⟨oneModePosition φ, oneModeMomentum ħ φ, fun x => ⟨hQ x, hP x⟩⟩, fun x => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun F : SchwartzMap ℝ ℂ => F x) hact
    simp only [smul_apply, smul_eq_mul] at h
    change oneModeMomentum ħ φ x = _ * oneModePosition φ x at h
    rw [hP, hQ] at h
    rw [h]
  · have h : inner ℂ (oneModeEmbed φ) (oneModeEmbed (oneModePosition φ)) = 0 := hx0
    rw [hint] at h
    simpa only [hQ, hφ] using h
  · rw [hint] at hp0
    simpa only [hP, hφ] using hp0
  · have h : ‖oneModeEmbed (oneModePosition φ)‖ ^ 2 = s ^ 2 / 2 := hx2
    rw [oneModeEmbed_norm_sq] at h
    simpa only [hQ] using h
  · have h : ‖oneModeEmbed (oneModeMomentum ħ φ)‖ ^ 2 = ħ ^ 2 / (2 * s ^ 2) := hp2
    rw [oneModeEmbed_norm_sq] at h
    simpa only [hP] using h
  · have h : inner ℂ (oneModeEmbed (oneModePosition φ)) (oneModeEmbed (oneModeMomentum ħ φ)) =
        Complex.I * ħ / 2 := hxp
    rw [hint] at h
    simpa only [hP, hQ] using h

/-- Dimensionless units: for $s > 0$ and $\hbar > 0$ let $D = \mathrm{diag}(1/s, s/\hbar)$, the
rescaling $q \mapsto q/s$, $p \mapsto sp/\hbar$ of position and momentum. Then
$D\, \mathrm{diag}(s^2, \hbar^2/s^2)\, D^T = 1$: in these units the covariance of entry 8 is the
vacuum covariance $1$. -/
theorem gaussian_dimensionless {s ħ : ℝ} (hs : 0 < s) (hħ : 0 < ħ) :
    Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s⁻¹) (fun _ : Fin 1 => s / ħ)) *
        Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s ^ 2) (fun _ : Fin 1 => ħ ^ 2 / s ^ 2)) *
        (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => s⁻¹) (fun _ : Fin 1 => s / ħ)))ᵀ =
      1 := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp <;> field_simp

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
      Matrix.diagonal (Sum.elim (fun _ => ħ / (m * ω)) (fun _ => ħ * m * ω)) := by
  have hr : 0 < ħ / (m * ω) := div_pos hħ (mul_pos hm hω)
  rw [(gaussian_wave_function (Real.sqrt_pos.2 hr) hħ ψ hψ A hA).2, Real.sq_sqrt hr.le]
  congr 2
  funext _
  field_simp

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
              (fun _ : Fin 1 => Fin.natAdd (M + M) 0))) := by
  have hS : MPS.Fourier.symbolWiring (M := M) k =
      Matrix.of fun a => Sum.elim ((1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ) a)
        ((Complex.exp (-2 * Real.pi * Complex.I * (k : ℕ) / N) •
          Matrix.diagonal (Sum.elim (fun _ : Fin M => (1 : ℂ)) (fun _ => -1))) a) := by
    ext a b
    rcases b with b | b
    · simp [MPS.Fourier.symbolWiring, Matrix.one_apply]
    · rcases a with a | a <;> rcases b with b | b <;>
        simp [MPS.Fourier.symbolWiring, MPS.Fourier.predecessorPhase, MPS.Fourier.twistSign,
          Matrix.diagonal_apply, eq_comm]
  have hV : MPS.Fourier.localV M =
      Sum.elim (Sum.map (fun a => Fin.castAdd 1 (Fin.castAdd M a))
          (fun a => Fin.castAdd 1 (Fin.castAdd M a)))
        (Sum.map (fun a => Fin.castAdd 1 (Fin.natAdd M a))
          (fun a => Fin.castAdd 1 (Fin.natAdd M a))) := by
    funext x
    rcases x with (a | a) | (a | a) <;> rfl
  have hC : MPS.Fourier.localC M =
      Sum.map (fun _ : Fin 1 => Fin.natAdd (M + M) 0) (fun _ : Fin 1 => Fin.natAdd (M + M) 0) := by
    funext x
    rcases x with a | a <;> rfl
  refine ⟨?_, ?_⟩
  · rw [MPS.Fourier.eliminatedSymbol, MPS.Fourier.virtualBlock, hS, hV]
  · rw [MPS.Fourier.covarianceSymbol, MPS.Fourier.crossSymbol, MPS.Fourier.crossBlock,
      MPS.Fourier.physicalBlock, hS, hV, hC]

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
        if k = l then MPS.Fourier.covarianceSymbol Γ k a b else 0 := by
  have hphys : ∀ (a : Fin 1 ⊕ Fin 1) (i : Fin N),
      (Sum.map (fun _ => i) (fun _ => i) a : Fin N ⊕ Fin N) = MPS.Fourier.physical a i := by
    intro a i
    rcases a with a | a <;> rfl
  obtain ⟨h1, h2, h3⟩ := homogeneousPeriodicCovariance_fourier N M hN hM Γ hΓ
  refine ⟨fun a b i j => ?_, h2, fun k l a b => ?_⟩
  · simp only [hphys]
    exact h1 a b i j
  · rw [← h3 k l a b, MPS.Fourier.fourierEntry]
    simp only [hphys, MPS.Fourier.character, MPS.Fourier.outputCovariance, Complex.star_def]

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
      MPS.Fourier.covarianceSymbol Γ l = (MPS.Fourier.covarianceSymbol Γ k).map conj := by
  have hphys : ∀ (a : Fin 1 ⊕ Fin 1) (i : Fin N),
      (Sum.map (fun _ => i) (fun _ => i) a : Fin N ⊕ Fin N) = MPS.Fourier.physical a i := by
    intro a i
    rcases a with a | a <;> rfl
  obtain ⟨h1, h2, h3⟩ := homogeneousPeriodicCovariance_reconstruct N M hN hM Γ hΓ
  refine ⟨fun a b i j => ?_, h2, fun k l hkl => h3 k l hkl⟩
  have h := h1 a b i j
  rw [MPS.Fourier.outputCovariance] at h
  rw [hphys, hphys, h]
  simp only [MPS.Fourier.character, Complex.star_def]

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
        if i = j then η i a b else 0 := by
  have h : (Sum.elim (fun i => Sum.map Sum.inl Sum.inl (finSumFinEquiv.symm i))
      (fun i => Sum.map Sum.inr Sum.inr (finSumFinEquiv.symm i)) :
        Fin (M + M + 1) ⊕ Fin (M + M + 1) → (Fin (M + M) ⊕ Fin (M + M)) ⊕ (Fin 1 ⊕ Fin 1)) =
      splitPhase := by
    funext x
    rcases x with i | i <;>
      obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin (M + M) ⊕ Fin 1 ≃ Fin (M + M + 1)).surjective i <;>
      rcases i with i | i <;> simp [splitPhase]
  refine ⟨by rw [h]; rfl, fun i j a b => ?_⟩
  rcases a with a | a <;> rcases b with b | b <;>
    obtain rfl := Subsingleton.elim a 0 <;> obtain rfl := Subsingleton.elim b 0 <;> rfl

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
    IsAdmissible (productCovariance η) :=
  periodicProduct_covariance hN hM η hη

/-- The covariance of a Gaussian kernel: for a complex $n \times n$ matrix $K$ with real part
$X$ and imaginary part $-Y$, so that $K = X - iY$, the kernel covariance is the real
$2n \times 2n$ matrix $\begin{pmatrix} X^{-1} & X^{-1}Y \\ YX^{-1} & X + YX^{-1}Y \end{pmatrix}$
in the blocks of positions and momenta, with $X^{-1}$ the matrix inverse. -/
theorem kernelCovariance_eq {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) :
    kernelCovariance K =
      Matrix.fromBlocks (K.map Complex.re)⁻¹ ((K.map Complex.re)⁻¹ * -(K.map Complex.im))
        (-(K.map Complex.im) * (K.map Complex.re)⁻¹)
        (K.map Complex.re + -(K.map Complex.im) * (K.map Complex.re)⁻¹ *
          -(K.map Complex.im)) :=
  rfl

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
            2 * (gi : ℂ) ^ 2 * (((t / (4 * (1 + g ^ 2)) : ℝ) : ℂ) + Complex.I)] :=
  rfl

/-- Gaussian kernels give admissible covariances: if the complex $n \times n$ matrix $K$ is
symmetric, $K^T = K$, and its real part $X$ is positive definite ($x^T X x > 0$ for every nonzero
real vector $x$, $X$ symmetric), then the kernel covariance of $K$ is admissible. -/
theorem isAdmissible_kernelCovariance {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (hK : Kᵀ = K)
    (hX : (K.map Complex.re).PosDef) : IsAdmissible (kernelCovariance K) :=
  kernelCovariance_admissible K hK hX

/-- Finitely squeezed cluster chains: for $t > 0$ and $g_i \in \{0, g\}$ the local resource of
entry 47 is admissible on three modes. -/
theorem isAdmissible_clusterLocalResource (t g gi : ℝ) (ht : 0 < t) (hgi : gi = 0 ∨ gi = g) :
    IsAdmissible (clusterLocalResource t g gi) :=
  clusterLocalResource_admissible t g gi ht hgi

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
    ∀ u w, σ u w = 0 → Commute (W u) (W w) := by
  let S : WeylSystem σ A := ⟨W, hu, hW, hgen⟩
  exact ⟨S.map_zero, S.star_eq hσ, S.mul_comm_phase hσ, fun u w h => S.commute_of_eq_zero hσ h⟩

/-- The CCR algebra is a Weyl system: for alternating $\sigma$ the Weyl operators $W(u)$, as
elements of $\mathrm{CCR}(V, \sigma)$, form a Weyl system for $(V, \sigma)$ in
$\mathrm{CCR}(V, \sigma)$. -/
theorem weylSystem_CCR {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    ∃ W : V → CCR σ, (∀ u, (W u : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
        weyl σ u) ∧
      (∀ u, W u ∈ unitary (CCR σ)) ∧
      (∀ u w, W u * W w = Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • W (u + w)) ∧
      (StarAlgebra.adjoin ℂ (Set.range W)).topologicalClosure = ⊤ :=
  ⟨(CCR.weylSystem σ hσ).W, fun _ => rfl, (CCR.weylSystem σ hσ).mem_unitary,
    (CCR.weylSystem σ hσ).mul_eq, (CCR.weylSystem σ hσ).generating⟩

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
      (StarAlgebra.adjoin ℂ (Set.range fun u => W (T u))).topologicalClosure = ⊤) := by
  let S : WeylSystem σ₀ A := ⟨W, hu, hW, hgen⟩
  exact ⟨fun u => hu (T u), S.pullback_mul_eq hT, fun hs => (S.pullback T hT hs).generating⟩

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
      (BosonicLean.Weyl.relabel T).conjStarAlgEquiv a :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

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
      (CCR.relabel h₁).trans (CCR.relabel h₂) := by
  refine ⟨fun u a ha => ?_, CCR.relabel_refl, CCR.relabel_trans h₁ h₂⟩
  rw [CCR.coe_relabel_apply, ha]
  exact conj_relabel_weyl h₁ u

/-- Injectivity of representations: let $\sigma$ be alternating and nondegenerate. Every
representation of $\mathrm{CCR}(V, \sigma)$ on a nonzero complex Hilbert space is injective. -/
theorem injective_representation {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (hnd : σ.Nondegenerate) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (π : CCR σ →⋆ₐ[ℂ] (H →L[ℂ] H)) : Function.Injective π :=
  haveI := CCR.isSimpleRing hσ hnd.1
  BosonicLean.injective_of_isSimpleRing π

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
      Complex.exp (Complex.I * (σ (u j) (u k) : ℂ) / 2) * χ (u k - u j)).PosSemidef := by
  let S : State σ := ⟨ω, h1, hpos⟩
  have hS : S.charFun = χ := funext fun v => hχ v _ rfl
  have := S.twistedKernel_posSemidef hσ u
  rwa [hS] at this

/-- The norm bound: let $\sigma$ be any real bilinear form on $V$ and $\omega$ a state on
$\mathrm{CCR}(V, \sigma)$. Then $|\omega(a)| \le \|a\|$ for every $a$. -/
theorem norm_state_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (ω : CCR σ →L[ℂ] ℂ) (h1 : ω 1 = 1)
    (hpos : ∀ a, 0 ≤ ω (star a * a)) (a : CCR σ) : ‖ω a‖ ≤ ‖a‖ :=
  norm_apply_le_of_nonneg_star_mul_self ω h1 hpos a

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
      (∀ u, 0 ≤ γ u u) ∧ ∀ u w, σ u w ^ 2 ≤ γ u u * γ w w) :=
  ⟨isStateConditionC_iff_pair hγ hσ, isStateConditionPair_iff⟩

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
          Complex.I * ((σ u w : ℂ) - (σ (L u) (L w) : ℂ))) / 2) • (f a * f b) := by
  have cond : IsStateConditionC ν (σ - σ.comp L L) := by
    intro m u
    simpa only [LinearMap.sub_apply, LinearMap.BilinForm.comp_apply] using hc m u
  let T : GaussianChannel σ :=
    { lin := L, noise := ν, noise_isSymm := hν, disp := μ, cond := cond,
      map := f, map_weyl := fun u => Subtype.ext (hf u _ rfl) }
  intro u w a b ha hb
  have hau : a = wCCR σ u := Subtype.ext ha
  have hbw : b = wCCR σ w := Subtype.ext hb
  subst hau hbw
  exact T.map_weyl_mul hσ u w

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
            ((γ.comp L L + ν) u u : ℂ) / 4) := by
  have cond : IsStateConditionC ν (σ - σ.comp L L) := by
    intro m u
    simpa only [LinearMap.sub_apply, LinearMap.BilinForm.comp_apply] using hc m u
  let T : GaussianChannel σ :=
    { lin := L, noise := ν, noise_isSymm := hν, disp := μ, cond := cond,
      map := f, map_weyl := fun u => Subtype.ext (hf u _ rfl) }
  let G : GaussianState σ :=
    { toCLM := ω, map_one := h1, nonneg := hpos, cov := γ, isSymm := hγ, disp := d,
      charFun_eq := fun u => hω u _ rfl }
  let G' := T.stateMap G
  refine ⟨G'.toCLM, fun a => rfl, G'.map_one, G'.nonneg, G'.isSymm, fun u a ha => ?_⟩
  have hau : a = wCCR σ u := Subtype.ext ha
  subst hau
  exact G'.charFun_eq u

/-- No noise: let $\sigma$ be alternating and $L : V \to V$ a linear map such that the data
$(L, 0)$ satisfy the channel condition, that is, the complex matrix
$(i\sigma(u_j, u_k) - i\sigma(Lu_j, Lu_k))_{jk}$ is positive semidefinite for every finite
family $u_1, \dots, u_m$. Then $L$ preserves $\sigma$: $\sigma(Lu, Lw) = \sigma(u, w)$. -/
theorem noiseless_preserves {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) (L : V →ₗ[ℝ] V)
    (hc : ∀ (m : ℕ) (u : Fin m → V), (Matrix.of fun j k => ((0 : LinearMap.BilinForm ℝ V)
      (u j) (u k) : ℂ) + Complex.I * ((σ (u j) (u k) - σ (L (u j)) (L (u k)) : ℝ) :
        ℂ)).PosSemidef) :
    ∀ u w, σ (L u) (L w) = σ u w := by
  apply preserves_of_noise_eq_zero hσ
  intro m u
  simpa only [LinearMap.sub_apply, LinearMap.BilinForm.comp_apply] using hc m u

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
      ∀ a, f a = CCR.relabel hL a := by
  refine ⟨⟨(GaussianChannel.ofRelabel σ hL).map, fun a => rfl⟩, fun f hf => ?_⟩
  have h0 : IsStateConditionC 0 (σ - σ.comp L.toLinearMap L.toLinearMap) :=
    (GaussianChannel.ofRelabel σ hL).cond
  let T : GaussianChannel σ :=
    { lin := L.toLinearMap, noise := 0, noise_isSymm := ⟨fun _ _ => rfl⟩, disp := 0, cond := h0,
      map := f, map_weyl := fun u => by
        apply Subtype.ext
        rw [hf u _ rfl]
        simp [wCCR] }
  have := GaussianChannel.map_eq_ofRelabel hσ T rfl rfl hL rfl
  intro a
  exact congrArg (fun g : CCR σ →CP CCR σ => g a) this

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
          (LinearMap.snd ℝ V V' ∘ₗ S ∘ₗ LinearMap.inl ℝ V V') := by
  have hS' : ∀ x y, sumForm σ σ' (S x) (S y) = sumForm σ σ' x y := hS
  refine ⟨dilation_preserves S hS', fun hγ' m u => ?_, dilation_cov S γ γ'⟩
  have := dilation_isStateConditionC S hS' (γ' := γ') hγ' m u
  simpa only [LinearMap.sub_apply, LinearMap.BilinForm.comp_apply, dilA_apply, dilC_apply]
    using this

/-- Closed star subalgebras are star-ordered: let $\mathcal A$ be a unital C*-algebra with a
partial order for which it is star-ordered, and $\mathcal S$ a norm-closed unital star subalgebra
of $\mathcal A$ with the order inherited from $\mathcal A$. Then an element $x$ of $\mathcal S$
satisfies $x \ge 0$ if and only if $x = s^* s$ for some $s \in \mathcal S$, and $\mathcal S$ is
star-ordered. -/
theorem starOrdered_of_isClosed {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A)) :
    (∀ x : S, (0 : A) ≤ x ↔ ∃ s : S, (x : A) = star (s : A) * s) ∧ StarOrderedRing S := by
  have := hS
  refine ⟨fun x => ?_, inferInstance⟩
  have := BosonicLean.StarSubalgebra.nonneg_iff_exists_star_mul_self S x
  rw [← Subtype.coe_le_coe] at this
  simpa [Subtype.ext_iff] using this

/-- Completely positive maps compose: let $\mathcal A$, $\mathcal B$, $\mathcal C$ be unital
C*-algebras, each with a partial order for which it is star-ordered, and
$f : \mathcal A \to \mathcal B$ and $g : \mathcal B \to \mathcal C$ completely positive maps. Then
$a \mapsto g(f(a))$ is completely positive, and so is the identity of $\mathcal A$. -/
theorem cp_comp {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] (f : A →CP B) (g : B →CP C) :
    (∃ h : A →CP C, ∀ x, h x = g (f x)) ∧ ∃ i : A →CP A, ∀ x, i x = x :=
  ⟨⟨BosonicLean.CStar.cpComp g f, fun _ => rfl⟩, ⟨BosonicLean.CStar.cpId, fun _ => rfl⟩⟩

/-! ## Further examples

These examples show that the hypotheses of entries 55, 56 and 57 can be met. -/

/-- A representation: let $\sigma$ be any real bilinear form on $V$. The Hilbert space
$\ell^2(V)$ is nonzero, and the inclusion of $\mathrm{CCR}(V, \sigma)$ in the bounded operators on
$\ell^2(V)$ is a representation. With entry 32 it gives an instance of the hypotheses of
entry 55. -/
theorem witness_inclusion_representation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ : LinearMap.BilinForm ℝ V) :
    Nontrivial (lp (fun _ : V => ℂ) 2) ∧
    ∃ π : CCR σ →⋆ₐ[ℂ] (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2), ∀ a, π a = a := by
  classical
  refine ⟨⟨⟨delta (0 : V), 0, fun h => ?_⟩⟩, ⟨(CCR σ).subtype, fun _ => rfl⟩⟩
  have := norm_delta (0 : V)
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- A state: let $\sigma$ be alternating. There is a state $\omega$ on $\mathrm{CCR}(V, \sigma)$
with characteristic function $\omega(W(u)) = 1$ for $u = 0$ and $\omega(W(u)) = 0$ for $u \ne 0$
(the vector state $a \mapsto \langle \delta_0, a\, \delta_0 \rangle$ of the basis vector at
$0$). -/
theorem witness_vector_state {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    ∃ ω : CCR σ →L[ℂ] ℂ, ω 1 = 1 ∧ (∀ a, 0 ≤ ω (star a * a)) ∧
      ∀ (u : V) (a : CCR σ),
        (a : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) = weyl σ u →
          ω a = if u = 0 then 1 else 0 := by
  refine ⟨vectorState σ, vectorState_one σ, fun a => ?_, fun u a ha => ?_⟩
  · rw [vectorState_star_mul_self]
    exact Complex.zero_le_real.2 (sq_nonneg _)
  · have hau : a = ⟨weyl σ u, weyl_mem_CCR σ u⟩ := Subtype.ext ha
    subst hau
    exact vectorState_weyl σ hσ u

end Sealed
