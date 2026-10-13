/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import BosonicLean.GaussianTNLean.MPS.Periodic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Matrix.Order

/-! Finite Fourier representation of homogeneous periodic Gaussian covariances. -/

noncomputable section
open scoped ComplexOrder
open Matrix

namespace Gaussian
namespace MPS.Fourier

def localA (M : ℕ) : PhaseIndex M → PhaseIndex (M + M + 1)
  | Sum.inl a => Sum.inl ⟨a.val, by omega⟩
  | Sum.inr a => Sum.inr ⟨a.val, by omega⟩

def localB (M : ℕ) : PhaseIndex M → PhaseIndex (M + M + 1)
  | Sum.inl a => Sum.inl ⟨M + a.val, by omega⟩
  | Sum.inr a => Sum.inr ⟨M + a.val, by omega⟩

def localC (M : ℕ) : PhaseIndex 1 → PhaseIndex (M + M + 1)
  | Sum.inl _ => Sum.inl ⟨M + M, by omega⟩
  | Sum.inr _ => Sum.inr ⟨M + M, by omega⟩

def localV (M : ℕ) := Sum.elim (localA M) (localB M)

def physical {N : ℕ} (a : PhaseIndex 1) (i : Fin N) : PhaseIndex N :=
  Sum.elim (fun _ => Sum.inl i) (fun _ => Sum.inr i) a

def twistSign {M : ℕ} (a : PhaseIndex M) : ℂ :=
  Sum.elim (fun _ => 1) (fun _ => -1) a

def character {N : ℕ} (k i : Fin N) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) * (i.val : ℂ) / (N : ℂ))

def predecessorPhase {N : ℕ} (k : Fin N) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (N : ℂ))

def symbolWiring {N M : ℕ} (k : Fin N) :
    Matrix (PhaseIndex M) (PhaseIndex M ⊕ PhaseIndex M) ℂ :=
  fun a => Sum.elim (fun b => if a = b then 1 else 0)
    (fun b => if a = b then predecessorPhase k * twistSign a else 0)

def virtualBlock {M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :=
  (Γ.map Complex.ofReal).submatrix (localV M) (localV M)

def crossBlock {M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :=
  (Γ.map Complex.ofReal).submatrix (localV M) (localC M)

def physicalBlock {M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :=
  (Γ.map Complex.ofReal).submatrix (localC M) (localC M)

def eliminatedSymbol {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) :=
  symbolWiring k * virtualBlock Γ * (symbolWiring k).conjTranspose

def crossSymbol {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) :=
  symbolWiring k * crossBlock Γ

def covarianceSymbol {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) :=
  physicalBlock Γ -
    (crossSymbol Γ k).conjTranspose * (eliminatedSymbol Γ k)⁻¹ * crossSymbol Γ k

def outputCovariance {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :
    Matrix (PhaseIndex N) (PhaseIndex N) ℝ :=
  contractCovariance (periodicInput (fun _ : Fin N => Γ)) (periodicWiring N M)

def fourierEntry {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k l : Fin N) (a b : PhaseIndex 1) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    character k i * ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) *
      star (character l j)

private def toZMod {N : ℕ} (i : Fin N) : ZMod N := i.val

private lemma character_eq_stdAddChar {N : ℕ} [NeZero N] (k i : Fin N) :
    character k i = ZMod.stdAddChar (-(toZMod i * toZMod k)) := by
  calc
    character k i =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((-((i.val * k.val : ℕ) : ℤ) : ℤ) : ℂ) / (N : ℂ)) := by
      rw [character]
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar (((-((i.val * k.val : ℕ) : ℤ) : ℤ) : ZMod N)) :=
      (ZMod.stdAddChar_coe (N := N) (-((i.val * k.val : ℕ) : ℤ))).symm
    _ = ZMod.stdAddChar (-(toZMod i * toZMod k)) := by
      congr 1
      simp [toZMod]

private lemma toZMod_finRotate {N : ℕ} [NeZero N] (i : Fin N) :
    toZMod (finRotate N i) = toZMod i + 1 := by
  rw [finRotate_apply]
  simp [toZMod, Fin.val_add, ZMod.natCast_mod]

private lemma predecessorPhase_eq_stdAddChar {N : ℕ} [NeZero N] (k : Fin N) :
    predecessorPhase k = ZMod.stdAddChar (-(toZMod k)) := by
  calc
    predecessorPhase k =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(k.val : ℤ) : ℂ) / (N : ℂ)) := by
      rw [predecessorPhase]
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar ((-(k.val : ℤ) : ℤ) : ZMod N) :=
      by simpa only [Int.cast_neg, Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := N) (-(k.val : ℤ))).symm
    _ = ZMod.stdAddChar (-(toZMod k)) := by
      congr 1
      simp [toZMod]

/-- A predecessor shift contributes the phase fixed by the periodic wiring convention. -/
lemma character_finRotate {N : ℕ} [NeZero N] (k i : Fin N) :
    character k (finRotate N i) = predecessorPhase k * character k i := by
  rw [character_eq_stdAddChar, character_eq_stdAddChar,
    predecessorPhase_eq_stdAddChar, toZMod_finRotate]
  rw [add_mul, neg_add, AddChar.map_add_eq_mul]
  simp [mul_comm]

private def modePhase {N : ℕ} [NeZero N] (k i : Fin N) : ℂ :=
  ZMod.stdAddChar (toZMod i * toZMod k)

private lemma modePhase_predecessor {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k i = predecessorPhase k * modePhase k (finRotate N i) := by
  rw [predecessorPhase_eq_stdAddChar]
  simp only [modePhase, toZMod_finRotate, add_mul]
  calc
    ZMod.stdAddChar (toZMod i * toZMod k) =
        ZMod.stdAddChar (-toZMod k +
          (toZMod i * toZMod k + 1 * toZMod k)) := by
      congr 1
      ring
    _ = ZMod.stdAddChar (-toZMod k) *
        ZMod.stdAddChar (toZMod i * toZMod k + 1 * toZMod k) :=
      AddChar.map_add_eq_mul _ _ _

private def successorPhase {N : ℕ} [NeZero N] (k : Fin N) : ℂ :=
  ZMod.stdAddChar (toZMod k)

private lemma star_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ← starRingEnd_apply, ← Circle.coe_inv_eq_conj]
  congr 1
  exact (ZMod.toCircle).map_neg_eq_inv x |>.symm

private lemma successorPhase_eq_star_predecessor {N : ℕ} [NeZero N] (k : Fin N) :
    successorPhase k = star (predecessorPhase k) := by
  rw [predecessorPhase_eq_stdAddChar, successorPhase, star_stdAddChar]
  simp

private lemma modePhase_finRotate {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k (finRotate N i) = successorPhase k * modePhase k i := by
  rw [modePhase, modePhase, successorPhase, toZMod_finRotate, add_mul,
    AddChar.map_add_eq_mul]
  ring_nf

private lemma modePhase_add_one {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k (i + 1) = successorPhase k * modePhase k i := by
  simpa only [finRotate_apply] using modePhase_finRotate k i

private lemma modePhase_finRotate_symm {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k ((finRotate N).symm i) = predecessorPhase k * modePhase k i := by
  simpa using modePhase_predecessor k ((finRotate N).symm i)

private lemma sum_ite_finRotate {N : ℕ} (i : Fin N) (f : Fin N → ℂ) :
    (∑ x : Fin N, if i = finRotate N x then f x else 0) =
      f ((finRotate N).symm i) := by
  let g : Fin N → ℂ := fun y => if i = y then f ((finRotate N).symm y) else 0
  calc
    (∑ x : Fin N, if i = finRotate N x then f x else 0) = ∑ y, g y :=
      Fintype.sum_equiv (finRotate N) _ _
        (by intro x; simp [g, -finRotate_apply, -finRotate_symm_apply])
    _ = f ((finRotate N).symm i) := by simp [g]

private lemma ofReal_ite (p : Prop) [Decidable p] (x y : ℝ) :
    ((if p then x else y : ℝ) : ℂ) = if p then (x : ℂ) else (y : ℂ) := by
  split_ifs <;> rfl

private lemma sum_pair_delta {N M : ℕ} (i : Fin N) (a : Fin M) (s : ℝ)
    (f : Fin N → Fin M → ℂ) :
    (∑ x : Fin N, ∑ b : Fin M,
      ((if i = x then if a = b then s else 0 else 0 : ℝ) : ℂ) * f x b) =
      (s : ℂ) * f i a := by
  calc
    _ = ∑ x : Fin N, if i = x then (s : ℂ) * f x a else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : i = x <;> simp [h, ofReal_ite]
    _ = _ := Fintype.sum_ite_eq i _

private lemma sum_pair_rotate_delta {N M : ℕ} (i : Fin N) (a : Fin M) (s : ℝ)
    (f : Fin N → Fin M → ℂ) :
    (∑ x : Fin N, ∑ b : Fin M,
      ((if i = finRotate N x then if a = b then s else 0 else 0 : ℝ) : ℂ) * f x b) =
      (s : ℂ) * f ((finRotate N).symm i) a := by
  let g : Fin N → ℂ := fun y => ∑ b : Fin M,
    ((if i = y then if a = b then s else 0 else 0 : ℝ) : ℂ) *
      f ((finRotate N).symm y) b
  calc
    _ = ∑ y, g y := Fintype.sum_equiv (finRotate N) _ _
      (by intro x; simp [g, -finRotate_apply, -finRotate_symm_apply])
    _ = ∑ y : Fin N,
        if i = y then (s : ℂ) * f ((finRotate N).symm y) a else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : i = y <;> simp [g, h, ofReal_ite]
    _ = _ := Fintype.sum_ite_eq i _

private lemma sum_pair_delta_right {N M : ℕ} (i : Fin N) (a : Fin M) (s : ℝ)
    (f : Fin N → Fin M → ℂ) :
    (∑ x : Fin N, ∑ b : Fin M,
      ((if x = i then if a = b then s else 0 else 0 : ℝ) : ℂ) * f x b) =
      (s : ℂ) * f i a := by
  calc
    _ = ∑ x : Fin N, if x = i then (s : ℂ) * f x a else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = i <;> simp [h, ofReal_ite]
    _ = _ := Fintype.sum_ite_eq' i _

private lemma sum_delta {N : ℕ} (i : Fin N) (s : ℝ) (f : Fin N → ℂ) :
    (∑ x : Fin N, ((if i = x then s else 0 : ℝ) : ℂ) * f x) =
      (s : ℂ) * f i := by
  simpa only [ofReal_ite, Complex.ofReal_zero, ite_mul, zero_mul] using
    (Fintype.sum_ite_eq i (fun x => (s : ℂ) * f x))

private def inputCoordinate {N d : ℕ} (a : PhaseIndex d) (i : Fin N) :
    PhaseIndex (N * d) :=
  (MPS.Internal.phaseSiteEquiv N d).symm (a, i)

private abbrev FourierPhaseOn (α : Type*) := α ⊕ α

private abbrev FourierLocalMode (M : ℕ) := (Fin M ⊕ Fin M) ⊕ Fin 1

private def fourierLocalModeEquiv (M : ℕ) : FourierLocalMode M ≃ Fin (M + M + 1) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

private def fourierPhaseModeEquiv (N M : ℕ) :
    FourierPhaseOn (Fin N × FourierLocalMode M) ≃ PhaseIndex (N * (M + M + 1)) :=
  Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (fourierLocalModeEquiv M)).trans finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (fourierLocalModeEquiv M)).trans finProdFinEquiv)

private def fourierEliminatedEquiv (N M : ℕ) :
    FourierPhaseOn (Fin N × Fin M) ≃ Fin (N * M + N * M) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

private def fourierWiringRowEquiv (N M : ℕ) :
    FourierPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N ≃
      Fin (N * M + N * M) ⊕ PhaseIndex N :=
  Equiv.sumCongr (fourierEliminatedEquiv N M) (Equiv.refl (PhaseIndex N))

private def fourierWiringCore (N M : ℕ) :
    Matrix (FourierPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N)
      (FourierPhaseOn (Fin N × FourierLocalMode M)) ℝ
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

private def internalEliminated {N M : ℕ} (a : PhaseIndex M) (i : Fin N) :
    FourierPhaseOn (Fin N × Fin M) :=
  match a with
  | Sum.inl q => Sum.inl (i, q)
  | Sum.inr p => Sum.inr (i, p)

private def internalA {N M : ℕ} (a : PhaseIndex M) (i : Fin N) :
    FourierPhaseOn (Fin N × FourierLocalMode M) :=
  match a with
  | Sum.inl q => Sum.inl (i, Sum.inl (Sum.inl q))
  | Sum.inr p => Sum.inr (i, Sum.inl (Sum.inl p))

private def internalB {N M : ℕ} (a : PhaseIndex M) (i : Fin N) :
    FourierPhaseOn (Fin N × FourierLocalMode M) :=
  match a with
  | Sum.inl q => Sum.inl (i, Sum.inl (Sum.inr q))
  | Sum.inr p => Sum.inr (i, Sum.inl (Sum.inr p))

private def internalC {N M : ℕ} (a : PhaseIndex 1) (i : Fin N) :
    FourierPhaseOn (Fin N × FourierLocalMode M) :=
  match a with
  | Sum.inl q => Sum.inl (i, Sum.inr q)
  | Sum.inr p => Sum.inr (i, Sum.inr p)

private def eliminatedCoordinate {N M : ℕ} (a : PhaseIndex M) (i : Fin N) :
    Fin (N * M + N * M) :=
  finSumFinEquiv <| match a with
    | Sum.inl q => Sum.inl (finProdFinEquiv (i, q))
    | Sum.inr p => Sum.inr (finProdFinEquiv (i, p))

private lemma eliminatedCoordinate_eq_internal {N M : ℕ} (a : PhaseIndex M) (i : Fin N) :
    eliminatedCoordinate a i = fourierEliminatedEquiv N M (internalEliminated a i) := by
  rcases a with a | a <;> rfl

private lemma inputCoordinate_localA_eq_internal {N M : ℕ}
    (a : PhaseIndex M) (i : Fin N) :
    inputCoordinate (localA M a) i = fourierPhaseModeEquiv N M (internalA a i) := by
  rcases a with a | a <;>
    simp [inputCoordinate, localA, internalA, fourierPhaseModeEquiv,
      fourierLocalModeEquiv, MPS.Internal.phaseSiteEquiv]
  all_goals apply Fin.ext <;> simp

private lemma inputCoordinate_localB_eq_internal {N M : ℕ}
    (a : PhaseIndex M) (i : Fin N) :
    inputCoordinate (localB M a) i = fourierPhaseModeEquiv N M (internalB a i) := by
  rcases a with a | a <;>
    simp [inputCoordinate, localB, internalB, fourierPhaseModeEquiv,
      fourierLocalModeEquiv, MPS.Internal.phaseSiteEquiv]
  all_goals apply Fin.ext <;> simp [Nat.add_comm]

private lemma inputCoordinate_localC_eq_internal {N M : ℕ}
    (a : PhaseIndex 1) (i : Fin N) :
    inputCoordinate (localC M a) i = fourierPhaseModeEquiv N M (internalC a i) := by
  rcases a with a | a <;>
    simp [inputCoordinate, localC, internalC, fourierPhaseModeEquiv,
      fourierLocalModeEquiv, MPS.Internal.phaseSiteEquiv]
  all_goals apply Fin.ext <;> simp

private lemma periodicWiring_eq_fourierWiringCore (N M : ℕ) :
    periodicWiring N M =
      Matrix.reindex (fourierWiringRowEquiv N M) (fourierPhaseModeEquiv N M)
        (fourierWiringCore N M) := by
  rfl

private def fourierInputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) :
    FourierPhaseOn (Fin N × FourierLocalMode M) → ℂ
  | Sum.inl (i, a) => modePhase k i * v (Sum.inl (fourierLocalModeEquiv M a))
  | Sum.inr (i, a) => modePhase k i * v (Sum.inr (fourierLocalModeEquiv M a))

private def fourierOutputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) :
    FourierPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N → ℂ
  | Sum.inl (Sum.inl (i, a)) =>
      modePhase k i *
        (v (Sum.inl (fourierLocalModeEquiv M (Sum.inl (Sum.inl a)))) +
          predecessorPhase k *
            v (Sum.inl (fourierLocalModeEquiv M (Sum.inl (Sum.inr a)))))
  | Sum.inl (Sum.inr (i, a)) =>
      modePhase k i *
        (v (Sum.inr (fourierLocalModeEquiv M (Sum.inl (Sum.inl a)))) -
          predecessorPhase k *
            v (Sum.inr (fourierLocalModeEquiv M (Sum.inl (Sum.inr a)))))
  | Sum.inr (Sum.inl i) =>
      modePhase k i * v (Sum.inl (fourierLocalModeEquiv M (Sum.inr 0)))
  | Sum.inr (Sum.inr i) =>
      modePhase k i * v (Sum.inr (fourierLocalModeEquiv M (Sum.inr 0)))

private lemma symbolWiring_mulVec {N M : ℕ} (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) (a : PhaseIndex M) :
    (symbolWiring k *ᵥ fun b => v (localV M b)) a =
      v (localA M a) + predecessorPhase k * twistSign a * v (localB M a) := by
  classical
  rcases a with a | a <;>
    simp [symbolWiring, Matrix.mulVec, dotProduct, localV, localA, localB,
      twistSign, Fintype.sum_sum_type]

private def symbolOutputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) :
    FourierPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N → ℂ
  | Sum.inl (Sum.inl (i, a)) =>
      modePhase k i *
        (symbolWiring k *ᵥ fun b => v (localV M b)) (Sum.inl a)
  | Sum.inl (Sum.inr (i, a)) =>
      modePhase k i *
        (symbolWiring k *ᵥ fun b => v (localV M b)) (Sum.inr a)
  | Sum.inr (Sum.inl i) => modePhase k i * v (localC M (Sum.inl 0))
  | Sum.inr (Sum.inr i) => modePhase k i * v (localC M (Sum.inr 0))

private lemma fourierOutputMode_eq_symbolOutputMode {N M : ℕ} [NeZero N]
    (k : Fin N) (v : PhaseIndex (M + M + 1) → ℂ) :
    fourierOutputMode k v = symbolOutputMode k v := by
  funext r
  rcases r with r | r <;> rcases r with r | r
  · obtain ⟨i, a⟩ := r
    have hA : Sum.inl (fourierLocalModeEquiv M (Sum.inl (Sum.inl a))) =
        localA M (Sum.inl a) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localA]
    have hB : Sum.inl (fourierLocalModeEquiv M (Sum.inl (Sum.inr a))) =
        localB M (Sum.inl a) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localB]
    simp [fourierOutputMode, symbolOutputMode, symbolWiring_mulVec, hA, hB,
      twistSign]
  · obtain ⟨i, a⟩ := r
    have hA : Sum.inr (fourierLocalModeEquiv M (Sum.inl (Sum.inl a))) =
        localA M (Sum.inr a) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localA]
    have hB : Sum.inr (fourierLocalModeEquiv M (Sum.inl (Sum.inr a))) =
        localB M (Sum.inr a) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localB]
    simp [fourierOutputMode, symbolOutputMode, symbolWiring_mulVec, hA, hB,
      twistSign, sub_eq_add_neg]
  · have hC : Sum.inl (fourierLocalModeEquiv M (Sum.inr 0)) =
        localC M (Sum.inl 0) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localC]
    simp [fourierOutputMode, symbolOutputMode, hC]
  · have hC : Sum.inr (fourierLocalModeEquiv M (Sum.inr 0)) =
        localC M (Sum.inr 0) := by
      congr 1 <;> simp [fourierLocalModeEquiv, localC]
    simp [fourierOutputMode, symbolOutputMode, hC]

private lemma fourierWiringCore_mulVec_mode {N M : ℕ} [NeZero N]
    (k : Fin N) (v : PhaseIndex (M + M + 1) → ℂ) :
    (fourierWiringCore N M).map Complex.ofReal *ᵥ fourierInputMode k v =
      fourierOutputMode k v := by
  classical
  funext r
  rcases r with r | r <;> rcases r with r | r
  · obtain ⟨i, a⟩ := r
    simp [Matrix.mulVec, dotProduct, fourierWiringCore, fourierInputMode,
      fourierOutputMode, Fintype.sum_sum_type, Fintype.sum_prod_type,
      fourierLocalModeEquiv, localA, localB, ite_and, eq_comm,
      sum_pair_delta, sum_pair_rotate_delta, modePhase_finRotate_symm,
      Finset.sum_add_distrib, -finRotate_apply, -finRotate_symm_apply]
    ring
  · obtain ⟨i, a⟩ := r
    simp [Matrix.mulVec, dotProduct, fourierWiringCore, fourierInputMode,
      fourierOutputMode, Fintype.sum_sum_type, Fintype.sum_prod_type,
      fourierLocalModeEquiv, localA, localB, ite_and, eq_comm,
      sum_pair_delta, sum_pair_rotate_delta, modePhase_finRotate_symm,
      Finset.sum_add_distrib, -finRotate_apply, -finRotate_symm_apply]
    ring
  · simp [Matrix.mulVec, dotProduct, fourierWiringCore, fourierInputMode,
      fourierOutputMode, Fintype.sum_sum_type, Fintype.sum_prod_type,
      fourierLocalModeEquiv, eq_comm, sum_delta]
  · simp [Matrix.mulVec, dotProduct, fourierWiringCore, fourierInputMode,
      fourierOutputMode, Fintype.sum_sum_type, Fintype.sum_prod_type,
      fourierLocalModeEquiv, eq_comm, sum_delta]

private def fourierRowMode {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    FourierPhaseOn (Fin N × Fin M) ⊕ PhaseIndex N → ℂ
  | Sum.inl (Sum.inl (i, a)) => modePhase k i * u (Sum.inl (Sum.inl a))
  | Sum.inl (Sum.inr (i, a)) => modePhase k i * u (Sum.inl (Sum.inr a))
  | Sum.inr (Sum.inl i) => modePhase k i * u (Sum.inr (Sum.inl 0))
  | Sum.inr (Sum.inr i) => modePhase k i * u (Sum.inr (Sum.inr 0))

private def fourierAdjointInput {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    FourierPhaseOn (Fin N × FourierLocalMode M) → ℂ
  | Sum.inl (i, Sum.inl (Sum.inl a)) =>
      modePhase k i * u (Sum.inl (Sum.inl a))
  | Sum.inl (i, Sum.inl (Sum.inr a)) =>
      modePhase k (finRotate N i) * u (Sum.inl (Sum.inl a))
  | Sum.inl (i, Sum.inr _) => modePhase k i * u (Sum.inr (Sum.inl 0))
  | Sum.inr (i, Sum.inl (Sum.inl a)) =>
      modePhase k i * u (Sum.inl (Sum.inr a))
  | Sum.inr (i, Sum.inl (Sum.inr a)) =>
      -(modePhase k (finRotate N i) * u (Sum.inl (Sum.inr a)))
  | Sum.inr (i, Sum.inr _) => modePhase k i * u (Sum.inr (Sum.inr 0))

private def fourierAdjointLocal {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    FourierPhaseOn (FourierLocalMode M) → ℂ
  | Sum.inl (Sum.inl (Sum.inl a)) => u (Sum.inl (Sum.inl a))
  | Sum.inl (Sum.inl (Sum.inr a)) => successorPhase k * u (Sum.inl (Sum.inl a))
  | Sum.inl (Sum.inr _) => u (Sum.inr (Sum.inl 0))
  | Sum.inr (Sum.inl (Sum.inl a)) => u (Sum.inl (Sum.inr a))
  | Sum.inr (Sum.inl (Sum.inr a)) => -(successorPhase k * u (Sum.inl (Sum.inr a)))
  | Sum.inr (Sum.inr _) => u (Sum.inr (Sum.inr 0))

private def localAdjoint {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) : PhaseIndex (M + M + 1) → ℂ
  | Sum.inl a => fourierAdjointLocal k u (Sum.inl ((fourierLocalModeEquiv M).symm a))
  | Sum.inr a => fourierAdjointLocal k u (Sum.inr ((fourierLocalModeEquiv M).symm a))

private lemma fourierAdjointInput_eq_fourierInputMode {N M : ℕ} [NeZero N]
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    fourierAdjointInput k u = fourierInputMode k (localAdjoint k u) := by
  funext c
  rcases c with c | c <;> obtain ⟨i, c⟩ := c <;>
    rcases c with c | c
  · rcases c with a | a <;>
      simp [fourierAdjointInput, fourierInputMode, localAdjoint,
        fourierAdjointLocal, modePhase_finRotate]
    all_goals rw [modePhase_add_one]
    all_goals ring
  · simp [fourierAdjointInput, fourierInputMode, localAdjoint,
      fourierAdjointLocal]
  · rcases c with a | a <;>
      simp [fourierAdjointInput, fourierInputMode, localAdjoint,
        fourierAdjointLocal, modePhase_finRotate]
    all_goals rw [modePhase_add_one]
    all_goals ring
  · simp [fourierAdjointInput, fourierInputMode, localAdjoint,
      fourierAdjointLocal]

private lemma localAdjoint_localV {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) (c : PhaseIndex M ⊕ PhaseIndex M) :
    localAdjoint k u (localV M c) =
      ((symbolWiring k).conjTranspose *ᵥ fun a => u (Sum.inl a)) c := by
  classical
  rcases c with c | c
  · rcases c with a | a
    · have h : (fourierLocalModeEquiv M).symm ⟨a.val, by omega⟩ =
          Sum.inl (Sum.inl a) := by
        apply (fourierLocalModeEquiv M).injective
        simp [fourierLocalModeEquiv]
        apply Fin.ext
        simp
      simp [localAdjoint, fourierAdjointLocal, localV, localA, h,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        symbolWiring, Fintype.sum_sum_type]
    · have h : (fourierLocalModeEquiv M).symm ⟨a.val, by omega⟩ =
          Sum.inl (Sum.inl a) := by
        apply (fourierLocalModeEquiv M).injective
        simp [fourierLocalModeEquiv]
        apply Fin.ext
        simp
      simp [localAdjoint, fourierAdjointLocal, localV, localA, h,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        symbolWiring, Fintype.sum_sum_type]
  · rcases c with a | a
    · have h : (fourierLocalModeEquiv M).symm ⟨M + a.val, by omega⟩ =
          Sum.inl (Sum.inr a) := by
        apply (fourierLocalModeEquiv M).injective
        simp [fourierLocalModeEquiv]
        apply Fin.ext
        simp
        omega
      simp [localAdjoint, fourierAdjointLocal, localV, localB, h,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        symbolWiring, Fintype.sum_sum_type,
        successorPhase_eq_star_predecessor, twistSign, apply_ite]
    · have h : (fourierLocalModeEquiv M).symm ⟨M + a.val, by omega⟩ =
          Sum.inl (Sum.inr a) := by
        apply (fourierLocalModeEquiv M).injective
        simp [fourierLocalModeEquiv]
        apply Fin.ext
        simp
        omega
      simp [localAdjoint, fourierAdjointLocal, localV, localB, h,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        symbolWiring, Fintype.sum_sum_type,
        successorPhase_eq_star_predecessor, twistSign, apply_ite]

private lemma localAdjoint_localC {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) (c : PhaseIndex 1) :
    localAdjoint k u (localC M c) = u (Sum.inr c) := by
  rcases c with c | c
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    have h : (fourierLocalModeEquiv M).symm ⟨M + M, by omega⟩ = Sum.inr 0 := by
      apply (fourierLocalModeEquiv M).injective
      simp [fourierLocalModeEquiv]
      apply Fin.ext
      rfl
    simp [localAdjoint, fourierAdjointLocal, localC, h]
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    have h : (fourierLocalModeEquiv M).symm ⟨M + M, by omega⟩ = Sum.inr 0 := by
      apply (fourierLocalModeEquiv M).injective
      simp [fourierLocalModeEquiv]
      apply Fin.ext
      rfl
    simp [localAdjoint, fourierAdjointLocal, localC, h]

private lemma sum_local_decomposition {M : ℕ} (f : PhaseIndex (M + M + 1) → ℂ) :
    (∑ x : PhaseIndex (M + M + 1), f x) =
      (∑ v : PhaseIndex M ⊕ PhaseIndex M, f (localV M v)) +
        ∑ c : PhaseIndex 1, f (localC M c) := by
  have hA (i : Fin M) : Fin.castAdd 1 (Fin.castAdd M i) =
      (⟨i.val, by omega⟩ : Fin (M + M + 1)) := by
    apply Fin.ext
    rfl
  have hB (i : Fin M) : Fin.castAdd 1 (i.addNat M) =
      (⟨M + i.val, by omega⟩ : Fin (M + M + 1)) := by
    apply Fin.ext
    simp
    omega
  have hC : Fin.natAdd (M + M) (0 : Fin 1) =
      (⟨M + M, by omega⟩ : Fin (M + M + 1)) := by
    apply Fin.ext
    simp
  simp [localV, localA, localB, localC, Fintype.sum_sum_type,
    Fin.sum_univ_add, hA, hB, hC]
  abel

private lemma localCovariance_mulVec_localAdjoint_virtual {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ)
    (c : PhaseIndex M ⊕ PhaseIndex M) :
    ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) (localV M c) =
      (virtualBlock Γ *ᵥ
          ((symbolWiring k).conjTranspose *ᵥ fun a => u (Sum.inl a))) c +
        (crossBlock Γ *ᵥ fun a => u (Sum.inr a)) c := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_local_decomposition]
  simp_rw [localAdjoint_localV, localAdjoint_localC]
  rfl

private lemma localCovariance_mulVec_localAdjoint_physical {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) (c : PhaseIndex 1) :
    ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) (localC M c) =
      ((crossBlock Γ).conjTranspose *ᵥ
          ((symbolWiring k).conjTranspose *ᵥ fun a => u (Sum.inl a))) c +
        (physicalBlock Γ *ᵥ fun a => u (Sum.inr a)) c := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_local_decomposition]
  simp_rw [localAdjoint_localV, localAdjoint_localC]
  simp only [crossBlock, physicalBlock, Matrix.conjTranspose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have hv := congr_fun (congr_fun hΓ (localV M v)) (localC M c)
  simp only [Matrix.transpose_apply] at hv
  change ((Γ (localC M c) (localV M v) : ℝ) : ℂ) * _ =
    star (((Γ (localV M v) (localC M c) : ℝ) : ℂ)) * _
  rw [hv]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private lemma symbolWiring_mulVec_localCovariance_virtual {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    symbolWiring k *ᵥ
        (fun c => ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) (localV M c)) =
      eliminatedSymbol Γ k *ᵥ (fun a => u (Sum.inl a)) +
        crossSymbol Γ k *ᵥ (fun a => u (Sum.inr a)) := by
  have hv : (fun c => ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) (localV M c)) =
      virtualBlock Γ *ᵥ
          ((symbolWiring k).conjTranspose *ᵥ fun a => u (Sum.inl a)) +
        crossBlock Γ *ᵥ (fun a => u (Sum.inr a)) := by
    funext c
    exact localCovariance_mulVec_localAdjoint_virtual Γ k u c
  rw [hv, Matrix.mulVec_add]
  apply congrArg₂ (· + ·)
  · change symbolWiring k *ᵥ
        (virtualBlock Γ *ᵥ
          ((symbolWiring k).conjTranspose *ᵥ fun a => u (Sum.inl a))) =
        (symbolWiring k * virtualBlock Γ * (symbolWiring k).conjTranspose) *ᵥ
          (fun a => u (Sum.inl a))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · change symbolWiring k *ᵥ
        (crossBlock Γ *ᵥ fun a => u (Sum.inr a)) =
        (symbolWiring k * crossBlock Γ) *ᵥ (fun a => u (Sum.inr a))
    rw [Matrix.mulVec_mulVec]

private def localWiredAction {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    PhaseIndex M ⊕ PhaseIndex 1 → ℂ
  | Sum.inl a =>
      (eliminatedSymbol Γ k *ᵥ fun b => u (Sum.inl b)) a +
        (crossSymbol Γ k *ᵥ fun b => u (Sum.inr b)) a
  | Sum.inr c =>
      ((crossSymbol Γ k).conjTranspose *ᵥ fun b => u (Sum.inl b)) c +
        (physicalBlock Γ *ᵥ fun b => u (Sum.inr b)) c

private lemma fourierWiringCore_conjTranspose_mulVec_mode {N M : ℕ} [NeZero N]
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    ((fourierWiringCore N M).map Complex.ofReal).conjTranspose *ᵥ fourierRowMode k u =
      fourierAdjointInput k u := by
  classical
  funext c
  rcases c with c | c <;> obtain ⟨i, c⟩ := c <;>
    rcases c with c | c
  · rcases c with a | a <;>
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        fourierWiringCore, fourierRowMode, fourierAdjointInput,
        Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and, eq_comm,
        sum_pair_delta, sum_pair_delta_right]
  · simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      fourierWiringCore, fourierRowMode, fourierAdjointInput,
      Fintype.sum_sum_type, Fintype.sum_prod_type, eq_comm, sum_delta]
  · rcases c with a | a <;>
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        fourierWiringCore, fourierRowMode, fourierAdjointInput,
        Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and, eq_comm,
        sum_pair_delta, sum_pair_delta_right]
  · simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      fourierWiringCore, fourierRowMode, fourierAdjointInput,
      Fintype.sum_sum_type, Fintype.sum_prod_type, eq_comm, sum_delta]

private def inputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) : PhaseIndex (N * (M + M + 1)) → ℂ :=
  fourierInputMode k v ∘ (fourierPhaseModeEquiv N M).symm

private def pairMode {N d : ℕ} [NeZero N] (k : Fin N) (v : PhaseIndex d → ℂ) :
    PhaseIndex d × Fin N → ℂ :=
  fun ai => modePhase k ai.2 * v ai.1

private lemma blockDiagonal_mulVec_pairMode {N d : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex d) (PhaseIndex d) ℝ) (k : Fin N)
    (v : PhaseIndex d → ℂ) :
    (Matrix.blockDiagonal (fun _ : Fin N => Γ.map Complex.ofReal)) *ᵥ pairMode k v =
      pairMode k ((Γ.map Complex.ofReal) *ᵥ v) := by
  classical
  funext ai
  obtain ⟨a, i⟩ := ai
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, pairMode,
    Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private def siteInputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) : PhaseIndex (N * (M + M + 1)) → ℂ :=
  pairMode k v ∘ MPS.Internal.phaseSiteEquiv N (M + M + 1)

private lemma periodicInput_mulVec_siteInputMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (v : PhaseIndex (M + M + 1) → ℂ) :
    (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal *ᵥ siteInputMode k v =
      siteInputMode k ((Γ.map Complex.ofReal) *ᵥ v) := by
  classical
  let e := MPS.Internal.phaseSiteEquiv N (M + M + 1)
  have hmap : (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal =
      (Matrix.blockDiagonal (fun _ : Fin N => Γ.map Complex.ofReal)).submatrix e e := by
    ext i j
    simp [periodicInput, e, Matrix.blockDiagonal_apply, ofReal_ite]
  rw [hmap, Matrix.submatrix_mulVec_equiv]
  have hin : siteInputMode k v ∘ e.symm = pairMode k v := by
    funext ai
    simp [siteInputMode, e]
  rw [hin, blockDiagonal_mulVec_pairMode]
  rfl

private lemma inputMode_eq_siteInputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) : inputMode k v = siteInputMode k v := by
  funext x
  obtain ⟨x, rfl⟩ := (fourierPhaseModeEquiv N M).surjective x
  rcases x with x | x <;> obtain ⟨i, a⟩ := x <;>
    simp [inputMode, siteInputMode, pairMode, fourierInputMode,
      fourierPhaseModeEquiv, fourierLocalModeEquiv, MPS.Internal.phaseSiteEquiv]

private lemma periodicInput_mulVec_inputMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (v : PhaseIndex (M + M + 1) → ℂ) :
    (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal *ᵥ inputMode k v =
      inputMode k ((Γ.map Complex.ofReal) *ᵥ v) := by
  rw [inputMode_eq_siteInputMode, inputMode_eq_siteInputMode]
  exact periodicInput_mulVec_siteInputMode Γ k v

private def outputMode {N M : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex (M + M + 1) → ℂ) :
    (Fin (N * M + N * M) ⊕ PhaseIndex N) → ℂ :=
  fourierOutputMode k v ∘ (fourierWiringRowEquiv N M).symm

private def rowMode {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    (Fin (N * M + N * M) ⊕ PhaseIndex N) → ℂ :=
  fourierRowMode k u ∘ (fourierWiringRowEquiv N M).symm

private lemma outputMode_localCovariance_eq_rowMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    outputMode k ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) =
      rowMode k (localWiredAction Γ k u) := by
  funext r
  obtain ⟨r, rfl⟩ := (fourierWiringRowEquiv N M).surjective r
  simp only [outputMode, rowMode, Function.comp_apply, Equiv.symm_apply_apply]
  rw [fourierOutputMode_eq_symbolOutputMode]
  rcases r with r | r <;> rcases r with r | r
  · obtain ⟨i, a⟩ := r
    simp only [symbolOutputMode, fourierRowMode, localWiredAction]
    rw [symbolWiring_mulVec_localCovariance_virtual]
    rfl
  · obtain ⟨i, a⟩ := r
    simp only [symbolOutputMode, fourierRowMode, localWiredAction]
    rw [symbolWiring_mulVec_localCovariance_virtual]
    rfl
  · simp only [symbolOutputMode, fourierRowMode, localWiredAction]
    rw [localCovariance_mulVec_localAdjoint_physical Γ hΓ]
    rw [crossSymbol, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec]
  · simp only [symbolOutputMode, fourierRowMode, localWiredAction]
    rw [localCovariance_mulVec_localAdjoint_physical Γ hΓ]
    rw [crossSymbol, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec]

private lemma periodicWiring_mulVec_mode {N M : ℕ} [NeZero N]
    (k : Fin N) (v : PhaseIndex (M + M + 1) → ℂ) :
    (periodicWiring N M).map Complex.ofReal *ᵥ inputMode k v = outputMode k v := by
  classical
  rw [periodicWiring_eq_fourierWiringCore]
  funext r
  change (∑ x, ((fourierWiringCore N M
      ((fourierWiringRowEquiv N M).symm r)
      ((fourierPhaseModeEquiv N M).symm x) : ℝ) : ℂ) *
        fourierInputMode k v ((fourierPhaseModeEquiv N M).symm x)) =
    fourierOutputMode k v ((fourierWiringRowEquiv N M).symm r)
  rw [← (fourierPhaseModeEquiv N M).sum_comp]
  simpa [Matrix.mulVec, dotProduct] using
    congr_fun (fourierWiringCore_mulVec_mode k v)
      ((fourierWiringRowEquiv N M).symm r)

private lemma periodicWiring_conjTranspose_mulVec_mode {N M : ℕ} [NeZero N]
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    ((periodicWiring N M).map Complex.ofReal).conjTranspose *ᵥ rowMode k u =
      inputMode k (localAdjoint k u) := by
  classical
  rw [periodicWiring_eq_fourierWiringCore]
  funext x
  change (∑ r, star (((fourierWiringCore N M
      ((fourierWiringRowEquiv N M).symm r)
      ((fourierPhaseModeEquiv N M).symm x) : ℝ) : ℂ)) *
        fourierRowMode k u ((fourierWiringRowEquiv N M).symm r)) =
    fourierInputMode k (localAdjoint k u) ((fourierPhaseModeEquiv N M).symm x)
  rw [← (fourierWiringRowEquiv N M).sum_comp]
  rw [← fourierAdjointInput_eq_fourierInputMode]
  simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using
    congr_fun (fourierWiringCore_conjTranspose_mulVec_mode k u)
      ((fourierPhaseModeEquiv N M).symm x)

private lemma wiredCovariance_mulVec_rowMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    ((periodicWiring N M).map Complex.ofReal *
          (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal *
          ((periodicWiring N M).map Complex.ofReal).conjTranspose) *ᵥ rowMode k u =
      outputMode k ((Γ.map Complex.ofReal) *ᵥ localAdjoint k u) := by
  rw [← Matrix.mulVec_mulVec, periodicWiring_conjTranspose_mulVec_mode]
  rw [← Matrix.mulVec_mulVec, periodicInput_mulVec_inputMode]
  exact periodicWiring_mulVec_mode k _

private lemma wiredCovariance_mulVec_rowMode_localWired {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    ((periodicWiring N M).map Complex.ofReal *
          (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal *
          ((periodicWiring N M).map Complex.ofReal).conjTranspose) *ᵥ rowMode k u =
      rowMode k (localWiredAction Γ k u) := by
  rw [wiredCovariance_mulVec_rowMode]
  exact outputMode_localCovariance_eq_rowMode Γ hΓ k u

private lemma admissible_map_posDef {n : ℕ}
    {Γ : Matrix (PhaseIndex n) (PhaseIndex n) ℝ} (hΓ : IsAdmissible Γ) :
    (Γ.map Complex.ofReal).PosDef := by
  let Q := Γ.map Complex.ofReal -
    Complex.I • (symplecticForm n).map Complex.ofReal
  have hΓC : (Γ.map Complex.ofReal).transpose = Γ.map Complex.ofReal := by
    ext i j
    change (Γ j i : ℂ) = (Γ i j : ℂ)
    exact congrArg Complex.ofReal (congr_fun (congr_fun hΓ.1 i) j)
  have hΩR : (symplecticForm n).transpose = -symplecticForm n := by
    simp [symplecticForm, Matrix.J_transpose]
  have hΩC : ((symplecticForm n).map Complex.ofReal).transpose =
      -(symplecticForm n).map Complex.ofReal := by
    ext i j
    change ((symplecticForm n) j i : ℂ) = -((symplecticForm n) i j : ℂ)
    have hij := congr_fun (congr_fun hΩR i) j
    exact_mod_cast hij
  have hhalf : ((2 : ℝ)⁻¹ • (Q + Q.transpose)) = Γ.map Complex.ofReal := by
    rw [show Q.transpose = (Γ.map Complex.ofReal).transpose -
        Complex.I • ((symplecticForm n).map Complex.ofReal).transpose by
      simp [Q]]
    rw [hΓC, hΩC]
    ext i j
    simp [Q]
    ring
  have hpsd : (Γ.map Complex.ofReal).PosSemidef := by
    rw [← hhalf]
    exact (hΓ.2.add hΓ.2.transpose).smul (by positivity : 0 ≤ (2 : ℝ)⁻¹)
  apply hpsd.posDef_iff_isUnit.mpr
  change IsUnit (Γ.map (⇑Complex.ofRealHom))
  exact hΓ.posDef.isUnit.map (Complex.ofRealHom.mapMatrix :
    Matrix (PhaseIndex n) (PhaseIndex n) ℝ →+*
      Matrix (PhaseIndex n) (PhaseIndex n) ℂ)

private lemma localV_injective (M : ℕ) : Function.Injective (localV M) := by
  intro x y h
  rcases x with (a | a) | (a | a) <;>
    rcases y with (b | b) | (b | b) <;>
    simp [localV, localA, localB] at h ⊢ <;>
    try { omega }

private lemma symbolWiring_vecMul_injective {N M : ℕ} (k : Fin N) :
    Function.Injective (symbolWiring (M := M) k).vecMul := by
  intro u v h
  funext a
  have ha := congr_fun h (Sum.inl a)
  simpa [Matrix.vecMul, dotProduct, symbolWiring] using ha

private lemma eliminatedSymbol_posDef {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ) (k : Fin N) : (eliminatedSymbol Γ k).PosDef := by
  have hvirtual : (virtualBlock Γ).PosDef := by
    exact (admissible_map_posDef hΓ).submatrix (localV_injective M)
  exact hvirtual.mul_mul_conjTranspose_same (symbolWiring_vecMul_injective k)

private def virtualAmplitude {M : ℕ} (u : PhaseIndex M → ℂ) :
    PhaseIndex M ⊕ PhaseIndex 1 → ℂ :=
  Sum.elim u 0

private def eliminatedMode {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M → ℂ) : Fin (N * M + N * M) → ℂ :=
  fourierRowMode k (virtualAmplitude u) ∘
    fun x => Sum.inl ((fourierEliminatedEquiv N M).symm x)

private lemma rowMode_virtualAmplitude {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M → ℂ) :
    rowMode k (virtualAmplitude u) = Sum.elim (eliminatedMode k u) 0 := by
  funext x
  rcases x with x | x
  · simp [rowMode, fourierWiringRowEquiv, eliminatedMode]
  · rcases x with i | i <;>
      simp [rowMode, fourierWiringRowEquiv, fourierRowMode, virtualAmplitude]

private lemma submatrix_inl_mulVec_of_sumElim {ι κ : Type*}
    [Fintype ι] [Fintype κ] {A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ}
    {x y : ι → ℂ} {z : κ → ℂ}
    (h : A *ᵥ Sum.elim x 0 = Sum.elim y z) :
    A.submatrix Sum.inl Sum.inl *ᵥ x = y := by
  funext i
  have hi := congr_fun h (Sum.inl i)
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hi

private def wiredCovarianceC {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :=
  (periodicWiring N M).map Complex.ofReal *
    (periodicInput (fun _ : Fin N => Γ)).map Complex.ofReal *
      ((periodicWiring N M).map Complex.ofReal).conjTranspose

private def eliminatedBlockC (N M : ℕ)
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :=
  (wiredCovarianceC (N := N) Γ).submatrix Sum.inl Sum.inl

private lemma localWiredAction_virtual {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k : Fin N) (u : PhaseIndex M → ℂ) :
    (fun a => localWiredAction Γ k (virtualAmplitude u) (Sum.inl a)) =
      eliminatedSymbol Γ k *ᵥ u := by
  funext a
  change (eliminatedSymbol Γ k *ᵥ u) a +
      (crossSymbol Γ k *ᵥ (0 : PhaseIndex 1 → ℂ)) a =
    (eliminatedSymbol Γ k *ᵥ u) a
  rw [Matrix.mulVec_zero, Pi.zero_apply, add_zero]

private lemma eliminatedBlockC_mulVec_mode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N) (u : PhaseIndex M → ℂ) :
    eliminatedBlockC N M Γ *ᵥ eliminatedMode k u =
      eliminatedMode k (eliminatedSymbol Γ k *ᵥ u) := by
  have hfull := wiredCovariance_mulVec_rowMode_localWired Γ hΓ k (virtualAmplitude u)
  rw [rowMode_virtualAmplitude] at hfull
  have hleft :
      (fun x => rowMode k (localWiredAction Γ k (virtualAmplitude u)) (Sum.inl x)) =
        eliminatedMode k (eliminatedSymbol Γ k *ᵥ u) := by
    funext x
    obtain ⟨x, rfl⟩ := (fourierEliminatedEquiv N M).surjective x
    rcases x with ⟨i, a⟩ | ⟨i, a⟩
    · simp only [rowMode, eliminatedMode, Function.comp_apply,
        fourierWiringRowEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
        Equiv.refl_symm, Sum.map_inl, Equiv.symm_apply_apply]
      change modePhase k i *
          localWiredAction Γ k (virtualAmplitude u) (Sum.inl (Sum.inl a)) =
        modePhase k i * (eliminatedSymbol Γ k *ᵥ u) (Sum.inl a)
      rw [congr_fun (localWiredAction_virtual Γ k u) (Sum.inl a)]
    · simp only [rowMode, eliminatedMode, Function.comp_apply,
        fourierWiringRowEquiv, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
        Equiv.refl_symm, Sum.map_inl, Equiv.symm_apply_apply]
      change modePhase k i *
          localWiredAction Γ k (virtualAmplitude u) (Sum.inl (Sum.inr a)) =
        modePhase k i * (eliminatedSymbol Γ k *ᵥ u) (Sum.inr a)
      rw [congr_fun (localWiredAction_virtual Γ k u) (Sum.inr a)]
  apply submatrix_inl_mulVec_of_sumElim (A := wiredCovarianceC (N := N) Γ)
    (z := fun x => rowMode k (localWiredAction Γ k (virtualAmplitude u)) (Sum.inr x))
  rw [← hleft]
  have hsplit : rowMode k (localWiredAction Γ k (virtualAmplitude u)) =
      Sum.elim
        (fun x => rowMode k (localWiredAction Γ k (virtualAmplitude u)) (Sum.inl x))
        (fun x => rowMode k (localWiredAction Γ k (virtualAmplitude u)) (Sum.inr x)) := by
    funext x
    rcases x with x | x <;> rfl
  rw [hsplit] at hfull
  exact hfull

private lemma eliminatedBlockC_eq_map_contractionBlock {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :
    eliminatedBlockC N M Γ =
      (contractionBlock (periodicInput (fun _ : Fin N => Γ))
        (periodicWiring N M)).map Complex.ofReal := by
  ext i j
  simp [eliminatedBlockC, wiredCovarianceC, contractionBlock,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma eliminatedBlockC_inv_mulVec_mode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k : Fin N) (u : PhaseIndex M → ℂ) :
    (eliminatedBlockC N M Γ)⁻¹ *ᵥ eliminatedMode k u =
      eliminatedMode k ((eliminatedSymbol Γ k)⁻¹ *ᵥ u) := by
  have hEunit : IsUnit (eliminatedBlockC N M Γ) := by
    rw [eliminatedBlockC_eq_map_contractionBlock]
    change IsUnit ((contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).map (⇑Complex.ofRealHom))
    exact hE.isUnit.map (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ →+*
        Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℂ)
  let _ : Invertible (eliminatedBlockC N M Γ) := hEunit.invertible
  let _ : Invertible (eliminatedSymbol Γ k) :=
    (eliminatedSymbol_posDef Γ hΓ k).isUnit.invertible
  have hforward := eliminatedBlockC_mulVec_mode Γ hΓ.1 k
    ((eliminatedSymbol Γ k)⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec] at hforward
  exact Matrix.inv_mulVec_eq_vec hforward.symm


private def phaseIndexZModEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun := toZMod
  invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
  left_inv := by
    intro i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv := by
    intro z
    exact ZMod.natCast_zmod_val z

private lemma character_modePhase_orthogonality {N : ℕ} [NeZero N]
    (k l : Fin N) :
    (∑ i : Fin N, character k i * modePhase l i) =
      if k = l then (N : ℂ) else 0 := by
  classical
  calc
    _ = ∑ i : Fin N,
        ZMod.stdAddChar (toZMod i * (toZMod l - toZMod k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [character_eq_stdAddChar, modePhase, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ z : ZMod N, ZMod.stdAddChar (z * (toZMod l - toZMod k)) :=
      Fintype.sum_equiv (phaseIndexZModEquiv N) _ _ (fun _ => rfl)
    _ = if toZMod l - toZMod k = 0 then (N : ℂ) else 0 := by
      simpa [ZMod.card] using
        AddChar.sum_mulShift (toZMod l - toZMod k) (ZMod.isPrimitive_stdAddChar N)
    _ = _ := by
      have heq : toZMod l - toZMod k = 0 ↔ k = l := by
        rw [sub_eq_zero]
        exact (phaseIndexZModEquiv N).injective.eq_iff.trans eq_comm
      simp only [heq]


private lemma character_comm {N : ℕ} (k i : Fin N) :
    character k i = character i k := by
  unfold character
  congr 1
  ring

private lemma modePhase_comm {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k i = modePhase i k := by
  unfold modePhase
  rw [mul_comm]

private lemma modePhase_eq_star_character {N : ℕ} [NeZero N] (k i : Fin N) :
    modePhase k i = star (character k i) := by
  rw [character_eq_stdAddChar, star_stdAddChar, neg_neg]
  rfl

private lemma character_modePhase_completeness {N : ℕ} [NeZero N]
    (i j : Fin N) :
    (∑ k : Fin N, character k i * modePhase k j) =
      if i = j then (N : ℂ) else 0 := by
  calc
    _ = ∑ k : Fin N, character i k * modePhase j k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [character_comm k i, modePhase_comm k j]
    _ = _ := character_modePhase_orthogonality i j

private lemma reconstruction_from_mode_sums {N : ℕ} [NeZero N]
    (f : Fin N → ℂ) (i : Fin N) :
    (N : ℂ)⁻¹ * (∑ k : Fin N, character k i *
      (∑ j : Fin N, modePhase k j * f j)) = f i := by
  classical
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ = (N : ℂ)⁻¹ * ∑ j : Fin N,
        (∑ k : Fin N, character k i * modePhase k j) * f j := by
      congr 1
      simp only [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = (N : ℂ)⁻¹ * ∑ j : Fin N, (if i = j then (N : ℂ) else 0) * f j := by
      simp_rw [character_modePhase_completeness]
    _ = f i := by
      simp [ite_mul, ← mul_assoc, hN]


private def physicalMode {N : ℕ} [NeZero N] (k : Fin N)
    (v : PhaseIndex 1 → ℂ) : PhaseIndex N → ℂ :=
  Sum.elim (fun i => modePhase k i * v (Sum.inl 0))
    (fun i => modePhase k i * v (Sum.inr 0))

private lemma rowMode_physical_projection {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    (fun x => rowMode k u (Sum.inr x)) =
      physicalMode k (fun a => u (Sum.inr a)) := by
  funext x
  rcases x with i | i <;> rfl

private lemma rowMode_virtual_projection {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex M ⊕ PhaseIndex 1 → ℂ) :
    (fun x => rowMode k u (Sum.inl x)) =
      eliminatedMode k (fun a => u (Sum.inl a)) := by
  funext x
  obtain ⟨x, rfl⟩ := (fourierEliminatedEquiv N M).surjective x
  rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;>
    simp [rowMode, eliminatedMode, fourierWiringRowEquiv,
      fourierRowMode, virtualAmplitude]

private lemma rowMode_physicalAmplitude {N M : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex 1 → ℂ) :
    rowMode (M := M) k (Sum.elim 0 u) = Sum.elim (0 : Fin (N * M + N * M) → ℂ) (physicalMode k u) := by
  funext x
  rcases x with x | x
  · have h := congr_fun (rowMode_virtual_projection (M := M) k (Sum.elim 0 u)) x
    rw [h]
    obtain ⟨x, rfl⟩ := (fourierEliminatedEquiv N M).surjective x
    rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;>
      simp [eliminatedMode, fourierRowMode, virtualAmplitude]
  · exact congr_fun (rowMode_physical_projection (M := M) k (Sum.elim 0 u)) x


private lemma crossBlockC_mulVec_physicalMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N) (u : PhaseIndex 1 → ℂ) :
    (wiredCovarianceC (N := N) Γ).submatrix Sum.inl Sum.inr *ᵥ physicalMode k u =
      eliminatedMode k (crossSymbol Γ k *ᵥ u) := by
  have hlocal : (fun a => localWiredAction Γ k (Sum.elim 0 u) (Sum.inl a)) =
      crossSymbol Γ k *ᵥ u := by
    funext a
    change (eliminatedSymbol Γ k *ᵥ (0 : PhaseIndex M → ℂ)) a +
      (crossSymbol Γ k *ᵥ u) a = (crossSymbol Γ k *ᵥ u) a
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_add]
  have hfull := wiredCovariance_mulVec_rowMode_localWired Γ hΓ k (Sum.elim 0 u)
  rw [rowMode_physicalAmplitude] at hfull
  have hproj := rowMode_virtual_projection k (localWiredAction Γ k (Sum.elim 0 u))
  rw [hlocal] at hproj
  funext x
  have hx := congr_fun hfull (Sum.inl x)
  have hp := congr_fun hproj x
  rw [hp] at hx
  simpa [wiredCovarianceC, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hx

private lemma adjointCrossBlockC_mulVec_eliminatedMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N) (u : PhaseIndex M → ℂ) :
    (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inl *ᵥ eliminatedMode k u =
      physicalMode k ((crossSymbol Γ k).conjTranspose *ᵥ u) := by
  have hlocal :
      (fun a => localWiredAction Γ k (virtualAmplitude u) (Sum.inr a)) =
        (crossSymbol Γ k).conjTranspose *ᵥ u := by
    funext a
    change ((crossSymbol Γ k).conjTranspose *ᵥ u) a +
        (physicalBlock Γ *ᵥ (0 : PhaseIndex 1 → ℂ)) a =
      ((crossSymbol Γ k).conjTranspose *ᵥ u) a
    rw [Matrix.mulVec_zero, Pi.zero_apply, add_zero]
  have hfull := wiredCovariance_mulVec_rowMode_localWired Γ hΓ k (virtualAmplitude u)
  rw [rowMode_virtualAmplitude] at hfull
  have hproj := rowMode_physical_projection k
    (localWiredAction Γ k (virtualAmplitude u))
  rw [hlocal] at hproj
  funext x
  have hx := congr_fun hfull (Sum.inr x)
  have hp := congr_fun hproj x
  rw [hp] at hx
  simpa [wiredCovarianceC, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hx

private lemma physicalBlockC_mulVec_physicalMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : Γ.transpose = Γ) (k : Fin N) (u : PhaseIndex 1 → ℂ) :
    (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inr *ᵥ physicalMode k u =
      physicalMode k (physicalBlock Γ *ᵥ u) := by
  have hlocal : (fun a => localWiredAction Γ k (Sum.elim 0 u) (Sum.inr a)) =
      physicalBlock Γ *ᵥ u := by
    funext a
    change ((crossSymbol Γ k).conjTranspose *ᵥ (0 : PhaseIndex M → ℂ)) a +
        (physicalBlock Γ *ᵥ u) a = (physicalBlock Γ *ᵥ u) a
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_add]
  have hfull := wiredCovariance_mulVec_rowMode_localWired Γ hΓ k (Sum.elim 0 u)
  rw [rowMode_physicalAmplitude] at hfull
  have hproj := rowMode_physical_projection k (localWiredAction Γ k (Sum.elim 0 u))
  rw [hlocal] at hproj
  funext x
  have hx := congr_fun hfull (Sum.inr x)
  have hp := congr_fun hproj x
  rw [hp] at hx
  simpa [wiredCovarianceC, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hx

private lemma wiredCovarianceC_eq_map {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ) :
    wiredCovarianceC (N := N) Γ =
      (periodicWiring N M * periodicInput (fun _ : Fin N => Γ) *
        (periodicWiring N M).transpose).map Complex.ofReal := by
  ext i j
  simp [wiredCovarianceC, Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma outputCovariance_map_eq_schur {N M : ℕ}
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef) :
    (outputCovariance Γ).map Complex.ofReal =
      (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inr -
        (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inl *
          (eliminatedBlockC N M Γ)⁻¹ *
            (wiredCovarianceC (N := N) Γ).submatrix Sum.inl Sum.inr := by
  let V := periodicWiring N M * periodicInput (fun _ : Fin N => Γ) *
    (periodicWiring N M).transpose
  let E := V.submatrix Sum.inl Sum.inl
  have hEdef : E = contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M) := by rfl
  have hEmap : E.map Complex.ofReal = eliminatedBlockC N M Γ := by
    rw [hEdef, eliminatedBlockC_eq_map_contractionBlock]
  let _ : Invertible E := (hEdef ▸ hE).isUnit.invertible
  have hEMapUnit : IsUnit (E.map (⇑Complex.ofRealHom)) :=
    (hEdef ▸ hE).isUnit.map (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ →+*
        Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℂ)
  let _ : Invertible (E.map (⇑Complex.ofRealHom)) := hEMapUnit.invertible
  let _ : Invertible ((Complex.ofRealHom.mapMatrix :
      Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ →+*
        Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℂ) E) :=
    Invertible.map (Complex.ofRealHom.mapMatrix :
      Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ →+*
        Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℂ) E
  have hinv : E⁻¹.map Complex.ofReal = (eliminatedBlockC N M Γ)⁻¹ := by
    calc
      E⁻¹.map Complex.ofReal = E⁻¹.map (⇑Complex.ofRealHom) := by rfl
      _ = (E.map (⇑Complex.ofRealHom))⁻¹ := by
        rw [← Matrix.invOf_eq_nonsing_inv E,
          ← Matrix.invOf_eq_nonsing_inv (E.map (⇑Complex.ofRealHom))]
        simpa only [RingHom.mapMatrix_apply] using
          (map_invOf (Complex.ofRealHom.mapMatrix :
            Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℝ →+*
              Matrix (Fin (N * M + N * M)) (Fin (N * M + N * M)) ℂ) E)
      _ = (eliminatedBlockC N M Γ)⁻¹ := congrArg Inv.inv hEmap
  have hVmap : V.map Complex.ofReal = wiredCovarianceC (N := N) Γ := by
    exact (wiredCovarianceC_eq_map Γ).symm
  have h22 : (V.submatrix Sum.inr Sum.inr).map Complex.ofReal =
      (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inr := by
    ext i j
    exact congr_fun (congr_fun hVmap (Sum.inr i)) (Sum.inr j)
  have h21 : (V.submatrix Sum.inr Sum.inl).map Complex.ofReal =
      (wiredCovarianceC (N := N) Γ).submatrix Sum.inr Sum.inl := by
    ext i j
    exact congr_fun (congr_fun hVmap (Sum.inr i)) (Sum.inl j)
  have h12 : (V.submatrix Sum.inl Sum.inr).map Complex.ofReal =
      (wiredCovarianceC (N := N) Γ).submatrix Sum.inl Sum.inr := by
    ext i j
    exact congr_fun (congr_fun hVmap (Sum.inl i)) (Sum.inr j)
  change (V.submatrix Sum.inr Sum.inr -
      V.submatrix Sum.inr Sum.inl * E⁻¹ * V.submatrix Sum.inl Sum.inr).map
        Complex.ofReal = _
  calc
    _ = (V.submatrix Sum.inr Sum.inr).map Complex.ofReal -
        (V.submatrix Sum.inr Sum.inl).map Complex.ofReal *
          E⁻¹.map Complex.ofReal *
            (V.submatrix Sum.inl Sum.inr).map Complex.ofReal := by
      ext i j
      simp [Matrix.mul_apply]
    _ = _ := by rw [h22, h21, hinv, h12]

private lemma outputCovariance_mulVec_physicalMode {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k : Fin N) (u : PhaseIndex 1 → ℂ) :
    (outputCovariance Γ).map Complex.ofReal *ᵥ physicalMode k u =
      physicalMode k (covarianceSymbol Γ k *ᵥ u) := by
  rw [outputCovariance_map_eq_schur Γ hE, Matrix.sub_mulVec,
    physicalBlockC_mulVec_physicalMode Γ hΓ.1]
  rw [← Matrix.mulVec_mulVec, crossBlockC_mulVec_physicalMode Γ hΓ.1]
  rw [← Matrix.mulVec_mulVec, eliminatedBlockC_inv_mulVec_mode Γ hΓ hE]
  rw [adjointCrossBlockC_mulVec_eliminatedMode Γ hΓ.1]
  funext x
  rcases x with i | i <;>
    simp [physicalMode, covarianceSymbol, Matrix.sub_mulVec,
      Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, sub_eq_add_neg, mul_add]

private lemma outputCovariance_mode_sum {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k : Fin N) (a b : PhaseIndex 1) (i : Fin N) :
    (∑ j : Fin N, ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) *
      modePhase k j) = modePhase k i * covarianceSymbol Γ k a b := by
  classical
  have h := congr_fun
    (outputCovariance_mulVec_physicalMode Γ hΓ hE k (Pi.single b 1))
    (physical a i)
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simpa [Matrix.mulVec, dotProduct, physicalMode, physical,
      Fintype.sum_sum_type] using h

private lemma outputCovariance_reconstruction {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (a b : PhaseIndex 1) (i j : Fin N) :
    ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ k : Fin N,
        star (character k i) * covarianceSymbol Γ k a b * character k j := by
  calc
    _ = (N : ℂ)⁻¹ * ∑ k : Fin N, character k j *
        (∑ r : Fin N,
          modePhase k r *
            ((outputCovariance Γ (physical a i) (physical b r) : ℝ) : ℂ)) :=
      (reconstruction_from_mode_sums
        (fun r => ((outputCovariance Γ (physical a i) (physical b r) : ℝ) : ℂ)) j).symm
    _ = (N : ℂ)⁻¹ * ∑ k : Fin N,
        star (character k i) * covarianceSymbol Γ k a b * character k j := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [show (∑ r : Fin N, modePhase k r *
          ((outputCovariance Γ (physical a i) (physical b r) : ℝ) : ℂ)) =
          modePhase k i * covarianceSymbol Γ k a b by
        simpa only [mul_comm] using outputCovariance_mode_sum Γ hΓ hE k a b i]
      rw [modePhase_eq_star_character]
      ring

private lemma fourierEntry_eq {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k l : Fin N) (a b : PhaseIndex 1) :
    fourierEntry Γ k l a b =
      if k = l then covarianceSymbol Γ k a b else 0 := by
  classical
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold fourierEntry
  simp_rw [← modePhase_eq_star_character]
  calc
    (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
        character k i *
          ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) *
            modePhase l j =
      (N : ℂ)⁻¹ * ∑ i : Fin N, character k i *
        (∑ j : Fin N,
          ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) *
            modePhase l j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (N : ℂ)⁻¹ * ∑ i : Fin N,
        character k i * (modePhase l i * covarianceSymbol Γ l a b) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [outputCovariance_mode_sum Γ hΓ hE l a b i]
    _ = (N : ℂ)⁻¹ *
        ((∑ i : Fin N, character k i * modePhase l i) *
          covarianceSymbol Γ l a b) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = if k = l then covarianceSymbol Γ k a b else 0 := by
      rw [character_modePhase_orthogonality]
      split_ifs with hkl
      · subst l
        field_simp
      · simp [hkl]

private lemma outputCovariance_translationInvariant {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (a b : PhaseIndex 1) (i j : Fin N) :
    outputCovariance Γ (physical a (finRotate N i)) (physical b (finRotate N j)) =
      outputCovariance Γ (physical a i) (physical b j) := by
  apply Complex.ofReal_injective
  rw [outputCovariance_reconstruction Γ hΓ hE,
    outputCovariance_reconstruction Γ hΓ hE]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hp : star (predecessorPhase k) * predecessorPhase k = 1 := by
    rw [predecessorPhase_eq_stdAddChar, star_stdAddChar, neg_neg,
      ← AddChar.map_add_eq_mul]
    simp
  rw [character_finRotate, character_finRotate, star_mul]
  calc
    star (character k i) * star (predecessorPhase k) *
          covarianceSymbol Γ k a b *
        (predecessorPhase k * character k j) =
      (star (predecessorPhase k) * predecessorPhase k) *
        (star (character k i) * covarianceSymbol Γ k a b * character k j) := by
          ring
    _ = _ := by rw [hp, one_mul]

private lemma character_eq_star_of_add_mod_eq_zero {N : ℕ} [NeZero N]
    (k l : Fin N) (hkl : (k.val + l.val) % N = 0) (i : Fin N) :
    character l i = star (character k i) := by
  have hz : toZMod k + toZMod l = 0 := by
    apply ZMod.val_injective
    simpa [toZMod, ZMod.val_add] using hkl
  have hl : toZMod l = -toZMod k := eq_neg_of_add_eq_zero_right hz
  rw [character_eq_stdAddChar, character_eq_stdAddChar, star_stdAddChar, hl]
  congr 1
  ring

private lemma fourierEntry_conj_of_add_mod_eq_zero {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (k l : Fin N) (hkl : (k.val + l.val) % N = 0)
    (a b : PhaseIndex 1) :
    fourierEntry Γ l l a b = star (fourierEntry Γ k k a b) := by
  classical
  unfold fourierEntry
  simp_rw [character_eq_star_of_add_mod_eq_zero k l hkl]
  rw [star_mul]
  simp only [star_sum, star_mul, star_star]
  rw [show star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ by simp]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

private lemma covarianceSymbol_conj_of_add_mod_eq_zero {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k l : Fin N) (hkl : (k.val + l.val) % N = 0) :
    covarianceSymbol Γ l = (covarianceSymbol Γ k).map star := by
  ext a b
  have hl := fourierEntry_eq Γ hΓ hE l l a b
  have hk := fourierEntry_eq Γ hΓ hE k k a b
  simp only [ite_eq_left] at hl hk
  rw [← hl, Matrix.map_apply, ← hk]
  exact fourierEntry_conj_of_add_mod_eq_zero Γ k l hkl a b

private def physicalFourierMatrix {N : ℕ} [NeZero N] (k : Fin N) :
    Matrix (PhaseIndex N) (PhaseIndex 1) ℂ
  | Sum.inl i, Sum.inl _ => modePhase k i
  | Sum.inr i, Sum.inr _ => modePhase k i
  | _, _ => 0

private lemma physicalFourierMatrix_mulVec {N : ℕ} [NeZero N] (k : Fin N)
    (u : PhaseIndex 1 → ℂ) :
    physicalFourierMatrix k *ᵥ u = physicalMode k u := by
  funext x
  rcases x with i | i <;>
    simp [physicalFourierMatrix, physicalMode, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]

private lemma physicalFourierMatrix_gram {N : ℕ} [NeZero N] (k : Fin N) :
    (physicalFourierMatrix k).conjTranspose * physicalFourierMatrix k =
      (N : ℝ) • (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℂ) := by
  classical
  have hstar (i : Fin N) : (starRingEnd ℂ) (modePhase k i) = character k i := by
    rw [modePhase_eq_star_character]
    change star (star (character k i)) = character k i
    exact star_star (character k i)
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, physicalFourierMatrix,
      Fintype.sum_sum_type]
  all_goals simpa [hstar] using character_modePhase_orthogonality k k

private lemma symplectic_mul_physicalFourierMatrix {N : ℕ} [NeZero N]
    (k : Fin N) :
    (symplecticForm N).map Complex.ofReal * physicalFourierMatrix k =
      physicalFourierMatrix k * (symplecticForm 1).map Complex.ofReal := by
  classical
  ext x a
  rcases x with i | i <;> rcases a with a | a <;>
    fin_cases a <;>
    simp [Matrix.mul_apply, physicalFourierMatrix, symplecticForm, Matrix.J,
      Fintype.sum_sum_type]
  all_goals simpa [Matrix.one_apply] using sum_delta i 1 (modePhase k)

private lemma outputCovariance_mul_physicalFourierMatrix {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (k : Fin N) :
    (outputCovariance Γ).map Complex.ofReal * physicalFourierMatrix k =
      physicalFourierMatrix k * covarianceSymbol Γ k := by
  ext x b
  change ((outputCovariance Γ).map Complex.ofReal *ᵥ fun y =>
      physicalFourierMatrix k y b) x =
    (physicalFourierMatrix k *ᵥ fun a => covarianceSymbol Γ k a b) x
  have hcol : (fun y => physicalFourierMatrix k y b) =
      physicalMode k (Pi.single b 1) := by
    funext y
    rcases y with i | i <;> rcases b with b | b <;>
      fin_cases b <;> simp [physicalFourierMatrix, physicalMode]
  rw [hcol, outputCovariance_mulVec_physicalMode Γ hΓ hE]
  rw [physicalFourierMatrix_mulVec]
  congr 1
  funext a
  rcases b with b | b <;> fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private lemma covarianceSymbol_uncertainty {N M : ℕ} [NeZero N]
    (Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ)
    (hΓ : IsAdmissible Γ)
    (hE : (contractionBlock (periodicInput (fun _ : Fin N => Γ))
      (periodicWiring N M)).PosDef)
    (hOut : IsAdmissible (outputCovariance (N := N) Γ)) (k : Fin N) :
    (covarianceSymbol Γ k -
      Complex.I • (symplecticForm 1).map Complex.ofReal).PosSemidef := by
  let T := physicalFourierMatrix k
  have hcov : T.conjTranspose * (outputCovariance Γ).map Complex.ofReal * T =
      (N : ℝ) • covarianceSymbol Γ k := by
    calc
      _ = T.conjTranspose *
          ((outputCovariance Γ).map Complex.ofReal * T) := by
            rw [Matrix.mul_assoc]
      _ = T.conjTranspose * (T * covarianceSymbol Γ k) := by
            rw [show (outputCovariance Γ).map Complex.ofReal * T =
              T * covarianceSymbol Γ k by
                simpa [T] using outputCovariance_mul_physicalFourierMatrix Γ hΓ hE k]
      _ = (T.conjTranspose * T) * covarianceSymbol Γ k := by
            rw [Matrix.mul_assoc]
      _ = (N : ℝ) • covarianceSymbol Γ k := by
            rw [show T.conjTranspose * T =
              (N : ℝ) • (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℂ) by
                simpa [T] using physicalFourierMatrix_gram k]
            simp [Matrix.smul_mul]
  have hsymp : T.conjTranspose * (symplecticForm N).map Complex.ofReal * T =
      (N : ℝ) • (symplecticForm 1).map Complex.ofReal := by
    calc
      _ = T.conjTranspose * ((symplecticForm N).map Complex.ofReal * T) := by
            rw [Matrix.mul_assoc]
      _ = T.conjTranspose * (T * (symplecticForm 1).map Complex.ofReal) := by
            rw [show (symplecticForm N).map Complex.ofReal * T =
              T * (symplecticForm 1).map Complex.ofReal by
                simpa [T] using symplectic_mul_physicalFourierMatrix k]
      _ = (T.conjTranspose * T) * (symplecticForm 1).map Complex.ofReal := by
            rw [Matrix.mul_assoc]
      _ = (N : ℝ) • (symplecticForm 1).map Complex.ofReal := by
            rw [show T.conjTranspose * T =
              (N : ℝ) • (1 : Matrix (PhaseIndex 1) (PhaseIndex 1) ℂ) by
                simpa [T] using physicalFourierMatrix_gram k]
            simp [Matrix.smul_mul]
  have hpull := hOut.2.conjTranspose_mul_mul_same T
  have hpullEq : T.conjTranspose *
        ((outputCovariance Γ).map Complex.ofReal -
          Complex.I • (symplecticForm N).map Complex.ofReal) * T =
      (N : ℝ) • (covarianceSymbol Γ k -
        Complex.I • (symplecticForm 1).map Complex.ofReal) := by
    calc
      _ = T.conjTranspose * (outputCovariance Γ).map Complex.ofReal * T -
          Complex.I •
            (T.conjTranspose * (symplecticForm N).map Complex.ofReal * T) := by
              rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
                Matrix.smul_mul]
      _ = (N : ℝ) • covarianceSymbol Γ k -
          Complex.I • ((N : ℝ) • (symplecticForm 1).map Complex.ofReal) := by
              rw [hcov, hsymp]
      _ = (N : ℝ) • (covarianceSymbol Γ k -
          Complex.I • (symplecticForm 1).map Complex.ofReal) := by
              rw [smul_sub]
              congr 1
              rw [smul_comm]
  rw [hpullEq] at hpull
  have hscaled := hpull.smul (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simpa [smul_smul, hNR] using hscaled

end MPS.Fourier

open MPS.Fourier

/-- Homogeneous periodic Gaussian contraction is diagonal in finite Fourier modes. -/
theorem homogeneousPeriodicCovariance_fourier : ∀ (N M : ℕ), 3 ≤ N → 1 ≤ M →
    ∀ Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ,
      IsAdmissible Γ →
      (∀ (a b : PhaseIndex 1) (i j : Fin N),
        outputCovariance Γ (physical a (finRotate N i)) (physical b (finRotate N j)) =
          outputCovariance Γ (physical a i) (physical b j)) ∧
      (∀ k : Fin N, (eliminatedSymbol Γ k).PosDef) ∧
      (∀ (k l : Fin N) (a b : PhaseIndex 1),
        fourierEntry Γ k l a b = if k = l then covarianceSymbol Γ k a b else 0) := by
  intro N M hN hM Γ hΓ
  letI : NeZero N := ⟨by omega⟩
  have hperiod := periodicCovariance_admissible hN hM
    (fun _ : Fin N => Γ) (fun _ => hΓ)
  have hE := hperiod.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro a b i j
    exact outputCovariance_translationInvariant Γ hΓ hE a b i j
  · intro k
    exact eliminatedSymbol_posDef Γ hΓ k
  · intro k l a b
    exact fourierEntry_eq Γ hΓ hE k l a b

/-- Fourier inversion reconstructs the periodic covariance and preserves each sector's uncertainty bound. -/
theorem homogeneousPeriodicCovariance_reconstruct : ∀ (N M : ℕ), 3 ≤ N → 1 ≤ M →
    ∀ Γ : Matrix (PhaseIndex (M + M + 1)) (PhaseIndex (M + M + 1)) ℝ,
      IsAdmissible Γ →
      (∀ (a b : PhaseIndex 1) (i j : Fin N),
        ((outputCovariance Γ (physical a i) (physical b j) : ℝ) : ℂ) =
          (N : ℂ)⁻¹ * ∑ k : Fin N,
            star (character k i) * covarianceSymbol Γ k a b * character k j) ∧
      (∀ k : Fin N,
        (covarianceSymbol Γ k -
          Complex.I • (symplecticForm 1).map Complex.ofReal).PosSemidef) ∧
      (∀ k l : Fin N, (k.val + l.val) % N = 0 →
        covarianceSymbol Γ l = (covarianceSymbol Γ k).map star) := by
  intro N M hN hM Γ hΓ
  letI : NeZero N := ⟨by omega⟩
  have hperiod := periodicCovariance_admissible hN hM
    (fun _ : Fin N => Γ) (fun _ => hΓ)
  have hE := hperiod.2.2.1
  have hOut := hperiod.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a b i j
    exact outputCovariance_reconstruction Γ hΓ hE a b i j
  · intro k
    exact covarianceSymbol_uncertainty Γ hΓ hE hOut k
  · intro k l hkl
    exact covarianceSymbol_conj_of_add_mod_eq_zero Γ hΓ hE k l hkl

end Gaussian
