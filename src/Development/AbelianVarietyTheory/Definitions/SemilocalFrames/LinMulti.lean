module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Ell

open Formalism.MainNotions.S

section Rep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))

def SmV (w : H) : Prop :=
  ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ Lie) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w

def dR (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : H := deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) 0

end Rep

def lieOf {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | Xᴴ * G + G * X = 0}

structure Mod (n k r : ℕ) where
  ε : Fin n → Bool
  lam : Fin n → ℝ
  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)
  G : Matrix (Fin n) (Fin n) ℂ
  fr : Matrix (Fin n) (Fin n) ℂ
  Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ
  Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  Vp : Type
  [nV : NormedAddCommGroup Vp]
  [iV : InnerProductSpace ℂ Vp]
  π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)
  hlam : Formalism.QuantumDeterminants.IsHCParam lam
  ds : IsDS ε lam σ
  fr_unit : IsUnit fr
  fr_gram : frᴴ * Formalism.REAL.Jm ε * fr = G
  Q_Qi : Q * Qi = 1
  Qi_Q : Qi * Q = 1
  Q_gram : Qᴴ * G * Q = Formalism.QuantumDeterminants.Hpk k r
  hz : Formalism.QuantumDeterminants.inWb k r z
  hT : 0 < Formalism.QuantumDeterminants.Tz k r z
  hc : ∀ a, c a ≠ 0
  hπ : IsHCTypeW k r z u π

attribute [instance] Mod.nH Mod.iH Mod.nV Mod.iV

namespace Mod

variable {n k r : ℕ} (M : Mod n k r)

end Mod

end GlobalTheory.Ell
