module

public import Formalism.RealPlaceAnalysis.StatementE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

def IsHCParam {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)

def lowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε

def GapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin n, ε a ≠ ε b → h ≤ |lam a - lam b|

def fdegHC {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) /
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

def rhoStd (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)

def capP {n : ℕ} (lam : Fin n → ℂ) (Y : ℂ) : ℂ := ∏ s : Fin n, (Y + lam s)

def LowKInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    ∀ a, ∃ m : ℤ, lowK ε lam a = (m : ℝ)

def FdegPos : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), Function.Injective lam → 0 < fdegHC lam

def FdegRatio : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ →
    (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) → Function.Injective (μ + Pi.single s 1) →
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def CapelliHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = capP (fun s => ν s + (rhoStd n s : ℂ)) Y • v

end Formalism.QuantumDeterminants
