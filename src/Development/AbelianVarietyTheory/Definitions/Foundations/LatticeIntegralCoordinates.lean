module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Glob.IntegralWittCoefficients

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric

structure G1 (p : ℕ) [Fact p.Prime] where
  lam : Qbar →+* ℂ_[p]
  abelian₂ : AddSubgroup ℂ
  C : WeierstrassCurve.VariableChange ℂ_[p]
  wq : PowerSeries ℂ_[p]
  ex : PowerSeries ℂ_[p]

namespace G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

variable {σ : Type*}

end G1

def IsTwoTorsionPointUnkilled (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

def th0 (Λ : AddSubgroup ℂ) (t0 : ℂ) : ℂ → ℂ :=
  fun z => U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (area Λ : ℂ)

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

end GlobalTheory.Glob.IntegralWittCoefficients
