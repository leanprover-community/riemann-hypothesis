module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
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

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount

open Formalism.MainNotions.S GlobalTheory.Count

def ballSet (I : AutInst) (x : I.GA) (r : InfinitePlace I.F → ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v}

def bigA (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / (tau1 I x) ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def AutBallCount : Prop :=
  ∀ (I : AutInst), 1 ≤ I.n → ∀ (x : I.GA) (r : InfinitePlace I.F → ℝ), (∀ v, 0 ≤ r v) →
    (ballSet I x r).Finite ∧
      ((ballSet I x r).ncard : ℝ) ≤ bigA I x * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount
