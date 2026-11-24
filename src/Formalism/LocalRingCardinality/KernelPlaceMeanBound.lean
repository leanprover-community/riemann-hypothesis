module

public import Formalism.LocalRingCardinality.DataKap
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

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions

def logHook (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def Lprime (D : D7) (L : SizeData₂ D) : ℝ :=
  Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def L6lo (D : D7) (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lprime D L

def kernelPlaceMeanBound (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
    meanE D (fun e => Real.log (X.kapR e))

end Formalism.BasicNotions.DV

end
