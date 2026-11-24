module

public import Formalism.FormalGroupLog.Statement
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)

def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ Formalism.G.IntegralMv (expS f)

def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, Formalism.G.IntegralMv (T i)) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i)) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, Formalism.G.IntegralMv (X' i)) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i





end Formalism.HermitianLattices.ExpSeriesBivariate
