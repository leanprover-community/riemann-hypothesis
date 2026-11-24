module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartMixedEnergy {e : ℕ} (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) : ℝ :=
  ∫ y : Fin e → ℂ, (hermChartPot M y - hermChartPot N y) *
    maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y

def ChartEnergy.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k =
      1 / 2 * (Real.log M.det.re - Real.log N.det.re) *
        chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
