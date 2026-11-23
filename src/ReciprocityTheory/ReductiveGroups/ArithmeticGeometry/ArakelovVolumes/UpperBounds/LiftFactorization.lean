module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def nD (f p q : ℕ) : ℕ := f * (p * q)

def Zof {f p q : ℕ} (v : V (nD f p q)) (k : Fin f) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun a b => v (finProdFinEquiv (k, finProdFinEquiv (a, b)))

def Dset (f p q : ℕ) : Set (V (nD f p q)) :=
  {v | ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef}

def rh {f p q : ℕ} (v : V (nD f p q)) : ℝ :=
  -∑ k, Real.log (1 - Zof v k * (Zof v k)ᴴ).det.re

def RhGradStatement : Prop :=
  ∀ f p q : ℕ, ∀ v ∈ Dset f p q, ∀ ξ : Fin (nD f p q) → ℂ,
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v ξ).re

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
