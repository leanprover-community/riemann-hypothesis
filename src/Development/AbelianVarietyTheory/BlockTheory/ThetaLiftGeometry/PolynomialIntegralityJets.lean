module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
