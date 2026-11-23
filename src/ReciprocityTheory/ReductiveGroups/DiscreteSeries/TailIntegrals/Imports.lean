module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
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

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

def fS {p m : ℕ} (s : Fin (p + 2) → ℝ) (x : Xp (p + 1) m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-s l))

def rho (t : ℝ) : ℂ := (1 + t * Complex.I) ^ 2 / ((1 + t ^ 2 : ℝ) : ℂ)

def rot {p m : ℕ} (t : ℝ) (x : Xp p m) : Xp p m :=
  (fun j => rho t * x.1 j, fun j => rho t * x.2.1 j, fun i => rho t * x.2.2.1 i, x.2.2.2)

def scl {p m : ℕ} (τ : ℝ) (x : Xp (p + 1) m) : Xp (p + 1) m :=
  (Function.update x.1 0 (τ * x.1 0), Function.update x.2.1 0 (x.2.1 0 / τ), x.2.2.1, x.2.2.2)

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
