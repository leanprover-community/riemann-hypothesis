module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.RgHe.A.Pf

theorem seedB_of : PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.Occ → PositivityTheory.RgHe.A.SchurEigenProjectionExists := by
  intro hS hO n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ hW
  have hG : PositivityTheory.RgHe.Gp ε lam ε' mu e :=
    ⟨hF, hP.two, hP.neg, hP.le, hP.hc, hP.hc', hP.gap, hP.gap'⟩
  have hj := hO n ε lam ε' mu e hG hW H H' π σ hπ hσ
  exact hS n ε lam ε' mu e hG H H' π σ ν hν hπ hσ hj

end PositivityTheory.RgHe.A.Pf
