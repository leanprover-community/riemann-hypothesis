module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem isNab_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → IsNab Xo c (fun {S} _ _ y k F α => (nab (twPt h y) k F α).val) := by
  intro E _ _ _ H Dw l Xo c ta h _ nab hn
  refine ⟨hn.1, fun S _ _ iQ y => ?_⟩
  letI : Algebra ℚ (Tw ta S) := iQ
  obtain ⟨C, h1, h2⟩ := hn.2 (Tw ta S) (twPt h y)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.GalTw
