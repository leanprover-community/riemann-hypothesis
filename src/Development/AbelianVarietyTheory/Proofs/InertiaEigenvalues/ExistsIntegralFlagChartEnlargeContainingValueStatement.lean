module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValue
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  first | exact @GlobalTheory.Reg.Enlarge.enlarge_exists | exact GlobalTheory.Reg.Enlarge.enlarge_exists | (intros; apply GlobalTheory.Reg.Enlarge.enlarge_exists <;> assumption)
