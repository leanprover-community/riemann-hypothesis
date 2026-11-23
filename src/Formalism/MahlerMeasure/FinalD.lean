module

public import Formalism.MahlerMeasure.LieRoots
import Formalism.MahlerMeasure.MahlerMeasureProofs.GaussRad
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieRoots
import Formalism.MahlerMeasure.MahlerMeasureProofs.MahlerK
public import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem smithZp : SmithZp := smith_form_p_adic_integers
theorem lieMat : LieMat := lieMat_of mahler_binomial_unit_ball
theorem lieRoots : LieRoots := lieRoots_of gauss_norm_multiplicative
theorem valuation_window_lower_bound : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
