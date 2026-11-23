module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExcBoundOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf
public import Formalism.LandauZeroFreeBounds.FinalSiegel
public import Formalism.LandauZeroFreeBounds.NoZeroComplex
import Formalism.ZeroFreeRegion.LogDerivRegion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.ZeroFreeDirichlet

theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet
