module

public import Development.EtaleCohomology.KummerTheory.AdicLimPf
public import Development.EtaleCohomology.KummerTheory.AdicAlgPf
public import Development.EtaleCohomology.KummerTheory.AdicLimPfGlue
public import Development.EtaleCohomology.WeilConjectures.AdicFinPf
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

@[expose] public section

namespace LateralTheory.Fin.AdicDeg
theorem etale_adic_cohomology_finiteness_holds : LateralTheory.KummerTheory.AdicFin := by
  apply LateralTheory.EWeil.AdicFinPf.AdicFin_of
theorem etale_adic_inverse_limit_comparison_holds : LateralTheory.KummerTheory.AdicLim := by
  apply LateralTheory.KummerTheory.AdicLim_of_fin <;> first | exact etale_adic_cohomology_finiteness_holds
theorem etale_adic_algebraic_comparison_holds : LateralTheory.KummerTheory.AdicAlg := by
  apply LateralTheory.KummerTheory.AdicAlg_of
theorem etale_adic_degree_bound_of_adic_finiteness : LateralTheory.KummerTheory.AdicDeg := by
  apply LateralTheory.KummerTheory.AdicDeg_of <;> first | exact etale_adic_inverse_limit_comparison_holds | exact etale_adic_algebraic_comparison_holds
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AdicDeg := etale_adic_degree_bound_of_adic_finiteness
end LateralTheory.Fin.AdicDeg
