module

public import Development.EtaleCohomology.KummerTheory.PlaceStepPf
public import Development.EtaleCohomology.KummerTheory.AlgExtPf
public import Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
public import Development.EtaleCohomology.KummerTheory.PlacePfVal
public import Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
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

namespace LateralTheory.Fin.AlgExt
theorem etale_cohomology_place_restriction_good_reduction : LateralTheory.KummerTheory.PlaceResGood := by
  apply LateralTheory.KummerTheory.PlaceResGood_of
theorem etale_cohomology_place_localization_inductive_extension : LateralTheory.KummerTheory.PlaceStep := by
  apply LateralTheory.KummerTheory.PlaceStep_of <;> first | exact etale_cohomology_place_restriction_good_reduction
theorem etale_cohomology_place_localization_exists : LateralTheory.KummerTheory.PlaceEx := by
  apply LateralTheory.KummerTheory.PlaceEx_of_step <;> first | exact etale_cohomology_place_localization_inductive_extension
theorem etale_cohomology_place_localization_holds : LateralTheory.KummerTheory.Place := by
  apply LateralTheory.KummerTheory.Place_of_ex <;> first | exact etale_cohomology_place_localization_exists
theorem etale_cohomology_algebraic_extension_invariance_of_places : LateralTheory.KummerTheory.AlgExt := by
  apply LateralTheory.KummerTheory.AlgExt_of <;> first | exact etale_cohomology_place_localization_holds
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AlgExt := etale_cohomology_algebraic_extension_invariance_of_places
end LateralTheory.Fin.AlgExt
