module

public import Development.EtaleCohomology.KummerTheory.LimitPf
public import Development.EtaleCohomology.KummerTheory.LimAssemblePf
public import Development.EtaleCohomology.KummerTheory.LimExtHlPf
public import Development.EtaleCohomology.KummerTheory.LimLHPf
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

@[expose] public section

namespace LateralTheory.Fin.Limit
theorem etale_limit_extension_groups_henselian_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimExtHl := by
  apply LateralTheory.KummerTheory.LimExtHl_of
theorem etale_limit_local_homotopy_compatible_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimLH := by
  apply LateralTheory.KummerTheory.LimLHPf.LimLH_of
theorem etale_limit_cohomology_assembled_from_stages : LateralTheory.KummerTheory.LimAssemble := by
  apply LateralTheory.KummerTheory.LimAssemble_of
theorem etale_cohomology_commutes_with_inverse_limits : LateralTheory.KummerTheory.Limit := by
  apply LateralTheory.KummerTheory.Limit_of <;> first | exact etale_limit_extension_groups_henselian_in_inverse_limits_assembly | exact etale_limit_local_homotopy_compatible_in_inverse_limits_assembly | exact etale_limit_cohomology_assembled_from_stages
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Limit := etale_cohomology_commutes_with_inverse_limits
end LateralTheory.Fin.Limit
