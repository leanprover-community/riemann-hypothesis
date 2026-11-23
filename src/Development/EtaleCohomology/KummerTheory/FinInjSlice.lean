module

public import Development.EtaleCohomology.KummerTheory.InjSlicePf
public import Development.EtaleCohomology.KummerTheory.ForgetInjPf
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

namespace LateralTheory.Fin.InjSlice
theorem etale_forget_preservesInjectiveObjects : LateralTheory.KummerTheory.ForgetInj := by
  apply LateralTheory.KummerTheory.ForgetInj_of
theorem etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a : LateralTheory.KummerTheory.InjSlice := by
  apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.InjSlice := etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
end LateralTheory.Fin.InjSlice
