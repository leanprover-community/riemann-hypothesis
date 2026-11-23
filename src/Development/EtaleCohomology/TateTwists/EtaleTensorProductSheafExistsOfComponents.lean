module

public import Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex
public import Development.EtaleCohomology.TateTwists.EtaleSheafTensorComplexExists
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

namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
