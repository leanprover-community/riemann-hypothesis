module

public import Development.EtaleCohomology.TateTwists.TensorVanishing
public import Development.EtaleCohomology.TateTwists.ColumnOf
public import Development.EtaleCohomology.TateTwists.StepPf
public import Development.EtaleCohomology.TateTwists.acycIffPf
public import Development.EtaleCohomology.TateTwists.conePf
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

namespace LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
theorem etale_complex_acyclic_iff_local_exactness : LateralTheory.EtaleFoundations.acyc.acycIff := by
  apply LateralTheory.EtaleFoundations.acyc.acycIff_of
theorem etale_tensor_column_acyclic_of_flat : LateralTheory.EtaleFoundations.acyc.column := by
  apply LateralTheory.EtaleFoundations.acyc.column_of
theorem etale_tensor_staircase_lifting_inductive : LateralTheory.EtaleFoundations.stairPf.Step := by
  apply LateralTheory.EtaleFoundations.StepPf.Step_of
theorem etale_tensor_acyclic_of_staircase_lifting : LateralTheory.EtaleFoundations.acyc.stair := by
  apply LateralTheory.EtaleFoundations.acyc.stair_of <;> first | exact etale_tensor_staircase_lifting_inductive
theorem etale_tensor_acyclic_cone_of_flat : LateralTheory.EtaleFoundations.tqis.acyc := by
  apply LateralTheory.EtaleFoundations.tqis.acyc_of <;> first | exact etale_complex_acyclic_iff_local_exactness | exact etale_tensor_column_acyclic_of_flat | exact etale_tensor_acyclic_of_staircase_lifting
theorem etale_tensor_mappingCone_commutes : LateralTheory.EtaleFoundations.tqis.cone := by
  apply LateralTheory.EtaleFoundations.tqis.cone_of
theorem etale_tensor_quasiIso_of_acyclic_cone : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  apply LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone <;> first | exact etale_tensor_acyclic_cone_of_flat | exact etale_tensor_mappingCone_commutes
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_quasiIso_of_acyclic_cone
end LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso
