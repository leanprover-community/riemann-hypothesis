module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
public import Development.EtaleCohomology.DivisorCycles.ChainPf
public import Development.EtaleCohomology.DivisorCycles.ConjugateIdempotents
public import Development.EtaleCohomology.DivisorCycles.CycleCount2
public import Development.EtaleCohomology.DivisorCycles.DegPoly2
public import Development.EtaleCohomology.DivisorCycles.ExpVanPf
public import Development.EtaleCohomology.DivisorCycles.GenSpecProof
public import Development.EtaleCohomology.DivisorCycles.MatUnitsOf
public import Development.EtaleCohomology.DivisorCycles.SpecPtPf
public import Development.EtaleCohomology.DivisorCycles.SumMulSum
public import Development.EtaleCohomology.DivisorCycles.TangentDegree
public import Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
public import Development.EtaleCohomology.DivisorCycles.TangentIndexDvd
public import Development.EtaleCohomology.DivisorCycles.TorusPtPf
public import Development.EtaleCohomology.DivisorCycles.UnipotentPartTrivial
public import Development.EtaleCohomology.DivisorCycles.UnitFactorizationTheorem
public import Development.EtaleCohomology.DivisorCycles.ZclMulPf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace LateralTheory.Fin.Key
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem etale_idempotent_conjugacy_of_key : LateralTheory.DivDb.IdemConj := by
  apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key
theorem etale_unit_factorization_of_key : LateralTheory.DivDb.UnitFactorization := by
  apply LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_zariski_closure_mul_closed_of_key : LateralTheory.DivDb.ZclMul := by
  apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_tangent_index_divides_of_key : LateralTheory.DivDb.TanIndex := by
  apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_unipotent_part_trivial_of_key : LateralTheory.DivDb.Unip := by
  apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key
theorem etale_generic_spectrum_of_key : LateralTheory.DivDb.GenSpec := by
  apply LateralTheory.DivDb.GenSpecProof.GenSpec_of
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_torus_point_exists_of_key : LateralTheory.DivDb.TorusPt := by
  apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCount₂.CycleCount_of
theorem etale_divisibility_key_criterion_of_components : LateralTheory.DivDb.Key := by
  apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski_closure_mul_closed_of_key | exact etale_generic_spectrum_of_key | exact etale_torus_point_exists_of_key | exact etale_tangent_degree_bound_of_key | exact etale_cycle_count_eigenvalues_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Key := etale_divisibility_key_criterion_of_components
end LateralTheory.Fin.Key
