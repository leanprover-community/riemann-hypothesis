module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section

namespace GlobalTheory

open Matrix Polynomial
open scoped BigOperators

theorem essFiniteType_of_finiteDimensional_subfield_closure {o Om : Type*} [CommRing o]
    [IsDomain o] [Field Om] [Algebra o Om] [FaithfulSMul o Om] {T : Set Om} (hT : T.Finite)
    (h : FiniteDimensional (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) Om) :
    Algebra.EssFiniteType o Om := by
  let K := FractionRing o
  letI : Algebra K Om := FractionRing.liftAlgebra o Om
  haveI : Algebra.EssFiniteType o K := .of_isLocalization K (nonZeroDivisors o)
  let E := IntermediateField.adjoin K T
  haveI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hT)
  have hle : Subfield.closure (Set.range (algebraMap o Om) ∪ T) ≤ E.toSubfield := by
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (IntermediateField.subset_adjoin K T))
    rintro _ ⟨x, rfl⟩
    rw [IsScalarTower.algebraMap_apply o K Om]
    exact E.algebraMap_mem _
  letI : Algebra (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om :=
    .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E Om :=
    .of_restrictScalars_finite (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om
  haveI : Algebra.EssFiniteType K Om := .comp K E Om
  exact .comp o K Om

end GlobalTheory
