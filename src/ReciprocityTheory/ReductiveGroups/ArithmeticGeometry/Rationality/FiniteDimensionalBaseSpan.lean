module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype

theorem incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem baseSpan_eq_range (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h

theorem finrank_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
