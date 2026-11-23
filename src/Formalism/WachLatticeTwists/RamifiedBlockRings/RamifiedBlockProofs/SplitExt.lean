module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.CharacterColumnKernels.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

theorem exists_ramification (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) [IsLocalHom (algebraMap O O')] :
    ∃ e : ℕ, ∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hφϖ0 : algebraMap O O' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hφϖnu : ¬ IsUnit (algebraMap O O' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ0 hϖ'
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hφϖnu
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  refine ⟨e, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp [he0, ENat.mul_top]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    have hu : IsDiscreteValuationRing.addVal O' (algebraMap O O' (u : O)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map _)
    simp only [map_mul, map_pow, hv, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_uniformizer hϖ']
    simp only [zero_add, nsmul_eq_mul, mul_one]
    ring



end Formalism.RepresentationBoundsCohomology.ringDataObjects
