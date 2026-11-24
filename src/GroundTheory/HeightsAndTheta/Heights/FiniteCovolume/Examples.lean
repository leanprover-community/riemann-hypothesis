module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section General

variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

theorem lineIndex_smul {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by
  let f : W →+ W := ((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom
  have hf : Function.Injective f := (γ : W ≃ₗ[E] W).injective
  have hfx : ∀ y : W, f y = γ • y := fun y => rfl
  have h1 : (ringMultiples E x).map f = ringMultiples E (γ • x) := by
    rw [ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]
    congr 1
    ext a
    simp only [AddMonoidHom.comp_apply, hfx]
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  have h2 : La.map f = La := by
    conv_rhs => rw [← hγ]
    change La.map f = (γ : W ≃ₗ[E] W) • La
    rw [AddSubgroup.pointwise_smul_def]
    rfl
  have h3 : ((Submodule.span E {x}).toAddSubgroup).map f =
      (Submodule.span E {γ • x}).toAddSubgroup := by
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [hfx, smul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩
  unfold lineIndex
  conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rw [AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]

end General

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
