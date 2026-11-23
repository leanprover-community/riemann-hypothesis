module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.MultOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace ComplexConjugate ComplexStarModule
open Set Function

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2ProductCompleteness

set_option linter.unusedSectionVars false

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem eq_smul_one_of_commute_of_star [Nontrivial E] {S : Set (E →L[ℂ] E)}
    (hirr : ∀ W : Submodule ℂ E, IsClosed (W : Set E) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {T : E →L[ℂ] E} (hT : ∀ s ∈ S, Commute T s) (hT' : ∀ s ∈ S, Commute (star T) s) :
    ∃ c : ℂ, T = c • (1 : E →L[ℂ] E) := by
  have hre : ∀ s ∈ S, Commute (ℜ T : E →L[ℂ] E) s := by
    intro s hs
    rw [realPart_apply_coe]
    exact ((hT s hs).add_left (hT' s hs)).smul_left _
  have him : ∀ s ∈ S, Commute (ℑ T : E →L[ℂ] E) s := by
    intro s hs
    rw [imaginaryPart_apply_coe]
    exact (((hT s hs).sub_left (hT' s hs)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := ArchWhittaker.eq_algebraMap_of_commute hirr (ℜ T).2 hre
  obtain ⟨b, hb⟩ := ArchWhittaker.eq_algebraMap_of_commute hirr (ℑ T).2 him
  refine ⟨a + Complex.I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

end Schur

variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [Group G₁] [TopologicalSpace G₁]
  [Group G₂] [TopologicalSpace G₂]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (τ : UnitaryRep G V) (ι₁ : G₁ →* G) (ι₂ : G₂ →* G)
variable (D : Submodule ℂ V) [CompleteSpace D]

variable {τ ι₁ ι₂ D}


variable {v : V}





end GL2ProductCompleteness

end

end GroundTheory.Automorphic
