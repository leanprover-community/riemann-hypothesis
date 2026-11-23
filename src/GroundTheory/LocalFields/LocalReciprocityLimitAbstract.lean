module

public import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityAbelianizationRestrictReciprocityLimi
import GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.LocalField.Abstract

section TopologicalAbelianization

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)

theorem continuous_topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    Continuous (topologicalAbelianizationMap f hf) := by
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact (QuotientGroup.isQuotientMap_mk _).continuous.comp hf

end TopologicalAbelianization

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtype_val.subtype_mk _

def limitRestrict {K K' : OpenSubgroup G} (hK : K' ≤ K) :
    TopologicalAbelianization (K' : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) :=
  topologicalAbelianizationMap (Subgroup.inclusion hK) (continuous_inclusion hK)

@[simp]
theorem limitRestrict_mk {K K' : OpenSubgroup G} (hK : K' ≤ K) (g : (K' : Subgroup G)) :
    limitRestrict hK (g : TopologicalAbelianization (K' : Subgroup G)) =
      ((⟨g, hK g.2⟩ : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem limitRestrict_reciprocityLimit {K K' : OpenSubgroup G} (hK : K' ≤ K)
    (a : fixedModule A (K' : Subgroup G)) :
    limitRestrict hK (D.reciprocityLimit hax K' a) =
      D.reciprocityLimit hax K (norm A (K : Subgroup G) (K' : Subgroup G) a) := by
  refine D.eq_reciprocityLimit hax fun L hL _ => ?_
  have hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤
      commutator (K : Subgroup G) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hL' : IsAbelianExtension K' (L ⊓ K') := by
    refine ⟨inf_le_right, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have h1 := hL.commutator_le (hmap ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have := hL'.normal
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a
  rw [← hg, abelianizationRestrict_mk] at e
  rw [← hg, limitRestrict_mk, abelianizationRestrict_mk]
  have h := D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left
    (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')
  rw [galRestrict_mk, e, normTateZero_mk] at h
  exact h

end ClassFieldData

end GroundTheory.LocalField.Abstract
