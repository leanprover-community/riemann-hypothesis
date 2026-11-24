module

public import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
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
import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

theorem dim_le_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X ≤ max (topologicalKrullDim U) (topologicalKrullDim V) := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  obtain ⟨z, hz⟩ := Z.2.nonempty
  have hzu : z ∈ Set.range f ∪ Set.range g := hc ▸ Set.mem_univ z
  rcases hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map f hf.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hf.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_left
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map g hg.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hg.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_right

theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
