module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
