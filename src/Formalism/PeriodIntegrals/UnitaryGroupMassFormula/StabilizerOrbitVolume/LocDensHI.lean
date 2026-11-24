module

public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (Λ L : AddSubgroup V) (hΛL : Λ ≤ L)
    (hL : MeasurableSet (L : Set V)) (hΛ : MeasurableSet (Λ : Set V)) (hfin : Λ.relIndex L ≠ 0) :
    μ L = (Λ.relIndex L : ENNReal) * μ Λ := by
  have emb : MeasurableEmbedding ((↑) : L → V) := MeasurableEmbedding.subtype_coe hL
  have hadd : ∀ g : L, Measurable (fun x : L => g + x) := fun g =>
    ((measurable_const_add (g : V)).comp measurable_subtype_coe).subtype_mk
  have : MeasurableAdd L := ⟨hadd, fun g =>
    ((measurable_add_const (g : V)).comp measurable_subtype_coe).subtype_mk⟩
  have : (Λ.addSubgroupOf L).FiniteIndex := ⟨hfin⟩
  have : (μ.comap ((↑) : L → V)).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (hadd g) hs, emb.comap_apply, emb.comap_apply]
    have e : ((↑) : L → V) '' ((fun x : L => g + x) ⁻¹' s) =
        (fun x : V => (g : V) + x) ⁻¹' (((↑) : L → V) '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g + y, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hxL : x ∈ L := by
          have : x = (z : V) - g := by rw [hzx]; abel
          rw [this]
          exact L.sub_mem z.2 g.2
        refine ⟨⟨x, hxL⟩, ?_, rfl⟩
        have : g + (⟨x, hxL⟩ : L) = z := Subtype.ext (by simp [hzx])
        rw [this]
        exact hz
    rw [e, measure_preimage_add]
  have key := AddSubgroup.index_mul_measure (Λ.addSubgroupOf L)
    (measurable_subtype_coe hΛ) (μ.comap ((↑) : L → V))
  rw [emb.comap_apply, emb.comap_apply, Set.image_univ, Subtype.range_coe] at key
  have e2 : ((↑) : L → V) '' ((Λ.addSubgroupOf L : AddSubgroup L) : Set L) = Λ := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hΛL hx⟩, hx, rfl⟩
  rw [e2] at key
  rw [← key]
  rfl

end PI.VolStabSW
