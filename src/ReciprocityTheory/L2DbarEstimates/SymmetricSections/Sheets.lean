module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem sheets : sheetsStatement.{u} := by
  intro n M _ z U u hcov w hw hfin
  obtain ⟨_, W, hwW, hW, _, H, hH⟩ := hcov w hw
  have : Finite (z ⁻¹' {w}) := hfin.to_subtype
  let e : Fin (Nat.card (z ⁻¹' {w})) ≃ (z ⁻¹' {w}) := (Finite.equivFin _).symm
  classical
  let s : Fin (Nat.card (z ⁻¹' {w})) → V n → M :=
    fun i v => if hv : v ∈ W then (H.symm (⟨v, hv⟩, e i)).1 else (e i).1
  have hs : ∀ i v (hv : v ∈ W), s i v = (H.symm (⟨v, hv⟩, e i)).1 := fun i v hv => dif_pos hv
  have hzs : ∀ i, ∀ v ∈ W, z (s i v) = v := by
    intro i v hv
    rw [hs i v hv]
    have := hH (H.symm (⟨v, hv⟩, e i))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hinj : ∀ v (hv : v ∈ W) i j, s i v = s j v → i = j := by
    intro v hv i j hij
    rw [hs i v hv, hs j v hv] at hij
    have h2 := congrArg (fun y => (H y).2)
      (Subtype.ext hij : H.symm (⟨v, hv⟩, e i) = H.symm (⟨v, hv⟩, e j))
    simp only [Homeomorph.apply_symm_apply] at h2
    exact e.injective h2
  have hsurj : ∀ v (hv : v ∈ W) (y : M), z y = v → ∃ i, s i v = y := by
    intro v hv y hy
    have hyW : y ∈ z ⁻¹' W := by
      show z y ∈ W
      rw [hy]; exact hv
    refine ⟨e.symm (H ⟨y, hyW⟩).2, ?_⟩
    rw [hs _ v hv]
    simp only [Equiv.apply_symm_apply]
    have h1 : (H ⟨y, hyW⟩).1 = ⟨v, hv⟩ := Subtype.ext (by rw [hH]; exact hy)
    have h3 : H.symm (⟨v, hv⟩, (H ⟨y, hyW⟩).2) = ⟨y, hyW⟩ := by
      rw [← h1]; simp
    rw [h3]
  refine ⟨W, Nat.card (z ⁻¹' {w}), s, hW, hwW, ?_, hzs, ?_⟩
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have : W.domRestrict (s i) = fun v : W => (H.symm (v, e i)).1 := by
      funext v
      exact hs i v.1 v.2
    rw [this]
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · intro v hv
    have hfv : (z ⁻¹' {v}).Finite := by
      refine (Set.finite_range fun i => s i v).subset ?_
      intro y hy
      obtain ⟨i, hi⟩ := hsurj v hv y hy
      exact ⟨i, hi⟩
    unfold fiberVals
    rw [dif_pos hfv]
    have hF : hfv.toFinset = Finset.univ.map ⟨fun i => s i v, fun i j h => hinj v hv i j h⟩ := by
      ext y
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
      constructor
      · intro hy; exact hsurj v hv y hy
      · rintro ⟨i, rfl⟩; exact hzs i v hv
    rw [hF, Finset.map_val, Multiset.map_map]
    rfl

end ReciprocityTheory.L2DbarEstimates.Norm
