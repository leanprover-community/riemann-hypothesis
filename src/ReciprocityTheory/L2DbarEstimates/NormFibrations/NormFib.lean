module

public import Mathlib.Topology.Covering.Basic
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ

theorem normFib : NormFibStatement.{u} := by
  intro n M _ z U hcov himg hfin hconn

  have hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard := by
    intro x
    obtain ⟨hd, W, hxW, hW, hzW, H, hH⟩ := hcov (z x) (himg x)
    have hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x}) :=
      fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩
    filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'
    exact Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  have hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard} := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
      rw [hx']
      exact hx
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx', hx]
  have hall := hS.eq_univ ⟨x0, rfl⟩
  refine ⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩
  rw [(hfin (z x0)).cast_ncard_eq]
  by_cases hy : ∃ x, z x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard := Set.eq_univ_iff_forall.1 hall x
    exact hx.le
  · have h0 : z ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hy ⟨x, h⟩
    rw [h0, Set.encard_empty]
    exact zero_le

end ReciprocityTheory.L2DbarEstimates
