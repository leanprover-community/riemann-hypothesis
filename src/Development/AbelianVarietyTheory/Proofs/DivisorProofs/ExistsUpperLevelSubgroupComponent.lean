module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
