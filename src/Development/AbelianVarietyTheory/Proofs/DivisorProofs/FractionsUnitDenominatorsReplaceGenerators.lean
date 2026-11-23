module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
