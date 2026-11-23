module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionCharStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTermsStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
namespace GlobalTheory.Shin

theorem tensorInd_virt_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hp hs χ hχ
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    exact mem_zpowers_of_prime_card rfl hs
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G χ).1 hχ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb
  obtain ⟨Z, hZ, hZ1, hZ2⟩ := GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b
    ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩)
    ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G).1, by simp⟩)
  have hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hA
  have hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hB
  refine ⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩
  · intro g
    simp only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]
    ring
  · intro δ
    simp only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]

end GlobalTheory.Shin
