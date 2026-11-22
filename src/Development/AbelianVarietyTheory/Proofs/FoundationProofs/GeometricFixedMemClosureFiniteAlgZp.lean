module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.GeoFix

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_finset_of_mem_closure (R A : Set Ω) {x : Ω} (hx : x ∈ Subfield.closure (R ∪ A)) :
    ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ x ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
  classical
  have mono : ∀ {S S' : Finset Ω}, S ⊆ S' →
      Subfield.closure (R ∪ (S : Set Ω)) ≤ Subfield.closure (R ∪ (S' : Set Ω)) := fun h =>
    Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))
  have two : ∀ {y z : Ω}, (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ z ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω)) ∧
        z ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
    rintro y z ⟨S, hS, hy⟩ ⟨S', hS', hz⟩
    refine ⟨S ∪ S', ?_, mono Finset.subset_union_left hy, mono Finset.subset_union_right hz⟩
    rw [Finset.coe_union]; exact Set.union_subset hS hS'
  let F : Subfield Ω :=
    { carrier := {y | ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, mul_mem h1 h2⟩
      one_mem' := ⟨∅, by simp, one_mem _⟩
      add_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, add_mem h1 h2⟩
      zero_mem' := ⟨∅, by simp, zero_mem _⟩
      neg_mem' := fun {a} ⟨S, hS, h1⟩ => ⟨S, hS, neg_mem h1⟩
      inv_mem' := fun a ⟨S, hS, h1⟩ => ⟨S, hS, inv_mem h1⟩ }
  have hle : Subfield.closure (R ∪ A) ≤ F := by
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · exact ⟨∅, by simp, Subfield.subset_closure (Or.inl hy)⟩
    · refine ⟨{y}, by simpa using hy, Subfield.subset_closure (Or.inr (by simp))⟩
  exact hle hx

end GlobalTheory.K5.GeoFix
