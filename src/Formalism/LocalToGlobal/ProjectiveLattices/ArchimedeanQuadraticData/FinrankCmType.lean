module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix
open scoped ComplexConjugate

lemma conj_conj_emb {K : Type} [Field K] (φ : K →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

def cmEquiv {K : Type} [Field K] {ι : Type} (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    ι ⊕ ι ≃ (K →+* ℂ) :=
  Equiv.ofBijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (hinj h)
      · exfalso
        have h1 : ∃ i', σ i' = σ i := ⟨i, rfl⟩
        exact (hcm (σ i)).1 h1 ⟨j, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [this, conj_conj_emb]⟩
      · exfalso
        have h1 : ∃ i', σ i' = σ j := ⟨j, rfl⟩
        exact (hcm (σ j)).1 h1 ⟨i, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [← this, conj_conj_emb]⟩
      · have := congrArg ComplexEmbedding.conjugate h
        simp only [Sum.elim_inr, conj_conj_emb] at this
        exact congrArg Sum.inr (hinj this)
    · intro τ
      by_cases h : ∃ i, σ i = τ
      · obtain ⟨i, hi⟩ := h
        exact ⟨Sum.inl i, hi⟩
      · have h2 : ∃ i, σ i = ComplexEmbedding.conjugate τ := by
          by_contra h3
          exact h ((hcm τ).2 h3)
        obtain ⟨i, hi⟩ := h2
        refine ⟨Sum.inr i, ?_⟩
        simp only [Sum.elim_inr, hi, conj_conj_emb])

end Formalism.L2.Pj.FundamentalDomainD5
