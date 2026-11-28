module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.Module.Card
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.Tactic.Algebraize
public import Lib.Speed

/-!
# Extending embeddings of countable rings into ℂ

This file compares embeddings of a countable ring into `ℂ` and into other fields. Two embeddings,
into `ℂ` and into an algebraically closed field of the same cardinality, differ by an isomorphism
of the fields, and an embedding into `ℂ` extends along an embedding into a field of cardinality at
most that of `ℂ`.

## Main definitions and results

* `New.exists_ringEquiv_extend`: two embeddings of a countable ring, into `ℂ` and into an
  algebraically closed field of the same cardinality, are matched by an isomorphism of the fields
  (Steinitz's classification, relative to the ring).
* `New.exists_ringHom_complex_extend` lets one view a point over a field of cardinality at most that
  of ℂ as a complex point, compatibly with given embeddings of a countable base ring in the field
  and in ℂ.

## Relation to the literature

The isomorphisms of fields come from Steinitz's theorem.
-/

@[expose] public section

/-! ## Steinitz's theorem relative to a countable ring -/

section ExtendEmbedding

open Cardinal IsAlgClosed

/-- Let `K` be a countable ring, `L` an algebraically closed field with the cardinality of `ℂ`, and
`f : K → ℂ`, `g : K → L` injective ring maps. Then some isomorphism `σ : ℂ ≃+* L` satisfies
`σ ∘ f = g`.

A form of Steinitz's theorem (characteristic and cardinality determine an uncountable algebraically
closed field up to isomorphism), refined so that the isomorphism respects the given embeddings. -/
lemma New.exists_ringEquiv_extend {L : Type} {K : Type*} [Field L] [IsAlgClosed L] [CommRing K]
    [Countable K] (h_mk : #ℂ = #L) (f : K →+* ℂ) (g : K →+* L)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : ℂ ≃+* L, ∀ a : K, σ (f a) = g a := by
  -- Use the two embeddings to regard the ambient fields as faithful `K`-algebras.
  -- Countability of `K` and uncountability of the fields ensure that the transcendence
  -- bases have the cardinalities of their respective ambient fields.
  algebraize [f, g]
  have : FaithfulSMul K ℂ := (faithfulSMul_iff_algebraMap_injective K ℂ).2 hf
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 hg
  have : Nontrivial K := f.domain_nontrivial
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  have h_uncountable : ℵ₀ < #ℂ := by simp [aleph0_lt_continuum]
  have hs_card : #ℂ = #s := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs mk_le_aleph0
      h_uncountable
  have ht_card : #L = #t := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht mk_le_aleph0
      (h_uncountable.trans_eq h_mk)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (by rw [← hs_card, ← ht_card, h_mk])
  -- Algebraic independence identifies the two generated subalgebras with polynomial rings.
  -- Renaming variables along the bijection gives the isomorphism over `K` that extends to
  -- the algebraic closures. Compatibility with the embeddings follows from `K`-linearity.
  let Ks : Subalgebra K ℂ := Algebra.adjoin K (Set.range (Subtype.val : s → ℂ))
  let Kt : Subalgebra K L := Algebra.adjoin K (Set.range (Subtype.val : t → L))
  let φ : Ks ≃ₐ[K] Kt :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv K e).trans ht.1.aevalEquiv)
  have : IsAlgClosure Ks ℂ := isAlgClosure_of_transcendence_basis Subtype.val hs
  have : IsAlgClosure Kt L := isAlgClosure_of_transcendence_basis Subtype.val ht
  refine ⟨IsAlgClosure.equivOfEquiv ℂ L φ.toRingEquiv, fun a ↦ ?_⟩
  -- `f` and `g` are the structure maps of the `K`-algebras `ℂ` and `L`
  calc _ = algebraMap Kt L (φ (algebraMap K Ks a)) :=
      IsAlgClosure.equivOfEquiv_algebraMap ℂ L φ.toRingEquiv (algebraMap K Ks a)
    _ = g a := by rw [φ.commutes]; rfl

end ExtendEmbedding

/-! ## Extension of embeddings of a countable ring into ℂ -/

section ComplexExtension

open Cardinal

/-- Let `D` be a countable ring, `K` a field with `#K ≤ #ℂ`, and `f : D → K`, `φ : D → ℂ`
injective ring maps. Then `φ` extends along `f` to a ring map `ψ : K → ℂ`. -/
lemma New.exists_ringHom_complex_extend {D : Type*} {K : Type} [CommRing D] [Countable D] [Field K]
    {f : D →+* K} {φ : D →+* ℂ} (hf : Function.Injective f) (hφ : Function.Injective φ)
    (h_le : #K ≤ #ℂ) :
    ∃ ψ : K →+* ℂ, ψ.comp f = φ := by
  -- The algebraic closure `L` of `K(X_z : z ∈ ℂ)` contains `K` and has the cardinality of `ℂ`, so
  -- some isomorphism `σ : ℂ ≃ L` is compatible with the two embeddings of the countable ring `D`.
  let F : Type := FractionRing (MvPolynomial ℂ K)
  let L : Type := AlgebraicClosure F
  -- a fraction field has the cardinality of the ring, which is `max (max #ℂ #K) ℵ₀`
  have hF : #F = #ℂ := by simp [F, aleph0_le_continuum, h_le.trans_eq mk_complex]
  have h_card : #ℂ = #L := by
    rw [← hF]
    refine le_antisymm (by simpa using mk_le_of_module F L) ?_
    simpa [hF, aleph0_le_continuum] using Algebra.IsAlgebraic.cardinalMk_le_max F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend h_card φ ((algebraMap K L).comp f) hφ
    ((algebraMap K L).injective.comp hf)
  exact ⟨(σ.symm : L →+* ℂ).comp (algebraMap K L),
    RingHom.ext fun a ↦ σ.symm_apply_eq.2 (hσ a).symm⟩

end ComplexExtension
