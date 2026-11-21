import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField

section
namespace GlobalTheory.ShiftVariables

noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)

theorem shiftVars_X (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental (↥k) c) :
    ∃ (σ : Ω ≃+* Ω), (∀ a ∈ k, (σ : Ω → Ω) a = a) ∧ (σ : Ω → Ω) c = c + (1 : Ω) := by
  classical
  have hs : AlgebraicIndepOn (↥k) id ({c} : Set Ω) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hc)
  obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset hs
  have hind : AlgebraicIndependent (↥k) ((↑) : t → Ω) := ht.1
  set K := IntermediateField.adjoin (↥k) (Set.range ((↑) : t → Ω)) with hK
  let e := hind.aevalEquivField
  let φ : FractionRing (MvPolynomial t ↥k) ≃ₐ[↥k] FractionRing (MvPolynomial t ↥k) :=
    IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial t ↥k))
      (L := FractionRing (MvPolynomial t ↥k)) (shiftVars t ↥k)
  let τ : K ≃ₐ[↥k] K := e.symm.trans (φ.trans e)
  have hmem : ∀ i : t, (i : Ω) ∈ K := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have he : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i)) = ⟨i, hmem i⟩ := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have he1 : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i + 1)) =
      ⟨i, hmem i⟩ + 1 := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have hτ : ∀ i : t, τ ⟨i, hmem i⟩ = ⟨i, hmem i⟩ + 1 := by
    intro i
    have h0 : e.symm ⟨i, hmem i⟩ = algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq, he]
    change e (φ (e.symm ⟨i, hmem i⟩)) = _
    rw [h0, IsFractionRing.algEquivOfAlgEquiv_algebraMap, shiftVars_X, he1]
  have : Algebra.IsAlgebraic K Ω := ht.isAlgebraic_field
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω τ.toRingEquiv
  have hσ : ∀ y : K, σ (y : Ω) = (τ y : Ω) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ.toRingEquiv y
  refine ⟨σ, fun a ha => ?_, ?_⟩
  · have hak : a ∈ K := IntermediateField.algebraMap_mem K (⟨a, ha⟩ : ↥k)
    have h1 := hσ ⟨a, hak⟩
    have h2 : τ ⟨a, hak⟩ = ⟨a, hak⟩ := τ.commutes (⟨a, ha⟩ : ↥k)
    rw [h2] at h1
    exact h1
  · have hc' : c ∈ t := hct rfl
    have h1 := hσ ⟨c, hmem ⟨c, hc'⟩⟩
    rw [hτ ⟨c, hc'⟩] at h1
    simpa using h1

end GlobalTheory.ShiftVariables
end

section
open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

theorem coeff_prod_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω)
    (S : Finset Ω) (hS : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) (n : ℕ) :
    (∏ x ∈ S, (X - C x)).coeff n ∈ k := by
  apply mem_of_forall_ringEquiv_fixed k
  intro σ hσ
  have hmap : S.map σ.toEquiv.toEmbedding = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact hS σ hσ x hx
    · simp
  have hP : (∏ x ∈ S, (X - C x)).map (σ : Ω →+* Ω) = ∏ x ∈ S, (X - C x) := by
    rw [Polynomial.map_prod]
    conv_rhs => rw [← hmap]
    rw [Finset.prod_map]
    simp
  have := congrArg (fun P => Polynomial.coeff P n) hP
  simpa [Polynomial.coeff_map] using this

theorem main : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω) (S : Finset Ω),
    (∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) → ∀ n,
      (∏ x ∈ S, (X - C x)).coeff n ∈ k :=
  fun _ _ _ _ k S hS n => coeff_prod_mem k S hS n

end GlobalTheory.FixedRoots
end
