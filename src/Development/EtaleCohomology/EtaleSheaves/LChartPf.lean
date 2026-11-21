import Development.EtaleCohomology.EtaleSheaves.HensIdemCut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

section
noncomputable section
open Polynomial

namespace LateralTheory.E.LFactorPf

def LEtaleLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ ψ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp ψ = φ

theorem LFactor_of (hE : LEtaleLift) : LateralTheory.E.HensIdemCut.LFactor := by
  intro A _ I _ f g₀ h₀ hf hg hh hgh e
  rcases subsingleton_or_nontrivial (A ⧸ I) with hs | hs
  · have hI : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    have h1 : (1 : A) ∈ (⊥ : Ideal A).jacobson := HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top)
    have hu := Ideal.mem_jacobson_bot.mp h1 (-1)
    have hA : Subsingleton A := by
      simp at hu
      exact subsingleton_of_zero_eq_one (by simpa using hu)
    refine ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hn : f.natDegree = g₀.natDegree + h₀.natDegree := by
    rw [← hg.natDegree_mul hh, ← e, hf.natDegree_map]
  let p : MonicDegreeEq A f.natDegree := .mk f hf rfl
  have e' : g₀ * h₀ = p.1.map (algebraMap A (A ⧸ I)) := e.symm
  let φ := (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) _ _ hn p).symm
    ⟨(.mk g₀ hg rfl, .mk h₀ hh rfl), e', hgh⟩
  obtain ⟨ψ, hψ⟩ := hE A I _ φ
  let q := UniversalCoprimeFactorizationRing.homEquiv A _ _ hn p ψ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_⟩
  · have := q.2.1
    simpa [p] using this.symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm

end LateralTheory.E.LFactorPf
end
end

section
noncomputable section

namespace LateralTheory.E.LEtaleLiftPf

def LChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Algebra.IsStandardEtale A (Localization.Away g)

theorem LEtaleLift_of (hC : LChart) : LateralTheory.E.LFactorPf.LEtaleLift := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hS⟩ := hC A I A' φ
  let φ' : Localization.Away g →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale I (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I) (fun b => (Ideal.Quotient.eq_zero_iff_mem).symm) φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom A A' _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A' _ a)).trans (show φ' (algebraMap A' _ a) = φ a by simp [φ'])

end LateralTheory.E.LEtaleLiftPf
end
end

section
noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I HenselianRing.jac (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
end
end
