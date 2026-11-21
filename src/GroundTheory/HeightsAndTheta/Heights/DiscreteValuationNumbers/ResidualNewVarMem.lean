import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsLast
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem ringKrullDim_quotient_le_comap_add_one {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {J : Type} {R : Type*} [CommRing R] [IsNoetherianRing R]
    (G' : Ideal (MRing (extIdx ι J) R)) [G'.IsPrime] (j₀ : J)
    (hY : ∀ j, j ≠ j₀ → (newVar j : MRing (extIdx ι J) R) ∈ G') :
    ringKrullDim (MRing (extIdx ι J) R ⧸ G') ≤
      ringKrullDim (MRing ι R ⧸ G'.comap (liftForm (J := J) (ι := ι) (R := R))) + 1 := by
  set G := G'.comap (liftForm (J := J) (ι := ι) (R := R)) with hGdef
  let φ : (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Ideal.quotientMap G' (liftForm (J := J) (ι := ι) (R := R)).toRingHom le_rfl
  let ψ : Polynomial (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Polynomial.eval₂RingHom φ (Ideal.Quotient.mk G' (newVar j₀))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (Ideal.Quotient.mk G (C a)), ?_⟩
      simp [ψ, φ, Ideal.quotientMap_mk, liftForm]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p v hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        by_cases hi : i = j₀
        · subst hi
          refine ⟨a * Polynomial.X, ?_⟩
          rw [map_mul, ha, map_mul]
          congr 1
          simp [ψ, newVar]
        · refine ⟨0, ?_⟩
          rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
          exact G'.mul_mem_left _ (hY i hi)
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk G (X ⟨k, i⟩)), ?_⟩
        rw [map_mul, ha, map_mul]
        congr 1
        simp [ψ, φ, Ideal.quotientMap_mk, liftForm, rename_X]
  calc ringKrullDim (MRing (extIdx ι J) R ⧸ G')
      ≤ ringKrullDim (Polynomial (MRing ι R ⧸ G)) := ringKrullDim_le_of_surjective ψ hψ
    _ = ringKrullDim (MRing ι R ⧸ G) + 1 := Polynomial.ringKrullDim_of_isNoetherianRing

theorem mem_minimalPrimes_of_ringKrullDim {A : Type*} [CommRing A] (P G : Ideal A) [P.IsPrime]
    [G.IsPrime] (s : A) (hsP : s ∉ P) (N : ℕ) (hP : ringKrullDim (A ⧸ P) = (N : WithBot ℕ∞))
    (hle : P ⊔ Ideal.span {s} ≤ G) (hG : (N : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ G) + 1) :
    G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
  refine ⟨⟨inferInstance, hle⟩, fun Q hQ hQG => ?_⟩
  have : Q.IsPrime := hQ.1
  by_contra hGQ
  have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hsP (h ▸ hsQ)
  have h1 := DimStrictDrop.proof A Q G (lt_of_le_not_ge hQG hGQ)
  have h2 := DimStrictDrop.proof A P Q hPQ
  have h3 : (N : WithBot ℕ∞) + 1 ≤ (N : WithBot ℕ∞) :=
    calc (N : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ G) + 1 + 1 := by gcongr
      _ ≤ ringKrullDim (A ⧸ Q) + 1 := by gcongr
      _ ≤ N := hP ▸ h2
  have h4 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : N + 1 ≤ N := by exact_mod_cast h4
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem residual_newVar_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof R (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfP hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hres; omega
  rintro (_ | _ | i) hj
  · exact absurd rfl hj
  · exact hY₁G'
  by_contra hYi
  have hrel : liftForm (powMonomial e i) * newVar (some none) -
      liftForm m * newVar (some (some i)) ∈ P' := by
    rw [hP'def, blowUpOf, RingHom.mem_ker]
    simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
    ring
  have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => hYi (hP'G' h)
  by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι R) ∈ P'
  · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
    rw [sub_sub_cancel] at h
    exact (hP'prime.mem_or_mem h).elim hlm hYiP'
  · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
    rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
    simp only [Pi.add_apply] at h1
    have h2 : divCycle P' (newVar (some (some i))) G' = 0 := by
      by_contra h; exact hYi (form_mem_of_divCycle_ne_zero h)
    have h3 := hnonneg (liftForm (powMonomial e i)) G'
    unfold ratDiv at hres; omega

theorem ResidualContractionComponent.proof (hpieces : BlowUpDecomposition.Statement.{u}) :
    ResidualContractionComponent.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', hsc', hsP', -⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have : P.IsPrime := hP.multiProj.isPrime
  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    by_contra h; unfold divCycle at hsG'; rw [dif_neg h] at hsG'; exact lt_irrefl _ hsG'
  have : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hY := residual_newVar_mem e hD.1.num_not_mem hmP hP'G' hresG'
  have hdim' := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) _ (d + 1) hP'
    (liftMDeg c) (liftForm s) hsc' hsP' G' hsG'.ne' hϖG'
  have hdim := ringKrullDim_quotient_le_comap_add_one G' none hY
  refine mem_minimalPrimes_of_ringKrullDim P _ s hsP (d + 1 + 1 + Fintype.card K) hP.dim ?_ ?_
  · refine sup_le (fun p hp => hP'G' ?_) ?_
    · rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hG'supp.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  · rw [Fintype.card_option, show d + 1 + (Fintype.card K + 1) = d + 1 + 1 + Fintype.card K by omega]
      at hdim'
    exact hdim' ▸ hdim

end GroundTheory.Heights₂.Heights.NumbersDVR
end
