import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial

namespace GlobalTheory.TypeAbove

theorem conj_over_split (D : D7) {p : ℕ} {w w' : PlE D.host} (hw : w ∈ placesOver D.host.E p)
    (hs : IsSplitPl D.host w) (hc : IsConjPl D.host w w') :
    w' ∈ placesOver D.host.E p ∧ IsSplitPl D.host w' := by
  have h := (GlobalTheory.ConjPlaceOff.isConjPl_iff D w w').1 hc
  refine ⟨?_, ?_⟩
  · have e := (h ((p : ℕ) : 𝓞 D.host.E)).1 hw
    rwa [map_natCast] at e
  · obtain ⟨x, hx, hcx⟩ := (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w).1 hs
    exact (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w').2 ⟨_, (h x).1 hx, fun h' => hcx ((h _).2 h')⟩

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.admDZ P → SumRepresentations.tie0 D → WDAbove D → TypeLGC P := by
  intro D P hDZ _ hWD i k hl r hr x PI hPI v τ hτ hsq hroot
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  refine ⟨u, hu, ?_⟩
  have key : ∀ w, w ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host w →
      D.naut.mono0 (D.naut.locV i PI w) →
      (D.naut.items₂ k w (D.naut.locV i PI w)).natDegree = D.R.nV →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w))).map
            fun y => X - C (P.om k w y σ)).prod := by
    intro w hw hs hm hdeg
    have hwl : w ∈ placesOver D.host.E (D.nd.l i) := hl ▸ hw
    obtain ⟨hdR, heq⟩ := hWD i r hr x PI hPI w hwl hs
    have hdim : D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := by
      have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) (r x)) w
      rwa [heq, D.naut.lpDim_tw] at h
    refine ⟨hdR, ?_, fun σ hσ => ?_⟩
    · rw [heq, D.naut.monomial_twist_iff]; exact hm
    · rw [heq, D.naut.inePol_tw _ _ σ hσ]
      exact P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) σ hσ
  intro w M hwM
  rcases hwM with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · have hdeg : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v))).natDegree = D.R.nV := by
      rw [hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
        ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      rfl
    have h := key _ (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hm0 hdeg
    rw [hlab] at h
    exact h
  · obtain ⟨hw, hs⟩ := conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    have h := key w hw hs hm hdeg
    rw [hroots] at h
    exact h

end GlobalTheory.TypeAbove
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_local_global : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.admDZ P → SumRepresentations.tie0 D → WDAbove D → TypeLGC P := by
  first | exact @GlobalTheory.TypeAbove.main | exact GlobalTheory.TypeAbove.main | (intros; apply GlobalTheory.TypeAbove.main <;> assumption)
end

section
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.WDAboveProof

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WDAbove D := by
  intro D hT h1 h2 h5 i r hr x PI hPx w hw hsp
  obtain ⟨Pa, hB⟩ := h1 i PI
  obtain ⟨ρ, hρc, hρs, hρw⟩ := GlobalTheory.T.exists_galois_rep_base_change_twist D hT h2 i PI Pa hB
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x PI Pa hPx hB ρ hρc hρs
    (fun w' _ => (hρw w').2)
  have hc := (hT.2.2.2.2.2 i).2.1 D.R.nV ρ _ hρc Pm hPm
  have hdR : D.naut.IsdRW i ρ w := ((hρw w).1).resolve_left (not_not.2 hw)
  refine ⟨(hc.1 w hw).2 hdR, ?_⟩
  rw [hc.2.1 w (hρw w).1, (hρw w).2, hB.2.2.2.1 w hsp]

end GlobalTheory.WDAboveProof
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_above : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WDAbove D := by
  atlas_forward_decl GlobalTheory.WDAboveProof.main
end

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.Pass.stepType_proof : StepType := by
  intro D P hDZ h0 h1 h2 h5
  exact GlobalTheory.T.type_local_global D P hDZ h0 (GlobalTheory.T.weil_deligne_above D h0 h1 h2 h5)
end
