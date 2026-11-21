import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_rep_unique_base_change : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, mapRep (iotaOQ D.nd D.naut i) (r x) g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.BaseChangeConj.rep_conj_of_baseChange | exact GlobalTheory.BaseChangeConj.rep_conj_of_baseChange | (intros; apply GlobalTheory.BaseChangeConj.rep_conj_of_baseChange <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.HubX.lgcG_of_adm : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.HubX.LgcG D := by
  intro D ht h1 h2 h5 i r hr w _hwS hwg x
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, hl⟩ := GlobalTheory.T.exists_galois_rep_base_change D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.galois_rep_unique_base_change D h5 i r hr x P Pa hP hPa ρ hc hss (fun w _ => hwd w)
  refine ⟨P, hP, ?_⟩
  obtain ⟨k, hk⟩ := hwg
  have hsp : IsSplitPl D.host w :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
  rw [← hPa.2.2.2.1 w hsp, ← hwd w]
  have hok : SumRepresentations.At.WDok D.nd D.naut i ρ w := by
    by_cases hwl : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hl w hwl).1
    · exact Or.inl hwl
  exact ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w hok
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_all : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.HubX.LgcG D := by
  atlas_forward_decl GlobalTheory.HubX.lgcG_of_adm
end
