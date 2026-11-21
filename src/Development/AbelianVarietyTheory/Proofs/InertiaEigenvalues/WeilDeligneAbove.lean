import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange

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
