import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CarHyp.Model

open GlobalTheory.TheRec

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}

omit [IsCMField E] in

theorem isRec_of_isTheRec (hL : GlobalTheory.Published.LocalLanglandsGL) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsTheRec h rc) : IsRec h rc := by
  obtain ⟨rc', h', -⟩ := hL.1 E Ω A w h
  rwa [← H.2 rc' h'.toLit]

theorem caraianiLocalGlobal_of_dual₂ (hL : GlobalTheory.Published.LocalLanglandsGL) (H : GlobalTheory.Published.CaraianiLocalGlobalDual)
    (hd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a),
      GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
      ∃ π' : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π' ∧ GKCoh.IsCohomological π' ∧
        ∀ w σ σ', π.IsLocComp w σ → Nonempty (σ'.ρ.Equiv (SmGL.contra σ.ρ)) → π'.IsLocComp w σ') :
    GlobalTheory.Published.CaraianiAboveLHyp := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh R hR P AI hT w A h O _ _ _ Bw hj hp σ σ' hσ hσ' rc hrc
  obtain ⟨π', c', coh', loc'⟩ := hd E a π hc hcoh
  obtain ⟨R', h1, h2, h3, h4⟩ := H E Ω l ι a ha π' c' coh'
  obtain ⟨p, e⟩ := hR.2 R' ⟨h1, h2, fun w hl A h rc hrc σ σ' hσ _ hσ' =>
    (h3 w hl A h rc (isRec_of_isTheRec Ω hL hrc) σ' (loc' w σ σ' hσ hσ')).wdOf_eq hl⟩
  rw [← (GlobalTheory.PstConj.main E Ω l ι a P AI hT w A h O Bw hj (R.comp (Dec (F := E) A).subtype)
    (R'.comp (Dec (F := E) A).subtype) p (fun g => e g) hp).2]
  exact (h4 P AI hT w A h O Bw hj).2 σ' (loc' w σ σ' hσ hσ') rc (isRec_of_isTheRec Ω hL hrc)

theorem locRep_triv (w : HeightOneSpectrum (𝓞 E)) (g) (φ : (CuspSub.triv E (le_refl 1)).V) :
    (CuspSub.triv E le_rfl).locRep w g φ = φ := by
  obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
  refine Subtype.ext ?_
  change act (.fin _) φ.1 = φ.1
  rw [← e]; rfl










end GlobalTheory.CarHyp.Model

end
