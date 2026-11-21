import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.ConjDual

theorem equiv_contra (hadm : IrreducibleAdmissibleGL) {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {π π' : CuspSub E a} (T : π.V ≃ₗ[ℂ] π'.V) (hT : ∀ o φ, T (π.op (conjOp o) φ) = π'.op o (T φ))
    (h : DualIsConj π) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h' : π'.IsLocComp w σ') (hσ : π.IsLocComp w σ) : Nonempty (σ.ρ.Equiv (GlobalTheory.SmGL.contra σ'.ρ)) := by
  obtain ⟨B, l, -, hf, -, -⟩ := h
  obtain ⟨f, f0, hfe⟩ := hσ
  have hT' : ∀ o φ, T.symm (π'.op o φ) = π.op (conjOp o) (T.symm φ) := fun o φ =>
    T.injective (by rw [hT, T.apply_symm_apply, T.apply_symm_apply])
  refine GlobalTheory.LocDual.equiv_contra_locComp hadm E a π'.V π'.stable π'.irred w σ' σ
    (((GlobalTheory.UnitaryBC.cuspSub_iff π').2.1 w σ').2 h') (B.flip.compl₁₂ T.symm.toLinearMap f) (fun e => f0 ?_) ?_
  · refine LinearMap.ext fun v => l _ fun ψ => ?_
    have := LinearMap.congr_fun (LinearMap.congr_fun e (T ψ)) v
    simpa using this
  · intro g φ ψ v e
    obtain rfl : ψ = π'.op (.fin (locGL E a w g)) φ := Subtype.ext e
    change B (f (σ.ρ g v)) (T.symm (π'.op _ φ)) = B (f v) (T.symm φ)
    rw [hT', hfe, CuspSub.locRep_eq, hf]


end GlobalTheory.ConjDual
