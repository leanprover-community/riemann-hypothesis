import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepOfPolarizedPairOfHyps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V


variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eq_of_unr {x y : WD h} (hy : y.unr) (hp : ∀ g : ↥(Weil h), x.charPol g = y.charPol g) (hm : x.mono0) : x = y := by
  have hd : x.lpDim = y.lpDim := by rw [← WD.charPol_natDegree x 1, hp, WD.charPol_natDegree]
  have hx : x.unr := (WD.unr_iff_ine x).2 ⟨hm, fun σ hσ => by
    have := ((WD.unr_iff_ine y).1 hy).2 σ hσ
    rw [WD.inePol_of_mem_Ine _ hσ] at this ⊢
    rw [hp, this, hd]⟩
  rw [WD.unr_eq_lpUnr x hx, WD.unr_eq_lpUnr y hy, WD.frobEig, WD.frobEig, WD.eig, WD.eig, hp]

theorem unr_algNorm {a : ℕ} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (algNorm σ)).unr := by
  rw [rec_algNorm hrc, WD.unr_tw]
  exact unr_rec_of_hasSat hrc σ S hS


variable [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}



end UpperTheory.GalN.V
