module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def SelfIso : Prop :=
  StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F),
    η ^ 2 = 1 → SelfTw π.HasSat η → IsoTwist π η

def BcAtt0 : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (Bc.res F Ω E)) → AttC ι (r.comp (Bc.res F Ω E)) P)

def BcConj0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (Bc.cPl w) B

end UpperTheory.V.Br
