module

public import Mathlib
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.L2 Formalism.L2.NT

def GoodCl (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w →
    (Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →
    ExpGood D I (avD D (avDesign D) (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D}

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

structure PhtOn {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (Wd : WDSide D T) (fr : OmFrame D)
    (p : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ), (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → Prop) : Prop where
  card : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (τ : D.host.E →+* Qbar l) (w : PlE D.host), p l a r →
    (∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) → Wd.IsdRW l ι r w → Multiset.card (Wd.jumpsW l ι r τ) = a

def PhtCmp : Prop :=
  ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T), PhtOn Wd fr fun l _ a r =>
    Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))

end GlobalTheory.HeightCounting

end
