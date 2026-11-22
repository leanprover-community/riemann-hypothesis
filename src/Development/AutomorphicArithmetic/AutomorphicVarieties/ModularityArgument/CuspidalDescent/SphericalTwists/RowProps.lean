module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def FrobPol (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
    (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = (B.map fun b => X - C b).prod

variable [IsAlgClosure E Ω] [IsCMField E]

end Defs

def GalAE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd → ∀ s : ℝ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
      ∀ B, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).HasSat w B → FrobPol ι r w (algSat a (normV w) B)

def SatTw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a) (s : ℝ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
    (CG.mk P).HasSat w B → (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).HasSat w (B.map (· * qPow w (-s)))

def SumAE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n c : ℕ) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ),
    (∀ i, 1 ≤ a i) → (∀ i, (P i).IsCsd) → (∀ i τ, (P i).HasInfChar τ (m i τ)) →
    (∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j) →
    ∃ f : G E Ω → (Qbar l)[X], (∀ j, Continuous fun g => (f g).coeff j) ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
      ∀ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
        ∀ σ : G E Ω, IsFrob A (normV w) σ → (f σ).map ι.toRingHom = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod

def SumAEOf : Prop := SatTw → GalAE → SumAE

def OnePart : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → SatTw → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n c : ℕ), 1 ≤ n →
    ∀ (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i)) (π : CuspSub E n), (∀ i, 1 ≤ a i ∧ 1 ≤ d i) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
      (CG.mk π).HasSat w (satTot w d S)) → c = 1 ∧ ∀ i, d i = 1

def Same : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (r : G E Ω →* GL (Fin n) (Qbar l)),
    Continuous r → AttC ι r π → ∀ U : Submodule ℂ (UA E n → ℂ), IsAutRepU U →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ GlobalTheory.LFun.HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) →
    (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
      ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt U φ lam ∧ π.HasInfChar φ (infOfWeight lam)

def UnlOf : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ, V.W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ →
      (∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) → Unl1 r w

end UpperTheory.V.Z.Desc.W
