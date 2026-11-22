module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Down2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

open UpperTheory.V.Published

def Twi : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAut ι r → IsAlgChar ι κ → IsAut ι (tw r κ)

def AlgOfCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ κ : G F Ω →* (Qbar l)ˣ, Continuous κ →
      (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
        ∃ (a : ℤ) (k : ℕ), 0 < k ∧ ∀ s ∈ Ine (F := F) A, (κ s * cycBar F Ω l s ^ (-a)) ^ k = 1) → IsAlgChar ι κ) ∧
    (∀ κ κ' : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ' → IsAlgChar ι (κ * κ') ∧ IsAlgChar ι κ⁻¹) ∧
    ∀ (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω]
      (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAlgChar ι (κ.comp (resG F M Ω))

def SelfDualC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), AttC ι r π →
    ∀ (χ : HChar (maximalRealSubfield F)) (μ : G (maximalRealSubfield F) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι χ μ →
    ∀ (c : G (maximalRealSubfield F) Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * μ.comp (resG (maximalRealSubfield F) F Ω)) P →
      GlobalTheory.ContraPair.DualIsConjBy π (compNorm F χ)

def SelfDualR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n), AttR ι r π →
    ∀ (θ : G F Ω →* (Qbar l)ˣ) (χ : HChar F), DualTw r θ → IsCharOf ι χ (θ * cycBar F Ω l ^ ((n : ℤ) - 1)) →
      π.IsSelfDualBy χ ∧ ((∀ c c' : G F Ω, IsConjEl c → IsConjEl c' → θ c = θ c') → π.Polarized χ)

def SolDescent : Prop :=
  ∀ (F₀ F M Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω]
    [Algebra F₀ F] [Algebra F M] [Algebra F₀ Ω] [Algebra F Ω] [Algebra M Ω] [IsScalarTower F₀ F Ω] [IsScalarTower F M Ω]
    [IsAlgClosure F₀ Ω] [IsAlgClosure F Ω] [IsAlgClosure M Ω] [IsGalois F M] [IsCMField F], IsSolvable (M ≃ₐ[F] M) → IsPlusOf F₀ F →
    (IsTotallyReal M ∨ IsCMField M) → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F₀ Ω →* (Qbar l)ˣ), Continuous r → IsIrr (r.comp (resG F M Ω)) →
      IsAlgChar ι μ → (∀ c c' : G F₀ Ω, IsConjEl c → IsConjEl c' → μ c = μ c') →
      (∃ (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c ∧ IsPairing c r (μ.comp (resG F₀ F Ω)) P) →
      (IsAut ι r ↔ IsAut ι (r.comp (resG F M Ω)))

section Ver

variable {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  {C : Type} [CommGroup C]

def VerEq (κ : G L Ω →* C) (ν : G F Ω →* C) : Prop :=
  ∀ g : G F Ω, g ∉ (resG F L Ω).range →
    (∀ s s' : G L Ω, resG F L Ω s' = g * resG F L Ω s * g⁻¹ → κ s * κ s' = ν (resG F L Ω s)) ∧
    ∀ t : G L Ω, resG F L Ω t = g * g → κ t = ν g

end Ver

section Compat

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

end Compat

end UpperTheory.V.Af
