module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af
open CategoryTheory
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def ClozelCohC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (Ξ : GlobalTheory.GKCoh.AlgRep E a),
      (∀ τ, ∃ m, π.HasInfChar τ m ∧ AlgInfChar Ξ τ (m.map Neg.neg)) → GlobalTheory.GKCoh.IsCohFor π Ξ

def ClozelConjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
      ∃ (π' : CuspSub E a) (τ τ' : SmIrr (GL (Fin a) (Af E))), IsFinComp π τ ∧ IsFinComp π' τ' ∧ IsConjBy σ τ τ' ∧
        ∀ (φ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar φ m → π'.HasInfChar (σ.toRingHom.comp φ) m

def BorelInjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : GlobalTheory.GKCoh.AlgRep E a) (S : Finset (CuspSub E a)), (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
      (∀ π ∈ S, GlobalTheory.GKCoh.IsCohFor π Ξ ∧ HasFixed π.finPart U) → (S.card : Cardinal) ≤ cohDim ⊤ U (ratC Ξ)

section Real

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

end Real

def StrongMultOneReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ π π' : TR.CuspSub F a,
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) → π.Iso π'

def GelfandKazhdanReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∃ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
      (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af F) k)) ψ) = B φ ψ) ∧
      (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ) ∧
      ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0

def AdmissibleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a)
    (U : Subgroup (GL (Fin a) (Af F))), IsOpen (U : Set (GL (Fin a) (Af F))) →
    ∀ (d : ℕ) (ξ : TR.Kinf F a →* Matrix (Fin d) (Fin d) ℂ), ∃ W : Submodule ℂ π.V, FiniteDimensional ℂ W ∧
      ∀ f : (Fin d → ℂ) →ₗ[ℂ] π.V, (∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)) → (∀ u ∈ U, ∀ v, π.finPart u (f v) = f v) →
        LinearMap.range f ≤ W

section BC

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
  {a : ℕ}

def IsoTwist (π : TR.CuspSub F a) (η : HChar F) : Prop :=
  ∃ T : π.V ≃ₗ[ℂ] π.V, (∀ k φ, T (π.op (.fin k) φ) = ((chiDet a η (finGL F a k) : ℂˣ) : ℂ) • π.op (.fin k) (T φ)) ∧
    (∀ k φ, T (π.op (.cpt k) φ) = ((chiDet a η (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • π.op (.cpt k) (T φ)) ∧
    ∀ X φ, T (π.op (.lie X) φ) = π.op (.lie X) (T φ)

variable (E) in
omit [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
def IsQuadCharOf (η : HChar F) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) →
      η.UnrAt v ∧ η.val v = if normV w = normV v then 1 else -1

structure IsBC (π : TR.CuspSub F a) (P : CuspSub E a) : Prop where
  inf : ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m
  split : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)
  unr : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → ∀ f : ℕ, normV w = normV v ^ f →
      ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

end BC

def NewformRep : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (j : ℤ), ∃ π : TR.CuspSub ℚ 2,
    (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) ∧
    ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ f.M → ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Published
