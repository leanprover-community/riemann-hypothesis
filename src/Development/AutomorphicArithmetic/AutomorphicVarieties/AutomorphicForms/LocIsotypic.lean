module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def IsLevelWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (M n : ℕ) (x : WD h) : Prop :=
  ∃ (χ : Fin n → G F Ω →* ℂˣ) (a : WDRep h (Fin n → ℂ)), (∀ i, KillsMu M (χ i)) ∧ WD.mk a = x ∧ a.N = 0 ∧
    ∀ s : ↥(Ine (F := F) A), a.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ))

variable (F) in
def KLoc (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ) : Subgroup (GL (Fin n) (w.adicCompletion F)) :=
  (KLev F n M).comap (locGL F n w)

def LocIsotypic {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V)
    (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  Nontrivial V ∧ ⨆ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, LinearMap.range f.1 = ⊤

def FlagAt {l : ℕ} [Fact l.Prime] {n : ℕ} (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) : Prop :=
  ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s

end Defs

def WDAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, KillsMu M (χ i)) → IsDiagOn r (Ine (F := F) A) χ →
      ∀ x : WD h, IsWDOf ι r x → IsLevelWD M n x

def WDAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ PotCrysAt r A) →
      IsLevelWD M n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype))

def JumpsAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw → ∀ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → ∀ (τ : F →+* Qbar l) (J : Multiset ℤ),
      IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ J → J = Finset.univ.val.map fun i => -m i

def GlobFixed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n M : ℕ), 1 ≤ M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V), GlobalTheory.PRep.IsSmooth ρ →
    (∀ w, ∃ σ, LocIsotypic ρ w σ ∧ HasFixed σ.ρ (KLoc F w n M)) → HasFixed ρ (KLev F n M)

def LocCompC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def LocCompR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def SatLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))),
    (HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n)) → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V), LocIsotypic ρ w σ →
      ∀ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B

def WeylC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ c A : ℕ, ∀ m : Fin n → ℤ, StrictAnti m →
    ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∃ Ξ : GlobalTheory.GKCoh.AlgRep E n, (∀ τ, AlgInfChar Ξ τ ((infOf m).map Neg.neg)) ∧ Ξ.d ≤ c * (H + 1) ^ A

end UpperTheory.V.Af
