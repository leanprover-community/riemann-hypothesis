module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def algNorm {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (k := w.adicCompletion E) :=
  (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)

omit [NumberField E] in
def IsSstAt (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (r : ↥Gw →* GL (Fin a) (Om l)) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ IsSst P (Bw.repE LL' r')

variable [IsAlgClosure E Ω] [IsCMField E]

def IsLAdicCharOf (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E))
    (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles (maximalRealSubfield E) →* Gab (maximalRealSubfield E) Ω)
    (n : (maximalRealSubfield E →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ n ∧ IsLAdicOf art ι χ n μ

end GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

open GlobalTheory.GalOfCusp

end GlobalTheory.Published

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

variable [IsCMField E] {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

end GlobalTheory.GalOfCusp
