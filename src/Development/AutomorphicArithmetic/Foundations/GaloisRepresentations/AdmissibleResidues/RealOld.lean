module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem pol_of_rel {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : ↥(Weil h)} {σ' : ↥(Weil h')} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

theorem RatioW.descend (P : PlaceIso A w A' w' φ j i) {x : WD h} {x' : WD h'} (hx : WDRel φ x x') (k : RatioW x') :
    RatioW x := by
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  intro g hg α hα β hβ
  rw [WD.eig, pol_of_rel hx ((hc g (c g)).2 rfl)] at hα hβ
  rw [← hq]
  exact k (c g) (by rw [hdeg, hg]) α hα β hβ

end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ} {π : TR.CuspSub F a} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (F →+* Qbar l) → Multiset ℤ}

end Real

end UpperTheory.GalN.V
