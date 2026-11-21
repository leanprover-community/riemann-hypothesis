import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem charPol_char_congr {x y z : WD h} (hz : z.lpDim = 1) (g : ↥(Weil h)) (e : x.charPol g = y.charPol g) :
    (x.lpChar z).charPol g = (y.lpChar z).charPol g := by
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((WD.card_eig z g).trans hz)
  rw [WD.charPol_eq_prod, WD.charPol_eq_prod (y.lpChar z), GlobalTheory.RowTie.EigTwist.eig_lpChar x z g hz c hc,
    GlobalTheory.RowTie.EigTwist.eig_lpChar y z g hz c hc, WD.eig, WD.eig, e]

theorem AwV.char {x y z : WD h} (k : AwV x y) (hz : z.lpDim = 1) : AwV (x.lpChar z) (y.lpChar z) :=
  ⟨fun g => charPol_char_congr hz g (k.pol g), fun m => by rw [k.n0 ((WD.monomial_char_iff _ _ hz).1 m)]⟩

theorem WDN.charpoly (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (k : WDN ι r y) (g : ↥(Weil h)) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = y.charPol g := by
  obtain ⟨x, hx, k⟩ := k
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  rw [← hN.charPol_wdOf hl ht ι g, e, k.pol]

theorem wn' (k : WDN ι r y) : WDN ι r y := k

end UpperTheory.GalN.V
