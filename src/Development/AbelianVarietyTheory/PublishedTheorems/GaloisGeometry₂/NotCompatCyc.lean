import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsPolarizedOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGlobAll.Model

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}

def Compat (π : CuspSub E a) (R : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous R ∧ IsSSRep R ∧
    (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
        IsPstAt P Bw (R.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
          wdAt P ι Bw h hj (R.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

theorem compat_of (H : GlobalTheory.Published.CaraianiLocalGlobal) (ha : 2 ≤ a) (π : CuspSub E a) (hc : π.IsCsd)
    (hcoh : GKCoh.IsCohomological π) : ∃ R, Compat Ω ι π R := H E Ω l ι a ha π hc hcoh

omit [IsCMField E] [IsAlgClosure E Ω] [NumberField E] in

theorem isPstAt_one {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) :
    IsPstAt P Bw (1 : ↥Gw →* GL (Fin a) (Om l)) := by
  refine ⟨Bw.LL, 1, isModel_one Bw, ?_⟩
  have := Bw.LL.2
  let b := Module.finBasis ℚ_[l] (Fin a → ↥Bw.LL.1)
  refine GlobalTheory.PstExt.isPst_of_coord P (LL := ℚ_[l]) (ρ := (1 : Representation ℚ_[l] ↥(GK Bw.Kw) ℚ_[l]))
    (E := b.equivFun) (fun g x i => ?_)
    (isPst_one_of_kummer l P (GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T) _)
  have : Bw.repE Bw.LL (1 : ↥Gw →* GL (Fin a) ↥Bw.LL.1) g x = x := by simp [LocBridge.repE]
  rw [this]; rfl




variable {Ω ι}

theorem Compat.unram_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    (∀ g ∈ Ine (F := E) A, R g = 1) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  have h1 := H.2.2.1 w hl A h rc hrc σ hσ
  obtain ⟨N, hN⟩ := (exists_isWDOf_iff hl (isTameChar_tameL h hl)).1 ⟨_, h1⟩
  rw [← hN.unr_wdOf_iff hl (isTameChar_tameL h hl) ι, h1.wdOf_eq hl]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

theorem Compat.crys_iff {π : CuspSub E a} {R : G E Ω →* GL (Fin a) (Qbar l)} (H : Compat Ω ι π R)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ} (hσ : π.IsLocComp w σ) :
    IsCrysAt P Bw (R.comp (Dec (F := E) A).subtype) ↔ SmGL.IsSpherical (algNorm σ).rep := by
  obtain ⟨h1, h2⟩ := H.2.2.2 P AI ⟨T⟩ w A h O Bw hj
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff (h := h) (hj := hj) (ι := ι) (hr := h1), h2 σ hσ rc hrc]
  obtain ⟨_, _, _, -, L⟩ := hrc
  exact (L.sph _).symm

end GlobalTheory.LocGlobAll.Model

end
