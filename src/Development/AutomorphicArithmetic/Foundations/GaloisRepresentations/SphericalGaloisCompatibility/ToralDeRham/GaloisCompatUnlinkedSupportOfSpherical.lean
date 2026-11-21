import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.IsQg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CharacterLevelCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMulti
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PstIneAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstOfIsSst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineDecompositionGroupNoMonodromy
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamDescends
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend

section
namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.UnlinkedChars

theorem rc_unlinked_chars : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (x : IrrGL (w.adicCompletion E)) (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) → Unlinked (chars ξ hξ) → (rc x).mono0 ∧ ∀ g : Weil h, (rc x).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ w A h a ha rc H x n ξ hξ hs hu
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hI.exh (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hI.zel _ 𝔪 x hm
  have he : chars ξ hξ = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hI.zel _ x _ _ hs hs'
  have hL := H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm)
  have hmem : ∀ Δ ∈ 𝔪, ∀ i : Fin Δ.len, Δ.term i ∈ chars ξ hξ := fun Δ hΔ i => by
    rw [he, msupp]
    exact Multiset.mem_bind.2 ⟨Δ, hΔ, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩

  have hlen : ∀ Δ ∈ 𝔪, Δ.len = 1 := by
    intro Δ hΔ
    by_contra hne
    have h2 : 1 < Δ.len := lt_of_le_of_ne Δ.len_pos (Ne.symm hne)
    refine hu _ (hmem Δ hΔ ⟨1, h2⟩) _ (hmem Δ hΔ ⟨0, Δ.len_pos⟩) ?_
    simp only [Segment.term, IrrGL.nu_nu]
    norm_num
  have hms : ∀ Δ ∈ 𝔪, Δ.ms = {Δ.first} := by
    intro Δ hΔ
    have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl (by rw [hlen Δ hΔ]; rfl)
    rw [e, Segment.ms_single]
    rfl
  have hsupp : msupp 𝔪 = 𝔪.map Segment.first := by
    rw [msupp, ← Multiset.bind_singleton]
    exact Multiset.bind_congr hms
  have hchar : ∀ y ∈ chars ξ hξ, ∃ j, y = IrrGL.ofChar (ξ j) (hξ j) := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    exact ⟨j, rfl⟩
  have hfirst : ∀ Δ ∈ 𝔪, ∃ j, Δ.first = IrrGL.ofChar (ξ j) (hξ j) := fun Δ hΔ =>
    hchar _ (by rw [he, hsupp]; exact Multiset.mem_map_of_mem _ hΔ)
  have hsum : rc x = sumList (𝔪.toList.map fun Δ => rc Δ.first) := by
    rw [hL, segSum]
    congr 1
    apply List.map_congr_left
    intro Δ hΔ
    rw [hlen Δ (Multiset.mem_toList.1 hΔ)]
    simp only [Nat.cast_one, sub_self, zero_div]
    exact (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h _).1
  have hpol1 : ∀ j (g : Weil h), (rc (IrrGL.ofChar (ξ j) (hξ j))).charPol g = X - C ((ξ j (a g) : ℂˣ) : ℂ) := by
    intro j g
    rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  refine ⟨?_, fun g => ?_⟩
  · rw [hsum]
    have key : ∀ L : List (Segment (w.adicCompletion E)), (∀ Δ ∈ L, Δ ∈ 𝔪) →
        (sumList (L.map fun Δ => rc Δ.first)).mono0 := by
      intro L
      induction L with
      | nil =>
        intro _
        show (WD.lpZero h).mono0
        exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl
      | cons Δ L ih =>
        intro hL'
        obtain ⟨j, hj⟩ := hfirst Δ (hL' Δ List.mem_cons_self)
        show (WD.lpSum _ _).mono0
        refine (WD.monomial_sum_iff _ _).2 ⟨?_, ih fun Δ' h' => hL' Δ' (List.mem_cons_of_mem _ h')⟩
        change (rc Δ.first).mono0
        rw [hj]
        exact WD.mono0_of_lpDim_eq_one (by rw [H.dim]; rfl)
    exact key _ fun Δ hΔ => Multiset.mem_toList.1 hΔ
  · rw [hsum, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_map]
    have r1 : (∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))) = ((chars ξ hξ).map fun y => (rc y).charPol g).prod := by
      rw [chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => (hpol1 j g).symm)
    rw [r1, he, hsupp, Multiset.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rfl

end GlobalTheory.RoadU.UnlinkedChars

section

end
end
end GalTw
end

section
open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem away_eq_of_plainTor : UpperTheory.Gal.ToralGalois.Inq → ToralGal → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → PlainTor (algNorm σ) → (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → wdOf h hl ι r = rc (algNorm σ) := by
  intro hI hT E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ hp
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a0 ha0).1, ?_⟩
  rintro rc ⟨a, ha, H⟩
  obtain ⟨h1, h2⟩ := hT E Ω l ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hs hu a ha
  obtain ⟨h3, h4⟩ := GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu
  exact GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ h1 h3 fun g => (h2 g).trans (h4 g).symm

end GlobalTheory.RoadU
end GalTw
end

section
open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralGal_of_holds : UpperTheory.Gal.ToralGalois.Inq → SphericalLevelCondition .all .unr → ToralGal := by
  intro hI hS E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha
  have key : ∀ g : Weil h, deg g ≠ 0 →
      (wdOf h hl ι r).mono0 ∧ (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', P, χ', hP, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hl' : ((l : ℕ) : 𝓞 M) ∉ u.asIdeal := by
      intro hm
      apply hl
      rw [← h]
      rw [← h'] at hm
      simpa using hm
    have hr' : Weak P ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π P hlift r hr
    have hF : UpperTheory.V.Af.FrobEig ι (resTo M r) u (UpperTheory.V.Af.algSat n (normV u) B) :=
      hS M Ω l ι n hn P χ' hP (resTo M r) hr' u trivial B hB hl'
    have hwd : wdOf h' hl' ι (resTo M r) = satWD h' n B :=
      GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius Ω M l ι n (resTo M r) hr'.1 u hl' A h' B hF
    have hres := GlobalTheory.AboveL.wdOf_restricts E M Ω A w u h h' l ι n r hl hl' hr.1
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hmono.mp ?_, ?_⟩
    · rw [hwd]
      simp [satWD, WD.lpUnr]
    · rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hwd]
      exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  refine ⟨(key (frob h) (by rw [deg_frob]; exact one_ne_zero)).1, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.trans (hy g).symm) g

end GlobalTheory.RoadU

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end GalTw
end

section
open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralAbove_of_holds : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.SphericalLevelCondition .all .crys → GlobalTheory.RoadU.SphericalLevelCondition .all .phi → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ, π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧ ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI hC hF E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha P AI hT O _ _ _ Bw hj
  have key : ∀ g : Weil h, deg g ≠ 0 →
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', Q, χ', hQ, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hr' : Weak Q ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π Q hlift r hr
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n Q u
    have hsph : IsSpherical τ.ρ :=
      GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL (((GlobalTheory.Cong.satake_locComp M n Q u τ hτ).1 B).1 hB)
    have hcl : ClauseAt .crys Q ι (resTo M r) u := hC M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    have hph : SphAt .phi Q ι (resTo M r) u B := hF M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := M) Bw hj Bw.LL
    have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
    have hc₀ := hcl P AI hT A h' _ Bw₀ hj₀ τ hτ hsph
    have hp₀ : IsPstAt P Bw₀ ((resTo M r).comp (Dec (F := M) A).subtype) :=
      GlobalTheory.GalCut.IwaAll.isPstAt_of_isSstAt P AI hT Bw₀ _
        (GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT M Ω _ _ Bw₀ n _ hc₀)
    have hpst : IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) :=
      GlobalTheory.AboveLRes.isPstAt_of_resTo E M Ω A l P AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
    obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
      GlobalTheory.AboveLRes.wdAt_resTo E M Ω A w u h h' l ι P AI hT n r O Bw hj hpst
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    have hc' := hcl P AI hT A h' O' Bw' hj' τ hτ hsph
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hpst, hmono.mp (GlobalTheory.CrysNoMono.crystalline_decompositionGroup_no_monodromy M Ω l ι n P u A h' O' Bw' hj' _ hc'), ?_⟩
    rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hph P AI hT A h' O' Bw' hj' ⟨g', hmem⟩]
    exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  obtain ⟨hpst, hmono, -⟩ := key (frob h) (by rw [deg_frob]; exact one_ne_zero)
  refine ⟨hpst, hmono, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.2.trans (hy g).symm) g

end GlobalTheory.RoadU
end GalTw
end

section
open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DeRhamOfPlainTorus

theorem deRham_of_plainTor (hI : UpperTheory.Gal.ToralGalois.Inq) (hS : SphericalLevelCondition .all .dR) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (π : CuspSub E n)
    (χ : HChar (maximalRealSubfield E)) (hsc : InScope .all l π χ) (r : G E Ω →* GL (Fin n) (Qbar l)) (hw : Weak π ι r)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hσ : π.IsLocComp w σ)
    (hp : PlainTor (algNorm σ)) : ClauseAt .dR π ι r w := by
  intro P AI hT A hA O _ _ _ Bw hj
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds E Ω A w hA
  obtain ⟨M, _, _, _, _, _, _, _, u, h', PM, χ', hsc', hlift, -, B, hB, -⟩ :=
    GlobalTheory.RoadU.exists_sph_lift_of_toral hI Ω E l ι n hn π χ hsc r hw w A hA σ hσ ξ hξ hs hu a ha (frob hA)
      (by rw [deg_frob]; exact one_ne_zero)
  have hwM : Weak PM ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π PM hlift r hw
  have hcl : ClauseAt .dR PM ι (resTo M r) u := hS M Ω l ι n hn PM χ' hsc' (resTo M r) hwM u trivial B hB
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E M Ω A w u hA h' l P AI hT n r hw.1 O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : M →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap M Ω))
  have hτL : τL.comp (algebraMap E M) = τ := by
    ext x
    show φ (Bw'.j (algebraMap M Ω (algebraMap E M x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E M Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hlift.inf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E M Ω A w u hA h' l P AI hT n r hw.1 O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')

theorem galoisCompat_unlinkedSupport_of_spherical : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := by
  intro hI hC E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hp
  refine ⟨fun hl A h => GlobalTheory.RoadU.away_eq_of_plainTor hI (GlobalTheory.RoadU.toralGal_of_holds hI (hC.2 .unr))
    E Ω l ι n hn π χ hπ r hr w hl A h σ hσ hp,
    fun hl => ⟨deRham_of_plainTor hI (hC.2 .dR) E Ω l ι n hn π χ hπ r hr w σ hσ hp, fun P AI hT A h O _ _ _ Bw hj => ?_⟩⟩
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.adicCompletion E) (algNorm σ) hp
  have key := fun a ha => GlobalTheory.RoadU.toralAbove_of_holds hI (hC.2 .crys) (hC.2 .phi) E Ω l ι n hn π χ hπ r hr w hl A h σ hσ
    ξ hξ hs hu a ha P AI hT O Bw hj
  obtain ⟨a0, ha0⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  refine ⟨(key a0 ha0).1, (key a0 ha0).2.1, ?_⟩
  rintro rc ⟨a, ha, H⟩ g
  exact ((key a ha).2.2 g).trans
    ((GlobalTheory.RoadU.UnlinkedChars.rc_unlinked_chars hI Ω E w A h a ha rc H (algNorm σ) n ξ hξ hs hu).2 g).symm

end GlobalTheory.DeRhamOfPlainTorus

end
end GalTw
end
