import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.PowEqOneOfRoots
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnlinkedLanglandsDatumGenericStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumNoMonodromyLengthOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportOfLengthOneLanglandsDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedLengthOneSegmentsFirstTermsNotNuTwistStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTameOfMemWeilDeligneListSumStatement
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.DepthZeroIntermediateHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationNatCastLtOneOfInduces

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Zero.LLC UpperTheory.GalStar UpperTheory.GalS PositivityTheory.Rg.DzCount
open private UpperTheory.Zero.LLC.AbC.dim_one from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv

namespace UpperTheory.Gal.Int.Row

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isTameWD_of_tmW {y : WD h} (k : TmW y) : IsTameWD y := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  have ha : a.Tame := (WD.tame_mk a).1 ((WD.tame_iff_inePol _).2 fun σ hσ => k σ hσ)
  refine ⟨n, a, rfl, fun σ hσ => ha σ fun x hx => ?_⟩
  have e : (σ : G E Ω) x / x - 1 = ((σ : G E Ω) x - x) / x := by field_simp
  have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
  rw [e, map_div₀, div_lt_one₀ h0]
  exact hσ.2 x hx

theorem dim_one_of_dvd {y : WD h} (hy : IsIrrWD y) (k : ∀ s t : Weil h, ∃ m : ℕ, y.charPol ⁅s, t⁆ ∣ (X - 1 : ℂ[X]) ^ m) :
    y.lpDim = 1 := by
  obtain ⟨n, b, rfl, hb⟩ := hy
  have hn : n = 1 := UpperTheory.Zero.LLC.AbC.dim_one b hb fun σ t => by
    obtain ⟨m, hm⟩ := k σ (ineIncl h t)
    rw [WD.charPol_mk] at hm
    exact ⟨m, hm⟩
  rw [WD.lpDim_mk]
  simpa using hn

theorem tor_of_fix {y : WD h} (ht : IsTameWD y) {γ : G E Ω} (hγ : TameGenAt A γ)
    (k : ∀ z : ℂ, (y.charPol (ineIncl h ⟨γ, hγ.1⟩)).IsRoot z → z ^ (normV w - 1) = 1) : Tor y := by
  obtain ⟨n, a, rfl, ha'⟩ := ht
  have ha : a.Tame := fun σ hσ => ha' σ (TameWeilRepresentationIrreducibility.wild_inertia_isWild hσ)
  let u := a.ρ.toHomUnits
  let g : Weil h := ineIncl h ⟨γ, hγ.1⟩
  have hq : 1 ≤ normV w := (one_lt_normV w).le
  have p1 : a.ρ g ^ (normV w - 1) = 1 := pow_eq_one_of_roots (a.semisimple g) fun z hz => k z (by rwa [WD.charPol_mk])
  have p2 : a.ρ (frob h * g * (frob h)⁻¹) = a.ρ g := by
    rw [ha.conj_eq_pow hγ.1 deg_frob, ← Nat.sub_add_cancel hq, pow_succ, p1, one_mul]
  have c1 : Commute (u (frob h)) (u g) := by
    have e : u (frob h * g * (frob h)⁻¹) = u g := Units.ext p2
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at e
    exact e
  have cen : ∀ x : (End ℂ (Fin n → ℂ))ˣ, Commute x (u g) → ∀ σ, Commute x (u (ineIncl h σ)) := fun x hx σ =>
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_of_gen ha hγ (Subgroup.centralizer {x}) (Subgroup.mem_centralizer_singleton_iff.2 hx.symm) σ) |>.symm
  have c2 := cen _ c1
  have c3 : ∀ τ σ, Commute (u (ineIncl h τ)) (u (ineIncl h σ)) := fun τ => cen _ (cen _ (Commute.refl _) τ).symm
  intro s t
  have c : Commute (u s) (u t) := by
    obtain ⟨τ, e⟩ := exists_eq_zpow_mul deg_frob s
    obtain ⟨τ', e'⟩ := exists_eq_zpow_mul deg_frob t
    rw [e, e', map_mul, map_mul, map_zpow, map_zpow]
    exact Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ _ _) ((c2 τ').zpow_left _))
      (Commute.mul_right ((c2 τ).symm.zpow_right _) (c3 τ τ'))
  have e : a.ρ ⁅s, t⁆ = 1 := by
    have := (map_commutatorElement u s t).trans (commutatorElement_eq_one_iff_commute.2 c)
    exact congrArg Units.val this
  show (WD.mk a).charPol _ = _
  rw [WD.charPol_mk, e, LinearMap.charpoly_one, WD.lpDim_mk]

variable {rc : IrrGL (w.adicCompletion E) → WD h}

theorem split (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep) (hm : (rc x).mono0) :
    ∃ l : List (IrrGL (w.adicCompletion E)), HasSupport x.rep (l : Multiset _) ∧ GlobalTheory.RoadU.Unlinked (l : Multiset (IrrGL (w.adicCompletion E))) ∧
      rc x = sumList (l.map rc) := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨c, Δ, hun, hL⟩ := GlobalTheory.T.exists_unlinked_langlandsDatum_generic _ x hx
  obtain ⟨a, ha, L⟩ := id hrc
  have e : rc x = segSum rc (List.ofFn Δ) := L.langlands _ x hL
  obtain ⟨hlen, hsum⟩ := GlobalTheory.T.segmentSum_no_monodromy_length_one rc hrc (List.ofFn Δ) (e ▸ hm)
  have h1 : ∀ i, (Δ i).len = 1 := fun i => hlen _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  refine ⟨List.ofFn fun i => (Δ i).first, ?_, ?_, ?_⟩
  · rw [← Fin.univ_val_map]; exact GlobalTheory.T.supercuspidalSupport_of_lengthOne_langlandsDatum _ c Δ x h1 hL
  · rw [← Fin.univ_val_map]; exact GlobalTheory.T.unlinkedLengthOneSegments_firstTerms_not_nuTwist rc hrc c Δ h1 hun
  · rw [e, hsum, List.map_ofFn, List.map_ofFn]; rfl

theorem plainTor_of_tor (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep) (ht : Tor (rc x))
    (hm : (rc x).mono0) : GlobalTheory.RoadU.PlainTor x := by
  obtain ⟨l, hs, hu, e⟩ := split hrc hx hm
  obtain ⟨a, ha, L⟩ := hrc
  refine ⟨_, hs, fun y hy => ?_, hu⟩
  rw [← L.dim y]
  refine dim_one_of_dvd (L.cusp y (hs.isCusp hy)) fun s t => ⟨(rc x).lpDim, ?_⟩
  have k : (rc x).charPol ⁅s, t⁆ = _ := ht s t
  rw [← k, e, CuspExt.charPol_sumList, List.map_map]
  exact List.dvd_prod (List.mem_map.2 ⟨y, hy, rfl⟩)

theorem good_of_dz (hq : IsQp w) {y : IrrGL (w.adicCompletion E)} (hy : y.IsCusp) (hd : DZ y) : Good y := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have h1 : IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
    simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
  exact ((goodSeg _).2.1 y hy).2 (Or.inr ⟨hq, y, 1, h1, hd, (y.tw_one h1).symm⟩)

theorem dz_of_cusp (hq : IsQp w) (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) (ht : IsTameWD (rc x)) :
    DZ x := by
  obtain ⟨a, ha, H⟩ := hrc
  obtain ⟨φ, hφ⟩ := deg_surjective (h := h) (-1)
  have hord : ord (w.adicCompletion E) (a φ) = 1 := by rw [ha.ord_eq, hφ]; rfl
  have hc : ((rc x).eig φ).prod ≠ 0 := by
    obtain ⟨δ, hδ⟩ := (wDBasic E Ω A w h (rc x)).1
    rw [hδ]
    exact Units.ne_zero _
  obtain ⟨f, hf, hfi⟩ := depth_zero_intermediate_holds E Ω A w h φ hφ x.1 _ hx.1
  obtain ⟨Y, hY, hYi⟩ := depth_zero_count_holds (w.adicCompletion E) x.1 hx.1 (a φ) hord (Units.mk0 _ hc)
  have hg : ∀ P ∈ Lab 𝓀[w.adicCompletion E] x.1, Good (Y P) := fun P hP => good_of_dz hq (hY P hP).2.1 (hY P hP).2.2.1
  have hmap : Set.MapsTo (rc ∘ Y) (Lab 𝓀[w.adicCompletion E] x.1) (TameSet φ x.1 ((rc x).eig φ).prod) := by
    intro P hP
    obtain ⟨h1, h2, h3, ω, h4, h5⟩ := hY P hP
    refine ⟨H.cusp _ h2, H.depth _ (hg P hP) h3, (H.dim _).trans h1, ?_⟩
    show ((rc (Y P)).eig φ).prod = _
    rw [H.central _ ω (hg P hP) h4 φ, h5, Units.val_mk0]
  have hinj : Set.InjOn (f ∘ rc ∘ Y) (Lab 𝓀[w.adicCompletion E] x.1) :=
    hfi.comp (fun P hP P' hP' e => hYi hP hP' (H.inj _ _ (hg P' hP') e)) hmap
  have hbij := ((lab_finite _ _).injOn_iff_bijOn_of_mapsTo (hf.comp hmap)).1 hinj
  have hxT : rc x ∈ TameSet φ x.1 ((rc x).eig φ).prod := ⟨H.cusp _ hx, ht, H.dim _, rfl⟩
  obtain ⟨P, hP, hPe⟩ := hbij.surjOn (hf hxT)
  have e : x = Y P := H.inj _ _ (hg P hP) (hfi (hmap hP) hxT hPe).symm
  rw [e]
  exact (hY P hP).2.2.1

theorem charPol_of_inert (hrc : IsRecT h rc) {y z : IrrGL (w.adicCompletion E)} (hy : Good y) (k : y.Inert z)
    (t : Ine (F := E) A) : (rc z).charPol (ineIncl h t) = (rc y).charPol (ineIncl h t) := by
  obtain ⟨a, ha, H⟩ := hrc
  obtain ⟨μ, hμ, rfl⟩ := k
  rw [H.twist _ _ _ hy, H.one, lpChar_lpOfChar]
  obtain ⟨n, b, hb⟩ := (rc y).exists_rep
  have h1 : μ (a (ineIncl h t)) = 1 :=
    hμ _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq, deg_ineIncl, neg_zero]))
  rw [← hb, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, MonoidHom.comp_apply, h1, Units.val_one, one_smul]

theorem mixed_of_tame (hq : IsQp w) (hrc : IsRecT h rc) {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep)
    (ht : TmW (rc x)) (hs : Sqf (rc x)) (hm : (rc x).mono0) :
    DZ x ∧ ∀ s, HasSupport x.rep s → GlobalTheory.RoadU.Unlinked s ∧ (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨l, hl, hu, e⟩ := split hrc hx hm
  have tame : ∀ y ∈ l, IsTameWD (rc y) := fun y hy =>
    GlobalTheory.T.isTame_of_mem_weilDeligneListSum _ (e ▸ isTameWD_of_tmW ht) _ (List.mem_map_of_mem hy)
  have dz : ∀ y ∈ l, DZ y := fun y hy => dz_of_cusp hq hrc (hl.isCusp hy) (tame y hy)
  obtain ⟨hGL, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  refine ⟨GlobalTheory.DepthZeroPass.depthZeroInduction hGL GlobalTheory.bernsteinZelevinskyFiniteness_holds hZ _ x _ hl dz, fun s hs' => ?_⟩
  obtain rfl : s = (l : Multiset _) := (goodSeg _).2.2 x _ _ hs' hl
  refine ⟨hu, _, Multiset.filter_coe _ l, ?_⟩
  rw [List.pairwise_filter, List.pairwise_iff_forall_sublist]
  intro y z hsub h2 _ hI
  have hy : y ∈ l := hsub.subset (by simp)
  obtain ⟨γ, hγ⟩ : ∃ γ : G E Ω, TameGenAt A γ := GlobalTheory.exists_tameGenAt_of_isPlaceOver E Ω A w h
  have e1 := charPol_of_inert hrc (good_of_dz hq (hl.isCusp hy) (dz y hy)) hI ⟨γ, hγ.1⟩
  have hd : (rc y).charPol (ineIncl h ⟨γ, hγ.1⟩) * (rc y).charPol (ineIncl h ⟨γ, hγ.1⟩) ∣ (rc x).charPol (ineIncl h ⟨γ, hγ.1⟩) := by
    rw [e, CuspExt.charPol_sumList, List.map_map]
    have := (hsub.map ((fun v : WD h => v.charPol (ineIncl h ⟨γ, hγ.1⟩)) ∘ rc)).prod_dvd_prod
    simpa [e1] using this
  have T : Tor (rc y) := tor_of_fix (tame y hy) hγ fun c hc => by
    refine hs γ hγ.1 hγ.2 c ?_
    rw [WD.inePol_of_mem_Ine _ hγ.1, le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero, pow_two]
    exact (mul_dvd_mul (dvd_iff_isRoot.2 hc) (dvd_iff_isRoot.2 hc)).trans hd
  obtain ⟨a, ha, H⟩ := hrc
  have d1 := dim_one_of_dvd (H.cusp y (hl.isCusp hy)) fun s t => ⟨_, (T s t : (rc y).charPol ⁅s, t⁆ = _).dvd⟩
  rw [H.dim] at d1
  simp only [decide_eq_true_eq] at h2
  omega

theorem dz_of_nu {x : IrrGL (w.adicCompletion E)} (h0 : 0 < x.1) (s : ℂ) (k : DZ (x.nu s)) : DZ x := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have e : x = (x.nu s).nu (-s) := by simp
  rw [e]
  refine (twTame _ (x.nu s) _ (isSmoothChar_absPow (-s)) h0 k).2 fun u hu => ?_
  have h1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 := by
    have := (valuation (w.adicCompletion E)).map_one_add_of_lt hu
    simpa using this
  exact isUnram_absPow _ _ _ h1

end UpperTheory.Gal.Int.Row
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.DeRhamOfPlainTorus
open UpperTheory.Zero.LLC UpperTheory.GalStar UpperTheory.GalS UpperTheory.Gal.ToralGalois.R2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Row

abbrev PlaceClass : Type 1 := ∀ (E : Type) [Field E] [NumberField E], HeightOneSpectrum (𝓞 E) → ℕ → Prop

def LocalGlobalCompatibilityAtPlaceClass (Q : PlaceClass) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ →
      fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥ → Q E w n → IsQg w → Apart (algNorm σ) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
      (rc (algNorm σ)).mono0 →
      (∀ hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal, (wdOf h hl ι r).mono0 ∧
        ∀ t : Ine (F := E) A, (wdOf h hl ι r).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t)) ∧
      (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ClauseAt .dR π ι r w ∧
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw),
          IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
          ∀ t : Ine (F := E) A,
            (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t))


theorem localGlobalAtPlaceClass_of_localGlobal (H : LocalGlobalCompatAtIwahoriFixedPlaces) (Q : PlaceClass) : LocalGlobalCompatibilityAtPlaceClass Q := fun E Ω _ _ _ _ _ _ l _ ι n hn π χ hI r hW w σ hσ hf _ q g =>
  H E Ω l ι n hn π χ hI r hW w σ hσ hf (Or.inr ⟨q, g⟩)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t))
    (g : Weil h) (hg : deg g = 0) : x.charPol g = y.charPol g := by
  obtain ⟨t, e⟩ := exists_eq_zpow_mul deg_frob g
  rw [hg, zpow_zero, one_mul] at e
  rw [e, k]

theorem dim_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t)) :
    x.lpDim = y.lpDim := by
  rw [← WD.charPol_natDegree x (ineIncl h 1), k, WD.charPol_natDegree]

variable [IsCMField E] {a : ℕ} {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
  {rc : IrrGL (w.adicCompletion E) → WD h}

theorem generic_algNorm (hσ : π.IsLocComp w σ) : IsGeneric (algNorm σ).rep :=
  (isGeneric_congr (IrrGL.twEquiv _ _ (isSmoothChar_absPow _))).1 ((isGeneric_twist_iff _).2
    ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a π w σ hσ)))

theorem guard_tame (ha : 1 ≤ a) (hσ : π.IsLocComp w σ) (hrc : IsRecT h rc) (hq : IsQp w) (ht : TmW (rc (algNorm σ)))
    (hs : Sqf (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    fixed σ.ρ (KOne (w.adicCompletion E) (Fin a)) ≠ ⊥ ∧ Apart (algNorm σ) := by
  obtain ⟨h1, h2⟩ := mixed_of_tame hq hrc (generic_algNorm hσ) ht hs hm
  exact ⟨GlobalTheory.WeakTheRep.fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    (dz_of_nu (x := IrrGL.of σ.ρ σ.smooth σ.irred) ha _ h1), fun s k => (h2 s k).2⟩

theorem exists_hasSat (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : ∃ B, (CG.mk π).HasSat w B := by
  obtain ⟨k1, k2⟩ := GlobalTheory.T.cuspRep_satake_iff_localComponent_satake E a π w σ hσ
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (k2.1 hs)
  exact ⟨B, (k1 B).2 hB⟩

end Local

def Cmp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (q : Prop) (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ (Tor y → y.mono0 → x = y) ∧
    (q → IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g)

section Global

variable {Q : PlaceClass} {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem away (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ) :
    Cmp (Q E w a) (wdOf h hl ι r) (rc (algNorm σ)) := by
  refine ⟨?_, fun ht hm => ?_, fun q hq ht hs hm => ?_⟩
  · obtain ⟨_, _, L⟩ := hrc
    rw [lpDim_wdOf, Fintype.card_fin, L.dim]
    rfl
  · exact ((H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).1 hl A h).2 rc hrc
  · obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq ht hs hm
    have k := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).1 hl
    exact ⟨k.1, charPol_of_ine k.2⟩

theorem above (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    {P : LocPrime l} {AI : LocAinf l P} (T : Nonempty (LocTied l P AI))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ)
    (g : (Q E w a ∧ IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    ClauseAt .dR π ι r w ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      Away (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ)) := by
  have hl := mem_of_induces h Bw hj
  by_cases ht : Tor (rc (algNorm σ))
  · obtain ⟨k1, k2⟩ := (H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T A h O Bw hj
    have e := GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ k4 hm (k5 rc hrc)
    exact ⟨k1, k3, by rw [e], fun _ _ => e, fun _ _ _ _ => ⟨k4, fun g _ => k5 rc hrc g⟩⟩
  · obtain ⟨q, hq, h1, h2⟩ := g.resolve_right ht
    obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq h1 h2 hm
    obtain ⟨k1, k2⟩ := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T O Bw hj
    exact ⟨k1, k3, dim_of_ine k5, fun t => absurd t ht, fun _ _ _ _ => ⟨k4, charPol_of_ine k5⟩⟩

theorem exists_weights (ha : 1 ≤ a) (hI : InScope .all l π χ) (ι : Qbar l ≃+* ℂ) :
    ∃ (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
        ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z) ∧
      ∀ τ : E →+* Qbar l, HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·) := by
  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l a ha π χ hI
  have ex : ∀ τ : E →+* Qbar l, ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z := fun τ => by
    haveI : CanLift ℂ ℤ (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z) := ⟨fun _ k => k⟩
    refine (Multiset.canLift (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z)).prf _ fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := (hI.1 (ι.toRingHom.comp τ)).2 z hz
    exact ⟨-n, by rw [hn]; push_cast; ring⟩
  choose HT hHT using ex
  refine ⟨wt, HT, hHT, fun τ => Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_⟩
  have k := hwt (ι.toRingHom.comp τ)
  have e := congrArg (Multiset.map fun y : ℂ => (wt : ℂ) - y) (hHT τ)
  rw [hHT, ← RingHom.comp_assoc, k]
  simp only [Multiset.map_map, Function.comp_def] at e ⊢
  push_cast
  rw [e]
  exact Multiset.map_congr rfl fun z _ => by ring

theorem crys (C : CoreAll) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r) (hσ : π.IsLocComp w σ)
    (hs : SmGL.IsSpherical σ.ρ) : ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w := by
  obtain ⟨B, hB⟩ := exists_hasSat hσ hs
  exact ⟨C.2 .crys E Ω l ι a ha π χ hI r hW w trivial B hB, C.2 .dR E Ω l ι a ha π χ hI r hW w trivial B hB⟩

end Global

theorem galoisLocalGlobal_of_placeClassCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass fun _ _ _ _ _ => True) :
    Row0 (fun h rc => IsRecT h rc) := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  have hI : InScope .all l π χ := ⟨hr, hp, trivial⟩
  obtain ⟨r, hW⟩ := C.1 E Ω l ι a ha π χ hI
  obtain ⟨wt, HT, w1, w2⟩ := exists_weights ha hI ι
  refine ⟨r, wt, HT, hW.1, hW.2.1, fun w hl A h rc hrc σ hσ => ?_, w1, w2, fun P AI T w A h O _ _ _ Bw hj =>
    ⟨fun σ hσ hs => ?_, fun σ hσ rc hrc g hm => ?_⟩⟩
  · have k := away H1 H2 ha hI hW hl hrc hσ
    exact ⟨k.1, k.2.1, k.2.2 trivial⟩
  · obtain ⟨k1, k2⟩ := crys C ha hI hW hσ hs
    have k3 := k2 P AI T A h O Bw hj
    exact ⟨k1 P AI T A h O Bw hj σ hσ hs, k3.1, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ)⟩
  · obtain ⟨k1, k2, k4⟩ := above H1 H2 ha hI hW T Bw hj hrc hσ (g.imp (fun q => ⟨trivial, q⟩) id) hm
    have k3 := k1 P AI T A h O Bw hj
    exact ⟨k3.1, k2, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ), k4⟩


theorem galoisLocalGlobal_of_localGlobalCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatAtIwahoriFixedPlaces) : Row0 (fun h rc => IsRecT h rc) :=
  galoisLocalGlobal_of_placeClassCompatibility C H1 (localGlobalAtPlaceClass_of_localGlobal H2 _)


end UpperTheory.Gal.Int.Row
end
end
