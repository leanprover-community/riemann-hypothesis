import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaDividedByConstantNonvanishingFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsPowLineBundleFromLocalBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endo_lbIso_symmetryHypothesis_extend_normalModel : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  first | exact @GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend | exact GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend | (intros; apply GlobalTheory.ZH.EndoExtend.hypS_and_endo_and_iso_extend <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → (∀ n : ℕ, n ≠ 0 → (n : Γ(S, ⊤)) ≠ 0) → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L), IsAbelianScheme G → Out.RelAmple G L.L → Out.KTriv ((Over.pullback U.ι).obj G) (L.L.pull (pullback.fst G.hom U.ι)) → Out.KTriv G L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_open_normal | exact GlobalTheory.KTrivSpread.kTriv_of_open_normal | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_open_normal <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.AbPol

open GlobalTheory.CechPic

theorem pic_ext_local {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      CechPic.pull (P.hom ⁻¹ᵁ V).ι a = CechPic.pull (P.hom ⁻¹ᵁ V).ι b := by
  rw [← sub_eq_zero, ← map_sub] at h
  have key : a - b = CechPic.pull P.hom (CechPic.pull e (a - b)) := by
    refine EndoExtend.pic_ext j hn P e he ?_ ?_
    · rw [← pull_comp, he, pull_id]
    · let eU : U ⟶ pullback P.hom j :=
        pullback.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
      have h₁ : eU ≫ pullback.fst P.hom j = j ≫ e := pullback.lift_fst _ _ _
      rw [h, ← pull_comp, pullback.condition, pull_comp, ← pull_comp j, ← h₁, pull_comp eU, h, map_zero, map_zero]
  obtain ⟨D, hD, hc⟩ := cls_surj (CechPic.pull e (a - b))
  obtain ⟨i, hi⟩ := exists_chart hD x
  obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset hi
  refine ⟨V, hV, hx, ?_⟩
  rw [← sub_eq_zero, ← map_sub, key, ← hc, ← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hD _)).2 (IsoExtend.exists_gen_of_chart hD _ i fun y => hle y.2)

theorem relAmple_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hn : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X)
    [Smooth P.hom] [IsProper P.hom] [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X)
    {L O : LB P.left} (hL : L.IsLB) (hO : O.IsLB) {N : ℕ} (hN : 1 ≤ N) (ha : RelAmple P O)
    (h : CechPic.pull (pullback.fst P.hom j) (N • cls L hL) = CechPic.pull (pullback.fst P.hom j) (cls O hO)) :
    RelAmple P L := by
  refine AmpleLocal.relAmple_of_locally X P L hL inferInstance inferInstance fun x => ?_
  obtain ⟨V, hV, hx, hc⟩ := pic_ext_local j hn P e he h x
  refine ⟨V, hx, ?_⟩
  have : IsAffine V := hV
  have : IsProper (Over.mk (P.hom ∣_ V)).hom := inferInstanceAs (IsProper (P.hom ∣_ V))
  have hL' := pull_isLB hL (P.hom ⁻¹ᵁ V).ι
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (P.hom ∣_ V)) hL').2 ?_
  refine (isAmpleLB_pow_iff hL' hN).1 ((isAmpleLB_of_relAmple P hO ha V hV).of_lbIso (isLB_lbPow hL' N) ?_)
  refine (cls_eq_iff (isLB_lbPow hL' N) (pull_isLB hO _)).1 ?_
  rw [cls_lbPow hL', cls_pull hL, cls_pull hO, ← hc, map_nsmul]

theorem exists_comb {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {H : LB Y} {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → R) : ∃ σ : H.Sec, ∀ l, σ.f l = ∑ j, constFn q (H.U l) (a j) * (s j).f l := by
  have hres : ∀ {U V : Y.Opens} (h : V ≤ U) (c : R),
      (Y.presheaf.map (homOfLE h).op).hom (constFn q U c) = constFn q V c := fun h c => by
    exact congrArg (fun z => z.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
      (q.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)
  refine ⟨⟨fun l => ∑ j, constFn q (H.U l) (a j) * (s j).f l, fun i k => ?_⟩, fun _ => rfl⟩
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hres, hres, (s j).compat i k]
  ring

theorem valR_comb {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp R) (r : Y ⟶ X) {H : LB X}
    {J : Type} [Fintype J] (s : J → H.Sec) (a : J → R) (σ : (H.pull r).Sec)
    (hσ : ∀ l, σ.f l = ∑ j, constFn q ((H.pull r).U l) (a j) * (GlobalTheory.secPull (s j) r).f l) (x : Sp K ⟶ Y)
    (l : (H.pull r).ι) (hx : ⊤ ≤ x ⁻¹ᵁ (H.pull r).U l) :
    valR x _ (σ.f l) = ∑ j, (Spec.preimage (x ≫ q)).hom (a j) * valF (x ≫ r) _ ((s j).f (l PUnit.unit)) := by
  rw [hσ, Points.valR_eq x _ hx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← Points.valR_eq, ← Points.valR_eq, Points.valR_constFn q x _ hx]
  exact congrArg _ (Points.valR_appLE x r _ hx _)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem cls_generic (hU : (U₀ : Set M.Z).Nonempty) {H Y : Scheme.{0}} [IsIntegral Y] (i : H ⟶ Q.G.left) (k : Y ⟶ H)
    (q : Y ⟶ Sp Ω) (w : (k ≫ i) ≫ Q.G.hom = q ≫ M.pt) (b : Matrix S.J S.J Ω) (O : LB H) (τ : S.J → LB.Sec O)
    (hO : O.IsLB) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : ∀ (K : Type) [Field K] (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (g' : Sp K ⟶ H)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι) (jO : O.ι),
      g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt → g' ≫ i = g ≫ Q.φ →
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
      Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range g' ⊆ O.U jO →
      ∃ c : K, c ≠ 0 ∧ ∀ i, ∑ l, β (b i l) * valF r _ ((ρ.s l).f (fun _ => jP)) = c * valF g' _ ((τ i).f jO)) :
    CechPic.pull k (S.N • CechPic.pull i (cls Q.L.L Q.L.isLB)) = CechPic.pull k (cls O hO) := by
  have hP := ρ.P.isLB
  have hL := Q.L.isLB
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)
  let x₀ : Sp Ω ⟶ U₀ := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have w' : (k ≫ i) ≫ Q.G.hom = (q ≫ x₀) ≫ U₀.ι := by rw [w, Category.assoc, hx₀]
  let g₀ : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift (k ≫ i) (q ≫ x₀) w'
  have g₁ : g₀ ≫ Q.φ = k ≫ i := Q.cart.1.lift_fst _ _ _
  have g₂ : g₀ ≫ pullback.snd _ _ = q ≫ x₀ := Q.cart.1.lift_snd _ _ _
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left,
      r₀ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g₀ ≫ pullback.fst _ _ :=
    ⟨pullback.lift ((g₀ ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g₀ ≫ pullback.fst _ _) (Category.comp_id _),
      pullback.lift_snd _ _ _⟩
  have hN : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb hP _ _
  choose σ hσ using fun i => exists_comb q (fun l => GlobalTheory.secPull (ρ.s l) r₀) (b i)
  obtain ⟨u, hu, -⟩ := CrdIso.exists_iso_of_crd Y (O.pull k) _ S.J (fun i => GlobalTheory.secPull (τ i) k) σ
    (pull_isLB hO k) (pull_isLB hN r₀) (by
      simp only [GlobalTheory.nonzeroLocus_secPull]
      rw [← Scheme.Hom.preimage_iSup, hτ]
      rfl) (by
      rintro K _ x v ⟨l, c, hl, hv⟩
      obtain ⟨jP, hj⟩ := exists_chart hP ((x ≫ g₀ ≫ pullback.fst _ _) (IsLocalRing.closedPoint K))
      have hj' : ⊤ ≤ (x ≫ g₀ ≫ pullback.fst _ _) ⁻¹ᵁ ρ.P.L.U jP := (Points.le_preimage_iff _ _).2 hj
      have hβ : spMap (Spec.preimage (x ≫ q)).hom = x ≫ q := Spec.map_preimage _
      have hl' : ⊤ ≤ (x ≫ k) ⁻¹ᵁ O.U (l PUnit.unit) := fun y _ =>
        (mem_pull (L := O) (F := k) (J := l)).1 (hl (x := y) trivial)
      obtain ⟨d, hd, e⟩ := h K (Spec.preimage (x ≫ q)).hom (x ≫ g₀) (x ≫ k) (x ≫ r₀) jP (l PUnit.unit)
        (by rw [hβ, Category.assoc, reassoc_of% g₂, hx₀, Category.assoc])
        (by rw [Category.assoc, Category.assoc, g₁]) (by rw [Category.assoc, Category.assoc, hr₀])
        ((top_le_preimage_iff _ _).1 (by rwa [Category.assoc])) ((top_le_preimage_iff _ _).1 hl')
      have hx : ⊤ ≤ x ⁻¹ᵁ ((LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).pull r₀).U (fun _ _ => jP) := fun y _ => by
        refine mem_pull.2 (Set.mem_iInter.2 fun _ => ?_)
        have := hj' (x := y) trivial
        rw [← hr₀] at this
        exact this
      refine ⟨fun _ _ => jP, c * (Units.mk0 d hd)⁻¹, hx, fun i => ?_⟩
      have e₁ : valR x _ ((GlobalTheory.secPull (τ i) k).f l) = valF (x ≫ k) _ ((τ i).f (l PUnit.unit)) :=
        Points.valR_appLE x k _ hl _
      have e₂ := valR_comb q r₀ ρ.s (b i) (σ i) (hσ i) x _ hx
      rw [hv, e₁, e₂.trans (e i)]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, _root_.mul_assoc, inv_mul_cancel_left₀ hd])
  have e₁ := (cls_eq_iff (pull_isLB hO k) (pull_isLB hN r₀)).2 ⟨u, hu⟩
  have e₂ := (cls_eq_iff (pull_isLB hL Q.φ) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have e₃ : cls _ hN = S.N • CechPic.pull (snd (baseOver (Sp S.R)) ρ.P.A).left (cls _ hP) :=
    (cls_linComb hP _ _ _).trans (by rw [Fin.sum_univ_one, natCast_zsmul])
  rw [cls_pull hL, cls_pull hP] at e₂
  rw [cls_pull hO, cls_pull hN, e₃] at e₁
  rw [e₁, map_nsmul, map_nsmul, ← pull_comp, ← pull_comp, ← g₁, hr₀, pull_comp, pull_comp, e₂]

theorem isNormalScheme_opens {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) (V : X.Opens) :
    Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem relAmple_affine [IsLocallyNoetherian M.Z] (hO : S.Over₀ M U₀) {EE : M.Lat S.J} (hs : Q.SecO EE) (hA : Q.Ab)
    (V : M.Z.Opens) (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) (hab : (V : Set M.Z) ⊆ abLocus Q.G)
    (b : Matrix S.J S.J Ω) (hb : ∀ z ∈ V, EE.E z = Submodule.span (M.O z) (Set.range b)) :
    RelAmple (Over.mk (Q.G.hom ∣_ V)) (Q.L.L.pull (Q.G.hom ⁻¹ᵁ V).ι) := by
  obtain ⟨O, τ, hO', hτ, h, -, ha⟩ := hs V b hV hb
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ Q.G
  have sq := (isPullback_morphismRestrict Q.G.hom V).flip
  have : Smooth (Over.mk (Q.G.hom ∣_ V)).hom := inferInstanceAs (Smooth (Q.G.hom ∣_ V))
  have : GeometricallyIntegral (Over.mk (Q.G.hom ∣_ V)).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) sq ‹_›
  have : IsProper (Over.mk (Q.G.hom ∣_ V)).hom := by
    have := hA.2 V hab
    change IsProper (Q.G.hom ∣_ V)
    rw [← sq.isoPullback_hom_snd]
    infer_instance
  have hr : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  let j : Sp Ω ⟶ V := IsOpenImmersion.lift V.ι M.pt hr
  have hj : j ≫ V.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have sqj := (IsOpenImmersion.isPullback_lift_id M.pt V.ι hr).flip
  have : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) sqj (EndoExtend.isPreimmersion_pt M)
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) sqj (EndoExtend.flat_pt M)
  have : IsDominant (j ≫ V.ι) := hj ▸ M.isDominant_pt
  have : IsDominant j := IsDominant.of_comp_of_isOpenImmersion j V.ι
  have he : eSec Q.G ≫ Q.G.hom = 𝟙 _ := Over.w _
  have : IsIntegral (pullback (Q.G.hom ∣_ V) j) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback (Q.G.hom ∣_ V) j)
  refine relAmple_of_densePart j (isNormalScheme_opens hO.normal V) (Over.mk (Q.G.hom ∣_ V))
    (sq.lift (V.ι ≫ eSec Q.G) (𝟙 _) (by rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _))
    (sq.lift_snd _ _ _) (pull_isLB Q.L.isLB _) hO' (N := S.N) (one_le_two.trans S.N_ge) (ha hab) ?_
  refine cls_generic Q hO.ne (Q.G.hom ⁻¹ᵁ V).ι (pullback.fst (Q.G.hom ∣_ V) j) (pullback.snd _ _) ?_ b O τ hO' hτ h
  rw [Category.assoc, sq.w, pullback.condition_assoc, hj]

theorem relAmple_open [IsLocallyNoetherian M.Z] (hO : S.Over₀ M U₀) {EE : M.Lat S.J} (hs : Q.SecO EE) (hA : Q.Ab)
    (W : M.Z.Opens) (hW : (W : Set M.Z) ⊆ abLocus Q.G) :
    RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) := by
  have hL := Q.L.isLB
  have : IsProper ((Over.pullback W.ι).obj Q.G).hom := hA.2 W hW
  refine AmpleLocal.relAmple_of_locally _ _ _ (pull_isLB hL _) inferInstance inferInstance fun s => ?_
  obtain ⟨B, b, hz, -, hb⟩ := EE.loc s.1
  obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := B ⊓ W) (x := s.1) ⟨hz, s.2⟩
  have ha := relAmple_affine Q hO hs hA V hV ⟨_, hx⟩ (fun z hz => hW (hle hz).2) b fun z hz => hb z (hle hz).1
  refine ⟨W.ι ⁻¹ᵁ V, hx, ?_⟩
  have h := IsPullback.of_hasPullback Q.G.hom W.ι
  have le' : pullback.snd Q.G.hom W.ι ⁻¹ᵁ (W.ι ⁻¹ᵁ V) ≤ pullback.fst Q.G.hom W.ι ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ V) :=
    fun y hy => (congrArg (fun q => q y ∈ V) h.w).mpr hy
  let ψ := (pullback.fst Q.G.hom W.ι).resLE _ _ le'
  have hψ : ψ ≫ (Q.G.hom ⁻¹ᵁ V).ι = _ ≫ pullback.fst Q.G.hom W.ι := Scheme.Hom.resLE_comp_ι _ le'
  have H : IsPullback ψ (pullback.snd Q.G.hom W.ι ∣_ (W.ι ⁻¹ᵁ V)) (Q.G.hom ∣_ V) (W.ι ∣_ V) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict Q.G.hom V).flip
    · rw [hψ, morphismRestrict_ι]
      exact (isPullback_morphismRestrict _ _).flip.paste_horiz h
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
        reassoc_of% hψ, h.w, morphismRestrict_ι_assoc]
  obtain ⟨w, hw⟩ : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom W.ι)).pull
      (pullback.snd Q.G.hom W.ι ⁻¹ᵁ (W.ι ⁻¹ᵁ V)).ι) ((Q.L.L.pull (Q.G.hom ⁻¹ᵁ V).ι).pull ψ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    rw [cls_pull (pull_isLB hL _), cls_pull (pull_isLB hL _), cls_pull hL, cls_pull hL, ← pull_comp, ← pull_comp, hψ]
  have : IsAffine V := hV
  exact relAmple_pull (A := Over.mk (Q.G.hom ∣_ V)) (A' := Over.mk (pullback.snd Q.G.hom W.ι ∣_ (W.ι ⁻¹ᵁ V))) H
    (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha

theorem kTriv_of_factor {T : Scheme.{0}} (G' : Over T) [GrpObj G'] (f : T ⟶ U₀) (φ : G'.left ⟶ Q.G.left)
    (h : IsGrpPullback G' Q.G (f ≫ U₀.ι) φ) {L' : LB G'.left} (hL' : L'.IsLB) (e : LBIso L' (Q.L.L.pull φ)) :
    KTriv G' L' := by
  have hP := ρ.P.isLB
  have hL := Q.L.isLB
  let ψ := Q.cart.1.lift φ (G'.hom ≫ f) (h.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ Q.φ = φ := Q.cart.1.lift_fst _ _ _
  have h₁ := (Q.cart.cancel (h.congr rfl hψ.symm) (Q.cart.1.lift_snd _ _ _)).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)
  obtain ⟨w, hw⟩ : LBIso L' (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Q.u₀)) := by
    have e₁ := (cls_eq_iff hL' (pull_isLB hL _)).2 e
    have e₂ := (cls_eq_iff (pull_isLB hL Q.φ) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
    refine (cls_eq_iff hL' (pull_isLB hP _)).1 (e₁.trans ?_)
    rw [cls_pull hL, cls_pull hP] at e₂
    rw [cls_pull hL, cls_pull hP, ← hψ]
    exact (pull_comp ψ Q.φ _).trans ((congrArg _ e₂).trans (pull_comp ψ _ _).symm)
  exact kTriv_pull h₁ hP hL' ((isGen_iff w).1 hw) ρ.P.ktriv

end Model

theorem relAmple_and_kTriv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), Laws → S.Over₀ M U₀ → Q.SecO EE → Q.Ab → ∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) := by
  intro o Ω _ _ _ hB S ρ M U₀ EE Q laws hO hs hA W hW
  have := hB.ded
  have := hB.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have ha := relAmple_open Q hO hs hA W hW
  refine ⟨ha, ?_⟩
  rcases (W : Set M.Z).eq_empty_or_nonempty with h0 | hne
  · intro R _ t x _
    have : IsEmpty (Spec (CommRingCat.of R)) := ⟨fun p => (h0.le (t p).2 : False)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := Spec (CommRingCat.of R))).hom_ext _ _)
  have : Nonempty W := hne.to_subtype
  have hL := Q.L.isLB
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have gp := isGrpPullback_pullback Q.G W.ι
  obtain ⟨hL', hr, ⟨c, -⟩, -⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf gp) Q.L Q.cub
  have hab : IsAbelianScheme ((Over.pullback W.ι).obj Q.G) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) gp.1 ‹_›, hA.2 W hW,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) gp.1 ‹_›⟩
  refine GlobalTheory.T.kTriv_of_kTriv_nonemptyOpen_normal_charZero laws W (isNormalScheme_opens hO.normal W) (fun n hn h => ?_) (W.ι ⁻¹ᵁ U₀) ?_ _
    ((cubeMapOf gp).rigLB Q.L hL' hr) c hab ha ?_
  · have e := congrArg ((M.res W hne).comp W.topIso.hom.hom) h
    rw [map_natCast, map_zero] at e
    exact hn (Nat.cast_eq_zero.1 e)
  · obtain ⟨z, hz⟩ := M.nonempty_inf hne hO.ne
    exact ⟨⟨z, hz.1⟩, hz.2⟩
  · refine kTriv_of_factor Q _ (W.ι ∣_ U₀) _ (((isGrpPullback_pullback _ (W.ι ⁻¹ᵁ U₀).ι).comp gp).congr
      (morphismRestrict_ι _ _).symm rfl) (pull_isLB hL' _) ?_
    exact (cls_eq_iff (pull_isLB hL' _) (pull_isLB hL _)).1 (pull_comp _ _ (cls _ hL)).symm

end GlobalTheory.ZH.AbPol

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_relAmple_and_principal_abelianLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), Laws → S.Over₀ M U₀ → Q.SecO EE → Q.Ab → ∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) := by
  first | exact @GlobalTheory.ZH.AbPol.relAmple_and_kTriv | exact GlobalTheory.ZH.AbPol.relAmple_and_kTriv | (intros; apply GlobalTheory.ZH.AbPol.relAmple_and_kTriv <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secOn_power_of_local_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  first | exact @GlobalTheory.ZH.exists_secOn_genVal_of_bases | exact GlobalTheory.ZH.exists_secOn_genVal_of_bases | (intros; apply GlobalTheory.ZH.exists_secOn_genVal_of_bases <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH

theorem exists_sec_pull_of_comp {X Y Z : Scheme.{0}} (L : LB X) (j : Y ⟶ X) (n : Z ⟶ Y) (φ : Z ⟶ X) (e : n ≫ j = φ)
    (σ : LB.Sec (L.pull j)) : ∃ θ : LB.Sec (L.pull φ), ∀ y, n y ∈ nonzeroLocus σ → y ∈ nonzeroLocus θ := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : PUnit => j) (fun _ => 1) σ n, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : y ∈ Z.basicOpen ((n.app _).hom (σ.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  have h₂ : y ∈ (L.pull (n ≫ j)).U k := mem_pull.2 ((mem_pull (F := j)).1 (Y.basicOpen_le _ hk))
  exact (Z.basicOpen_res _ _).ge ⟨h₂, h₁⟩

theorem unif_pullback_of_unif_ring : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → IsOpen (abLocus Q.G) → Q.Ab → Q.LocTheta → HypS Q.G Q.L.L → (∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι))) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus Q.G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj Q.G)], ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj Q.G)), LBIso U.LG.L (Q.L.L.pull (pullback.fst Q.G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Q.G) := by
  intro H o Ω _ _ _ _ S ρ M U₀ Q _ hop hab hth hS hpol R _ _ _ _ hN hI hC ξ hne _
  have h := isGrpPullback_pullback Q.G ξ
  obtain ⟨hL, hr, ⟨c', -⟩, hs⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf h) Q.L Q.cub
  have hrefl : LBIso (Q.L.L.pull (pullback.fst Q.G.hom ξ)) (Q.L.L.pull (pullback.fst Q.G.hom ξ)) :=
    ⟨_, CubePf.idIsoL_isGen hL⟩
  let W₀ : M.Z.Opens := ⟨abLocus Q.G, hop⟩
  let W : (Sp R).Opens := ξ ⁻¹ᵁ W₀
  let G' := (Over.pullback ξ).obj Q.G
  have h₀ := isGrpPullback_pullback Q.G W₀.ι
  have h₁ := isGrpPullback_pullback G' W.ι
  have sq : (ξ ∣_ W₀) ≫ W₀.ι = W.ι ≫ ξ := morphismRestrict_ι ξ W₀
  have h₂ := (h₁.comp h).congr sq.symm rfl
  let ψ : ((Over.pullback W.ι).obj G').left ⟶ ((Over.pullback W₀.ι).obj Q.G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst Q.G.hom W₀.ι = pullback.fst G'.hom W.ι ≫ pullback.fst Q.G.hom ξ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback W.ι).obj G') ((Over.pullback W₀.ι).obj Q.G) (ξ ∣_ W₀) ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hsa := IsSemiAbelian.pullback W₀.ι Q.G Q.semi
  have hA : IsAbelianScheme ((Over.pullback W₀.ι).obj Q.G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := hab.2 W₀ subset_rfl, geomConnected := hsa.geomConnected }
  have hiso : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom ξ)).pull (pullback.fst G'.hom W.ι))
      ((Q.L.L.pull (pullback.fst Q.G.hom W₀.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => pullback.fst G'.hom W.ι) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => (Category.comp_id _).symm)
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => ψ) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => hψ.trans (Category.comp_id _).symm)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB Q.L.isLB (𝟙 _))⟩
  obtain ⟨hA', ha, hk⟩ := GlobalTheory.pol_pull _ _ _ _ _ ψ _ _ (pull_isLB Q.L.isLB _) (pull_isLB hL _) hA h₃ hiso
  obtain ⟨ha₀, hk₀⟩ := hpol W₀ subset_rfl
  have hsp : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G') := by
    obtain ⟨E, hE⟩ := GlobalTheory.ZJ.SplitAll.fieldPoint (G := Q.G) Q.split _ (spMap (IsLocalRing.residue R) ≫ ξ)
    exact ⟨E, isGt_of_iso (pullCompIso _ ξ Q.G) hE⟩
  have hθ' : ∃ θ : LB.Sec (Q.L.L.pull (pullback.fst Q.G.hom ξ)), ∃ x ∈ nonzeroLocus θ,
      G'.hom x = IsLocalRing.closedPoint R := by
    obtain ⟨N, σ, hz, hσ⟩ := hth (ξ (IsLocalRing.closedPoint R))
    have hξ : ξ ⁻¹ᵁ N = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hz
    obtain ⟨n, hn⟩ : ∃ n : G'.left ⟶ (Q.G.hom ⁻¹ᵁ N).toScheme, n ≫ (Q.G.hom ⁻¹ᵁ N).ι = pullback.fst Q.G.hom ξ :=
      ⟨IsOpenImmersion.lift _ (pullback.fst Q.G.hom ξ) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ N) h.1.w).mpr (hξ.ge (Set.mem_univ (G'.hom y)))),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨θ, hθ⟩ := exists_sec_pull_of_comp Q.L.L _ n _ hn σ
    obtain ⟨x, hx, hx'⟩ := hσ _ hz
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback h.1 _ _ hx'
    refine ⟨θ, y, hθ y ?_, hy'⟩
    have e : n y = x := (Q.G.hom ⁻¹ᵁ N).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q y) hn).trans hy)
    rwa [e]
  obtain ⟨D, A, U, hU, hP⟩ := H R hN hI hC G' ((cubeMapOf h).rigLB Q.L hL hr) c' W
    (IsSemiAbelian.pullback ξ Q.G Q.semi) (hs Q.sym)
    (GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.G G' ξ _ Q.L.L _ Q.L.isLB hL h hrefl hS) hsp hθ' hne
    (Set.ext fun x => abLocus_pullback abLocusOne Q.semi h.1 x) hA'.proper
    (ha ha₀) (hk hk₀)
  exact ⟨D, A, U, by rw [hU]; exact hrefl, hP⟩

end GlobalTheory.ZH

end
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  first | exact @GlobalTheory.ZH.CoordMap.exists_coordMap | exact GlobalTheory.ZH.CoordMap.exists_coordMap | (intros; apply GlobalTheory.ZH.CoordMap.exists_coordMap <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_projSpace_of_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (m : ℕ) (e : Fin (m + 1) ≃ J), ImmBy p H s Set.univ → ∃ φ : X ⟶ PSpace k m, IsClosedImmersion φ ∧ φ ≫ PSpace.str k m = p ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd (ProjSpace.O1 k m) (ProjSpace.coord k m) (x ≫ φ) (fun i => v (e i)) := by
  first | exact @GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | exact GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy | (intros; apply GlobalTheory.ZH.ImmProj.exists_closedImmersion_of_immBy <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isImmersion_projSpace_of_local_linearChange : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  first | exact @GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | exact GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | (intros; apply GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
  {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem Clos.crd_chart_of_generic (C : Clos ρ M U₀ EE) (l : C.Λ) {K : Type} [Field K] (β : Ω →+* K)
    (x : Sp K ⟶ (C.P.hom ⁻¹ᵁ C.W l).toScheme) (hx : x ≫ (C.P.hom ⁻¹ᵁ C.W l).ι ≫ C.P.hom = spMap β ≫ M.pt)
    (s : S.J → K) (hs : Crd C.O1 C.st (x ≫ (C.P.hom ⁻¹ᵁ C.W l).ι) s) (b : Matrix S.J S.J Ω) (m' : Matrix S.J S.J K)
    (hm : m' * (b * (C.c l).map (valF M.pt (C.W l))).map β = 1) (d : K) (hd : d ≠ 0) (t : S.J → K)
    (ht : ∀ i, ∑ j, β (b i j) * s j = d * t i) :
    Crd (C.O1.pull (C.P.hom ⁻¹ᵁ C.W l).ι) (C.σ l) x (m'.mulVec t) := by
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (H := C.O1.pull (C.P.hom ⁻¹ᵁ C.W l).ι)
    (LB.isLB_linComb C.isLB _ _) (C.σ l) x
  have h1 := C.rel l K x w hw
  rw [hx] at h1
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hs h1
  have hc : (C.c l).map (valR (spMap β ≫ M.pt) (C.W l)) = ((C.c l).map (valF M.pt (C.W l))).map β := by
    ext i j
    exact valR_spMap_comp β M.pt _ (M.top_le_preimage_pt (C.ne l)) _
  rw [hc] at hu
  have h2 : (((C.c l).map (valF M.pt (C.W l))).map β).mulVec w = (u : K) • s := funext hu
  have h3 : (b.map β).mulVec s = d • t := funext ht
  have h4 : w = ((u : K) * d) • m'.mulVec t := by
    have := congrArg (fun n => n.mulVec w) hm
    simp only [Matrix.one_mulVec] at this
    rw [← this, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3,
      smul_smul, Matrix.mulVec_smul]
  have h5 : (u : K) * d ≠ 0 := mul_ne_zero u.ne_zero hd
  have h6 := CrdCalc.crd_smul (Units.mk0 _ h5)⁻¹ hw
  convert h6 using 1
  funext j
  rw [h4]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_cancel_left₀ h5]

theorem exists_mem_basicOpen_of_geometric {X : Scheme.{0}} {J I : Type} {U : I → X.Opens} (σ : J → ∀ j, Γ(X, U j))
    (x : X) (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (g : Sp K ⟶ X), (∀ w, g w = x) → ∃ i j, valF g _ (σ i j) ≠ 0) :
    ∃ i j, x ∈ X.basicOpen (σ i j) := by
  let k : Type := X.residueField x
  let K : Type := AlgebraicClosure k
  let g : Sp K ⟶ X := spMap (algebraMap k K) ≫ X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, j, hij⟩ := h K g hg
  have hU : ⊤ ≤ g ⁻¹ᵁ U j := by
    by_contra h0
    exact hij (dif_neg h0)
  have := (le_preimage_basicOpen_iff g hU (σ i j)).2 (Ne.isUnit hij) (x := IsLocalRing.closedPoint K) trivial
  exact ⟨i, j, hg (IsLocalRing.closedPoint K) ▸ this⟩

theorem ZHPre.immersedBy_of_clos (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (hU : (U₀ : Set M.Z).Nonempty)
    (k : Q.G.left ⟶ C.P.left) [IsOpenImmersion k] (hk : k ≫ C.P.hom = Q.G.hom)
    (hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (v : S.J → K),
      ρ.Crd (x ≫ pullback.fst _ _) v → Crd C.O1 C.st (x ≫ Q.φ ≫ k) v)
    (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω)
    (hb : ∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b))
    (σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j))
    (hσ : ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧
      GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i))
    (hz : ∀ x ∈ Q.G.hom ⁻¹ᵁ W, ∃ i j, x ∈ Q.G.left.basicOpen (σ i j)) :
    ImmersedBy Q.G.hom M.s (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) σ := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card S.J = m + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ S.J := (Fintype.equivFinOfCardEq hm).symm
  obtain ⟨π, hπ, hcl, hπc⟩ := GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero o _ _ Q.G.hom M.s _ _ _ σ m e (fun i => (hσ i).1) hz
  refine ⟨m, e, π, hπ, ?_, hcl⟩
  let V := Q.G.hom ⁻¹ᵁ W
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  refine GlobalTheory.T.isImmersion_projSpace_of_local_linearChange o _ _ M.s (V.ι ≫ Q.G.hom) m π hπ fun y => ?_
  have hyW : (V.ι ≫ Q.G.hom) y ∈ W := by
    rw [Scheme.Hom.comp_apply]
    exact y.2
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ ((V.ι ≫ Q.G.hom) y)))
  have hne : ((W ⊓ C.W l : M.Z.Opens) : Set M.Z).Nonempty := ⟨_, hyW, hl⟩
  obtain ⟨n, n', hn, hn'⟩ := exists_matrix_mul_eq_one_of_span_eq o Ω M S.J W (C.W l) b (C.B l) (C.c l)
    (fun z hz => (hb z hz.1).2.symm.trans (C.basis l z hz.2)) (C.c_inv l)
  replace hn' := hn' hne
  let Y := (V.ι ≫ Q.G.hom) ⁻¹ᵁ (W ⊓ C.W l)
  have hr : Set.range (Y.ι ≫ V.ι ≫ k) ⊆ Set.range (C.P.hom ⁻¹ᵁ C.W l).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change C.P.hom ((Y.ι ≫ V.ι ≫ k) w) ∈ C.W l
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hk, Scheme.Hom.comp_apply]
    exact w.2.2
  let κ := IsOpenImmersion.lift (C.P.hom ⁻¹ᵁ C.W l).ι (Y.ι ≫ V.ι ≫ k) hr
  have hκ : κ ≫ (C.P.hom ⁻¹ᵁ C.W l).ι = Y.ι ≫ V.ι ≫ k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (κ ≫ (C.P.hom ⁻¹ᵁ C.W l).ι) := by rw [hκ]; infer_instance
  have : IsOpenImmersion κ := IsOpenImmersion.of_comp κ (C.P.hom ⁻¹ᵁ C.W l).ι
  obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := GlobalTheory.T.exists_closedImmersion_projSpace_of_sections _ _ _ _ _ (C.σ l) m e (C.imm l)
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hU
  have hgen : ∀ T : Q.G.left.Opens, ∀ p ∈ T, Set.range (g ≫ Q.φ) ⊆ T := by
    rintro T p hp _ ⟨w, rfl⟩
    rw [h4]
    exact (genericPoint_specializes p).mem_open T.isOpen hp
  have hgG : g ≫ Q.φ ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [← h1]
    exact congrArg (g ≫ ·) Q.cart.1.w
  have hr' : Set.range (g ≫ Q.φ) ⊆ Set.range (Y.ι ≫ V.ι) := by
    have := hgen (Y.ι ≫ V.ι).opensRange _ ⟨⟨y, hyW, hl⟩, rfl⟩
    exact this
  let ξ := IsOpenImmersion.lift (Y.ι ≫ V.ι) (g ≫ Q.φ) hr'
  have hξ : ξ ≫ Y.ι ≫ V.ι = g ≫ Q.φ := IsOpenImmersion.lift_fac _ _ _
  have hξf : ξ ≫ Y.ι ≫ V.ι ≫ Q.G.hom = spMap β ≫ M.pt := by
    rw [← hgG, ← reassoc_of% hξ]
  obtain ⟨jL, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ Q.φ) Q.L.isLB.cover
  have hL := (top_le_preimage_iff _ _).1 hj
  have hgV : Set.range (g ≫ Q.φ) ⊆ V := hgen V _ y.2
  let t : S.J → K := fun i => valF (g ≫ Q.φ) _ (σ i fun _ => jL)
  have hpt := M.top_le_preimage_pt hne
  let ev : Γ(M.Z, W ⊓ C.W l) →+* K := β.comp (M.res _ hne)
  have hev : valF (ξ ≫ Y.ι ≫ V.ι ≫ Q.G.hom) (W ⊓ C.W l) = ev := by
    rw [hξf]
    funext a
    exact (valR_spMap_comp β M.pt _ hpt a).trans (congrArg β (M.res_apply _ hne a).symm)
  refine ⟨W ⊓ C.W l, Γ(M.Z, C.W l), inferInstance, M.Z.homOfLE inf_le_right ≫ (C.aff l).isoSpec.hom, κ ≫ ψ,
    n'.submatrix e e, K, inferInstance, ξ, fun i => t (e i), ⟨hyW, hl⟩, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hψ2, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (C.W l).ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [reassoc_of% hκ, hk]
  · rw [Matrix.det_submatrix_equiv_self]
    exact Matrix.isUnit_det_of_left_inverse hn
  · refine ⟨fun p => ?_⟩
    let w₀ : Sp K := IsLocalRing.closedPoint K
    have h5 : (Y.ι ≫ V.ι) (ξ w₀) ⤳ (Y.ι ≫ V.ι) p := by
      rw [← Scheme.Hom.comp_apply ξ, hξ, h4]
      exact genericPoint_specializes _
    have h6 := (Y.ι ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff.1 h5
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w₀)) h6.mem_closure
  · have h5 := hπc K (ξ ≫ Y.ι) (fun _ => jL) (by
      rw [Category.assoc, hξ]
      exact fun w _ => Set.mem_iInter.2 fun _ => hL ⟨w, rfl⟩)
    simp only [Category.assoc] at h5
    rw [hξ] at h5
    exact h5
  · have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
        (fun _ => jP, fun _ => jL) := fun w _ =>
      ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
        Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
    have hω : valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ≠ 0 := by
      refine IsUnit.ne_zero ?_
      rw [valF_eq_valR, valR_eq g _ hw]
      exact (Units.isUnit _).map _
    have hth : β (S.th x₀) ≠ 0 := (map_ne_zero β).2 (hb _ hyW).1.1
    have hs : ρ.Crd (g ≫ pullback.fst _ _) fun j => valF r _ ((ρ.s j).f fun _ => jP) :=
      ⟨r, h2, fun _ => jP, 1, fun w _ => Set.mem_iInter.2 fun _ => by
        have h7 : (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) w ∈ ρ.P.L.U jP := h2 ▸ h3 ⟨w, rfl⟩
        rw [Scheme.Hom.comp_apply] at h7
        exact h7, fun j => by rw [Units.val_one, _root_.one_mul]; rfl⟩
    have hx : (ξ ≫ κ) ≫ (C.P.hom ⁻¹ᵁ C.W l).ι = g ≫ Q.φ ≫ k := by
      rw [Category.assoc, hκ, reassoc_of% hξ]
    have h5 := C.crd_chart_of_generic l β (ξ ≫ κ) (by rw [← Category.assoc, hx, Category.assoc, Category.assoc, hk, hgG]) _
      (hx ▸ hcrd K g _ hs) b (n'.map ev) (by
        have h8 : (b * (C.c l).map (valF M.pt (C.W l))).map β = n.map ev := by
          rw [← hn']
          ext i j
          exact congrArg β (M.res_apply _ hne _).symm
        rw [h8, ← Matrix.map_mul, mul_eq_one_comm.1 hn, Matrix.map_one _ (map_zero _) (map_one _)])
      _ (mul_ne_zero hth (zpow_ne_zero (S.N : ℤ) hω)) t (fun i => by
        rw [_root_.mul_assoc, ← (hσ i).2 K β g r jP jL h1 h2 h3 hL hgV, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_div₀, ← _root_.mul_assoc, mul_div_cancel₀ _ hth])
    have h6 := hψ3 K _ _ h5
    rw [Category.assoc] at h6
    convert h6 using 1
    rw [hev]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply]
    exact e.sum_comp fun j => ev (n' (e i) j) * t j

theorem ThetaSys.isOpen_setOf_TT_eq_bot {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

theorem ZHPre.nonempty_out : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (ex : C.Ext), (∃ e : Q.G.left ≅ C.G.toScheme, e.hom ≫ C.G.ι ≫ C.P.hom = Q.G.hom ∧ Q.u₀ = C.u₀ ∧ HEq (Q.φ ≫ e.hom) ex.a) → S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.Sec → Q.LocTheta → Q.SecO EE → Q.Ab → Nonempty (ZHOut ρ M U₀ EE) := by
  intro hExt hUnif hSS hU hL hL2 hT o Ω _ _ _ _ S ρ M U₀ EE Q C ex ⟨e, he1, he2, he3⟩ hBig hO hEE hSec hLoc hSecO hAb
  obtain ⟨hS, hEndo, hIso⟩ := GlobalTheory.T.endo_lbIso_symmetryHypothesis_extend_normalModel hExt o Ω S ρ M U₀ Q hO
  have hPol := GlobalTheory.T.thetaModel_relAmple_and_principal_abelianLocus o Ω S ρ M U₀ EE Q hL hO hSecO hAb
  have hOpen : IsOpen (abLocus Q.G) := by
    rw [hAb.1]
    exact S.isOpen_setOf_TT_eq_bot M
  have hS' := GlobalTheory.T.exists_sections_pow_line_bundle_from_local_basis hSS hU hL hL2 hT o Ω S ρ M U₀ EE Q hO hEE hSecO
  have hcrd : ∀ (u : U₀.toScheme ⟶ Sp S.R) (a : pullback ρ.P.A.hom u ⟶ C.G.toScheme), u = C.u₀ → HEq a ex.a →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom u) (v : S.J → K),
        ρ.Crd (x ≫ pullback.fst _ _) v → Crd C.O1 C.st (x ≫ a ≫ C.G.ι) v := by
    rintro _ a rfl h K _ x v hv
    rw [eq_of_heq h, ex.a_eq]
    exact C.crd K x v hv
  exact ⟨{
    u₀ := Q.u₀
    u₀_gen := Q.u₀_gen
    G := Q.G
    grp := Q.grp
    comm := Q.comm
    semi := Q.semi
    dim := Q.dim
    qproj := Q.qproj
    φ := Q.φ
    cart := Q.cart
    L := Q.L
    cub := Q.cub
    sym := Q.sym
    w := Q.w
    w_gen := Q.w_gen
    w_rig := Q.w_rig
    hypS := hS
    endo := hEndo
    isoExt := hIso
    split := Q.split
    ab := hAb.1
    pol := hPol
    sec := hSec
    unif := unif_pullback_of_unif_ring hUnif o Ω S ρ M U₀ Q hO hOpen hAb hLoc hS hPol
    theta := GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres hExt hSS hU hL hL2 hT o Ω S ρ M U₀ Q hBig hO hSec hLoc
    secOf := GlobalTheory.T.exists_secOn_power_of_local_bases o Ω S ρ M U₀ EE Q hO.ne fun W x₀ b hb => (hS' W x₀ b hb).imp fun _ h => h.1
    sections := hS'
    imm := fun W x₀ b hb σ hσ => by
      obtain ⟨σ', h1, h2⟩ := hS' W x₀ b hb
      obtain rfl : σ = σ' := funext fun i => Q.eq_of_genVal hO.ne _ _ _ _ _ _ (hσ i).2 (h1 i).2
      refine Q.immersedBy_of_clos C hO.ne (e.hom ≫ C.G.ι) ((Category.assoc _ _ _).trans he1)
        (fun K _ x v hv => ?_) W x₀ b hb σ hσ fun x hx => exists_mem_basicOpen_of_geometric σ x fun K _ _ g hg => ?_
      · have := hcrd _ _ he2 he3 K x v hv
        rwa [Category.assoc] at this
      · refine (h2 K (g ≫ Q.G.hom) ?_).1 g rfl
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Hom.comp_apply, hg]
        exact hx }⟩

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_of_fourProperties_groupScheme : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀) (C : Clos ρ M U₀ EE) (ex : C.Ext), (∃ e : Q.G.left ≅ C.G.toScheme, e.hom ≫ C.G.ι ≫ C.P.hom = Q.G.hom ∧ Q.u₀ = C.u₀ ∧ HEq (Q.φ ≫ e.hom) ex.a) → S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → Q.Sec → Q.LocTheta → Q.SecO EE → Q.Ab → Nonempty (ZHOut ρ M U₀ EE) := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.nonempty_out
end
