import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic

namespace GlobalTheory.DiagonalAmple

theorem isAmpleLB_of_cls_eq_lam {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {L N : LB B.left} (hL : L.IsLB) (hA : Out.RelAmple B L) (hN : N.IsLB)
    (e : cls N hN = lam (cls L hL) (𝟙 B) (𝟙 B)) : IsAmpleLB N := by
  have := hB.comm
  have hΘ := AbLaw.CubeProj.exists_gen_theta_of_isProjBy globalFns_holds K B hB
    (WtTower.isProjBy_of_relAmple B hL hA) L hL
  have h₁ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left] at h₁
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ η[B].left := rfl
    rw [this, pull_comp, PrimitiveOverField.pic_field (pull η[B].left (cls L hL)), map_zero]
  have h₂ : lam (cls L hL) (𝟙 B)⁻¹ (𝟙 B) = -(pull ((𝟙 B)⁻¹).left (cls L hL)) - cls L hL := by
    rw [lam, inv_mul_cancel, h₀, Over.id_left, pull_id]
    abel
  have hi : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := by
    have : ((𝟙 B)⁻¹ : B ⟶ B) = GrpObj.inv := Category.id_comp _
    rw [this]; infer_instance
  have : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left := inferInstanceAs (IsIso ((Over.forget _).map ((𝟙 B)⁻¹ : B ⟶ B)))
  have hL' := isAmpleLB_of_relAmple_of_isAffine B hL hA
  have hP : IsAmpleLB (L.pull ((𝟙 B)⁻¹).left) := hL'.pull_of_isAffineHom _
  refine hL'.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
  rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_pull hL, e, eq_neg_of_add_eq_zero_left h₁.symm, h₂]
  abel

variable {S : Scheme.{0}}

theorem diag_sqToBase (A : Over S) {S' : Scheme.{0}} (s : S' ⟶ S) :
    (lift (𝟙 ((Over.pullback s).obj A)) (𝟙 _)).left ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s =
      pullback.fst A.hom s ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    simp
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]
    simp

theorem isAmpleLB_geometricFibre (P : PPAS S) {M : LB P.A.left} (hM : M.IsLB)
    (e : cls M hM = pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) :
    IsAmpleLB (M.pull (pullback.fst P.A.hom s)) := by
  obtain ⟨L, hL, hA, -, hc⟩ := P.isPol.2.2 Ω s
  refine isAmpleLB_of_cls_eq_lam ((Over.pullback s).obj P.A) (AbLaw.CubeGen.isAb_baseChange P.isAb s) hL hA
    (LB.isLB_pull hM _) ?_
  have h := congrArg (pull (lift (𝟙 ((Over.pullback s).obj P.A)) (𝟙 _)).left) hc
  rw [pull_lam, lift_fst, lift_snd, ← pull_comp, diag_sqToBase, pull_comp, ← e] at h
  exact h

theorem isProjOver_of_locally (A : Over S) [IsProper A.hom] {M : LB A.left} (hM : M.IsLB)
    (h : ∀ y : S, ∃ U : S.Opens, IsAffineOpen U ∧ y ∈ U ∧ IsAmpleLB (M.pull (A.hom ⁻¹ᵁ U).ι))
    (hS : IsProjOver (ShFam.Pad.toSpZ S)) : IsProjOver (ShFam.Pad.toSpZ A.left) := by
  obtain ⟨hp, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hS
  have hA : Out.RelAmple A M := AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun y => by
    obtain ⟨U, hU, hy, ha⟩ := h y
    have : IsAffine U := hU
    have : IsProper (Over.mk (A.hom ∣_ U)).hom := inferInstanceAs (IsProper (A.hom ∣_ U))
    exact ⟨U, hy, (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (A.hom ∣_ U)) ha.isLB).2 ha⟩
  obtain ⟨-, N, hN⟩ := RelAmpleQProj.isProper_and_exists_isAmpleLB A hM hA hH
  have e : ShFam.Pad.toSpZ A.left = A.hom ≫ ShFam.Pad.toSpZ S := specZIsTerminal.hom_ext _ _
  have : IsProper (ShFam.Pad.toSpZ A.left) := by rw [e]; infer_instance
  exact hN.isProjOver _

end GlobalTheory.DiagonalAmple
end
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.ProperFinite

theorem finite_coh_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsProper f] (F : X.Modules) [QCoh.IsFiniteQC F] (p : ℕ) :
    letI := algebraΓOfHom f; Module.Finite R (coh F p) :=
  finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p

theorem nonempty_perf_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) : Nonempty (Perf f M) := by
  let := algebraΓOfHom f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have := Twist.isFiniteQC_twist (F := structureModule Y) hM
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD') (fun n => by
        obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
        have := finite_coh_of_isProper f (twist (structureModule Y) M) n
        exact Module.Finite.equiv e.symm)
  exact perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩

open FibreLift in

theorem exists_pull_eq_smul {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {Y₀ : Scheme.{0}} {π : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Sp K}
    (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))) (hH : FirstCohomologyVanishes (M.pull π))
    (x₀ : SecOnR f₀ (M.pull π) ⊤) :
    ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  obtain ⟨P⟩ := nonempty_perf_of_isProper f hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm

open AmpleNear in

theorem relAmple_near_fibre {R : Type} [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [IsProper B.hom]
    [Flat B.hom] {L : LB B.left} (hL : L.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a)
    (hA : RelAmple ((Over.pullback (spMap g)).obj B) (L.pull (pullback.fst B.hom (spMap g)))) :
    ∃ r : R, g r ≠ 0 ∧
      RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r))).obj B)
        (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)))) := by
  have h := IsPullback.of_hasPullback B.hom (spMap g)
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1
    ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Sp R) (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'

open FibreAmple in

theorem relAmple_of_geometricFibres {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [IsProper A.hom]
    [Flat A.hom] {M : LB A.left} (hM : M.IsLB)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), IsAmpleLB (M.pull (pullback.fst A.hom y))) :
    RelAmple A M := by
  refine AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Sp Γ(S, V) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback A.hom t
  have hL := pull_isLB hM (pullback.fst A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  have : IsProper (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Flat (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (Flat (pullback.snd A.hom t))
  have : IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom _))
  obtain ⟨r, hr, hA⟩ := relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _)
      ((relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)).2 (hfib _ _)))
  let D : (Sp Γ(S, V)).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.ProperFinite

theorem GlobalTheory.PPAS.isProjOver_of_isProjOver_base : ∀ (S : Scheme.{0}) (P : GlobalTheory.PPAS S),
    IsProjOver (GlobalTheory.ShFam.Pad.toSpZ S) → IsProjOver (GlobalTheory.ShFam.Pad.toSpZ P.A.left) := by
  intro S P hS
  have := P.isAb.proper
  have := P.isAb.smooth
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hS).1
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ShFam.Pad.toSpZ S)
  obtain ⟨M, hM, e⟩ := CechPic.cls_surj (CechPic.pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c)
  have hA := ProperFinite.relAmple_of_geometricFibres P.A hM (DiagonalAmple.isAmpleLB_geometricFibre P hM e)
  refine DiagonalAmple.isProjOver_of_locally P.A hM (fun y => ?_) hS
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := y) trivial
  exact ⟨V, hV, hy, isAmpleLB_of_relAmple P.A hM hA V hV⟩
end
end
