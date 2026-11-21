import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplex
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpecMapAppFromSpec
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsIsoOfClosedImmersion
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPointOfIsAffine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemKLOfTrivLam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RigDescent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteGroupHomKernelPullback
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteCommutativeGroupDualCharacter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteSurjectiveOfPoints
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KTrivModelOfTrivLocus
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PreDualOfIsPerfect
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AppTopCompApply
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FewEquationsStatementStatement
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.AbelianDeRham.FreeAbelianDeRham.H1StructureDimLe

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

set_option maxHeartbeats 1000000 in

theorem addAcyclic_pf : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic := by
  intro k _ _ A _ hA M hM hadd hn κ _ _ D hD hc
  have : IsCommMonObj A := hA.comm
  have hp : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  refine GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed k A hA hp M hM ?_ hn κ D hD hc
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hlam).1 ?_
  refine (GlobalTheory.CechPic.cls_cube_two hM (fst A A) (snd A A) hlam).trans ?_
  have h1 := hadd (A ⊗ A) (fst A A) (snd A A)
  have h0 := hadd (A ⊗ A) 1 1
  rw [_root_.mul_one] at h0
  have h0' : GlobalTheory.CechPic.pull (1 : A ⊗ A ⟶ A).left (cls M hM) = 0 := by
    exact add_left_cancel (h0.symm.trans (add_zero _).symm)
  simp only [GlobalTheory.CechPic.lam, h1, h0']
  abel

end CompanionTheory.PfDual
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual

open GlobalTheory.TrivRep in

theorem exists_ideal_locTriv_noeth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ F : LB B.left, F.IsLB → ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) → ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ B _ hB F hF
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI : Smooth B.hom := hB.smooth
  have hP : Nonempty (Perf B.hom F) := GlobalTheory.ProperFinite.nonempty_perf_of_isProper B.hom hF
  have hQ : Nonempty (Perf B.hom (pw F (-1))) := GlobalTheory.ProperFinite.nonempty_perf_of_isProper B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := exists_ideal (TrivOn B.hom F) (TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => loc_iff B.hom F h q

end CompanionTheory.PfDual
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual

open GlobalTheory.TrivSubscheme in

theorem exists_closed_locTriv_noeth : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left → ∀ F : LB (A ⊗ Y).left, F.IsLB → ∃ (H : Over S) (j : H ⟶ Y), IsClosedImmersion j.left ∧ ∀ (T' : Over S) (x : T' ⟶ Y), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (A ◁ x).left).pull ((snd A T').left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro S A Y _ hB hY F hF
  have h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom :=
    IsPullback.of_hasPullback A.hom Y.hom
  obtain ⟨I, hI⟩ := exists_idealSheaf (LocTrivOver (snd A Y).left F) LocTrivOver.comp locTrivOver_of_affine
    (fun U => by
      haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S := U.2.fromSpec ≫ Y.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀
    rw [Over.whiskerLeft_left_fst, Over.w x]
    exact IsPullback.of_hasPullback A.hom T'.hom
  simp only [triv_pull_iff]
  rw [← locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end CompanionTheory.PfDual
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem trivLocus_pf : CompanionTheory.ObstructionTrivialLocus.TrivLocus := by
  intro S A Y _ hA hY N hN h0
  obtain ⟨Z, i, hi, hZ⟩ := exists_closed_locTriv_noeth S A Y hA hY N hN
  refine ⟨Z, i, hi, fun T y => ?_⟩
  have e : lift (fst A T) (snd A T ≫ y) = A ◁ y := by ext <;> simp
  rw [← hZ T y, ev, e]
  constructor
  · intro ht p
    exact ⟨⊤, trivial, CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp _ rfl ht)⟩
  · intro hloc
    have hpb : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
      IsPullback.of_hasPullback _ _
    have e' : y ≫ lift (1 : Y ⟶ A) (𝟙 Y) = lift (1 : T ⟶ A) (𝟙 T) ≫ A ◁ y := by ext <;> simp
    have hsec : Triv ((N.pull (A ◁ y).left).pull (lift (1 : T ⟶ A) (𝟙 T)).left) :=
      CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp y.left (congrArg (·.left) e') h0)
    exact GlobalTheory.exists_gen_of_local_of_section (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left
      (N.pull (A ◁ y).left) (pull_isLB hN _) (congrArg (·.left) (lift_snd (1 : T ⟶ A) (𝟙 T)))
      (GlobalTheory.BaseChangeFns.app_surjective GlobalTheory.globalFns_holds S A hA _ _ T.hom _ _ hpb) hloc hsec

end CompanionTheory.PfDual
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CompanionTheory.PointSurjectivity
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

section Lemmas

variable {k : Type} [Field k] {A T : Over (Sp k)} {M : LB (A ⊗ T).left}

theorem pull_evc_const (hM : M.IsLB) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T) {Y : Over (Sp k)} (a : Y ⟶ A) :
    GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) = evc hM a (toUnit Y ≫ t₀) := by
  rw [pull_evc, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem pull_mul_evc_const [GrpObj A] (hM : M.IsLB) (hadd : IsAdditive M) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T)
    {Y : Over (Sp k)} (a a' : Y ⟶ A) :
    GlobalTheory.CechPic.pull (a * a').left (evc hM (𝟙 A) (toUnit A ≫ t₀)) =
      GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) +
        GlobalTheory.CechPic.pull a'.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) := by
  rw [pull_evc_const, pull_evc_const, pull_evc_const]
  exact (isAdditive_iff hM).1 hadd Y a a' _

end Lemmas

set_option maxHeartbeats 2000000 in

theorem pointSurj_pf : (∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic) → PointSurj := by
  intro hAA k _ _ A B _ _ hA hB P hP hadd hadd' hfin M hM haddM
  by_contra hno
  push Not at hno
  have : IsCommMonObj A := hA.comm
  have : IsCommMonObj B := hB.comm
  have hpA : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  have hpB : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have hpq : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have hsw : (swap P).IsLB := pull_isLB hP _
  obtain ⟨G, hG, eG⟩ := cls_surj
    (GlobalTheory.CechPic.pull (lift (fst A B) (toUnit (A ⊗ B))).left (cls M hM) - cls P hP)
  have cst : ∀ {X : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ X) (Y : Over (Sp k)),
      (toUnit Y ≫ x).left = Y.hom ≫ x.left := fun x Y =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit Y)))

  have sl₁ : ∀ y' : 𝟙_ (Over (Sp k)) ⟶ B, cls _ (pull_isLB hG (lift (𝟙 A) (toUnit A ≫ y')).left) =
      evc hM (𝟙 A) (toUnit A ≫ 𝟙 _) - evc hP (𝟙 A) (toUnit A ≫ y') := fun y' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit,
      Category.comp_id]
    rfl

  have sl₂ : ∀ x' : 𝟙_ (Over (Sp k)) ⟶ A, cls _ (pull_isLB hG (lift (toUnit B ≫ x') (𝟙 B)).left) =
      - evc hsw (𝟙 B) (toUnit B ≫ x') := fun x' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit]
    have e₁ : GlobalTheory.CechPic.pull (lift (toUnit B ≫ x') (toUnit B)).left (cls M hM) = 0 := by
      have e := pull_evc hM (toUnit B) x' (𝟙 _)
      rw [Category.comp_id, GlobalTheory.T.picard_group_of_field_trivial k (evc hM x' (𝟙 _)), map_zero] at e
      exact e.symm
    rw [e₁, zero_sub, evc_swap hP hsw]
    rfl
  have fibB : ∀ (y : Sp k ⟶ B.left) (σ : A.left ⟶ (A ⊗ B).left), y ≫ B.hom = 𝟙 _ →
      σ ≫ (fst A B).left = 𝟙 _ → σ ≫ (snd A B).left = A.hom ≫ y → FibAc A.hom (G.pull σ) := by
    intro y σ hy h₁ h₂
    let y' : 𝟙_ (Over (Sp k)) ⟶ B := Over.homMk y hy
    have hσ : σ = (lift (𝟙 A) (toUnit A ≫ y')).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₁, ← Over.comp_left, lift_fst]
        rfl
      · rw [h₂, ← Over.comp_left, lift_snd, cst]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k A hA _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₁ y', map_sub, map_sub, map_sub, pull_mul_evc_const hM haddM, pull_mul_evc_const hP hadd]
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₁ y', sub_eq_zero] at h0
      refine hno y' ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
      have e := congrArg (GlobalTheory.CechPic.pull (fst A (𝟙_ (Over (Sp k)))).left) h0
      rw [pull_evc, pull_evc, Category.comp_id, Category.comp_id,
        ← Category.assoc (fst A _) (toUnit A) y',
        toUnit_unique (fst A (𝟙_ (Over (Sp k))) ≫ toUnit A) (snd A _)] at e
      refine Eq.trans ?_ (e.trans (cls_ev hP _ _ _).symm)
      rw [evc, lift_fst_snd, Over.id_left, pull_id]
  have htot : FibAc ((fst A B).left ≫ A.hom) G :=
    GlobalTheory.T.fibre_acyclicity_of_sections A.hom B.hom (fst A B).left (snd A B).left hpq hpA G hG fibB
  let F' : Set (Sp k ⟶ A.left) :=
    (fun x : 𝟙_ (Over (Sp k)) ⟶ A => x.left) '' {x | Triv (ev P (toUnit B ≫ x) (𝟙 B))}
  have fibA : ∀ (y : Sp k ⟶ A.left) (σ : B.left ⟶ (A ⊗ B).left), y ≫ A.hom = 𝟙 _ →
      σ ≫ (snd A B).left = 𝟙 _ → σ ≫ (fst A B).left = B.hom ≫ y → y ∉ F' → FibAc B.hom (G.pull σ) := by
    intro y σ hy h₁ h₂ hyF
    let x' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk y hy
    have hσ : σ = (lift (toUnit B ≫ x') (𝟙 B)).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₂, ← Over.comp_left, lift_fst, cst]
        rfl
      · rw [h₁, ← Over.comp_left, lift_snd]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k B hB _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₂ x', map_neg, map_neg, map_neg, pull_mul_evc_const hsw hadd']
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₂ x', neg_eq_zero, evc_swap hP hsw] at h0
      exact hyF ⟨x', (triv_ev_iff hP _ _).2 h0, rfl⟩
  have htot' : FibAc ((snd A B).left ≫ B.hom) G := hpq.w ▸ htot
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨m, D, hD, hc, hac⟩ := GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite B.hom A.hom (snd A B).left (fst A B).left hpq.flip hpB G hG F'
    (hfin.image _) fibA htot' η[A].left (lift (toUnit B ≫ η[A]) (𝟙 B)).left hη
    (by rw [← Over.comp_left, lift_snd]; rfl) (by rw [← Over.comp_left, lift_fst, cst])
  have : Nonempty B.left := ⟨η[B].left (IsLocalRing.closedPoint k)⟩
  refine GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic B.hom _ (pull_isLB hG _) ?_ (Fin m) D hc hac
  refine (cls_eq_zero_iff (pull_isLB hG _)).1 ?_
  rw [sl₂, evc_swap hP hsw, ← Hom.one_def, IsAdditive.evc_one hP hadd, neg_zero]

end CompanionTheory.PfDual
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem fewEquations_of_fewEqSt (hF : FewEqSt) (hLe : H1StructureDimLe) : FewEquations := by
  intro R _ _ _ A _ g hab hsm M hM I hI hJ
  refine hF R A.left A.hom g hab.smooth hab.proper ?_ M hM I hI hJ
  intro X' s' φ hP
  obtain ⟨_, hab', hsm'⟩ := GlobalTheory.CompanionTheory.Hodge.FormBC.exists_grp A g hab hsm s' φ hP
  exact hLe _ (Over.mk s') g hab' hsm'

theorem fewEquations_pf : H1StructureDimLe → FewEquations := fun hLe => fewEquations_of_fewEqSt GlobalTheory.T.FewEquationsStatement hLe

end CompanionTheory.PfDual
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem h1Le : H1StructureDimLe := MainStatements.Hodge.Free.h1Le

theorem trivLocus : TrivLocus := trivLocus_pf

theorem fewEquations : FewEquations := fewEquations_pf h1Le

theorem ciFlat : CIFlat := GlobalTheory.T.CechFlatComplex

theorem trivLocusFlat : TrivLocusFlat := @GlobalTheory.CompanionTheory.TrivFlat.trivLocusFlat fewEquations ciFlat

theorem pointSurj : PointSurj := pointSurj_pf addAcyclic_pf

theorem finDual : FinDual := @GlobalTheory.CompanionTheory.DualAb.finDual_of_univNoeth (@GlobalTheory.CompanionTheory.DualUniv.univNoeth trivLocus trivLocusFlat pointSurj)

theorem kTrivModel : KTrivModel := @GlobalTheory.CompanionTheory.KTrivSpread.kTrivModel_of_trivLocus trivLocus

theorem kTrivDual : KTrivDual := @GlobalTheory.CompanionTheory.DualScheme.ktrivDual kTrivModel finDual

end CompanionTheory.PfDual
end
end
