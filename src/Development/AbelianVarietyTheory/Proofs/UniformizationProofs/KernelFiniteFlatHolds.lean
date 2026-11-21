import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal : ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  first | exact @GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | exact GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_localization_maximal <;> assumption)
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem memKL_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} (x : T' ⟶ A') (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst T' A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T' A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T' A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

end

theorem memKL_iff_memKL_push : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) (A' : Over S') [GrpObj A] [GrpObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left) (L' : LB A'.left) (h : IsGrpPullback A' A f φ), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (T' : Over S') (x : T' ⟶ A'), GlobalTheory.MemKL A' L' x ↔ GlobalTheory.MemKL A L (pushPt h.1.w x) :=
  fun _ _ _ _ _ _ _ _ _ _ h hL hL' hw _ x => ⟨memKL_push h hL hL' hw x, memKL_of_push h hL hL' hw x⟩

end GlobalTheory
end
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem memKL_baseChange_rep : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  intro S S' f B _ L hL H j hrep T' x
  have h := isGrpPullback_pullback B f
  have hL' : (L.pull (pullback.fst B.hom f)).IsLB := LB.isLB_pull hL _
  rw [GlobalTheory.memKL_iff_memKL_push S S' f B _ _ L _ h hL hL' (GlobalTheory.lbIso_self hL') T' x, hrep]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.left ≫ j.left = x.left ≫ pullback.fst B.hom f := congrArg (·.left) hz
    refine ⟨Over.homMk (pullback.lift z.left T'.hom (Over.w z)) (pullback.lift_snd _ _ _), ?_⟩
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w x).symm))
    rw [← hz']
    simp [pullback.lift_fst, pullback.lift_fst_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨Over.homMk (z.left ≫ pullback.fst H.hom f) ?_, ?_⟩
    · have := Over.w z
      simp only [Over.pullback_obj_hom] at this
      simp [pullback.condition, ← this]
    · refine Over.OverMorphism.ext ?_
      change (z.left ≫ pullback.fst H.hom f) ≫ j.left = (z.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst B.hom f
      simp [pullback.lift_fst]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memKernelOfLineBundle_baseChange_representable : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  atlas_forward_decl GlobalTheory.memKL_baseChange_rep
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  first | exact @GlobalTheory.StabFlatLocal.flat_of_isFinite | exact GlobalTheory.StabFlatLocal.flat_of_isFinite | (intros; apply GlobalTheory.StabFlatLocal.flat_of_isFinite <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelFlat

theorem kernelFiniteFlat : Laws → GlobalTheory.Published.KernelFiniteFlatSt := by
  intro hLaw V _ _ A _ hA L hL ha
  obtain ⟨H, j, hj, hfin, hH⟩ := GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample hLaw.globalFns V A hA L hL ha
  refine ⟨H, j, hj, hfin, GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal V H hfin fun m _ => ?_, hH⟩
  let f := spMap (algebraMap V (Localization.AtPrime m))
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have : IsCommMonObj ((Over.pullback f).obj A) := hA'.comm
  have hP : IsProjBy ((Over.pullback f).obj A).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha (Localization.AtPrime m) f
      _ (pullback.fst A.hom f) (pullback.snd A.hom f) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom f)).IsLB := LB.isLB_pull hL _
  have hj' : IsClosedImmersion ((Over.pullback f).map j).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback H.hom f) hfin
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hLaw.globalFns (Localization.AtPrime m) ((Over.pullback f).obj A) hA' hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hLaw _ _ hA' hP _ hL') ((Over.pullback f).obj H)
    ((Over.pullback f).map j) hj' (GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f A L hL H j hH) hfin'

end GlobalTheory.KernelFlat
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.kernelFiniteFlat_holds : _root_.GlobalTheory.Published.KernelFiniteFlatSt :=
  _root_.GlobalTheory.KernelFlat.kernelFiniteFlat _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end
