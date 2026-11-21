import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFinite
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (p : Y ⟶ Sp F) (σ : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d p] [SmoothOfRelativeDimension d (σ ≫ p)] (K : CanonLB p d) (K' : CanonLB (σ ≫ p) d),
    ∃ J : H0 (σ ≫ p) (LB.div K'.bundle (K.bundle.pull σ)) ⊤, ∀ x : X, Function.Bijective (σ.stalkMap x).hom →
      ∀ (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a),
        IsUnit (H0.germ a x (memTop x) ha J) := by
  first | exact @GlobalTheory.exists_jacobian_section_isUnit_germ | exact GlobalTheory.exists_jacobian_section_isUnit_germ | (intros; apply GlobalTheory.exists_jacobian_section_isUnit_germ <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  first | exact @GlobalTheory.isIntegral_of_nonempty_modif | exact GlobalTheory.isIntegral_of_nonempty_modif | (intros; apply GlobalTheory.isIntegral_of_nonempty_modif <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y, IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  first | exact @GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | exact GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr | (intros; apply GlobalTheory.CompHS.Modif.exists_bijective_stalkMap_of_dvr <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  first | exact @GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | exact GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull | (intros; apply GlobalTheory.germToFunctionField_mem_range_stalk_of_mul_pull <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.ModifCanon
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

theorem stalkMap_bijective_of_isIso_restrict : ∀ (Y X : Scheme.{0}) (σ : X ⟶ Y) (U : Y.Opens), IsIso (σ ∣_ U) →
    ∀ x : X, x ∈ σ ⁻¹ᵁ U → Function.Bijective (σ.stalkMap x).hom := by
  intro Y X σ U h x hx
  have e := morphismRestrictStalkMap σ U ⟨x, hx⟩
  have h1 : IsIso ((σ ∣_ U).stalkMap ⟨x, hx⟩) := ((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 h).2 _
  have h2 : IsIso (σ.stalkMap x) := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h1
  exact ConcreteCategory.bijective_of_isIso _

theorem isUnit_val_of_isUnit_germ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens)
    (x : Sp ℂ ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) (e : Sp ℂ)
    (hy : x e ∈ O) (hiy : x e ∈ B.U i), IsUnit (H0.germ i (x e) hy hiy f) → IsUnit (H0.val x i hO hi f) := by
  intro k _ Y p B O x i hO hi f e hy hiy hu
  have hb : x e ∈ Y.basicOpen (f.loc i) := (Y.mem_basicOpen _ _ (Vanishing.memInf hy hiy)).2 hu
  have hV : ⊤ ≤ x ⁻¹ᵁ Y.basicOpen (f.loc i) := fun y _ => by rw [Subsingleton.elim y e]; exact hb
  rw [H0.val_apply, ← evalPt_res x (Y.basicOpen_le (f.loc i)) _ hV]
  exact (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (f.loc i)).map _

end GlobalTheory.ModifCanon

namespace GlobalTheory.ModifCanon

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

variable {X Y : Scheme.{0}}

abbrev jacChart {K' : LB X} {K B : LB Y} (σ : X ⟶ Y) (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K B).pull σ) (tens K' (B.pull σ)) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK hB) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB σ)
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K B) σ (t.2.1, t.2.2)
  c t := (t.1, pIdx B σ t.2.2)
  cover x := by
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (σ x)
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ σ x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) (mem_pull.1 e.2.1) (mem_pull.1 e'.2.1), map_mul, mul_assoc]
    exact congrArg (tr K' x t.1 t'.1 * ·) (inv_mul_cancel_left _ _).symm

theorem val_restr {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp ℂ ⟶ Y) (i : B.ι)
    (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem exists_push_sections : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  intro F _ _ Y _ p d _ U M K K' B hproj hU hB
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have := M.iso
  have hXi : IsIntegral M.X := GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty F Y p U d M hU
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso F Y M.X p M.σ d K K'
  have hL : (tens K.bundle B).IsLB := isLB_tens K.isLB hB
  let C := jacChart M.σ K'.isLB K.isLB hB
  have hopn : ∀ x ∈ M.opn, Function.Bijective (M.σ.stalkMap x).hom :=
    stalkMap_bijective_of_isIso_restrict Y M.X M.σ U M.iso
  have hJU : NowhereZero (H0.restr (le_top : M.opn ≤ ⊤) J) := fun x hx a ha => by
    rw [germ_restr]; exact hJ x (hopn x hx) a ha
  have hT : M.opn ≤ M.σ ⁻¹ᵁ (⊤ : Y.Opens) := fun x _ => memTop (M.σ x)
  have ext : ∀ g : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤, ∃ s : H0 p (tens K.bundle B) ⊤,
      C.mul (H0.restr le_top J) (H0.pull M.σ hT s) = H0.restr le_top g := by
    intro g
    obtain ⟨s₀, hs₀⟩ := (M.bijective_pull hL).2 ((C.mulEquiv hJU).symm (H0.restr le_top g))
    have rel : C.mul (H0.restr le_top J) (H0.pull M.σ le_rfl s₀) = H0.restr le_top g := by
      rw [hs₀]; exact (C.mulEquiv hJU).apply_symm_apply _
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s₀)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint F Y p U d M hproj hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (M.σ x')
      have : Nonempty ((tens K.bundle B).U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U ((tens K.bundle B).U i)
      exact ⟨i, hne, hi, GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso F Y M.X p M.σ U _ _ _ C J g s₀ rel x' hb (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    have e : H0.restr (le_top : U ≤ ⊤) (H0.ofSec p ⊤ t) = s₀ := by
      rw [restr_ofSec]; exact LB.sec_ext fun i => ht i
    rw [← rel, ← e, pull_restr]
  choose Ψ hΨ using ext
  refine ⟨Ψ, fun z hz k' hk' k hk => ?_⟩
  obtain ⟨e⟩ : Nonempty (Sp ℂ) := inferInstance
  have all : ∀ (V : M.X.Opens), z e ∈ V → ⊤ ≤ z ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y e]; exact hV
  have he : z e ∈ M.opn := hz trivial
  obtain ⟨t, ha, hb, hc⟩ := C.cover (z e)
  have ha' := all _ ha
  have hb' := all _ hb
  have hc' := all _ hc
  have hb'' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U ((C.b t) PUnit.unit) := fun y _ => by
    rw [Subsingleton.elim y e]; exact mem_pull.1 hb
  have hJv := isUnit_val_of_isUnit_germ F M.X M.str _ M.opn z (C.a t) hz ha' (H0.restr le_top J) e he ha
    (hJU _ he _ ha)
  obtain ⟨T1, hT1, e2⟩ : ∃ T1 : ℂ, T1 ≠ 0 ∧ ∀ g, H0.val z k' le_top hk' g = T1 * H0.val z (C.c t) le_top hc' g :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := M.str) (O := ⊤) z k' (C.c t) le_top hk' hc' g⟩
  obtain ⟨T2, hT2, e1⟩ : ∃ T2 : ℂ, T2 ≠ 0 ∧ ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) =
      T2 * H0.val (z ≫ M.σ) ((C.b t) PUnit.unit) le_top hb'' (Ψ g) :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := p) (O := ⊤) (z ≫ M.σ) k ((C.b t) PUnit.unit) le_top hk hb'' (Ψ g)⟩
  refine ⟨Units.mk0 (T2 / (H0.val z (C.a t) hz ha' (H0.restr le_top J) * T1))
    (div_ne_zero hT2 (mul_ne_zero hJv.ne_zero hT1)), fun g => ?_⟩
  have e3 := C.val_mul (H0.restr le_top J) (H0.pull M.σ hT (Ψ g)) t z hz ha' hb' hc'
  rw [hΨ g, val_restr z _ le_top hz le_top] at e3
  have e4 := val_pull M.σ hT z (C.b t) hz hb' le_top hb'' (Ψ g)
  rw [e1, e2, e3, ← e4, Units.val_mk0]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hJv.ne_zero hT1)]
  ring

end GlobalTheory.ModifCanon
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_push_sections_canonical_modification : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  atlas_forward_decl GlobalTheory.ModifCanon.exists_push_sections
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  first | exact @GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | (intros; apply GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.NefGrowth

section SlopeTestRemainingChoices

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem isLocallyNoetherian_of_isProjOver (hp : IsProjOver (strHom k X)) :
    IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k X) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty [IsEmpty X] (L : LB X) : lbH0 k L = 0 := by
  have : Subsingleton (coh (twist (structureModule X) L) 0) := by
    refine ⟨fun x y => ?_⟩
    have h : ∀ z : coh (twist (structureModule X) L) 0, z = 0 := fun z => by
      rw [← one_smul Γ(X, ⊤) z, Subsingleton.elim (1 : Γ(X, ⊤)) 0, zero_smul]
    rw [h x, h y]
  exact hdim_eq_zero_of_subsingleton k 0

theorem lineBundleGlobalSectionsDim_le_of_injective_section_mul [IsLocallyNoetherian X] {N A B : LB X} (hN : N.IsLB)
    (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) (s : B.Sec)
    (hs : Mono (cutHom (structureModule X) hB s))
    (hfin : Module.Finite k (coh (twist (structureModule X) N) 0)) : lbH0 k A ≤ lbH0 k N := by
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e
  have := Twist.isQuasicoherent_twist (F := structureModule X) hA
  have : Mono (Twist.secHom (twist (structureModule X) A) s) := by
    rw [mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]
    exact hs
  exact LinearMap.finrank_le_finrank_of_injective
    (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))

end SlopeTestRemainingChoices

open GlobalTheory.Published

theorem lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0})
    [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F Z) → topologicalKrullDim Z ≤ d →
    ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  intro hNum F _ Z _ d hp hd L A hL hA
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, .of_forall fun m => by rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]; simp⟩
  have := isLocallyNoetherian_of_isProjOver hp
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim Z = e := by
    have h0 : topologicalKrullDim Z ≠ ⊥ := topologicalKrullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty Z)
    revert h0 hd
    generalize topologicalKrullDim Z = D
    intro hd h0
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl h0
    | coe D =>
      induction D using ENat.recTopCoe with
      | top =>
        have h' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hd
        exact absurd (top_le_iff.1 h') (ENat.coe_ne_top d)
      | coe n => exact ⟨n, rfl⟩
  have hed : e ≤ d := by
    rw [he] at hd
    exact_mod_cast hd
  have hLA : IsNef F (tens L A) := hL.tens hA.isNef hA
  have ht := hNum.2.2.tendsto hp he hLA
  set c : ℝ := (topSelfIntersection F (tens L A) e : ℝ) / e.factorial
  have hb := ht.eventually (gt_mem_nhds (lt_add_one c))
  have hcut : ∀ᶠ m : ℕ in atTop,
      ∃ t : (lbPow A (m - 1)).Sec, Mono (cutHom (structureModule Z) (isLB_lbPow hA.isLB (m - 1)) t) :=
    (tendsto_sub_atTop_nat 1).eventually (hA.eventually_exists_mono_cutHom_pow (structureModule Z))
  refine ⟨|c| + 1, ?_⟩
  filter_upwards [hcut, hb, eventually_ge_atTop 1] with m ⟨t, hts⟩ hm hm1
  have hcls : cls _ (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) =
      cls _ (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) + cls _ (isLB_lbPow hA.isLB (m - 1)) := by
    rw [cls_lbPow (isLB_tens hL.isLB hA.isLB), cls_tens hL.isLB hA.isLB,
      cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_lbPow hA.isLB]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_smul, one_smul, smul_add]
    abel
  have h1 := lineBundleGlobalSectionsDim_le_of_injective_section_mul (k := F) (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m)
    (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) (isLB_lbPow hA.isLB (m - 1)) hcls t hts
    (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom F Z) hp
      (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m))
  have hmpos : (0 : ℝ) < (m : ℝ) ^ e := by positivity
  have h2 : (lbH0 F (lbPow (tens L A) m) : ℝ) ≤ (c + 1) * (m : ℝ) ^ e :=
    ((div_lt_iff₀ hmpos).1 hm).le
  have h3 : (m : ℝ) ^ e ≤ (m : ℝ) ^ d := pow_le_pow_right₀ (by exact_mod_cast hm1) hed
  calc (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (lbPow (tens L A) m) := by exact_mod_cast h1
    _ ≤ (c + 1) * (m : ℝ) ^ e := h2
    _ ≤ (|c| + 1) * (m : ℝ) ^ e := by gcongr; exact le_abs_self c
    _ ≤ (|c| + 1) * (m : ℝ) ^ d := by gcongr

end GlobalTheory.NefGrowth
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F Z) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  atlas_forward_decl GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_resolution_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n → ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  first | exact @GlobalTheory.WeakRes.weak_resolution | exact GlobalTheory.WeakRes.weak_resolution | (intros; apply GlobalTheory.WeakRes.weak_resolution <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

namespace GlobalTheory.DenomIdeal

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (w : ι → X.functionField)

def IsDen (V : X.Opens) (a : Γ(X, V)) : Prop :=
  ∀ h : genericPoint X ∈ V, ∀ j, ∀ y ∈ V, RegAt y (fnOf V h a * w j)

def gens (V : X.Opens) : Set Γ(X, V) :=
  {b | ∃ a, IsDen w V a ∧ ∃ j, ∀ h : genericPoint X ∈ V, fnOf V h b = fnOf V h a * w j}

def idealOn (V : X.Opens) : Ideal Γ(X, V) := Ideal.span (gens w V)

variable {w}

theorem IsDen.res {U V : X.Opens} (e : V ≤ U) {a : Γ(X, U)} (ha : IsDen w U a) :
    IsDen w V (resG X e a) := by
  intro h j y hy
  rw [fnOf_resG]
  exact ha (e h) j y (e hy)

theorem res_mem_gens {U V : X.Opens} (e : V ≤ U) {b : Γ(X, U)} (hb : b ∈ gens w U) :
    resG X e b ∈ gens w V := by
  obtain ⟨a, ha, j, hj⟩ := hb
  exact ⟨resG X e a, ha.res e, j, fun h => by rw [fnOf_resG, fnOf_resG, hj]⟩

theorem mem_map_of_mem_gens_basicOpen [Fintype ι] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {b : Γ(X, X.basicOpen f)} (hb : b ∈ gens w (X.basicOpen f)) :
    b ∈ (idealOn w U).map (resG X (X.basicOpen_le f)) := by
  by_cases hg : genericPoint X ∈ X.basicOpen f
  swap
  · have : b = 0 := Cartier.fn_ext fun h => (hg h).elim
    rw [this]; exact zero_mem _
  have hU' : genericPoint X ∈ U := X.basicOpen_le f hg
  have := hU.isLocalization_basicOpen f
  obtain ⟨a', ha', j, hj⟩ := hb
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) a'
  have e' : fnOf _ hg a' * fnOf U hU' f ^ n = fnOf U hU' a := by
    have := congrArg (fnOf _ hg) e
    simp only [map_mul, map_pow] at this
    change fnOf _ hg a' * fnOf _ hg (resG X (X.basicOpen_le f) f) ^ n =
      fnOf _ hg (resG X (X.basicOpen_le f) a) at this
    rwa [fnOf_resG, fnOf_resG] at this
  have hreg : ∀ i, ∀ x ∈ X.basicOpen f, RegAt x (fnOf U hU' a * w i) := fun i x hx => by
    rw [← e', mul_right_comm]
    exact (ha' hg i x hx).mul (GlobalTheory.TrueGeo.SmallSec.regAt_pow (regAt_fnOf (X.basicOpen_le f hx) hU' f) n)
  have := fun i => GlobalTheory.InvertIdeal.exists_mul_pow hU hU' f hg (hreg i)
  choose m γ hγ using this
  set M := ∑ i, m i
  have hm : ∀ i, m i ≤ M := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have key : ∀ i, fnOf U hU' (γ i * f ^ (M - m i)) = fnOf U hU' (a * f ^ M) * w i := fun i => by
    rw [map_mul, map_mul, hγ, map_pow, map_pow, ← Nat.add_sub_cancel' (hm i), pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hden : IsDen w U (a * f ^ M) := fun h i y hy => by
    rw [← key i]; exact regAt_fnOf hy _ _
  have hgen : γ j * f ^ (M - m j) ∈ gens w U := ⟨_, hden, j, fun h => key j⟩
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := IsLocalization.Away.algebraMap_isUnit f
  have hb0 : resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) = b * resG X (X.basicOpen_le f) f ^ (n + M) :=
    Cartier.fn_ext fun h => by
      rw [fnOf_resG, key, map_mul (fnOf _ h), map_pow, fnOf_resG, hj, map_mul, map_pow, ← e']
      ring
  have hb : b = resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) * ((hu.unit⁻¹ : _) : Γ(X, X.basicOpen f)) ^ (n + M) := by
    rw [hb0, mul_assoc, ← mul_pow, hu.mul_val_inv, one_pow, mul_one]
  rw [hb]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hgen))

variable (w) in

def idealSheaf [Fintype ι] : X.IdealSheafData where
  ideal U := idealOn w U.1
  map_ideal_basicOpen U f := by
    show Ideal.map (resG X (X.basicOpen_le f)) (idealOn w U.1) = idealOn w (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun b hb => ?_
      exact Ideal.subset_span (res_mem_gens (X.basicOpen_le f) hb)
    · exact Ideal.span_le.2 fun b hb => mem_map_of_mem_gens_basicOpen U.2 f hb


theorem idealSheaf_ne_bot [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) : idealSheaf w ≠ ⊥ := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hW' : IsAffineOpen W := hW
  choose β γ hβ hγ using fun j => GlobalTheory.InvertIdeal.exists_denom hW' hηW hηW (regAt_genericPoint (w j))
  have hβ0 : ∀ j, fnOf W hηW (β j) ≠ 0 := fun j => ((unitAt_fnOf_iff hηW hηW (β j)).2 (hβ j)).ne_zero
  set d := ∏ j, β j
  have hd : ∀ j, fnOf W hηW d * w j = fnOf W hηW (γ j) * fnOf W hηW (∏ i ∈ Finset.univ.erase j, β i) := fun j => by
    rw [hγ, show d = β j * ∏ i ∈ Finset.univ.erase j, β i from (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm,
      map_mul]
    ring
  have hden : IsDen w W d := fun h j y hy => by
    rw [hd j]; exact (regAt_fnOf hy _ _).mul (regAt_fnOf hy _ _)
  have hgen : d ∈ gens w W := ⟨d, hden, i₀, fun h => by rw [h1, mul_one]⟩
  have hd0 : fnOf W hηW d ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hβ0 j
  intro hbot
  have hmem : d ∈ (idealSheaf w).ideal ⟨W, hW⟩ := Ideal.subset_span hgen
  rw [hbot] at hmem
  exact hd0 (by rw [(Ideal.mem_bot).1 hmem, map_zero])

theorem notMem_support [Finite ι] [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) {y : X} {k : ι} (hk : w k ≠ 0)
    (hy : ∀ j, RegAt y (w j / w k)) : y ∉ (idealSheaf w).support := by
  obtain ⟨V, hyV, ha⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
  choose a ha using ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have e : W ≤ V := hWV
  have hηW : genericPoint X ∈ W := gen_mem hyW
  have hfa : ∀ j, fnOf W hηW (resG X e (a j)) = w j / w k := fun j => by rw [fnOf_resG, ha]
  have hden : IsDen w W (resG X e (a i₀)) := fun h j x hx => by
    rw [hfa, h1, one_div, inv_mul_eq_div, ← hfa j]; exact regAt_fnOf hx _ _
  have hgen : (1 : Γ(X, W)) ∈ gens w W :=
    ⟨_, hden, k, fun h => by rw [map_one, hfa, h1, one_div, inv_mul_cancel₀ hk]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW, Scheme.mem_zeroLocus_iff]
  intro H
  exact H 1 (Ideal.subset_span hgen) (by rw [Scheme.basicOpen_one]; exact hyW)

theorem fnOf_appLE {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X) {W : X.Opens} {A : Y'.Opens} (hA : A ≤ s ⁻¹ᵁ W)
    (hA' : genericPoint Y' ∈ A) (hW : genericPoint X ∈ W) (c : Γ(X, W)) :
    fnOf A hA' ((s.appLE W A hA).hom c) = GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hW c) := by
  rw [GlobalTheory.TrueGeo.SmallSec.fnMap_fnOf s hη hW (hA hA'), ← fnOf_resG hA hA']
  rfl

theorem exists_dvd_of_effCartier [Fintype ι] {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X)
    (hE : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((idealSheaf w).comap s)) (y' : Y') :
    ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k) ≠ 0 ∧ ∀ j,
      RegAt y' (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k)) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s y')) isOpen_univ
  obtain ⟨U0, f0, sectionFrameQuotient, hf0, hI0⟩ := hE y'
  obtain ⟨t, htle, hyt⟩ := U0.2.exists_basicOpen_le (V := U0.1 ⊓ s ⁻¹ᵁ W) ⟨y', sectionFrameQuotient, hyW⟩ sectionFrameQuotient
  have hAW : Y'.basicOpen t ≤ s ⁻¹ᵁ W := fun x hx => (htle hx).2
  have hA' : genericPoint Y' ∈ Y'.basicOpen t := gen_mem hyt
  have hηW : genericPoint X ∈ W := gen_mem hyW
  set F := resG Y' (Y'.basicOpen_le t) f0 with hFdef
  have hIA : ((idealSheaf w).comap s).ideal (Y'.affineBasicOpen t) = Ideal.span {F} := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI0, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W) = Ideal.span {F} := by
    rw [← hIA, GlobalTheory.Principalise.comapIdealAffine _ s ⟨W, hW⟩ (Y'.affineBasicOpen t) hAW]
    rfl
  set φ := fnOf (Y'.basicOpen t) hA'
  set w' := fun j => GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) with hw'
  have hφ : ∀ c : Γ(X, W), φ ((s.appLE W (Y'.basicOpen t) hAW).hom c) =
      GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW c) := fun c => fnOf_appLE s hη hAW hA' hηW c
  have hF0 : φ F ≠ 0 := by
    have hU0 : genericPoint Y' ∈ U0.1 := Y'.basicOpen_le t hA'
    have : Nontrivial Γ(Y', U0.1) := (fnOf U0.1 hU0).domain_nontrivial
    rw [hFdef, fnOf_resG]
    intro h
    exact nonZeroDivisors.ne_zero hf0 (fnOf_injective _ hU0 (h.trans (map_zero _).symm))
  have key : ∀ x ∈ Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W),
      ∃ C : ι → Y'.functionField, φ x = ∑ j, w' j * C j ∧ ∀ i j, ∃ r : Γ(Y', Y'.basicOpen t),
        w' i * C j = φ F * φ r := by
    intro x hx
    rw [idealOn, Ideal.map_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, ⟨a, ha, j₀, hb⟩, rfl⟩ := hx
      refine ⟨Pi.single j₀ (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW a)), ?_, fun i j => ?_⟩
      · rw [hφ, hb hηW, map_mul, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (by simp), Pi.single_eq_same, mul_comm]
      · by_cases hj : j = j₀
        · subst hj
          rw [Pi.single_eq_same]
          obtain ⟨bi, hbi⟩ := exists_fnOf_eq hηW fun y hy => ha hηW i y hy
          have hmem : (s.appLE W (Y'.basicOpen t) hAW).hom bi ∈ Ideal.span {F} :=
            hmap ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, i, fun _ => hbi⟩)
          obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
          refine ⟨r, ?_⟩
          rw [hw', ← map_mul, mul_comm (w i), ← hbi, ← hφ, ← hr, map_mul, mul_comm]
        · rw [Pi.single_eq_of_ne hj, mul_zero]
          exact ⟨0, by rw [map_zero, mul_zero]⟩
    | zero => exact ⟨0, by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨C, hC, hC'⟩ := hx
      obtain ⟨D, hD, hD'⟩ := hy
      refine ⟨C + D, by rw [map_add, hC, hD, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add],
        fun i j => ?_⟩
      obtain ⟨r, hr⟩ := hC' i j
      obtain ⟨r', hr'⟩ := hD' i j
      exact ⟨r + r', by simp only [Pi.add_apply, mul_add, hr, hr', map_add]⟩
    | smul c x _ hx =>
      obtain ⟨C, hC, hC'⟩ := hx
      refine ⟨fun j => φ c * C j, ?_, fun i j => ?_⟩
      · rw [smul_eq_mul, map_mul, hC, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · obtain ⟨r, hr⟩ := hC' i j
        refine ⟨c * r, ?_⟩
        rw [map_mul, mul_left_comm, hr]
        ring
  obtain ⟨C, hC, hC'⟩ := key F (hmap ▸ Ideal.mem_span_singleton_self F)
  choose r hr using hC'
  have hreg : ∀ i j, RegAt y' (w' i * (C j / φ F)) := fun i j => by
    rw [mul_div_assoc', hr, mul_div_cancel_left₀ _ hF0]
    exact regAt_fnOf hyt _ _
  have he1 : ∑ j, (fun _ => (1 : Y'.functionField)) j * (w' j * (C j / φ F)) = 1 := by
    simp only [one_mul, mul_div_assoc']
    rw [← Finset.sum_div, ← hC, div_self hF0]
  obtain ⟨k, hk⟩ := GlobalTheory.InvertIdeal.exists_unitAt (x := y') (c := fun _ => 1)
    (g := fun j => w' j * (C j / φ F)) (fun _ => ⟨1, map_one _⟩) (fun j => hreg j j) he1
  have hk0 : w' k * (C k / φ F) ≠ 0 := hk.ne_zero
  refine ⟨k, left_ne_zero_of_mul hk0, fun j => ?_⟩
  have e : w' j / w' k = (w' j * (C k / φ F)) * (w' k * (C k / φ F))⁻¹ := by
    have h2 : C k / φ F ≠ 0 := right_ne_zero_of_mul hk0
    rw [← div_eq_mul_inv, mul_div_mul_right _ _ h2]
  change RegAt y' (w' j / w' k)
  rw [e]
  exact (hreg j k).mul hk.inv.regAt

theorem exists_idealSheaf : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  intro Y _ N w i₀ U h1 hU
  refine ⟨idealSheaf w, idealSheaf_ne_bot i₀ h1, fun y hy => ?_, fun Y' _ s hη hE y' =>
    exists_dvd_of_effCartier s (specializes_of_eq hη) hE y'⟩
  obtain ⟨k, hk, hreg⟩ := hU y hy
  exact notMem_support i₀ h1 hk hreg

end GlobalTheory.DenomIdeal
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  atlas_forward_decl GlobalTheory.DenomIdeal.exists_idealSheaf
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  first | exact @GlobalTheory.ProjSpace.exists_ratCoords_extend | exact GlobalTheory.ProjSpace.exists_ratCoords_extend | (intros; apply GlobalTheory.ProjSpace.exists_ratCoords_extend <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modification_extending_map_from_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  atlas_forward_decl GlobalTheory.CompHS.exists_modif_map_of_open
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme : ∀ (F : Type) [Field F] (X V : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ] [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by
  first | exact @GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | exact GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion | (intros; apply GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

set_option autoImplicit false

namespace GlobalTheory.ModifGeomConn

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  infer_instance

theorem geometricallyConnected_modif : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  intro F _ X _ sX n _ U M _ _ hU
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : GeometricallyIntegral sX := GlobalTheory.geometricallyIntegral_of_smooth sX
  obtain ⟨x, hx⟩ := hU
  have : Surjective (U.ι ≫ sX) := ⟨fun s => ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩⟩
  have h2 : GeometricallyConnected (U.ι ≫ sX) := geometricallyConnected_of_geometricallyIrreducible _
  have := M.iso
  have h3 : GeometricallyConnected (M.opn.ι ≫ M.str) := by
    have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ sX) := by
      rw [Modif.str, ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    rw [e]
    rw [GeometricallyConnected.eq_geometrically] at h2 ⊢
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h2
  exact GlobalTheory.CompactVar.geometricallyConnected_of_denseRange M.opn.ι M.str
    (by rw [Scheme.Opens.range_ι]; exact M.dense)

end GlobalTheory.ModifGeomConn
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  atlas_forward_decl GlobalTheory.ModifGeomConn.geometricallyConnected_modif
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuotSetup

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i
    have hdV' := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QuotSep

open Filter

open GlobalTheory.ThickeningDetermines (secIdeal)

theorem isProjOver_along {k : Type} [Field k] {X Z : Scheme.{0}} [Algebra k Γ(X, ⊤)] (hp : IsProjOver (strHom k X))
    (i : Z ⟶ X) [IsClosedImmersion i] : letI := algebraΓAlong k i; IsProjOver (strHom k Z) := by
  letI := algebraΓAlong k i
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom (appTop_algebraMap_along k i)]⟩

section Cut

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem dim_zeroScheme_le [IsIntegral X] [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) {t : L.Sec} (ht : t ≠ 0) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) : topologicalKrullDim (secIdeal hL t).subscheme ≤ d := by
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  refine le_of_eq_of_le ?_ (suppDim_cut_le (structureModule _) hL t (d := d) (by rwa [QCoh.suppDim_structureModule]))
  rw [QCoh.suppDim, support_cut_eq_inter, QCoh.support_structureModule, Set.univ_inter]
  exact (topologicalKrullDim_eq_of_isEmbedding (secIdeal hL t).subschemeι.isClosedEmbedding.isEmbedding
    (secIdeal hL t).range_subschemeι).symm

theorem globalSections_dim_le_div_add_restriction [IsIntegral X] (hp : IsProjOver (strHom k X)) {L B : LB X} (hL : L.IsLB) (hB : B.IsLB) {t : L.Sec}
    (ht : t ≠ 0) : letI := algebraΓAlong k (secIdeal hL t).subschemeι
    lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 k (B.pull (secIdeal hL t).subschemeι) := by
  letI := algebraΓAlong k (secIdeal hL t).subschemeι
  have := isNoetherian_of_isProjOver hp
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp
  have h := hdim₂_le k (Twist.shortExact_map hB (shortExact_cutComplex (structureModule X) hL t)) 0
    ((hF.twist (Twist.isLB_lbZPow hL (-1)) _ hB).finite 0) ((hF.cut hL t _ hB).finite 0)
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) (Twist.isLB_lbZPow hL (-1)) hB
    (LB.isLB_div hB hL) (by rw [cls_div hB hL, cls_lbZPow hL]; abel)
  obtain ⟨e₂, -⟩ := exists_cut_structureModule_iso hL t
  have := Twist.isQuasicoherent_twist (F := structureModule _) (LB.isLB_pull hB (secIdeal hL t).subschemeι)
  refine h.trans_eq (congrArg₂ (· + ·) (hdim_congr k 0 e₁) ((hdim_congr k 0 ((twistFunctor B).mapIso e₂)).trans
    ((hdim_congr k 0 (Twist.projIso B _ _)).symm.trans ?_)))
  exact hdim_pushforward k (appTop_algebraMap_along k _) _ 0

end Cut

theorem nef_pull (hN : GlobalTheory.Published.NefNumerics) {F E : Type} [Field F] [Field E] {X Y : Scheme.{0}} (pX : X ⟶ Sp F)
    (pY : Y ⟶ Sp E) (g : Y ⟶ X) (hX : IsProjOver pX) (hY : IsProjOver pY) (L : LB X)
    (hL : letI := algebraΓOfHom pX; IsNef F L) : letI := algebraΓOfHom pY; IsNef E (L.pull g) := by
  letI := algebraΓOfHom pX
  letI := algebraΓOfHom pY
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB pX).1 hX
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hY
  have : IsProper (strHom F X) := by rw [strHom_eq (f := pX) fun _ => rfl]; exact hpp
  exact NefFieldExt.isNef_pull hN hL hA hB g

theorem big_pull_modif {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) (hU : (U : Set X).Nonempty) [IsIntegral M.X]
    (δ : LB X) (h : letI := algebraΓOfHom sX; IsBig F δ) : letI := algebraΓOfHom M.str; IsBig F (δ.pull M.σ) := by
  refine BigPull.isBig_pull F X M.X sX M.σ M.proj ?_ ?_ δ h
  · rw [HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance,
      HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth M.str n inferInstance]
  · have := M.iso
    refine (U.isOpen.dense hU).mono fun x hx => ?_
    obtain ⟨y, hy⟩ := (M.σ ∣_ U).surjective ⟨x, hx⟩
    exact ⟨y.1, (morphismRestrict_base_coe M.σ U y).symm.trans (congrArg Subtype.val hy)⟩

theorem ampleAt_generic (hN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    [Algebra F Γ(Y, ⊤)] (hp : IsProjOver (strHom F Y)) {n : ℕ} (hd : topologicalKrullDim Y = (n + 1 : ℕ))
    {L A : LB Y} (hL : IsNef F L) (hA : IsAmpleLB A) {c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ (n + 1) ≤ lbH0 F (tens (lbPow L m) A)) : AmpleAt L (genericPoint Y) := by
  have := isNoetherian_of_isProjOver hp
  obtain ⟨q, hq, hg⟩ := hA.exists_isGenerated_pow
  have hP : (lbPow (lbPow A q) 2).IsLB := isLB_lbPow hg.isLB 2
  obtain ⟨t, ht⟩ : HasNonzeroSec (lbPow (lbPow A q) 2) := hg.hasNonzeroSec.pow hg.isLB 2
  let ι := (secIdeal hP t).subschemeι
  letI := algebraΓAlong F ι
  obtain ⟨C, hC⟩ := GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim hN F _ n (isProjOver_along hp ι) (dim_zeroScheme_le hP ht hd.le)
    (L.pull ι) (A.pull ι) (hL.pull_of_isClosedImmersion ι (appTop_algebraMap_along F ι))
    (hA.pull_of_isClosedImmersion ι)
  have hlt : ∀ᶠ m : ℕ in atTop, C < c * (m : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop C
  obtain ⟨m, h₁, h₂, h₃, h₄⟩ := (h.and_eventually (hC.and (hlt.and (eventually_ge_atTop 1)))).exists
  have hB : (tens (lbPow L m) A).IsLB := isLB_tens (isLB_lbPow hL.isLB m) hA.isLB
  have e₁ := globalSections_dim_le_div_add_restriction hp hP hB ht
  have hLι := LB.isLB_pull hL.isLB ι
  have hAι := LB.isLB_pull hA.isLB ι
  have e₂ : lbH0 F ((tens (lbPow L m) A).pull ι) = lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι)) :=
    lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull hB ι) (isLB_tens (isLB_lbPow hLι m) hAι) (by
      rw [cls_pull hB, cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB,
        cls_tens (isLB_lbPow hLι m) hAι, cls_lbPow hLι, cls_pull hL.isLB, cls_pull hA.isLB, map_add, map_nsmul])
  have hm : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have hpos : 0 < lbH0 F (LB.div (tens (lbPow L m) A) (lbPow (lbPow A q) 2)) := by
    by_contra h0
    rw [Nat.pos_iff_ne_zero, not_not] at h0
    rw [h0, zero_add] at e₁
    have e₃ : (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (tens (lbPow (L.pull ι) m) (A.pull ι)) := by
      rw [← e₂]; exact_mod_cast e₁
    have := mul_lt_mul_of_pos_right h₃ hm
    rw [pow_succ] at h₁
    nlinarith
  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq
  have hA' : IsAmpleLB (lbPow A (2 * q' + 1)) := (isAmpleLB_pow_iff hA.isLB (by omega)).2 hA
  have hD := Semi.LB.isLB_div (isLB_lbPow hL.isLB m) hA'.isLB
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 ((lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).of_cls_eq hD (Semi.LB.isLB_div hB hP) (by
    rw [cls_div (isLB_lbPow hL.isLB m) hA'.isLB, cls_div hB hP, cls_tens (isLB_lbPow hL.isLB m) hA.isLB,
      cls_lbPow hg.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]
    module))
  exact ⟨m, _, s, h₄, hA'.isLB, hA', hs⟩

theorem ampleAt_of_isBig_pull (hN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] {M W : Scheme.{0}} [IsIntegral M]
    [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) {n : ℕ} (hn : 1 ≤ n) (hdW : topologicalKrullDim W = n)
    (hdM : topologicalKrullDim M = n) (hp : IsProjOver p) (hq : IsProjOver (f ≫ p)) (hf : Surjective f)
    (hr : f.residueDegree (genericPoint M) ≠ 0) {L : LB W} (hL : letI := algebraΓOfHom p; IsNef F L)
    (hb : letI := algebraΓOfHom (f ≫ p); IsBig F (L.pull f)) : AmpleAt L (genericPoint W) := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨r, A, hA, hle⟩ := GlobalTheory.T.exists_ample_sections_pullback_bound_of_genFinite F M W p f hp hq hf hr
  obtain ⟨-, c, hc, hm⟩ := (isBig_iff (fun _ => rfl) hq hdM).1 hb
  refine ampleAt_generic hN (by rwa [strHom_eq (f := p) fun _ => rfl]) hdW hL hA (c := c / (r + 1))
    (by positivity) (hm.mono fun m hm => ?_)
  have hB := isLB_lbPow hL.isLB m
  have hL' := isLB_lbPow (LB.isLB_pull hL.isLB f) m
  rw [lineBundleGlobalSectionsDim_congr_picardClass hL' (LB.isLB_pull hB f) ((cls_eq_iff hL' (LB.isLB_pull hB f)).2 (lbIso_lbPow_pull hL.isLB f m))] at hm
  have h₁ : (lbH0 F ((lbPow L m).pull f) : ℝ) ≤ r * lbH0 F (tens (lbPow L m) A) := by exact_mod_cast hle _ hB
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ lbH0 F (tens (lbPow L m) A) := by positivity
  nlinarith

theorem exists_etale_restrict {F : Type} [Field F] [CharZero F] {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) [LocallyOfFiniteType p] (f : M ⟶ W) [IsProper f] [Surjective f]
    (hr : f.residueDegree (genericPoint M) ≠ 0) : ∃ U : W.Opens, genericPoint W ∈ U ∧ Etale (f ∣_ U) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian p
  letI := algebraΓOfHom p
  have : CharZero Γ(W, ⊤) := charZero_of_injective_algebraMap (algebraMap F Γ(W, ⊤)).injective
  have hη : f (genericPoint M) = genericPoint W := by
    have h := (genericPoint_spec M).image f.continuous
    rw [Set.image_univ, f.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec W)
  obtain ⟨U, -, hU, hη', hU', -, hE, -⟩ :=
    GenFiniteEtale.exists_finite_etale_of_isProper f hη hr ⊤ trivial
  refine ⟨U, hη', ?_⟩
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU'
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have key : ∀ V : W.Opens, V = U → (f.app V).hom.Etale := fun V e => e ▸ hE
  exact (RingHom.Etale.respectsIso.cancel_right_isIso _ _).2 (key _ U.ι_image_top)

section Descent

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem sum_val_pull_eq_zero {F : Type} [Field F] [Algebra F ℂ] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (n : ℕ)
    [SmoothOfRelativeDimension n p] (hp : IsProjOver p) (hc : GeometricallyConnected p) (hn : 1 ≤ n) {T : LB Y}
    (hT : T.IsLB) {J : Type} [Fintype J] (x : J → (Sp ℂ ⟶ pullback p (spMap (algebraMap F ℂ))))
    (hx : ∀ j, x j ≫ pullback.snd _ _ = 𝟙 _) (k : J → T.ι)
    (hk : ∀ j, ⊤ ≤ (x j ≫ pullback.fst _ _) ⁻¹ᵁ T.U (k j))
    (hk' : ∀ j, ⊤ ≤ x j ⁻¹ᵁ (T.pull (pullback.fst _ _)).U (pIdx T _ (k j))) (a : J → ℂ)
    (h : ∀ g : H0 p T ⊤, ∑ j, a j * val (x j ≫ pullback.fst _ _) (k j) le_top (hk j) g = 0)
    (g : H0 (pullback.snd p (spMap (algebraMap F ℂ))) (T.pull (pullback.fst _ _)) ⊤) :
    ∑ j, a j * val (x j) (pIdx T _ (k j)) le_top (hk' j) g = 0 := by
  let Z : Scheme.{0} := pullback p (spMap (algebraMap F ℂ))
  let π : Z ⟶ Y := pullback.fst p (spMap (algebraMap F ℂ))
  let q : Z ⟶ Sp ℂ := pullback.snd p (spMap (algebraMap F ℂ))
  let S : LinSys F := ⟨Y, p, n, T, hT, 0, Fin.elim0⟩
  letI := algebraΓOfHom q
  obtain ⟨N, b, hb⟩ : ∃ (N : ℕ) (b : Fin N → T.Sec), ∀ t : (T.pull π).Sec, ∃ u : Fin N → ℂ,
      ∑ i, algebraMap ℂ Γ(Z, ⊤) (u i) • secPull (b i) π = t :=
    SectionsFieldChange.exists_pullSecs_spanning F ℂ S ⟨inferInstance, hp, hc, hn⟩
  obtain ⟨t, rfl⟩ := (bijective_ofSec_top (p := q) (B := T.pull π)).2 g
  obtain ⟨u, hu⟩ := hb t
  have e (c : ℂ) : algebraMap ℂ Γ(Z, ⊤) c = algX q ⊤ c := by
    change q.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have ht : t = ∑ i, algX q ⊤ (u i) • secPull (b i) π := by
    rw [← hu]
    exact Finset.sum_congr rfl fun i _ => by rw [e]
  have hx' : ∀ j, x j ≫ q = spMap (RingHom.id ℂ) := fun j =>
    (hx j).trans (Spec.map_id (CommRingCat.of ℂ)).symm
  have hv : ∀ j i, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ (secPull (b i) π)) =
      val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j i => by
    refine (val_ofSec (p := q) (O := ⊤) (x j) _ le_top (hk' j) _).trans
      (Eq.trans ?_ (val_ofSec (p := p) (O := ⊤) (x j ≫ π) _ le_top (hk j) _).symm)
    exact congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom ((b i).f (k j)))
      (Scheme.Hom.appLE_comp_appLE (x j) π (T.U (k j)) _ ⊤ ((chartPullPull T π).le (pIdx T π (k j))) (hk' j))
  have hs : ∀ j, val (x j) (pIdx T π (k j)) le_top (hk' j) (ofSec q ⊤ t) =
      ∑ i, u i * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i)) := fun j => by
    rw [ht, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofSec_smul]
    exact (H0.val_smul (O := ⊤) (x j) (hx' j) _ le_top (hk' j) _ _).trans (congrArg (u i * ·) (hv j i))
  calc _ = ∑ j, ∑ i, u i * (a j * val (x j ≫ π) (k j) le_top (hk j) (ofSec p ⊤ (b i))) :=
        Finset.sum_congr rfl fun j _ => by
          rw [hs j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_eq_zero fun i _ => by rw [← Finset.mul_sum, h, mul_zero]

abbrev tensPullChart {X Y : Scheme.{0}} {K B : LB Y} (π : X ⟶ Y) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.triv X) (tens (K.pull π) (B.pull π)) ((tens K B).pull π) where
  isLB₁ := LB.isLB_triv X
  isLB₂ := isLB_tens (LB.isLB_pull hK π) (LB.isLB_pull hB π)
  isLB₃ := LB.isLB_pull (isLB_tens hK hB) π
  τ := K.ι × B.ι
  a _ := PUnit.unit
  b t := (pIdx K π t.1, pIdx B π t.2)
  c t := pIdx (tens K B) π t
  cover x := by
    obtain ⟨j, hj⟩ := exists_chart hK (π x)
    obtain ⟨l, hl⟩ := exists_chart hB (π x)
    exact ⟨(j, l), trivial, ⟨mem_pIdx.2 hj, mem_pIdx.2 hl⟩, mem_pIdx.2 ⟨hj, hl⟩⟩
  rule x t t' e e' := by
    have h1 : tr (LB.triv X) x PUnit.unit PUnit.unit = 1 := map_one _
    rw [h1, one_mul, tr_tens _ _ x e.2.1 e'.2.1, tr_pull _ π x e.2.2 e'.2.2, tr_pull _ π x e.2.1.1 e'.2.1.1,
      tr_pull _ π x e.2.1.2 e'.2.1.2, tr_tens _ _ (π x) (mem_pull.1 e.2.2) (mem_pull.1 e'.2.2), map_mul]
    rfl

theorem exists_val_eq_tens_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} (q : X ⟶ Sp k) {K B : LB Y} (π : X ⟶ Y)
    (hK : K.IsLB) (hB : B.IsLB) (g : H0 q (tens (K.pull π) (B.pull π)) ⊤) :
    ∃ g' : H0 q ((tens K B).pull π) ⊤, ∀ (x : Sp ℂ ⟶ X) (t : (tens K B).ι)
      (h : ⊤ ≤ x ⁻¹ᵁ (tens (K.pull π) (B.pull π)).U (pIdx K π t.1, pIdx B π t.2))
      (h' : ⊤ ≤ x ⁻¹ᵁ ((tens K B).pull π).U (pIdx (tens K B) π t)),
      val x (pIdx (tens K B) π t) le_top h' g' = val x (pIdx K π t.1, pIdx B π t.2) le_top h g := by
  let one : (LB.triv X).Sec := ⟨fun _ => 1, fun _ _ => by simp⟩
  refine ⟨(tensPullChart π hK hB).mul (ofSec q ⊤ one) g, fun x t h h' => ?_⟩
  have e := (tensPullChart π hK hB).val_mul (ofSec q ⊤ one) g t x le_top le_top h h'
  have e₁ : val x PUnit.unit le_top le_top (ofSec q ⊤ one) = 1 :=
    (val_ofSec (p := q) (O := ⊤) x _ le_top le_top one).trans (map_one _)
  exact e.trans ((congrArg (· * _) e₁).trans (one_mul _))

end Descent

theorem etale_restrict_of_isPullback {M W M' W' : Scheme.{0}} {a : M' ⟶ M} {f' : M' ⟶ W'} {f : M ⟶ W} {b : W' ⟶ W}
    (H : IsPullback a f' f b) (U : W.Opens) (hU : Etale (f ∣_ U)) : Etale (f' ∣_ (b ⁻¹ᵁ U)) := by
  have H₁ := (isPullback_morphismRestrict f' (b ⁻¹ᵁ U)).flip.paste_horiz H
  have H₂ := (isPullback_morphismRestrict f U).flip
  rw [← morphismRestrict_ι b U] at H₁
  have H₃ := IsPullback.of_right (h₁₁ := H₂.lift _ _ (H₁.w.trans (Category.assoc _ _ _).symm))
    (by rwa [H₂.lift_fst]) (H₂.lift_snd _ _ _) H₂
  exact MorphismProperty.of_isPullback (P := @Etale) H₃ hU

theorem separate_numberField (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (F : Type) [Field F] (σ : F →+* ℂ) (M W : Scheme.{0}) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n (f ≫ p)] [SmoothOfRelativeDimension n p] (hMp : IsProjOver (f ≫ p))
    (hWp : IsProjOver p) (hMc : GeometricallyConnected (f ≫ p)) (hWc : GeometricallyConnected p) [Surjective f]
    (hn : 1 ≤ n) (U : W.Opens) (hU : Etale (f ∣_ U)) (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M)
    (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (hNn : letI := algebraΓOfHom p; IsNef F N)
    (hN'n : letI := algebraΓOfHom (f ≫ p); IsNef F N') (hm : (n + 1).choose 2 < m)
    (hBc : cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN') (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M))
    (hz : Function.Injective z) (hzp : ∀ j, z j ≫ f ≫ p = spMap σ) (hzf : ∀ j j', z j ≫ f = z j' ≫ f)
    (hzU : ∀ j s, (z j ≫ f) s ∈ U ∧ AmpleAt N ((z j ≫ f) s)) (k : J → (tens K.bundle B).ι)
    (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ)
    (h : ∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) : a = 0 := by
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩
  · exact Subsingleton.elim _ _
  letI : Algebra F ℂ := σ.toAlgebra
  let πW := pullback.fst p (spMap (algebraMap F ℂ))
  let pC := pullback.snd p (spMap (algebraMap F ℂ))
  let πM := pullback.fst (f ≫ p) (spMap (algebraMap F ℂ))
  let qM := pullback.snd (f ≫ p) (spMap (algebraMap F ℂ))
  have HW : IsPullback πW pC p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  have HM : IsPullback πM qM (f ≫ p) (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  let fC := HW.lift (πM ≫ f) qM (by rw [Category.assoc, HM.w])
  have hf₁ : fC ≫ πW = πM ≫ f := HW.lift_fst _ _ _
  have hf₂ : fC ≫ pC = qM := HW.lift_snd _ _ _
  have HM' : IsPullback πM (fC ≫ pC) (f ≫ p) (spMap (algebraMap F ℂ)) := hf₂.symm ▸ HM
  have Hf : IsPullback πM fC f πW := IsPullback.of_bot HM' hf₁.symm HW
  obtain ⟨hWi, -, hWs, hWq, -⟩ := BaseChangeVariety.baseChange_props F ℂ W _ p pC πW n HW hWp hWc
  obtain ⟨hMi, -, hMs, hMq, -⟩ := BaseChangeVariety.baseChange_props F ℂ M _ (f ≫ p) (fC ≫ pC) πM n HM' hMp hMc
  haveI := hWi; haveI := hMi; haveI := hWs; haveI := hMs
  haveI : Surjective fC := MorphismProperty.of_isPullback (P := @Surjective) Hf inferInstance
  haveI : IsAffineHom πW := MorphismProperty.of_isPullback (P := @IsAffineHom) HW.flip inferInstance
  let zC : J → (Sp ℂ ⟶ pullback (f ≫ p) (spMap (algebraMap F ℂ))) := fun j =>
    HM.lift (z j) (𝟙 _) (by rw [hzp j, Category.id_comp])
  have hz₁ : ∀ j, zC j ≫ πM = z j := fun j => HM.lift_fst _ _ _
  have hz₂ : ∀ j, zC j ≫ qM = 𝟙 _ := fun j => HM.lift_snd _ _ _
  let x := zC j₀ ≫ fC
  have hxW : ∀ j, (zC j ≫ fC) ≫ πW = z j ≫ f := fun j => by
    rw [Category.assoc, hf₁, ← Category.assoc, hz₁]
  have hxp : ∀ j, (zC j ≫ fC) ≫ pC = 𝟙 _ := fun j => by rw [Category.assoc, hf₂, hz₂]
  have hzx : ∀ j, zC j ≫ fC = x := fun j =>
    HW.hom_ext (by rw [hxW, hxW, hzf j j₀]) (by rw [hxp, hxp])
  have hπx : ∀ s, πW (x s) = (z j₀ ≫ f) s := fun s => congrArg (fun g => g s) (hxW j₀)
  obtain ⟨s₀⟩ : Nonempty (Sp ℂ) := inferInstance
  letI := algebraΓOfHom pC
  letI := algebraΓOfHom (fC ≫ pC)
  have hNC := LB.isLB_pull hN πW
  have hAx : AmpleAt (N.pull πW) (x s₀) :=
    AmplePull.ampleAt_pull W _ πW N hN (x s₀) (by rw [hπx]; exact (hzU j₀ s₀).2)
  have hNnC : IsNef ℂ (N.pull πW) := nef_pull hNN p pC πW hWp hWq N hNn
  have hc : 1 • cls (N.pull πW) hNC = cls (N.pull πW) hNC + cls (LB.triv _) (LB.isLB_triv _) := by
    rw [one_smul, cls_triv, add_zero]
  have hbig : IsBig ℂ (N.pull πW) :=
    isBig_of_smul_cls_eq_add_ampleAt hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx
      (isNef_triv ℂ _)
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ pC hWq _ _ _ hNC hNC (LB.isLB_triv _) 1 (x s₀) hNnC one_pos hc hAx
    (isNef_triv ℂ _)
  have hbig' : IsBig ℂ ((N.pull πW).pull fC) := BigPull.isBig_pull ℂ _ _ pC fC hMq
    (by rw [HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth pC n hWs,
      HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (fC ≫ pC) n hMs])
    fC.surjective.denseRange _ hbig
  have hUC : Etale (fC ∣_ (πW ⁻¹ᵁ U)) := etale_restrict_of_isPullback Hf U hU
  have hcB : cls (B.pull πM) (LB.isLB_pull hB πM) =
      m • CechPic.pull fC (cls (N.pull πW) hNC) + cls (N'.pull πM) (LB.isLB_pull hN' πM) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul, ← pull_comp, ← pull_comp, hf₁]
  have hpt : ∀ (Y : Scheme.{0}) (y : Sp ℂ ⟶ Y) (O : Y.Opens), y s₀ ∈ O → ⊤ ≤ y ⁻¹ᵁ O := by
    intro Y y O hs t _
    rw [Subsingleton.elim t s₀]
    exact hs
  have hkM : ∀ j, ⊤ ≤ (zC j ≫ πM) ⁻¹ᵁ (tens K.bundle B).U (k j) := fun j => by rw [hz₁]; exact hk j
  have hk₁ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ (tens (K.bundle.pull πM) (B.pull πM)).U (pIdx _ πM (k j).1, pIdx B πM (k j).2) :=
    fun j => hpt _ _ _ ⟨mem_pIdx.2 (hkM j trivial).1, mem_pIdx.2 (hkM j trivial).2⟩
  have hk₂ : ∀ j, ⊤ ≤ zC j ⁻¹ᵁ ((tens K.bundle B).pull πM).U (pIdx _ πM (k j)) :=
    fun j => hpt _ _ _ (mem_pIdx.2 (hkM j trivial))
  refine GlobalTheory.T.sections_adjointNef_separate_etaleFibre hK hNN _ _ pC fC n hWq hMq hn (CanonLB.baseChange HM' K) (N.pull πW) hNC (N'.pull πM)
    (B.pull πM) (LB.isLB_pull hN' πM) (LB.isLB_pull hB πM) m x (πW ⁻¹ᵁ U) hNnC hbig
    (nef_pull hNN pC (fC ≫ pC) fC hWq hMq _ hNnC) hbig' (nef_pull hNN (f ≫ p) (fC ≫ pC) πM hMp hMq N' hN'n) hm hcB
    (hxp j₀) (hpt _ _ _ (show πW (x s₀) ∈ U from hπx s₀ ▸ (hzU j₀ s₀).1)) hUC
    (fun Z e hZ hxZ he hd => hpos Z e hZ (hxZ ⟨s₀, rfl⟩) he hd) J zC
    (fun j j' e => hz (by rw [← hz₁, ← hz₁ j', e])) hzx _ hk₁ a fun g => ?_
  obtain ⟨g', hg'⟩ := exists_val_eq_tens_pull qM πM K.isLB hB g
  have key := sum_val_pull_eq_zero (f ≫ p) n hMp hMc hn (isLB_tens K.isLB hB) zC hz₂ k hkM hk₂ a (fun g => by
    rw [← h g]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hv : ∀ {y y' : Sp ℂ ⟶ M} (_ : y = y') (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U (k j))
        (hy' : ⊤ ≤ y' ⁻¹ᵁ (tens K.bundle B).U (k j)),
        H0.val y (k j) le_top hy g = H0.val y' (k j) le_top hy' g := by
      rintro y _ rfl _ _
      rfl
    exact congrArg (a j * ·) (hv (hz₁ j) (hkM j) (hk j))) g'
  rw [← key]
  exact Finset.sum_congr rfl fun j _ => congrArg (a j * ·) (hg' (zC j) (k j) (hk₁ j) (hk₂ j)).symm

theorem separate_numberField' (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (F : Type) [Field F] (σ : F →+* ℂ) (M W : Scheme.{0}) (pM : M ⟶ Sp F) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n pM] [SmoothOfRelativeDimension n p] (e : f ≫ p = pM) (hMp : IsProjOver pM)
    (hWp : IsProjOver p) (hMc : GeometricallyConnected pM) (hWc : GeometricallyConnected p) (hf : Surjective f)
    (hn : 1 ≤ n) (U : W.Opens) (hU : Etale (f ∣_ U)) (K : CanonLB pM n) (N : LB W) (hN : N.IsLB) (N' B : LB M)
    (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (hNn : letI := algebraΓOfHom p; IsNef F N)
    (hN'n : letI := algebraΓOfHom pM; IsNef F N') (hm : (n + 1).choose 2 < m)
    (hBc : cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN') (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M))
    (hz : Function.Injective z) (hzp : ∀ j, z j ≫ pM = spMap σ) (hzf : ∀ j j', z j ≫ f = z j' ≫ f)
    (hzU : ∀ j s, (z j ≫ f) s ∈ U ∧ AmpleAt N ((z j ≫ f) s)) (k : J → (tens K.bundle B).ι)
    (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ)
    (h : ∀ g : H0 pM (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) : a = 0 := by
  subst e
  exact separate_numberField hK hNN F σ M W p f n hMp hWp hMc hWc hn U hU K N hN N' B hN' hB m hNn hN'n hm hBc J z
    hz hzp hzf hzU k hk a h

theorem generic_data (hNN : GlobalTheory.Published.NefNumerics) {F : Type} [Field F] [CharZero F] {M W : Scheme.{0}}
    [IsIntegral M] [IsIntegral W] (pM : M ⟶ Sp F) (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ)
    [SmoothOfRelativeDimension n pM] [SmoothOfRelativeDimension n p] (hn : 1 ≤ n) (e : f ≫ p = pM)
    (hMp : IsProjOver pM) (hWp : IsProjOver p) (hf : Surjective f) (L : LB W)
    (hL : letI := algebraΓOfHom p; IsNef F L) (hb : letI := algebraΓOfHom pM; IsBig F (L.pull f)) :
    AmpleAt L (genericPoint W) ∧ ∃ U : W.Opens, genericPoint W ∈ U ∧ Etale (f ∣_ U) := by
  subst e
  have hdW := HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p n inferInstance
  have hdM := HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) n inferInstance
  have h₁ : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hWp).1
  have h₂ : IsProper (f ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hMp).1
  have h₃ : IsProper f := IsProper.of_comp f p
  have hr := GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional F M W p f n inferInstance inferInstance hf hdM hdW
  exact ⟨ampleAt_of_isBig_pull hNN p f hn hdW hdM hWp hMp hf hr hL hb, exists_etale_restrict p f hr⟩

theorem sections_separate_quotient_fibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  intro hK hNN hPr F _ _ σ X X' W V _ _ _ sX n _ φ q sW i ℓ hXp hgc hn hφp hWp hqf hqs hcomm hi hℓ hℓφ
  letI := algebraΓOfHom sX
  intro K δ N' B hδ hN' hB N hN m hpull hδn hδb hN'n hm hBc J _ v hv hvσ hvq hvgen k hk a hsum
  haveI := hi
  obtain ⟨W', hW'i, pW, U, M, f, NW, hNW, hMi, hWs, hWp', hWgc, hfp, hfs, hUne, hcls, z, hzU, hzσ, hzf, hzgen⟩ :=
    QuotSetup.exists_resolved_modification hPr F X X' W V sX n φ q sW i ℓ hXp hgc hφp hWp hqf hqs hcomm hi hℓ hℓφ δ hδ N hN hpull J v hvq hvgen
  haveI := hW'i; haveI := hMi; haveI := hWs
  have hUd : Dense (U : Set X) := U.isOpen.dense hUne
  have hMgc : GeometricallyConnected M.str :=
    Modif.geometricallyConnected_str F X sX U n M inferInstance hgc hUd
  have hδσn : (letI := algebraΓOfHom M.str; IsNef F (δ.pull M.σ)) :=
    nef_pull hNN sX M.str M.σ hXp M.proj δ hδn
  have hN'σn : (letI := algebraΓOfHom M.str; IsNef F (N'.pull M.σ)) :=
    nef_pull hNN sX M.str M.σ hXp M.proj N' hN'n
  have hδσb : (letI := algebraΓOfHom M.str; IsBig F (δ.pull M.σ)) := big_pull_modif sX n U M hUne δ hδb
  have hNWn : (letI := algebraΓOfHom pW; IsNef F NW) :=
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective F M.X W' f pW M.str NW hNW (δ.pull M.σ) (LB.isLB_pull hδ M.σ) hfp hWp' M.proj hfs hcls hδσn
  letI := algebraΓOfHom M.str
  have hfNb : IsBig F (NW.pull f) := hδσb.of_cls_eq (LB.isLB_pull hNW f) hcls
  obtain ⟨hamp, UW, hgUW, het⟩ := generic_data hNN M.str pW f n hn hfp M.proj hWp' hfs NW hNWn hfNb
  let K' : CanonLB M.str n := CanonLB.all M.str n
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_push_sections_canonical_modification F X sX n U M K K' B hXp hUne hB
  have hK'B : (tens K'.bundle (B.pull M.σ)).IsLB := isLB_tens K'.isLB (LB.isLB_pull hB M.σ)
  obtain ⟨s0⟩ : Nonempty (Sp ℂ) := inferInstance
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens), x s0 ∈ O → ⊤ ≤ x ⁻¹ᵁ O := by
    intro Y x O hs t _
    rw [Subsingleton.elim t s0]
    exact hs
  choose k' hk' using fun j => (exists_chart hK'B ((z j) s0)).imp fun c hc => hpt _ (z j) _ hc
  have hkσ : ∀ j, ⊤ ≤ (z j ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U (k j) := fun j => by rw [hzσ j]; exact hk j
  choose lam hlam using fun j => hΨ (z j) (hzU j) (k' j) (hk' j) (k j) (hkσ j)
  have hvx : ∀ {x y : Sp ℂ ⟶ X} (e : x = y) (c : (tens K.bundle B).ι) (hx : ⊤ ≤ x ⁻¹ᵁ (tens K.bundle B).U c)
      (hy : ⊤ ≤ y ⁻¹ᵁ (tens K.bundle B).U c) (g : H0 sX (tens K.bundle B) ⊤),
      H0.val x c le_top hx g = H0.val y c le_top hy g := by
    intro x y e c hx hy g
    subst e
    rfl
  have hzinj : Function.Injective z := fun j j' e => hv ((cancel_mono i).1 (by rw [← hzσ j, ← hzσ j', e]))
  have hzp : ∀ j, z j ≫ M.str = spMap σ := fun j => by
    show z j ≫ M.σ ≫ sX = _
    rw [← Category.assoc, hzσ j, Category.assoc]
    exact hvσ j
  have hBM : cls (B.pull M.σ) (LB.isLB_pull hB M.σ) =
      m • CechPic.pull f (cls NW hNW) + cls (N'.pull M.σ) (LB.isLB_pull hN' M.σ) := by
    rw [hcls]
    change CechPic.pull M.σ (cls B hB) = m • CechPic.pull M.σ (cls δ hδ) + CechPic.pull M.σ (cls N' hN')
    rw [hBc, map_add, map_nsmul]
  have hsep := separate_numberField' hK hNN F σ M.X W' M.str pW f n hfp M.proj hWp' hMgc hWgc hfs hn UW het K' NW hNW
    (N'.pull M.σ) (B.pull M.σ) (LB.isLB_pull hN' M.σ) (LB.isLB_pull hB M.σ) m hNWn hN'σn hm hBM
    J z hzinj hzp hzf (fun j s => by rw [hzgen j s]; exact ⟨hgUW, hamp⟩) k' hk' (fun j => a j * (lam j : ℂ)) (fun g => by
      rw [← hsum (Ψ g)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hvx (hzσ j) (k j) (hkσ j) (hk j) (Ψ g), hlam j g]
      ring)
  funext j
  have h := congrFun hsep j
  simpa [Units.ne_zero] using h

end GlobalTheory.QuotSep
end
end
