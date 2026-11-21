import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFields
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGraded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) [GeometricallyIntegral p] (b : Y.functionField), (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) → b ∈ (GlobalTheory.Cartier.constFn p).range := by
  first | exact @GlobalTheory.GeomIntConst.mem_range_constFn | exact GlobalTheory.GeomIntConst.mem_range_constFn | (intros; apply GlobalTheory.GeomIntConst.mem_range_constFn <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstDescent

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier

theorem exists_fnOf_eq_of_algebraic {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp F) (U : X.Opens) (hU : genericPoint X ∈ U)
    {a : X.functionField} (ha : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (Cartier.constFn p) a = 0) :
    ∃ s : Γ(X, U), fnOf U hU s = a := by
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI := (algX p U).toAlgebra
  letI : Algebra F X.functionField := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower F Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U hU).symm
  obtain ⟨P, hP, hPa⟩ := ha
  have hint : IsIntegral F a := (show IsAlgebraic F a from
    ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩).isIntegral
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(X, U))
    (A := X.functionField)).1 hint.tower_top
  exact ⟨s, hs⟩

theorem appLE_comp_algX {F : Type} [CommRing F] {W V : Scheme.{0}} (pW : W ⟶ Sp F) (π : V ⟶ W) :
    (π.appLE ⊤ ⊤ le_top).hom.comp (algX pW ⊤) = algX (π ≫ pW) ⊤ := by
  have e := Scheme.Hom.appLE_comp_appLE π pW ⊤ ⊤ ⊤ le_top le_top
  exact congrArg (fun f => (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom) e

theorem descent : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V]
    [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV →
    (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) →
      b ∈ (GlobalTheory.Cartier.constFn pV).range) →
    ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  intro F _ W V _ _ _ pW pV π hπ hV a ha
  subst hπ
  have hW : genericPoint W ∈ (⊤ : W.Opens) := trivial
  have hV' : genericPoint V ∈ (⊤ : V.Opens) := trivial

  let φ : Γ(W, ⊤) →+* V.functionField := (fnOf ⊤ hV').comp (π.appLE ⊤ ⊤ le_top).hom
  have hφ : φ.comp (algX pW ⊤) = Cartier.constFn (π ≫ pW) := by
    simp only [φ, RingHom.comp_assoc, appLE_comp_algX]
    rfl
  obtain ⟨s, hs⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW ha
  obtain ⟨P, hP, hPa⟩ := ha
  have h0 : P.eval₂ (algX pW ⊤) s = 0 := fnOf_injective ⊤ trivial (by
    rw [Polynomial.hom_eval₂, fnOf_comp_algX pW ⊤ hW, hs, hPa, map_zero])
  have hb : P.eval₂ (Cartier.constFn (π ≫ pW)) (φ s) = 0 := by
    rw [← hφ, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c, hc⟩ := hV _ ⟨P, hP, hb⟩
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : a - Cartier.constFn pW c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht : fnOf ⊤ hW (s - algX pW ⊤ c) = a - Cartier.constFn pW c := by
    rw [map_sub, hs, ← fnOf_comp_algX pW ⊤ hW, RingHom.comp_apply]
  have hφt : φ (s - algX pW ⊤ c) = 0 := by
    rw [map_sub, ← RingHom.comp_apply φ, hφ, hc, sub_self]
  have hinv : ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.eval₂ (Cartier.constFn pW) (a - Cartier.constFn pW c)⁻¹ = 0 := by
    letI : Algebra F W.functionField := (Cartier.constFn pW).toAlgebra
    have h1 : IsAlgebraic F a :=
      ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩
    have h2 : IsAlgebraic F (a - Cartier.constFn pW c) :=
      h1.sub (isAlgebraic_algebraMap (A := W.functionField) c)
    obtain ⟨Q, hQ, hQx⟩ := h2.inv
    exact ⟨Q, hQ, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at hQx; exact hQx⟩
  obtain ⟨u, hu⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW hinv
  have htu : (s - algX pW ⊤ c) * u = 1 := fnOf_injective ⊤ trivial (by
    rw [map_mul, ht, hu, map_one, mul_inv_cancel₀ hne'])
  have h3 := congrArg φ htu
  rw [map_mul, hφt, zero_mul, map_one] at h3
  exact zero_ne_one h3

end GlobalTheory.ConstDescent
end
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V] [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV → (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) → b ∈ (GlobalTheory.Cartier.constFn pV).range) → ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) → a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  atlas_forward_decl GlobalTheory.ConstDescent.descent
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CompOfVar

theorem exists_var_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hsm Y π hπ
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  let z : gen Z := π (genericPoint Y.X)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := GlobalTheory.GenFibreComp.isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z ≫ spMap e.toRingHom) :=
    (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension Dw.dim (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : Y.X ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : Smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.ModifSections.isNormalScheme_of_smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom)
  have : GeometricallyConnected (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
    exact GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme F V.toScheme Y.X _ Y.str g (by rw [reassoc_of% hg, hπ])
      (GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range F Y.X Y.str)
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ]
    exact hr

end GlobalTheory.CompOfVar
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_connectedComponent_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  first | exact @GlobalTheory.CompOfVar.exists_var_comp | exact GlobalTheory.CompOfVar.exists_var_comp | (intros; apply GlobalTheory.CompOfVar.exists_var_comp <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_component_unique_point_each_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  first | exact @GlobalTheory.CarryAll.carries_everywhere | exact GlobalTheory.CarryAll.carries_everywhere | (intros; apply GlobalTheory.CarryAll.carries_everywhere <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_unique_lift_any_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → (∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat Dw.mult K, Par 0 ⊤ h → ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ Bears E' φ A h p := by
  first | exact @GlobalTheory.ShFam.FieldLift.lifts_of_closed | exact GlobalTheory.ShFam.FieldLift.lifts_of_closed | (intros; apply GlobalTheory.ShFam.FieldLift.lifts_of_closed <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ y : Y₁.X, ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  first | exact @GlobalTheory.FlagBundle.dominates_O | exact GlobalTheory.FlagBundle.dominates_O | (intros; apply GlobalTheory.FlagBundle.dominates_O <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.CoBear₂ | exact GlobalTheory.FlagBundle.CoBear₂ | (intros; apply GlobalTheory.FlagBundle.CoBear₂ <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.coBear_comp_of_isHom | exact GlobalTheory.FlagBundle.coBear_comp_of_isHom | (intros; apply GlobalTheory.FlagBundle.coBear_comp_of_isHom <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.ClsMap

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL Y' φ' f' S' hR'

  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', -⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  have R₁ : Reps Eb E' φ f := ⟨hφ, hsub,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩
  have R₂ : Reps Eb S' φ' f' := hR'.reps

  obtain ⟨ψ, hψ, hG⟩ := GlobalTheory.T.exists_functionField_map_fullFlag_generic_point F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing F Y'.Fn (ratOf Y') C.Y.Fn (ratOf C.Y) ψ
    (GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique hφ
  refine ⟨h, hf, fun K _ _ => GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ h hf
    (GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG h hh) K⟩

end GlobalTheory.ShFam.ClsMap
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  atlas_forward_decl GlobalTheory.ShFam.ClsMap.main
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagCptRad

theorem isHom_apply_eq {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    {M : GlobalTheory.ZH.RatModel F Ω} {M' : GlobalTheory.ZH.RatModel F Ω'} {φ ψ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}
    (hφ : M.IsHom M' φ f) (hψ : M.IsHom M' ψ f) (x : Ω) : φ x = ψ x := by
  have hx : ∀ w, x ∈ M.O (f (M'.pt w)) := fun w => by
    have e1 : (M'.pt ≫ f) w = f (M'.pt w) := Scheme.Hom.comp_apply _ _ _
    have e2 : (M'.pt ≫ f) w = genericPoint M.Z := by
      rw [hφ, Scheme.Hom.comp_apply, M.pt_apply]
    rw [← e1, e2, M.O_genericPoint]; exact Algebra.mem_top
  have h1 := hφ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  have h2 := hψ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  rw [GlobalTheory.ZH.RatModel.val_pt] at h1 h2
  exact h1.symm.trans h2

theorem keepsRad_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hj hjs f hf f₀ Eb A₀ hT hlift φ hφ
  haveI : CharZero F := RingHom.charZero e.toRingHom
  obtain ⟨Y', φ', f', S', -, hR⟩ := tower _ (ratOf X) X.dim Eb (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  change Y'.X ⟶ X.X at f'
  obtain ⟨h, hh, hbij⟩ := GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints E H Dw l Xo c O β Z F e C X j hj hjs f hf f₀ Eb A₀ hT hlift Y' φ' f' S' hR
  have hs' : f' ≫ X.str = Y'.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hstr : h ≫ Y'.str = C.Y.str := by
    rw [← hs', ← Category.assoc, hh, ← hjs, ← C.π_str, ← hf, Category.assoc]
  have hiso : IsIso h := GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero F C.Y Y' h hstr hbij
  obtain ⟨ψ, S'', hR2⟩ := exists_refines_of_iso (ratOf Y') (ratOf C.Y) (@asIso _ _ _ _ h hiso) hstr S'
  have hR2' : Refines S' S'' ψ h := hR2
  subst hh
  have hR3 := hR.comp hR2'
  have hrad : KeepsRad (ratOf X) (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.rad
  have hhom : (ratOf X).IsHom (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.hom
  intro z' g hg
  rw [isHom_apply_eq hφ hhom g]
  exact hrad z' g hg

end GlobalTheory.FlagCptRad
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_principal_ideals_stay_radical_flag_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  atlas_forward_decl GlobalTheory.FlagCptRad.keepsRad_of_flagCpt
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.BaseRefine

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', hG⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  exact ⟨E', φ, ⟨fun _ => Nat.zero_le _, hφ, hsub,
    GlobalTheory.T.radical_principal_ideals_stay_radical_flag_component E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩, hG⟩

end GlobalTheory.ShFam.BaseRefine
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  atlas_forward_decl GlobalTheory.ShFam.BaseRefine.main
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_base_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∃ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn), (j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) ∧ IsLieBase e (Φ.C k) X j f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.T.exists_variety_connectedComponent_genericFibre E H Dw l Xo c O β T.Z F e T.smooth (Φ.C k).Y (Φ.C k).π (Φ.C k).π_str
  let f : (Φ.C k).Y.X ⟶ X.X := IsOpenImmersion.lift j (Φ.C k).π hr
  have hf : f ≫ j = (Φ.C k).π := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f₀, Eb, A₀, hT⟩ := GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β T.Z F e X j hj
  have hcar := GlobalTheory.T.flagSpace_component_unique_point_each_flag E H Dw l Xo c O β T.Z F e σ _ U Φ k X j hoi hj f hf
  obtain ⟨E', φ, hR, hG⟩ := GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded E H Dw l Xo c O β T.Z F e (Φ.C k) X j hoi hj f hf f₀ Eb A₀ hT
    (fun K _ _ χ x hx g => hcar K χ x hx g)
  exact ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, ⟨hoi, hf, hT⟩, hR, hG⟩
end
end
