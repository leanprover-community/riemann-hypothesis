import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfDisjointCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open CoordToExt

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev charBundle (χ : D.X) : LB D.P.A.left := LB.LinComb D.P.L (D.Oφ (𝟙 D.P.A) χ) Oε

theorem comp_Oφ_id {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) :
    x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem charBundle_rig (χ : D.X) : ∃ t : LB.Gen ((charBundle D χ).pull (eSec D.P.A)), t.IsGen := by
  refine ((refines_self _ _).linComb (fun _ : PUnit => eSec D.P.A) (fun _ => 1)).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ?_)
  have e : (η[D.P.A] : 𝟙_ _ ⟶ D.P.A) = 1 := by simp [Hom.one_def]
  rw [Fintype.prod_prod_type, Fintype.prod_unique]
  simp only [_root_.mul_one, eSec, comp_Oφ_id]
  refine (prod_O D η[D.P.A] χ h).trans ?_
  rw [e, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_add (χ χ' : D.X) :
    ∃ t : LB.Iso (charBundle D χ') (LB.div (charBundle D (χ + χ')) (charBundle D χ)), t.IsGen := by
  refine (((refines_self _ _).div (refines_self _ _)).div (refines_self _ _)).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (𝟙 D.P.A))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (toUnit _ ≫ D.c χ') (𝟙 D.P.A) h).trans (Eq.symm ?_)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D (𝟙 D.P.A) _ h) (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h)))
    (congrArg (·⁻¹) (prod_O D (𝟙 D.P.A) _ h))).trans ?_
  rw [c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem charBundle_zero : ∃ t : LB.Gen (charBundle D 0), t.IsGen := by
  refine (refines_self _ _).exists_gen D.P.isLB (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((prod_O D (𝟙 D.P.A) _ h).trans ?_))
  rw [c_zero, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem charBundle_primitive (χ : D.X) : ∃ t : LB.Gen (abelian₂ D.P.A (charBundle D χ)), t.IsGen := by
  refine ((refines_self _ _).linComb _ _).exists_gen D.P.isLB (fun U _ h => ?_)
    _ (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (toUnit _ ≫ D.c χ) (lift (x2 D.P.A 0) (x2 D.P.A 1))).left)
  refine (prod_cub (toUnit _ ≫ D.c χ) (x2 D.P.A 0) (x2 D.P.A 1) h).trans (Eq.symm ?_)
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, comp_Oφ_id]
  refine (prod_square (x2 D.P.A) (fun x => ∏ k, h (D.Oφ x χ k) ^ Oε k)).trans ?_
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_O D _ _ h) (congrArg (·⁻¹) (prod_O D _ _ h)))
    (congrArg (·⁻¹) (prod_O D _ _ h))) (prod_O D _ _ h)).trans ?_
  rw [_root_.mul_one, ← _root_.mul_assoc (toUnit _ ≫ D.c χ)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def splitExt : SplitExt (Spec (CommRingCat.of R)) where
  B := D.P.A
  isAbelian := D.P.isAb
  X := D.X
  O χ := ⟨charBundle D χ, (charBundle_rig D χ).choose, DVR.linComb_isLB _ D.P.isLB _ _,
    (charBundle_rig D χ).choose_spec⟩
  addIso := charBundle_add D
  zeroTriv := charBundle_zero D
  primitive := charBundle_primitive D

variable {D} {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]

theorem nonempty_gtCoord (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) (I : Ideal R) (e : ℕ) :
    Nonempty (GtCoord I D e H) := by
  obtain ⟨d⟩ := h
  refine nonempty_gtCoord_of_isGt hG R I D e H (GtBaseChange.extBC (thick R I e) (splitExt D)) (Iso.refl _)
    (AddEquiv.refl _) (inferInstanceAs (IsMonHom (𝟙 (thickObj R I e D.P.A)))) (fun χ => ?_)
    (GtBaseChange.isGt_extBC _ _ H d)
  refine ((refines_self _ _).div ((refines_self (D.Oφ (𝟙 D.P.A) χ) Oε).linComb
    (fun _ : PUnit => pullback.fst D.P.A.hom (thick R I e)) (fun _ => 1))).exists_gen D.P.isLB
    (fun U _ h => ?_) _ isGen_one
  refine (Fintype.prod_empty _).trans (Eq.symm ((Fintype.prod_sum_type _).trans ?_))
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_prod_type, mul_inv_eq_one, eq_comm, Fintype.prod_unique]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.mul_one]
  have e₀ : ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e).left =
      pullback.fst D.P.A.hom (thick R I e) := Category.id_comp _
  exact congrArg (fun q => h (q ≫ D.Oφ (𝟙 D.P.A) χ k) ^ Oε k) e₀.symm

instance isIso_thick_bot : IsIso (thick R ⊥ 0) := by
  have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk ((⊥ : Ideal R) ^ (0 + 1)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (Ideal.Quotient.mk_bijective_iff_eq_bot _ |>.2 (by simp))
  infer_instance

instance isIso_fstG_bot : IsIso (fstG (⊥ : Ideal R) 0 H).left :=
  inferInstanceAs (IsIso (pullback.fst H.hom (thick R ⊥ 0)))

theorem exists_points (hG : GlobalFnsSt) (h : (splitExt D).IsGt H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T,
      (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
        GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x')) := by
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

end GlobalTheory.TorusModel
end
end

section
noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T T' : Over (Spec (CommRingCat.of R))}

variable {U} in
theorem hasCoords_pull {e : ℕ} {k : T' ⟶ T} {g : GtPt D.toPre T} {g' : GtPt D.toPre T'}
    (h : GtPt.IsPull k.left g g') {Z : Scheme.{0}} {r : Z ⟶ T'.left} {y : Z ⟶ (thickObj R I e G).left} :
    HasCoords U e g (r ≫ k.left) y ↔ HasCoords U e g' r y := by
  rw [hasCoords_iff, hasCoords_iff, h.1, Category.assoc]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun z => forall_congr' fun J =>
    forall_congr' fun hJ => ?_)
  rw [(val_corr hJ (h.2 χ) r).trans (val_pull hJ _ _ _)]

variable {U} in
theorem eq_of_hasCoords {e : ℕ} {g g' : GtPt D.toPre T} {y : T.left ⟶ (thickObj R I e G).left}
    (h : HasCoords U e g (𝟙 _) y) (h' : HasCoords U e g' (𝟙 _) y) : g = g' := by
  rw [hasCoords_iff, Category.id_comp] at h h'
  exact pt_ext (Over.OverMorphism.ext (h.1.symm.trans h'.1)) fun χ z J hJ => (h.2 χ z J hJ).symm.trans (h'.2 χ z J hJ)

theorem isPointOf_iff_thick (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (thickι I e T) (thickHom I e x) := by
  refine ⟨fun h e => h e _ _ _ (thickHom_ι I e x), fun h e Z r y hy => ?_⟩
  have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ thickι I e T = r := ⟨pullback.lift r _ w, pullback.lift_fst _ _ _⟩
  obtain rfl : y = l ≫ thickHom I e x := by
    rw [← cancel_mono (thickι I e G), Category.assoc, thickHom_ι]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

theorem existsUnique_point (hT : IsAdicColimit I T) (g : GtPt D.toPre T) : ∃! x : T ⟶ G, IsPointOf U g x := by
  choose y hy using fun e =>
    exists_hasCoords U e g (thickι I e T) (thickObj R I e T).hom pullback.condition.symm
  refine existsUnique_of_exists_of_unique ?_ fun x x' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    (h.comp_fstG_eq (hy e)).symm.trans (h'.comp_fstG_eq (hy e)))
  obtain ⟨x, hx, -⟩ := hT G.left (fun e => y e ≫ thickι I e G) fun e => by
    have h₁ := (hy (e + 1)).comp (thickMap R I e T)
    rw [thickMap_ι] at h₁
    rw [← Category.assoc, h₁.unique (hy e).succ, Category.assoc, thickMap_ι]
  have hw : x ≫ G.hom = T.hom := hT.hom_ext fun e => by
    have h₁ : thickι I e G ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    rw [reassoc_of% hx e, h₁, reassoc_of% (hy e).1, Over.w]
  refine ⟨Over.homMk x hw, (isPointOf_iff_thick U g _).2 fun e => ?_⟩
  have : thickHom I e (Over.homMk x hw : T ⟶ G) = y e := by
    rw [← cancel_mono (thickι I e G), thickHom_ι]
    exact hx e
  rw [this]
  exact hy e

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T}

theorem existsUnique_lift (hΦ : Represents Φ) (hT : IsAdicColimit I T) (x : T ⟶ G) :
    ∃! w : T ⟶ H, IsPointOf U (Φ T w) x := by
  have pl : ∀ (e : ℕ) (w : T ⟶ H), HasCoords U e (Φ T w) (thickι I e T) (thickHom I e x) ↔
      HasCoords U e (Φ _ (fstG I e T ≫ w)) (𝟙 _) (thickHom I e x) := fun e w => by
    rw [← hasCoords_pull (hΦ.1 _ _ (fstG I e T) w), Category.id_comp]; rfl
  refine existsUnique_of_exists_of_unique ?_ fun w w' h h' => Over.OverMorphism.ext (hT.hom_ext fun e =>
    congrArg (·.left) ((Φ _).injective (eq_of_hasCoords ((pl e w).1 ((isPointOf_iff_thick U _ x).1 h e))
      ((pl e w').1 ((isPointOf_iff_thick U _ x).1 h' e)))))
  have ex : ∀ e, ∃ w : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶ H,
      HasCoords U e (Φ _ w) (𝟙 _) (thickHom I e x) := fun e => by
    obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf (U.gt e) (T := (Over.map (thick R I e)).obj (thickObj R I e T))
      (thickHom I e x) (by rw [← Category.assoc, Over.w]; rfl)
    refine ⟨(Φ _).symm ξ, ?_⟩
    rw [Equiv.apply_symm_apply, hasCoords_iff]
    refine ⟨hξ.1.symm.trans (Category.id_comp _).symm, fun χ z J hJ => ?_⟩
    have := (val_corr hJ (hξ.2 χ) (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  choose w hw using ex
  obtain ⟨v, hv, -⟩ := hT H.left (fun e => (w e).left) fun e => by
    let m : (Over.map (thick R I e)).obj (thickObj R I e T) ⟶
        (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) T) := Over.homMk (thickMap R I e T)
      (((congrArg (thickMap R I e T ≫ ·) (Over.w (fstG I (e + 1) T)).symm).trans
        (thickMap_ι_assoc I e T T.hom)).trans (Over.w (fstG I e T)))
    have h₁ := (hw (e + 1)).comp (thickMap R I e T)
    rw [thickMap_thickHom, Category.comp_id, ← Category.id_comp (thickMap R I e T)] at h₁
    have h₂ := (hasCoords_pull (hΦ.1 _ _ m (w (e + 1)))).1 h₁
    exact congrArg (·.left) ((Φ _).injective (eq_of_hasCoords h₂ (hw e).succ))
  have hv' : v ≫ H.hom = T.hom := hT.hom_ext fun e => by
    rw [reassoc_of% hv e, Over.w]
    exact (Over.w (fstG I e T)).symm
  refine ⟨Over.homMk v hv', (isPointOf_iff_thick U _ x).2 fun e => (pl e _).2 ?_⟩
  have : fstG I e T ≫ (Over.homMk v hv' : T ⟶ H) = w e := Over.OverMorphism.ext (hv e)
  rw [this]
  exact hw e

theorem exists_mulEquiv (hG : GlobalFnsSt) (hΦ : Represents Φ) :
    ∃ J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)),
      ∀ T hT w x, J T hT w = x ↔ IsPointOf U (Φ T w) x := by
  choose j hj hu using fun T (hT : IsAdicColimit I T) (w : T ⟶ H) => existsUnique_point U hT (Φ T w)
  have bij : ∀ T hT, Function.Bijective (j T hT) := fun T hT => (Function.bijective_iff_existsUnique _).2 fun x =>
    (existsUnique_congr fun w => ⟨fun h => (hu T hT w x h).symm, fun h => h ▸ hj T hT w⟩).1
      (existsUnique_lift U hΦ hT x)
  exact ⟨fun T hT => MulEquiv.mk' (Equiv.ofBijective _ (bij T hT)) fun w w' =>
      (hu T hT _ _ ((hj T hT w).mul hG (hj T hT w') (hΦ.2 T w w'))).symm,
    fun T hT w x => ⟨fun h => h ▸ hj T hT w, fun h => (hu T hT w x h).symm⟩⟩

end GlobalTheory.TorusModel
end
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open GlobalTheory.AdicColimit

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem exists_isGt (hG : GlobalFnsSt) (E : SplitExt S) :
    ∃ (H : Over S) (_ : GrpObj H), IsCommMonObj H ∧ E.IsGt H := by
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := exists_grpObj_gtDatum_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, hc, ⟨d⟩⟩

def polPull [IsAffine S] (P : PolAV S) : PolAV S' :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
  { A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top S) (fun _ => trivial) P.ample
    ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }

theorem torsion_pullback (B : Over S) [GrpObj B] (N : ℕ) (h₁ : IsFinite (𝟙 B ^ N).left) (h₂ : Flat (𝟙 B ^ N).left) :
    IsFinite (torsion ((Over.pullback f).obj B) N).hom ∧ Flat (torsion ((Over.pullback f).obj B) N).hom := by
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁ h₂
  have H := MulEtaleDvr.isPullback_torsion ((Over.pullback f).obj B) N
  rw [← MulEtaleDvr.pullback_map_mulN] at H
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H
      (MorphismProperty.overPullbackMap (P := @IsFinite) f _ h₁),
    MorphismProperty.of_isPullback (P := @Flat) H (MorphismProperty.overPullbackMap (P := @Flat) f _ h₂)⟩

variable {H : Over S} [GrpObj H]

theorem exists_pushEquiv (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H), ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

def actPull [IsCommMonObj H] {O : Type} [Ring O] (ρ : RingAct H O) : RingAct ((Over.pullback f).obj H) O where
  act a := (Over.pullback f).map (ρ.act a)
  hom a := by have := ρ.hom a; infer_instance
  map_one := by rw [ρ.map_one, CategoryTheory.Functor.map_id]
  map_mul a b := by rw [ρ.map_mul, CategoryTheory.Functor.map_comp]
  map_add a b := by
    rw [ρ.map_add]
    exact map_mul (Over.pullback f).homMonoidHom (ρ.act a) (ρ.act b)

end BaseChange

theorem exists_model (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hO : U.OLinear O ιD ιA ιG)
    {S' : Scheme.{0}} (f : S' ⟶ Spec (CommRingCat.of R)) :
    ∃ (Gt : Over S') (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt O)
      (J : ∀ (T : Over S') (s : T.left ⟶ Spec (CommRingCat.of R)), s = T.hom ≫ f → IsAdicColimit I (Over.mk s) →
        ((T ⟶ Gt) ≃* (Over.mk s ⟶ G))),
      (GtBaseChange.extBC f (splitExt D.toPre)).IsGt Gt ∧
      (∀ T T' s s' hs hs' hT hT' (k : T' ⟶ T) (x : T ⟶ Gt),
        (J T' s' hs' hT' (k ≫ x)).left = k.left ≫ (J T s hs hT x).left) ∧
      ∀ T s hs hT (x : T ⟶ Gt) (a : O), J T s hs hT (x ≫ ρ.act a) = J T s hs hT x ≫ ιG.act a := by
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hG hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hG ιD (Φ := Φ) hΦ
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hG (Φ := Φ) hΦ
  choose π hπ using exists_pushEquiv f (H := H)
  obtain ⟨d⟩ := hH
  refine ⟨(Over.pullback f).obj H, inferInstance, inferInstance, actPull f ρ,
    fun T s hs hT => (π T s hs).trans (J _ hT), GtBaseChange.isGt_extBC f _ H d, ?_, ?_⟩
  · intro T T' s s' hs hs' hT hT' k x
    let k₀ : Over.mk s' ⟶ Over.mk s := Over.homMk k.left (by
      change k.left ≫ s = s'
      rw [hs, hs', Over.w_assoc])
    have e : π T' s' hs' (k ≫ x) = k₀ ≫ π T s hs x := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc]; rfl)
    have := (hJ _ hT' (k₀ ≫ π T s hs x) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).pull k₀ (hΦ.1 _ _ k₀ _))
    rw [← e] at this
    exact congrArg (·.left) this
  · intro T s hs hT x a
    have e : π T s hs (x ≫ (actPull f ρ).act a) = π T s hs x ≫ ρ.act a := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc, Category.assoc]
      exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _))
    have := (hJ _ hT (π T s hs x ≫ ρ.act a) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).smul hG hO a (hρ a _ _))
    rw [← e] at this
    exact this

theorem isAdicColimit_of_pow {R A : Type} [CommRing R] [CommRing A] (I : Ideal R) (φ : R →+* A) (n : ℕ)
    (h : ∀ a ∈ I ^ n, φ a = 0) : IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  refine isAdicColimit_of_factor n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) φ
    fun a ha => h a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)))) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  rfl

theorem isAdicColimit_of_finite_flat {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (I : Ideal R)
    (f : R →+* O) (hO : IsAdicComplete (I.map f) O) (hm : ∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ I.map f)
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] :
    IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
  have := henselianLocalRing_of_le_radical (I.map f) hm
  refine isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing isAdicColimit_of_disjoint_cover
    R I O A _ ?_
  rw [← Ideal.map_map]
  exact GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O _ hO A

theorem main : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  intro hL _ E _ _ _ H V _ _ _ _ t P O _ _ f _ hO hm
  letI := H.starRing
  obtain ⟨Gt, _, _, ρ, J, h₁, h₂, h₃⟩ := exists_model hL.globalFns P.U.toUnifPre P.lin (spMap f)
  have hs : ∀ (A : Type) [CommRing A] [Algebra O A],
      Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)) = (specO O A).hom ≫ spMap f := fun A _ _ => by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  have hc : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨
      ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) →
      IsAdicColimit (maximalIdeal V) (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
    rintro A _ _ (⟨_, _⟩ | ⟨n, hn⟩)
    exacts [isAdicColimit_of_finite_flat _ f hO hm A, isAdicColimit_of_pow _ _ n hn]
  refine ⟨GtBaseChange.extBC (spMap f) (splitExt P.D.toPre), polPull (spMap f) P.D.toPre.P, rfl, HEq.rfl,
    Gt, inferInstance, inferInstance, ρ, fun A _ _ hA => J (specO O A) _ (hs A) (hc A hA), h₁, fun N hN => ?_,
    fun A A' _ _ _ _ hA hA' φ x => h₂ _ _ _ _ _ _ _ _ (ptMap φ) x,
    fun A _ _ hA => ⟨map_mul _, h₃ _ _ _ _, MulEquiv.injective _, fun _ => MulEquiv.surjective _,
      fun _ g _ _ => MulEquiv.surjective _ g⟩⟩
  obtain ⟨a, b, -⟩ := hL.mulN _ P.D.toPre.P N hN
  exact torsion_pullback (spMap f) P.D.toPre.P.A N a b

end GlobalTheory.TorusModel
end
end
