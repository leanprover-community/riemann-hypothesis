import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHomStatement
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparison
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransitionMapRaisedModelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8Sharp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExtStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatricesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChangeStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.RaisedAmple

theorem exists_closure {O F F' : Type} [CommRing O] [Field F] [Field F'] [CharZero F] [CharZero F'] (β : O →+* F)
    (k : F →+* F') (hβ : IsDedFrac β) (hk : k.Finite) :
    ∃ (O' : Type) (_ : CommRing O') (β' : O' →+* F') (b : O →+* O'), IsDedFrac β' ∧ β'.comp b = k.comp β ∧ b.Finite ∧
      ∀ x : F', IsIntegral ℤ x → x ∈ β'.range := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := k.toAlgebra
  letI := (k.comp β).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F F' := hk
  have hD : IsDedekindDomain (integralClosure O F') := integralClosure.isDedekindDomain O F F'
  have hF : IsFractionRing (integralClosure O F') F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hfin : Module.Finite O (integralClosure O F') := IsIntegralClosure.finite O F F' _
  refine ⟨integralClosure O F', inferInstance, algebraMap _ F', algebraMap O _, ⟨⟨inferInstance, hD⟩, inferInstance, hF⟩,
    rfl, hfin, fun x hx => ⟨⟨x, hx.tower_top⟩, rfl⟩⟩

theorem lift_lift {T X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (k : W ⟶ Z) (hk : g' ≫ g = k) (r : T ⟶ X)
    (s : T ⟶ W) (w : r ≫ f = s ≫ k) (r' : T ⟶ pullback f g) (h₁ : r' ≫ pullback.fst _ _ = r)
    (h₂ : r' ≫ pullback.snd _ _ = s ≫ g') :
    ∃ e : pullback f k ≅ pullback (pullback.snd f g) g', pullback.lift r' s h₂ = pullback.lift r s w ≫ e.hom := by
  subst hk
  refine ⟨(pullbackLeftPullbackSndIso f g g').symm, ?_⟩
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst, h₁]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.lift_snd]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isIntegral_zeta {A : ℕ} (hA : 0 < A) : IsIntegral ℤ (zeta A) :=
  (Complex.isPrimitiveRoot_exp A hA.ne').isIntegral hA

theorem exists_coeff {l : Level H} (c : Coeff l) (l' : Level H) : ∃ c' : Coeff l', c.F ≤ c'.F := by
  have := c.fin
  have := GlobalTheory.BaseRing.finiteDimensional_KA l'
  have hM : 0 < l'.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l'.three_le) l'.A_pos
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l'.M'}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_zeta hM).tower_top
  refine ⟨⟨(c.F ⊔ KA l') ⊔ IntermediateField.adjoin ℚ {zeta l'.M'}, inferInstance, fun τ a => ?_, ?_, ?_⟩, ?_⟩
  · exact (le_sup_left.trans le_sup_left : c.F ≤ _) (c.conj τ a)
  · exact (le_sup_right : IntermediateField.adjoin ℚ {zeta l'.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_left.trans le_sup_left

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← Nat.div_mul_div hd'.1 hd.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc,
      h.1, Category.assoc]
  · rw [← Nat.div_mul_div hd'.2.2 hd.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a),
      Category.assoc, h.2, Category.assoc]

theorem exists_isInc_of_mem {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S A : ℕ}
    (h₁ : (1 + H.rt0) / 2 ∈ i.range) (h₂ : (S : ℂ)⁻¹ ∈ i.range) (h₃ : zeta A ∈ i.range) :
    ∃ b : RZ H S A →+* O, IsInc (RZ H S A).subtype i b := by
  have hle : RZ H S A ≤ i.range := by
    unfold RZ
    rw [Subring.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))

theorem exists_cover (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O]
    [CommRing O'] {β : O →+* c.F} {β' : O' →+* c'.F} (Y : Model (Xo l) c β) (b : O →+* O') (d : l.Dvd l')
    (hc : c.F ≤ c'.F) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = (IntermediateField.inclusion hc).toRingHom.comp β) (hfin : b.Finite) :
    ∃ (Y' : Model (Xo l') c' β') (r : (Xo l').XF c' ⟶ (Xo l).XF c) (ν : SABMap Y'.oF.t Y.oF.t r)
      (a : (ofModel Y').Above (ofModel Y) b r ν), LevComp Y'.oF Y.oF r ν ∧ IsFinite a.π ∧ Surjective a.π := by
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l' (KA l') (KA l') (baseKA l') (baseKA l') (RingHom.id _) _ _ (Xo l').s
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ (Xo l').s)
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l').univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -, hs⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l' c' o m0 d
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l').XF c' ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp o Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩
  obtain ⟨e, he⟩ := lift_lift (Xo l).s _ _ (spMap k) (by rw [hkk, spMap_comp]) r _ hr r' hr₁ hr₂
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hs' : Surjective (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hsm : Smooth (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) := by
    have := (Xo l').smooth
    have : Smooth (Xo l').s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, ⟨a⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ Y.oF.t β _ _ _
    (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) o.t β' (ofModel Y) b _ r' hr₂ ν' hβ hβ'
    hb hnorm hf'
  have hπ : IsFinite a.π := by
    have := a.fin
    have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hfin
    rw [← pullback.lift_fst a.π C.s a.π_over]
    infer_instance
  have hr' : Surjective r' := by
    have : Surjective (spMap (IntermediateField.inclusion hc).toRingHom) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    rw [← pullback.lift_fst r' _ hr₂]
    infer_instance
  have hj : IsDominant (ofModel Y).j := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.2.2.2.2.1
  have hd : IsDominant a.π := by
    have : IsDominant (C.j ≫ a.π) := by rw [a.j_comm]; infer_instance
    exact IsDominant.of_comp C.j a.π
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    r', ν', a, hl', hπ, surjective_of_isDominant_of_isClosed_range a.π a.π.isClosedMap.isClosed_range⟩

theorem amp_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨n ^ k, Y'.X, a.π, Y'.t, a.mu, hodd.pow, by rw [Nat.cast_pow]; exact hu.pow k, hf, hs, ⟨A'⟩⟩

end GlobalTheory.RaisedAmple
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.RaisedDescends

theorem map_nsmul_eq_pow {A Q : Type*} [AddMonoid A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (m : ℕ) (a : A) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.mp h
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem Cpt_j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem levComp_comp {D : Datum H} {l l' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    (m : ObjMap o'' o' g) {ν : SABMap o'.t o.t r} (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r))
    (e : ν'.φ = m.toSABMap.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := h.1 a
    rw [← map_nsmul_eq_pow _ o'.eta_add] at h1
    rw [← map_nsmul_eq_pow _ o''.eta_add, e, ← Category.assoc, m.eta, Category.assoc, h1, Category.assoc]
  · have h1 := h.2 a
    rw [← map_nsmul_eq_pow _ o'.etaA_add] at h1
    rw [← map_nsmul_eq_pow _ o''.etaA_add, e, ← Category.assoc, m.etaA, Category.assoc, h1, Category.assoc]

theorem descends_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  intro h1 h2 h3 E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y hn hd hA hβ hR
  obtain ⟨b, r, ν, hb, hlev, ⟨a⟩⟩ := hR
  obtain ⟨k, r₁, ν₁, hr₁, hk, hlev₁, hfin, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l hd
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hD₀ : IsDedFrac B.β := isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc
  have hD₁ : IsDedFrac (k.comp B.β) :=
    isDedFrac_of_isInc l _ 1 hS hA rfl _ fun x => (hk (B.β x)).trans (B.β_inc x)
  have hsm : Smooth (Xo l).s := by
    have := (Xo l).smooth
    exact SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨C', ⟨a'⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ B.β _ _ _ (Xo l).s (Xo l).univ.t (k.comp B.β) B.C (RingHom.id _) k r₁ hr₁ ν₁
    hD₀ hD₁ (RingHom.comp_id _)
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1 hfin
  have hbβ : β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp (k.comp B.β) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hred : IsReduced ((Xo l).XF c) :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1
  obtain ⟨ν₂, hν₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ Y.m0.toSABMap
  have hover : r ≫ (Xo l₀).s = (pullback.fst _ _ ≫ r₁) ≫ (Xo l₀).s := by
    have := mono_spMap_of_isDedFrac hD₀
    rw [← cancel_mono (spMap B.β), Category.assoc, ← Cpt_j_over B.C, ← Category.assoc, ← a.j_comm, Category.assoc,
      a.π_over, ← Category.assoc, Cpt_j_over, Category.assoc, ← spMap_comp, hbβ, spMap_comp, spMap_comp,
      Category.assoc, Category.assoc, reassoc_of% hr₁, pullback.condition_assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique h1 h2 h3 E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r _ ν ν₂ hred hover hlev
    (levComp_comp Y.m0 hlev₁ ν₂ hν₂)
  obtain ⟨h, mu', hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C C' (ofModel Y) (RingHom.id _) b (IntermediateField.inclusion c.le).toRingHom r₁ ν₁ a' (pullback.fst _ _)
    Y.m0.toSABMap a.π a.mu a.π_over hβ hbβ pullback.condition
    (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₂, Category.assoc])
  exact GlobalTheory.descends_of_above E H D l (Xo l) c O β Y _ (k.comp B.β) C' b ⟨h, hh, hf a.fin, mu', hj, hφ⟩ hD₁ hβ hbβ

end GlobalTheory.RaisedDescends

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_level_one_descends : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  atlas_forward_decl GlobalTheory.RaisedDescends.descends_of_raises
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_goodReduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X : Scheme.{0}) (z : X ⟶ Sp ℤ) (G : Over X) [GrpObj G] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (y : Sp V ⟶ X) (𝒜 : Over (Sp V)) [GrpObj 𝒜] (A : Over (Sp C)) [GrpObj A] (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ G.left), LocallyOfFiniteType z → IsSemiAbelian G → IsAbelianScheme 𝒜 → IsGrpPullback A 𝒜 (spMap (algebraMap V C)) φ₁ → IsGrpPullback A G (spMap (algebraMap V C) ≫ y) φ₂ → Set.range y ⊆ abLocus G := by
  first | exact @GlobalTheory.range_subset_abLocus_of_goodReduction | exact GlobalTheory.range_subset_abLocus_of_goodReduction | (intros; apply GlobalTheory.range_subset_abLocus_of_goodReduction <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodRedUnitBall

theorem finiteType_closure (s : Set ℂ) (hs : s.Finite) :
    (algebraMap ℤ (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) := Algebra.FiniteType.adjoin_of_finite hs
  rw [RingHom.finiteType_algebraMap]
  have e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_int]; rfl
  refine Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s)
    (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective

theorem valuationRing_of_unitBall {V C : Type} [CommRing V] [NormedField C] [Algebra V C] (h : IsUnitBall V C) :
    ∃ _ : IsDomain V, ValuationRing V ∧ IsFractionRing V C := by
  have hd : IsDomain V := h.1.isDomain _
  refine ⟨hd, ?_⟩
  have key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹ := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · exact Or.inl ((h.2 x).2 hx)
    · exact Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 h.1
  have hf : IsFractionRing V C := by
    refine IsFractionRing.of_field V C fun x => ?_
    rcases key x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, 1, by simp [ha]⟩
    · exact ⟨1, a, by simp [ha]⟩
  exact ⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩

theorem goodRedExt_unitBall : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Raises B Y → ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra V C], IsUnitBall V C → Y.GoodRedExt V C := by
  intro hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩
  obtain ⟨_, _, _⟩ := valuationRing_of_unitBall hV
  obtain ⟨b₀, r, ν, -, -, ⟨ab⟩⟩ := hR
  have hp : IsProper Y.s := projProper _ _ _ Y.proj
  have hp' : IsProper B.C.s := projProper _ _ _ B.C.proj
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨q⟩⟩ := hE
    { R := V
      K := C
      i₁ := y ≫ Y.j
      i₂ := spMap b
      commSq := ⟨by rw [Category.assoc]; exact hy⟩ }
  obtain ⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j :=
    ⟨q.l, q.fac_right, q.fac_left⟩
  obtain ⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π := ⟨_, rfl⟩
  refine ⟨y', hs, hl, ?_⟩
  have hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact finiteType_closure _ (Set.toFinite _)
  have hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ := hπ ▸ ab.mu.cart
  have h₃ := (h₂.comp Y.m.cart).comp hc
  have h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ) := by
    rw [← Category.assoc, hl]
    exact h₃
  have h₅ := GlobalTheory.T.range_subset_abelianLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _
    inferInstance B.C.t.semi hab h₁ h₄
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)

end GlobalTheory.GoodRedUnitBall
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevActs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem exists_sab_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n'.φ ≫ n.φ = 𝟙 _ ∧ n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevUniq.exists_sab_cast i e.inv_hom_id.symm
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', h, ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

section

variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem exists_lift_end {C' : Cpt c' t₀' β'} {C : Cpt c t₀ β} {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r}
    (a : C'.Above C b r ν) (hD : IsDedFrac β') (e' : U' ⟶ U') (n' : SABMap t₀' t₀' e') (ρ : C.X ⟶ C.X)
    (mu : SABMap C.t C.t ρ) (he' : e' ≫ c' = c') (hρ : ρ ≫ C.s = C.s) (hj : r ≫ C.j ≫ ρ = e' ≫ r ≫ C.j)
    (hφ : ν.φ ≫ C.m.φ ≫ mu.φ = n'.φ ≫ ν.φ ≫ C.m.φ) :
    ∃ (h : C'.X ⟶ C'.X) (mu' : SABMap C'.t C'.t h), h ≫ C'.s = C'.s ∧ C'.j ≫ h = e' ≫ C'.j ∧
      C'.m.φ ≫ mu'.φ = n'.φ ≫ C'.m.φ := by
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp mu a.mu
  obtain ⟨h, mu', hh, -, -, h₁, h₂, -⟩ := Cpt.Above.exists_lift E H U F O c t₀ β U' F' O' c' t₀' β' U' F' O' c' t₀' β'
    C C' C' b (RingHom.id _) (RingHom.id _) r ν a e' n' (a.π ≫ ρ) m
    (by rw [Category.assoc, hρ, a.π_over, RingHom.id_comp]) hD (by rw [RingHom.id_comp, RingHom.comp_id])
    (by rw [he', spMap_id', Category.comp_id]) (by rw [← Category.assoc, a.j_comm, Category.assoc, hj])
    (by rw [hm, ← Category.assoc, a.φ_comm, Category.assoc, hφ])
  exact ⟨h, mu', by rw [hh, spMap_id', Category.comp_id], h₁, h₂⟩

theorem hom_ext_j (C : Cpt c t₀ β) (hD : IsDedFrac β) {f g : C.X ⟶ C.X} (h : C.j ≫ f = C.j ≫ g) : f = g := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hD
  letI := β.toAlgebra
  obtain ⟨-, -, hS, -, -, h3, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x ↦
    have := (C.normal x).1
    inferInstance
  have := isReduced_of_isReduced_stalk C.X
  have : IsDominant C.j := h3
  exact ext_of_isDominant C.j h

theorem extendsAut_up {C' : Cpt c' t₀' β'} {C : Cpt c t₀ β} {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r}
    (a : C'.Above C b r ν) (hD : IsDedFrac β') (e' : U' ≅ U') (n' : SABMap t₀' t₀' e'.hom) (e : U ≅ U)
    (n : SABMap t₀ t₀ e.hom) (he' : e'.hom ≫ c' = c') (hr : e'.hom ≫ r = r ≫ e.hom)
    (hν : n'.φ ≫ ν.φ = ν.φ ≫ n.φ) (hC : C.ExtendsAut e n) : C'.ExtendsAut e' n' := by
  obtain ⟨ρ, mu, h₁, h₂, h₃⟩ := hC
  obtain ⟨ni, hni, -⟩ := exists_sab_inv e' n'
  obtain ⟨mi, -, hmi⟩ := exists_sab_inv ρ mu
  have hj : r ≫ C.j ≫ ρ.hom = e'.hom ≫ r ≫ C.j := by rw [h₂, ← Category.assoc, ← hr, Category.assoc]
  have hφ : ν.φ ≫ C.m.φ ≫ mu.φ = n'.φ ≫ ν.φ ≫ C.m.φ := by rw [h₃, ← Category.assoc, ← hν, Category.assoc]
  obtain ⟨h, mu', k₁, k₂, k₃⟩ := exists_lift_end a hD e'.hom n' ρ.hom mu he' h₁ hj hφ
  obtain ⟨h', -, -, k₂', -⟩ := exists_lift_end a hD e'.inv ni ρ.inv mi (by rw [Iso.inv_comp_eq, he'])
    (by rw [Iso.inv_comp_eq, h₁])
    (by
      rw [Iso.eq_inv_comp, ← cancel_mono ρ.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hj.symm)
    (by
      calc ν.φ ≫ C.m.φ ≫ mi.φ = (ni.φ ≫ n'.φ) ≫ ν.φ ≫ C.m.φ ≫ mi.φ := by rw [hni, Category.id_comp]
        _ = ni.φ ≫ (n'.φ ≫ ν.φ ≫ C.m.φ) ≫ mi.φ := by simp only [Category.assoc]
        _ = ni.φ ≫ ν.φ ≫ C.m.φ ≫ mu.φ ≫ mi.φ := by rw [← hφ]; simp only [Category.assoc]
        _ = ni.φ ≫ ν.φ ≫ C.m.φ := by rw [hmi, Category.comp_id])
  refine ⟨⟨h, h', hom_ext_j C' hD ?_, hom_ext_j C' hD ?_⟩, mu', k₁, k₂, k₃⟩
  · rw [← Category.assoc, k₂, Category.assoc, k₂', Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [← Category.assoc, k₂', Category.assoc, k₂, Iso.inv_hom_id_assoc, Category.comp_id]

theorem extendsAut_of_isEmpty [IsEmpty U] (C : Cpt c t₀ β) (e : U ≅ U) (n : SABMap t₀ t₀ e.hom) :
    C.ExtendsAut e n := by
  obtain ⟨i, -⟩ := ObjMaps.exists_sab_id C.t
  have : IsEmpty t₀.G.left := Function.isEmpty (t₀.G.hom : t₀.G.left → U)
  exact ⟨Iso.refl _, i, Category.id_comp _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end

theorem mono_spMap {l : Level H} (hA : l.A = 1) {S : ℕ} (β : RZ H S 1 →+* KA l)
    (hβ : IsInc (RZ H S 1).subtype (KA l).val.toRingHom β) : Mono (spMap β) := by
  have : Epi (CommRingCat.ofHom β) := by
    refine ⟨fun {R} f g h => ?_⟩
    have h' : ∀ x, f.hom (β x) = g.hom (β x) := fun x => congrArg (fun k => k.hom x) h
    have hw : ∀ (x : ℂ) (hx : x ∈ RZ H S 1) (hx' : x ∈ KA l), f.hom ⟨x, hx'⟩ = g.hom ⟨x, hx'⟩ := fun x hx hx' => by
      have : β ⟨x, hx⟩ = ⟨x, hx'⟩ := Subtype.ext (hβ ⟨x, hx⟩)
      rw [← this, h']
    ext ⟨x, hx⟩
    change (⟨x, hx⟩ : KA l) ∈ RingHom.eqLocusField f.hom g.hom
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      refine hw x ?_ _
      rcases hx with rfl | rfl
      · have h2 : (1 + H.rt0) / 2 ∈ RZ H S 1 := Subring.subset_closure (Or.inl rfl)
        convert sub_mem (add_mem h2 h2) (one_mem _) using 1
        ring
      · rw [hA]
        exact Subring.subset_closure (Or.inr (Or.inr rfl))
    | algebraMap q => exact SubfieldClass.ratCast_mem (RingHom.eqLocusField f.hom g.hom) q
    | add x y hx hy ihx ihy => exact add_mem ihx ihy
    | inv x hx ih => exact inv_mem ih
    | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
  exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom β).op))

variable {D : Datum H}

section

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_zero (o : Obj D l b s) : o.eta 0 = 1 := o.eta_ker 0 (Submodule.zero_mem _)

theorem eta_nsmul (o : Obj D l b s) (n : ℕ) (a : D.La) : o.eta (n • a) = o.eta a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := by
  rw [← sub_add_cancel x y, o.eta_add, o.eta_ker _ h, _root_.one_mul]

theorem etaA_eq (o : Obj D l b s) (hA : l.A = 1) (a : D.La) : o.etaA a = o.eta 0 := by
  rw [eta_zero, ← o.etaA_ker a, hA, one_smul]

theorem mem_of_eta_eq_one [Nonempty S] (o : Obj D l b s) {a : D.La} (ha : o.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨p⟩ := ‹Nonempty S›
  let k : Type := AlgebraicClosure (S.residueField p)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) k)) ≫ S.fromSpecResidueField p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x φ.hom hφ.symm
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈
    l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  have hsub : a - e' • a = e • a := by rw [sub_eq_iff_eq_add, ← add_smul, hee, one_smul]
  have hm : a - e' • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := hsub ▸ Submodule.smul_mem_smul he Submodule.mem_top
  have h₁ := hI (e' • a) (Submodule.smul_mem_smul he' Submodule.mem_top)
  rw [← eta_congr o hm, ha, MonObj.comp_one] at h₁
  have hM : 0 < l.M := by have := l.three_le; omega
  have h₂ := SimMb.mem_of_modN D l ((I.ker l.M hM _).1 h₁.symm)
  simpa using add_mem hm h₂

end

theorem map_unique (hL : Out.Laws) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) {S : Scheme.{0}} (hS : IsReduced S)
    {t : SAB H S} {r r' : S ⟶ Xo.X} (ν : SABMap t Xo.univ.t r) (ν' : SABMap t Xo.univ.t r')
    (hs : r ≫ Xo.s = r' ≫ Xo.s)
    (h : ∀ a, ∃ y : 𝟙_ (Over S) ⟶ t.G, y.left ≫ ν.φ = r ≫ (Xo.univ.eta a).left ∧
      y.left ≫ ν'.φ = r' ≫ (Xo.univ.eta a).left) : r = r' ∧ ν.φ = ν'.φ := by
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by rw [spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := LevUniq.exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := LevUniq.exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    obtain ⟨y, hy, hy'⟩ := h a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans hy.symm), hy']
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [etaA_eq _ hA, etaA_eq _ hA, e₁]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l (KA l) (KA l) (baseKA l) (baseKA l) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

theorem isReduced_X {l : Level H} (Xo : Moduli D l) : IsReduced Xo.X :=
  have := Xo.smooth
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1

theorem isReduced_XF {l : Level H} (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1

theorem exists_end (hD : 1 ≤ D.p + D.q) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (ω : Sim D) :
    ∃ (f : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t f), f ≫ Xo.s = Xo.s ∧
      ∀ a, (Xo.univ.eta (ω.f l.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left := by
  obtain ⟨f, hf, ⟨m⟩⟩ := (Xo.rep Xo.X Xo.s (isReduced_X Xo) (LevelTwist.objTwist Xo.univ ω
    ((SimAlg.sim_group E H D hD).1 ω) (by rw [hA]; exact one_dvd _))).exists
  exact ⟨f, m.toSABMap, hf, m.eta⟩

theorem comp_eq_id (hL : Out.Laws) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) {g g' : D.La → D.La}
    {f f' : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t f) (ν' : SABMap Xo.univ.t Xo.univ.t f')
    (hf : f ≫ Xo.s = Xo.s) (hf' : f' ≫ Xo.s = Xo.s)
    (h : ∀ a, (Xo.univ.eta (g a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left)
    (h' : ∀ a, (Xo.univ.eta (g' a)).left ≫ ν'.φ = f' ≫ (Xo.univ.eta a).left)
    (hg : ∀ a, D.ModN l.M (g (g' a) - a)) : f ≫ f' = 𝟙 _ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp ν' ν
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id Xo.univ.t
  refine (map_unique hL hA Xo (isReduced_X Xo) n i (by rw [Category.assoc, hf', hf, Category.id_comp])
    fun a => ⟨Xo.univ.eta a, ?_, by rw [hi, Category.comp_id, Category.id_comp]⟩).1
  conv_lhs => rw [← eta_congr _ (SimMb.mem_of_modN D l (hg a))]
  rw [hn, ← Category.assoc, h, Category.assoc, h', Category.assoc]

theorem exists_aut (hL : Out.Laws) (hD : 1 ≤ D.p + D.q) {l : Level H} (hA : l.A = 1) (Xo : Moduli D l)
    (g : D.La →ₗ[𝓞 E] D.La)
    (hg : ∀ x, g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ (e : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t e.hom), e.hom ≫ Xo.s = Xo.s ∧
      ∀ a, (Xo.univ.eta (g a)).left ≫ ν.φ = e.hom ≫ (Xo.univ.eta a).left := by
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨ω, hω, -⟩ := exists_sim_of_aut_mod E H D l 1 g hD one_pos (Nat.coprime_one_left _) hg
  obtain ⟨ω', hω'⟩ := (SimAlg.sim_group E H D hD).2.2.2 ω
  obtain ⟨f, ν, hf, h⟩ := exists_end hD hA Xo ω
  obtain ⟨f', ν', hf', h'⟩ := exists_end hD hA Xo ω'
  refine ⟨⟨f, f', comp_eq_id hL hA Xo ν ν' hf hf' h h' fun a => ((hω' _ hM).1 a).2,
    comp_eq_id hL hA Xo ν' ν hf' hf h' h fun a => ((hω' _ hM).1 a).1⟩, ν, hf, fun a => ?_⟩
  rw [← eta_congr _ (hω a)]
  exact h a

theorem levelActs_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), l₀.Dvd l → IsDedFrac β → Raises B Y → Y.LevelActs := by
  intro hL _ _ E _ _ _ H D Xo n N T hD l₀ B l c O _ β Y hl hβ hR r ν gM gA hr hM _
  obtain ⟨b, r', ν', -, hlev, ⟨a⟩⟩ := hR
  change (ofModel Y).ExtendsAut r ν
  rcases isEmpty_or_nonempty ((Xo l).XF c) with _ | _
  · exact extendsAut_of_isEmpty _ r ν
  have hinj : ∀ x, gM x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro x hx
    refine mem_of_eta_eq_one Y.oF (Over.OverMorphism.ext ?_)
    rw [← cancel_epi r.hom, ← hM x, ← eta_zero Y.oF, ← hM 0, map_zero, eta_zero, Y.oF.eta_ker _ hx]
  obtain ⟨h, hh⟩ := SimMb.exists_left_inv D l gM hinj
  have hinj₀ : ∀ x, gM x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) → x ∈ l₀.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro x hx
    simpa using sub_mem (LevelTwist.map_mem_smul_top h _ hx) (Submodule.smul_mono hl.2.1 le_rfl (hh x))
  obtain ⟨e, ν₀, he, hν₀⟩ := exists_aut hL hD B.A_one (Xo l₀) gM hinj₀
  obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp ν' ν
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν₀ ν'
  have hs : (r.hom ≫ r') ≫ (Xo l₀).s = (r' ≫ e.hom) ≫ (Xo l₀).s := by
    have := mono_spMap B.A_one B.β B.β_inc
    have h₁ : (r' ≫ (Xo l₀).s) ≫ spMap B.β = pullback.snd _ _ ≫ spMap β ≫ spMap b := by
      rw [Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, ← Category.assoc, ← a.j_comm, Category.assoc, a.π_over,
        ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc]
    rw [Category.assoc, Category.assoc, he, ← cancel_mono (spMap B.β), Category.assoc, h₁, ← Category.assoc, hr]
  obtain ⟨k₁, k₂⟩ := map_unique hL B.A_one (Xo l₀) (isReduced_XF _ c) n₁ n₂ hs fun x =>
    ⟨Y.oF.eta (gM x) ^ (l.M / l₀.M), by
      rw [hn₁, ← Category.assoc, ← eta_nsmul, ← map_nsmul, hM, eta_nsmul, Category.assoc, hlev.1, Category.assoc],
      by rw [hn₂, ← Category.assoc, hlev.1, Category.assoc, hν₀, Category.assoc]⟩
  exact extendsAut_up a hβ r ν e ν₀ hr k₁ (hn₁.symm.trans (k₂.trans hn₂)) (B.acts e ν₀ gM he hν₀)

end GlobalTheory.LevActs
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAut_acts_on_raised_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), l₀.Dvd l → IsDedFrac β → Raises B Y → Y.LevelActs := by
  atlas_forward_decl GlobalTheory.LevActs.levelActs_of_raises
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem System.levelStructureConditions_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hpq hlev S p W hp hW i
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW i
  have hdvd : l₀.Dvd i.l := ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 i.l l₀ h).1
  obtain ⟨hded, hunit, -⟩ := (GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW
  have hgood : Good (S.Y p W hp hW i).t := by
    obtain ⟨b, r, ν, -, -, ⟨A⟩⟩ := hR
    exact good_pullback L3.gtBaseChange E H _ _ _ _ A.π A.mu (S.B (S.ch p) l₀ h.1).good
  refine ⟨⟨?_, fun hA => ?_, ?_, ?_, ?_, ?_⟩, hgood.2.1⟩
  · exact GlobalTheory.T.levelAut_acts_on_raised_model L1 L2 L3 E H D Xo _ _ _ hpq l₀ _ i.l i.c _ _ _ hdvd hded hR
  · exact GlobalTheory.T.raised_model_level_one_descends L1 L2 L3 E H D Xo _ _ _ hlev l₀ _ i.l i.c _ _ _ (S.aux _).1.pos hdvd hA hded hR
  · exact GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D i.l _ _ _ _ _ _ (S.Y p W hp hW i).oF _ _ (ofModel (S.Y p W hp hW i)) hded
      hgood.2.2
  · obtain ⟨U, hU, hσ⟩ := GlobalTheory.torsion_section_extends_abLocus E H D i.l _ i.c _ _ (S.Y p W hp hW i) hded hgood.1
    exact ⟨U, hU, fun a n hn => ⟨hσ _ n (hunit n hn), hσ _ n (hunit n hn)⟩⟩
  · intro V K _ _ _ _ _ _ _
    exact GlobalTheory.goodRedExt_of_isDiscreteValuationRing hext E H D i.l _ i.c _ _ _ V K
  · intro V C _ _ _ _ _ _ _ hV _
    exact GlobalTheory.GoodRedUnitBall.goodRedExt_unitBall hext E H D Xo _ _ _ l₀ _ i.l i.c _ _ _ hR V C hV

end GlobalTheory.Models
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModel_oneModel_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  atlas_forward_decl GlobalTheory.Models.System.levelStructureConditions_and_splitFibres
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section Incl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H} {c : Coeff l}
  {c₂ : Coeff l₂} {W : ValuationSubring ℂ}

theorem exists_isIncl (hc : c.F ≤ c₂.F) : ∃ b : c.V W →+* c₂.V W, IsIncl b := by
  refine ⟨RingHom.codRestrict ((IntermediateField.inclusion hc).toRingHom.comp (c.V W).subtype) (c₂.V W)
    (fun x => x.2), fun x => rfl⟩

theorem isIncl_unique {b b' : c.V W →+* c₂.V W} (hb : IsIncl b) (hb' : IsIncl b') : b = b' := by
  refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact (hb x).trans (hb' x).symm

end Incl

theorem system_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN S p W hp hW
  refine ⟨fun i => (GlobalTheory.T.localModel_oneModel_and_splitFibres hext L1 L2 L3 E H D Xo hD hN S p W hp hW i).1, ?_⟩
  obtain ⟨hnp, hodd, h3, h4⟩ := S.aux (S.ch p)
  have hcop := (GlobalTheory.T.exists_two_inert_odd_primes_coprime_level E H).2 _ (S.aux (S.ch p))
  obtain ⟨-, hl2, hl3⟩ := GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp
  have key : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F →
      ∃ π : (S.Y p W hp hW i₂).X ⟶ (S.Y p W hp hW i).X, ∀ b : i.c.V W →+* i₂.c.V W, IsIncl b →
        IsTransition (S.Y p W hp hW i) (S.Y p W hp hW i₂) b π := by
    intro i i₂ hl hc
    obtain ⟨b, hb⟩ := exists_isIncl (W := W) hc
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₂
    obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models hext L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
      (S.Y p W hp hW i) i₂.l i₂.c _ _ (S.Y p W hp hW i₂) b hnp.pos ⟨_, dvd_rfl⟩ (hl3 _ _ _ _ h₀ h₀' hl)
      (hl2 _ _ h₀).1 (hl2 _ _ h₀').1 hl hc ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW).1
      ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i₂.l i₂.c).2.2.2 p W hp hW).1 hb hr hr'
    exact ⟨π, fun b' hb' => isIncl_unique hb hb' ▸ hπ⟩
  choose π hπ using key
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.cm_models_siegel_family_comparison L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN p hp (S.ch_ne p).symm hnp ⟨_, rfl⟩
  refine ⟨π, hπ, S.n (S.ch p), S.J (S.ch p), Ag, hnp, hodd, S.ch_ne p, ?_, hcop, ?_⟩
  · have h2 : 3 ≤ S.n (S.ch p) := by
      have := hnp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h2.trans (Nat.le_self_pow (by have := S.J_pos (S.ch p); omega) _)
  · intro i i₁ hl hc b z hb hz hM hMb hA hF
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₁
    have h₁ : IsPrimeToPart l₀' i.l p := by
      obtain ⟨a1, a2, a3⟩ := h₀'
      exact ⟨a1, hM ▸ a2, hMb ▸ a3⟩
    obtain rfl : l₀' = l₀ := (hl2 _ _ h₀).2.2 _ h₁
    exact hAg W l₀' _ i.l i₁.l i.c i₁.c _ _ b z _ hW h₀ (hcop _) hb hz hM hMb hA hF hr hr' (hπ i i₁ hl hc b hb)

end GlobalTheory.Models
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localModelSystem_transition_siegel_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  atlas_forward_decl GlobalTheory.Models.system_clauses
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

theorem exists_localSystems_ample :
    GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  intro hext hL hL2 hL3 htop hN1 E _ _ _ H D hpq Xo
  obtain ⟨-, hN⟩ := hN1
  have hlev : ToroidalLevelCompatibility (H := H) (D := D) := (hN E H D hpq).1

  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel hext hL hL2 hL3 htop E H D Xo hpq hlev
  refine ⟨S.Y, fun p W hp hW => ⟨GlobalTheory.T.localModelSystem_transition_siegel_clauses hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW, fun i => ?_⟩,
    GlobalTheory.T.exists_global_model_of_local_models hext hL hL2 hL3 E H D Xo hpq hlev S⟩
  refine ⟨(GlobalTheory.T.localModel_oneModel_and_splitFibres hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW i).2, ?_⟩

  obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
  obtain ⟨k, hk⟩ := hS (S.ch p)
  have hc := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
  have hcop : (S.n (S.ch p)).Coprime p := (Nat.coprime_primes (S.aux _).1 hp).2 (S.ch_ne p)
  exact GlobalTheory.T.raised_model_finite_cover_ample_frames hL hL2 hL3 E H D Xo (S.n (S.ch p)) (S.n (S.ch p) ^ S.J (S.ch p)) k (S.T (S.ch p)) hlev
    l₀ i.l (S.B (S.ch p) l₀ h₀.1) i.c _ (i.c.V W).subtype (S.Y p W hp hW i) (S.aux _).1 (S.aux _).2.1
    ⟨_, rfl⟩ (hc.2.1 _ hcop) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 i.l l₀ h₀).1 hc.1 hr hk

end GlobalTheory.Models
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystems_ampleFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  atlas_forward_decl GlobalTheory.Models.exists_localSystems_ample
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem modelsSt_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ModelsSt :=
  fun S => GlobalTheory.T.exists_localModelSystems_ampleFrames GlobalTheory.homExtension_semiAbelian_dvr GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction S) GlobalTheory.T.moduliScheme_levelMaps_heckePoints'

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e → k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (j : o →+* ZP p k), ArBase em ∧ j (b.ζ : o) = zetaZP p k ∧ (∀ x, ((j x : ZP p k) : ℂ) = em x) ∧ ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y := by
  first | exact @GlobalTheory.ZM.CycBase.exists_base | exact GlobalTheory.ZM.CycBase.exists_base | (intros; apply GlobalTheory.ZM.CycBase.exists_base <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelFromSharp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

def restrictBase {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} (j : B →+* B') (hj : j ζ = ζ')
    {S : Scheme.{0}} {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) where
  A := c.A
  ab := c.ab
  P := c.P
  isLB := c.isLB
  rig₁ := c.rig₁
  rig₂ := c.rig₂
  symm := c.symm
  lev := c.lev
  lev_add := c.lev_add
  lev_tors := c.lev_tors
  geom := by
    intro K _ _ x β z hx hz
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s')
    refine c.geom K x φ.hom z hφ.symm ?_
    have : spMap (φ.hom.comp j) = spMap β := by
      rw [← spMap_comp, ← hx, ← Category.assoc, ← hφ]; rfl
    have e : φ.hom.comp j = β := congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    rw [hz, ← e, ← hj]; rfl

theorem finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem dirMap_base {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  simp only [constPt, Category.assoc, spMap_comp]
  congr 1
  ext x <;> simp [dirMap]

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (f : X ⟶ Y) :
    constPt x ≫ f = constPt (x ≫ f) := by
  simp only [constPt, Category.assoc]

theorem nonempty_siegelFamily (L1 : Out.Laws) (L2 : Out.Laws2)
    (L3 : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {h g p n N' : ℕ} (hh : 1 ≤ h) (hp : p.Prime) {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} [Finite J]
    {a : J → Matrix (Fin 8) (Fin 8) ℤ} {w w' : J}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) (hbas : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hu : ∀ u v, ∃ j, a j = Matrix.single u v 1) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (h3 : 3 ≤ N') (hodd : Odd N') {o : Type} [CommRing o] {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    (j : o →+* ZP p (N' ^ 2)) (har : ArBase em) (hj : j (b.ζ : o) = zetaZP p (N' ^ 2))
    (hconst : ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p (N' ^ 2))), y = constPt y)
    (good : GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2))
    (F : WFam n em (SharpClass (b := b) W a bas em) Mat κ)
    (rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S →
      Dense (fromSet em (SharpClass (b := b) W a bas em) t) → t.FibShape Mat κ →
      ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f) :
    Nonempty (SiegelFamily h p (N' ^ 2)) := by
  have hk : Odd (N' ^ 2) := hodd.pow
  have hk3 : 3 ≤ N' ^ 2 := by nlinarith
  have hζ : b.ζ ^ N' ^ 2 = 1 := by
    refine Units.ext (har.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  haveI : IsDedekindDomain o := har.1
  haveI : CharZero o := RingHom.charZero em
  obtain ⟨hq, hflat, hred, htan⟩ := GlobalTheory.T.thetaClosureOpenFamily_qproj_flat_reduced_ext L1 L2 o g n N' J b em _ Mat κ F hodd
  obtain ⟨hqc, hft⟩ := finiteType_of_isQProjOver (hq.resolve_right (not_not.2 inferInstance))
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsharp⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 L3 h g W J a bas hW hbas hu _ o b em _ _ F.univ hk F.dense

  have pull : ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (c' : SiegPre h (N' ^ 2) (b.ζ : o) s) (t : TObj g (N' ^ 2) J b s)
      (f : S ⟶ F.U.toScheme), c'.Principal → IsSharp W a bas t c' → (SiegPB c' c f ↔ TMap t F.univ f) := by
    intro S s c' t f h1 h2
    have := GlobalTheory.T.siegelPullback_iff_eighthPower_pullback L1 L2 h g W J a bas hW hbas _ o b _ _ _ _ c c' F.univ t f hc h1 hsharp h2
    exact ⟨this.1, this.2 hu⟩
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (F.U.ι ≫ F.Y.s) := by
    refine GlobalTheory.T.smoothOfRelativeDimension_of_flat_dedekind_tangent_le o _ _ _ har.2.1 hflat hft
      (GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre L1 L2 g n N' J Mat κ w w' o b em _ _ F h3 hodd har good) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨p1, p2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ _ _
      (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β)) x rfl (by rw [spMap_id, Category.comp_id, hx])
    obtain ⟨c', hc'⟩ := p1 c
    have hp' := p2 c c' hc' hc
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ c' hk hk3 hζ hp'
    have hm : TMap t' F.univ x := (pull _ _ c' t' x hp' ht').1 hc'
    refine GlobalTheory.T.siegelFamily_tangent_dimension_bound L1 L2 L3 h g W J a bas hW hbas w w' hw hw' _ o b K r β t' c' hp' ht' ?_
    intro lam t'' m1 m2
    refine hlam lam ?_
    rw [← constPt_comp]
    refine htan (DualNumber K) _ _ _ t'' ?_ (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m1)
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m2)
    rw [Category.assoc, Category.assoc, hx]
    exact dirMap_base β lam
  obtain ⟨q1, q2, -⟩ := GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) o _ (b.ζ : o) _ j _ _ (F.U.ι ≫ F.Y.s)
    (pullback.snd (F.U.ι ≫ F.Y.s) (spMap j)) (pullback.fst _ _) hj pullback.condition
  obtain ⟨u, hupb⟩ := q1 c
  have hup := q2 c u hupb hc
  refine ⟨⟨pullback (F.U.ι ≫ F.Y.s) (spMap j), pullback.snd _ _,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm, inferInstance, u, hup, ?_, ?_⟩⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpC β c₁ hgen hamp
    have hp₁ : c₁.Principal := GlobalTheory.T.principal_siegel_of_generic_principal_special_ample L1 L2 h _ hk hk3 _ _ C O hO p hp hpC β c₁ hgen hamp
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have hfrom := GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h g W J a w w' bas hW hbas hw hw' hu N' o b em har _ _ t _ hp₀ ht C
      (spMap (algebraMap O C))
    haveI : IsDomain O := hO.1.isDomain _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) := by
      have hd : DenseRange (PrimeSpectrum.comap (algebraMap O C)) := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 hO.1]
        exact bot_le
      exact Dense.mono (fun z hz => ⟨C, inferInstance, _, hz, hfrom⟩) hd
    have hshape : t.Shape Mat κ := by
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom
      have hs := (good.shape tc htc).1
      obtain ⟨cc, hcc, hcs⟩ := htc
      exact GlobalTheory.T.eighthPower_shape_depends_only_on_matrices L1 L2 h g W J a bas hW hbas _ o b Mat κ _ _ _ _ cc _ tc t hh inferInstance hcc hp₀ hcs ht hs
    obtain ⟨f, ⟨hf, hm⟩, -⟩ := rep _ _ t inferInstance hdense fun K _ _ x t' hx =>
      (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ x t t' hx).1 hshape
    have hpb : SiegPB c₁ c f := (pull _ _ (restrictBase j hj c₁) t f hp₀ ht).2 hm
    refine ⟨pullback.lift f (spMap β) hf, pullback.lift_snd _ _ _, ?_⟩
    refine ((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).2 ?_
    rwa [pullback.lift_fst]
  · intro K _ x c₁ m1 m2
    have hp₁ : c₁.Principal := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h (N' ^ 2) _ _ _ _ (RingHom.id _) _ _ _ _ x rfl
      (by rw [spMap_id, Category.comp_id])).2.1 u c₁ m1 hup
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have n1 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m1)
    have n2 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((GlobalTheory.T.siegelPullback_id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m2)
    have e : x ≫ pullback.snd _ _ = constPt x ≫ pullback.snd _ _ := by
      rw [constPt_comp]; exact hconst K _
    refine pullback.hom_ext (htan (DualNumber K) _ _ _ t ?_ n1 n2) e
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, e, Category.assoc]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  intro L1 L2 L3 L4 h p n hh hp hn hodd hnp
  obtain ⟨W, hW, hb⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hb h
  have hinv : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)
  let a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ :=
    Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
      (fun e => (W + W.transpose)⁻¹ * (if e then W else W.transpose))
  have hw : (W + W.transpose) * a (.inr true) = W := by
    change _ * (_ * W) = W
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hw' : (W + W.transpose) * a (.inr false) = W.transpose := by
    change _ * (_ * W.transpose) = W.transpose
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hu : ∀ u v, ∃ j, a j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 L3 L4 h _ W _ a _ _ bas hW hbas hw hw' hu
  obtain ⟨j₁, h₁⟩ := hcl n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.nonempty_thetaFamily_over_open_closure L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨j₃, h₃⟩ := GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨m, hm⟩ : ∃ m, m = j₁ + j₂ + j₃ + 1 := ⟨_, rfl⟩
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨e, he⟩ := hodd
    omega
  have h3 : 3 ≤ n ^ m := hn3.trans (Nat.le_self_pow (by omega) n)
  obtain ⟨o, _, b, em, j, har, hj, -, hconst⟩ :=
    GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime n (m * 2) p ((n ^ m) ^ 2) hn hp hnp (by omega) (pow_mul n m 2).symm
  have good := h₁ m (by omega) _ rfl o b em
  obtain ⟨F⟩ := h₂ m (by omega) o b em _ _ har good
  refine ⟨m * 2, hn3.trans (Nat.le_self_pow (by omega) n), ?_⟩
  rw [pow_mul]
  exact nonempty_siegelFamily L1 L2 L3 hh hp hW hbas hw hw' hu h3 hodd.pow j har hj hconst good F
    (h₃ m (by omega) o b em _ _ har good F)

end GlobalTheory.SiegelFromSharp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelFamily_localisation_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  atlas_forward_decl GlobalTheory.SiegelFromSharp.exists_siegelFamily
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem siegelFamilies_closed : N0 :=
  GlobalTheory.T.exists_siegelFamily_localisation_prime_power_level GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory.Moduli
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamilies_exist : N0 := by
  atlas_forward_decl GlobalTheory.Moduli.siegelFamilies_closed
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem partI_of_semistableReduction_of_arcFam :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ArcFamSt → PartI :=
  fun S A => by
    obtain ⟨L, L2, L3, L4, L5, L6⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
    exact GlobalTheory.T.modelSystems_jointProperties_of_laws GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange L L2 L3 L4 L5 L6 GlobalTheory.LN.ega_holds
      GlobalTheory.uniformisation_dvr_unconditional GlobalTheory.T.linearUniformisation_triples_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing A
      (GlobalTheory.modelsSt_of_semistableReduction S) GlobalTheory.T.siegelFamilies_exist

end GlobalTheory
end
