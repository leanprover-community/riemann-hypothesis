import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPoleOfBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalAtOfUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendOfIntegralAtDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitCoefOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroClo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ValLocal

theorem exists_dvd_away {A : Type} [CommRing A] [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (a b : A) (hb : b ≠ 0) :
    ∃ s r : A, s ∉ q ∧ (s * a = r * b ∨ s * b = r * a) := by
  by_cases hq : q = ⊥
  · exact ⟨b, a, by simpa [hq] using hb, Or.inl (mul_comm _ _)⟩
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have key : ∀ (u v : A) (z : Localization.AtPrime q), algebraMap A _ u * z = algebraMap A _ v →
      ∃ s r : A, s ∉ q ∧ s * v = r * u := by
    intro u v z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl z
    refine ⟨s, r, s.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hrs]
    ring
  obtain ⟨z, hz | hz⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) a) (algebraMap A _ b)
  · obtain ⟨s, r, hs, h⟩ := key a b z hz
    exact ⟨s, r, hs, Or.inr h⟩
  · obtain ⟨s, r, hs, h⟩ := key b a z hz
    exact ⟨s, r, hs, Or.inl h⟩

theorem exists_integral_frac {F : Type} [Field F] [NumberField F] (W : ValuationSubring F) (x : W) :
    ∃ a s : W, IsIntegral ℤ (a : F) ∧ IsIntegral ℤ (s : F) ∧ IsUnit s ∧ x * s = a := by
  have hmem : ∀ y : 𝓞 F, (y : F) ∈ W := fun y => by
    have h : IsIntegral W (y : F) := y.isIntegral_coe.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
    rw [← hz]
    exact z.2
  let φ : 𝓞 F →+* W := (algebraMap (𝓞 F) F).codRestrict W.toSubring hmem
  have hφ : ∀ y : 𝓞 F, ((φ y : W) : F) = (y : F) := fun _ => rfl
  let q : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal W).comap φ
  have hunit : ∀ s : 𝓞 F, s ∉ q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb0
  have hxb : (x : F) * b = a := by
    rw [← hx]
    exact div_mul_cancel₀ _ hbF
  obtain ⟨s, r, hs, h | h⟩ := exists_dvd_away q a b hb0
  · refine ⟨φ r, φ s, r.isIntegral_coe, s.isIntegral_coe, hunit s hs, Subtype.ext ?_⟩
    have h' : (s : F) * a = r * b := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    show (x : F) * s = r
    apply mul_right_cancel₀ hbF
    rw [← h', ← hxb]
    ring
  · have h' : (s : F) * b = r * a := by exact_mod_cast congrArg (fun y : 𝓞 F => (y : F)) h
    have hxr : x * φ r = φ s := by
      apply Subtype.ext
      show (x : F) * r = s
      apply mul_right_cancel₀ hbF
      rw [h', ← hxb]
      ring
    exact ⟨φ s, φ r, s.isIntegral_coe, r.isIntegral_coe,
      isUnit_of_mul_isUnit_right (hxr ▸ hunit s hs), hxr⟩

theorem preimmersion_flat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  intro E _ _ _ H l c O _ β hβ W b hb
  haveI := c.fin
  haveI : NumberField c.F := {}
  letI : Algebra O W := b.toAlgebra
  have hbv : ∀ o : O, ((b o : W) : c.F) = β o := fun o => by rw [← hb]; rfl
  have hinj : Function.Injective b := fun u v h => hβ.1 (by rw [← hbv, ← hbv, h])
  let S : Submonoid O := (IsUnit.submonoid W).comap b
  haveI : IsLocalization S W := by
    refine (isLocalization_iff S W).2 ⟨fun y => y.2, fun z => ?_, fun {u v} h => ⟨1, by rw [hinj h]⟩⟩
    obtain ⟨a, s, ha, hs, hu, hz⟩ := exists_integral_frac W z
    obtain ⟨a', ha'⟩ := hβ.2 _ ha
    obtain ⟨s', hs'⟩ := hβ.2 _ hs
    have e1 : b a' = a := Subtype.ext (by rw [hbv, ha'])
    have e2 : b s' = s := Subtype.ext (by rw [hbv, hs'])
    refine ⟨⟨a', ⟨s', ?_⟩⟩, ?_⟩
    · show IsUnit (b s')
      rwa [e2]
    · show z * b s' = b a'
      rw [e1, e2, hz]
  refine ⟨IsPreimmersion.of_isLocalization (R := O) (S := W) S, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact (RingHom.flat_algebraMap_iff (R := O) (S := W)).2 (IsLocalization.flat W S)

end GlobalTheory.ValLocal
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  atlas_forward_decl GlobalTheory.ValLocal.preimmersion_flat
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_subring_dedekind_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  first | exact @GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | exact GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | (intros; apply GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

noncomputable section

namespace GlobalTheory.LocArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

@[reducible] def arcRestrict (b : O →+* O') (hb : β'.comp b = β) {O'' : Type} [CommRing O''] [IsDomain O'']
    {b' : O' →+* O''} (a : ArcIn D l β' O'' b') : ArcIn D l β O'' (b'.comp b) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom := fun F _ _ _ r z hr hz => a.geom F (b r) (b z) (by rw [← hb] at hr; exact hr) (by rw [← hb] at hz; exact hz)

variable (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)]

theorem mono_locMap : Mono (locMap Y b).φ :=
  (MorphismProperty.monomorphisms Scheme.{0}).of_isPullback (locMap Y b).cart.1.flip
    (show Mono (pullback.fst Y.s (spMap b)) from inferInstance)

theorem hasArcData_iff {O'' R : Type} [CommRing O''] [IsDomain O''] [CommRing R] [IsDomain R] {b' : O' →+* O''}
    (a : ArcIn D l β' O'' b') (I : Ideal R) (f : O'' →+* R) (u : R) (χ : Sp R ⟶ (locModel Y b hb).X) :
    (locModel Y b hb).HasArcData a I f u χ ↔
      Y.HasArcData (arcRestrict b hb a) I f u (χ ≫ pullback.fst Y.s (spMap b)) := by
  have ej := locModel_j Y b hb
  have em := locModel_m Y b hb
  constructor
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, ej, hy]
      simp only [Category.assoc]
    · have := mono_locMap Y b
      rw [← cancel_mono (locMap Y b).φ]
      rw [hn, ← em] at k₄
      simp only [Category.assoc]
      exact k₄
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_cancel (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← ej, ← Category.assoc, hy]
      simp only [Category.assoc]
    · have := congrArg (· ≫ (locMap Y b).φ) k₄
      simp only [Category.assoc] at this
      rw [hn, ← em]
      exact this

theorem mem_range_j_iff (x : (locModel Y b hb).X) :
    x ∈ Set.range (locModel Y b hb).j ↔ pullback.fst Y.s (spMap b) x ∈ Set.range Y.j := by
  rw [← locModel_j Y b hb]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (pullback.fst Y.s (spMap b)).isEmbedding.injective ?_⟩
    rw [← hu, Scheme.Hom.comp_apply]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem locModel_arc (h : Y.N4) : (locModel Y b hb).N4 := by
  intro O'' _ _ _ b' ϖ a hO
  obtain ⟨χ₀, hu, hs⟩ := h O'' (b'.comp b) ϖ (arcRestrict b hb a) hO
  obtain ⟨c₁, c₂, c₃, c₄⟩ := (hu χ₀).1 rfl
  have hw : χ₀ ≫ Y.s = (spMap (PowerSeries.C (R := O'')) ≫ spMap b') ≫ spMap b := by
    rw [c₁, spMap_comp', Category.assoc]
  have hχ : pullback.lift χ₀ _ hw ≫ pullback.fst Y.s (spMap b) = χ₀ := pullback.lift_fst _ _ _
  refine ⟨pullback.lift χ₀ _ hw, fun χ' => ⟨?_, ?_⟩, fun hi y' ev d₁ d₂ d₃ d₄ d₅ => ?_⟩
  · rintro rfl
    refine ⟨pullback.lift_snd _ _ _, fun x => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_abLocus_locModel, ← Scheme.Hom.comp_apply, hχ]
      exact c₂ x
    · rw [mem_range_j_iff, ← Scheme.Hom.comp_apply, hχ]
      exact c₃ x hx
    · rw [hasArcData_iff, hχ]
      exact c₄
  · rintro ⟨d₁, d₂, d₃, d₄⟩
    rw [← cancel_mono (pullback.fst Y.s (spMap b)), hχ]
    refine (hu _).2 ⟨?_, fun x => ?_, fun x hx => ?_, (hasArcData_iff Y b hb a _ _ _ _).1 d₄⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp', ← Category.assoc]
      exact congrArg (· ≫ spMap b) d₁
    · rw [Scheme.Hom.comp_apply, ← mem_abLocus_locModel Y b hb]
      exact d₂ x
    · rw [Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₃ x hx
  · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, hχ]
    refine hs hi _ ev ?_ ?_ ((hasArcData_iff Y b hb a _ _ _ _).1 d₃) d₄ d₅
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp']
      exact congrArg (· ≫ spMap b) d₁
    · rintro _ ⟨q, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₂ ⟨q, rfl⟩

end GlobalTheory.LocArc

theorem GlobalTheory.LocArc.arc_localise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ b hb _ _ h => GlobalTheory.LocArc.locModel_arc Y b hb h
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcProperty_localisationBaseChange_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 := by
  atlas_forward_decl GlobalTheory.LocArc.arc_localise
end

section
section
noncomputable section

namespace GlobalTheory.KeyUnitModels.SplitLoc

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped CategoryTheory.Obj

theorem isIso_residueFieldMap {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] (z : Z) :
    IsIso (i.residueFieldMap z) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, fun u => ?_⟩
  obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
  obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
  exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩

theorem split_of_pullback {Z X : Scheme.{0}} (i : Z ⟶ X) [SurjectiveOnStalks i] {G : Over X} {G' : Over Z} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G i φ) (z : Z)
    (h : ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField (i z)) k),
      FiniteDimensional (X.residueField (i z)) k ∧ Algebra.IsSeparable (X.residueField (i z)) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z))).obj G)) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField z) k),
      FiniteDimensional (Z.residueField z) k ∧ Algebra.IsSeparable (Z.residueField z) k ∧
      ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z)).obj G') := by
  obtain ⟨k, _, _, hfin, hsep, S, hS⟩ := h
  have := isIso_residueFieldMap i z
  let e : X.residueField (i z) ≃+* Z.residueField z := (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv
  let _ : Algebra (Z.residueField z) k := ((algebraMap (X.residueField (i z)) k).comp e.symm.toRingHom).toAlgebra
  have he : (algebraMap (Z.residueField z) k).comp (e : _ →+* _) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (X.residueField (i z)) k) :=
    RingHom.ext fun a => congrArg (algebraMap (X.residueField (i z)) k) (e.symm_apply_apply a)
  refine ⟨k, inferInstance, inferInstance, Module.Finite.of_equiv_equiv e (RingEquiv.refl k) he,
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl k) he, S, ?_⟩
  have hc : i.residueFieldMap z ≫ CommRingCat.ofHom (algebraMap (Z.residueField z) k) =
      CommRingCat.ofHom (algebraMap (X.residueField (i z)) k) := CommRingCat.hom_ext he
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) k)) ≫ Z.fromSpecResidueField z) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (i z)) k)) ≫ X.fromSpecResidueField (i z) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.fromSpecResidueField (i z)) (Spec.map_comp _ _).symm)
  obtain ⟨j, hj, -⟩ := grpPullback_iso (isGrpPullback_pullback G _)
    (((isGrpPullback_pullback G' _).comp hφ).congr key rfl)
  exact isGt_of_iso j hS

theorem locModel_splitFibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)]
    [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' b hb _ _ h x
  exact split_of_pullback (pullback.fst Y.s (spMap b)) (locMap Y b).cart x (h _)

end GlobalTheory.KeyUnitModels.SplitLoc
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFibres_localisedModel_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.SplitFibres → (locModel Y b hb).SplitFibres := by
  atlas_forward_decl GlobalTheory.KeyUnitModels.SplitLoc.locModel_splitFibres
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpenModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem charZero_of_range [IsOpenImmersion Y.j] {R : Type} [CommRing R] [Nontrivial R] (z : Sp R ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : CharZero R :=
  charZero_of_injective_ringHom (Spec.preimage (IsOpenImmersion.lift Y.j z h ≫ pullback.snd _ _)).hom.injective

theorem exists_keyAt_of_range [IsOpenImmersion Y.j] (hpq : 1 ≤ D.p + D.q) (M : GChart Y) {R : Type} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (h : Set.range z ⊆ Set.range Y.j) :
    ∃ x : KeyIn R, KeyAt M z hz x := by
  obtain ⟨t, ⟨m⟩⟩ := exists_sab z Y.t
  have e : IsOpenImmersion.lift Y.j z h ≫ Y.j = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t Y.j (IsOpenImmersion.lift Y.j z h) Y.m (e.symm ▸ m)
  have hp₀ := Y.oF.proper
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp₀
  have hA : Out.RelAmple t.G t.PP.L := by
    have h₁ := AmpleBaseChange.relAmple_of_isPullback Y.oF.t.PP.isLB Y.oF.ample m'.cart.1
    refine (GlobalTheory.KeyAtFam.relAmple_iff_of_cls (pull_isLB Y.oF.t.PP.isLB m'.φ) t.PP.isLB le_rfl ?_).2 h₁
    rw [one_smul]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m')
  have := charZero_of_range z h
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h₂ := IsTotallyComplex.finrank E
    exact Nat.mul_pos (by omega) hpq
  obtain ⟨x₀, -, h₀⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (spMap (algebraMap R (FractionRing R)) ≫ z)
    (le_preimage_comp _ hz) (by
      rintro _ ⟨s, rfl⟩
      exact h ⟨_, rfl⟩) hpos
  obtain ⟨x, -, hx⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hz m hp hA _ h₀
  exact ⟨x, hx⟩

theorem exists_unit_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y hO hj hpq κ hκ M
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : IsReduced Y.X := by
    have (x : Y.X) : _root_.IsReduced (Y.X.presheaf.stalk x) := by
      have := GlobalTheory.IsNormalScheme.isDomain_stalk x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  let W₀ : Y.X.Opens := M.U ⊓ Y.j.opensRange
  have hW₀ : ∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j := fun x => Iff.rfl
  have hr : ∀ {R : Type} [CommRing R] (z : Sp R ⟶ Y.X), ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := by
    rintro R _ z hz _ ⟨s, rfl⟩
    exact ((hW₀ _).1 (hz (Set.mem_univ s))).2
  let P : Y.X.Opens → Prop := fun W => IsDomain Γ(Y.X, W)
  have hP : ∀ q ∈ W₀, ∃ W : Y.X.Opens, IsAffineOpen W ∧ W ≤ W₀ ∧ P W ∧ q ∈ W := fun q hq => by
    obtain ⟨D', hqD, hD⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X q
    obtain ⟨_, ⟨W, hW, rfl⟩, hqW, hle⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ ((W₀ ⊓ D' : Y.X.Opens) : Set Y.X) from ⟨hq, hqD⟩) (W₀ ⊓ D').isOpen
    exact ⟨W, hW, fun r hr => (hle hr).1, hD W hqW fun r hr => (hle hr).2, hqW⟩
  have loc₁ : ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (hWV : W ≤ W₀), P W →
      ∃ (y : KeyIn Γ(Y.X, W)) (u : Γ(Y.X, W)ˣ),
        KeyAt M (tau hW) (tau_le hW (hWV.trans inf_le_left)) y ∧ GlobalTheory.KeyCl.IsValue κ y (u : Γ(Y.X, W)) := by
    intro W hW hWV hdom
    have : IsDomain Γ(Y.X, W) := hdom
    have : IsNoetherianRing Γ(Y.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : IsIntegrallyClosed Γ(Y.X, W) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
    have : CharZero Γ(Y.X, W) := charZero_of_range (tau hW) (hr _ (tau_le hW hWV))
    obtain ⟨y, hy⟩ := exists_keyAt_of_range hpq M (tau hW) (tau_le hW (hWV.trans inf_le_left)) (hr _ (tau_le hW hWV))
    obtain ⟨u, hu⟩ := GlobalTheory.KeyFamUnit.famUnit κ hκ.2.1 hκ.2.2.1 Γ(Y.X, W) y
    exact ⟨y, u, hy, hu⟩
  obtain ⟨f, hf⟩ := GlobalTheory.KeyOpen.glue_units W₀ P hP
    (fun L _ z v => ∀ (hc : CharZero L) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn L), KeyAt M z hz' x → v = (κ L x : L))
    (fun L _ z hz v w hv hw => by
      have hc : CharZero L := charZero_of_range z (hr z hz)
      have hz' : ⊤ ≤ z ⁻¹ᵁ M.U := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      obtain ⟨x, hx⟩ := exists_keyAt_of_range hpq M z hz' (hr z hz)
      exact (hv hc _ x hx).trans (hw hc _ x hx).symm)
    (fun W hW hWV hPW => by
      obtain ⟨y, u, hy, hu⟩ := loc₁ W hW hWV hPW
      refine ⟨u, fun L _ z hz hc hz' x hx => ?_⟩
      have e : spMap (ev z W hz) ≫ tau hW = z := GlobalTheory.FlagMod.spMap_ev z hW hz
      generalize ev z W hz = φ at e ⊢
      subst e
      exact (hu L φ x (GlobalTheory.KeyAtBC.keyPB_of_keyAt hy hx)).symm)
  exact ⟨W₀, f, hW₀, fun K _ hK z hz hz' x hx => hf K z hz hK hz' x hx⟩

end GlobalTheory.KeyOpenModel
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  atlas_forward_decl GlobalTheory.KeyOpenModel.exists_unit_open
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  atlas_forward_decl GlobalTheory.KeyUnitGood.isUnit_key_of_good
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generatingFrame_unit_change_to_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  first | exact @GlobalTheory.KeyFramePoint.exists_keyAt_units | exact GlobalTheory.KeyFramePoint.exists_keyAt_units | (intros; apply GlobalTheory.KeyFramePoint.exists_keyAt_units <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec), NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  first | exact @GlobalTheory.BoxNonzeroClosed.main | exact GlobalTheory.BoxNonzeroClosed.main | (intros; apply GlobalTheory.BoxNonzeroClosed.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_line_sections_externalTensorPower_fibre : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  first | exact @GlobalTheory.BoxLine.sections_line | exact GlobalTheory.BoxLine.sections_line | (intros; apply GlobalTheory.BoxLine.sections_line <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.KeySwapSec

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open ReciprocityTheory.ChartRestriction.G.H1

theorem exists_isFibreOf_of_isMul (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G))
    (x : KeyIn R') (hL : L.IsLB) (hx : IsFibreOf x G L rig θ w f) (θ₀ : L.Sec) (b : R) (hb : IsMul (X := G) θ b θ₀) :
    ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀),
      (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧
      IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  obtain ⟨φ, he, e, hg, F, hp, hgen, hr, hs, hF, hFe, hv⟩ := hx
  obtain ⟨th₀, h₀⟩ := sec_pull_down ((isGen_iff e).1 hgen) hL x.P.isLB θ₀
  have h₁ := (KeyCancel.appLE_eq_iff_stalk e θ x.th).1 hs
  have hm : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i := by
    refine (sec_eq_iff _ _ _ _).2 fun k y hk => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (φ y)
    have e₁ := h₁ _ (𝟙 _) y j k hj hk
    have e₀ := h₀ _ (𝟙 _) y j k hj hk
    rw [hb j, gs_mul (𝟙 _ ≫ φ) y _ hj, gs_constFn _ _ (𝟙 _ ≫ φ) y hj, e₀, Category.id_comp, hp.1.w, cst_comp,
      mul_left_comm] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  refine ⟨th₀, fun s => ?_, hm, φ, he, e, hg, F, hp, hgen, hr, (KeyCancel.appLE_eq_iff_stalk e θ₀ th₀).2 h₀, hF, hFe, hv⟩
  obtain ⟨z, hz, hne⟩ := x.th_ne s
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hne
  refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
  rw [hm k, Scheme.basicOpen_mul] at hk
  exact hk.2

end GlobalTheory.KeySwapSec
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G)) (x : KeyIn R'), L.IsLB → IsFibreOf x G L rig θ w f → ∀ (θ₀ : L.Sec) (b : R), IsMul (X := G) θ b θ₀ → ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀), (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧ IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  atlas_forward_decl GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul
end

section
open scoped LaurentSeries

namespace GlobalTheory.PowerSeriesNoPole

open scoped LaurentSeries in
open PowerSeries in
private lemma C_dvd_iff_map_mk_eq_zero {A : Type} [CommRing A] (ϖ : A) (f : PowerSeries A) :
    C ϖ ∣ f ↔ PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    ext d
    simp [coeff_C_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · intro h
    have hd : ∀ d, ϖ ∣ coeff d f := fun d ↦ by
      have := congrArg (coeff d) h
      simpa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    choose q hq using hd
    refine ⟨mk q, ?_⟩
    ext d
    simp [coeff_C_mul, hq d]

open scoped LaurentSeries in
open PowerSeries in
private lemma prime_C_powerSeries {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (hϖ : Prime ϖ) :
    Prime (C ϖ : PowerSeries A) := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  refine ⟨fun h ↦ hϖ.ne_zero (by simpa using congrArg (coeff 0) h), fun hu ↦ hϖ.not_unit ?_,
    fun f g h ↦ ?_⟩
  · simpa using hu.map (constantCoeff (R := A))
  · rw [C_dvd_iff_map_mk_eq_zero, C_dvd_iff_map_mk_eq_zero]
    rw [C_dvd_iff_map_mk_eq_zero, map_mul] at h
    exact mul_eq_zero.mp h

open scoped LaurentSeries in
open PowerSeries in

theorem _root_.GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : Irreducible ϖ) (k : A →+* ℂ) (hk : Function.Injective k)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S]
    (ι : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A,
      ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s))
    (v : S) (hv : ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range)
    (hst : ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧
      v * algebraMap _ S t = algebraMap _ S s) :
    ∃ s : PowerSeries A, v = algebraMap _ S s := by
  obtain ⟨s, t, ht, hvt⟩ := hst
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (C ϖ * X : PowerSeries A) v
  rw [← map_pow] at ha
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu0 : (C ϖ * X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h ↦ hϖ0 (by simpa using congrArg (coeff 0) h)) X_ne_zero
  have hinj : Function.Injective (algebraMap (PowerSeries A) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hu0)
  have hat : a * t = s * (C ϖ * X) ^ n := by
    apply hinj
    rw [map_mul, map_mul, ← ha, ← hvt]
    ring
  obtain ⟨g, hg⟩ := hv
  have hga : g * PowerSeries.map k ((C ϖ * X) ^ n) = PowerSeries.map k a := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, hg, ← hι, ← hι, ← map_mul, ha]
  have hXa : (X : PowerSeries A) ^ n ∣ a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    apply hk
    rw [map_zero, ← PowerSeries.coeff_map, ← hga]
    have hdvd : (X : PowerSeries ℂ) ^ n ∣ g * PowerSeries.map k ((C ϖ * X) ^ n) :=
      ⟨g * C (k ϖ) ^ n, by rw [map_pow, map_mul, map_C, map_X, mul_pow]; ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  obtain ⟨a₁, rfl⟩ := hXa
  have ha₁ : a₁ * t = (C ϖ) ^ n * s := by
    have hX : (X : PowerSeries A) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [mul_pow] at hat
    linear_combination hat
  have hp : Prime (C ϖ : PowerSeries A) := prime_C_powerSeries hϖ.prime
  obtain ⟨a₂, rfl⟩ := hp.pow_dvd_of_dvd_mul_right n ht ⟨s, ha₁⟩
  refine ⟨a₂, ?_⟩
  have hunit : IsUnit (algebraMap (PowerSeries A) S ((C ϖ * X) ^ n)) :=
    IsLocalization.map_units S (⟨(C ϖ * X) ^ n, n, rfl⟩ : Submonoid.powers (C ϖ * X))
  apply hunit.mul_left_inj.mp
  rw [ha, ← map_mul]
  congr 1
  ring

end GlobalTheory.PowerSeriesNoPole
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  atlas_forward_decl GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime, IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  atlas_forward_decl GlobalTheory.PowerSeriesUniformiser.main
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open GlobalTheory.ArcIntegral

namespace GlobalTheory.ArcIntegralMixed

theorem exists_denominator {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] (ϖ : A)
    (hϖ : Irreducible ϖ) (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (v : S)
    (hv : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (ρ : PowerSeries A →+* R) (ψ : S →+* K),
      ψ.comp (algebraMap (PowerSeries A) S) = (algebraMap R K).comp ρ → IsUnit (ρ PowerSeries.X) →
      ψ v ∈ (algebraMap R K).range) :
    ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s := by
  obtain ⟨hp, hdvr⟩ := GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser A ϖ hϖ
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra (PowerSeries A) R), IsLocalization.AtPrime R (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}) :=
    ⟨_, _, _, hdvr, _, inferInstance⟩
  let K := FractionRing R
  have hρ : Function.Injective (algebraMap (PowerSeries A) R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}))
  let f : PowerSeries A →+* K := (algebraMap R K).comp (algebraMap (PowerSeries A) R)
  have hf : Function.Injective f := (IsFractionRing.injective R K).comp hρ
  have hC : Function.Injective (f.comp (PowerSeries.C (R := A))) := hf.comp PowerSeries.C_injective
  haveI : CharZero K := (RingHom.charZero_iff hC).1 inferInstance
  have h0 : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero
  have hu : IsUnit (f (PowerSeries.C ϖ * PowerSeries.X)) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hf).2 h0)
  obtain ⟨ψ, hψ⟩ := exists_away_lift (S := S) _ f hu
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, ha⟩ :=
      IsLocalization.surj (Submonoid.powers (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A)) x
    have ha0 : a = 0 := hf (by
      have := congrArg ψ ha
      rw [map_mul, hx, zero_mul, hψ] at this
      rw [← this, map_zero])
    rw [ha0, map_zero] at ha
    exact (IsLocalization.map_units S m).mul_left_eq_zero.1 ha
  have hX : (PowerSeries.X : PowerSeries A) ∈ (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl := by
    intro hm
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
    have := congrArg (PowerSeries.coeff 1) hq
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul] at this
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ this.symm)
  obtain ⟨r, hr⟩ := hv R K (algebraMap _ R) ψ (RingHom.ext hψ) (IsLocalization.map_units R ⟨_, hX⟩)
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl r
  refine ⟨s, t, fun hd => t.2 (Ideal.mem_span_singleton.2 hd), hψi ?_⟩
  rw [map_mul, hψ, hψ, ← hr]
  exact (map_mul (algebraMap R K) _ _).symm.trans (congrArg (algebraMap R K) hst)

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem integral_of_arcs_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  intro E _ _ _ H Dw l Xo c V Y h3 h4 hS hj U₀ W₀ f₀ hUW harc hgood R K _ _ _ _ _ _ _ z y hcount hU hy h
  by_cases hab : Set.range z ⊆ abLocus Y.t.G
  · exact hgood R K z y hU hy hab h
  have hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ Y.X), Set.range w ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ →
      ⊤ ≤ w ⁻¹ᵁ W₀ := fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, rfl⟩)
  obtain ⟨io, hio⟩ := exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨b₀, hover⟩ := exists_spMap (z ≫ Y.s)
  have hcomp : (algebraMap R K).comp b₀ = io.comp V.subtype := spMap_injective (by
    rw [← sp_comp, ← sp_comp, ← hover, ← hio, ← Category.assoc, ← hy, Model.j, ← Y.jQ_over]
    simp only [Category.assoc, pullback.condition])
  have hgen : Set.range (spMap (algebraMap R K) ≫ z) ⊆ Set.range Y.j := by
    rw [← hy]; rintro _ ⟨x, rfl⟩; exact ⟨y x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hch : CharZero R := (RingHom.charZero_iff (IsFractionRing.injective R K)).2 inferInstance
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum R hcount
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  obtain ⟨iK, hiK⟩ := exists_frac_lift (K := K) _ hiF
  let y' : Sp T.V ⟶ Y.X := spMap i ≫ z
  let b : V →+* T.V := i.comp b₀
  let io' : c.F →+* T.Fr := iK.comp io
  have hbio : (algebraMap T.V T.Fr).comp b = io'.comp V.subtype := by
    simp only [b, io']
    rw [← RingHom.comp_assoc, ← hiK, RingHom.comp_assoc, hcomp, RingHom.comp_assoc]
  have hy' : y' ≫ Y.s = spMap b := by
    simp only [y', Category.assoc]; rw [hover, sp_comp]
  let zT : Sp T.Fr ⟶ Xo.XF c := spMap iK ≫ y
  have hzT : zT ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' := by
    simp only [y', zT]
    rw [Category.assoc, hy, ← Category.assoc, sp_comp, hiK, ← sp_comp, Category.assoc]
  have hzT' : zT ≫ pullback.snd _ _ = spMap io' := by
    simp only [zT, io']
    rw [Category.assoc, hio, sp_comp]
  clear_value zT
  have hbad : ¬ Set.range y' ⊆ abLocus Y.t.G := fun hy => hab (by
    rintro _ ⟨x, rfl⟩
    rcases point_cases R K x with ⟨p, rfl⟩ | rfl
    · exact range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)
    · have e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R := spMap_closedPoint i
      have := hy ⟨IsLocalRing.closedPoint T.V, rfl⟩
      change (spMap i ≫ z) (IsLocalRing.closedPoint T.V) ∈ _ at this
      erw [Scheme.Hom.comp_apply, e] at this; exact this)
  obtain ⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c V Y h3 hS T io' b y' zT hbio hy' hzT' hzT hbad
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V := hϖ.maximalIdeal_eq ▸ T'.cpl
  obtain ⟨χ₀, hχ, hsp⟩ := h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover₀, hab₀, hopen, hW⟩ := (hχ χ₀).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ₀).1 hW
  obtain ⟨-, -, evu, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl
  have hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hg
  obtain ⟨gF, hgF'⟩ := exists_frac_lift (K := T.Fr) _ hgF
  have hχy : spMap evu ≫ χ₀ = spMap g ≫ y' := hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      have e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j := by
        rw [hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]
        rfl
      exact ⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX
  have hχz : spMap evu ≫ χ₀ = spMap g ≫ spMap i ≫ z := hχy
  haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg
  have hχU : ⊤ ≤ χ₀ ⁻¹ᵁ U₀ := by
    have hc : χ₀ (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀ := by
      rw [← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]
      change (spMap evu ≫ χ₀) (IsLocalRing.closedPoint T'.V) ∈ U₀
      rw [hχz]
      exact hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))
    exact ((IsLocalRing.closed_point_mem_iff (U := χ₀ ⁻¹ᵁ U₀)).1 hc).ge

  let S := Localization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries T'.V)
  let ι : PowerSeries T'.V →+* S := algebraMap _ _
  have huX : IsUnit (ι (PowerSeries.C ϖ * PowerSeries.X)) := IsLocalization.Away.algebraMap_isUnit _
  have hSj : Set.range (spMap ι ≫ χ₀) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    exact hopen (spMap ι x) fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ι (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal from hx) huX)
  have hSW : ⊤ ≤ (spMap ι ≫ χ₀) ⁻¹ᵁ W₀ := hzW _ hSj (le_preimage_comp _ hχU)

  have hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum := by
    rw [show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact mk_le_continuum_of_finite g hgf hcard
  obtain ⟨κ, hκ⟩ := @GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _
    (gF.comp io').toAlgebra hcard' c.F.val.toRingHom
  let κ₀ : T'.V →+* ℂ := κ.comp (algebraMap T'.V T'.Fr)
  have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b) := by
    rw [← hκ]
    change κ.comp (gF.comp (io'.comp V.subtype)) = κ.comp (((algebraMap T'.V T'.Fr).comp g).comp b)
    rw [← hbio, ← hgF']; rfl
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ
    (g.comp b) a κ₀ hκ₀ _ hb'
  obtain ⟨hW₁, -⟩ := hbc a₁ p hp
  obtain ⟨W₁, -⟩ := hW₁ χ₀ W
  have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
  have hXu : IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ (isUnit_map_X κ₀)
    rw [RingHom.comp_apply, PowerSeries.map_C]
    exact ((IsUnit.mk0 _ hϖ0).map _).map _
  obtain ⟨ιC, hιC'⟩ := exists_away_lift (S := S) _ _ hXu
  have hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s) :=
    fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)
  have hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ = spMap ιC ≫ spMap ι ≫ χ₀ := by
    rw [← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp,
      show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]
  have hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀) ⁻¹ᵁ W₀ := by
    rw [hpt]; exact le_preimage_comp _ hSW
  have hres := harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀) ((Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by
      rw [Category.assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by
      refine hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))
    (le_preimage_comp _ hχU) hLh
  rw [ev_factor ιC (spMap ι ≫ χ₀) _ hpt W₀ hSW hLh f₀] at hres

  have hden := exists_denominator ϖ hϖ S (ev (spMap ι ≫ χ₀) W₀ hSW f₀) (by
    intro R' K' _ _ _ _ _ _ _ ρ ψ hψ hρ
    have e : spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀ = spMap ψ ≫ spMap ι ≫ χ₀ := by
      rw [← Category.assoc, ← Category.assoc (spMap ψ), sp_comp, sp_comp, ← hψ]
    have hW' : ⊤ ≤ (spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀) ⁻¹ᵁ W₀ := by
      rw [e]; exact le_preimage_comp _ hSW
    rw [← ev_factor ψ (spMap ι ≫ χ₀) _ e W₀ hSW hW' f₀]
    refine hgood R' K' (spMap ρ ≫ χ₀) (spMap ψ ≫ IsOpenImmersion.lift Y.j (spMap ι ≫ χ₀) hSj)
      (le_preimage_comp _ hχU) (by rw [Category.assoc, IsOpenImmersion.lift_fac, e]) ?_ hW'
    rintro _ ⟨x, rfl⟩
    exact (hab₀ (spMap ρ x)).2 fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ρ PowerSeries.X ∈ x.asIdeal from hx) hρ))
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X T'.V ϖ hϖ κ₀ hκ₀ S ιC hιC _ hres hden

  have hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [RingHom.comp_apply, map_mul evu, hevC, hevX]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2
      (mul_ne_zero hϖ.ne_zero hϖ.ne_zero))
  obtain ⟨φS, hφS⟩ := exists_away_lift (S := S) _ _ hϖu
  have hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i)) :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)
  obtain ⟨la, hla⟩ := exists_frac_lift (K := K) _ hgi
  have hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ := by
    have e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, hla]
    have e2 : spMap φS ≫ spMap ι ≫ χ₀ = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS,
        ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    rw [e1, e2]
  have hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s) := by
    rw [← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h),
      GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]
    rfl
  haveI : IsLocalHom (g.comp i) := inferInstance
  exact mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩

end GlobalTheory.ArcIntegralMixed
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_arcs_and_goodReduction_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  atlas_forward_decl GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyUnitModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open GlobalTheory.FlagMod (ev_res ev_spMap le_preimage_mono)

theorem norm_bounds {κ : KeyRule} (hκ : IsKeyRule κ) (x : KeyIn ℂ) {τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hab : GlobalTheory.KeyPow.charHalf _ a b) (hc : c₀ ≠ 0)
    (hN : GlobalTheory.KeyPow.NormalAt x τ Mx a b c₀) {C : ℝ} (hC : 0 < C) (h₁ : C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2)
    (h₂ : ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C) : ‖(κ ℂ x : ℂ)‖ ≤ C ^ 4 ∧ ‖(κ ℂ x : ℂ)⁻¹‖ ≤ C ^ 4 := by
  have hr : 0 < ‖Mx.det‖ / ‖c₀‖ ^ 2 := (inv_pos.2 hC).trans_le h₁
  have hM : Mx.det ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨P, hg, rig, hrig, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := GlobalTheory.KeyConst.exists_rescale P hg rig hrig th hth v hv τ Mx _ _ c₀ hc hM hN
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff _ _ _ _).1 hN₀
  have e := hκ.1 ℂ P hg rig hrig _ hth₀ v₀ hv₀ th hth v hv c₀ Mx e₁ hMv
  rw [hκ.2.2.2.1 ⟨P, hg, rig, hrig, th₀, hth₀, v₀, hv₀⟩ u τ a b k₁ k₂ hab.1 hab.2 k₃ k₄ k₅ k₆, Units.val_one,
    _root_.mul_one] at e
  have q : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have e' : ‖(κ ℂ ⟨P, hg, rig, hrig, th, hth, v, hv⟩ : ℂ)‖ = (‖Mx.det‖ / ‖c₀‖ ^ 2) ^ 4 := by
    have := congrArg (‖·‖) e
    simp only [norm_mul, norm_pow] at this
    rw [div_pow, ← pow_mul, eq_div_iff (by positivity), ← this, _root_.mul_comm]
  constructor
  · rw [e']
    gcongr
  · rw [norm_inv, e', ← inv_pow]
    gcongr
    exact inv_le_of_inv_le₀ hC h₁

theorem countable_sections {X : Scheme.{0}} {O : Type} [CommRing O] [Countable O] (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have hf : (s.appLE ⊤ _ le_top).hom.FiniteType :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top)
  letI := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp O, ⊤) Γ(X, U) := hf
  have hc : Countable Γ(Sp O, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.symm.injective.countable
  obtain ⟨n, f, hfs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  have : Countable (MvPolynomial (Fin n) Γ(Sp O, ⊤)) :=
    (MvPolynomial.basisMonomials (Fin n) Γ(Sp O, ⊤)).repr.injective.countable
  exact hfs.countable

theorem exists_chart_unit {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (M : GChart Y) : ∃ u : Γ(Y.X, M.U), IsUnit u ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X)
      (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), Set.range z ⊆ Set.range Y.j → KeyAt M z hz x → (κ K x : K) = ev z M.U hz u := by
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, hopen⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  have := Y.jQ_open
  have hj : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  obtain ⟨-, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen W c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  obtain ⟨W₀, f₀, hW, hf⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart E H D l Xo c _ _ Y inferInstance hj hpq κ hκ M
  have hcF : Countable c.F := by
    have := c.fin
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F
    rw [← Cardinal.mk_le_aleph0_iff]
    simpa [Cardinal.mkRat] using this
  have : Countable W := Subtype.val_injective.countable
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := M.dom
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ := IsTotallyComplex.finrank E
    have h₂ : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Nat.mul_pos (by omega) hpq
  have hWU : W₀ ≤ M.U := fun x hx => ((hW x).1 hx).1
  have hWj : ∀ {K : Type} [Field K] {z : Sp K ⟶ Y.X}, ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := fun hz => by
    rintro _ ⟨q, rfl⟩; exact ((hW _).1 (hz (Set.mem_univ q))).2
  have hne : ∃ x, x ∈ W₀ := by
    obtain ⟨q⟩ : Nonempty (Sp Γ(Y.X, M.U)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨x, hx, hx'⟩ := hdense.exists_mem_open M.U.isOpen ⟨_, tau_le M.hU le_rfl (Set.mem_univ q)⟩
    exact ⟨x, (hW x).2 ⟨hx', hx⟩⟩
  obtain ⟨hinj, hext⟩ := GlobalTheory.GenExt.extend_of_integral_at_dvr _ _ W₀ hWU M.hU M.dom
    (IsLocallyNoetherian.component_noetherian ⟨_, M.hU⟩) (GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen M.hU)
    (countable_sections Y.s M.hU) hne
  have key : ∀ u : Γ(Y.X, W₀), (u = f₀.val ∨ u = (f₀⁻¹).val) → ∃ f, resG _ hWU f = u := by
    intro u hu
    refine hext u fun R K _ _ _ _ _ _ z hR hz h => ?_
    let y := IsOpenImmersion.lift Y.j (spMap (algebraMap R K) ≫ z) (hWj h)
    have : CharZero K := charZero_of_injective_ringHom (Spec.preimage (y ≫ pullback.snd _ _)).hom.injective
    refine GlobalTheory.T.integral_of_arcs_and_goodReduction_points E H D l Xo c W Y h3 h4 hs hj M.U W₀ u (fun x hx hx' => (hW x).2 ⟨hx, hx'⟩)
      (fun a χ hA hover hgen hχ => ?_) (fun R K _ _ _ _ _ _ _ z y hz hy hab h => ?_) R K z y hR hz
      (IsOpenImmersion.lift_fac _ _ _) h
    · obtain ⟨y, hy, T, C', hC', hT⟩ := GlobalTheory.ArcNormal.arc_normal_form _ _ _ _ _ _ _ Y hpq hP a χ hA hover hgen M hχ
      refine GlobalTheory.ArcReg.not_pole_of_bounded _ M.U W₀ u χ y M.hU hWU hχ hy ⟨T, C' ^ 4, fun w hw hyw => ?_⟩
      obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (y w) (le_preimage_mono hWU hyw) (hWj hyw) hpos
      obtain ⟨τ, Mx, a', b', c₀, k₁, k₂, k₃, k₄, k₅⟩ := hT w hw _ x hk
      obtain ⟨b₁, b₂⟩ := norm_bounds hκ x k₁ k₂ k₃ hC' k₄ k₅
      have e := hf ℂ (y w) hyw _ x hk
      rcases hu with rfl | rfl
      · rwa [e]
      · rwa [map_units_inv, e]
    · obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M _ (le_preimage_comp _ hz) (hWj h) hpos
      obtain ⟨v, hv⟩ := GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart E H D l Xo c _ _ Y κ hκ M R K z hz y hy hab x hk
      have e := hf K _ h _ x hk
      rcases hu with rfl | rfl
      · exact ⟨v, by rw [e, hv]⟩
      · exact ⟨(v⁻¹ : Rˣ), by rw [map_units_inv, map_units_inv, e, hv]⟩
  obtain ⟨f, hf₁⟩ := key _ (Or.inl rfl)
  obtain ⟨f', hf₂⟩ := key _ (Or.inr rfl)
  refine ⟨f, IsUnit.of_mul_eq_one f' (hinj ?_), fun K _ _ z hz x hr hk => ?_⟩
  · exact ((RingHom.map_mul _ f f').trans ((congrArg₂ (· * ·) hf₁ hf₂).trans f₀.mul_inv)).trans (RingHom.map_one _).symm
  · have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := fun q hq => (hW _).2 ⟨hz hq, hr ⟨q, rfl⟩⟩
    rw [← hf K z hz₀ _ x hk, ← hf₁, ev_res z hWU hz₀ hz]

theorem lieComb_one {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) :
    IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i) x.v (x.v i) := by
  have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  have := x.P.isAb.comm
  exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i

theorem unitAt_local {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] :
    UnitAt κ Y V K := by
  intro y yt hyt t m n w hw θ x hx
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, -⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  obtain ⟨M, hM⟩ := GlobalTheory.FlagMod.exists_gChart hP (yt (IsLocalRing.closedPoint V))
  have hz : ⊤ ≤ yt ⁻¹ᵁ M.U := ((IsLocalRing.closed_point_mem_iff (U := yt ⁻¹ᵁ M.U)).1 hM).ge
  obtain ⟨u, hu, hval⟩ := exists_chart_unit Y hpq hP h3 h4 hs hκ M
  have := t.semi.smooth
  obtain ⟨θ₀, h₀⟩ : ∃ θ₀ : t.PP.L.Sec, NonzeroClosed (X := t.G) θ₀ := by
    obtain ⟨-, θ₀, -, -, hne⟩ := GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact ⟨θ₀, g, h₁, TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  have hC : ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
      Generates (X := t.G) θ → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := fun θ x hx hθ => by
    obtain ⟨x', a, d, hk, e⟩ := GlobalTheory.T.exists_generatingFrame_unit_change_to_chart E H D l Xo c _ _ Y M V K yt hz t m n w hw θ x hx hθ
    have e₁ := e κ hκ
    rw [hval K _ _ x' (by
      rw [hyt]; rintro _ ⟨q, rfl⟩; exact ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩) hk,
      ev_spMap (algebraMap V K) yt M.U hz, RingHom.comp_apply] at e₁
    refine ⟨(d ^ 4)⁻¹ * (a ^ 8 * (hu.map (ev yt M.U hz)).unit), ?_⟩
    have hd : algebraMap V K d ≠ 0 := (d.isUnit.map _).ne_zero
    rw [Units.val_mul, map_mul, map_units_inv, Units.val_mul, map_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, e₁, inv_mul_cancel_left₀ (pow_ne_zero _ hd)]
  have hB : ∀ (θ : t.PP.L.Sec), Generates (X := t.G) θ → ∀ N : ℕ, Generates (X := pow t.G N) (boxSec t.G θ N) :=
    fun θ' hθ N => by
      obtain ⟨a, ha, -⟩ := hθ θ₀
      obtain ⟨hfl, g, hg, hnz⟩ := GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre V t.G t.PP.L θ' (NonzeroClosed.of_isMul ha h₀).2 N
      obtain ⟨X', p', φ, L', b, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_line_sections_externalTensorPower_fibre V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx N
      exact generates_of_generic_line (pow t.G N).hom k₁ (LB.isLB_linComb t.PP.isLB _ _) k₂ k₃ b k₄ _ hg hnz
  refine ⟨fun hθ => ⟨hC θ x hx hθ, fun N _ => hB θ hθ N⟩, ?_⟩
  intro N hN σ a hσ hmul
  have hg₀ := generates_of_isFibreOf t.PP.isLB hx h₀
  obtain ⟨b, hθb, -⟩ := hg₀ θ
  obtain ⟨th₀, hth₀, hth, hx₀⟩ := GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx θ₀ b hθb
  obtain ⟨u₀, hu₀⟩ := hC θ₀ _ hx₀ hg₀
  have hbox₀ := hB θ₀ hg₀ N
  have hom := hκ.1 K x.P x.g_pos x.rig x.rig_gen th₀ hth₀ x.v x.basis x.th x.th_ne x.v x.basis (algebraMap V K b) 1
    hth (lieComb_one x)
  rw [Matrix.det_one, one_pow, _root_.one_mul] at hom
  obtain ⟨c', hc', -⟩ := hσ (boxSec t.G θ₀ N)
  have hcu : IsUnit c' := Generates.isUnit hσ hbox₀ hc'
  have ha : a = b ^ N * c' := (hσ (boxSec t.G θ N)).unique hmul (IsMul.trans (isMul_boxSec hθb N) hc')
  obtain ⟨k, rfl⟩ := hN
  refine ⟨hcu.unit * u₀ ^ k, ?_⟩
  rw [ha, Nat.mul_div_cancel_left k (by norm_num : 0 < 8)]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu₀, ← hom, pow_mul]
  ring

theorem unitAt_valuation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hpq : 1 ≤ D.p + D.q)
    (hβ : IsBaseRing β) (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule}
    (hκ : IsKeyRule κ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] : UnitAt κ Y V K := by
  intro y yt hyt t m
  have hinj := IsFractionRing.injective V K
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B),
      spMap f ≫ spMap g = spMap (f.comp g) := fun _ _ => (Spec.map_comp _ _).symm
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* K, spMap io = y ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : O →+* V, spMap b₀ = yt ≫ Y.s := ⟨_, Spec.map_preimage _⟩
  have hc : (algebraMap V K).comp b₀ = io.comp β := by
    have e : spMap ((algebraMap V K).comp b₀) = spMap (io.comp β) := by
      rw [← sp, ← sp, hb₀, hio, ← Category.assoc, hyt, Model.j, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let W : ValuationSubring c.F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  let b : O →+* W := β.codRestrict W.toSubring fun a => ⟨b₀ a, RingHom.congr_fun hc a⟩
  have hb : W.subtype.comp b = β := rfl
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let b' : W →+* V := e.symm.toRingHom.comp ((io.comp W.subtype).codRestrict (algebraMap V K).range fun a => a.2)
  have hb' : b'.comp b = b₀ := RingHom.ext fun a => by
    apply e.injective
    exact (e.apply_symm_apply _).trans (Subtype.ext (RingHom.congr_fun hc a).symm)
  obtain ⟨_, _⟩ := GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing E H l c O β hβ W b hb
  let yt' : Sp V ⟶ (locModel Y b hb).X := pullback.lift yt (spMap b') (by rw [sp, hb', hb₀])
  have hy' : yt' ≫ pullback.fst Y.s (spMap b) = yt := pullback.lift_fst _ _ _
  obtain ⟨m', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := yt') (locMap Y b) (hy'.symm ▸ m)
  exact unitAt_local (locModel Y b hb) hpq (locModel_pushInvertible Y b hb (GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W).1 hP) (localisedModel_uniformisation_baseChange Y b hb h3)
    (GlobalTheory.T.arcProperty_localisationBaseChange_of_model E H D l Xo c O β Y _ _ b hb h4) (GlobalTheory.T.splitFibres_localisedModel_baseChange E H D l Xo c O β Y _ _ b hb hs) hκ V K y yt' (by
      rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, Category.assoc, hy', locModel_j, hyt]) t m'

theorem keyUnitOnModels : KeyUnitOnModels := by
  intro κ hκ E _ _ _ H D l Xo c O _ β Y p h₁ h₂ _ h₄ h₅ h₆ h₇
  refine ⟨fun V K _ _ _ _ _ _ _ _ => unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V K, fun V C _ _ _ _ _ _ _ hV => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.GoodRedUnitBall.valuationRing_of_unitBall hV
  exact unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V C

end GlobalTheory.KeyUnitModels
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.KeyUnitOnModels := by
  atlas_forward_decl GlobalTheory.KeyUnitModels.keyUnitOnModels
end

section
noncomputable section

namespace GlobalTheory.KeyIntegralVal

section Valuation

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem exists_mem_different_vLa {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] (σ : E →+* F)
    (w : HeightOneSpectrum (𝓞 F)) : ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      vLa (R := 𝓞 F) w (σ (δ : E)) = (ord_vw w (conjDifferent σ) : ℤ) := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := fun a b h =>
    Subtype.ext (σ.injective (congrArg (fun x : 𝓞 F => (x : F)) h))
  have hJ : conjDifferent σ ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) ((Ideal.map_eq_bot_iff_of_injective hinj).1 h)
  have hfin : FiniteMultiplicity w.asIdeal (conjDifferent σ) := FiniteMultiplicity.of_prime_left w.prime hJ
  have h1 : conjDifferent σ ≤ w.asIdeal ^ ord_vw w (conjDifferent σ) := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  have h2 : ¬ conjDifferent σ ≤ w.asIdeal ^ (ord_vw w (conjDifferent σ) + 1) := fun h =>
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.2 h)
  generalize ord_vw w (conjDifferent σ) = n at h1 h2 ⊢
  rw [conjDifferent, Ideal.map_le_iff_le_comap] at h1 h2
  obtain ⟨δ, hδ, hn⟩ := Set.not_subset.1 h2
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine ⟨δ, hδ, hδ0, ?_⟩
  have e : σ (δ : E) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingHom σ δ) := rfl
  have hne : w.intValuation (RingOfIntegers.mapRingHom σ δ) ≠ 0 :=
    w.intValuation_ne_zero _ ((map_ne_zero_iff _ hinj).2 hδ0)
  have a1 := (w.intValuation_le_pow_iff_mem _ n).2 (h1 hδ)
  have a2 := mt (w.intValuation_le_pow_iff_mem (RingOfIntegers.mapRingHom σ δ) (n + 1)).1 hn
  rw [← WithZero.log_le_iff_le_exp hne] at a1 a2
  rw [vLa, e, HeightOneSpectrum.valuation_of_algebraMap]
  push_cast at a2
  omega

theorem nval_bounds {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {T : CDVR} {io : F →+* T.Fr}
    {e : ℕ} (ho : OverLa w T.V io e) {ι : Type} [Fintype ι] (x : ι → F) (z : ι → T.V) (n : ι → ℕ) (D : T.V)
    (u : T.Vˣ) (hx : ∀ i, x i ≠ 0) (hz : ∀ i, algebraMap T.V T.Fr (z i) = io (x i)) (hD : D ∣ ∏ i, z i ^ n i) :
    0 ≤ nval T.V e (algebraMap T.V T.Fr (D ^ 4 * (u : T.V))) ∧
      nval T.V e (algebraMap T.V T.Fr (D ^ 4 * (u : T.V))) ≤
        ((4 * ∑ i, (n i : ℝ) * (vLa (R := 𝓞 F) w (x i) : ℝ) : ℝ) : EReal) := by
  classical
  have nn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := fun a => by
    by_cases h : algebraMap T.V T.Fr a = 0
    · simp [h, vV]
    have := (WithZero.log_le_log (valV_ne_zero (V := T.V) h) one_ne_zero).2
      (HeightOneSpectrum.valuation_le_one _ a)
    rw [WithZero.log_one] at this
    rw [vV]; omega
  have pw : ∀ (a : T.Fr) (k : ℕ), vV T.V (a ^ k) = k * vV T.V a := fun a k => by simp [vV]
  have hp : ∀ s : Finset ι, vV T.V (∏ i ∈ s, io (x i) ^ n i) = ∑ i ∈ s, n i * (e * vLa w (x i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp [vV]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, vV_mul (pow_ne_zero _ ((map_ne_zero io).2 (hx a)))
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero io).2 (hx i))), ih, pw, ho.2]
  obtain ⟨q, hq⟩ := hD
  have hq' : algebraMap T.V T.Fr D * algebraMap T.V T.Fr q = ∏ i, io (x i) ^ n i := by
    rw [← map_mul, ← hq, map_prod]
    simp only [map_pow, hz]
  have hne : algebraMap T.V T.Fr D * algebraMap T.V T.Fr q ≠ 0 :=
    hq' ▸ Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero io).2 (hx i))
  have h1 := hp Finset.univ
  rw [← hq', vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at h1
  have hu : ∀ u : T.Vˣ, algebraMap T.V T.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have hu0 : vV T.V (algebraMap T.V T.Fr u) = 0 := by
    have h := vV_mul (V := T.V) (hu u) (hu u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : T.Vˣ)
    omega
  have hD0 := pow_ne_zero 4 (left_ne_zero_of_mul hne)
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  rw [map_mul, map_pow, nval, if_neg (mul_ne_zero hD0 (hu u)), vV_mul hD0 (hu u), hu0, pw, add_zero]
  have h2 : (0 : ℝ) ≤ vV T.V (algebraMap T.V T.Fr D) := by exact_mod_cast nn D
  have h3 : (vV T.V (algebraMap T.V T.Fr D) : ℝ) ≤ ∑ i, (n i : ℝ) * (e * (vLa w (x i) : ℝ)) := by
    have := nn q
    exact_mod_cast (by omega : vV T.V (algebraMap T.V T.Fr D) ≤ ∑ i, n i * (e * vLa w (x i)))
  refine ⟨EReal.coe_nonneg.2 (by push_cast; positivity), EReal.coe_le_coe_iff.2 ?_⟩
  rw [div_le_iff₀ he, mul_assoc, Finset.sum_mul]
  push_cast
  refine mul_le_mul_of_nonneg_left (h3.trans_eq (Finset.sum_congr rfl fun i _ => by ring)) (by norm_num)

end Valuation

section Lie

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

theorem exists_lie_matrices {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) {n : ℕ} {w : Fin n → (epsR R ⟶ G)} (hw : IsLieBasis w) {I : Type} (τ : I → O →+* R)
    {m : I → ℕ} (u : ∀ i, Fin (m i) → (epsR R ⟶ G)) (h₁ : ∀ i k, IsTangent (u i k))
    (h₂ : ∀ i k a, (u i k ≫ act.act a).left = spMap (epsScaleR (τ i a)) ≫ (u i k).left)
    (h₃ : ∀ i x, IsTangent x → (∀ a, (x ≫ act.act a).left = spMap (epsScaleR (τ i a)) ≫ x.left) →
      ∃ cf, IsLieComb cf (u i) x) :
    ∃ (A : O →+* Matrix (Fin n) (Fin n) R) (U : ∀ i, Fin (m i) → Fin n → R),
      (∀ i (x : Fin n → R), (∀ a, (A a).mulVec x = τ i a • x) → ∃ cf : Fin (m i) → R, x = ∑ k, cf k • U i k) ∧
      (∀ i k a, (A a).mulVec (U i k) = τ i a • U i k) ∧ ∀ i k, IsLieComb (U i k) w (u i k) := by
  let b := Lie.basis act hw
  let A : O →+* Matrix (Fin n) (Fin n) R :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp (Module.toModuleEnd R (Lie act))
  have hA : ∀ a (x : Lie act), (A a).mulVec (b.equivFun x) = b.equivFun (a • x) := fun a x =>
    LinearMap.toMatrix_mulVec_repr b b (Module.toModuleEnd R (Lie act) a) x
  let u' : ∀ i, Fin (m i) → Lie act := fun i k => Lie.mk act (u i k) (h₁ i k)
  refine ⟨A, fun i k => b.equivFun (u' i k), fun i x hx => ?_, fun i k a => ?_, fun i k => ?_⟩
  · obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    have hm : x ∈ Lie.eig act (τ i) := fun a => b.equivFun.injective (by rw [← hA, hx, map_smul])
    obtain ⟨cf, hcf⟩ := h₃ i x.hom x.isTangent (Lie.mem_eig_iff_left.1 hm)
    refine ⟨cf, ?_⟩
    have : x = ∑ k, cf k • u' i k := Lie.ext ((Lie.isLieComb_iff cf (u' i) x.hom).1 hcf)
    rw [this, map_sum]
    simp only [map_smul]
  · have hm : u' i k ∈ Lie.eig act (τ i) := Lie.mem_eig_iff_left.2 (h₂ i k)
    rw [hA, hm a, map_smul]
  · have hw' : w = fun k => (b k).hom := funext fun k => (Lie.hom_basis (a := act) hw k).symm
    rw [hw', Lie.isLieComb_iff, b.sum_equivFun]
    rfl

theorem isTan_iff_isTangent {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

end Lie

section Model

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ∃ (W : ValuationSubring ℂ) (p : ℕ) (Y : Model Xo c (c.V W).subtype),
      c.V W = (la.valuation c.F).valuationSubring ∧ p.Prime ∧ Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := by
  classical
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.Reg.exists_prime_natCast_mem la
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hg p hp⟩
    exact ⟨_, h1.1 ⟨l, c, hg p hp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨W, p, Y, hWe, hp, hY⟩

theorem key_unit {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨W, p, Y, hW, hp, h2, h3, h4, h5⟩ := exists_model Xo c hpq hg la
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (β := (c.V W).subtype)
    (fun a => (Valuation.mem_valuationSubring_iff _ _).1 (hW ▸ a.2)) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

theorem isFibreOf_of_sabMap {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {G : SAB H (Sp S)}
    (P : GlobalTheory.CM.PAT H (Sp S')) (n : SABMap P.t G (spMap φ)) (hp : 1 ≤ P.g) {θ : G.PP.L.Sec} {σ : P.t.PP.L.Sec}
    (hσ : ∀ s : Sp S', ∃ q : P.t.G.left, P.t.G.hom q = s ∧ q ∈ Out.nonzeroLocus σ)
    {w : LB.Iso P.t.PP.L (G.PP.L.pull n.φ)} {θ₂ : (G.PP.L.pull n.φ).Sec} (hw : RigIso n w) (hm : IsoMaps w σ θ₂)
    (hθ : PullSec n.φ θ θ₂) {v : Fin P.g → (epsR S ⟶ G.G)} {v' : Fin P.g → (epsR S' ⟶ P.t.G)} (hb : IsLieBasis v')
    (hv : ∀ i, (v' i).left ≫ n.φ = spMap (Chart.dualMapR φ) ≫ (v i).left) :
    IsFibreOf ⟨P.pol, hp, P.t.PP.rig, P.t.PP.rigGen, σ, hσ, v', hb⟩ G.G G.PP.L G.PP.rig θ v φ := by
  have he : eSec P.t.G ≫ n.φ = spMap φ ≫ eSec G.G := n.cm.e_comm.trans (congrArg (· ≫ eSec G.G) n.base)
  have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec P.t.G ≫ n.φ = e ≫ eSec G.G),
      rigPullOf n.φ e he G.PP.L G.PP.rig = n.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨n.φ, he, w, rfl, Chart.dualMapR φ, n.cart, hw.1, ?_, fun j i h => ?_, fun a => ?_, ?_, hv⟩
  · exact (hr _ n.base he).symm ▸ hw.2
  · refine Eq.trans ?_ (hm j i)
    have le : (G.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ G.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
    rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_tied_det {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {r : ℕ} (ho : OverLa la T.V io r)
    (τ' : (E →+* ℂ) → (𝓞 E →+* T.V)) (hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a))
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T.V)
      (U : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin g → T.V) (u : T.Vˣ), Tied e y.s y.u Φ ∧
      (∀ τ (x : Fin g → T.V), (∀ a, (A a).mulVec x = τ' τ a • x) →
        ∃ cf : Fin (Dw.mult τ) → T.V, x = ∑ k, cf k • U τ k) ∧
      (∀ τ k a, (A a).mulVec (U τ k) = τ' τ a • U τ k) ∧
      (κ T.Fr Φ.key : T.Fr) =
        algebraMap T.V T.Fr ((Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V)) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, u1, u2, u3, u4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hs⟩ := hy
  obtain ⟨U₀, hU₀, hg₀⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨⟨P, rfl, hPg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U₀ t' (hU₀ ▸ m1)
  obtain ⟨Ψ, -, hΨ, -⟩ := exists_tied E H Dw l Xo c g e T.Fr y hpq
  have hgp : 1 ≤ g := hΨ ▸ Ψ.g_pos
  obtain rfl : P.g = g := hPg.trans (hg₀.trans (card_frame_index Dw e))
  have ht : SecTie m1 σ y.s := ⟨w1, s1, r1, i1, hs⟩
  have hne := ((SecTieEx.secTie_exists_unique E H Dw l Xo T.Fr y.x P.t m1).2.2 σ _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo T.Fr _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c T.Fr y.x y.u P.g e y.tan y.eig).1 y.basis
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo T.Fr y.x P.t.G m1.φ m1.cart
  choose u' hu₁ hu₂ using u4
  have hov : ∀ τ i, u' τ i ≫ P.t.G.hom = (epsR T.Fr).hom := fun τ i => by
    have : IsPreimmersion (spMap (algebraMap T.V T.Fr)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu₂,
      Category.assoc, Over.w]
    exact (GlobalTheory.EtaVal.spMap_comp_spMap _ _).trans ((congrArg spMap (RingHom.ext fun a => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (GlobalTheory.EtaVal.spMap_comp_spMap _ _).symm)
  let v : Fin P.g → (epsR T.Fr ⟶ P.t.G) := fun j => Over.homMk (u' (e j).1 (e j).2) (hov _ _)
  have hv : IsLieBasis v := (hb _ v).2 (by
    rw [show (fun j => (v j).left ≫ m1.φ) = fun j => y.u (e j).1 (e j).2 from funext fun j => hu₁ _ _]
    exact hB)
  obtain ⟨n, w, hw⟩ := Chart.exists_isLieBasis G.G G.semi.smooth
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ G.G P.t.G m2.φ m2.cart G.semi.smooth n w hw
  obtain rfl : P.g = n := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis P.t.act hv).indexEquiv (GlobalTheory.Serre.Lie.basis P.t.act hw'))
  have inj := IsFractionRing.injective T.V T.Fr
  obtain ⟨A, U, a1, a2, a3⟩ := exists_lie_matrices G.act hw τ' (m := Dw.mult) ub
    (fun τ k => (isTan_iff_isTangent _).1 (u1 τ k)) (fun τ k a => u2 τ k a _ (hτ τ a))
    (fun τ x hx he => (u3 τ x ((isTan_iff_isTangent _).2 hx) fun a z hz => by
      rw [inj (hz.trans (hτ τ a).symm)]
      exact he a).exists)
  obtain ⟨u, hu⟩ := key_unit hκ hpq hg ho y.x_over m1 m2 hw hθ _
    (isFibreOf_of_sabMap _ P m2 hgp hne r2 i2 hp hw' hww)
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, A, U, u, ⟨ht, rfl, fun j => hu₁ _ _⟩, a1, a2, ?_⟩
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

end Model

section Main

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem key_valuation_bounds : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal) := by
  intro κ hκ E _ _ _ H Dw l Xo c g e K hpq hg _ hK w v hv
  classical
  obtain ⟨⟨_, T, io, r, ho, y, -, η, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io r ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det hκ hpq hg e ho τ' hτ y.1 y.2.2
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ) inferInstance a1 a2 δ hδ
  have hb := nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD
  rw [← hu, ← hK T.Fr y.1 Φ hΦ] at hb
  simp only [hδv, Int.cast_natCast] at hb
  exact hb

end Main

end GlobalTheory.KeyIntegralVal
end
end
