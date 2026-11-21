import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsProjOverIsPullbackOfIsLocalization

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.model_finite_over_moduliModel_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* KA l) (C : Cpt Xo.s Xo.univ.t β₀) (b : O₀ →+* O) (_ : (ofModel Y).Above C b (pullback.fst _ _) Y.m0.toSABMap), IsDedFrac β₀ → IsDedFrac β → β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp β₀ → Y.Descends := by
  first | exact @GlobalTheory.descends_of_above | exact GlobalTheory.descends_of_above | (intros; apply GlobalTheory.descends_of_above <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem surjectiveOnStalks_of_dedekind_overring {O O' F : Type} [CommRing O] [IsDedekindDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] [CommRing O'] (β' : O' →+* F) (b : O →+* O') (hβ' : Function.Injective β')
    (h : ∀ x, β' (b x) = algebraMap O F x) : b.SurjectiveOnStalks := by
  intro P' hP'
  rw [RingHom.surjective_localRingHom_iff]
  intro s
  obtain ⟨x, y, hy, hs⟩ := IsFractionRing.div_surjective (A := O) (β' s)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap O F y ≠ 0 := fun e => hy0 (IsFractionRing.injective O F (by rw [e, map_zero]))
  have h1 : (1 : O') ∉ P' := P'.primeCompl.one_mem
  have key : ∀ u v : O, v * x = u * y → b v * s = b u := by
    intro u v e
    apply hβ'
    have e' := congrArg (algebraMap O F) e
    rw [map_mul, map_mul] at e'
    rw [map_mul, h, h, ← hs, ← mul_div_assoc, e', mul_div_assoc, div_self hyF, _root_.mul_one]
  by_cases hP : P'.comap b = ⊥
  · refine ⟨x, y, 1, h1, fun hm => hy0 ?_, by rw [_root_.one_mul, _root_.one_mul]; exact key x y (mul_comm _ _)⟩
    have : y ∈ P'.comap b := hm
    rwa [hP, Ideal.mem_bot] at this
  · have hd := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP
      (Localization.AtPrime (P'.comap b))
    have inj : Function.Injective (algebraMap O (Localization.AtPrime (P'.comap b))) :=
      IsLocalization.injective _ (P'.comap b).primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap O (Localization.AtPrime (P'.comap b)) x) (algebraMap O _ y)
    obtain ⟨u, v, rfl⟩ := IsLocalization.exists_mk'_eq (P'.comap b).primeCompl c
    have hv : b v ∉ P' := v.2
    rcases hc with hc | hc
    · have e : u * x = v * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      have e' := key _ _ e
      refine ⟨v, u, 1, h1, fun hm => hv ?_, by rw [_root_.one_mul, _root_.one_mul]; exact e'⟩
      rw [← e']
      exact P'.mul_mem_right _ hm
    · have e : v * x = u * y := by
        apply inj
        rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec' (Localization.AtPrime (P'.comap b)) u v]
        ring
      exact ⟨u, v, 1, h1, hv, by rw [_root_.one_mul, _root_.one_mul]; exact key _ _ e⟩

theorem flat_of_dedekind_of_injective {O O' : Type} [CommRing O] [IsDedekindDomain O] [CommRing O'] [IsDomain O']
    (b : O →+* O') (hb : Function.Injective b) : b.Flat := by
  algebraize [b]
  refine IsDedekindDomain.flat_iff_torsion_eq_bot.2 ?_
  rw [eq_bot_iff]
  rintro x ⟨a, ha⟩
  have ha' : b a * x = 0 := by
    rw [Submonoid.smul_def, Algebra.smul_def] at ha
    exact ha
  rcases mul_eq_zero.1 ha' with e | e
  · exact absurd (hb (by rw [e, map_zero])) (nonZeroDivisors.ne_zero a.2)
  · exact e

theorem isNormalScheme_of_flat_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [SurjectiveOnStalks f]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks f y
  obtain ⟨h₁, h₂⟩ := hX (f y)
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem Models.Cpt.exists_above_isIso_of_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  intro E _ _ _ H U F O _ _ c t β O' _ β' b C ν hν hβ hβ' hb
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, -⟩, -, hF'⟩ := hβ'
  have inj' : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  have hbx : ∀ x, β' (b x) = β x := fun x => congrArg (fun f : O →+* F => f x) hb
  have inj : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O F
  have injb : Function.Injective b := fun x y e => inj (by rw [← hbx, ← hbx, e])
  have hS : SurjectiveOnStalks (spMap b) := by
    letI := β.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2
      (surjectiveOnStalks_of_dedekind_overring β' b inj' hbx)
  have hFl : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact flat_of_dedekind_of_injective b injb
  have hS' : SurjectiveOnStalks (pullback.fst C.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip hS
  have hsp : spMap β' ≫ spMap b = spMap β := by
    rw [← hb, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hp : IsPullback (pullback.fst (pullback.snd C.s (spMap b)) (spMap β') ≫ pullback.fst C.s (spMap b))
      (pullback.snd (pullback.snd C.s (spMap b)) (spMap β')) C.s (spMap β) := by
    rw [← hsp]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have hj : ((C.jQ ≫ hp.isoPullback.inv) ≫ pullback.fst (pullback.snd C.s (spMap b)) (spMap β')) ≫
      pullback.fst C.s (spMap b) = C.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, hp.isoPullback_inv_fst]
  obtain ⟨t', ⟨mu⟩⟩ : ∃ t' : SAB H (pullback C.s (spMap b)), Nonempty (SABMap t' C.t (pullback.fst C.s (spMap b))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C.s (spMap b)) C.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t t' ((C.jQ ≫ hp.isoPullback.inv) ≫
      pullback.fst (pullback.snd C.s (spMap b)) (spMap β')), C.m.φ = m'.φ ≫ mu.φ := by
    have aux : ∀ (g : U ⟶ pullback C.s (spMap b)) (e : U ⟶ C.X) (n : SABMap t C.t e),
        g ≫ pullback.fst C.s (spMap b) = e → ∃ m' : SABMap t t' g, n.φ = m'.φ ≫ mu.φ := by
      rintro g e n rfl
      exact ObjMaps.exists_sab_cancel mu n
    exact aux _ _ C.m hj
  have := C.flat
  have := C.jQ_open
  have hr : Set.range (C.jQ ≫ hp.isoPullback.inv) = hp.isoPullback.hom ⁻¹' Set.range C.jQ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simp [hu]⟩
  have hiso : IsIso (pullback.lift (pullback.fst C.s (spMap b)) (pullback.snd C.s (spMap b)) pullback.condition) := by
    rw [pullback.lift_fst_snd]
    infer_instance
  refine ⟨⟨pullback C.s (spMap b), pullback.snd _ _,
    isNormalScheme_of_flat_of_surjectiveOnStalks (pullback.fst C.s (spMap b)) C.normal,
    ProjSpace.isProjOver_pullback_snd b C.proj, inferInstance, C.jQ ≫ hp.isoPullback.inv, ?_, inferInstance, ?_, t', m', ?_⟩,
    ⟨pullback.fst _ _, pullback.condition, inferInstance, mu, ?_, ?_⟩, hiso⟩
  · rw [Category.assoc, hp.isoPullback_inv_snd, C.jQ_over]
  · rw [hr]
    exact C.jQ_dense.preimage hp.isoPullback.hom.isOpenEmbedding.isOpenMap
  · rw [hr, ← C.ab_gen]
    ext x
    simp only [Set.mem_preimage]
    rw [← abLocus_pullback abLocusOne C.t.semi mu.cart.1, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hp.isoPullback_hom_fst]
  · exact hj.trans (Category.id_comp _).symm
  · refine hm'.symm.trans ?_
    rw [hν, Category.id_comp]

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_model_baseChange_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  first | exact @GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | exact GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | (intros; apply GlobalTheory.Models.Cpt.exists_above_isIso_of_overring <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.Domination

noncomputable def toRing {T : Scheme.{0}} {R : Type} [CommRing R] (u : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop).hom

theorem toRing_inj {T : Scheme.{0}} {R : Type} [CommRing R] {u v : T ⟶ Sp R} (h : toRing u = toRing v) : u = v := by
  apply ext_of_isAffine
  exact (cancel_epi _).1 (CommRingCat.hom_ext h)

theorem toRing_comp {T : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (u : T ⟶ Sp R') (b : R →+* R') :
    toRing (u ≫ spMap b) = (toRing u).comp b := by
  unfold toRing
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

theorem eq_of_overring {T : Scheme.{0}} {O O' F : Type} [CommRing O] [CommRing O'] [Field F] {β : O →+* F}
    {β' : O' →+* F} {b : O →+* O'} (hβ : IsDedFrac β) (hβ' : IsDedFrac β') (hb : β'.comp b = β) (u : T ⟶ Sp O')
    (w : T ⟶ Sp F) (h : u ≫ spMap b = w ≫ spMap β) : u = w ≫ spMap β' := by
  obtain ⟨⟨_, -⟩, -, hf⟩ := hβ
  obtain ⟨-, -, hf'⟩ := hβ'
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  rw [toRing_comp]
  ext x
  letI := β.toAlgebra
  have hinj : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  obtain ⟨p, q, hq, e⟩ := IsFractionRing.div_surjective (A := O) (β' x)
  have hq0 : β q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have e' : β' x * β q = β p := by
    rw [← e]; exact div_mul_cancel₀ _ hq0
  have e₂ : x * b q = b p := by
    apply hinj
    rw [map_mul]
    have := RingHom.congr_fun hb
    simp only [RingHom.comp_apply] at this
    rw [this, this, e']
  have hu : IsUnit (toRing w (β q)) := (IsUnit.mk0 _ hq0).map _
  have k₁ : ∀ y, toRing u (b y) = toRing w (β y) := RingHom.congr_fun h'
  apply hu.mul_right_cancel
  rw [RingHom.comp_apply, ← map_mul, e', ← k₁, ← k₁, ← map_mul, e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_RZ {T : Scheme.{0}} {l : Level H} {S A : ℕ} (hA : l.A = A) {β : RZ H S A →+* KA l}
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) (u v : T ⟶ Sp (KA l))
    (h : u ≫ spMap β = v ≫ spMap β) : u = v := by
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  have k₁ : ∀ y, toRing u (β y) = toRing v (β y) := RingHom.congr_fun h'
  have k₂ : ∀ (x : ℂ) (hx : x ∈ KA l), x ∈ RZ H S A → toRing u ⟨x, hx⟩ = toRing v ⟨x, hx⟩ := fun x hx hx' => by
    have : β ⟨x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext (hβ _)
    rw [← this, k₁]
  let K : Subfield ℂ := ((toRing u).eqLocusField (toRing v)).map (KA l).val.toRingHom
  have hK : (KA l).toSubfield ≤ K := by
    have : KA l ≤ K.toIntermediateField (fun x => by simp) := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · have m₁ : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)
        have m₂ : H.rt0 ∈ RZ H S A := by
          have : H.rt0 = (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1 := by ring
          rw [this]
          exact sub_mem (add_mem m₁ m₁) (one_mem _)
        exact ⟨(baseKA l).ρ, k₂ _ _ m₂, rfl⟩
      · exact ⟨(baseKA l).ζ, k₂ _ _ (Subring.subset_closure (by simp [hA])), rfl⟩
    exact this
  ext x
  obtain ⟨y, hy, e⟩ := hK x.2
  have : y = x := Subtype.ext e
  exact this ▸ hy

theorem dominates_of_map_to_base : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c O O' _ _ β β' Y Y' b f t m₁ m₂ r ν k hβ hβ' hb hR hν hk hr hf hφ
  obtain ⟨b₀, r₀, ν₀, hb₀, hν₀, ⟨a₀⟩⟩ := hR

  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.eta x).trans (Y'.m0.eta x).symm)
  have η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.etaA x).trans (Y'.m0.etaA x).symm)
  obtain ⟨ν₁, hν₁⟩ := LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)
  have hl₁ : LevComp Y.oF (Xo l₀).univ r₀ ν₁ := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hν₀.1]
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hν₀.2]
  have hkb : k.comp B.β = β'.comp b₀ := RingHom.ext fun x => Subtype.ext
    ((hk (B.β x)).trans ((B.β_inc x).trans (hb₀ x).symm))
  have hrB : r ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap (β'.comp b₀) := by
    rw [Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc, hr, Category.assoc, ← spMap_comp, hkb]
  have hrr : r ≫ (Xo l₀).s = r₀ ≫ (Xo l₀).s := by
    apply eq_of_RZ B.A_one B.β_inc
    rw [Category.assoc, Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, hrB, ← Category.assoc, ← a₀.j_comm, Category.assoc,
      a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  have hred : IsReduced ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨rfl, hνν⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r r₀ ν ν₁ hred hrr hν hl₁

  obtain ⟨ido, hid⟩ := ObjMaps.exists_sab_id Y.oF.t
  obtain ⟨C, a, hiso⟩ := GlobalTheory.T.exists_model_baseChange_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid hβ hβ' hb
  obtain ⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π),
      IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ :=
    ⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩
  have hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ (Xo l).XF c),
      u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e := fun S u x h => by
    apply pullback.hom_ext
    · rw [h, Category.assoc, Category.assoc, e₁, hj]
    · rw [Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]
      apply eq_of_overring hβ hβ' hb
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))
  have hjf : C.j ≫ e ≫ f = r ≫ B.C.j := by
    rw [← Category.assoc]
    exact hf _ (by rw [Category.assoc, e₁, hj])
  obtain ⟨κ, hκ⟩ := LevelCover.sab_cancel m₁ mu e e₁
  obtain ⟨κ₂, hκ₂⟩ := LevelCover.sab_comp κ m₂ rfl
  have hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ := by
    rw [Category.assoc, hκ, hm]
  have hover : (e ≫ f) ≫ B.C.s = C.s ≫ spMap ((RingHom.id O').comp b₀) := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ'
    letI := β'.toAlgebra
    obtain ⟨-, -, -, -, -, h3, -⟩ :=
      GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
    have : IsDominant C.j := h3
    have : IsReduced C.X := by
      have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
        have := (C.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk _
    apply ext_of_isDominant C.j
    rw [← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  obtain ⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩ := Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C
    (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl
    (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp])
    (by rw [hκ₂, ← Category.assoc, hφ _ hm₁, hνν, hν₁, Category.assoc])
  obtain ⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧
      C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ :=
    ⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩
  obtain ⟨idt, hid'⟩ := ObjMaps.exists_sab_id t
  obtain ⟨κi, hκi⟩ := LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)
  obtain ⟨m₃, hm₃⟩ := LevelCover.sab_comp κi κ' rfl
  have hκκ : κ.φ ≫ κi.φ = 𝟙 _ := by
    apply κ.cart.1.hom_ext
    · change (κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ
      rw [Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]
    · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
      have w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e := κi.cart.1.w
      rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  refine ⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  · rw [Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]
  · rw [hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]
  · have w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
    have s₂ : g₂ = g₁ ≫ ν'.φ := by
      apply Y'.m0.toSABMap.cart.1.hom_ext
      · change g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ
        rw [Category.assoc, hν', q₂]
      · rw [Category.assoc, w₀, q₃]
    have s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ := by
      apply m₁.cart.1.hom_ext
      · change g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ
        rw [Category.assoc, hm₁, q₁]
      · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
        have w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j := C.m.cart.1.w
        have w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _ := m₁.cart.1.w
        have w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
        rw [hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by
          rw [Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]
        simp only [Category.assoc]
        rw [w₁, reassoc_of% w₂]
    rw [s₁, s₂, hm₃]
    simp only [Category.assoc]
    rw [reassoc_of% hκκ, hmh]

end GlobalTheory.Models.Domination
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_dominated_of_map_to_baseModel : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  first | exact @GlobalTheory.Models.Domination.dominates_of_map_to_base | exact GlobalTheory.Models.Domination.dominates_of_map_to_base | (intros; apply GlobalTheory.Models.Domination.dominates_of_map_to_base <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_triple_glue_two_opens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.TripleGlue.exists_sab_glue | exact GlobalTheory.TripleGlue.exists_sab_glue | (intros; apply GlobalTheory.TripleGlue.exists_sab_glue <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

def DensePart {X X₀ : Scheme.{0}} (j : X₀ ⟶ X) : Prop :=
  (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion j ∧ Flat j ∧
    IsDominant j ∧ QuasiCompact j

theorem DensePart.restrict {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) (i : Y ⟶ X) [IsOpenImmersion i]
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) : DensePart k := by
  obtain ⟨⟨hn, z, hz₁, hz₂⟩, h₁, h₂, h₃, h₄⟩ := h
  have sq : IsPullback (𝟙 X₀) k j i := IsPullback.of_horiz_isIso_mono ⟨by rw [hk, Category.id_comp]⟩
  refine ⟨⟨fun y => ?_, i ≫ z, inferInstance, inferInstance⟩, MorphismProperty.of_isPullback sq h₁,
    MorphismProperty.of_isPullback sq h₂, ⟨?_⟩, MorphismProperty.of_isPullback sq h₄⟩
  · obtain ⟨_, _⟩ := hn (i y)
    have e := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · have e : Set.range k = i ⁻¹' Set.range j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hk, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, i.isOpenEmbedding.injective (by rw [← hx, ← hk, Scheme.Hom.comp_apply])⟩
    rw [DenseRange, e]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_fac {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {t₀ : SAB H X₀} {t : SAB H X} (a : SABMap t₀ t j) (i : Y ⟶ X)
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) :
    ∃ (s : SAB H Y) (b : SABMap t₀ s k) (m : SABMap s t i), b.φ ≫ m.φ = a.φ := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull i t
  obtain ⟨a', ha'⟩ := exists_cast a hk.symm
  obtain ⟨b, hb⟩ := ObjMaps.exists_sab_cancel m a'
  exact ⟨_, b, m, hb.symm.trans ha'⟩

theorem DensePart.generic {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} {t : SAB H X}
    (a : SABMap t₀ t j) (hp : IsProper t₀.G.hom) : IsReduced X ∧ genericPoints X ⊆ abLocus t.G := by
  obtain ⟨hX, h₁, h₂, h₃, h₄⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX.1 x).1
    infer_instance
  exact ⟨isReduced_of_isReduced_stalk X,
    (densePart_basic X X₀ j h₁ h₂ h₃ h₄).1.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩

section

variable (hdvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
include hdvr

theorem DensePart.exists_map {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {k : X₀ ⟶ Y} (h : DensePart k) {i : Y ⟶ X}
    (hk : k ≫ i = j) {t₀ : SAB H X₀} {t : SAB H X} {s : SAB H Y} (a : SABMap t₀ t j) (b : SABMap t₀ s k)
    (hp : IsProper t₀.G.hom) : ∃ n : SABMap s t i, b.φ ≫ n.φ = a.φ := by
  obtain ⟨s', b', m, hm⟩ := exists_fac a i hk
  obtain ⟨c, hc⟩ := exists_sabMap_id_of_common_generic hdvr E H Y X₀ k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    t₀ s s' b b' hp
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m c
  obtain ⟨n', hn'⟩ := exists_cast n (Category.id_comp i)
  exact ⟨n', by rw [hn', hn, ← Category.assoc, hc, hm]⟩

theorem DensePart.glue_top {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {jU : X₀ ⟶ U.toScheme} {jV : X₀ ⟶ V.toScheme} (hU : jU ≫ U.ι = j) (hV : jV ≫ V.ι = j) {t₀ : SAB H X₀}
    {t₁ : SAB H U.toScheme} {t₂ : SAB H V.toScheme} (a₁ : SABMap t₀ t₁ jU) (a₂ : SABMap t₀ t₂ jV)
    (hp : IsProper t₀.G.hom) : ∃ t : SAB H X, Nonempty (SABMap t₀ t j) := by
  have hr : Set.range j ⊆ Set.range (U ⊓ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨by rw [← hU]; exact (jU x).2, by rw [← hV]; exact (jV x).2⟩
  obtain ⟨k, hk⟩ : ∃ k : X₀ ⟶ (U ⊓ V).toScheme, k ≫ (U ⊓ V).ι = j := ⟨_, IsOpenImmersion.lift_fac _ j hr⟩
  have hkU : k ≫ X.homOfLE inf_le_left = jU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hk, hU]
  have hkV : k ≫ X.homOfLE inf_le_right = jV := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hk, hV]
  obtain ⟨s, b, m₁, -⟩ := exists_fac a₁ _ hkU
  obtain ⟨m₂, -⟩ := (h.restrict _ hk).exists_map hdvr hkV a₂ b hp
  obtain ⟨t, n₁, -, -⟩ := GlobalTheory.T.exists_triple_glue_two_opens E H X U V t₁ t₂ s m₁ m₂ hUV ((h.restrict _ hU).generic a₁ hp)
    ((h.restrict _ hV).generic a₂ hp)
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n₁ a₁
  obtain ⟨n', -⟩ := exists_cast n hU
  exact ⟨t, ⟨n'⟩⟩

omit hdvr in

theorem exists_trace {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (i : Y ⟶ X) {k : X₀ ⟶ Y} (hk : k ≫ i = j) {U : X.Opens}
    {jU : X₀ ⟶ U.toScheme} (hU : jU ≫ U.ι = j) {t₀ : SAB H X₀} {t : SAB H U.toScheme} (a : SABMap t₀ t jU) :
    ∃ (k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme) (s : SAB H (i ⁻¹ᵁ U).toScheme),
      k' ≫ (i ⁻¹ᵁ U).ι = k ∧ Nonempty (SABMap t₀ s k') := by
  have hr : Set.range k ⊆ Set.range (i ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show i (k x) ∈ U
    rw [← Scheme.Hom.comp_apply, hk, ← hU]
    exact (jU x).2
  obtain ⟨k', hk'⟩ : ∃ k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme, k' ≫ (i ⁻¹ᵁ U).ι = k := ⟨_, IsOpenImmersion.lift_fac _ k hr⟩
  have e : k' ≫ (i ∣_ U) = jU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk', hk, hU]
  obtain ⟨s, b, -, -⟩ := exists_fac a _ e
  exact ⟨k', s, hk', ⟨b⟩⟩

theorem DensePart.glue_sup {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} (hp : IsProper t₀.G.hom)
    {U V : X.Opens}
    (hU : ∃ (k : X₀ ⟶ U.toScheme) (s : SAB H U.toScheme), k ≫ U.ι = j ∧ Nonempty (SABMap t₀ s k))
    (hV : ∃ (k : X₀ ⟶ V.toScheme) (s : SAB H V.toScheme), k ≫ V.ι = j ∧ Nonempty (SABMap t₀ s k)) :
    ∃ (k : X₀ ⟶ (U ⊔ V).toScheme) (s : SAB H (U ⊔ V).toScheme), k ≫ (U ⊔ V).ι = j ∧ Nonempty (SABMap t₀ s k) := by
  obtain ⟨jU, t₁, hU, ⟨a₁⟩⟩ := hU
  obtain ⟨jV, t₂, hV, ⟨a₂⟩⟩ := hV
  have hk : (jU ≫ X.homOfLE le_sup_left) ≫ (U ⊔ V).ι = j := by rw [Category.assoc, Scheme.homOfLE_ι, hU]
  obtain ⟨k₁, s₁, hk₁, ⟨b₁⟩⟩ := exists_trace _ hk hU a₁
  obtain ⟨k₂, s₂, hk₂, ⟨b₂⟩⟩ := exists_trace _ hk hV a₂
  have hc : (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  obtain ⟨t, ha⟩ := (h.restrict _ hk).glue_top hdvr hc hk₁ hk₂ b₁ b₂ hp
  exact ⟨_, t, hk, ha⟩

end

end GlobalTheory.TripleGlue

theorem GlobalTheory.exists_sab_glue_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  intro hdvr E _ _ _ H X X₀ j t₀ I _ U jU t a hI hX h₁ h₂ h₃ h₄ hp hcov hj
  have h : TripleGlue.DensePart j := ⟨hX, h₁, h₂, h₃, h₄⟩
  have := Fintype.ofFinite I
  have key : ∃ (k : X₀ ⟶ (Finset.univ.sup' Finset.univ_nonempty U).toScheme) (s : SAB H _),
      k ≫ (Finset.univ.sup' Finset.univ_nonempty U).ι = j ∧ Nonempty (SABMap t₀ s k) :=
    Finset.sup'_induction (p := fun W : X.Opens => ∃ (k : X₀ ⟶ W.toScheme) (s : SAB H W.toScheme),
      k ≫ W.ι = j ∧ Nonempty (SABMap t₀ s k)) _ _ (fun _ hU _ hV => h.glue_sup hdvr hp hU hV)
      (fun i _ => ⟨jU i, t i, hj i, ⟨a i⟩⟩)
  rw [Finset.sup'_univ_eq_ciSup, hcov] at key
  obtain ⟨k, s, hk, ⟨b⟩⟩ := key
  have e : j ≫ X.topIso.inv = k := by
    rw [← hk, Category.assoc]
    exact (congrArg (k ≫ ·) X.topIso.hom_inv_id).trans (Category.comp_id _)
  obtain ⟨t', a', -, -⟩ := TripleGlue.exists_fac b _ e
  choose n hn using fun i => (h.restrict _ (hj i)).exists_map hdvr (hj i) a' (a i) hp
  exact ⟨t', a', n, hn⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  first | exact @GlobalTheory.exists_sab_glue_of_common_generic | exact GlobalTheory.exists_sab_glue_of_common_generic | (intros; apply GlobalTheory.exists_sab_glue_of_common_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.JoinModels

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isPullback_toImage_comp {U P Z : Scheme.{0}} (j : U ⟶ P) (q : P ⟶ Z) (v : U ⟶ Z)
    (h : j ≫ q = v) [QuasiCompact j] [IsSeparated q] [Flat v] [Mono v] :
    IsPullback (𝟙 U) j.toImage v (j.imageι ≫ q) := by
  have Hu := IsPullback.of_hasPullback v q
  have : Mono (pullback.snd v q) := inferInstance
  let c : U ⟶ pullback v q := pullback.lift (𝟙 U) j (by simpa using h.symm)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have H := (GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ hc₂).paste_horiz Hu
  rwa [hc₁] at H

theorem exists_common_projective {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ j ≫ p i = u i := by
  classical
  have key : ∀ S : Finset I, ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i ∈ S, ∃ p : P ⟶ X i, p ≫ s i = r ∧ j ≫ p = u i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨X i, s i, u i, hs i, hu i, by simp⟩
    | insert k S _ ih =>
      obtain ⟨P, r, j, h1, h2, h3⟩ := ih
      refine ⟨pullback r (s k), pullback.fst _ _ ≫ r, pullback.lift j (u k) (h2.trans (hu k).symm),
        GlobalTheory.ProjSpace.isProjOver_pullback h1 (hs k), by rw [pullback.lift_fst_assoc, h2], fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨p, hp1, hp2⟩ := h3 i hi
        exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp1], by rw [pullback.lift_fst_assoc, hp2]⟩
  have := Fintype.ofFinite I
  obtain ⟨P, r, j, h1, h2, h3⟩ := key Finset.univ
  choose p hp using fun i => h3 i (Finset.mem_univ i)
  exact ⟨P, r, j, p, h1, h2, hp⟩

theorem isProper_of_proj {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str O N
  infer_instance

theorem exists_join {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) [∀ i, Flat (u i)] [∀ i, Mono (u i)]
    [∀ i, QuasiCompact (u i)] :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ IsPullback (𝟙 U) j (u i) (p i) := by
  obtain ⟨P, r, j, p, h1, h2, h3⟩ := exists_common_projective σ X s hs u hu
  have := isProper_of_proj h1
  have hsep : ∀ i, IsSeparated (p i) := fun i => by
    have : IsSeparated (p i ≫ s i) := by rw [(h3 i).1]; infer_instance
    exact IsSeparated.of_comp (p i) (s i)
  have : QuasiCompact j := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have : QuasiCompact (j ≫ p i) := by rw [(h3 i).2]; infer_instance
    exact QuasiCompact.of_comp j (p i)
  obtain ⟨N, e, he, hr⟩ := h1
  refine ⟨j.image, j.imageι ≫ r, j.toImage, fun i => j.imageι ≫ p i,
    ⟨N, j.imageι ≫ e, inferInstance, by rw [Category.assoc, hr]⟩, by simpa using h2, fun i => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h3 i).1]
  · exact isPullback_toImage_comp j (p i) (u i) (h3 i).2

theorem exists_join_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  intro E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hR _ _
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  have hβ : algebraMap O F = β := rfl
  have hcl : ∀ i, ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (κ : (C i).X ⟶ X'), IsProjOver s' ∧
      IsPullback κ (C i).s s' (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact GlobalTheory.ProjClosure.exists_projective_closure O (R i) (a i) (C i).X (C i).s (C i).proj
  choose X' s' κ hs' hk using hcl
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hko : ∀ i, IsOpenImmersion (κ i) := fun i => MorphismProperty.of_isPullback (hk i).flip (hbo i)
  have hj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ QuasiCompact (C i).j ∧ QuasiCompact (κ i) :=
    fun i => by
      obtain ⟨⟨⟨_, _⟩, _, hfr⟩, _, _⟩ := hR i
      letI := (ω i).toAlgebra
      obtain ⟨-, -, -, h1, h2, -, h3⟩ := GlobalTheory.genericPart_dense_proOpen (R i) F (C i).X U (C i).s (C i).jQ
        (C i).flat (C i).proj (C i).jQ_open (C i).jQ_dense
      exact ⟨h1, h2, h3, MorphismProperty.of_isPullback (hk i).flip inferInstance⟩
  have hωb : ∀ i, spMap (ω i) ≫ spMap (b i) = spMap β := fun i => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, (hR i).2.1]
  have hjs : ∀ i, (C i).j ≫ (C i).s = c ≫ spMap (ω i) := fun i => by
    rw [Cpt.j, Category.assoc, pullback.condition, reassoc_of% (C i).jQ_over]
  have h1 := fun i => (hj i).1
  have h2 := fun i => (hj i).2.1
  have h3 := fun i => (hj i).2.2.1
  have h4 := fun i => (hj i).2.2.2
  obtain ⟨P, r, j, p, hr, hjr, hp⟩ := exists_join (c ≫ spMap β) X' s' hs' (fun i => (C i).j ≫ κ i)
    (fun i => by rw [Category.assoc, (hk i).w, reassoc_of% (hjs i), hωb])
  have hjp : ∀ i, j ≫ p i = (C i).j ≫ κ i := fun i => by simpa using (hp i).2.w.symm
  let jP : U ⟶ pullback r (spMap β) := pullback.lift j c hjr
  have hjP₁ : jP ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have hjP₂ : jP ≫ pullback.snd _ _ = c := pullback.lift_snd _ _ _
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U :=
    isNormalScheme_of_flat_preimmersion (C i₀).j (C i₀).normal
  have hjPo : IsOpenImmersion jP := by
    have G := (IsPullback.of_hasPullback (C i₀).s (spMap (ω i₀))).flip.paste_vert (hk i₀).flip
    rw [hωb] at G
    let ρ : pullback r (spMap β) ⟶ pullback (C i₀).s (spMap (ω i₀)) :=
      G.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p i₀)
        (by rw [Category.assoc, (hp i₀).1, pullback.condition])
    have hρ₁ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ := G.lift_fst _ _ _
    have hρ₂ : ρ ≫ pullback.fst _ _ ≫ κ i₀ = pullback.fst _ _ ≫ p i₀ := G.lift_snd _ _ _
    have A : IsPullback ρ (pullback.fst r (spMap β)) (pullback.fst _ _ ≫ κ i₀) (p i₀) := by
      refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := s' i₀) (v₁₃ := spMap β) ?_ hρ₂ G
      rw [hρ₁, (hp i₀).1]
      exact (IsPullback.of_hasPullback _ _).flip
    have B : IsPullback (𝟙 U) jP (C i₀).jQ ρ := by
      refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) (v₂₂ := pullback.fst _ _ ≫ κ i₀) (h₃₁ := p i₀)
        ?_ ?_ A
      · rw [hjP₁, ← Category.assoc]
        exact (hp i₀).2
      · refine G.hom_ext ?_ ?_
        · rw [Category.id_comp, Category.assoc, hρ₁, hjP₂, (C i₀).jQ_over]
        · rw [Category.id_comp, Category.assoc, hρ₂, reassoc_of% hjP₁, hjp, Cpt.j, Category.assoc]
    exact MorphismProperty.of_isPullback B (C i₀).jQ_open
  obtain ⟨Y, π, jQ, -, hY, hproj, hflat, hq₁, hq₂, hqo, hqd, hqr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O F P U r c j jP.opensRange jP.isoOpensRange.hom hr hU inferInstance
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₁)
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₂)
  let f : ∀ i, pullback (π ≫ r) (spMap (b i)) ⟶ (C i).X := fun i =>
    (hk i).lift (pullback.fst _ _ ≫ π ≫ p i) (pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, (hp i).1, pullback.condition])
  have hf : ∀ i, f i ≫ κ i = pullback.fst _ _ ≫ π ≫ p i := fun i => (hk i).lift_fst _ _ _
  refine ⟨Y, π ≫ r, jQ, f, hY, hproj, hflat, hq₁, hqo, hqd, fun i => ⟨(hk i).lift_snd _ _ _, ?_, ?_⟩⟩
  · intro g hg
    have hq₂' : jQ ≫ pullback.fst (π ≫ r) (spMap β) ≫ π = j := hq₂
    rw [← cancel_mono (κ i), Category.assoc, hf, reassoc_of% hg, reassoc_of% hq₂', hjp]
  · rintro x ⟨y, hy⟩
    have e1 : p i (π (pullback.fst (π ≫ r) (spMap (b i)) x)) = ((C i).j ≫ κ i) y := by
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply (f i), hf]
      simp only [Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hp i).2 y _ e1.symm
    obtain ⟨w, hw⟩ : pullback.fst (π ≫ r) (spMap (b i)) x ∈ Set.range (pullback.fst (π ≫ r) (spMap β)) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨c z, ?_⟩
      rw [Scheme.Hom.comp_apply π r, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjr]
    obtain ⟨v, hv⟩ := (hqr w).mpr ⟨jP.isoOpensRange.hom z, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact (congrArg (fun m : U ⟶ P => m z) hjP₁).trans (hz.trans (congrArg π hw.symm))⟩
    exact ⟨v, by rw [Scheme.Hom.comp_apply, ← hw]; exact congrArg _ hv⟩

end GlobalTheory.JoinModels
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_join_normal_projective_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  first | exact @GlobalTheory.JoinModels.exists_join_scheme | exact GlobalTheory.JoinModels.exists_join_scheme | (intros; apply GlobalTheory.JoinModels.exists_join_scheme <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace ModelJoin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isOpenImmersion_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : IsOpenImmersion (spMap b) := by
  letI := b.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := O) (S := R) a

theorem mem_range_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) (x : Sp O) (hx : a ∉ x.asIdeal) :
    x ∈ Set.range (spMap b) := by
  letI := b.toAlgebra
  have := PrimeSpectrum.localization_away_comap_range R a
  have h2 : (x : PrimeSpectrum O) ∈ Set.range (PrimeSpectrum.comap (algebraMap O R)) := by
    rw [this]; exact hx
  exact h2

theorem arith_base (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] :
    LocallyOfFiniteType (spMap (algebraMap ℤ O)) ∧ Flat (spMap (algebraMap ℤ O)) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end ModelJoin

open ModelJoin

theorem exists_join_of_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  intro hext E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hω hspan hft hprop
  obtain ⟨⟨hdom, hded⟩, hchar, hfrac⟩ := id hβ
  obtain ⟨X, s, jQ, f, hn, hproj, hflat, hover, hopen, hdense, hf⟩ :=
    GlobalTheory.T.exists_join_normal_projective_models E H U F O c t β I R a b ω C hβ hω hspan hchar
  have hpo : IsPreimmersion (jQ ≫ pullback.fst s (spMap β)) ∧ Flat (jQ ≫ pullback.fst s (spMap β)) ∧
      IsDominant (jQ ≫ pullback.fst s (spMap β)) ∧ QuasiCompact (jQ ≫ pullback.fst s (spMap β)) := by
    letI := β.toAlgebra
    exact (genericPart_dense_proOpen O F X U s jQ hflat hproj hopen hdense).2.2.2
  have hβp : IsPreimmersion (spMap β) := by
    letI := β.toAlgebra
    exact IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  have hfp : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβp
  have hb : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => isOpenImmersion_away (a i) (b i) (hω i).2.2
  have hβe : ∀ i, spMap β = spMap (ω i) ≫ spMap (b i) := fun i => by
    rw [← (hω i).2.1]; exact Spec.map_comp (CommRingCat.ofHom (b i)) (CommRingCat.ofHom (ω i))
  have hsp : IsProper s := projProper O X s hproj
  let V : I → X.Opens := fun i => (pullback.fst s (spMap (b i))).opensRange
  let e : ∀ i, pullback s (spMap (b i)) ≅ (V i).toScheme := fun i =>
    (pullback.fst s (spMap (b i))).isoOpensRange
  have he : ∀ i, (e i).hom ≫ (V i).ι = pullback.fst s (spMap (b i)) := fun i =>
    Scheme.Hom.isoOpensRange_hom_ι _
  have hcov' : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst s (spMap (b i))) := by
    intro x
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hc
      push Not at hc
      refine (s x).isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact mem_range_away (a i) (b i) (hω i).2.2 _ hi
  have hcov : ⨆ i, V i = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov' x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hw : ∀ i, (jQ ≫ pullback.fst s (spMap β)) ≫ s = (c ≫ spMap (ω i)) ≫ spMap (b i) := fun i => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc, ← hβe]
  let g : ∀ i, U ⟶ pullback s (spMap (b i)) := fun i => pullback.lift _ _ (hw i)
  have hg : ∀ i, g i ≫ pullback.fst _ _ = jQ ≫ pullback.fst s (spMap β) := fun i => pullback.lift_fst _ _ _
  choose tV mV using fun i => exists_pull ((e i).inv ≫ f i) (C i).t
  replace mV := fun i => (mV i).some
  choose t₁ k using fun i => exists_pull (e i).hom (tV i)
  replace k := fun i => (k i).some
  choose aV haV using fun i => cancel_of_eq (g := g i ≫ (e i).hom) (mV i) (C i).m (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact (hf i).2.1 _ (hg i))
  obtain ⟨hz₁, hz₂⟩ := arith_base O
  obtain ⟨t', a', n, hn'⟩ := GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart hext E H X U (jQ ≫ pullback.fst s (spMap β)) t I V
    (fun i => g i ≫ (e i).hom) tV aV inferInstance
    ⟨hn, s ≫ spMap (algebraMap ℤ O), inferInstance, inferInstance⟩ hpo.1 hpo.2.1 hpo.2.2.1 hpo.2.2.2 hprop hcov
    (fun i => by rw [Category.assoc, he, hg])
  choose m₁ hm₁ using fun i => comp_of_eq (n i) (k i) (he i)
  choose m₂ hm₂ using fun i => comp_of_eq (h := f i) (mV i) (k i) (Iso.hom_inv_id_assoc _ _)
  have hab : pullback.fst s (spMap β) ⁻¹' abLocus t'.G = Set.range jQ := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, w, hw'⟩ := hcov' (pullback.fst s (spMap β) z)
      have h1 : w ∈ abLocus (t₁ i).G :=
        (abLocus_pullback abLocusOne t'.semi (m₁ i).cart.1 w).1 (by rw [hw']; exact hz)
      have h2 : f i w ∈ abLocus (C i).t.G :=
        (abLocus_pullback abLocusOne (C i).t.semi (m₂ i).cart.1 w).2 h1
      have h3 : f i w ∈ Set.range (pullback.fst (C i).s (spMap (ω i))) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨pullback.snd s (spMap β) z, (spMap (b i)).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hβe, ← Scheme.Hom.comp_apply, ← pullback.condition,
          ← Scheme.Hom.comp_apply (f i), (hf i).1, ← Scheme.Hom.comp_apply, ← pullback.condition,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw']
      obtain ⟨z', hz'⟩ := h3
      have h4 : z' ∈ Set.range (C i).jQ := by
        rw [← (C i).ab_gen]
        show _ ∈ abLocus (C i).t.G
        rw [hz']; exact h2
      obtain ⟨u, hu⟩ := h4
      obtain ⟨u', hu'⟩ := (hf i).2.2 w ⟨u, by rw [Cpt.j, Scheme.Hom.comp_apply, hu, hz']⟩
      refine ⟨u', (pullback.fst s (spMap β)).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hu', hw']
    · rintro _ ⟨u, rfl⟩
      exact range_subset_abLocus_of_isProper t'.semi a'.cart.1 ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  refine ⟨⟨X, s, hn, hproj, hflat, jQ, hover, hopen, hdense, t', a', hab⟩, fun i => ?_⟩
  refine ⟨f i, t₁ i, m₁ i, m₂ i, (hf i).1, (hf i).2.1, fun y hy => ?_⟩
  have hmono : IsOpenImmersion (n i).φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n i).cart.1.flip inferInstance
  have hy' : y ≫ (k i).φ = (aV i).φ := by
    rw [← cancel_mono (n i).φ, Category.assoc, ← hm₁, hn']; exact hy
  rw [hm₂, ← Category.assoc, hy', haV]

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_dominating_models_on_open_cover : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  first | exact @GlobalTheory.exists_join_of_models | exact GlobalTheory.exists_join_of_models | (intros; apply GlobalTheory.exists_join_of_models <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GlobalModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isLocalization_away {S A : ℕ} (hS : 0 < S) (b : RZ H 1 A →+* RZ H S A)
    (hb : IsInc (RZ H 1 A).subtype (RZ H S A).subtype b) :
    @IsLocalization.Away (RZ H 1 A) _ (S : RZ H 1 A) (RZ H S A) _ b.toAlgebra := by
  letI := b.toAlgebra
  have hS' : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hb' : ∀ x, ((b x : RZ H S A) : ℂ) = x := hb
  have key : ∀ z ∈ RZ H S A, ∃ (n : ℕ) (a : RZ H 1 A), z * (S : ℂ) ^ n = a := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inl rfl)⟩, by simp⟩
      · exact ⟨1, 1, by simp [hS']⟩
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inr (Or.inr rfl))⟩, by simp⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      refine ⟨n + m, a * (S : RZ H 1 A) ^ m + c * (S : RZ H 1 A) ^ n, ?_⟩
      push_cast
      rw [← ha, ← hc]; ring
    | neg x _ hx =>
      obtain ⟨n, a, ha⟩ := hx
      exact ⟨n, -a, by push_cast; rw [← ha]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      exact ⟨n + m, a * c, by push_cast; rw [← ha, ← hc]; ring⟩
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun x y h => ⟨0, ?_⟩)
  · refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext ?_)
    simp [hS']
  · obtain ⟨n, a, ha⟩ := key z.1 z.2
    refine ⟨n, a, Subtype.ext ?_⟩
    rw [map_natCast]
    refine Eq.trans ?_ (ha.trans (hb' a).symm)
    push_cast
    rfl
  · have : x = y := Subtype.ext ((hb' x).symm.trans ((congrArg Subtype.val h).trans (hb' y)))
    rw [this]

theorem span_natCast_eq_top {R I : Type} [CommRing R] (a : I → ℕ) (h : ∀ p : ℕ, p.Prime → ∃ i, ¬ p ∣ a i) :
    Ideal.span (Set.range fun i => (a i : R)) = ⊤ := by
  set J := Ideal.span (Set.range fun i => (a i : R))
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (J.comap (Int.castRingHom R))).principal
  have hd : ∀ i, g ∣ (a i : ℤ) := fun i => by
    rw [← Ideal.mem_span_singleton]
    change _ ∈ Submodule.span ℤ {g}
    rw [← hg, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h1 : g.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨i, hi⟩ := h p hp
    exact hi (hpg.trans (Int.natAbs_dvd_natAbs.mpr (hd i)))
  have hu : IsUnit g := Int.isUnit_iff_natAbs_eq.mpr h1
  have hm : g ∈ J.comap (Int.castRingHom R) := hg ▸ Submodule.mem_span_singleton_self g
  exact Ideal.eq_top_of_isUnit_mem _ hm (hu.map _)

theorem finite_parts (l : Level H) : Finite {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p} := by
  refine Finite.of_injective (fun x => (⟨x.1.M, ?_⟩ : Set.Iic l.M)) ?_
  · obtain ⟨p, -, -, h, -⟩ := x.2
    exact h ▸ Nat.div_le_self _ _
  · rintro ⟨⟨M, _, _, Mb, _, _, _, A, _⟩, p, _, h₁, _, h₃⟩ ⟨⟨M', _, _, Mb', _, _, _, A', _⟩, p', _, h₁', _, h₃'⟩ h
    obtain rfl : M = M' := congrArg Subtype.val h
    obtain rfl : A = A' := h₁.trans h₁'.symm
    obtain rfl : Mb = Mb' := h₃.trans h₃'.symm
    rfl

theorem exists_map_to_base {U U'' U₀ : Scheme.{0}} {F F'' F₀ O O'' O₀ R V : Type} [Field F] [Field F''] [Field F₀]
    [CommRing O] [CommRing O''] [CommRing O₀] [CommRing R] [CommRing V]
    {c : U ⟶ Sp F} {c'' : U'' ⟶ Sp F''} {c₀ : U₀ ⟶ Sp F₀} {t : SAB H U} {t'' : SAB H U''} {t₀ : SAB H U₀}
    {β : O →+* F} {β'' : O'' →+* F''} {β₀ : O₀ →+* F₀} {ω : R →+* F}
    {C' : Cpt c t β} {C'' : Cpt c'' t'' β''} {C₀ : Cpt c₀ t₀ β₀} {C₁ : Cpt c t ω}
    {b'' : O →+* O''} {r'' : U'' ⟶ U} {ν'' : SABMap t'' t r''} (A'' : C''.Above C' b'' r'' ν'')
    {b₀ : O₀ →+* R} {r : U ⟶ U₀} {ν : SABMap t t₀ r} (A₁ : C₁.Above C₀ b₀ r ν)
    (b₁ : O →+* R) [Mono (spMap b₁)] (hω : ω.comp b₁ = β)
    (f : pullback C'.s (spMap b₁) ⟶ C₁.X) (t₁ : SAB H (pullback C'.s (spMap b₁)))
    (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ C₁.t f)
    (h₁ : ∀ g : U ⟶ pullback C'.s (spMap b₁), g ≫ pullback.fst _ _ = C'.j → g ≫ f = C₁.j)
    (h₂ : ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = C₁.m.φ)
    (b : O'' →+* V) (e : R →+* V) (he : e.comp b₁ = b.comp b'') :
    ∃ (f' : pullback C''.s (spMap b) ⟶ C₀.X) (τ : SAB H (pullback C''.s (spMap b)))
      (n₁ : SABMap τ C''.t (pullback.fst _ _)) (n₂ : SABMap τ C₀.t f'),
      (∀ g : U'' ⟶ pullback C''.s (spMap b), g ≫ pullback.fst _ _ = C''.j → g ≫ f' = (r'' ≫ r) ≫ C₀.j) ∧
      ∀ y : t''.G.left ⟶ τ.G.left, y ≫ n₁.φ = C''.m.φ → y ≫ n₂.φ = (ν''.φ ≫ ν.φ) ≫ C₀.m.φ := by
  have w₀ : (pullback.fst C''.s (spMap b) ≫ A''.π) ≫ C'.s = (pullback.snd _ _ ≫ spMap e) ≫ spMap b₁ := by
    rw [Category.assoc, A''.π_over, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← spMap_comp, ← spMap_comp, he]
  let g₀ : pullback C''.s (spMap b) ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₀
  have hg₀ : g₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ A''.π := pullback.lift_fst _ _ _
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C''.s (spMap b)) C''.t
  obtain ⟨k₁, hk₁⟩ := LevelCover.sab_comp n₁ A''.mu rfl
  obtain ⟨k₂, hk₂⟩ := LevelCover.sab_cancel m₁ k₁ g₀ hg₀
  obtain ⟨k₃, hk₃⟩ := LevelCover.sab_comp m₂ A₁.mu rfl
  obtain ⟨n₂, hn₂⟩ := LevelCover.sab_comp k₂ k₃ rfl
  have w₁ : C'.j ≫ C'.s = (c ≫ spMap ω) ≫ spMap b₁ := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C'.jQ_over, Category.assoc, ← spMap_comp, hω]
  let g₁ : U ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₁
  have hg₁ : g₁ ≫ pullback.fst _ _ = C'.j := pullback.lift_fst _ _ _
  refine ⟨_, _, n₁, n₂, fun g hg => ?_, fun y hy => ?_⟩
  · have : g ≫ g₀ = r'' ≫ g₁ := by
      rw [← cancel_mono (pullback.fst C'.s (spMap b₁)), Category.assoc, hg₀, ← Category.assoc, hg, A''.j_comm,
        Category.assoc, hg₁]
    rw [← Category.assoc, this, Category.assoc, ← Category.assoc g₁, h₁ g₁ hg₁, A₁.j_comm, Category.assoc]
  · have p₁ : IsPullback m₁.φ t₁.G.hom C'.t.G.hom (pullback.fst C'.s (spMap b₁)) := m₁.cart.1
    have w₂ : C'.m.φ ≫ C'.t.G.hom = (t.G.hom ≫ g₁) ≫ pullback.fst C'.s (spMap b₁) := by
      rw [Category.assoc, hg₁]
      exact C'.m.cart.1.w
    have hy₁ : p₁.lift _ _ w₂ ≫ m₁.φ = C'.m.φ := p₁.lift_fst _ _ _
    have : Mono m₁.φ := (MorphismProperty.monomorphisms _).of_isPullback p₁.flip
      (inferInstanceAs (Mono (pullback.fst C'.s (spMap b₁))))
    have e₁ : y ≫ k₂.φ = ν''.φ ≫ p₁.lift _ _ w₂ := by
      rw [← cancel_mono m₁.φ, Category.assoc, hk₂, hk₁, ← Category.assoc, hy, A''.φ_comm, Category.assoc, hy₁]
    rw [hn₂, hk₃, ← Category.assoc, e₁, Category.assoc, ← Category.assoc _ m₂.φ, h₂ _ hy₁, A₁.φ_comm, Category.assoc]

theorem base_ring (l : Level H) (h : l.A = 1) {S : ℕ} (hS : 0 < S) :
    (∃ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S 1) ∧
      ∀ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  have := GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by simp [h])
  rwa [h] at this

theorem exists_global_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  intro hExt L₁ L₂ L₃ E _ _ _ H D Xo _ hN S l c hg hA
  let P := {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p}
  have : Finite P := finite_parts l
  have hP : ∀ x : P, x.1.A = 1 ∧ x.1.Dvd l := fun x => by
    obtain ⟨p, hp, h⟩ := x.2
    exact ⟨h.1, ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l x.1 h).1⟩
  have hcop : ∀ (p : ℕ), p.Prime → ∀ l₀ : Level H, IsPrimeToPart l₀ l p → (S.n (S.ch p) * l₀.M).Coprime p :=
    fun p hp l₀ h => Nat.Coprime.mul_left ((Nat.coprime_primes (S.aux _).1 hp).mpr (S.ch_ne p))
      ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l l₀ h).2.1
  have : Nonempty P := by
    obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H 2 Nat.prime_two).1 l (hg 2 Nat.prime_two)
    exact ⟨⟨l₀, 2, Nat.prime_two, h⟩⟩
  let a : Bool × P → ℕ := fun i => S.n i.1 * i.2.1.M
  have ha : ∀ i, 0 < a i := fun i => Nat.mul_pos (S.aux _).1.pos (lt_of_lt_of_le (by norm_num) i.2.1.three_le)
  let B : ∀ i : Bool × P, BaseModel (S.T i.1) i.2.1 := fun i => S.B i.1 i.2.1 (hP i.2).1
  choose k r ν hr hk hlev hfin _ using fun x : P => GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN x.1 l (hP x).2
  have hnorm : Geo.Tor.IsNormalScheme (Xo l).X := by
    have := (Xo l).smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let ω : ∀ i : Bool × P, RZ H (a i) 1 →+* KA l := fun i => (k i.2).comp (B i).β
  have hω : ∀ i, IsInc (RZ H (a i) 1).subtype (KA l).val.toRingHom (ω i) := fun i x =>
    (hk i.2 _).trans ((B i).β_inc x)
  have hωd : ∀ i, IsDedFrac (ω i) := fun i => (base_ring l hA (ha i)).2.2 _ (hω i)
  choose C hC using fun i : Bool × P => GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ (B i).β _ _ _ (Xo l).s (Xo l).univ.t (ω i) (B i).C
    (RingHom.id _) (k i.2) (r i.2) (hr i.2) (ν i.2) ((base_ring i.2.1 (hP i.2).1 (ha i)).2.2 _ (B i).β_inc) (hωd i)
    rfl hnorm (hfin i.2)
  obtain ⟨⟨β₀, hβ₀⟩, hft, hd₀⟩ := base_ring l hA Nat.one_pos
  choose b₁ hb₁ using fun i : Bool × P => (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).1
  have hωb : ∀ i, (ω i).comp (b₁ i) = β₀ := fun i =>
    RingHom.ext fun x => Subtype.ext ((hω i _).trans ((hb₁ i x).trans (hβ₀ x).symm))
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_model_dominating_models_on_open_cover hExt E H _ _ _ (Xo l).s (Xo l).univ.t β₀ (Bool × P) (fun i => RZ H (a i) 1)
    (fun i => (a i : RZ H 1 1)) b₁ ω C (hd₀ _ hβ₀) (fun i => ⟨hωd i, hωb i, isLocalization_away (ha i) _ (hb₁ i)⟩)
    (span_natCast_eq_top a fun p hp => by
      obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).1 l (hg p hp)
      exact ⟨(S.ch p, ⟨l₀, p, hp, h⟩), (Nat.Prime.coprime_iff_not_dvd hp).mp (hcop p hp l₀ h).symm⟩)
    hft (Xo l).univ.proper
  obtain ⟨hdO, -, hbO, hV⟩ := GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H l c
  obtain ⟨b₀, hb₀⟩ := hbO 1 (one_dvd _)
  have hb₀' : (algebraMap (𝓞 c.F) c.F).comp b₀ = (IntermediateField.inclusion c.le).toRingHom.comp β₀ :=
    RingHom.ext fun x => Subtype.ext ((hb₀ x).trans ((hβ₀ x).symm.trans
      (IntermediateField.coe_inclusion c.le (β₀ x)).symm))
  obtain ⟨oF, ⟨m0⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) (Xo l).X ((Xo l).XF c)
    (Xo l).s (pullback.fst _ _ ≫ (Xo l).s) (pullback.fst _ _) rfl rfl
    (by rw [LevelCover.spMap_id', Category.comp_id]) (Xo l).univ
  have hnormF : Geo.Tor.IsNormalScheme ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  obtain ⟨C'', ⟨A''⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ β₀ ((Xo l).XF c) _ _ (pullback.snd _ _) oF.t
    (algebraMap (𝓞 c.F) c.F) C' b₀ (IntermediateField.inclusion c.le).toRingHom (pullback.fst _ _) pullback.condition
    m0.toSABMap (hd₀ _ hβ₀) hdO hb₀' hnormF (by rw [pullback.lift_fst_snd]; infer_instance)
  let Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F) :=
    ⟨C''.X, C''.s, C''.normal, C''.proj, C''.flat, C''.jQ, C''.jQ_over, C''.jQ_open, C''.jQ_dense, C''.t, oF, m0,
      C''.m, C''.ab_gen⟩
  refine ⟨Y, GlobalTheory.T.model_finite_over_moduliModel_descends E H D l (Xo l) c _ _ Y _ β₀ C' b₀ A'' (hd₀ _ hβ₀) hdO hb₀', fun p W hp hW b hb => ?_⟩
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW ⟨l, c, hg p hp⟩
  let i : Bool × P := (S.ch p, ⟨l₀, p, hp, h⟩)
  obtain ⟨hdV, -, hbV⟩ := hV p W hp hW
  obtain ⟨e, he⟩ := hbV (a i) 1 (hcop p hp l₀ h) Nat.one_pos (hA ▸ c.le (baseKA l).ζ.2)
  obtain ⟨f, t₁, m₁, m₂, -, h₁, h₂⟩ := hC' i
  obtain ⟨A₁⟩ := hC i
  have := (((GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).2 _ (hb₁ i)).2 rfl).1
  obtain ⟨f', τ, n₁, n₂, e₁, e₂⟩ := exists_map_to_base A'' A₁ (b₁ i) (hωb i) f t₁ m₁ m₂ h₁ h₂ b e
    (RingHom.ext fun x => Subtype.ext (Subtype.ext ((he _).trans ((hb₁ i x).trans ((hb₀ x).symm.trans
      (congrArg Subtype.val (hb _)).symm)))))
  obtain ⟨ν', hν'⟩ := LevelCover.sab_comp m0.toSABMap (ν i.2) rfl
  refine GlobalTheory.T.model_dominated_of_map_to_baseModel L₁ L₂ L₃ E H D Xo _ _ _ l₀ l (B i) c _ _ _ _ Y _ b f' τ n₁ n₂ _ ν'
    ((IntermediateField.inclusion c.le).toRingHom.comp (k i.2)) hdO hdV (RingHom.ext hb) hR ⟨fun x => ?_, fun x => ?_⟩
    (fun x => (IntermediateField.coe_inclusion c.le _).trans (hk i.2 x)) ?_ e₁ (hν' ▸ e₂)
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.eta x), Category.assoc, (hlev i.2).1,
      Category.assoc]
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.etaA x), Category.assoc, (hlev i.2).2,
      Category.assoc]
  · rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp]

end GlobalTheory.GlobalModel
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_model_of_local_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  first | exact @GlobalTheory.GlobalModel.exists_global_model | exact GlobalTheory.GlobalModel.exists_global_model | (intros; apply GlobalTheory.GlobalModel.exists_global_model <;> assumption)
end
