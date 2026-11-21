import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFuncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekindStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZerosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhoodStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_degreeTwo_class_dies_on_principalOpen : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
    ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧
      pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq i x
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · have hSH : SH B := GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB
    haveI : Subsingleton (Ht q (sp B) 2 i) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B hSH (tw q i) 2 (by norm_num)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Subsingleton.elim x 0, map_zero]
  · obtain ⟨inst, halg⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    letI := inst
    haveI := halg
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    haveI : Subsingleton (Ht q (sp (FractionRing B)) 2 i) :=
      GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK 2 i le_rfl
    obtain ⟨f, hf, -, hx⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB 2 i x (Subsingleton.elim _ _)
    exact ⟨f, hf, hx⟩

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CurveNbhdExcision

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := RingHom.ext fun _ => Subsingleton.elim _ _
  have key : ∀ z : Ht q (sp Z) n i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1, ← hy.2, hfs]
  rw [key a, key b]

theorem away_zero_subsingleton (B : Type) [CommRing B] : Subsingleton (Localization.Away (0 : B)) := by
  have h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_zero, isUnit_zero_iff] at h
  exact subsingleton_of_zero_eq_one h

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf n i hn x
  by_cases hu : IsUnit f
  · haveI := away_zero_subsingleton B
    refine ⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩
    · intro a'
      exact ⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩
    · intro a _
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i
      exact Subsingleton.elim _ _
  · obtain ⟨A', i1, i2, i3, hN, hx⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x
    exact ⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩

end GlobalTheory.EtC.CurveNbhdExcision
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.CurveNbhdExcision.main) | (exact GlobalTheory.EtC.CurveNbhdExcision.main) | (intros; apply GlobalTheory.EtC.CurveNbhdExcision.main <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_tateTwistCohomology_two_subsingleton : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ,
    Subsingleton (Ht q (sp B) 2 i) := by
  intro q _ k B _ _ _ _ _ _ hq i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)).ne'
  have hζ : ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    refine ⟨algebraMap k B z, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic,
      hz.eq_zero, map_zero]
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q B hqB hζ 2 i 1
  have h0 : ∀ x : Ht q (sp B) 2 1, x = 0 := by
    intro x
    obtain ⟨f, hf, hxf⟩ := GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two q k B hq 1 x
    obtain ⟨A', _, _, hA', hxA'⟩ := GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass q k B hq f hf 2 1 (by norm_num) x
    obtain ⟨w, hw⟩ := GlobalTheory.T.etaleExcision_vanishing_under_refinement q B A' f hA' 1 1 x hxf hxA'
    obtain ⟨g, hfg, A₂, C, _, _, _, _, _, _, h2, hg, hC, a, haC, hwa⟩ := GlobalTheory.T.exists_kummerClass_agreeing_near_zeros q k B hq f hf A' hA' w
    exact hw g hfg A₂ C h2 hg hC a haC hwa
  exact ⟨fun a b => e.injective (by rw [h0 (e a), h0 (e b)])⟩

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ, Subsingleton (Ht q (sp B) 2 i) := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (exact GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_shortExact_of_free : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  intro R _ X₁ X₂ X₃ X₄ a b c d w₁ w₂ h
  obtain ⟨hLE, hnat, -⟩ := chains_basic R
  have hm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (chainsXIso R (sch.obj Y) p).hom =
      (chainsXIso R (sch.obj X) p).hom ≫ (free R).map (yoneda.map f) := fun f p => hnat (sch.map f) p
  let e : ∀ (X : Scheme.{0}) (p : ℕ), ((chains R).obj (sch.obj X)).X (-(p : ℤ)) ≅ (free R).obj (yoneda.obj X) :=
    fun X p => chainsXIso R (sch.obj X) p
  have he : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ), ((chains R).map (sch.map f)).f (-(p : ℤ)) ≫ (e Y p).hom =
      (e X p).hom ≫ (free R).map (yoneda.map f) := fun f p => hm f p
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases (show (∃ p : ℕ, n = -(p : ℤ)) ∨ 0 < n from by
    by_cases hn : 0 < n
    · exact Or.inr hn
    · exact Or.inl ⟨(-n).toNat, by omega⟩) with ⟨p, rfl⟩ | hn
  · have c1 : (e X₁ p).hom ≫ biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) =
        (biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b))).f (-(p : ℤ)) ≫
          ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, HomologicalComplex.biprodXIso_hom_fst_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_fst, he]
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, HomologicalComplex.biprodXIso_hom_snd_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.neg_comp, he,
          Preadditive.comp_neg]
    have c2 : ((HomologicalComplex.biprodXIso _ _ _).hom ≫ biprod.map (e X₂ p).hom (e X₃ p).hom) ≫
        biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) =
        (biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d))).f (-(p : ℤ)) ≫ (e X₄ p).hom := by
      rw [Category.assoc, ← Iso.eq_inv_comp]
      apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc, biprod.inl_desc, HomologicalComplex.inl_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inl_desc, he]
      · simp only [biprod.inr_map_assoc, biprod.inr_desc, HomologicalComplex.inr_biprodXIso_inv_assoc]
        rw [← HomologicalComplex.comp_f_assoc, biprod.inr_desc, he]
    refine ShortComplex.shortExact_of_iso ?_ h
    refine (ShortComplex.isoMk (e X₁ p)
      (HomologicalComplex.biprodXIso _ _ _ ≪≫ biprod.mapIso (e X₂ p) (e X₃ p))
      (e X₄ p) ?_ ?_).symm
    · exact c1
    · exact c2
  · have z : ∀ X : Scheme.{0}, IsZero (((chains R).obj (sch.obj X)).X n) := fun X =>
      have := hLE (sch.obj X); CochainComplex.isZero_of_isStrictlyLE _ 0 n hn
    have z₂ : IsZero ((((chains R).obj (sch.obj X₂)) ⊞ ((chains R).obj (sch.obj X₃))).X n) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨z X₂, z X₃⟩) (HomologicalComplex.biprodXIso _ _ _)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ z₂
        mono_f := ⟨fun _ _ _ => (z X₁).eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => (z X₄).eq_of_src _ _⟩ }

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_complex_exact_square : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  first | (exact @GlobalTheory.EtC.chains_shortExact_of_free) | (exact GlobalTheory.EtC.chains_shortExact_of_free) | (intros; apply GlobalTheory.EtC.chains_shortExact_of_free <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.EtC.ExcisionNat

abbrev C (R : Type) [CommRing R] (B : Type) [CommRing B] : Cx R := (chains R).obj (sp B)

abbrev Cm (R : Type) [CommRing R] {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') : C R B' ⟶ C R B :=
  (chains R).map (spMap g)

theorem spMap_comp {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B) (g : B →+* B') :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem Cm_comp (R : Type) [CommRing R] {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B)
    (g : B →+* B') : Cm R g ≫ Cm R h = Cm R (g.comp h) := by
  rw [← Functor.map_comp, spMap_comp]

theorem awayMap_comp_algebraMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
  IsLocalization.map_comp _

theorem awayHom_comp_awayMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (Localization.awayMap (algebraMap A A') f) = Localization.awayMap (algebraMap A A'') f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, awayMap_comp_algebraMap, ← RingHom.comp_assoc, awayHom_comp_algebraMap,
    awayMap_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

def exSC (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    ShortComplex (Cx R) :=
  ShortComplex.mk
    (biprod.lift (Cm R (Localization.awayMap (algebraMap A A') f))
      (-Cm R (algebraMap A' (Localization.Away (algebraMap A A' f)))))
    (biprod.desc (Cm R (algebraMap A (Localization.Away f))) (Cm R (algebraMap A A')))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Cm_comp, Cm_comp, awayMap_comp_algebraMap, add_neg_cancel])

theorem exSC_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A) (hN : IsNbhd A A' f) : (exSC R A A' f).ShortExact := by
  refine GlobalTheory.T.chain_complex_exact_square R _ _ _ _ ?_ (exSC R A A' f).zero (GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f hN ?_)
  all_goals
    simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayMap_comp_algebraMap, add_neg_cancel]

def exMap (R : Type) [CommRing R] {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) : exSC R A A'' f ⟶ exSC R A A' f where
  τ₁ := Cm R (awayHom φ f)
  τ₂ := biprod.map (𝟙 _) (Cm R φ.toRingHom)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [exSC, Category.assoc, biprod.lift_fst, biprod.map_fst, Category.comp_id, Cm_comp, awayHom_comp_awayMap]
    · simp only [exSC]
      rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
        Preadditive.comp_neg, Preadditive.neg_comp, Cm_comp, Cm_comp, awayHom_comp_algebraMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [exSC, biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc, Category.comp_id]
    · simp only [exSC, biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, Cm_comp]
      congr 2
      exact RingHom.ext fun a => φ.commutes a

theorem excision_natural : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  intro q A A' _ _ _ _ f hN n i
  have hI : ∀ k, Injective ((res (ZMod q) (tw q i)).X k) := fun k =>
    inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X k))
  obtain ⟨d, hex, hnat⟩ := longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) hI
  have hS := exSC_shortExact (ZMod q) A A' f hN
  refine ⟨d (exSC (ZMod q) A A' f) hS n, ?_, ?_⟩
  · intro x
    refine Iff.trans ?_ ((hex _ hS n).2.2 x)
    have hb := (cpull_biprod_bijective (ZMod q) (C (ZMod q) (Localization.Away f)) (C (ZMod q) A')
      (res (ZMod q) (tw q i)) (n + 1)).1
    have e1 : pull (ZMod q) (spMap (algebraMap A (Localization.Away f))) (tw q i) (n + 1) x =
        cpull (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A (Localization.Away f)) := biprod.inl_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    have e2 : pull (ZMod q) (spMap (algebraMap A A')) (tw q i) (n + 1) x =
        cpull (biprod.inr : C (ZMod q) A' ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inr : C (ZMod q) A' ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A A') := biprod.inr_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    change (_, _) = ((0, 0) : _ × _) ↔ _
    rw [e1, e2]
    obtain ⟨y, hy⟩ : ∃ y : CohomologyClass (C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') (res (ZMod q) (tw q i)) (n + 1),
      y = cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x := ⟨_, rfl⟩
    rw [← hy]
    constructor
    · intro h
      apply hb
      dsimp only
      rw [h]
      exact Prod.ext (map_zero _).symm (map_zero _).symm
    · intro h
      rw [h]
      exact Prod.ext (map_zero _) (map_zero _)
  · intro A'' _ _ _ φ hN'' z hz
    have hS'' := exSC_shortExact (ZMod q) A A'' f hN''
    have h := hnat _ _ hS'' hS (exMap (ZMod q) φ f) n z
    have hz' : cpull (exMap (ZMod q) φ f).τ₁ (res (ZMod q) (tw q i)) n z = 0 := hz
    rw [hz', map_zero] at h
    have hid : cpull (exMap (ZMod q) φ f).τ₃ (res (ZMod q) (tw q i)) (n + 1) (d _ hS n z) = d _ hS n z :=
      ZcFun.cpull_id _ _ _ _
    rw [hid] at h
    exact h

end GlobalTheory.EtC.ExcisionNat
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.AffineCurve

theorem subsingleton_of_three_le : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n →
    Subsingleton (Ht q (sp B) n i) := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · exact GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B (GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB) (tw q i) n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    suffices h : ∀ x : Ht q (sp B) (m + 1) i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    obtain ⟨_, _⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    have h1 : pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 :=
      (GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK (m + 1) i (by omega)).elim _ _
    obtain ⟨f, hf0, hfu, hxf⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB (m + 1) i x h1
    obtain ⟨A', _, _, _, hA', hxA'⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf0 hfu (m + 1) i (by omega) x
    obtain ⟨δ, hex, hkill⟩ := GlobalTheory.T.mayer_vietoris_exact_etale q B A' f hA' m i
    obtain ⟨z, rfl⟩ := (hex x).mp (by simp [hxf, hxA'])
    obtain ⟨A'', _, _, _, φ, hA'', hz⟩ := GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood q k B hq f hf0 hfu A' hA' m i (by omega) z
    exact hkill A'' φ hA'' z hz

end GlobalTheory.EtC.AffineCurve
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n → Subsingleton (Ht q (sp B) n i) := by
  first | (exact @GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (exact GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le) | (intros; apply GlobalTheory.EtC.AffineCurve.subsingleton_of_three_le <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.etC_c2 : GlobalTheory.EtC.C2 := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed q k B hq i
  · exact GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three q k B hq n i (by omega)

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
end
