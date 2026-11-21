import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommon
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_local_equation_common : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] [IsAffine Z], topologicalKrullDim Z ≤ 1 → ∀ (D : CartierDiv Z) (S : Set Z), S.Finite → ∃ g : Z.functionFieldˣ, ∀ z ∈ S, D.IsEqn z g := by
  first | exact @GlobalTheory.Cartier.CommonEqn.exists_isEqn_curve | exact GlobalTheory.Cartier.CommonEqn.exists_isEqn_curve | (intros; apply GlobalTheory.Cartier.CommonEqn.exists_isEqn_curve <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_dim_zero_finite : ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) (q : Z ⟶ Sp k), IsArithVar q 0 → IsFinite q := by
  first | exact @GlobalTheory.ArithCurveFinite.isFinite | exact GlobalTheory.ArithCurveFinite.isFinite | (intros; apply GlobalTheory.ArithCurveFinite.isFinite <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.PlaceFormula

theorem coheight_eq_one {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : Order.coheight z = 1 := by
  have hg (w : Z) : w ≤ genericPoint Z := genericPoint_specializes w
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) (Order.one_le_iff_ne_zero.2 fun h => ?_)
  · have h1 : y = genericPoint Z := by
      by_contra h
      have h2 : y ⤳ z := hy.le
      have h3 := (SmallSecHeight.isClosed_of_ne hd h).closure_eq ▸ specializes_iff_mem_closure.1 h2
      exact hy.ne h3
    have h2 : Order.coheight y = 0 := Order.coheight_eq_zero.2 fun w _ => h1 ▸ hg w
    simp [h2]
  · have h1 : z ⤳ genericPoint Z := Order.coheight_eq_zero.1 h (hg z)
    exact hz (h1.antisymm (genericPoint_specializes z)).eq

theorem spec_appTop {K : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (y : Spec K ⟶ Z) :
    Spec.map (y.appTop ≫ (Scheme.ΓSpecIso K).hom) ≫ (isAffineOpen_top Z).fromSpec = y := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem fromSpec_comp {k : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (q : Z ⟶ Spec k) :
    (isAffineOpen_top Z).fromSpec ≫ q = Spec.map ((Scheme.ΓSpecIso k).inv ≫ q.appTop) := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]

theorem valAt_spec {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] [IsAffine Z] (ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K)
    (a : Γ(Z, ⊤)) :
    valAt (K := K) (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec) (fnOf ⊤ trivial a) = ψ.hom a := by
  have h := Spec.map_injective ((cancel_mono _).1 (spec_appTop (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec)))
  rw [OfModel.valAt_fnOf (U := ⊤) _ trivial le_rfl]
  conv_rhs => rw [← h]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem injective_of_charZero {F R : Type} [Field F] [NumberField F] [CommRing R] [CharZero R] (φ : 𝓞 F →+* R) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
  simpa [RingHom.mem_ker] using hn

set_option maxHeartbeats 400000 in

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ),
    ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
    -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  intro F _ _ Z _ _ q hZ v e t
  have := GlobalTheory.ArithCurveFinite.isFinite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  have hU := isAffineOpen_top Z
  have := hZ.charZero
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  let φ : CommRingCat.of (𝓞 F) ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ q.appTop
  have hq : hU.fromSpec ≫ q = Spec.map φ := fromSpec_comp q
  let : Algebra (𝓞 F) Γ(Z, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective hU.fromSpec := by
    refine ⟨hU.fromSpec.isOpenEmbedding.injective, fun z => ?_⟩
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; trivial
    exact this
  have : Module.Finite (𝓞 F) Γ(Z, ⊤) := (IsFinite.SpecMap_iff φ).1 (by
    rw [← hq, IsAffineOpen.fromSpec_top]; infer_instance)
  have := functionField_isFractionRing_of_isAffineOpen Z ⊤ hU
  have hφ : Function.Injective (algebraMap (𝓞 F) Γ(Z, ⊤)) := injective_of_charZero _
  have := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have hi : Function.Injective ((algebraMap Γ(Z, ⊤) Z.functionField).comp (algebraMap (𝓞 F) Γ(Z, ⊤))) :=
    (IsFractionRing.injective _ _).comp hφ
  let : Algebra F Z.functionField := (IsFractionRing.lift hi).toAlgebra
  have : IsScalarTower (𝓞 F) Γ(Z, ⊤) Z.functionField :=
    .of_algebraMap_eq fun a => IsFractionRing.lift_algebraMap (K := F) hi a
  have : Module.Finite F Z.functionField := Module.Finite.of_isLocalization (𝓞 F) Γ(Z, ⊤) (nonZeroDivisors _)

  let P (τ : Z.functionField →ₐ[F] AlgebraicClosure F) :
      {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} :=
    ⟨Spec.map (CommRingCat.ofHom (τ.toRingHom.comp (algebraMap Γ(Z, ⊤) Z.functionField))) ≫ hU.fromSpec, by
      rw [Category.assoc, hq, ← Spec.map_comp]
      congr 1
      ext a
      change τ (algebraMap Γ(Z, ⊤) _ (algebraMap (𝓞 F) _ a)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F, τ.commutes]
      rfl⟩
  have hP : Function.Bijective P := by
    refine ⟨fun τ τ' h => ?_, fun y => ?_⟩
    · have h1 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 (congrArg Subtype.val h)))
      exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Γ(Z, ⊤)) h1)
    · obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Z, ⊤) ⟶ CommRingCat.of (AlgebraicClosure F), Spec.map ψ ≫ hU.fromSpec = y.1 :=
        ⟨_, spec_appTop y.1⟩
      have h1 := y.2
      rw [← hψ, Category.assoc, hq, ← Spec.map_comp] at h1
      have h2 (a : 𝓞 F) : ψ.hom (algebraMap _ _ a) = algebraMap _ _ a :=
        congrArg (fun f => f.hom a) (Spec.map_injective h1)
      have h3 : Function.Injective ψ.hom := by
        rw [RingHom.injective_iff_ker_eq_bot]
        refine Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) (eq_bot_iff.2 fun a ha => ?_)
        rw [Ideal.mem_comap, RingHom.mem_ker, h2] at ha
        exact injective_of_charZero (algebraMap (𝓞 F) (AlgebraicClosure F)) (ha.trans (map_zero _).symm)
      have h4 : (IsFractionRing.lift (K := Z.functionField) h3).comp (algebraMap F _) = algebraMap F _ :=
        IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a => by
          simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
          rw [IsScalarTower.algebraMap_apply (𝓞 F) Γ(Z, ⊤), IsFractionRing.lift_algebraMap, h2])
      refine ⟨⟨IsFractionRing.lift h3, fun a => congrArg (fun f => f a) h4⟩, Subtype.ext ?_⟩
      rw [← hψ]
      exact congrArg (fun f => Spec.map f ≫ hU.fromSpec)
        (CommRingCat.hom_ext (RingHom.ext fun a =>
          IsFractionRing.lift_algebraMap (K := Z.functionField) h3 a))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(Z, ⊤)) (t : Z.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap _ Z.functionField b ≠ 0 := by simpa using hb0
  have hab' : algebraMap _ Z.functionField a = t * algebraMap _ _ b := by rw [← hab, div_mul_cancel₀ _ hb1]
  have ha1 : algebraMap _ Z.functionField a ≠ 0 := hab' ▸ mul_ne_zero t.ne_zero hb1
  have ha0 : a ≠ 0 := by simpa using ha1
  have hval (τ) : valAt (P τ).1 (t : Z.functionField) = τ t := by
    have hg : below (P τ).1 = genericPoint Z :=
      SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField _ Z (P τ).1).2.hom.charZero
    have h1 (c : Γ(Z, ⊤)) : valAt (P τ).1 (algebraMap _ Z.functionField c) = τ (algebraMap _ _ c) := valAt_spec _ c
    have h2 := h1 a
    rw [hab', OfModel.valAt_mul _ (hg ▸ regAt_genericPoint _) (hg ▸ regAt_genericPoint _), h1, map_mul] at h2
    exact mul_right_cancel₀ ((map_ne_zero τ).2 hb1) h2
  have hR : ∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (t : Z.functionField))) := by
    rw [← finsum_eq_of_bijective P hP (f := fun τ => Real.log (e.w (τ t))) fun τ => by rw [hval],
      finsum_eq_sum_of_fintype, ← e.w_alg, Algebra.norm_eq_prod_embeddings, map_prod, Real.log_prod]
    exact fun τ _ => e.w.ne_zero ((map_ne_zero τ).2 t.ne_zero)

  have hL (c : Γ(Z, ⊤)) (hc : c ≠ 0) : ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (algebraMap _ Z.functionField c) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (algebraMap _ Z.functionField c))) := by
    let (m : PrimeSpectrum Γ(Z, ⊤)) : Algebra Γ(Z, ⊤) (Z.presheaf.stalk (hU.fromSpec m)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨hU.fromSpec m, trivial⟩ : (⊤ : Z.Opens))
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec m)) m.asIdeal :=
      hU.isLocalization_stalk' m trivial
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalRing (Z.presheaf.stalk (hU.fromSpec m)) :=
      Z.toLocallyRingedSpace.isLocalRing _
    rw [← GlobalTheory.finsum_length_mul_log_card_eq_neg_log_adicAbv_norm F Γ(Z, ⊤) Z.functionField (fun m => Z.presheaf.stalk (hU.fromSpec m)) v c hc]
    refine (finsum_eq_of_bijective _ hbij fun m => ?_).symm
    have hqm (m) : (q (hU.fromSpec m)).asIdeal = m.asIdeal.comap (algebraMap (𝓞 F) Γ(Z, ⊤)) := by
      rw [← Scheme.Hom.comp_apply, hq]; rfl
    refine finsum_congr_Prop (by rw [hqm]) fun h => ?_
    have hne : hU.fromSpec m ≠ genericPoint Z := fun h' => v.ne_bot (by
      have h1 := genericPoint_eq_of_isOpenImmersion hU.fromSpec
      rw [genericPoint_eq_bot_of_affine] at h1
      rw [← h, h', ← h1]
      exact (hqm _).trans (Ideal.comap_bot_of_injective _ hφ))
    have h1 := ord_algebraMap (coheight_eq_one hZ.dim_eq hne)
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral Z (U := ⊤) _ trivial)).2 hc)
    rw [algebraMap_germ (U := ⊤) trivial c] at h1
    exact congrArg (· * _) ((Int.cast_natCast _).symm.trans (congrArg _ h1.symm))
  have hfin : {z : Z | (q z).asIdeal = v.asIdeal}.Finite :=
    (q.finite_preimage_singleton ⟨v.asIdeal, v.isPrime⟩).subset fun z hz => PrimeSpectrum.ext hz
  have h1 := hL a ha0
  have h2 := hL b hb0
  have hn (x : Z.functionField) (hx : x ≠ 0) :
      NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F x) ≠ 0 :=
    AbsoluteValue.ne_zero _ (Algebra.norm_ne_zero_iff.2 hx)
  rw [hab', map_mul, map_mul, Real.log_mul (hn _ t.ne_zero) (hn _ hb1)] at h1
  simp only [Scheme.ord_mul t.ne_zero hb1, Int.cast_add, add_mul] at h1
  have h3 := finsum_mem_add_distrib
    (f := fun z => (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)))
    (g := fun z => (Scheme.ord (algebraMap _ Z.functionField b) z : ℝ) * Real.log (Nat.card (Z.residueField z))) hfin
  simp only [Set.mem_ofPred_eq] at h3
  rw [hR]
  linear_combination h1 - h2 - h3

end GlobalTheory.TrueGeo.PlaceFormula
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_order : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ), ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))}, Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  atlas_forward_decl GlobalTheory.TrueGeo.PlaceFormula.main
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.FinSum

theorem finsum_group {α β : Type} (f : α → ℝ) (hf : (Function.support f).Finite) (R : β → α → Prop)
    (h : ∀ a, f a ≠ 0 → ∃! b, R b a) : ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ (a) (_ : R b a), f a := by
  classical
  let g : α × β → ℝ := fun p => if R p.2 p.1 then f p.1 else 0
  have hg (p : α × β) (hp : g p ≠ 0) : R p.2 p.1 ∧ f p.1 ≠ 0 := by
    by_cases hR : R p.2 p.1
    · exact ⟨hR, by simpa [g, hR] using hp⟩
    · simp [g, hR] at hp
  have hfin : (Function.support g).Finite :=
    Set.Finite.of_injOn (f := Prod.fst) (fun p hp => (hg p hp).2) (fun p hp p' hp' e =>
      Prod.ext e ((h _ (hg p hp).2).unique (hg p hp).1 (e ▸ (hg p' hp').1))) hf
  have hfin' : (Function.support fun p : β × α => g p.swap).Finite :=
    hfin.preimage (f := Prod.swap) Prod.swap_injective.injOn
  calc ∑ᶠ a, f a = ∑ᶠ a, ∑ᶠ b, g (a, b) := finsum_congr fun a => by
        by_cases ha : f a = 0
        · simp [g, ha]
        · obtain ⟨b, hb, hu⟩ := h a ha
          rw [finsum_eq_single _ b fun b' hb' => if_neg fun e => hb' (hu b' e)]
          exact (if_pos hb).symm
    _ = ∑ᶠ p, g p := (finsum_curry g hfin).symm
    _ = ∑ᶠ p : β × α, g p.swap := (finsum_comp_equiv (Equiv.prodComm β α)).symm
    _ = ∑ᶠ b, ∑ᶠ a, g (a, b) := finsum_curry _ hfin'
    _ = _ := finsum_congr fun b => finsum_congr fun a => by rw [finsum_eq_if]

variable {F : Type} [Field F] [NumberField F] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp (𝓞 F)}

theorem eq_generic (hZ : IsArithVar q 0) {z : Z} (hz : (q z).asIdeal = ⊥) : z = genericPoint Z := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.fromSpecResidueField z ≫ q)
  have e : q z = Spec.map φ (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact congrArg q (Scheme.fromSpecResidueField_apply _ _).symm
  have hi : Function.Injective φ.hom := (injective_iff_map_eq_zero _).2 fun a ha => by
    have : a ∈ (q z).asIdeal := by
      rw [e]
      change φ.hom a ∈ IsLocalRing.maximalIdeal _
      rw [ha]
      exact zero_mem _
    rwa [hz] at this
  exact SmallSecHeight.eq_genericPoint hZ ((RingHom.charZero_iff hi).1 (inferInstanceAs (CharZero (𝓞 F))))

omit [IsIntegral Z] in

theorem exists_ext [IsProper q] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ Z)
    (hy : y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))) :
    ∃ yt : Sp e.O ⟶ Z, spMap e.O.subtype ≫ yt = y ∧
      (q (yt (IsLocalRing.closedPoint e.O))).asIdeal = v.asIdeal := by
  let r : 𝓞 F →+* e.O := (algebraMap (𝓞 F) (AlgebraicClosure F)).codRestrict e.O fun a => by
    rw [e.mem_O, IsScalarTower.algebraMap_apply (𝓞 F) F, e.w_alg, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one F v a
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := y, i₂ := spMap r, commSq := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩ }
  refine ⟨l.l, l.fac_left, Ideal.ext fun a => ?_⟩
  have h : q (l.l (IsLocalRing.closedPoint e.O)) = spMap r (IsLocalRing.closedPoint e.O) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp e.O ⟶ Sp (𝓞 F) => t _) l.fac_right)
  rw [h, ← ExtConj.lies_over e a]
  exact e.O.valuation_lt_one_iff (r a)

theorem w_valAt {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ Z)
    (yt : Sp e.O ⟶ Z) (h : spMap e.O.subtype ≫ yt = y) {u : Z.functionField}
    (hu : UnitAt (yt (IsLocalRing.closedPoint e.O)) u) : e.w (valAt y u) = 1 := by
  obtain ⟨U, hU, hu⟩ := hu.exists_nhds
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq hu
  have ht : ⊤ ≤ yt ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of e.O) yt hU).ge
  have h₁ : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
    change y x ∈ U
    rw [← h]
    exact ht (x := spMap e.O.subtype x) trivial
  have h₂ : below y ∈ U := h₁ trivial
  have h₃ := OfModel.eval_pull e.O.subtype (𝟙 Z) y yt (h.trans (Category.comp_id _).symm) (U := U) (W := U)
    le_rfl h₁ ht a
  have h₄ : (Scheme.Hom.appLE (𝟙 Z) U U le_rfl).hom a = a := by
    exact congrArg (fun ψ => ψ.hom a.val) (Z.presheaf.map_id (Opposite.op U))
  rw [← ha (gen_mem h₂), OfModel.valAt_fnOf y h₂ h₁, ← h₄, h₃]
  exact OfModel.w_unit e (a.isUnit.map _)

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v) (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ), (∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ, D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) → ∑ᶠ z : Z, (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ v, ∑ᶠ y, l v y := by
  intro F _ _ Z _ _ q hZ D e l hl
  have := hZ.isNoetherian
  have := T.arithmetic_variety_dim_zero_finite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  rw [finsum_group _ (D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0]))
    (fun (v : HeightOneSpectrum (𝓞 F)) z => (q z).asIdeal = v.asIdeal) fun z hz => ?_, ← finsum_neg_distrib]
  · refine finsum_congr fun v => ?_
    obtain ⟨t, ht⟩ := T.cartier_local_equation_common Z hZ.dim_eq.le D (q ⁻¹' {⟨v.asIdeal, v.isPrime⟩}) (q.finite_preimage_singleton _)
    have ht' (z : Z) (hz : (q z).asIdeal = v.asIdeal) : D.IsEqn z t := ht z (PrimeSpectrum.ext hz)
    have hv (y) : l v y = Real.log ((e v).w (valAt y.1 (t : Z.functionField))) := by
      obtain ⟨yt, h₁, h₂⟩ := exists_ext (e v) y.1 y.2
      obtain ⟨g, hg, h₃⟩ := hl v y yt h₁
      have hb : below y.1 = genericPoint Z := SmallSecHeight.eq_genericPoint hZ
        (Scheme.SpecToEquivOfField _ Z y.1).2.hom.charZero
      rw [h₃, ← div_mul_cancel₀ (g : Z.functionField) t.ne_zero,
        OfModel.valAt_mul _ (hb ▸ regAt_genericPoint _) (hb ▸ regAt_genericPoint _), map_mul,
        w_valAt _ _ yt h₁ ((ht' _ h₂).iff_unitAt.1 hg), one_mul]
    rw [finsum_congr hv, ← T.product_formula_order F Z q hZ v (e v) t]
    exact finsum_congr fun z => finsum_congr fun hz => by rw [(ht' z hz).mult_eq]
  · have h0 : (q z).asIdeal ≠ ⊥ := fun h => hz (by
      have : D.mult z = 0 := by_contra fun h' =>
        D.genericPoint_notMem_supp (eq_generic hZ h ▸ CartierDiv.mem_supp_of_mult_ne_zero h')
      simp [this])
    exact ⟨⟨_, (q z).isPrime, h0⟩, rfl, fun v hv => HeightOneSpectrum.ext hv.symm⟩

end GlobalTheory.TrueGeo.FinSum
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_equations_height_sum : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v) (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ), (∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ, D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) → ∑ᶠ z : Z, (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ v, ∑ᶠ y, l v y := by
  first | exact @GlobalTheory.TrueGeo.FinSum.main | exact GlobalTheory.TrueGeo.FinSum.main | (intros; apply GlobalTheory.TrueGeo.FinSum.main <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ResidueCard

theorem card_ringHom_eq {X Z : Scheme.{0}} (i : Z ⟶ X) [IsPreimmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem card_emb (F L : Type) [Field F] [NumberField F] [Field L] [Algebra F L] [Module.Finite F L] :
    Nat.card (L →+* ℂ) = Module.finrank ℚ F * Nat.card (L →ₐ[F] AlgebraicClosure F) := by
  haveI : NumberField L := NumberField.of_module_finite F L
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AlgHom.card, NumberField.Embeddings.card,
    Module.finrank_mul_finrank]

theorem card_parity_sign_length_of_eq {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nat.card (X.residueField x →+* ℂ) = Module.finrank ℚ F *
      Nat.card {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite F (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[F] AlgebraicClosure F) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s =
        spMap (algebraMap F (AlgebraicClosure F)) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[F] AlgebraicClosure F) →
      {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      ExtConj.below_comp x _⟩
  have hb : Function.Bijective P := by
    refine ⟨fun a b h => ?_, ?_⟩
    · have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.fromSpecResidueField x =
          Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨ψ, h⟩ := ExtConj.factor y x hyx
      have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) := by
        rw [Spec.map_comp, hφ, ← Category.assoc, h]
        exact hy
      have h3 := Spec.map_injective h2
      exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩
  rw [card_emb F (X.residueField x), Nat.card_congr (Equiv.ofBijective P hb)]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  intro F _ _ Y M x hx
  have h1 : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion M.j := MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip h1
  rw [card_ringHom_eq]
  exact card_parity_sign_length_of_eq Y.str x hx

end GlobalTheory.TrueGeo.ResidueCard
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_embeddings_card : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  first | exact @GlobalTheory.TrueGeo.ResidueCard.main | exact GlobalTheory.TrueGeo.ResidueCard.main | (intros; apply GlobalTheory.TrueGeo.ResidueCard.main <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosedAlg

theorem isAlgPt_of_isClosed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → ArInt.IsAlgPt (M.j x) := by
  intro F _ _ Y M x hx
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra
  obtain ⟨⟨⟨y, hy⟩, hyx⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) Y.str x hx).1
  have h : (y ≫ M.j) ≫ M.p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm
  have h2 := GlobalTheory.Mean4O.GeomPt.isAlgPt M.ar
    (⟨y ≫ M.j, h⟩ : GlobalTheory.Mean4O.GeomPt M.p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))
  subst hyx
  exact h2

end GlobalTheory.TrueGeo.ClosedAlg
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_point_algebraic : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → ArInt.IsAlgPt (M.j x) := by
  first | exact @GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed | exact GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed | (intros; apply GlobalTheory.TrueGeo.ClosedAlg.isAlgPt_of_isClosed <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosurePts

theorem lift_closed {K : Type} [Field K] {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)
    (y : Sp K ⟶ X) (h : below y = i z) : ∃ y' : Sp K ⟶ Z, y' ≫ i = y := by
  obtain ⟨ψ, rfl⟩ := ExtConj.factor y _ h
  have hbij : Function.Bijective (i.residueFieldMap z).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have : IsIso (i.residueFieldMap z) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  refine ⟨Spec.map (inv (i.residueFieldMap z) ≫ ψ) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id_assoc]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ M.X) [IsClosedImmersion i], IsArithVar (i ≫ M.p) 0 → i (genericPoint Z) = M.j x → ∀ (K : Type) [Field K] (σ : F →+* K), ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃ {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x}, ∀ y, (E y).1.1 ≫ M.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  intro F _ _ Y M x Z _ i _ hZ hx K _ σ
  have : CharZero K := charZero_of_injective_ringHom σ.injective
  have hgen (y : Sp K ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField K Z y).2.hom.charZero
  have hpre : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F)) (S := F)
  have hj : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip hpre
  have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp]
    rfl
  have hw (y : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))}) :
      (y.1 ≫ i) ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [Category.assoc, y.2, hs]
  let f : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} →
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x} := fun y =>
    ⟨⟨M.pb.lift (y.1 ≫ i) (spMap σ) (hw y), M.pb.lift_snd _ _ _⟩, by
      apply M.j.isEmbedding.injective
      rw [← hx, ← hgen y.1]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun t : Sp K ⟶ M.X => below t) (M.pb.lift_fst _ _ (hw y))).trans
          (Scheme.Hom.comp_apply _ _ _))⟩
  have hf (y) : (f y).1.1 ≫ M.j = y.1 ≫ i := M.pb.lift_fst _ _ _
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun y => ⟨hf y, hgen y.1⟩⟩
  · apply Subtype.ext
    rw [← cancel_mono i, ← hf, ← hf, h]
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨y', hy'⟩ := lift_closed i (genericPoint Z) (y ≫ M.j)
      ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg M.j hyx).trans hx.symm))
    have h1 : y' ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [← Category.assoc, hy', Category.assoc, M.pb.w, ← Category.assoc, hy, hs]
    refine ⟨⟨y', h1⟩, Subtype.ext (Subtype.ext (M.pb.hom_ext ((hf _).trans hy') ?_))⟩
    exact (f ⟨y', h1⟩).1.2.trans hy.symm

end GlobalTheory.TrueGeo.ClosurePts
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_equiv_fibre : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ M.X) [IsClosedImmersion i], IsArithVar (i ≫ M.p) 0 → i (genericPoint Z) = M.j x → ∀ (K : Type) [Field K] (σ : F →+* K), ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃ {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x}, ∀ y, (E y).1.1 ≫ M.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  first | exact @GlobalTheory.TrueGeo.ClosurePts.main | exact GlobalTheory.TrueGeo.ClosurePts.main | (intros; apply GlobalTheory.TrueGeo.ClosurePts.main <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

set_option autoImplicit false

namespace GlobalTheory.RestrictRatSec

theorem top_le_of_below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) {U : Z.Opens}
    (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_appLE {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) (y : Sp K ⟶ Y)
    (z : Sp K ⟶ X) (e : z = y ≫ j) {U : X.Opens} {W : Y.Opens} (l : W ≤ j ⁻¹ᵁ U) (hW : below y ∈ W)
    (h : genericPoint Y ∈ W) (hz : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) :
    valAt y (fnOf W h ((j.appLE U W l).hom a)) =
      (z.appLE U ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  subst e
  rw [OfModel.valAt_fnOf y hW (top_le_of_below y hW), ← Scheme.Hom.appLE_comp_appLE y j U W ⊤ l
    (top_le_of_below y hW)]
  rfl

theorem mem_pullU {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c : (B.pull j).ι) (x : Y) :
    x ∈ (B.pull j).U c ↔ j x ∈ B.U (c PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem inf_le_pull {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    (B.pull j).U c ⊓ (B.pull j).U c' ≤ j ⁻¹ᵁ (B.U (c PUnit.unit) ⊓ B.U (c' PUnit.unit)) :=
  fun x hx => ⟨(mem_pullU B j c x).1 hx.1, (mem_pullU B j c' x).1 hx.2⟩

theorem val_pull_g {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    ((B.pull j).g c c').val =
      (j.appLE _ _ (inf_le_pull B j c c')).hom (B.g (c PUnit.unit) (c' PUnit.unit)).val := by
  have : (B.pull j).g c c' =
      res (inf_le_pull B j c c') (pullU j _ (B.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem exists_lift {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [SurjectiveOnStalks j] (x : Y)
    {f : Y.functionField} (hf : UnitAt x f) :
    ∃ (W : X.Opens) (hx : j x ∈ W) (a : Γ(X, W)), j x ∈ X.basicOpen a ∧
      fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.appLE W _ le_rfl).hom a) = f := by
  obtain ⟨b, -, hb⟩ := id hf
  obtain ⟨b', rfl⟩ := j.stalkMap_surjective x b
  obtain ⟨W, hx, a, rfl⟩ := X.presheaf.exists_germ_eq b'
  have e : fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.app W).hom a) = f := by
    rw [← algebraMap_germ (x := x) hx, ← hb]
    exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j W x hx a).symm
  refine ⟨W, hx, a, ?_, by rw [← Scheme.Hom.app_eq_appLE]; exact e⟩
  have := (unitAt_fnOf_iff (U := j ⁻¹ᵁ W) (x := x) hx _ _).1 (e ▸ hf)
  rw [← Scheme.preimage_basicOpen] at this
  exact this

theorem exists_restriction : ∀ (X Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (j : Y ⟶ X) [SurjectiveOnStalks j] (i : Z ⟶ X) (x : Y), i (genericPoint Z) = j x → ∀ (B : LB X), B.IsLB → ∀ (r : (B.pull j).ι → Y.functionFieldˣ), IsRatSec (B.pull j) r → ∀ (u : Y.functionFieldˣ), (∀ c, x ∈ (B.pull j).U c → UnitAt x ((u * r c : Y.functionFieldˣ) : Y.functionField)) → ∃ s : (B.pull i).ι → Z.functionFieldˣ, IsRatSec (B.pull i) s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Y) (y' : Sp K ⟶ Z) (c : B.ι), y ≫ j = y' ≫ i → below y = x → below y' = genericPoint Z → j x ∈ B.U c → valAt y' (s (fun _ => c) : Z.functionField) = valAt y ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) := by
  intro X Y Z _ _ j _ i x hi B hB r hr u hu
  obtain ⟨c₀, hc₀⟩ := exists_chart hB (j x)
  have hx₀ : x ∈ (B.pull j).U (fun _ => c₀) := (mem_pullU B j _ x).2 hc₀
  obtain ⟨W, hW, a, ha, e⟩ := exists_lift j x (hu _ hx₀)
  have hgW : genericPoint Z ∈ i ⁻¹ᵁ W := show i _ ∈ W from hi ▸ hW
  have hg₀ : genericPoint Z ∈ (B.pull i).U (fun _ => c₀) := (mem_pullU B i _ _).2 (hi ▸ hc₀)
  have hne : fnOf (i ⁻¹ᵁ W) hgW ((i.appLE W _ le_rfl).hom a) ≠ 0 := by
    refine UnitAt.ne_zero (x := genericPoint Z) ((unitAt_fnOf_iff hgW _ _).2 ?_)
    rw [← Scheme.Hom.app_eq_appLE, ← Scheme.preimage_basicOpen]
    exact show i _ ∈ X.basicOpen a from hi ▸ ha
  refine ⟨fun c => frameRat (B.pull i) _ hg₀ c * Units.mk0 _ hne, fun c c' h => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, isRatSec_frameRat (LB.isLB_pull hB i) _ hg₀ c c' h, mul_assoc]
  intro K _ y y' c hy hyx hy' hc
  have hxc : x ∈ (B.pull j).U (fun _ => c) := (mem_pullU B j _ x).2 hc
  have hgc : genericPoint Z ∈ (B.pull i).U (fun _ => c) := (mem_pullU B i _ _).2 (hi ▸ hc)
  have hb : below (y ≫ j) = j x := hyx ▸ rfl
  have h₁ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.U c ⊓ B.U c₀) := top_le_of_below _ (hb ▸ memInf hc hc₀)
  have h₂ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ W := top_le_of_below _ (hb ▸ hW)
  have hxx := memInf hxc hx₀
  have hgg := memInf hgc hg₀
  have e₁ : ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) =
      fnOf _ (gen_mem hxx) ((B.pull j).g (fun _ => c) (fun _ => c₀)).val *
        ((u * r (fun _ => c₀) : Y.functionFieldˣ) : Y.functionField) := by
    rw [Units.val_mul, Units.val_mul, hr _ _ (gen_mem hxx), mul_left_comm]
  have hxW : x ∈ j ⁻¹ᵁ W := hW
  rw [← hyx] at hxx hxW
  rw [← hy'] at hgg hgW
  have v₁ := valAt_appLE j y _ rfl (inf_le_pull B j (fun _ => c) (fun _ => c₀)) hxx (gen_mem hxx) h₁
    (B.g c c₀).val
  have v₂ := valAt_appLE i y' _ hy (inf_le_pull B i (fun _ => c) (fun _ => c₀)) hgg (gen_mem hgg) h₁
    (B.g c c₀).val
  have w₁ := congrArg (fun t => valAt y (fnOf _ (gen_mem hxx) t)) (val_pull_g B j (fun _ => c) (fun _ => c₀))
  have w₂ := congrArg (fun t => valAt y' (fnOf _ (gen_mem hgg) t)) (val_pull_g B i (fun _ => c) (fun _ => c₀))
  have t₁ := valAt_appLE j y _ rfl le_rfl hxW (gen_mem hxW) h₂ a
  have t₂ := valAt_appLE i y' _ hy le_rfl hgW (gen_mem hgW) h₂ a
  rw [e₁, ← e, OfModel.valAt_mul y (regAt_fnOf hxx _ _) (regAt_fnOf hxW _ _), Units.val_mul, Units.val_mk0]
  refine (congrArg (fun t => valAt y' (t * _)) (val_frameRat _ hg₀ _ hgc)).trans ?_
  refine (OfModel.valAt_mul y' (regAt_fnOf hgg _ _) (regAt_fnOf hgW _ _)).trans ?_
  exact congrArg₂ (· * ·) ((w₂.trans v₂).trans (w₁.trans v₁).symm) (t₂.trans t₁.symm)

end GlobalTheory.RestrictRatSec
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_extension : ∀ (X Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (j : Y ⟶ X) [SurjectiveOnStalks j] (i : Z ⟶ X) (x : Y), i (genericPoint Z) = j x → ∀ (B : LB X), B.IsLB → ∀ (r : (B.pull j).ι → Y.functionFieldˣ), IsRatSec (B.pull j) r → ∀ (u : Y.functionFieldˣ), (∀ c, x ∈ (B.pull j).U c → UnitAt x ((u * r c : Y.functionFieldˣ) : Y.functionField)) → ∃ s : (B.pull i).ι → Z.functionFieldˣ, IsRatSec (B.pull i) s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Y) (y' : Sp K ⟶ Z) (c : B.ι), y ≫ j = y' ≫ i → below y = x → below y' = genericPoint Z → j x ∈ B.U c → valAt y' (s (fun _ => c) : Z.functionField) = valAt y ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) := by
  first | exact @GlobalTheory.RestrictRatSec.exists_restriction | exact GlobalTheory.RestrictRatSec.exists_restriction | (intros; apply GlobalTheory.RestrictRatSec.exists_restriction <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HtModel

theorem ratVal_eq_valAt {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (f : Z.functionField) (y : CxPts q σ) : ratVal f y = valAt y.1 f := by
  by_cases h : RegAt (under y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hy : y ∈ CxPts.ptsIn q σ U := CxPts.mem_ptsIn.2 hU
    rw [ratVal_fnOf hy, OfModel.valAt_fnOf y.1 hU hy, CxPts.ev_eq hy]
    rfl
  · rw [ratVal, dif_neg h, valAt, dif_neg h]

theorem bijective_comp (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => ?_, fun σ => ?_⟩
  · exact IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun h a
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (I := RingHom.ker σ) (eq_bot_iff.2 fun n hn => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    exact Int.cast_eq_zero.1 hn
  refine ⟨IsFractionRing.lift (A := 𝓞 F) (K := F) hσ, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

open Classical in

theorem ht_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+), A.Induced M L k 0 → ∀ (x : Y.X) (a : ℝ), IsClosed ({x} : Set Y.X) → ArInt.IsPtHt L (M.j x) a → A.ht x = a / (((k : ℕ) : ℝ) * (A.n : ℕ)) := by
  intro F _ _ C Y A M L k ⟨_, r, hr, hinf, hfin⟩ x a hx ⟨h, H, ha⟩
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (M.j x)
  have := M.ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := GlobalTheory.T.closed_point_algebraic F Y M x hx
  have hri : Set.range i = closure {M.j x} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ M.p) 0 := M.ar.of_isClosedImmersion i hcΓ hd
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  have he : A.D.IsEqn x (eqn A.D x) := (A.D.exists_isEqn x).choose_spec
  have hu (c) (hc : x ∈ (L.B.pull M.j).U c) :
      UnitAt x (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) := by
    have := (he.nsmul k).iff_unitAt.1 (hr.isEqn c x hc)
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  obtain ⟨s, hs, hval⟩ := GlobalTheory.T.rational_section_extension M.X Y.X Z M.j i x hi L.B L.isLB r hr.isRatSec _ hu
  have hdeg := H.point Z i hcΓ hd s hs
  have hne := (ExtConj.main F).1

  obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have h₁ := GlobalTheory.T.local_equations_height_sum F Z (i ≫ M.p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => (k : ℕ) * A.lg v (hne v).some (E y).1) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ M.j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : M.j x ∈ L.B.U c := by
        have := Set.mem_iInter.1 (OfModel.le_chart M L.B _ (E y).1 (yt ≫ i) e₁ (i := fun _ => c) hU
          (x := IsLocalRing.closedPoint _) trivial) PUnit.unit
        rw [← (E y).2]
        exact this
      rw [hfin v _ (E y).1 (yt ≫ i) (fun _ => c) e₁ hU, hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc, (E y).2]
      simp)
  have h₂ (v) : ∑ᶠ y, ((k : ℕ) : ℝ) * A.lg v (hne v).some (E y).1 =
      (k : ℕ) * if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]
    exact congrArg _ (finsum_comp_equiv E (f := fun y => A.lg v (hne v).some y.1))
  replace h₁ := h₁.trans (congrArg (- ·) (finsum_congr h₂))

  have h₃ (σ : F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ M.p) (σ.comp (algebraMap (𝓞 F) F)), logNorm ((L.restr i).φ _) s y =
      (k : ℕ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi ℂ σ
    rw [← finsum_subtype_eq_finsum_cond, mul_finsum]
    refine finsum_eq_of_bijective E E.bijective fun y => ?_
    have hp := CxPts.mem_ptsIn.1 (CxPts.mem_pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y)
    unfold logNorm
    generalize CxPts.pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = c at hp ⊢
    have hxc : M.j x ∈ L.B.U (c PUnit.unit) := by
      have := Set.mem_iInter.1 hp PUnit.unit
      rw [← hi, ← (hE y).2]
      exact this
    have hx' : under (E y).1 = x := (E y).2
    have hxc' : x ∈ (L.B.pull M.j).U c := Set.mem_iInter.2 fun _ => hxc
    have hg : A.D.GeneratesAt (under (E y).1) ((eqn A.D x)⁻¹ : Y.Fnˣ) := by
      rw [hx', Units.val_inv_eq_inv_val]
      exact CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hreg : ((k : ℕ) • A.D).RegularAt (under (E y).1) ((((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) ^ (k : ℕ)) := by
      rw [hx', ← Units.val_pow_eq_pow_val, inv_pow, Units.val_inv_eq_inv_val]
      exact (CartierDiv.isEqn_iff_generatesAt_inv.1 (he.nsmul k)).regularAt
    have e₁ := hinf σ (E y).1 (Points.PtsOver.map i rfl _ y) c _ (hE y).1.symm (hx'.symm ▸ hxc') hreg
    rw [C.pn_mPow _ _ _ _ _ _ _ hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at e₁
    have h0 : ‖ratVal (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) (E y).1‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (by rw [hx']; exact hu c hxc'))
    have e₂ := congrArg Real.log e₁
    have h0' : C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) (E y).1 ^ (k : ℕ) ≠ 0 :=
      right_ne_zero_of_mul (e₁.trans_ne (mul_ne_zero (pow_ne_zero _ h0) (Real.exp_ne_zero _)))
    rw [Real.log_mul (Real.exp_ne_zero _) h0', Real.log_mul (pow_ne_zero _ h0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow, ratVal_eq_valAt] at e₂
    have e₃ := hval ℂ _ _ (c PUnit.unit) (hE y).1 (E y).2 (hE y).2 hxc
    have e₄ := (L.φ _).pull_φ i rfl c y
    rw [ratVal_eq_valAt]
    refine (congrArg₂ (fun a b => Real.log ‖a‖ - b / 2) e₃ e₄).trans ?_
    push_cast at e₂
    change Real.log ‖valAt (E y).1.1 (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn)‖ - _ = _
    push_cast
    linarith
  unfold HermLB.curveDeg at hdeg
  rw [h₁, ← finsum_eq_of_bijective _ (bijective_comp F) fun σ => (h₃ σ).symm, hi, ha,
    GlobalTheory.T.residue_embeddings_card F Y M x hx, ← mul_finsum, ← mul_finsum, finsum_eq_sum_of_fintype (α := F →+* ℂ)] at hdeg
  obtain ⟨_, _⟩ := ExtConj.pts Y x hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hk : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  rw [Adl.ht, div_eq_div_iff (by positivity) (by positivity)]
  rw [Nat.cast_mul] at hdeg
  linear_combination (-((A.n : ℕ) : ℝ)) * hdeg

end GlobalTheory.TrueGeo.HtModel
end
end
