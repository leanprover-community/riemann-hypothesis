import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocalChartDepthEqIntegralBiextDepth
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChartStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverId

section
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.JetDim

variable {V : Type} [CommRing V]

def tanAll (κ : Type) [DecidableEq κ] : Jet V κ 1 →ₐ[V] TrivSqZeroExt V (κ → V) :=
  liftJet (MvPolynomial.aeval fun i => TrivSqZeroExt.inr (Pi.single i (1 : V))) (by
    have h1 : Ideal.span (Set.range fun i => (MvPolynomial.aeval fun i : κ =>
        (TrivSqZeroExt.inr (Pi.single i (1 : V)) : TrivSqZeroExt V (κ → V))) (MvPolynomial.X i : MvPolynomial κ V))
        ≤ RingHom.ker (TrivSqZeroExt.fstHom V V (κ → V)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    refine le_bot_iff.1 ((Ideal.pow_right_mono h1 _).trans ?_)
    rw [show 1 + 1 = 2 from rfl, pow_two, Ideal.mul_le]
    intro a ha b hb
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    refine (Submodule.mem_bot _).2 (TrivSqZeroExt.ext ?_ ?_) <;> simp [ha', hb'])

theorem tanAll_X (κ : Type) [DecidableEq κ] (i : κ) :
    tanAll (V := V) κ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = TrivSqZeroExt.inr (Pi.single i (1 : V)) := by
  show MvPolynomial.aeval _ (MvPolynomial.X i) = _
  simp

theorem card_le_of_surjective [Nontrivial V] {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ]
    (ψ : Jet V κ' 1 →ₐ[V] Jet V κ 1) (hψ : Function.Surjective ψ) : Fintype.card κ ≤ Fintype.card κ' := by
  let φ : MvPolynomial κ' V →ₐ[V] TrivSqZeroExt V (κ → V) :=
    ((tanAll κ).comp ψ).comp (Ideal.Quotient.mkₐ V _)
  let v : κ' → κ → V := fun j => (φ (MvPolynomial.X j)).snd
  have hmem : ∀ p, (φ p).snd ∈ Submodule.span V (Set.range v) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algHom_C, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      exact zero_mem _
    | add p q hp hq =>
      rw [map_add, TrivSqZeroExt.snd_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) (Submodule.smul_mem _ _ hp)
  have htop : Submodule.span V (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun V κ).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := hψ (Ideal.Quotient.mk _ (MvPolynomial.X i))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : (φ p).snd = Pi.basisFun V κ i := by
      show (tanAll κ (ψ (Ideal.Quotient.mk _ p))).snd = _
      rw [ha, tanAll_X, TrivSqZeroExt.snd_inr, Pi.basisFun_apply]
    rw [← this]
    exact hmem p
  have h := finrank_range_le_card (R := V) v
  rw [Set.finrank, htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra V A] : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [Formalism.L2.Pj.homAt, spMap]

theorem exists_surjective {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} {z : GlobalTheory.PowGerm.JetPts G κ}
    {z' : GlobalTheory.PowGerm.JetPts G κ'} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (hz' : GlobalTheory.PowGerm.IsUnivJ G κ' z') (m : ℕ) :
    ∃ ψ : Jet V κ' m →ₐ[V] Jet V κ m, Function.Surjective ψ := by
  have hk : ∀ σ : Type, RingHom.ker (jetAug : Jet V σ m →ₐ[V] V) ^ (m + 1) = ⊥ := fun σ => by
    have ea : (jetAug : Jet V σ m →ₐ[V] V) = Chart.jetAug V σ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow σ m
  obtain ⟨ψ, ⟨a, b⟩, -⟩ := hz'.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  obtain ⟨ψ', ⟨a', b'⟩, -⟩ := hz.2.2 _ jetAug m (hk κ') (z' m) (hz'.2.1 m)
  obtain ⟨χ, -, hu⟩ := hz.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  have e1 := hu (AlgHom.id V _) ⟨AlgHom.comp_id _, by rw [homAt_id, Category.id_comp]⟩
  have e2 := hu (ψ.comp ψ') ⟨by rw [← AlgHom.comp_assoc, a, a'], by
    rw [← homAt_comp, Category.assoc, ← b', ← b]⟩
  exact ⟨ψ, fun y => ⟨ψ' y, AlgHom.congr_fun (e2.trans e1.symm) y⟩⟩

end GlobalTheory.ChartCmp.JetDim

theorem GlobalTheory.ChartCmp.univJ_dim_unique : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  intro V _ _ G _ d d' x x' h h'
  obtain ⟨ψ, hψ⟩ := JetDim.exists_surjective h h' 1
  obtain ⟨ψ', hψ'⟩ := JetDim.exists_surjective h' h 1
  have a := JetDim.card_le_of_surjective ψ hψ
  have b := JetDim.card_le_of_surjective ψ' hψ'
  simp only [Fintype.card_prod, Fintype.card_fin, one_mul] at a b
  omega
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalJetCoordinates_dim_unique : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  atlas_forward_decl GlobalTheory.ChartCmp.univJ_dim_unique
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_appTop_integralModel_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  first | exact @GlobalTheory.ModelSquareFunctions.surjective_appTop_square | exact GlobalTheory.ModelSquareFunctions.surjective_appTop_square | (intros; apply GlobalTheory.ModelSquareFunctions.surjective_appTop_square <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem dualMap_injective_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem intData_models_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I I' : IntData Xo c T io y), ∃ n : SABMap I.G I'.G (𝟙 (Sp T.V)), ∀ τ i, (I.ub τ i).left ≫ n.φ = (I'.ub τ i).left := by
  intro E _ _ _ H Dw l Xo c T io y I I'
  letI := io.toAlgebra
  obtain ⟨k, n, hk, hn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr y.x I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2
  refine ⟨n, fun τ i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := I.lift τ i
  obtain ⟨v, hv1, hv2⟩ := I'.lift τ i
  have hnw : n.φ ≫ I'.G.G.hom = I.G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  have hkw : k.φ ≫ I'.t'.G.hom = I.t'.G.hom := k.cart.1.w.trans (Category.comp_id _)
  have huv : u ≫ k.φ = v := by
    apply I'.m1.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (u ≫ ·) hk).trans (hu1.trans hv1.symm)
    · rw [Category.assoc, hkw]
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      have e1 : (u ≫ I.m2.φ) ≫ I.G.G.hom = (v ≫ I'.m2.φ) ≫ I'.G.G.hom := by
        rw [hu2, hv2, Category.assoc, Category.assoc, Over.w (I.ub τ i), Over.w (I'.ub τ i)]
      rw [Category.assoc, Category.assoc, ← I.m2.cart.1.w, ← I'.m2.cart.1.w]
      simpa only [Category.assoc] using e1
  have hsep : IsSeparated I'.G.G.hom := I'.G.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _)
      (dualMap_injective_of_injective _ (IsFractionRing.injective T.V T.Fr))
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant I'.G.G.hom ?_ (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) ?_
  · rw [Category.assoc, hnw, Over.w (I.ub τ i), Over.w (I'.ub τ i)]
  · rw [← Category.assoc, ← hu2, ← hv2, Category.assoc, hn, ← Category.assoc, huv]

end GlobalTheory.ChartCmp
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_integralModels_matching_lieBases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I I' : IntData Xo c T io y), ∃ n : SABMap I.G I'.G (𝟙 (Sp T.V)), ∀ τ i, (I.ub τ i).left ≫ n.φ = (I'.ub τ i).left := by
  first | exact @GlobalTheory.ChartCmp.intData_models_iso | exact GlobalTheory.ChartCmp.intData_models_iso | (intros; apply GlobalTheory.ChartCmp.intData_models_iso <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChartDepth_eq_integralBiextDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), letI := io.toAlgebra; ∀ BT : FB T.V (chD C.ch) (𝓞 E), BT.FK T.Fr = C.ch.B.FK T.Fr → (∀ a, BT.actK T.Fr a = C.ch.B.actK T.Fr a) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuAlg Dw T BT C.ch.h C.ch.uvec e k a n := by
  first | exact @GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | exact GlobalTheory.ChartCmp.nuLocC_eq_nuAlg | (intros; apply GlobalTheory.ChartCmp.nuLocC_eq_nuAlg <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_depth_le_of_related : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (d : ℕ) (B B' : FB T.V d (𝓞 E)) (φ φi : Pt T.V 1 d) (h h' : PS T.Fr 2 d) (u u' : Lt1 Dw → Fin d → T.Fr), (∀ m, ∃ ε : PS T.V 2 d, JRel m B B' φ φi ε) → B.IsCanonGauge T.Fr h → B'.IsCanonGauge T.Fr h' → (∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ) → (∀ ℓ, u ℓ = ((dLin φ).map (algebraMap T.V T.Fr)).mulVec (u' ℓ)) → ∀ (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuAlg Dw T B h u e k a n ≤ nuAlg Dw T B' h' u' e k a n := by
  first | exact @GlobalTheory.ChartCmp.nuAlg_le_of_jrel | exact GlobalTheory.ChartCmp.nuAlg_le_of_jrel | (intros; apply GlobalTheory.ChartCmp.nuAlg_le_of_jrel <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nuAlg_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (t t' : SAB H (Sp T.V)) (n : SABMap t t' (𝟙 (Sp T.V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB T.V d (𝓞 E)) (B' : FB T.V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber T.V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber T.V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → T.V) (uv' : Fin d' → Fin d' → T.V)
    (x : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp T.V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp T.V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp T.V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp T.V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp T.V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp T.V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp T.V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    (h : PS T.Fr 2 d) (h' : PS T.Fr 2 d') (hg : B.IsCanonGauge T.Fr h) (hg' : B'.IsCanonGauge T.Fr h')
    (uT : Lt1 Dw → Fin d → T.V) (uT' : Lt1 Dw → Fin d' → T.V)
    (v : Lt1 Dw → (Sp (DualNumber T.V) ⟶ t.G.left))
    (hv : ∀ ℓ, IsCombAtG t (𝟙 (Sp T.V)) (dirs x) (uT ℓ) (v ℓ))
    (hv' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp T.V)) (dirs x') (uT' ℓ) (v ℓ ≫ n.φ))
    (u : Lt1 Dw → Fin d → T.Fr) (u' : Lt1 Dw → Fin d' → T.Fr)
    (huT : ∀ ℓ i, u ℓ i = algebraMap T.V T.Fr (uT ℓ i)) (huT' : ∀ ℓ i, u' ℓ i = algebraMap T.V T.Fr (uT' ℓ i))
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ)
    (ε k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (N : ℕ) :
    nuAlg Dw T B h u ε k a N ≤ nuAlg Dw T B' h' u' ε k a N := by
  obtain ⟨x'', -, hx''u, -, -⟩ := GlobalTheory.T.pushChartAlt E H T.V t t' n d x
  have hd : d = d' := GlobalTheory.T.universalJetCoordinates_dim_unique T.V t'.G d d' x'' x' (hx''u hu) hu'
  subst hd
  obtain ⟨φ, φi, hrel, hlin⟩ := GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id E H hs T.V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  refine GlobalTheory.T.biextension_depth_le_of_related E H Dw l Xo c hs T io d B B' φ φi h h' u u' hrel hg hg' heig ?_ ε k a N
  intro ℓ
  have hu1 : u ℓ = fun i => algebraMap T.V T.Fr (uT ℓ i) := funext (huT ℓ)
  have hu2 : u' ℓ = fun j => algebraMap T.V T.Fr (uT' ℓ j) := funext (huT' ℓ)
  rw [hu1, hu2, hlin (uT ℓ) (uT' ℓ) (v ℓ) (hv ℓ) (hv' ℓ)]
  funext i
  exact RingHom.map_mulVec (algebraMap T.V T.Fr) (dLin φ) (uT' ℓ) i

theorem nuLocC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntegralChartA3 Xo c T io y) (e k : ℕ)
      (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n ≤ nuLocC C' e k a n := by
  letI := H.starRing
  intro hs T io y C C' e k a n
  letI := io.toAlgebra
  obtain ⟨BT, hF, hA, hP1, hP2, hSy, hAd, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨BT', hF', hA', hP1', hP2', hSy', hAd', hK'⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  obtain ⟨hFK, hActK, hG, hGc⟩ := hK T.Fr
  obtain ⟨hFK', hActK', hG', hGc'⟩ := hK' T.Fr
  rw [GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C BT hFK hActK e k a n,
    GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C' BT' hFK' hActK' e k a n]
  obtain ⟨nm, hnm⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io _ C.I C'.I
  have hsurj := GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io _ C'.I
  have hU := GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y
  have e1 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C.ch.h = C.ch.h := by
    ext
    simp
  have e2 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C'.ch.h = C'.ch.h := by
    ext
    simp
  rw [e1] at hGc
  rw [e2] at hGc'
  have gen := C.gen
  have gen' := C'.gen
  unfold IsGenFibreChart at gen gen'
  refine nuAlg_le_of_charts Xo c hs T io C.I.G C'.I.G nm hsurj (chD C.ch) (chD C'.ch) BT BT' C.tgT C'.tgT
    (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_ (hU C) (hU C') ?_ ?_
    C.ch.h C'.ch.h ((hG _).2 hGc) ((hG' _).2 hGc') C.uvecT C'.uvecT (fun ℓ => (C.I.ub ℓ.1 ℓ.2).left)
    (fun ℓ => C.dirT ℓ) ?_ C.ch.uvec C'.ch.uvec gen.1.2.2.2.2.2.2 gen'.1.2.2.2.2.2.2 ?_ e k a n
  · rw [hF, hA]
    exact C.chartT
  · rw [hF', hA']
    exact C'.chartT
  · rw [hF, hA, hP1, hP2, hSy, hAd]
    exact C.frameT
  · rw [hF', hA', hP1', hP2', hSy', hAd']
    exact C'.frameT
  · intro ℓ
    rw [hnm]
    exact C'.dirT ℓ
  · intro b ℓ
    have h2 : dAct T.Fr BT' b = dAct T.Fr C'.ch.B b := by
      funext i j
      simp only [dAct, hActK' b]
    rw [h2]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C' b ℓ

theorem chartIndep_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartIndep Xo c := by
  intro E _ _ _ H Dw l Xo c inst hs
  have hst : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hs
  subst hst
  intro T io y C C' e k a n
  exact le_antisymm (nuLocC_le Xo c hs T io y C C' e k a n) (nuLocC_le Xo c hs T io y C' C e k a n)

end GlobalTheory.ChartCmp
end
end
