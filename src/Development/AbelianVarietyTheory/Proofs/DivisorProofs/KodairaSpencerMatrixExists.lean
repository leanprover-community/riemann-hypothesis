import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihilaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSExist.ksRow_exists_lieComb | exact GlobalTheory.KSExist.ksRow_exists_lieComb | (intros; apply GlobalTheory.KSExist.ksRow_exists_lieComb <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme <;> assumption)
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem conj_embK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksExist : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type)
    [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q →
    GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ hx
  have P := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G x'
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G y.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have hL := (P.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → K,
      ∃ w, IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, conj_embK]) a₀
  choose cf w hw using hrow
  refine ⟨fun k => cf k.1 k.2.1 k.2.2, A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub,
    hb, hπ, hπ', rfl, hpol, hu, fun σ k => hbl ⟨σ, k⟩, fun τ a₀ => ⟨w τ a₀, (hw τ a₀).1, (hw τ a₀).2⟩⟩

end GlobalTheory.KSExist
end
end
