import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LatContMapContinuous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

section
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem taylor_congr {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    {f f' : (I → ℂ) → ℂ} (h : f =ᶠ[nhds 0] f') : taylor N t f = taylor N t f' := by
  unfold taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem isAb_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h

theorem gaussManinPeriods_of_parts : ∀ ε : ℤˣ, GlobalTheory.PeriodFamily.FamUnif → PExist → PHom → PSpan → PLie → PEnd → PChern ε → PFix → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  intro ε HF HE HH HS HL HEn HC HX HT
  have pm : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (L : LB A.left), L.IsLB → ∀ (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P → IsPeriodMap ε u P :=
    fun A _ g hA hg L hL u P hP ↦ ⟨(HS A g hA hg L u P hP).1, (HS A g hA hg L u P hP).2, HL A g hA hg L u P hP,
      fun α _ M ↦ HEn A g hA L u P hP α M, fun H χ ψ ↦ HC A g hA L u P hP L u hL rfl H χ ψ⟩
  refine ⟨ε, fun B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0 hy A _ φ hφ m L hL A₀ _ φ₀ hφ₀ L₀ hL₀ u₀ ↦ ?_⟩
  obtain ⟨r, u, τ, hr, hrU, hhol, ⟨W, hW, hW0⟩, c1, c2, c3, c4⟩ :=
    HF B 𝒜 g h𝒜 hg I U y hU h0 hy A φ hφ L hL A₀ φ₀ hφ₀ L₀ u₀
  have hA : ∀ z, IsAbelianScheme (A z) := fun z ↦ isAb_pull (hφ z) h𝒜
  have hA₀ : IsAbelianScheme A₀ := isAb_pull hφ₀ h𝒜
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have gA : ∀ z, SmoothOfRelativeDimension g (A z).hom := fun z ↦
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (hφ z).1 hg
  have gA₀ : SmoothOfRelativeDimension g A₀.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hφ₀.1 hg
  choose P hP using fun z ↦ HH (A z) g (hA z) (L z) (u z)
  obtain ⟨P₀, hP₀⟩ := HH A₀ g hA₀ L₀ u₀
  let V : Opens (I → ℂ) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have V0 : (0 : I → ℂ) ∈ V := Metric.mem_ball_self hr
  let F : Fam I g u₀.Λ :=
    { V := V
      τ := { toFun x z := (τ z x : Fin g → ℂ)
             map_zero' := funext fun z ↦ by simp
             map_add' a b := funext fun z ↦ by simp }
      hol x := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (c3 x) }
  have ya : ∀ b, AnalyticOnNhd ℂ (fun z ↦ y z b) V := fun b ↦
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball ((hy b).mono hrU)
  let σ : B →ₐ[ℂ] Hol F.V :=
    { toFun b := Hol.mk _ (ya b)
      map_one' := Subtype.ext (funext fun z ↦ map_one (y z))
      map_mul' a b := Subtype.ext (funext fun z ↦ map_mul (y z) a b)
      map_zero' := Subtype.ext (funext fun z ↦ map_zero (y z))
      map_add' a b := Subtype.ext (funext fun z ↦ map_add (y z) a b)
      commutes' a := Subtype.ext (funext fun z ↦ (y z).commutes a) }
  have hσ : ∀ b, ∀ z ∈ V, (σ b).fn z = y z b := fun b z hz ↦ Hol.fn_mk _ (ya b) hz
  let e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V) :=
    { E q := (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1
      w p hp := by
        have e1 : (show Sp ℂ ⟶ (A p.1).left from ((u p.1).ex p.2).left) ≫ (A p.1).hom = 𝟙 _ := Over.w ((u p.1).ex p.2)
        rw [Category.comp_id, Category.assoc, (hφ p.1).1.w, ← Category.assoc, e1, Category.id_comp]
        rfl
      per l p _ := by
        have : (u p.1).ex (p.2 + (τ p.1 l : Fin g → ℂ)) = (u p.1).ex p.2 := by
          rw [(u p.1).ex_add, ((u p.1).ker _).2 (τ p.1 l).2, _root_.mul_one]
        exact congrArg (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A p.1 ↦ (show Sp ℂ ⟶ (A p.1).left from x.left) ≫ φ p.1) this
      hol U' f := by
        have := hhol U' f
        simp only [Set.mem_prod, Set.mem_univ, and_true] at this
        exact this }
  haveI : IsSeparated (𝒜.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]
    haveI := h𝒜.proper
    infer_instance
  choose per hper using HE I g u₀.Λ F B 𝒜.left _ _ e ⟨W, hW, hW0⟩
  have fix : ∀ x (c : primDR 𝒜), ∀ z ∈ V, P z (τ z x) ((m z).pull c) = (per c.1 x).fn z := fun x c z hz ↦
    HX I g u₀.Λ F B 𝒜 h𝒜 _ e z hz _ (fun b ↦ (hσ b z hz).symm) (A z) (hA z) (φ z) (m z) (L z) (u z) (fun _ ↦ rfl)
      (τ z).toAddMonoidHom (fun _ ↦ rfl) (P z) (hP z) c _ (hper c.1) x
  have nV : (V : Set (I → ℂ)) ∈ nhds (0 : I → ℂ) := V.isOpen.mem_nhds V0
  refine ⟨Metric.ball 0 r, u, τ, P, P₀, Metric.isOpen_ball, V0, hrU, pm A₀ g hA₀ gA₀ L₀ hL₀ u₀ P₀ hP₀,
    fun z _ ↦ pm _ g (hA z) (gA z) _ (hL z) _ _ (hP z), c1, c2, c3, c4,
    fun x c ↦ (per c.1 x).analytic.differentiableOn.congr (fix x c), ?_⟩
  intro D _ _ π κ hκ hπ N t ht hN j hj A' _ φ' hφ' m' i h hi k x d hd c
  rw [HT I g B 𝒜 h𝒜 hg (y 0) A₀ φ₀ hφ₀ L₀ u₀ F σ e V0 (fun b ↦ (hσ b 0 V0).symm) c1 (fun x ↦ c2 x) P₀ hP₀ D π κ hκ hπ N t ht hN j
    (fun b ↦ (hj b).trans (taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (hσ b z hz).symm)))
    A' φ' hφ' m' i h hi k x d hd c _ (hper c.1)]
  exact taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (fix x c z hz).symm)

end GlobalTheory.AnPer
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

open GlobalTheory.LocLift

theorem exists_core {X : Scheme.{0}} (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] {g m : ℕ} {B : Set (Fin m → ℂ)}
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G))
    (hs : LocallyOfFiniteType s) (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (hB : IsOpen B)
    (hb₀ : b₀ ∈ B) (hys : ∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) (hy : IsHolTo B y) (he₀ : IsExp (y b₀) e₀)
    {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (P₀ : La →+ (Fin g → ℂ))
    (hi : Function.Injective P₀) (hsp : Submodule.span ℝ (Set.range P₀) = ⊤) (hk : ∀ z, e₀ z = 1 ↔ z ∈ P₀.range) :
    ∃ (C : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))),
      IsOpen C ∧ b₀ ∈ C ∧ C ⊆ B ∧ e b₀ = e₀ ∧ P b₀ = P₀ ∧
      IsHolTo (C ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧
      (∀ b ∈ C, IsExp (y b) (e b) ∧ (∀ z, e b z = 1 ↔ z ∈ (P b).range) ∧ Function.Injective (P b) ∧
        Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range) ∧
      (∀ x, DifferentiableOn ℂ (fun b => P b x) C) ∧
      ∀ (α : G ⟶ G) [IsMonHom α] (M₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, e₀ (M₀ w) = e₀ w ≫ α) →
        ∀ b ∈ C, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ w, e b (M w) = e b w ≫ α) ∧
          ∀ x x', P₀ x' = M₀ (P₀ x) → P b x' = M (P b x) := by
  classical
  have : IsProper G.hom := hG.proper
  obtain ⟨B', e, r, hB'o, hb₀', hB'B, he0, hr, hol, hexp, hlift⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) X s G g m B y b₀ e₀ hs hG hg hB hb₀ hys hy he₀
  have hl : HasLifts B' y e := hlift
  have hyB' : IsHolTo B' y := isHolTo_mono hy hB'o hB'B
  have hk' : ∀ z, e b₀ z = 1 ↔ z ∈ P₀.range := by rw [he0]; exact hk
  obtain ⟨P, hP0, hev⟩ := exists_periods GlobalTheory.latContinuation hB'o hb₀' hyB' hr hol
    (fun b hb => ⟨(hexp b hb).1, (hexp b hb).2⟩) hl P₀ hi hsp hk'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.Eventually.and (hB'o.mem_nhds hb₀' : ∀ᶠ b in 𝓝 b₀, b ∈ B') hev)
  have hCo : IsOpen (Metric.ball b₀ ε) := Metric.isOpen_ball
  have hb₀C : b₀ ∈ Metric.ball b₀ ε := Metric.mem_ball_self hε
  have hCB' : Metric.ball b₀ ε ⊆ B' := fun b hb => (hball b hb).1
  have hadd : ∀ b ∈ B', ∀ z w, e b (z + w) = e b z * e b w := fun b hb => (hexp b hb).1.1
  have hsurj : ∀ b ∈ B', Function.Surjective (e b) := fun b hb => (hexp b hb).1.2.1
  have hrad : ∀ b ∈ B', ∀ z, ‖z‖ < r → e b z = 1 → z = 0 := fun b hb => (hexp b hb).2
  refine ⟨Metric.ball b₀ ε, e, P, hCo, hb₀C, hCB'.trans hB'B, he0, hP0,
    isHolTo_mono hol (hCo.prod isOpen_univ) (Set.prod_mono hCB' subset_rfl),
    fun b hb => ⟨(hexp b (hCB' hb)).1, (hball b hb).2.2⟩,
    fun x b hb => ((hball b hb).2.1 x).differentiableWithinAt, ?_⟩
  intro α _ M₀ hM₀
  have hxadd : ∀ b ∈ B', ∀ z w, e b (z + w) ≫ α = (e b z ≫ α) * (e b w ≫ α) := by
    intro b hb z w
    rw [hadd b hb, MonObj.mul_comp]
  have huniq : ∀ b ∈ B', ∀ M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ w, e b (M w) = e b w ≫ α) →
      (∀ w, e b (M' w) = e b w ≫ α) → M = M' :=
    fun b hb M M' h h' => linear_lift_unique (hadd b hb) hr (hrad b hb) (fun z => (h z).trans (h' z).symm)
  have hloc : ∀ b₁ ∈ Metric.ball b₀ ε, ∃ F : (Fin m → ℂ) → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)),
      ContinuousAt F b₁ ∧ ∀ᶠ b in 𝓝 b₁, ∀ z, e b (F b z) = e b z ≫ α := by
    intro b₁ hb₁
    have hW : IsOpen (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) := hB'o.prod isOpen_univ
    have hxhol : IsHolTo (B' ×ˢ (Set.univ : Set (Fin g → ℂ)))
        (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (e q.1 q.2 ≫ α).left) :=
      isHolTo_congr (isHolTo_comp_hom hol α.left) (fun q _ => by simp only [Over.comp_left])
    have h0 : e b₁ 0 = e b₁ 0 ≫ α := by
      rw [hom_zero (hadd b₁ (hCB' hb₁)), MonObj.one_comp]
    obtain ⟨ζ, -, hζa, hζe⟩ := hl.lift (V := (Fin m → ℂ) × (Fin g → ℂ))
      (W := B' ×ˢ (Set.univ : Set (Fin g → ℂ))) (β := Prod.fst)
      (fun q => e q.1 q.2 ≫ α) hW
      (show ((b₁, 0) : (Fin m → ℂ) × (Fin g → ℂ)) ∈ B' ×ˢ (Set.univ : Set (Fin g → ℂ)) from ⟨hCB' hb₁, trivial⟩)
      differentiableOn_fst (fun q hq => hq.1) hxhol h0
    have hpt : Continuous (fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) := by fun_prop
    have hcont : ContinuousAt (fun b : Fin m → ℂ => fderiv ℂ ζ (b, 0)) b₁ :=
      ContinuousAt.comp (g := fderiv ℂ ζ) (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ)))
        hζa.fderiv.continuousAt hpt.continuousAt
    have hA : ∀ᶠ b in 𝓝 b₁, AnalyticAt ℂ ζ (b, 0) :=
      Filter.Tendsto.eventually hpt.continuousAt hζa.eventually_analyticAt
    have hE : ∀ᶠ b in 𝓝 b₁, ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), e b (ζ (b, w)) = e b w ≫ α := by
      have h := hζe
      rw [nhds_prod_eq] at h
      exact h.curry
    refine ⟨fun b => (fderiv ℂ ζ (b, 0)).comp (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)),
      hcont.clm_comp continuousAt_const, ?_⟩
    filter_upwards [hA, hE, hB'o.mem_nhds (hCB' hb₁)] with b hAb hEb hb
    intro z
    have hζb0 : e b (ζ (b, 0)) = 1 := by
      rw [hEb.self_of_nhds, hom_zero (hadd b hb), MonObj.one_comp]
    have hinr : HasFDerivAt (fun w : Fin g → ℂ => (b, w))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) 0 := by
      exact hasFDerivAt_prodMk_right b 0
    have hder := (hAb.differentiableAt.hasFDerivAt.comp (0 : Fin g → ℂ) hinr).sub_const (ζ (b, 0))
    have hev0 : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), e b ((fun w => ζ (b, w) - ζ (b, 0)) w) = e b w ≫ α := by
      filter_upwards [hEb] with w hw
      have h1 : e b (ζ (b, w)) = e b (ζ (b, w) - ζ (b, 0)) * e b (ζ (b, 0)) := by
        rw [← hadd b hb, sub_add_cancel]
      rw [hζb0, _root_.mul_one] at h1
      rw [← h1]
      exact hw
    have key := fderiv_lift (x := fun w => e b w ≫ α) (hxadd b hb) (hadd b hb) (hsurj b hb) hr (hrad b hb)
      hder.differentiableAt hev0 z
    rw [hder.fderiv] at key
    exact key
  have hexM : ∀ b, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), b ∈ Metric.ball b₀ ε → ∀ w, e b (M w) = e b w ≫ α := by
    intro b
    by_cases hb : b ∈ Metric.ball b₀ ε
    · obtain ⟨F, -, hF⟩ := hloc b hb
      exact ⟨(F b).toLinearMap, fun _ w => hF.self_of_nhds w⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose Mf hMf using hexM
  have hPx : ∀ c ∈ Metric.ball b₀ ε, ∀ x, e c (P c x) = 1 :=
    fun c hc x => ((hball c hc).2.2.1 _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)
  intro b hb
  refine ⟨Mf b, hMf b hb, ?_⟩
  intro x x' hxx'
  have hzero := eq_zero_of_small (B := Metric.ball b₀ ε) (convex_ball b₀ ε).isPreconnected
    (d := fun c => Mf c (P c x) - P c x') ?_ hr ?_ hb₀C ?_
  · exact (sub_eq_zero.1 (hzero b hb)).symm
  · intro c hc
    obtain ⟨F, hFc, hF⟩ := hloc c hc
    have hPc : ContinuousAt (fun c' => P c' x) c := ((hball c hc).2.1 x).continuousAt
    have hPc' : ContinuousAt (fun c' => P c' x') c := ((hball c hc).2.1 x').continuousAt
    have hcont : ContinuousAt (fun c' => F c' (P c' x) - P c' x') c := (hFc.clm_apply hPc).sub hPc'
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hF, hCo.mem_nhds hc] with c' hc' hc'C
    have hM : Mf c' = (F c').toLinearMap :=
      huniq c' (hCB' hc'C) _ _ (hMf c' hc'C) (fun w => hc' w)
    rw [hM]
    rfl
  · intro c hc hlt
    beta_reduce at hlt ⊢
    apply hrad c (hCB' hc) _ hlt
    rw [hom_sub_eq_one (hadd c (hCB' hc)), hMf c hc, hPx c hc x, hPx c hc x', MonObj.one_comp]
  · have hM : Mf b₀ = M₀ := huniq b₀ (hCB' hb₀C) _ _ (hMf b₀ hb₀C) (fun w => by rw [he0]; exact hM₀ w)
    show Mf b₀ (P b₀ x) - P b₀ x' = 0
    rw [hM, hP0, hxx', sub_self]

theorem exists_fibre {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsAbelianScheme G) {t t' : Sp ℂ ⟶ X} (ht : t' = t)
    {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left} (hφ : IsGrpPullback A G t φ) {L : LB A.left} (hL : L.IsLB) {g : ℕ}
    {e : (Fin g → ℂ) → (Over.mk t' ⟶ G)} (he : IsExp t' e) {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hi : Function.Injective P) (hsp : Submodule.span ℝ (Set.range P) = ⊤)
    (hd : DiscreteTopology P.range) :
    ∃ (u : HolUnif A L g) (τ : La ≃+ u.Λ), (∀ w, (u.ex w).left ≫ φ = (e w).left) ∧ ∀ x, (τ x : Fin g → ℂ) = P x := by
  subst ht
  have hA : IsAbelianScheme A := by
    obtain ⟨h1, h2, h3, h4⟩ := hG
    refine ⟨?_, MorphismProperty.of_isPullback hφ.1 h2, MorphismProperty.of_isPullback hφ.1 h3,
      MorphismProperty.of_isPullback hφ.1 h4⟩
    haveI := h1
    refine ⟨?_⟩
    apply Over.OverMorphism.ext
    apply hφ.1.hom_ext
    · have hw : φ ≫ G.hom = A.hom ≫ t' := hφ.1.w
      let x₀ : Over.mk ((A ⊗ A).hom ≫ t') ⟶ G := Over.homMk ((fst A A).left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      let y₀ : Over.mk ((A ⊗ A).hom ≫ t') ⟶ G := Over.homMk ((snd A A).left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e1 := hφ.2 (A ⊗ A) (fst A A) (snd A A) x₀ y₀ rfl rfl
      have e2 := hφ.2 (A ⊗ A) (snd A A) (fst A A) y₀ x₀ rfl rfl
      have hb : (β_ A A).hom = lift (snd A A) (fst A A) := by ext <;> simp
      have m1 : fst A A * snd A A = (μ : A ⊗ A ⟶ A) := by simp [Hom.mul_def]
      have m2 : snd A A * fst A A = (β_ A A).hom ≫ (μ : A ⊗ A ⟶ A) := by rw [hb, Hom.mul_def]
      rw [← m2, ← m1, ← e1, ← e2, mul_comm]
    · exact (Over.w _).trans (Over.w _).symm
  have hcomm : IsCommMonObj A := hA.1
  obtain ⟨d, hdim⟩ : ∃ d : ℕ, SmoothOfRelativeDimension d A.hom := by
    exact GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A d hA hdim
  obtain ⟨u₁, -, -, -, -⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ d u₀ L hL
  have htan := GlobalTheory.TorusTransfer.tangent_bijective u₁ hdim
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ (Over (Sp ℂ))) t' (by simp)
  set ε : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => Φ.symm (e z) with hε
  have hεadd : ∀ z w, ε (z + w) = ε z * ε w := by
    intro z w; simp only [hε, he.1 z w, map_mul]
  have hεleft : ∀ z, (ε z).left ≫ φ = (e z).left := by
    intro z; rw [← hΦ]; simp [hε]
  have hεhol : IsHolTo Set.univ (fun z => (ε z).left) := by
    refine GlobalTheory.FibreUnif.isHolTo_of_isPullback hφ.1 (fun z => ?_) ?_
    · have := Over.w (ε z)
      simpa using this
    · simp only [hεleft]
      exact he.2.2.1
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L d g u₁ htan.1 htan.2 ε hεadd hεhol
  have hker : ∀ z, ε z = 1 ↔ z ∈ P.range := by
    intro z; rw [← hk z]; simp only [hε]
    constructor
    · intro h; have := congrArg Φ h; simpa using this
    · intro h; rw [h]; simp
  obtain ⟨r, hr, hk1⟩ : ∃ r > 0, ∀ z : Fin d → ℂ, ‖z‖ < r → u₁.ex z = 1 → z = 0 := by
    have hdisc : DiscreteTopology u₁.Λ := u₁.discrete
    obtain ⟨U, hU, hU0⟩ : ∃ U ∈ 𝓝 (0 : Fin d → ℂ), ∀ z ∈ U, z ∈ u₁.Λ → z = 0 := by
      have ho := isOpen_discrete ({⟨0, u₁.Λ.zero_mem⟩} : Set u₁.Λ)
      obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 ho
      refine ⟨V, hV.mem_nhds ?_, fun z hz hzΛ => ?_⟩
      · have h0 : (⟨0, u₁.Λ.zero_mem⟩ : u₁.Λ) ∈ Subtype.val ⁻¹' V := by
          rw [hVeq]; exact Set.mem_singleton _
        exact h0
      · have h0 : (⟨z, hzΛ⟩ : u₁.Λ) ∈ Subtype.val ⁻¹' V := hz
        rw [hVeq] at h0
        exact congrArg Subtype.val (Set.mem_singleton_iff.1 h0)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨r, hr, fun z hz h1 => hU0 z (hball (mem_ball_zero_iff.2 hz)) ((u₁.ker z).1 h1)⟩
  have hkx : IsDiscrete {z | ε z = 1} := by
    have hs : {z | ε z = 1} = (P.range : Set (Fin g → ℂ)) := Set.ext fun z => hker z
    rw [hs]
    exact ⟨hd⟩
  have hεsurj : Function.Surjective ε := fun a => by
    obtain ⟨z, hz⟩ := he.2.1 (Φ a)
    exact ⟨z, by simp [hε, hz]⟩
  obtain ⟨Lq, hLq⟩ := GlobalTheory.LocLift.exists_linearEquiv_lift (x := ε) (e := u₁.ex) hεadd u₁.ex_add hεsurj
    u₁.ex_onto hkx hr hk1 (ζ := ⇑(LinearMap.toContinuousLinearMap F))
    (LinearMap.toContinuousLinearMap F).differentiableAt
    (Filter.Eventually.of_forall fun z => by simpa using hF z)
  have hgd : g = d := by
    have := Lq.toLinearEquiv.finrank_eq
    simpa using this
  subst hgd
  let Λ : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  have hΛd : DiscreteTopology Λ := hd
  have hΛf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by
    have hs : (Λ : Set (Fin g → ℂ)) = Set.range P := by ext; simp [Λ]
    rw [hs]; exact hsp
  have hΛ : ∀ z, Lq.toLinearEquiv z ∈ u₁.Λ ↔ z ∈ Λ := by
    intro z
    rw [← u₁.ker, show u₁.ex (Lq.toLinearEquiv z) = ε z from hLq z]
    show ε z = 1 ↔ z ∈ P.range.toIntSubmodule
    exact hker z
  let u := GlobalTheory.TorusTransfer.reparam u₁ Lq.toLinearEquiv (fun _ => 0) (differentiable_const _) Λ hΛd hΛf hΛ
  have hPΛ : P.range = Λ.toAddSubgroup := by ext; simp [Λ]
  refine ⟨u, (AddMonoidHom.ofInjective hi).trans (AddEquiv.addSubgroupCongr hPΛ), fun w => ?_, fun x => rfl⟩
  show (u₁.ex (Lq.toLinearEquiv w)).left ≫ φ = (e w).left
  rw [show u₁.ex (Lq.toLinearEquiv w) = ε w from hLq w, hεleft]

private theorem nonempty_addEquiv_of_discrete_span_eq_univ {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [DiscreteTopology Λ'] (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (h' : Submodule.span ℝ (Λ' : Set (Fin g → ℂ)) = ⊤) : Nonempty (Λ ≃+ Λ') := by
  have : IsZLattice ℝ Λ := ⟨h⟩
  have : IsZLattice ℝ Λ' := ⟨h'⟩
  exact ⟨(LinearEquiv.ofFinrankEq Λ Λ' ((ZLattice.rank ℝ Λ).trans (ZLattice.rank ℝ Λ').symm)).toAddEquiv⟩

theorem exists_any {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    {L : LB A.left} (hL : L.IsLB) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hf : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) : ∃ u : HolUnif A L g, Nonempty (Λ ≃+ u.Λ) := by
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨u, -⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  have : DiscreteTopology u.Λ := u.discrete
  exact ⟨u, nonempty_addEquiv_of_discrete_span_eq_univ Λ u.Λ hf u.full⟩

theorem famUnif_holds : FamUnif := by
  intro B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0U hy A _ φ hφ L hL A₀ _ φ₀ hφ₀ L₀ u₀

  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let ψ : (Fin (Fintype.card I) → ℂ) ≃L[ℂ] (I → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : I => ℂ) eI.symm
  let s : Sp B ⟶ Sp ℂ := spMap (algebraMap ℂ B)
  let yb : (Fin (Fintype.card I) → ℂ) → (Sp ℂ ⟶ Sp B) := fun b => spMap ((y (ψ b) : B →ₐ[ℂ] ℂ) : B →+* ℂ)
  have hψ0 : ψ 0 = 0 := map_zero ψ
  have hUo : IsOpen (ψ ⁻¹' U) := hU.preimage ψ.continuous
  have h0 : (0 : Fin (Fintype.card I) → ℂ) ∈ ψ ⁻¹' U := by simpa [Set.mem_preimage, hψ0] using h0U
  have hys : ∀ b ∈ ψ ⁻¹' U, yb b ≫ s = spMap (RingHom.id ℂ) := fun b _ =>
    PelTangent.spMap_comp _ _ _ (by ext c; simp)
  have hyb : IsHolTo (ψ ⁻¹' U) yb :=
    ThetaValueCont.isHolTo_spMap hUo (fun b => ((y (ψ b) : B →ₐ[ℂ] ℂ) : B →+* ℂ)) fun a =>
      (hy a).comp ψ.differentiable.differentiableOn (Set.mapsTo_preimage _ _)

  have hs : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

  have : DiscreteTopology u₀.Λ := u₀.discrete
  have : IsZLattice ℝ u₀.Λ := ⟨u₀.full⟩
  let P₀ : u₀.Λ →+ (Fin g → ℂ) := u₀.Λ.subtype.toAddMonoidHom
  have hi : Function.Injective P₀ := Subtype.val_injective
  have hsp : Submodule.span ℝ (Set.range P₀) = ⊤ := by
    simpa [P₀, Subtype.range_coe] using u₀.full

  have hbc : ∀ (f : B →+* ℂ) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left),
      IsGrpPullback A' 𝒜 (spMap f) φ' → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
    intro f A' _ φ' hpb
    obtain ⟨hc, hsm, hpr, hgc⟩ := h𝒜
    have hp := hpb.1
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    have : IsCommMonObj 𝒜 := hc
    have key : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A'), x * y = y * x := by
      intro T x y
      let x₀ : Over.mk (T.hom ≫ spMap f) ⟶ 𝒜 := Over.homMk (x.left ≫ φ') (by
        simp only [Over.mk_hom, Category.assoc, hpb.1.w, Over.w_assoc])
      let y₀ : Over.mk (T.hom ≫ spMap f) ⟶ 𝒜 := Over.homMk (y.left ≫ φ') (by
        simp only [Over.mk_hom, Category.assoc, hpb.1.w, Over.w_assoc])
      have h1 := hpb.2 T x y x₀ y₀ rfl rfl
      have h2 := hpb.2 T y x y₀ x₀ rfl rfl
      apply Over.OverMorphism.ext
      apply hpb.1.hom_ext
      · rw [← h1, ← h2, mul_comm]
      · simp
    have hcomm : IsCommMonObj A' := ⟨by
      have := key (A' ⊗ A') (fst A' A') (snd A' A')
      have hb : (β_ A' A').hom = lift (snd A' A') (fst A' A') := by ext <;> simp
      rw [hb]
      simpa [Hom.mul_def] using this.symm⟩
    exact ⟨⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hp hsm,
      MorphismProperty.of_isPullback (P := @IsProper) hp hpr,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp hgc⟩,
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hp hg⟩
  have hexp : ∃ e₀ : (Fin g → ℂ) → (Over.mk (yb 0) ⟶ 𝒜), IsExp (yb 0) e₀ ∧ (∀ z, e₀ z = 1 ↔ z ∈ P₀.range) ∧
      (∀ w, (e₀ w).left = (u₀.ex w).left ≫ φ₀) := by
    have hφ₀' : IsGrpPullback A₀ 𝒜 (yb 0) φ₀ := by simpa [yb, hψ0] using hφ₀
    have htb := TorusTransfer.tangent_bijective u₀ (hbc _ A₀ φ₀ hφ₀).2
    obtain ⟨Φ, hΦ⟩ := LiePull.exists_pushEquiv hφ₀' (𝟙_ (Over (Sp ℂ))) (yb 0) (by simp)
    refine ⟨fun z => Φ (u₀.ex z), PointUnif.isExp_push hφ₀' u₀ htb.1 htb.2 Φ hΦ, fun z => ?_, fun w => hΦ _⟩
    rw [MulEquiv.map_eq_one_iff, u₀.ker z]
    exact ⟨fun h => ⟨⟨z, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  obtain ⟨e₀, he₀, hk, he₀u⟩ := hexp
  obtain ⟨C, e, P, hCo, hC0, hCB, he0, hP0, hhol, hfib, hdiff, hend⟩ :=
    exists_core s 𝒜 e₀ hs h𝒜 hg hUo h0 hys hyb he₀ P₀ hi hsp hk
  have hAz : ∀ z, IsAbelianScheme (A z) ∧ SmoothOfRelativeDimension g (A z).hom := fun z =>
    hbc _ (A z) (φ z) (hφ z)

  have hW : ∃ (r : ℝ) (W : 𝒜.left.Opens), 0 < r ∧ IsAffineOpen W ∧
      Metric.ball (0 : I → ℂ) r ⊆ ψ.symm ⁻¹' C ∧ ∀ b ∈ C, ψ b ∈ Metric.ball (0 : I → ℂ) r → ⊤ ≤ (e b 0).left ⁻¹ᵁ W := by
    have hsub : Subsingleton (Sp ℂ : Scheme.{0}) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    obtain ⟨q₀⟩ : Nonempty (Sp ℂ : Scheme.{0}) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
    obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, -⟩ :=
      𝒜.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((e 0 0).left.base q₀)) isOpen_univ
    have hO := ((hhol W 0).1).preimage (continuous_id.prodMk continuous_const :
      Continuous fun b : Fin (Fintype.card I) → ℂ => (b, (0 : Fin g → ℂ)))
    have h0O : (0 : Fin (Fintype.card I) → ℂ) ∈ (fun b : Fin (Fintype.card I) → ℂ => (b, (0 : Fin g → ℂ))) ⁻¹'
        {q | q ∈ C ×ˢ Set.univ ∧ ⊤ ≤ (e q.1 q.2).left ⁻¹ᵁ W} := by
      refine ⟨⟨hC0, Set.mem_univ _⟩, fun q _ => ?_⟩
      obtain rfl : q = q₀ := @Subsingleton.elim (Sp ℂ : Scheme.{0}) hsub q q₀
      exact hxW
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hO.preimage ψ.symm.continuous) 0
      (by rw [Set.mem_preimage, show ψ.symm 0 = 0 from map_zero _]; exact h0O)
    refine ⟨r, W, hr, hWa, fun z hz => (hball hz).1.1, fun b _ hb => ?_⟩
    have := (hball hb).2
    rw [ContinuousLinearEquiv.symm_apply_apply] at this
    exact this
  obtain ⟨r, W, hr, hWa, hrC, hWb⟩ := hW
  have hmem : ∀ z ∈ Metric.ball (0 : I → ℂ) r, ψ.symm z ∈ C := fun z hz => hrC hz
  have hex : ∀ z : I → ℂ, ∃ p : (Σ u : HolUnif (A z) (L z) g, u₀.Λ ≃+ u.Λ), z ∈ Metric.ball (0 : I → ℂ) r →
      (∀ w, (p.1.ex w).left ≫ φ z = (e (ψ.symm z) w).left) ∧ ∀ x, (p.2 x : Fin g → ℂ) = P (ψ.symm z) x := by
    intro z
    by_cases hz : z ∈ Metric.ball (0 : I → ℂ) r
    · have hb := hfib _ (hmem z hz)
      have ht : yb (ψ.symm z) = spMap ((y z : B →ₐ[ℂ] ℂ) : B →+* ℂ) := by simp [yb]
      obtain ⟨u, τ, hu, hτ⟩ := exists_fibre h𝒜 ht (hφ z) (hL z) hb.1 (P (ψ.symm z)) hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2
      exact ⟨⟨u, τ⟩, fun _ => ⟨hu, hτ⟩⟩
    · obtain ⟨u, ⟨τ⟩⟩ := exists_any (hAz z).1 (hAz z).2 (hL z) u₀.Λ u₀.full
      exact ⟨⟨u, τ⟩, fun h => absurd h hz⟩
  choose p hp using hex
  refine ⟨r, fun z => (p z).1, fun z => (p z).2, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have := hCB (hmem z hz)
    simpa using this
  · let β : (I → ℂ) × (Fin g → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ) × (Fin g → ℂ) :=
      ContinuousLinearMap.prodMap (ψ.symm : (I → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ)) (ContinuousLinearMap.id ℂ _)
    have h1 := isHolTo_comp hhol (Metric.isOpen_ball.prod isOpen_univ) β.differentiable.differentiableOn
      (fun q hq => ⟨hmem q.1 hq.1, Set.mem_univ _⟩)
    refine isHolTo_congr (isHolTo_comp_hom h1 (𝟙 _)) ?_
    intro q hq
    simpa [β] using (hp q.1 hq.1).1 q.2
  · refine ⟨W, hWa, fun z hz => ?_⟩
    have h := (hp z hz).1 0
    rw [h]
    exact hWb _ (hmem z hz) (by simpa using hz)
  · intro w
    have h := (hp 0 (Metric.mem_ball_self hr)).1 w
    rw [show ψ.symm 0 = 0 from map_zero _] at h
    rw [h, he0, he₀u]
  · intro x
    have h := (hp 0 (Metric.mem_ball_self hr)).2 x
    rw [show ψ.symm 0 = 0 from map_zero _] at h
    rw [h, hP0]
    rfl
  · intro x
    exact ((hdiff x).comp ψ.symm.differentiable.differentiableOn (fun z hz => hmem z hz)).congr
      (fun z hz => (hp z hz).2 x)
  · intro α _ M₀ hM₀ z hz
    have hM : ∀ w, e₀ (M₀ w) = e₀ w ≫ α := fun w => by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, he₀u, he₀u, hM₀ w, Category.assoc]
    obtain ⟨M, hMe, hMP⟩ := hend α M₀ hM (ψ.symm z) (hmem z hz)
    refine ⟨M, fun w => ?_, fun x x' hx => ?_⟩
    · rw [(hp z hz).1 (M w), ← Category.assoc, (hp z hz).1 w, hMe w, Over.comp_left]
    · rw [(hp z hz).2, (hp z hz).2]
      exact hMP x x' hx

end GlobalTheory.PeriodFamily
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  first | exact @GlobalTheory.AnPer.isPeriod_pull1_eq_comap | exact GlobalTheory.AnPer.isPeriod_pull1_eq_comap | (intros; apply GlobalTheory.AnPer.isPeriod_pull1_eq_comap <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodHom_push_end' : PEnd := by
  atlas_forward_decl GlobalTheory.AnPer.periodHom_push_end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_comp_translationGroup_hom : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  atlas_forward_decl GlobalTheory.AnPer.Reindex.isPeriod_comp
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_fibre_eq_value : PFix := by
  intro I _ g Λ _ F B _ 𝒜 _ h𝒜 σ e z hz y hy A _ hA φ m L u hE τ hτ P hP c per hper l
  let u' : Unif (⟨(fibFam u).V, (fibFam u).τ.comp τ, fun l ↦ (fibFam u).hol (τ l)⟩ : Fam Empty g Λ)
      (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) :=
    { E := (fibUnif u).E
      w := (fibUnif u).w
      per := fun l p hp ↦ (fibUnif u).per (τ l) p hp
      hol := (fibUnif u).hol }
  have h1 := GlobalTheory.T.period_comp_translationGroup_hom (fibUnif u) τ u' rfl _ _ (hP (m.pull c))
  have h2 := GlobalTheory.AnPer.isPeriod_pull1_eq_comap u' e (GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA)
    (GlobalTheory.abelianScheme_left_isSeparated_of_affine 𝒜 h𝒜) (fun _ ↦ z) analyticOnNhd_const (fun _ _ ↦ hz)
    LinearMap.id (AddMonoidHom.id Λ) (fun l _ _ ↦ (hτ l).symm) y φ m.isMor
    (fun x ↦ Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Hol.fn_comap _ _ _ _ hp, hy])
    (fun p _ ↦ (hE p.2).symm) c.1 per _ hper h1 l
  have hp : (0 : Empty → ℂ) ∈ (fibFam u).V := trivial
  have h3 := congrArg (fun f ↦ Hol.fn f 0) h2
  simp only [Hol.fn_comap _ _ _ _ hp] at h3
  exact (Hol.fn_algebraMap _ hp).symm.trans h3

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePeriod_eq_familyPeriod_value : PFix := by
  atlas_forward_decl GlobalTheory.AnPer.period_fibre_eq_value
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_firstOrderJet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  first | exact @GlobalTheory.AnPer.Hol.exists_jet_algHom | exact GlobalTheory.AnPer.Hol.exists_jet_algHom | (intros; apply GlobalTheory.AnPer.Hol.exists_jet_algHom <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_of_uniformisation_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  atlas_forward_decl GlobalTheory.AnPer.exists_tangent_of_jet
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem exists_bound_glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  intro I _ g Λ _ F B _ X s σ K hK r f per hc
  have hc' : GlobalTheory.CatCoh.H1.mk K.Oc (r.coef.pullbackOneCocycle f.1) = GlobalTheory.CatCoh.H1.mk K.Oc (K.perZ per) := hc
  obtain ⟨q, hq⟩ := GlobalTheory.CatCoh.H1.mk_eq_mk.1 hc'
  have key : ∀ (l : Λ) (k k' : K.K) (h : K.le l k' k),
      Charts.sh h (q (K.triv k)) = q (K.triv k') + K.cst k' (per l) := by
    intro l k k' h
    have e := congrFun (congrFun (congrFun hq (K.triv k)) (K.triv k')) (Charts.ptHom (K.triv k') h)
    have h0 : (r.coef.pullbackOneCocycle f.1).1 _ _ (Charts.ptHom (K.triv k') h) = 0 :=
      f.2 (r.functor.map (Charts.ptHom (K.triv k') h)) rfl rfl
    rw [GlobalTheory.CatCoh.amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0, zero_sub] at e
    change q (K.triv k') - Charts.sh h (q (K.triv k)) = -K.cst k' (per l) at e
    linear_combination -e
  obtain ⟨G, hGa, hG, hsh, -⟩ := Charts.glue K hK (fun k ↦ q (K.triv k))
    (fun k k' h ↦ by rw [key 0 k k' h, map_zero, map_zero, add_zero])
  exact ⟨q, G, hq, hGa, hG, fun l p hp ↦ hsh l (per l) (fun k k' h ↦ key l k k' h) p hp⟩

end GlobalTheory.AnPer.Charts
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_bound_of_period_class : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  atlas_forward_decl GlobalTheory.AnPer.Charts.exists_bound_glue
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.LieVal

open GlobalTheory.CatCoh

theorem main : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  intro A I _ g Λ _ F K r k p hp w ρ hρ v hv f per q hq
  let e : Hol (K.W k) →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp (Hol.ev p hp).toRingHom
  let T : K.Obj :=
    { k := k, C := DualNumber ℂ, alg := (e.comp (K.cst k)).toAlgebra
      J := RingHom.ker ((SqExt.dual ℂ).π : DualNumber ℂ →+* ℂ)
      nil := ⟨2, (SqExt.dual ℂ).sq⟩, ρ := e, ρ_cst := fun _ ↦ rfl }
  have hder : ∀ h : Hol (K.W k), fderiv ℂ h.fn p (0, w) = ∑ a, (dw a h).fn p * w a := fun h ↦ by
    have : ((0, w) : Tot I g) = ∑ a, w a • ((0, Pi.single a 1) : Tot I g) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        exact pi_eq_sum_univ' w
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    exact congrArg (· * w a) (Hol.fn_der _ h hp).symm
  have hexp : ∀ h : Hol (K.W k), ρ h = e h + ∑ a, e (dw a h) * TrivSqZeroExt.inr (w a) := fun h ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hρ h).1]
      simp [e, TrivSqZeroExt.fst_sum, Hol.ev_apply]
    · rw [(hρ h).2, hder]
      simp [e, TrivSqZeroExt.snd_sum, Hol.ev_apply, mul_comm]
  let a : K.triv k ⟶ T := Charts.ptHom T (K.le_refl k)
  let b : K.triv k ⟶ T := Charts.fromTriv T (K.le_refl k) ρ.toRingHom
    (fun c ↦ by
      change ρ (K.cst k c) = e (K.cst k c)
      rw [hexp]; simp [Charts.dw_cst])
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (w a), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, Charts.sh_refl]
        exact hexp h⟩)
  have ea := congrFun (congrFun (congrFun hq _) _) a
  have eb := congrFun (congrFun (congrFun hq _) _) b
  change ((show DualNumber ℂ from q T) - e (Charts.sh (K.le_refl k) (q (K.triv k))) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map a)) - e (K.cst k (per 0)) at ea
  change ((show DualNumber ℂ from q T) - ρ (q (K.triv k)) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map b)) - e (K.cst k (per 0)) at eb
  rw [Charts.sh_refl] at ea
  let E := SqExt.dual ℂ
  have hfst : (E.π : E.C →+* E.B).comp ρ.toRingHom = (Hol.ev p hp).toRingHom :=
    RingHom.ext fun h ↦ (hρ h).1.trans (Hol.ev_apply p hp h).symm
  have halg : ∀ c : ℂ, e (K.cst k (algebraMap ℂ (Hol F.V) c)) = algebraMap ℂ (DualNumber ℂ) c := fun c ↦ by
    have : K.cst k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ (Hol (K.W k)) c := rfl
    rw [this]
    change TrivSqZeroExt.inl (Hol.ev p hp (algebraMap ℂ _ c)) = _
    rw [AlgHom.commutes]; rfl
  let Φ : E.thick _ (E.red_w (pt_w v)) ⟶ r.obj T :=
    { φ := { RingHom.id (DualNumber ℂ) with commutes' := fun c ↦ (halg c).symm }
      φ₀ := (Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)
      comm := fun c ↦ Ideal.Quotient.eq.2 (by
        change (TrivSqZeroExt.inl (TrivSqZeroExt.fst (R := ℂ) (M := ℂ) c) - (show TrivSqZeroExt ℂ ℂ from c)).fst = 0
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self])
      dp := isDPMorphism_of_rat (C' := DualNumber ℂ) _ _ _ fun c hc ↦ hc
      pt := by
        have h0 : spMap ((Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)) ≫
            spMap (E.π : E.C →+* E.B) ≫ v.left = spMap ((Ideal.Quotient.mk T.J).comp e) ≫ r.x k := by
          rw [hv, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← Cris.spMap_comp, hfst, ← Category.assoc,
            ← Cris.spMap_comp]
        exact h0 }
  have mkHom : ∀ (C : Type) [CommRing C] [Algebra ℂ C] (ψ : Hol (K.W k) →ₐ[ℂ] C) (y : Sp C ⟶ A.left)
      (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap ℂ C)), y = spMap ψ.toRingHom ≫ r.x k →
      ∃ m : r.obj (K.triv k) ⟶ Thick.triv C y hy, ∀ c, m.φ c = ψ c := fun C _ _ ψ y hy e' ↦
    ⟨{ φ := { ψ.toRingHom with commutes' := fun c ↦ ψ.commutes c }
       φ₀ := Ideal.Quotient.lift ⊥ ψ.toRingHom fun c hc ↦ by rw [Ideal.mem_bot.1 hc, map_zero]
       comm := fun _ ↦ rfl
       dp := isDPMorphism_of_eq_bot _ rfl _ _
       pt := by
        refine Eq.trans ?_ e'.symm
        refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r.x k) ?_)
        exact (Cris.spMap_comp _ _).symm }, fun _ ↦ rfl⟩
  obtain ⟨a', ha'⟩ := mkHom ℂ (Hol.ev p hp) _ (E.red_w (pt_w v)) (by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, hfst])
  obtain ⟨b', hb'⟩ := mkHom (DualNumber ℂ) ρ v.left (pt_w v) hv
  have e1 : r.functor.map a = a' ≫ E.secHom (E.red_w (pt_w v)) E.i E.π_i ≫ Φ := Thick.hom_ext fun c ↦ by
    change e (Charts.sh (K.le_refl k) c) = TrivSqZeroExt.inl (a'.φ c)
    exact (congrArg e (Charts.sh_refl _ c)).trans (congrArg TrivSqZeroExt.inl (ha' c).symm)
  have e2 : r.functor.map b = b' ≫ E.idHom (pt_w v) ≫ Φ := Thick.hom_ext fun c ↦ (hb' c).symm
  have z1 : ev f.1 a' = 0 := f.2 a' rfl rfl
  have z2 : ev f.1 b' = 0 := f.2 b' rfl rfl
  have g1 : ev f.1 (r.functor.map a) = Φ.φ (ev f.1 (E.secHom (E.red_w (pt_w v)) E.i E.π_i)) + ev f.1 Φ := by
    rw [e1]
    refine (ev_comp f.1 a' _).trans ?_
    rw [z1, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  have g2 : ev f.1 (r.functor.map b) = Φ.φ (ev f.1 (E.idHom (pt_w v))) + ev f.1 Φ := by
    rw [e2]
    refine (ev_comp f.1 b' _).trans ?_
    rw [z2, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  rw [g1] at ea
  rw [g2] at eb
  have key : (E.val v.left (pt_w v) f.1 : DualNumber ℂ) = ρ (q (K.triv k)) - e (q (K.triv k)) := by
    rw [SqExt.val_apply]
    have aux : ∀ x y z u s t c : DualNumber ℂ, x - y = s + u - c → x - z = t + u - c → s - t = z - y :=
      fun x y z u s t c h1 h2 ↦ by linear_combination h2 - h1
    exact aux _ _ _ _ _ _ _ ea eb
  rw [tanVal_apply, key, TrivSqZeroExt.snd_sub, (hρ _).2]
  exact sub_zero _

end GlobalTheory.AnPer.LieVal
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  atlas_forward_decl GlobalTheory.AnPer.LieVal.main
end

section
open Filter Topology

namespace GlobalTheory

theorem fderiv_eq_fderiv_zero_of_const_differences {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ)
    (hG : Differentiable ℂ G) (hp : ∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l)
    (v : Fin g → ℂ) : fderiv ℂ G v = fderiv ℂ G 0 := by
  have hd : Differentiable ℂ (fun w => G (w + v) - G w) :=
    (hG.comp (differentiable_id.add_const v)).sub hG
  have hc : ∀ w, G (w + v) - G w = G (0 + v) - G 0 := fun w =>
    entire_apply_eq_of_periodic_of_span_real hd hΛ (fun x l hl => by
      have h1 := hp ⟨l, hl⟩ (x + v)
      have h2 := hp ⟨l, hl⟩ x
      simp only at h1 h2
      show G (x + l + v) - G (x + l) = G (x + v) - G x
      rw [add_right_comm, h1, h2]
      ring) w 0
  have he : (fun w => G (w + v)) = fun w => G w + (G (0 + v) - G 0) := by
    funext w
    rw [← hc w]
    ring
  have h1 : fderiv ℂ (fun w => G (w + v)) 0 = fderiv ℂ G (0 + v) := fderiv_comp_add_right v
  rw [he, fderiv_add_const, zero_add v] at h1
  exact h1.symm

theorem fderiv_zero_eq_of_const_differences :
    ∀ {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ), Differentiable ℂ G →
        (∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l) →
        ∀ l : Λ, fderiv ℂ G 0 l = p l := by
  intro g Λ hΛ G p hG hp l
  have hk := fderiv_eq_fderiv_zero_of_const_differences Λ hΛ G p hG hp
  have hd : Differentiable ℂ (fun w => G w - fderiv ℂ G 0 w) :=
    hG.sub (fderiv ℂ G 0).differentiable
  have hz : ∀ w, fderiv ℂ (fun w => G w - fderiv ℂ G 0 w) w = 0 := fun w => by
    have := ((hG w).hasFDerivAt.sub (fderiv ℂ G 0).hasFDerivAt).fderiv
    rw [hk w, sub_self] at this
    exact this
  have h := is_const_of_fderiv_eq_zero hd hz (l : Fin g → ℂ) 0
  have h2 := hp l 0
  rw [zero_add] at h2
  simp only [map_zero, sub_zero] at h
  rw [h2] at h
  linear_combination -h

end GlobalTheory
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem pLie_holds : PLie := by
  intro A _ g hA _ L u P hP x
  have hs := GlobalTheory.T.abelianScheme_isSeparated_of_affine_base A hA
  obtain ⟨K, -, -, hK, hsm, -⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map (fibUnif u) (fibUnif u) id analyticOnNhd_id (fun _ h ↦ h)
    LinearMap.id (AddMonoidHom.id _) (fun _ _ _ ↦ rfl)
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine (fibUnif u) hs K hsm
  obtain ⟨k, hk⟩ := hK.1 0 trivial
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_firstOrderJet_algHom (K.W k) 0 hk (0, (x : Fin g → ℂ))
  obtain ⟨v, hv, ht, hd⟩ := GlobalTheory.T.exists_tangent_of_uniformisation_jet u hs (K.W k) (r.x k) (hr k)
    ((congrArg (r.x k ≫ ·) (Category.comp_id A.hom).symm).trans (r.w k)) hk x ρ hρ
  refine ⟨v, ⟨ht, fun f hf ↦ ?_⟩, hd⟩
  obtain ⟨q, G, hq, hG, hGk, hGl⟩ := GlobalTheory.T.exists_global_bound_of_period_class K hK r f _ (hP ⟨_, hf⟩ K r hr)
  rw [GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function K r k 0 hk x ρ hρ v hv f _ q hq, Hol.fderiv_fn_congr _ (hGk k) hk]
  have hdG : ∀ p, DifferentiableAt ℂ G p := fun p ↦ (hG p trivial).differentiableAt
  have hi : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ ↦ ((0, w) : Tot Empty g))
      (ContinuousLinearMap.inr ℂ (Empty → ℂ) (Fin g → ℂ)) w := fun w ↦ hasFDerivAt_prodMk_right _ _
  have := GlobalTheory.fderiv_zero_eq_of_const_differences u.Λ u.full (fun w ↦ G (0, w)) (fun l ↦ P l ⟨_, hf⟩)
    (fun w ↦ (hdG _).comp w (hi w).differentiableAt)
    (fun l w ↦ (hGl l (0, w) trivial).trans (congrArg (G (0, w) + ·) (Hol.fn_algebraMap _ trivial))) x
  rw [← this]
  exact congrArg (fun D : (Fin g → ℂ) →L[ℂ] ℂ ↦ D x) ((hdG (0, 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (hi 0)).fderiv

end GlobalTheory.AnPer
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrationOverCycles_lifts_lieLattice : PLie := by
  atlas_forward_decl GlobalTheory.AnPer.pLie_holds
end

section
namespace GlobalTheory.AnPer

theorem gaussManinPeriods_of_span_taylor : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods :=
  fun HS HT ↦ gaussManinPeriods_of_parts (-1) GlobalTheory.PeriodFamily.famUnif_holds GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.exists_integrationOverCyclesHom HS
    GlobalTheory.T.integrationOverCycles_lifts_lieLattice GlobalTheory.T.periodHom_push_end' GlobalTheory.T.pChern_neg_one GlobalTheory.T.fibrePeriod_eq_familyPeriod_value HT

end GlobalTheory.AnPer
end
