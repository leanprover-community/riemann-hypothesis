import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsSectionOrderBoundHilbertSamuel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueLePhiOfHilbertSamuel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetsOfConstantSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspWithThetaJetValueLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsThetaRuleValueLeCoverCharZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorHalfGenerationOfCover
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftGaps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ThetaValueOnCuspNeighbourhood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistPreservesBoundaryValuation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DistinguishedSectionBoundaryValuationVanishes
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumbersAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GermFactorizationUnitMulEvaluation

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HalfCover
theorem divisor_half_generated_on_cover_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  intro _ h2 _ _
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  refine Formalism.MainNotions.Closed.imp h2 ?_
  intro eps Fm CH _ _
  refine ⟨0, le_rfl, 0, fun x hx _ ι p _ i hi Y hY => ?_⟩
  letI := p.T.Q.H.starRing
  have hL := p.fw.laws
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split (Fm.D x ι) p.T.toCore hL.toLawsM (Fm.ex x hx ι).errX
  have hM : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := hL.pins.2.1.1
  have hlev := hY.1.lev.1
  have hq := (hL.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, by omega⟩).2.1
  refine ⟨α, by rw [hα1, hM], ?_, ?_, ?_⟩
  · rw [hlev.2.1, ← hM]
    exact dvd_mul_right _ _
  · rw [hlev.2.2.2.1, ← hα2]
    exact Ideal.mul_le_left
  · show Module.finrank ℚ (Fm.D x ι).host.E * (p.T.Q.Dw ((i : ℕ) + 1)).q ≤ _
    rw [GlobalTheory.DepthLink.finrank_host, hq]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
end GlobalTheory.HalfCover
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_half_generated_of_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  first | exact @_root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt | exact _root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt | (intros; apply _root_.GlobalTheory.HalfCover.divisor_half_generated_on_cover_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.JetsCharZero
theorem exists_theta_rule_value_le_cover_char_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.divisor_half_generated_of_covers h1 h2 h3 h4
  have hG := _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ h3
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition Formalism.MainNotions.Closed at hA hG ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hG⟩ := hG
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hG eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hGi⟩ := hx1 x hx hle ι p hp
  obtain ⟨α, hα, hdvd, hMb, hρq⟩ := hAi i hi Y hY
  obtain ⟨hp1, hgap⟩ := hGi i hi Y hY
  intro la hla cst hJ nab hnab T io y' C P φT hch hTr hP hφ
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hbd : ∀ (τ : AllWt.Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)),
      |((la τ k : ℤ) : ℝ)| ≤ ∑ τ' : AllWt.Psi p.T.Q.H, ∑ k' : Fin ((dat p i).p + (dat p i).q), |((la τ' k' : ℤ) : ℝ)| :=
    fun τ k => (Finset.single_le_sum (f := fun k' => |((la τ k' : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun τ' => ∑ k' : Fin ((dat p i).p + (dat p i).q),
        |((la τ' k' : ℤ) : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  have hEven : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    unfold GlobalTheory.RefSum.nCol
    exact ⟨4 * ((∑ f : Lt1 (dat p i), 2 * rk f) / 8 + Fintype.card (Lt1 (dat p i)) + 1), by ring⟩
  have hn1 : 1 ≤ GlobalTheory.RefSum.nCol (dat p i) := by unfold GlobalTheory.RefSum.nCol; omega
  obtain ⟨hDom, -⟩ := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hEven
    hanti hgp hbd
  have hg0 : 2 ≤ (Fm.D x ι).host.g 0 := ((Fm.D x ι).host.g_prime 0).two_le
  have hg1 : 2 ≤ (Fm.D x ι).host.g 1 := ((Fm.D x ι).host.g_prime 1).two_le
  obtain ⟨j1, j2, j3⟩ := hJ 0
  have hle0 : (Fm.D x ι).host.g 0 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hle0' : ((Fm.D x ι).host.g 0 : ℝ) ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) := by exact_mod_cast hle0
  have hg0' : (0 : ℝ) < (Fm.D x ι).host.g 0 := by exact_mod_cast (show 0 < (Fm.D x ι).host.g 0 by omega)
  have hN0 : (0 : ℝ) ≤ 2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m := by positivity
  have hR0 : 0 ≤ GlobalTheory.PtTie.rr0 (Fm.D x ι) := by unfold GlobalTheory.PtTie.rr0; positivity
  exact exists_thRule_value_le _ _ _ _ Y.d.Xo₂ Y.d.c₂ nab hnab T io y' C hTr P hP hch φT hφ α _ hα hdvd hMb _ _ hDom.1
    GlobalTheory.RefSum.sum_le_nCol hn1 (2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m) cst (by exact_mod_cast hρq) (j1.trans hle0)
    (lt_of_lt_of_le j2 hle0') (num_le _ _ _ _ _ _ _ hR0 hN0 (Nat.cast_nonneg _) hg0' hle0' j3)
end GlobalTheory.JetsCharZero
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_jet_value_bound_char_zero' : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt | exact _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt | (intros; apply _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  intro hP hD hS hF
  have hG := _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hG ⊢
  refine Formalism.MainNotions.Closed.imp hG ?_
  rintro eps Fm CH - ⟨C3, hC3, x3, h3⟩
  refine ⟨C3, hC3, x3, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hp1, hgap⟩ := h3 x hx hle ι p hp i hi Y hY
  intro Z TF la hla
  letI := p.T.Q.H.starRing
  intro nab hnab f hf y T io y' g hfac
  have hU := hY.1.unf
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb
  have hr : 1 ≤ (Fm.D x ι).R.r := by
    have := (Fm.D x ι).R.two_le_m
    have := (Fm.D x ι).R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hr hU nab hnab).2 _ _ hw.1 hw.2.2.1 f hf
  obtain ⟨g', hg'e, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hU Z _ ⟨f, hcusp⟩
  refine ⟨g', g'.2, ?_⟩
  letI := io.toAlgebra
  have hfac' : TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z := hfac
  have hL : GlobalTheory.AllWt.LiesOn Z y'.1 := by
    refine (ptY_le_iff TF.X Z y'.1).1 ?_
    rw [hfac']
    first
      | (rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top])
      | (intro s _; exact (((Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y) s).2 : _))
      | (intro s _; simp)
  exact hg'e T.Fr y'.1 hL
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_cusp_value_formula_at_weight : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  first | exact @_root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' | exact _root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' | (intros; apply _root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ThetaJetsT
theorem exists_cusp_with_theta_jet_value_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.theta_jet_value_bound_char_zero' h1 h2 h3 h4
  have hC := _root_.GlobalTheory.T.theta_cusp_value_formula_at_weight h1 h2 h3 h4
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition Formalism.MainNotions.Closed at hA hC ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hC⟩ := hC
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hC eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hCi⟩ := hx1 x hx hle ι p hp
  have hA' := hAi i hi Y hY
  have hC' := hCi i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hpt
  have hch : CharZero (IsLocalRing.ResidueField T.V) := GlobalTheory.UnifTrait.charZero_residue_of_map T.V
    (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π ≫ TF.Y.s)
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ _ _ _ Y.d.Xo₂ Y.d.c₂
  obtain rfl := GlobalTheory.PowGerm.starSt _ _ st hnab.1
  obtain ⟨T', io', y'', r, C, P, hch', hr, hC0, hP, hφ', hsc⟩ := GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero _ _ _ _ Y.d.Xo₂ Y.d.c₂ T io y' hch φT hφ
  obtain ⟨f, hf, hne, hle⟩ := hA' la hla cst hJ nab hnab T' io' y'' C P (r * φT) hch' hC0 hP hφ'
  have hs := hsc nab hnab _ _ 1 1 f hf
  simp only [map_one, one_mul, mul_one] at hs
  obtain ⟨f', hf', hev⟩ := hC' Z TF la hla nab hnab f hf y T io y' g hpt
  have hne' : evI y' f ≠ 0 := by
    intro h0
    rw [h0, nval_zero, nval_of_ne hne] at hs
    exact EReal.coe_ne_top _ hs
  refine ⟨f', hf', hev ▸ hne', ?_⟩
  rw [hev]
  rw [nval_of_ne hne, nval_of_ne hne', EReal.coe_eq_coe_iff] at hs
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hφ0 := hφ.nonneg
  rw [Nat.cast_one, div_one] at hs
  rw [← hs, div_le_iff₀ hr']
  nlinarith
end GlobalTheory.ThetaJetsT
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_jet_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | exact _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | (intros; apply _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KeyValZero
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem covers_distinguished_section_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g _ hpt hZ => ?_⟩
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := twSec_keyRoot_val _ _ _ _ _ _ _ Y.U (xiR (Fm.D x ι)) hY.1.unf hY.1.xiAbs hY.1.geo hL.pos hL.good Z
  refine ⟨t, ht T io y' (fun a => ?_) hZ⟩
  letI := io.toAlgebra
  have h1 := ptY_str TF.X y'.1
  rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
  obtain ⟨b, hb⟩ := Spec.map_surjective
    (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
  rw [← hb, ← Spec.map_comp] at h1
  exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
end GlobalTheory.KeyValZero
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.distinguished_section_boundary_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  first | exact @_root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero | exact _root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero | (intros; apply _root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  intro hP hD _ hF
  have F := _root_.GlobalTheory.CovTop.FlatVal.flat_val_alt hF
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (hD.and F).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g hg hpt hZ w => ?_⟩
  obtain ⟨-, hB⟩ := hx0 x hx hle ι p hp
  have hFE := (hB i hi Y hY).2.2.1
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.FlatValZero.twisted_section_flat_valuation hP hL hFE Z w
  refine ⟨t, ht T io y' (fun a ha => ?_) hZ⟩
  have ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range := fun a => by
    letI := io.toAlgebra
    have h1 := ptY_str TF.X y'.1
    rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
    obtain ⟨b, hb⟩ := Spec.map_surjective
      (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
    rw [← hb, ← Spec.map_comp] at h1
    exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  have h1 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a)
  have h2 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a⁻¹)
  have h3 := vV_mul (V := T.V) ha' ((map_ne_zero io).2 (inv_ne_zero ha))
  rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
  omega
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_point_stalk_compat_third_place_series : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | exact _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | (intros; apply _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistVal
open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.AllWt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {T : CDVR} {io : c.F →+* T.Fr} (y' : IntFr Xo c T io)
end GlobalTheory.TwistVal
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwistVal.cuspOn_local_hom_valuation_of_four_dvd : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : AllWt.Psi p.T.Q.H → ℤ) (m : ℤ), 4 ∣ m → ∀ f ∈ AllWt.cuspOn Y.U Z (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' f ≠ 0 → ∃ f' : Cusp Z Y.U la, evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ vV T.V (evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂))) = vV T.V (evI y' f) := by
  intro hP hD hS hF
  have A := _root_.GlobalTheory.T.distinguished_section_boundary_valuation_eq_zero hP hD hS hF
  have B := _root_.GlobalTheory.T.integral_frame_point_stalk_compat_third_place_series hP hD hS hF
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (A.and B).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF la w m _ f hf y T io y' g hg hpt hf0 => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  have hfi : GlobalTheory.FlatLine.idem Z * f = f :=
    GlobalTheory.FlatLine.idem_mul_eq (e := exZ _ (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m))
      ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩
  have hid : evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 := fun h0 => hf0 (by rw [← hfi, evI_mul, h0, zero_mul])
  have he := GlobalTheory.TwistVal.evI_idem_eq_one y' hid
  obtain ⟨t1, ht1⟩ := hA i hi Y hY Z TF y T io y' g hg hpt hid
  obtain ⟨t2, ht2⟩ := hB i hi Y hY Z TF y T io y' g hg hpt hid (-w)
  obtain ⟨tk, htk⟩ := GlobalTheory.TwistVal.exists_zpow y' t1 he ht1 (-m)
  let z := t2.mul tk
  have hz := GlobalTheory.TwistVal.val_mul y' t2 tk he ht2 htk
  have hw : AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m +
      (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) (-w)) 0 + AllWt.wtOf (dat p i) 0 (-m)) =
      AllWt.wtOf (dat p i) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add]
    congr 1
    · funext τ j
      simp [GlobalTheory.FlatLine.parWt]
    · ring
  have hmem := z.cusp_sig _ (AllWt.even_wtOf _ _) f hf
  rw [hw] at hmem
  refine ⟨⟨f * z.sig, hmem⟩, ?_, ?_⟩
  · show evI y' (f * z.sig) ≠ 0
    rw [evI_mul]
    exact mul_ne_zero hf0 (GlobalTheory.TwistVal.val_inv y' z he).1
  · show vV T.V (evI y' (f * z.sig)) = vV T.V (evI y' f)
    rw [evI_mul, vV_mul hf0 (GlobalTheory.TwistVal.val_inv y' z he).1, hz, add_zero]
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspOn_boundary_valuation_of_four_dvd : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : AllWt.Psi p.T.Q.H → ℤ) (m : ℤ), 4 ∣ m → ∀ f ∈ AllWt.cuspOn Y.U Z (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' f ≠ 0 → ∃ f' : Cusp Z Y.U la, evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ vV T.V (evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂))) = vV T.V (evI y' f) := by
  first | exact @_root_.GlobalTheory.TwistVal.cuspOn_local_hom_valuation_of_four_dvd | exact _root_.GlobalTheory.TwistVal.cuspOn_local_hom_valuation_of_four_dvd | (intros; apply _root_.GlobalTheory.TwistVal.cuspOn_local_hom_valuation_of_four_dvd <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_antitone_boundary' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  first | exact @_root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ | exact _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ | (intros; apply _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.JetsCst.jets_of_constant_section_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  intro hP hD hS hF
  have hA := _root_.GlobalTheory.T.theta_jet_cusp_value_bound_alt hP hD hS hF
  have hB := _root_.GlobalTheory.T.cuspOn_boundary_valuation_of_four_dvd hP hD hS hF
  have hG := _root_.GlobalTheory.T.weight_antitone_boundary' hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hA hB hG ⊢
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hA hB) hG) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, hC1, x1, h1⟩, ⟨C2, hC2, x2, h2⟩⟩, ⟨C3, hC3, x3, h3⟩⟩
  refine ⟨0, le_rfl, max x1 (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY
  have b := h2 x hx ((le_max_left _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  have c := h3 x hx ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨f, hf, hne, hv⟩ := a Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨hp1, hgap⟩ := c
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb).2.1
  rw [hw] at hf
  have h4 : (4 : ℤ) ∣ ((GlobalTheory.RefSum.nCol (dat p i) / 2 : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨k, by rw [hk]; omega⟩
  obtain ⟨f', hne', hv'⟩ := b Z TF la _ _ h4 f hf y T io y' g hg hfac hne
  exact ⟨f', hne', by rw [hv']; exact hv⟩
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_constant_section_eq_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCst.jets_of_constant_section_alt | exact _root_.GlobalTheory.JetsCst.jets_of_constant_section_alt | (intros; apply _root_.GlobalTheory.JetsCst.jets_of_constant_section_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RefSum.JetsUb
open GlobalTheory.AllWt GlobalTheory.CompHS
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end GlobalTheory.RefSum.JetsUb
theorem GlobalTheory.RefSum.JetsUb.jetNum_ub_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
  intro hS
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)) (_root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point hS)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩, ⟨_, _, hC⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and (_root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hA hB) hC
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨⟨hA, hB⟩, hC⟩ := h x hx hle ι p hp
  obtain ⟨⟨u1, hu⟩, -⟩ := (hA i).2.2.2.2.2.2 hi
  obtain ⟨hp1, -, -, hq, hanti, -⟩ := hB i hi
  have j := (hC i hi u1 hu).1
  rw [hq u1 hu] at j
  exact j.of_le (GlobalTheory.RefSum.JetsUb.DF_ub_le _ _ hp1 fun τ => (hanti τ).1.antitone)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetNum_thA_ub : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
  atlas_forward_decl _root_.GlobalTheory.RefSum.JetsUb.jetNum_ub_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_cusp_value_le_phi_of_hilbertSamuel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  intro h1 h2 h3 h4
  refine ((((_root_.GlobalTheory.T.jets_constant_section_eq_alt h1 h2 h3 h4).and (_root_.GlobalTheory.T.jetNum_thA_ub h3)).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt h3)).and ((_root_.GlobalTheory.T.jetNum_nCol_lenT_bounds_of_quo h3).and h3)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hJ⟩, ⟨C1, hC1, x1, hN⟩⟩, ⟨C2, hC2, x2, hA⟩⟩, ⟨⟨C3, hC3, x3, hB⟩, ⟨C4, hC4, x4, hS⟩⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 (max x3 x4)), fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt => ?_⟩
  have l0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have l1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have l2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  have l4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hle
  obtain ⟨-, -, hfin, hquo, -⟩ := hA x hx' l2 ι p hp i hi
  obtain ⟨⟨u1, hu1⟩, -⟩ := (hS x hx' l4 ι p hp i).2.2.2.2.2.2 hi
  have hnum : GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
    rcases hla with rfl | hla
    · have := (hB x hx' l3 ι p hp i hi u1 hu1).1
      rwa [hquo u1 hu1] at this
    · rw [Set.mem_singleton_iff] at hla
      subst hla
      exact hN x hx' l1 ι p hp i hi
  obtain ⟨f, hf0, hfb⟩ := hJ x hx' l0 ι p hp i hi Y hY Z TF la hla (1 / 2500) hnum y hy T io y' g φT hg hφT hpt
  have hE : Extends TF.X Z Y.U la := GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace (Fm.D x ι) p.T.toCore ((i : ℕ) + 1) Y _ _ hY.1 hfin Z TF la
  refine ⟨hE.equiv f, ?_⟩
  have e : ofSpace TF.X Z Y.U la (hE.equiv f) = f := hE.equiv.symm_apply_apply f
  rw [e]
  refine ⟨hf0, ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact hfb
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ w : space TF.X Z Y.U la, evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 ∧ (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) ≤ φT / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | exact _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt | (intros; apply _root_.GlobalTheory.HSApp.exists_cusp_value_le_phi_of_hilbertSamuel_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
theorem germ_eq_unit_mul_evaluation_ideal_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  exact ⟨C, hC, x0, fun x hx' hle ι p hp i hi Y hY Z TF la w y T io y' g _ hpt j' hj' =>
    germ_eq_unit_mul_evI_core TF.X Z Y.U la w y T io y' g hpt j' hj'⟩
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_local_hom_germ_factorization : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  first | exact @_root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | exact _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | (intros; apply _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
set_option maxHeartbeats 2000000 in
theorem exists_subspace_vanishing_order_le_phi_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  intro h1 h2 h3 h4
  refine ((_root_.GlobalTheory.T.exists_form_cusp_value_bound_alt h1 h2 h3 h4).and (_root_.GlobalTheory.T.stalk_local_hom_germ_factorization h1 h2 h3 h4)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩ := h
  refine ⟨C, hC, max x0 x1, fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy ν hν φ hφ => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  haveI hg : IsLocalHom g := isLocalHom_of_centred hν T g ρ hρ hval
  obtain ⟨w, hw0, hwb⟩ := hx x hx' ((le_max_left _ _).trans hle) ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt
  refine ⟨w.1, w.2, fun j' hj' => ?_⟩
  obtain ⟨u, hu⟩ := hx1 x hx' ((le_max_right _ _).trans hle) ι p hp i hi Y hY Z TF la w y T io y' g hg hpt j' hj'
  have hu0 : algebraMap T.V T.Fr (u : T.V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u.ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) ≠ 0 := by
    rw [hu]; exact mul_ne_zero hu0 hw0
  have hgerm : H0.germ j' y (memTop y) hj' w.1 ≠ 0 := by
    intro h; rw [h, map_zero, map_zero] at hg0; exact hg0 rfl
  have hne : ν (H0.germ j' y (memTop y) hj' w.1) ≠ 0 := fun h => hgerm (hν.2.2 _ h)
  refine ⟨hne, fun m hm => ?_⟩
  have hv := hval _ hne
  rw [hm, log_ofAdd_neg, hu, vV_mul hu0 hw0, vV_algebraMap_unit, zero_add] at hv
  have e : (m : ℝ) = ρ * (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) := by
    rw [← hv]; push_cast; ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hwb hρ.le
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt | exact _root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt | (intros; apply _root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt <;> assumption)
end
end
end
