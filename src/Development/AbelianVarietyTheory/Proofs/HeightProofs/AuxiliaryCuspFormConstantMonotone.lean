module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
public import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
public import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
public import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCuspStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IInfLeOfCombBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonSectionsOfNoLeadingTerm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

theorem runOK_of_pageOK {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.EtaAn.RunOK D.host.E D.R.r (DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + DF wL))) D.R.m := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 B.KO) B.KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  exact (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j X _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1

theorem small_rows {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    0 ≤ large₂.sc.L ∧ 0 ≤ Zb D large₂ ∧ 0 ≤ cc D large₂ C2 A2 7 wL ∧ OPO large₂ B ∧ 1 ≤ WeightFamilies.PPv D large₂ 200000 2 ∧
      1 ≤ 200000 * zBase large₂ ^ 2 := by
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  obtain ⟨hA, hS, -, -, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hd⟩ := hS
  have hC : 0 ≤ C2 := by have := hd.1; rw [hP.tie.1] at this; linarith
  have hrd : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
  have hL : 0 ≤ large₂.sc.L := by
    by_contra hn
    have h1 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) := by positivity
    have h2 := mul_nonpos_of_nonneg_of_nonpos h1 (not_le.1 hn).le
    unfold zBase at hZ1
    linarith
  refine ⟨hL, le_trans zero_le_one hZ1, ?_, hO, ?_, by nlinarith⟩
  · unfold cc WeightFamilies.RRv WeightFamilies.PPv
    have := Real.rpow_nonneg hrd 7
    have := Real.rpow_nonneg (le_trans zero_le_one hZ1) A2
    positivity
  · unfold WeightFamilies.PPv
    have := Real.one_le_rpow hZ1 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem auxiliaryCuspFormConstant_monotone (D : D7) (j : ℕ) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') : PI4 D j a b ≤ PI4 D j a' b' := by
  unfold PI4
  have : 2 * b / (WeightFamilies.dimY D j : ℝ) ≤ 2 * b' / (WeightFamilies.dimY D j : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith

end GlobalTheory.RunPrimeData
