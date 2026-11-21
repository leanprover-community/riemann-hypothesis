import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DiscreteSeriesCoefficientsCuspidal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GlobalModelExists
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoTheta
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.WeilBound.CoreStatements.NefModelVolumes.TopCovolG
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.HermitianSectionsHeightBound
import Development.WeilBound.CoreStatements.NefModelVolumes.InjectivityWeightSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonvanishingOfToroidal
import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import Development.WeilBound.CoreStatements.HodgeTatePoints.AhSlim
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.FubiniStudyChowHeight.FubiniStudyChowHeightOfArExists
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan

section
open MvPolynomial

namespace ChowFormCompatibility

theorem projCycle_eq_fundCycle {k : Type} [Field k] {N : ℕ} (J : Ideal (MvPolynomial (Fin N) k)) :
    GlobalTheory.ChowHt.projCycle J = GroundTheory.Heights₂.Heights.fundCycle J := by
  ext Q
  rw [GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]
  by_cases hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J
  · haveI hp : Q.IsPrime := hQ.1.1.1
    have h1 := GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ
    rw [if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dif_pos hp]
    have h2 := congrArg ENat.toNat h1
    rw [ENat.toNat_coe] at h2
    exact h2
  · rw [if_neg hQ]
    exact GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ

theorem hyperplane_section_divCycle : ∀ (k : Type) [Field k] (N B : ℕ) (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k), GlobalTheory.ChowHt.hyperplaneSection P u = GroundTheory.Heights₂.Heights.divCycle P u ∧ GlobalTheory.ChowHt.fixFirstBlock u f = GroundTheory.Heights₂.Heights.specFirst f u := by
  intro k _ N B P u f
  refine ⟨projCycle_eq_fundCycle _, ?_⟩
  have h : (fun p : Fin (B + 1) × Fin N =>
      (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
        Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) =
      GroundTheory.Heights₂.Heights.specFirstVar u := by
    funext ⟨b, j⟩
    induction b using Fin.cases with
    | zero => rfl
    | succ b => rfl
  rw [GlobalTheory.ChowHt.fixFirstBlock, h]
  rfl

end ChowFormCompatibility
end

section
open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_unique_up_to_constant : ∀ (k : Type) [Field k] (N B : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f g : MvPolynomial (Fin B × Fin N) k), GroundTheory.Heights₂.Heights.IsChowForm I B f → GroundTheory.Heights₂.Heights.IsChowForm I B g → ∃ c : k, c ≠ 0 ∧ g = C c * f := by
  intro k _ N B I f g hf hg
  have hfg : f ∣ g := (hf.2 g).1 ((hg.2 g).2 dvd_rfl)
  have hgf : g ∣ f := (hg.2 f).1 ((hf.2 f).2 dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hfg hgf
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end ChowFormCompatibility
end

section
open MvPolynomial

namespace ChowFormCompatibility

attribute [local instance] MvPolynomial.gradedAlgebra

theorem chow_form_hyperplane_section : GlobalTheory.Published.ChowFormHyperplaneSection := by
  unfold GlobalTheory.Published.ChowFormHyperplaneSection
  intro k _ _ N e P hP hprime _ u hu dl f hf d g hg
  have hrel : GroundTheory.Heights₂.Heights.IsRelevant P := by
    by_contra h
    simp only [GroundTheory.Heights₂.Heights.IsRelevant, not_exists, not_not] at h
    exact hu (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  have hproj : GroundTheory.Heights₂.Heights.IsProjPrime P :=
    ⟨hprime, (GroundTheory.Heights₂.Heights.isHomogIdeal_iff P).2 hP, hrel⟩
  have hf' := chow_form_of_integral_version k N (e + 1) dl P f hf
  obtain ⟨c, hc, g', hg', heq⟩ :=
    GroundTheory.Heights₂.Heights.ChowFormSection.full k N (e + 1) P f u hproj hf' hu
  obtain ⟨hsec, hfix⟩ := hyperplane_section_divCycle k N (e + 1) P u f
  have key : ∀ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support,
      ∃ a : k, a ≠ 0 ∧ g' Q = C a * g Q := by
    intro Q hQ
    have hQ' : Q ∈ (GlobalTheory.ChowHt.hyperplaneSection P u).support := by
      rw [hsec]
      exact hQ
    exact chow_form_unique_up_to_constant k N (e + 1) Q (g Q) (g' Q) (chow_form_of_integral_version k N e (d Q) Q (g Q) (hg Q hQ')) (hg' Q hQ)
  choose! a ha hga using key
  refine ⟨c * ∏ Q ∈ (GroundTheory.Heights₂.Heights.divCycle P u).support, a Q ^ (GroundTheory.Heights₂.Heights.divCycle P u) Q, ?_, ?_⟩
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (ha Q hQ))
  · rw [hfix, heq, hsec, Finsupp.prod, map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hga Q hQ, mul_pow, map_pow]

end ChowFormCompatibility
end

section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace SelfIntersectionVolumeEstimates

set_option maxHeartbeats 1000000 in

theorem topCovolSlim2 : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → HT.FarguesExact → GR.ZarhinStatement → Pub.NefRR → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.PointSeparationPair → GlobalTheory.Published.ArDegree → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.CovTop.CovolX :=
  fun h₁ h₂ hPL hHS hBig hFar hZar hRR hS hK hN hSep hDeg hP hSW hGD =>
    have hX : GlobalTheory.CovTop.HypothesesX := ⟨hK, hN, GlobalTheory.GreenBridge.green_of_regular GlobalTheory.greenRegularCharacters_holds, hSep, FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_hypotheses hP⟩
    have hF := PositivityTheory.Prw.toroidalChartsForFan_of hK
    have hH : GlobalTheory.CovHt.HypothesesH := ⟨hS, hF, GlobalTheory.Published.toroidalCharts_of_siegel_of_forFan hS hF, hDeg⟩
    topCovolG ⟨ChowFormHeightComparison₂.hermitian_sections_height_bound, PositivityTheory.Xj7N.injectivity_weight_sections (GlobalTheory.CompanionTheory.Ar.Rec.exists_nonvanishing_of_toroidal hH.sieg hX.ks)⟩ hX hP hH hSW hGD ⟨hP.q6, hP.q8, hP.q13, hP.q7, hP.q10, GlobalTheory.Published.chowFormIntExists_holds, ChowFormCompatibility.chow_form_hyperplane_section, hP.q12⟩
      (PositivityTheory.HtPt.Ah.deep_slim h₁ h₂ hPL hHS hBig hFar hZar hRR)

end SelfIntersectionVolumeEstimates
end
