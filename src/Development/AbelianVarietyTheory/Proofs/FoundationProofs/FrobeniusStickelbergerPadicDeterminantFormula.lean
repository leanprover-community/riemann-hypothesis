module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameterStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplexStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLogStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDeterminantDefectOnLineStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerSigmaStarDetComplexStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerTaylorDefectEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicDataStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransportStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLinesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

theorem frobenius_stickelberger_padic_determinant_formula : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data D p cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  obtain ⟨hAa, hBa, hS, hAv, hBv⟩ := GlobalTheory.T.sigmaStar_cube_columns_model_parameter_series p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hCa, hCv⟩ := GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series GlobalTheory.T.model_parameter_series_deriv_transport p g hq hL h2 h3 hσ v hv hw
  have hF : ∀ j, AlgEnt (![colA g.abelian₂, colB g.abelian₂ v, colC g.abelian₂ v] j) := by
    intro j; fin_cases j
    exacts [hAa, hBa, hCa]
  have h6 := GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex p g.lam _ (sgStar g.abelian₂) hF hσ (GlobalTheory.T.frobeniusStickelberger_taylor_defect_eq_zero GlobalTheory.T.mvPowerSeries_fin_three_eq_zero_of_subst_lines GlobalTheory.T.frobeniusStickelbergerDeterminantDefect_on_line GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex g.abelian₂ hL v hv)
  obtain ⟨c0, c1, c2, c3, h7⟩ := GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log p g ok
  have h8 := h7 ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) _ _ h6
  have e : ∀ F : ℂ → ℂ, (PowerSeries.subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) (GL3Theta.ser1 g.lam F) : PowerSeries ℂ_[p]) = g.atU F :=
    fun F => (GlobalTheory.SerTransport.atU_eq g F).symm
  simp only [e, hS] at h8
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  refine GlobalTheory.T.det_column_operations_model_parameter p (ePhi1 g.lam g.abelian₂ g.C g.wq) g.wq ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) g.C.r g.W.a₁ g.W.a₃ _ _ _ _ (Units.ne_zero _) hw0 c0 c1 c2 c3 ?_
  rw [← h8]
  congr 1
  ext i j
  fin_cases j <;> simp [hAv, hBv, hCv]

end GlobalTheory.FrobStick
