module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnConvolutionIntegrableOnSlice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftHasTypeAtPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsCuspidalOfDefinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardThetaLiftIsCuspidalOfIntegrable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralIntegrableOnAutomorphicQuotient
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaIntegralIntegrableOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaKernelMulCuspFormIntegrableOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftHasKType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsSmoothAutomorphic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormHasKType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaIntegralConverges
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftHasKType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspSmoothLift
theorem cuspidal_lift_smooth_at_of_cuspidal_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_integral_integrableOn_automorphic_quotient hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_upward_theta_integral_converges hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro t j hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.columnConvolution_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.columnLift_isAutomorphicFunction hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_isCuspForm hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc⟩
end GlobalTheory.CuspSmoothLift
end
end

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  first | exact @_root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | exact _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | (intros; apply _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift <;> assumption)
end
