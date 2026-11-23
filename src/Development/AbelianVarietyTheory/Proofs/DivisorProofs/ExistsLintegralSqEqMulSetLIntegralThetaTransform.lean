module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodingerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvariStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainThetaStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F ψ hψ κ Φ γ hγ w])]
  simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
