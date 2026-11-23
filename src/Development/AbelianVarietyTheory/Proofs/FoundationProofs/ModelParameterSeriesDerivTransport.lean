module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.DerivTransport

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) :
    coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · exact (contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = PowerSeries.derivative (R := ℂ_[p]) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  ext n
  have e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ) := by
    rw [taylorCoeffAtZero_deriv, ha]; push_cast; rfl
  rw [PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha,
    GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]
  simp [mul_comm]

theorem atU_deriv : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  intro p _ g F hF
  refine ⟨algEnt_deriv hF, ?_⟩
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    PowerSeries.derivative_subst hs]
  have hd : PowerSeries.derivative (R := ℂ_[p]) (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) =
      PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l,
      GlobalTheory.WpForm.derivative_flog]
  rw [hd]
  ring

end GlobalTheory.DerivTransport

end
