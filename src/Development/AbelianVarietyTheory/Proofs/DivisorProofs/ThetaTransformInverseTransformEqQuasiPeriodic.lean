module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    fun_prop
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
