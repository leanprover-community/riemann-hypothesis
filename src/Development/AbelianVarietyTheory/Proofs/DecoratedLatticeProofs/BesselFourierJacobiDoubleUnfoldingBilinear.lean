module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DoubleStepLin

theorem besselFourierJacobi_doubleUnfolding_bilinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    (∀ (Ξ Ξ' : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ B.V₀ J.W₀ Ξ' → IsThetaFunO ψ J.W₀ B'.V₀ Θ →
      hand0 s₁ s₂ l vL φ (Ξ + Ξ') Θ = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ' Θ) ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ (c • Ξ) Θ = c • hand0 s₁ s₂ l vL φ Ξ Θ) ∧
    (∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ Θ' : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → IsThetaFunO ψ J.W₀ B'.V₀ Θ' →
      hand0 s₁ s₂ l vL φ Ξ (Θ + Θ') = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ Θ') ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ Ξ (c • Θ) = c • hand0 s₁ s₂ l vL φ Ξ Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ hφ
  refine ⟨fun Ξ Ξ' Θ hΞ hΞ' hΘ => ?_, fun c Ξ Θ => ?_, fun Ξ Θ Θ' hΞ hΘ hΘ' => ?_, fun c Ξ Θ => ?_⟩
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_first_datum s₁ s₂ l vL (Ξ₂ := Θ) hφ hΞ hΞ' hΘ 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, handBF, map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (φ _) c, integral_const_mul, star_mul', star_star]
    simp_rw [show ∀ x y : ℂ, x * (c * y) = c * (x * y) from fun x y => by ring, integral_const_mul]
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_second_datum s₁ s₂ l vL hφ hΞ hΘ hΘ' 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul]

end GlobalTheory.DoubleStepLin
