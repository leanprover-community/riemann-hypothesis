module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSection
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

def chartSubst {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  bind₁ (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ))

theorem chartSubst_X {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (p : Σ k, ι k) :
    chartSubst σ i (X p) = X (σ.symm (Function.update i p.1 p.2)) := by
  exact MvPolynomial.bind₁_X_right _ _

theorem chartSection_eq_chartSubst [Fintype K] [∀ k, Fintype (ι k)] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) :
    chartSection σ i s = chartSubst σ i (map (Int.castRingHom ℂ) s) := rfl

def ChartConeComponent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiProjPrime W → ∀ W' ∈ segreChartComponents W σ i,
      ∃ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W'

end GroundTheory.Heights₂.Heights.Targets
