module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

namespace GlobalTheory.Published

def ThetaRationalInvariance : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ W : WeilO D cc δ N N' e0,
      ∃ a a' : D.what₂.Tau → ℤ,
        (∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧ (∀ τ, 2 * a' τ = W.ep * W.chV.n τ + (N : ℤ)) ∧
        ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E),
          IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' →
          ∀ F ∈ TT D (tor0 D cc δ) N N',
            W.Om γA γA' F = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ)) * embT D τ γ'.det ^ (-(a' τ))) *
              pull D (tor0 D cc δ) γ γ' F z

theorem thetaRationalInvariance_holds : ThetaRationalInvariance := by
  intro D cc δ hc N N' hN e0 he W
  have h : ∀ (ε n : ℤ) (k : ℕ), (ε = 1 ∨ ε = -1) → Even (n - k) →
      (∃ a, 2 * a = ε * n + k) ∧ ∃ a, 2 * a = ε * n - k := by
    rintro ε n k (rfl | rfl) ⟨j, hj⟩
    · exact ⟨⟨j + k, by omega⟩, ⟨j, by omega⟩⟩
    · exact ⟨⟨-j, by omega⟩, ⟨-j - k, by omega⟩⟩
  choose a' ha' using fun τ => (h _ _ N W.ep_pm.1 (W.chV.par τ)).1
  choose a ha using fun τ => (h _ _ N' W.ep_pm.2 (W.chV'.par τ)).2
  exact ⟨a, a', ha, ha', fun g g' γ γ' hr hr' =>
    GlobalTheory.OddRank.oddEq_of_mem hc hN he W g g' γ γ' a a' hr hr' ha' ha⟩

end GlobalTheory.Published
