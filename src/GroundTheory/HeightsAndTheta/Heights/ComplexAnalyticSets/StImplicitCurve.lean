module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology

noncomputable section

def ImplicitCurve.Statement : Prop :=
  ∀ (n k : ℕ) (γ : (Fin (k + 1) → ℂ) → Fin n → ℂ) (R : ℝ) (L : Matrix (Fin k) (Fin n) ℂ)
    (s : Fin (k + 1) → ℂ),
    DifferentiableOn ℂ γ (Metric.ball 0 R) → s ∈ Metric.ball 0 R →
    Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ t)) s) →
      ∃ r > 0, ∃ φ : (Fin 1 → ℂ) → Fin (k + 1) → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ φ 0 = s ∧
        (∀ τ ∈ Metric.ball 0 r,
          φ τ ∈ Metric.ball 0 R ∧ φ τ 0 = s 0 + τ 0 ∧ L *ᵥ γ (φ τ) = L *ᵥ γ s) ∧
        ∃ P ∈ 𝓝 s, ∀ t ∈ P, L *ᵥ γ t = L *ᵥ γ s → ∃ τ ∈ Metric.ball 0 r, φ τ = t

end

end GroundTheory.Heights₂.Heights
