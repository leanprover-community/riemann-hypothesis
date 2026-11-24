module

public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Mathlib.MeasureTheory.Constructions.Pi
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory

namespace PI.QuotProdK

def QuotProdK : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (ε : ∀ v, Fin (n v) → Bool)
    (N H : ∀ v, Set (Formalism.REAL.UJ (ε v))),
    (∀ v, IsClosed (N v)) → (∀ v, IsCompact (H v)) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ N v ∧ (∀ a ∈ N v, ∀ b ∈ N v, a * b ∈ N v) ∧ ∀ a ∈ N v, a⁻¹ ∈ N v) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ H v ∧ (∀ a ∈ H v, ∀ b ∈ H v, a * b ∈ H v) ∧ ∀ a ∈ H v, a⁻¹ ∈ H v) →
    (∀ v, ∀ h ∈ H v, ∀ m ∈ N v, h * m * h⁻¹ ∈ N v) →
    (∀ v (μ : Measure (Formalism.REAL.UJ (ε v))), SigmaFinite μ → μ ≠ 0 → μ (N v)ᶜ = 0 →
      (∀ s ∈ N v, μ.map (fun x => s * x) = μ) → ∀ s ∈ N v, μ.map (fun x => x * s) = μ) →
    ∀ muN muH nuQ : Measure (∀ v, Formalism.REAL.UJ (ε v)),
      (SigmaFinite muN ∧ muN ≠ 0 ∧ muN (Set.pi Set.univ N)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ N, muN.map (fun x => s * x) = muN) →
      (SigmaFinite muH ∧ muH ≠ 0 ∧ muH (Set.pi Set.univ H)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ H, muH.map (fun x => s * x) = muH) →
      (∀ f : (∀ v, Formalism.REAL.UJ (ε v)) → ENNReal, Measurable f →
        ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
          ∫⁻ x, (∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2))) ∂nuQ) →
      ∃ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (ε v))) (C : ENNReal), C ≠ 0 ∧ C ≠ ⊤ ∧
        (∀ v, (SigmaFinite (μS v) ∧ μS v ≠ 0 ∧ μS v {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}ᶜ = 0 ∧
          ∀ s ∈ {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}, (μS v).map (fun x => s * x) = μS v) ∧
          ∀ F : Formalism.REAL.UJ (ε v) → ENNReal, Measurable F →
            ∫⁻ x, F x ∂(Formalism.REAL.muG (ε v)) = ∫⁻ x, (∫⁻ s, F (s * x) ∂(μS v)) ∂(νl v)) ∧
        ∀ F : ∀ v, Formalism.REAL.UJ (ε v) → ENNReal, (∀ v, Measurable (F v)) →
          (∀ v, ∀ m ∈ N v, ∀ h ∈ H v, ∀ x, F v (m * h * x) = F v x) →
          ∫⁻ x, ∏ v, F v (x v) ∂nuQ = C * ∏ v, ∫⁻ y, F v y ∂(νl v)

end PI.QuotProdK
