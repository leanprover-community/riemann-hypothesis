module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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

namespace PI.VolStabS

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLat : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T → ∀ Nb ∈ 𝓝 T, (∀ x, G x ∈ Nb → x ∈ U) →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
      (∀ y ∈ L, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, (L : Set V).indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabS
