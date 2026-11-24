module

public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
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

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

def SegmentBound : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ) (hr : 1 ≤ r), 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ (s s' : ℕ) (f f' : Fin (3 * r) → ℕ),
      s < n / ((6 * r + 1) * u) → s' < n / ((6 * r + 1) * u) →
      Marked T r u s → Marked T r u s' →
      (∀ j, 0 < j →
        j < (if s < s' then s' - s else s' + n / ((6 * r + 1) * u) - s) →
        ¬ Marked T r u ((s + j) % (n / ((6 * r + 1) * u)))) →
      StrictMono f → T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) = univ.image f →
      StrictMono f' → T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u)) = univ.image f' →
      let a := f ⟨r, by omega⟩
      let b := f' ⟨2 * r - 1, by omega⟩
      let D := if s < s' then b - a else b + n - a
      D < G' ∧ (a + D) % n = b ∧
        (T ∩ (range (D + 1)).image (fun j => (a + j) % n)).card ≤ N₁

def NextEvenTop : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ i < n, ∃ D ∈ Icc 1 G', (i + D) % n ∈ T ∧ Even ((i + D) % n)

def TopCount : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    n ≤ T.card * G' ∧ T.card * G' ≤ N₁ * (n + G')

end Formalism.GrowthSums
