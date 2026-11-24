module

public import Formalism.IncomingBounds.IncomingBound
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

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def rowRad {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d) (isTop : ι → Bool)
    (spec : ι → Option (ZMod d × ℤ)) (i : ι) : ℝ :=
  if isTop i then eps (lt i) else
    match spec i with
    | some (s, j) =>
        if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s)
        else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹
    | none => sig (lt i)

def ThmAAssembly : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
  ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
    (∀ s, nu1 s ≤ size s) →
  ∀ sig : ZMod d → ℝ, IsOptDual l d (fun s => (Dl d TT nu1 size s : ℝ)) sig →
  ∀ (ι : Type) [Fintype ι] (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ))
    (κ : ι → ℕ),
    (∀ i, isTop i = true → lt i ∈ TT ∧ spec i = none) →
    (∀ s ∈ TT, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) =
      (nu1 s : ℝ)) →
    (∀ s, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) =
      (Dl d TT nu1 size s : ℝ)) →
    (∀ i s j, spec i = some (s, j) → s ∈ TT ∧ Odd j ∧ lt i = s + (j : ZMod d) ∧
      (0 < j → l ^ j.toNat ≤ nu1 s) ∧ (j < 0 → l ^ (-j).toNat ≤ size (lt i))) →
    (∀ (s : ZMod d) (j : ℤ), (∑ i ∈ Finset.univ.filter (fun i => spec i = some (s, j)), (κ i : ℝ)) ≤
      (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ)) →
    ∃ eps : ZMod d → ℝ, (∀ s, 0 ≤ eps s) ∧
      (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) ∧
      (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) ≤
        ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)

end Formalism.DworkPowerSeriesWeights
