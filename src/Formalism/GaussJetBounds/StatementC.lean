module

public import Formalism.GaussJetBounds.Statement
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

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def frameM {K : Type u} [Field K] {d N0 N1 : ℕ} (x : ZMod d × Fin N0 × Fin N0 → K) :
    ZV d N0 N1 → ZV d N0 N1 → K :=
  fun z y => if y.1 = z.1 ∧ y.2.2 = z.2.2 then x (z.1, y.2.1, z.2.1) else 0

def FramePure : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0) (x : ZMod d × Fin N0 × Fin N0 → K), (∀ y, ‖x y‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K,
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
    ∀ (s s' : ZMod d), s ≠ s' → ∀ (k : Fin N0) (b b' : Fin N1) (α β : ℕ),
      (b ≠ b' → MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b') α β)
          (bSum (frameM (N1 := N1) x) be) = 0) ∧
      ((if β ≤ α then ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖
          else ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖) ≤ ‖(l : K)‖ →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1))
          (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
          (MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
            (bSum (frameM (N1 := N1) x) be)))

end Formalism.DworkPowerSeriesWeights
