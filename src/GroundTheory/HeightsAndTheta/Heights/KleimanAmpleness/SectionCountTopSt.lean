module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Top.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) (d + 1) → IsVeryAmple Nb.toSubSystem →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)

end

end GroundTheory.Heights₂.Heights.Kleiman
