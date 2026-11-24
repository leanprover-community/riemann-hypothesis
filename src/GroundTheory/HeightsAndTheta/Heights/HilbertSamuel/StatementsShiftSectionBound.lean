module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftSectionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ∧
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) + C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
