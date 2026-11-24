module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ArithmeticVolumeDimensionOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (M : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    IsNefBigDatum P0 y 0 M → 0 < II K ι (mCoordIdeal y) 1 (fun _ => M) →
    ∃ (n : ℕ) (s : Ω), 1 ≤ n ∧ s ∈ chartLat y M.a n ∧ s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y M n c s

namespace ArithmeticVolumeDimensionOne

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end ArithmeticVolumeDimensionOne

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
