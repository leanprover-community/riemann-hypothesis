module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
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

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
