module

public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep
