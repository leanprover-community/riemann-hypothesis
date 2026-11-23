module

public import GroundTheory.HeightsAndTheta.Theta.Cartan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Theta

open MeasureTheory Matrix GroundTheory.Automorphic
open scoped NNReal ComplexOrder MatrixOrder

noncomputable section

variable {p q : ℕ}

def indefJElem (p q : ℕ) : indefiniteUnitaryGroup p q :=
  upqOfMatrix (indefJ p q) (by rw [indefJ_conjTranspose, indefJ_mul_self, Matrix.one_mul])

theorem indefJElem_mul_self : indefJElem p q * indefJElem p q = 1 :=
  Subtype.ext (Units.ext (indefJ_mul_self p q))

theorem indefJElem_mul_mul_indefJElem (s : cartanPos p q) :
    indefJElem p q * upqOfMatrix s.1 s.2.2 * indefJElem p q = (upqOfMatrix s.1 s.2.2)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change indefJ p q * s.1 * indefJ p q = indefJ p q * s.1ᴴ * indefJ p q
  rw [s.2.1.isHermitian.eq]

variable [MeasurableSpace (indefiniteUnitaryGroup p q)] [BorelSpace (indefiniteUnitaryGroup p q)]

end

end GroundTheory.Heights₂.Theta
