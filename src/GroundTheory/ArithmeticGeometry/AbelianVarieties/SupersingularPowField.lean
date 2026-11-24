module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [DecidableEq F] (E E' : WeierstrassCurve F) (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]

variable {E E'} [E.IsElliptic] [E'.IsElliptic]


omit [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in
theorem Isogeny.val_eq_some_x_y (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  obtain ⟨Q, ⟨x, y, h, rfl, -⟩, -⟩ := φ
  rfl

variable [IsAlgClosed F]

end GroundTheory.Arith.Abelian
