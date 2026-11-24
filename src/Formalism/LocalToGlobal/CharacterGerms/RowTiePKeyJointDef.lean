module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def JointEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C], IsAlgClosed C → ∀ (n q : ℕ), 2 ≤ q →
    ∀ (T : Set (Matrix (Fin n) (Fin n) C)), (∀ t ∈ T, t ^ q = t) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    ∀ v : Fin n → C, ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧
      ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
