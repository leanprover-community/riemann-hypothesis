module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.RepresentationRank

noncomputable abbrev proj {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens) :
    (V : Scheme.{0}) ⟶ T.left :=
  V.ι ≫ (fst T G).left

def Rep {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens) : Prop :=
  IsClosed (U : Set (Y ⊗ G).left) ∧
    ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) →
      ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V

def RepOfRank {S : Scheme.{0}} (r : ℕ) (G Y : Over S) (U : (Y ⊗ G).left.Opens) : Prop :=
  IsClosed (U : Set (Y ⊗ G).left) ∧ (∀ y, (proj U).finrank y = r) ∧
    ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) →
      (∀ t, (proj V).finrank t = r) → ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V

end UpperTheory.RepresentationRank
