module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finite_point_mem_opens {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      ∃ y : Spec (CommRingCat.of L) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧ Set.range y ⊆ W := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  have hc : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  refine ⟨X.residueField x, inferInstance, inferInstance, hfin, X.fromSpecResidueField x, hφ.symm, ?_⟩
  rw [Scheme.range_fromSpecResidueField]
  simpa using hxW

theorem moduli_exists_algebraic_point :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W : (Xo.XF c).Opens), (W : Set (Xo.XF c)).Nonempty → ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ ∃ y : Sp L ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ Set.range y ⊆ W := by
  intro E _ _ _ H D l Xo c W hW
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact exists_finite_point_mem_opens (pullback.snd _ _) W hW

end GlobalTheory
