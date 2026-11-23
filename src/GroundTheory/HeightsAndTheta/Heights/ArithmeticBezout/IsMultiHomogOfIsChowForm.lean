module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)

variable {n : ℕ}

theorem specFirst_eq {R : Type*} [CommRing R] {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R)
    (u : Fin n → R) : specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f := by
  rw [specFirst, IndefiniteRowSideFullHecke.ArithBezout.specFirst, aeval_eq_bind₁]
  rfl

theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by
  have h : (fun ij => map φ (specFirstVar u ij)) =
      (specFirstVar (φ ∘ u) : Fin (e + 1) × Fin n → MvPolynomial (Fin e × Fin n) S) := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [specFirstVar]
  rw [← specFirst_eq, ← specFirst_eq, specFirst, specFirst, map_bind₁, h]

end ObjectsChow

end GroundTheory.Heights₂.Heights
