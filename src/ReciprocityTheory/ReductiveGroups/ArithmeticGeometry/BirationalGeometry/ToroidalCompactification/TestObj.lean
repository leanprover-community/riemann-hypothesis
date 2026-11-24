module

public import Mathlib.Algebra.Order.PUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨PUnit.unit, LinearMap.ext fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (map_zero f).symm⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => by simp, fun x hx => absurd (Subsingleton.elim x 0) hx,
    fun a A t _ ht => by
      have hA : A = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
      subst hA
      simp [ht]⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
