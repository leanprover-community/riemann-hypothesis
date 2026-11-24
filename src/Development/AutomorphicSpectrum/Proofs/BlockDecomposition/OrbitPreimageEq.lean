module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

open Matrix
open PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.EllProp

theorem twConj_twConj {G : Type*} [Group G] (θ : Monoid.End G) (x g d : G) :
    twConj θ x (twConj θ g d) = twConj θ (g * x) d := by
  simp only [twConj, map_mul]
  group

theorem orbit_preimage_eq {G : Type*} [Group G] (θ : Monoid.End G) (g d : G) (C : Set G) :
    {x | twConj θ x (twConj θ g d) ∈ C} = (fun y => g⁻¹ * y) '' {y | twConj θ y d ∈ C} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, twConj_twConj]
  constructor
  · intro h
    exact ⟨g * x, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem ellProperOf : EllProperOf := by
  intro hD hP _ n d hd C hC
  obtain ⟨g, d', z, h1, h2, h3, rfl⟩ := hD n d hd
  rw [orbit_preimage_eq]
  exact (hP n d' z h1 h2 h3 C hC).image (continuous_const.mul continuous_id)

end GlobalTheory.CompanionTheory.EllProp
