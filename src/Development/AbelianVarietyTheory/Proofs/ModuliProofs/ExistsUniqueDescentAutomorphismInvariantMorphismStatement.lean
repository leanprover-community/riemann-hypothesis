module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueDescentAutomorphismInvariantMorphism
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.existsUnique_descent_automorphism_invariant_morphism : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  first | exact @GlobalTheory.InvariantMorDescent.existsUnique_desc | exact GlobalTheory.InvariantMorDescent.existsUnique_desc | (intros; apply GlobalTheory.InvariantMorDescent.existsUnique_desc <;> assumption)
