module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.torsion_points_descend_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  first | exact @GlobalTheory.torsion_points_field_extension | exact GlobalTheory.torsion_points_field_extension | (intros; apply GlobalTheory.torsion_points_field_extension <;> assumption)
