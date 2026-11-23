module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SimilitudeDefiniteFormIsAlgebraicOnVector
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by
  first | exact @GlobalTheory.SimAlg.similitude_algebraic | exact GlobalTheory.SimAlg.similitude_algebraic | (intros; apply GlobalTheory.SimAlg.similitude_algebraic <;> assumption)
