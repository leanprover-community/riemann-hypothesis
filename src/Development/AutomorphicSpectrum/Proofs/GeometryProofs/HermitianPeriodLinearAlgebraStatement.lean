module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.hermitian_period_linear_algebra : ∀ (p q g : ℕ) (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ) (π : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ), IsLinearMap ℂ T → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → S.det ≠ 0 → LinearIndependent ℂ V → LinearIndependent ℂ W → (∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) → (∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W)) → (∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n) → ∃! x : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × ℂ, (∀ n, T' (π n) = ∑ j, x.2.1 j n • W j) ∧ (∀ j n, ∑ m, x.1 j m * S m n = x.2.1 j n) ∧ x.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • π m) = V a) ∧ ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • π m) = V a) → (Matrix.fromRows C x.1).det = x.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | exact GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra <;> assumption)
