module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_hermitian_type_compatibility : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → (∀ j k, ty j ≠ ty k → Hm j k = 0) ∧ (∀ (τ : E →+* ℂ) x y, hermForm Hm (tyPart ty τ (P x)) (tyPart ty τ (P y)) - star (hermForm Hm (tyPart ty (ComplexEmbedding.conjugate τ) (P x)) (tyPart ty (ComplexEmbedding.conjugate τ) (P y))) = 2 * Complex.I * τ (sesq D x y)) ∧ ∀ (r : ℕ) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (Matrix.of fun m n => sesq D (e m) (e n)).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | exact GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component <;> assumption)
