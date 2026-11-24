module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtension
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.finite_group_scheme_sum_extension : ∀ {X : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), 1 ≤ n → ∀ (xl : Sp K ⟶ X) (A : FG M (Sp K)), (∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')), (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J → e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.exists_gen_normalised <;> assumption)
