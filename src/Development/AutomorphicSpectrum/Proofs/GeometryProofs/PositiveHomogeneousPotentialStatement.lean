module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotential
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.positive_homogeneous_potential : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  exact @GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line
