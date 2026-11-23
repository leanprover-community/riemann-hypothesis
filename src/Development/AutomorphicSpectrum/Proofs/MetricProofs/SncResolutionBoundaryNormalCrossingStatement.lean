module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionBoundaryNormalCrossing
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

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_boundary_normal_crossing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_sncData_of_isSncModel <;> assumption)
