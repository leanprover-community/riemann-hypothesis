module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRealSpanPeriodsOfCharacterKernel
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.mem_realSpan_periods_of_character_kernel : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  first | exact @GlobalTheory.PeriodSpan.mem_span_periods | exact GlobalTheory.PeriodSpan.mem_span_periods | (intros; apply GlobalTheory.PeriodSpan.mem_span_periods <;> assumption)
