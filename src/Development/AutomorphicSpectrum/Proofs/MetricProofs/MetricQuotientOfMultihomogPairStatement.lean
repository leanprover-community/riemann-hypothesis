module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.metric_quotient_of_multihomog_pair : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | exact GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay <;> assumption)
