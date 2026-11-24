module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
