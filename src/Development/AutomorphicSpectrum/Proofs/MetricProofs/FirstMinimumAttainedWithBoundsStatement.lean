module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAttainedWithBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.first_minimum_attained_with_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (vr : ℝ), IsCMFam σ → R.HasSig σ j j' → 1 ≤ j' → 0 < vr → (∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr) → 0 < R.lam1 ∧ (∃ x, x ≠ 0 ∧ Real.sqrt (R.normSq x) = R.lam1) ∧ (∀ x y, Real.sqrt (R.normSq x) < vr ^ (-(1 / 2 : ℝ)) → Real.sqrt (R.normSq y) < vr ^ (-(1 / 2 : ℝ)) → ∀ a : 𝓞 E, R.form (a • x) y = 0) ∧ ∀ t : ℝ, R.lam1 < t → t ≤ vr ^ (-(1 / 2 : ℝ)) → {x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t}.Finite ∧ (({x : Λ | x ≠ 0 ∧ Real.sqrt (R.normSq x) < t}.ncard : ℝ)) ≤ (3 * t / R.lam1) ^ (2 * Fintype.card Ψ * j') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ShortVec.short_vectors | exact GlobalTheory.CompanionTheory.Ar.Cusp.ShortVec.short_vectors | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ShortVec.short_vectors <;> assumption)
