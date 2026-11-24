module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBounds
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.first_minimum_and_cusp_weight_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsCMFam σ → R.HasRank σ m → 1 ≤ m → 0 < R.lam1 ∧ (∀ v : Λ, v ≠ 0 → R.lam1 ≤ Real.sqrt (R.normSq v)) ∧ (∀ I, R.IsCusp I → -Real.log (R.nz σ I) ≤ R.cuspW σ ∧ Module.finrank (𝓞 E) I ≤ m) ∧ 0 ≤ R.cuspW σ ∧ R.cuspW σ ≤ Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | exact GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le <;> assumption)
