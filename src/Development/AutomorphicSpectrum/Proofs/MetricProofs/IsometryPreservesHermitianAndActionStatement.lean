module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
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

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.isometry_preserves_hermitian_and_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | exact GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes <;> assumption)
