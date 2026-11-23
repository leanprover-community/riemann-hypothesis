module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicPeriodFamily
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.local_holomorphic_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g n : ℕ) (ty : Fin g → (E →+* ℂ)) (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g D.La), IsTypeFn H D.p D.q ty → IsOpen V → IsHolFam V R → (∀ t ∈ V, (R t).form = D.EF ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp (R t).B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) → ∀ t₀ ∈ V, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ))) (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolPeriods D ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧ ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ (R t).P x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem | exact GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.period_of_riem <;> assumption)
