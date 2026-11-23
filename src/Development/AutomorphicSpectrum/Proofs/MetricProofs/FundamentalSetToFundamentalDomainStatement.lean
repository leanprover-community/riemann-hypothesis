module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FundamentalSetToFundamentalDomain
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.fundamental_set_to_fundamental_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))), F.IsArith Γ → F.IsFundSet Γ FF → IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ → (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') → ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul <;> assumption)
