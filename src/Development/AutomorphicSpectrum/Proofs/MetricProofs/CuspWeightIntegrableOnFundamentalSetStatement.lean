module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.cusp_weight_integrable_on_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | exact GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW <;> assumption)
