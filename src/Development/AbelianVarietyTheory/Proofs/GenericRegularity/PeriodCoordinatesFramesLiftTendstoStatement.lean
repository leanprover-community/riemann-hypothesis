module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

theorem _root_.GlobalTheory.T.period_coordinates_frames_lift_tendsto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  first | exact @GlobalTheory.PeriodLift.period_lift | exact GlobalTheory.PeriodLift.period_lift | (intros; apply GlobalTheory.PeriodLift.period_lift <;> assumption)
