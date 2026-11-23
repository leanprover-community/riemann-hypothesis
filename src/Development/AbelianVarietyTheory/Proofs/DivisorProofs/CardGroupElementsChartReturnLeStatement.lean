module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.card_group_elements_chart_return_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  first | exact @GlobalTheory.chart_mult_le | exact GlobalTheory.chart_mult_le | (intros; apply GlobalTheory.chart_mult_le <;> assumption)
