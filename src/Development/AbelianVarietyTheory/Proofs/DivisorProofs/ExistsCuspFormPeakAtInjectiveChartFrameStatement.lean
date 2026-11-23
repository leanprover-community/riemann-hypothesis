module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrame
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  first | exact @GlobalTheory.PeakThick.peak | exact GlobalTheory.PeakThick.peak | (intros; apply GlobalTheory.PeakThick.peak <;> assumption)
