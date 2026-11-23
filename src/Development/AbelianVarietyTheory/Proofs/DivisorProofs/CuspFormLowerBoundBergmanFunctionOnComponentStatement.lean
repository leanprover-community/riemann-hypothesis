module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  first | exact @GlobalTheory.BergLower.le_bergOn | exact GlobalTheory.BergLower.le_bergOn | (intros; apply GlobalTheory.BergLower.le_bergOn <;> assumption)
