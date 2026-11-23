module

public import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V ((V.l : C) • hCoef X γ V.l) ∧ ((∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg v)))) → ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i ((V.l : C) • hCoef X γ V.l)))) := by
  first | exact @GlobalTheory.GaugeCoef.main | exact GlobalTheory.GaugeCoef.main | (intros; apply GlobalTheory.GaugeCoef.main <;> assumption)
