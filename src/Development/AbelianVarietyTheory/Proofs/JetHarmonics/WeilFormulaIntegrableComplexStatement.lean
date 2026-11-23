module

public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.weil_formula_integrable_complex : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  first | exact @GlobalTheory.weil_formula_integrable | exact GlobalTheory.weil_formula_integrable | (intros; apply GlobalTheory.weil_formula_integrable <;> assumption)
