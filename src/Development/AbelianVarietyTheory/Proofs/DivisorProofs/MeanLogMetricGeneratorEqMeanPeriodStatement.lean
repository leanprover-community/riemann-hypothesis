module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriod
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  first | exact @GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | exact GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | (intros; apply GlobalTheory.MeanPeriodGenerator.mean_logMet_eq <;> assumption)
