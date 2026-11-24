module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaWithCutoffSubgroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.weil_formula_with_cutoff_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  first | exact @GlobalTheory.weil_formula_cutoff | exact GlobalTheory.weil_formula_cutoff | (intros; apply GlobalTheory.weil_formula_cutoff <;> assumption)
