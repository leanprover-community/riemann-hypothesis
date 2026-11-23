module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
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

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.sParam_measurePreserving | exact GlobalTheory.sParam_measurePreserving | (intros; apply GlobalTheory.sParam_measurePreserving <;> assumption)
