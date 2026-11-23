module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.highestWeight_generated_weights_below : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (μ : Ix p q → ℚ) (v : V), Formalism.BasicNotions.TH.IsHW act μ v → ∃ W : Submodule ℂ V, v ∈ W ∧ KStable act W ∧ (∀ W' : Submodule ℂ V, v ∈ W' → KStable act W' → W ≤ W') ∧ ∀ (ν : Ix p q → ℝ) (w : V), w ∈ W → w ≠ 0 → (∀ a, act (Eab a a) w = ((ν a : ℝ) : ℂ) • w) → ∃ c : Ix p q → Ix p q → ℕ, (∀ a b, c a b ≠ 0 → posC a b) ∧ ∀ x, ((μ x : ℚ) : ℝ) - ν x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) := by
  first | exact @GlobalTheory.RealPar.HwGen.hw_generated | exact GlobalTheory.RealPar.HwGen.hw_generated | (intros; apply GlobalTheory.RealPar.HwGen.hw_generated <;> assumption)
