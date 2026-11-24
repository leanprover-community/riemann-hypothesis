module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatrices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by
  first | exact @GlobalTheory.map_withDensity_of_jacobian | exact GlobalTheory.map_withDensity_of_jacobian | (intros; apply GlobalTheory.map_withDensity_of_jacobian <;> assumption)
