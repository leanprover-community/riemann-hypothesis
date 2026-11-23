module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.unitStrip_integral_eq_iterated : (∀ F : ℍ → ENNReal, Measurable F → ∫⁻ τ in strip, F τ = ∫⁻ y in Set.Ioi (0 : ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) * ENNReal.ofReal (1 / y ^ 2)) ∧ ∀ F : ℍ → ℂ, IntegrableOn F strip → ∫ τ in strip, F τ = ∫ y in Set.Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, F (ofComplex (x + y * Complex.I))) / (y : ℂ) ^ 2 := by
  first | exact @GlobalTheory.EisM.strip_iterated | exact GlobalTheory.EisM.strip_iterated | (intros; apply GlobalTheory.EisM.strip_iterated <;> assumption)
