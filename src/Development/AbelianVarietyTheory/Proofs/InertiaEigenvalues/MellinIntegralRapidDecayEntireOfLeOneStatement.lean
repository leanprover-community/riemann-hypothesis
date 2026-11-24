module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ → (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν → (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) → (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧ Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  first | exact @GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | exact GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | (intros; apply GlobalTheory.integral_mul_cpow_of_rapid_decay_entire <;> assumption)
