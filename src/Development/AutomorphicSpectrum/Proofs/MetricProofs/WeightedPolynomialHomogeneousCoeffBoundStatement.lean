module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBound
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | exact GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame <;> assumption)
