module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' : ∀ (g : ℕ) (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ k ∈ S, c₁ k = 0) → thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (thetaCharOff S τ c₁ c₂) ∧ ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z, thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) = a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaCharOff S τ c₁ c₂ z := by
  exact @GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic
