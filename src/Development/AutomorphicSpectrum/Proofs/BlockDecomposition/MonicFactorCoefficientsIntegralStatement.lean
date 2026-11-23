module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonicFactorCoefficientsIntegral
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


theorem _root_.GlobalTheory.T.monic_factor_coefficients_integral : ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) * Q.eval (algebraMap ℂ A (u + c₂)))) → ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  first | exact @GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | exact GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | (intros; apply GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product <;> assumption)
