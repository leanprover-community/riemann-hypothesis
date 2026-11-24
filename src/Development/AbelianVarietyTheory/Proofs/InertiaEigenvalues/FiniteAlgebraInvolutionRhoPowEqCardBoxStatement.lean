module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAlgebraInvolutionRhoPowEqCardBox
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

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.finiteAlgebraInvolution_rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  first | exact @GlobalTheory.UnitLemma.rho_pow_eq_card_box | exact GlobalTheory.UnitLemma.rho_pow_eq_card_box | (intros; apply GlobalTheory.UnitLemma.rho_pow_eq_card_box <;> assumption)
