module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInduction
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  first | (exact @GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (exact GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (intros; apply GlobalTheory.EtC.GmStep.FinSH.induction_principle  <;> assumption)
