module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosure
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → ∀ (t : A), (∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a)) → ∀ (m : ℕ) (y : Fin m → A), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) → ∀ y' : Fin m → B, (∀ j, (y' j : K) = algebraMap F K (y j)) → IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  first | (exact @GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (exact GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (intros; apply GlobalTheory.isTranscendenceBasis_quotient_integralClosure <;> assumption)
