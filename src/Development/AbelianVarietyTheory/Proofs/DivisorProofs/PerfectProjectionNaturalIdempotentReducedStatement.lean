module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectProjectionNaturalIdempotentReduced
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.perfectProjection_natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  first | exact @GlobalTheory.PerfectProj.natural_idempotent_reduced | exact GlobalTheory.PerfectProj.natural_idempotent_reduced | (intros; apply GlobalTheory.PerfectProj.natural_idempotent_reduced <;> assumption)
