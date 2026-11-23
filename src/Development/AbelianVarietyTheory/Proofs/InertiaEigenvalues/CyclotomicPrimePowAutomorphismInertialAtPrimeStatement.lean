module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPrimePowAutomorphismInertialAtPrime
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
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

theorem _root_.GlobalTheory.T.cyclotomicPrimePow_automorphism_inertial_at_prime : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) → ∀ τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ}), (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧ (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  first | exact @GlobalTheory.CycInertial.main | exact GlobalTheory.CycInertial.main | (intros; apply GlobalTheory.CycInertial.main <;> assumption)
