module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq : ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
  [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E] [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
  ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ → (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
  ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
    ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E)) (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  first | exact @GlobalTheory.kummer_not_map_comap_le_sq | exact GlobalTheory.kummer_not_map_comap_le_sq | (intros; apply GlobalTheory.kummer_not_map_comap_le_sq <;> assumption)
