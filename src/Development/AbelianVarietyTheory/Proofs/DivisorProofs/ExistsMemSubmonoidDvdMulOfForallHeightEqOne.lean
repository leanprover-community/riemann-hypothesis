module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
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
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
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

open IsLocalRing

namespace GlobalTheory

theorem exists_mem_submonoid_dvd_mul_of_forall_height_eq_one :
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  intro B _ _ _ _ S _ x y hy h
  by_contra! hS
  set M := B ⧸ Ideal.span {y}
  set N : Submodule B M := B ∙ (Ideal.Quotient.mk (Ideal.span {y}) x)
  have hmem : ∀ r : B, r ∈ Module.annihilator B N ↔ y ∣ r * x := by
    intro r
    change r ∈ Submodule.annihilator N ↔ _
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  set I := Module.annihilator B N
  have hdisj : Disjoint (S : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro u hu huI
    exact hS u hu ((hmem u).mp huI)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  obtain ⟨P', hP'min, hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
  have hass : P' ∈ associatedPrimes B N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B N hP'min
  have hass' : P' ∈ associatedPrimes B M :=
    associatedPrimes.subset_of_injective Subtype.val_injective (f := N.subtype) hass
  obtain ⟨hpr, h1, hyP⟩ := (mem_associatedPrimes_iff_height_eq_one hy).mp hass'
  obtain ⟨t, htQ, ht⟩ := h P' hpr h1 hyP (hPS.symm.mono_right hP'P)
  exact htQ (hP'min.1.2 ((hmem t).mpr ht))

end GlobalTheory
