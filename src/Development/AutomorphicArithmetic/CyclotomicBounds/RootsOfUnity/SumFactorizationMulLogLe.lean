module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuQDUnit
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.HC KStar.Tree

private theorem sum_factorization_mul_log_le (m : ℕ) (S : Finset ℕ) :
    ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l ≤ Real.log m := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l
      = ∑ l ∈ S.filter (· ∈ m.factorization.support), (m.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro l _ h
        by_contra hs
        rw [Finsupp.notMem_support_iff.mp hs] at h
        simp at h
    _ ≤ ∑ l ∈ m.factorization.support, (m.factorization l : ℝ) * Real.log l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          exact (Finset.mem_filter.mp hl).2
        · intro l hl _
          have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using hl)
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

theorem UpperTheory.Mu.nuSum :
    ∀ (φ : Frame) (H : HostRaw φ) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → ¬ (H.q - 1) / 2 ∣ n → ¬ (H.d - 1) / 2 ∣ n → ∀ ν : ℕ → ℕ, (∀ (l : ℕ) [Fact l.Prime], ν l = nuOf l (cyc l H.E Ω) n) → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (ν l : ℝ) * Real.log l ≤ Real.log H.QS + Real.log n := by
  intro φ H Ω _ _ _ n hn hq hd ν hν S hS
  have key : ∀ l ∈ S, (ν l : ℝ) * Real.log l ≤
      (H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l := by
    intro l hl
    have hp : l.Prime := hS l hl
    haveI : Fact l.Prime := ⟨hp⟩
    have hlog : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hnat : ν l ≤ H.QS.factorization l + n.factorization l := by
      rw [hν l]
      by_cases hlq : l = H.q
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inl hlq) (hlq ▸ hq)]
        exact Nat.zero_le _
      by_cases hld : l = H.d
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inr hld) (hld ▸ hd)]
        exact Nat.zero_le _
      have := UpperTheory.Mu.nuLe φ H l Ω n hn hlq hld
      split_ifs at this <;> omega
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hlog
    exact_mod_cast hnat
  calc ∑ l ∈ S, (ν l : ℝ) * Real.log l
      ≤ ∑ l ∈ S, ((H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l) :=
        Finset.sum_le_sum key
    _ = ∑ l ∈ S, (H.QS.factorization l : ℝ) * Real.log l + ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_add_distrib
    _ ≤ Real.log H.QS + Real.log n :=
        add_le_add (sum_factorization_mul_log_le H.QS S) (sum_factorization_mul_log_le n S)
