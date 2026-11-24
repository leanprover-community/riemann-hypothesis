module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.exists_prime_over :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      (∀ q : Ideal R, q.IsPrime → q ≤ p → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap R B) = q) ∧
      (∀ a : R, algebraMap R B a = 0 → ∃ s : R, s ∉ p ∧ s * a = 0) := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI := IsCplAt.flat R p B h
  refine ⟨fun q hq hqp => ?_, fun a ha => ?_⟩
  · haveI := hq
    haveI : (maximalIdeal B).LiesOver p := ⟨h.comap_eq.symm⟩
    obtain ⟨P, -, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal B) hqp
    exact ⟨P, hP, hlo.over.symm⟩
  · let Rp := Localization.AtPrime p
    haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
    have hmem : ∀ n : ℕ, algebraMap R Rp a ∈ (maximalIdeal Rp) ^ n := by
      intro n
      obtain ⟨s, hs, hsa⟩ := h.strict n a (by rw [ha]; exact zero_mem _)
      have hu : IsUnit (algebraMap R Rp s) := IsLocalization.map_units Rp (⟨s, hs⟩ : p.primeCompl)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      have := Ideal.mem_map_of_mem (algebraMap R Rp) hsa
      rw [map_mul] at this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rp) (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top
    have h0 : algebraMap R Rp a = 0 := by
      have : algebraMap R Rp a ∈ ⨅ i, (maximalIdeal Rp) ^ i := Ideal.mem_iInf.mpr hmem
      rw [hbot] at this
      exact (Ideal.mem_bot).mp this
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp a).mp h0
    exact ⟨s, hs, hsa⟩
