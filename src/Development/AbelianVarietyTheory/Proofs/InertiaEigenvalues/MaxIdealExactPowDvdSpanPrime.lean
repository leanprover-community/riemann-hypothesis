module

public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem maxIdeal_exact_pow_dvd_span_prime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  intro L _ _ l e _ la hmax hin hout
  classical
  have hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1) := ⟨e, hout⟩
  have hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ e := Nat.find_min' hex hout
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h, zero_add, pow_one] at hspec; exact hspec hin
    · exact h
  have hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex := by
    have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_not] at h1
    have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [h4] at h1
  have hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hmem
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩
  by_contra hne
  have hJle : J ≤ la := by
    have h2 := hmax.eq_of_le hne le_sup_left
    calc J ≤ la ⊔ J := le_sup_right
      _ = la := h2.symm
  apply hspec
  have h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1) := by
    rw [hJ, pow_succ]; exact Ideal.mul_mono_right hJle
  exact h3 (Ideal.subset_span (Set.mem_singleton _))

end GlobalTheory
