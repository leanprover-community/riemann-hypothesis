module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Lemmata.GeneralBFactRest.Imports
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem exists_assoc_step {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) :
    ∃ q ∈ associatedPrimes R (QuotSMulTop x M), p < q ∧ x ∈ q ∧ x ∉ p := by
  first | exact Bl.general_b_fact_rest.goal1 .. | (apply Bl.general_b_fact_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_rest.goal1 <;> assumption)

theorem length_le_of_isRegular_of_mem_associatedPrimes : ∀ (rs : List R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M],
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsRegular M rs → ∀ {p : Ideal R},
    p ∈ associatedPrimes R M → (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
  | [], M, _, _, _, _, _, p, hp => by
    have : p.IsPrime := hp.isPrime
    have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial
  | x :: rs', M, _, _, _, hm, reg, p, hp => by
    obtain ⟨hreg, hreg'⟩ := (isRegular_cons_iff M x rs').mp reg
    have hx : x ∈ maximalIdeal R := hm x List.mem_cons_self
    obtain ⟨q, hq, hpq, hxq, hxnp⟩ := exists_assoc_step hp hx hreg
    have ih := length_le_of_isRegular_of_mem_associatedPrimes rs'
      (fun r hr => hm r (List.mem_cons_of_mem _ hr)) hreg' hq
    have hpp : p.IsPrime := hp.isPrime
    have hxp : Ideal.Quotient.mk p x ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact hxnp
    have hdim : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
      ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
        (Ideal.Quotient.factor_surjective hpq.le) (mem_nonZeroDivisors_of_ne_zero hxp)
        (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq)
    calc ((x :: rs').length : WithBot ℕ∞) = (rs'.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ q) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ p) := hdim

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem ModDepthGE.le_ringKrullDim_quotient_of_mem_associatedPrimes {n : ℕ}
    (h : ModDepthGE R M n) {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  subst hlen
  exact length_le_of_isRegular_of_mem_associatedPrimes rs hmem hreg hp

end ReciprocityTheory.CA
