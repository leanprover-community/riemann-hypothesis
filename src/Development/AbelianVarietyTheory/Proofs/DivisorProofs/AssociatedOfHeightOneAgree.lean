module

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

@[expose] public section

namespace GlobalTheory

theorem exists_unit_eq_mul_of_height_one_avoiding (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n))
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (hdiv : ∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) :
    ∃ u : Rˣ, a = u * b := by

  have avoid : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → ∀ x : R, x ≠ 0 → x ∈ Q →
      (∀ j ∈ J, Prime (π j) → ¬ π j ∣ x) → ∀ j ∈ J, π j ∉ Q := by
    intro Q hQ h1 x hx hxQ hnd j hj hjQ
    rcases hπ j hj with hu | hp
    · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hjQ hu)
    · have hmin := mem_minimalPrimes_span_singleton_of_height_eq_one h1 hp.ne_zero hjQ
      have hsp : (Ideal.span {π j}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hle : Q ≤ Ideal.span {π j} :=
        hmin.2 ⟨hsp, le_refl _⟩ ((Ideal.span_singleton_le_iff_mem Q).mpr hjQ)
      exact hnd j hj hp (Ideal.mem_span_singleton.mp (hle hxQ))
  have hba : b ∣ a := dvd_of_forall_height_eq_one hb fun Q _ h1 hbQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 b hb hbQ fun j hj hp => (hdiv j hj hp).2)
    exact ⟨d, hd, c, by rw [mul_comm d a, e]⟩
  have hab : a ∣ b := dvd_of_forall_height_eq_one ha fun Q _ h1 haQ => by
    obtain ⟨c, d, hc, hd, e⟩ :=
      h Q inferInstance h1 (avoid Q h1 a ha haQ fun j hj hp => (hdiv j hj hp).1)
    exact ⟨c, hc, d, by rw [mul_comm c b, ← e]⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hba hab
  exact ⟨u, by rw [← hu, mul_comm]⟩

end GlobalTheory
