module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne

@[expose] public section

namespace ReciprocityTheory.CA.AB.RegA

namespace IsRegularLocalRing

open IsLocalRing

universe u

theorem spanFinrank_span_finset_le {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card :=
  (Submodule.spanFinrank_span_le_ncard_of_finite (R := R) s.finite_toSet).trans_eq
    (Set.ncard_coe_finset s)

theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_repr_ne_zero b hv

theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.span_insert_image_erase_eq_top b v hj

theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx

theorem spanFinrank_maximalIdeal_quotient_succ_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2

theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.eq_natCast_and_add_one_eq_of_le h1 h2 h3

theorem spanFinrank_quotient_eq_and_ringKrullDim_add_one (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2

theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime :=
  Ideal.minimalPrimes_isPrime hp

theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle

theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain_of_maximalIdeal_eq_bot R h

theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R h

theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin

theorem quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.quotient_span_singleton hx hx2

theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2

theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain_of_forall_spanFinrank_lt R IH

theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R :=
  PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain_of_spanFinrank_le

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R := isDomain_of_spanFinrank_le _ R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

end IsRegularLocalRing

end ReciprocityTheory.CA.AB.RegA
