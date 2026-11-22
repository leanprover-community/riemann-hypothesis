module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries

@[expose] public section

open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Res

variable {A : Type} [CommRing A] [Finite A] {p : ℕ}

def owedC_res (hp : p.Prime) (h : Nat.card A = p) : A ≃+* ZMod p :=
  letI := Fintype.ofFinite A
  (ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card]; exact h)).symm

theorem owedC_res_intCast (hp : p.Prime) (h : Nat.card A = p) (a : ℤ) :
    owedC_res hp h (a : A) = (a : ZMod p) := map_intCast _ _

theorem owedC_exists_int (hp : p.Prime) (h : Nat.card A = p) (x : A) : ∃ a : ℤ, x = (a : A) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨((owedC_res hp h x).val : ℤ), ?_⟩
  apply (owedC_res hp h).injective
  rw [owedC_res_intCast]
  simp

theorem owedC_intCast_eq_iff (hp : p.Prime) (h : Nat.card A = p) (a b : ℤ) :
    (a : A) = (b : A) ↔ (p : ℤ) ∣ a - b := by
  rw [← (owedC_res hp h).injective.eq_iff, owedC_res_intCast, owedC_res_intCast,
    ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

variable {K : Type} [Field K]

end Res

section Chars

variable {X : Fields} {Pr : Primes X}

end Chars

section Weil

variable {X : Fields} {Pr : Primes X}

end Weil

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
