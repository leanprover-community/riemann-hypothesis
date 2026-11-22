module

public import Mathlib

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

namespace UpperTheory.V.abelian₂

section Lift

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

theorem eq_of_sub_mem_pow (I : Ideal R) [IsHausdorff I R] {a b : R} (h : ∀ n, a - b ∈ I ^ n) : a = b := by
  apply sub_eq_zero.mp
  apply IsHausdorff.haus ‹IsHausdorff I R› (a - b)
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h n

end Lift

section Local

variable {O : Type*} [CommRing O] [IsLocalRing O]

variable (O) in
def oneUnits : Subgroup Oˣ where
  carrier := {u | (u : O) - 1 ∈ maximalIdeal O}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have := (maximalIdeal O).add_mem (Ideal.mul_mem_right (b : O) _ ha) hb
    simpa [sub_mul] using this
  inv_mem' {a} ha := by
    have := (maximalIdeal O).neg_mem (Ideal.mul_mem_right ((a⁻¹ : Oˣ) : O) _ ha)
    simpa [sub_mul] using this

def pt (u : oneUnits O) : maximalIdeal O := ⟨((u : Oˣ) : O) - 1, u.2⟩

@[simp] theorem coe_pt (u : oneUnits O) : (pt u : O) = ((u : Oˣ) : O) - 1 := rfl

end Local

section MuLam

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def mu (f : O⟦X⟧) : ℕ∞ := ⨅ n, IsDiscreteValuationRing.addVal O (coeff n f)

def lam (f : O⟦X⟧) : ℕ := sInf {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}

theorem mu_le (f : O⟦X⟧) (n : ℕ) : mu f ≤ IsDiscreteValuationRing.addVal O (coeff n f) := iInf_le _ n

theorem addVal_coeff_lam (f : O⟦X⟧) : IsDiscreteValuationRing.addVal O (coeff (lam f) f) = mu f := by
  have hne : {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}.Nonempty := by
    obtain ⟨n, hn⟩ := csInf_mem (Set.range_nonempty fun n => IsDiscreteValuationRing.addVal O (coeff n f))
    exact ⟨n, hn⟩
  exact Nat.sInf_mem hne

theorem mu_eq_top_iff {f : O⟦X⟧} : mu f = ⊤ ↔ f = 0 := by
  unfold mu
  rw [iInf_eq_top, PowerSeries.ext_iff]
  simp [IsDiscreteValuationRing.addVal_eq_top_iff]

end MuLam

section Char

variable {R : Type*} [CommRing R]

def coinvLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (QuotSMulTop g M)

def invLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (Submodule.torsionBy R M g)

end Char

end UpperTheory.V.abelian₂

end
