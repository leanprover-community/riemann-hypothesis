import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzStickDefs
import Development.DiscreteGroups.GlobalIrreducibility.DzStickDigits
import Development.DiscreteGroups.GlobalIrreducibility.DzDigDef
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

theorem associated_prime_pow {A : Type*} [CommRing A] [IsDomain A] {p : ℕ} (hp : p.Prime) {ζ : A}
    (hζ : IsPrimitiveRoot ζ p) : Associated (p : A) ((ζ - 1) ^ (p - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  symm
  rw [← Polynomial.eval_one_cyclotomic_prime (R := A) (p := p),
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.totient_prime hp, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem psi_apply (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra (ZMod p) k] {A : Type*}
    [CommRing A] (ζ : A) (hζ : ζ ^ p = 1) (x : k) :
    psi p k ζ hζ x = ζ ^ (Algebra.trace (ZMod p) k x).val := by
  simp [psi, AddChar.zmodChar_apply]

theorem psi_isPrimitive (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    {A : Type*} [CommRing A] [IsDomain A] (ζ : A) (hζ : IsPrimitiveRoot ζ p) :
    (psi p k ζ hζ.pow_eq_one).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod p) k 1
  refine AddChar.ne_one_iff.2 ⟨a, fun hf => ?_⟩
  rw [psi_apply, ha, ZMod.val_one, pow_one] at hf
  exact hζ.ne_one (Fact.out : p.Prime).one_lt hf

theorem psi_pow (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [Algebra (ZMod p) k]
    {A : Type*} [CommRing A] (ζ : A) (hζ : ζ ^ p = 1) (x : k) :
    psi p k ζ hζ (x ^ p) = psi p k ζ hζ x := by
  have : CharP k p := charP_of_injective_algebraMap' (ZMod p) p
  have : ExpChar k p := .prime Fact.out
  rw [psi_apply, psi_apply]
  have h := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquiv (ZMod p) k p) x
  have h2 : FiniteField.frobeniusAlgEquiv (ZMod p) k p x = x ^ p := by
    simp [FiniteField.frobeniusAlgEquiv_apply, ZMod.card]
  rw [h2] at h
  rw [h]

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

include D in

theorem p_mem : (p : A) ∈ Q.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← map_natCast D.ι,
    ← map_natCast (algebraMap (ZMod p) k), ZMod.natCast_self, map_zero, map_zero]

theorem ζ_sub_one_mem : D.ζ - 1 ∈ Q.asIdeal := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := (associated_prime_pow hp D.prim)
  have h : (D.ζ - 1) ^ (p - 1) ∈ Q.asIdeal := by
    rw [← hu]
    exact Ideal.mul_mem_right _ _ (p_mem D)
  exact Q.isPrime.mem_of_pow_mem _ h

theorem val_p : Q.intValuation (p : A) = Q.intValuation (D.ζ - 1) ^ (p - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := (associated_prime_pow hp D.prim)
  have h1 : Q.intValuation (u : A) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [← map_pow, ← hu, map_mul, h1, mul_one]

theorem val_ζ_sub_one_ne_zero : Q.intValuation (D.ζ - 1) ≠ 0 := by
  have hp : p.Prime := Fact.out
  exact Q.intValuation_ne_zero _ (sub_ne_zero.2 (D.prim.ne_one hp.one_lt))

theorem ω_pow_card : D.ω ^ (p ^ f - 1) = 1 := by
  classical
  rw [← D.card_eq, ← Fintype.card_units]
  exact D.ω.pow_card_eq_one

theorem ω_pow_ne_one {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) : D.ω ^ a ≠ 1 := by
  classical
  intro h
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf x = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units,
      D.card_eq]
  have h1 : (D.ω ^ a) (x : k) = 1 := by rw [h, MulChar.one_apply_coe]
  rw [MulChar.pow_apply_coe, ← map_pow] at h1
  have h2 : D.ι ((x : k) ^ a) = D.ι 1 := by
    rw [← D.mk_ω, h1, map_one, map_one]
  have h3 : (x : k) ^ a = 1 := D.ι.injective h2
  have h4 : x ^ a = 1 := by
    ext; simpa using h3
  have := Nat.le_of_dvd h0 (orderOf_dvd_of_pow_eq_one h4)
  omega

theorem g_zero : D.g 0 = -1 := by
  have hprim : D.ψ.IsPrimitive := psi_isPrimitive p k D.ζ D.prim
  have hne : D.ψ ≠ 1 := by
    have := hprim (a := 1) one_ne_zero
    rwa [AddChar.mulShift_one] at this
  unfold GSDatum.g
  rw [pow_zero, inv_one]
  exact gaussSum_one_left hne

end GSDatum

end DiscreteGroups.sglob.Stick
end
end

section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

theorem sum_inv_mul_trace (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Fintype k]
    [Algebra (ZMod p) k] :
    ∑ x : k, x⁻¹ * algebraMap (ZMod p) k (Algebra.trace (ZMod p) k x) = -1 := by
  classical
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := k), ZMod.card]
  have hn : 0 < Module.finrank (ZMod p) k := Module.finrank_pos
  simp_rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod, Finset.mul_sum]
  rw [Finset.sum_comm]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [hm, Finset.sum_range_succ']
  have h0 : ∑ x : k, x⁻¹ * x ^ p ^ 0 = -1 := by
    have h1 : ∀ x : k, x⁻¹ * x ^ p ^ 0 = 1 - if x = 0 then 1 else 0 := by
      intro x
      by_cases hx : x = 0 <;> simp [hx]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib]
    simp
  rw [h0, Finset.sum_eq_zero, zero_add]
  intro i hi
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpos : 1 < p ^ (i + 1) := Nat.one_lt_pow (by omega) hp1
  have h2 : ∀ x : k, x⁻¹ * x ^ p ^ (i + 1) = x ^ (p ^ (i + 1) - 1) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [inv_zero, zero_mul, zero_pow (by omega)]
    · rw [pow_sub₀ _ hx hpos.le, pow_one, mul_comm]
  simp_rw [h2]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hcard, hm, Nat.succ_eq_add_one]
  have h3 : p ^ (i + 1) < p ^ (m + 1) :=
    Nat.pow_lt_pow_right hp1 (by simpa using hi)
  omega

theorem exists_pow_eq_one_add {A : Type*} [CommRing A] (ζ : A) (n : ℕ) :
    ∃ r : A, ζ ^ n = 1 + n * (ζ - 1) + (ζ - 1) ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r * ζ + n, ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

theorem sum_inv_val_add_one_mem :
    (∑ x : k, (D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) + 1 ∈ Q.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_sum, map_one]
  have h : ∀ x : k, Ideal.Quotient.mk Q.asIdeal
      ((D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) =
      D.ι (x⁻¹ * algebraMap (ZMod p) k (Algebra.trace (ZMod p) k x)) := by
    intro x
    rw [map_mul, map_mul, MulChar.inv_apply', D.mk_ω, map_natCast]
    congr 1
    conv_rhs => rw [← ZMod.natCast_zmod_val (Algebra.trace (ZMod p) k x)]
    rw [map_natCast, map_natCast]
  simp_rw [h]
  rw [← map_sum, sum_inv_mul_trace, map_neg, map_one, neg_add_cancel]

theorem exists_g_one_eq (h : 1 < p ^ f - 1) :
    ∃ y ∈ Q.asIdeal, D.g 1 = (D.ζ - 1) * (-1 + y) := by
  choose r hr using fun x : k => exists_pow_eq_one_add D.ζ (Algebra.trace (ZMod p) k x).val
  have hne : D.ω⁻¹ ≠ 1 := by
    intro h1
    apply D.ω_pow_ne_one one_pos h
    rw [pow_one]
    exact inv_eq_one.mp h1
  have hs : ∑ x : k, (D.ω⁻¹) x = 0 := MulChar.sum_eq_zero_of_ne_one hne
  refine ⟨((∑ x : k, (D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) + 1) +
    (D.ζ - 1) * ∑ x : k, (D.ω⁻¹) x * r x, ?_, ?_⟩
  · exact Q.asIdeal.add_mem D.sum_inv_val_add_one_mem
      (Q.asIdeal.mul_mem_right _ D.ζ_sub_one_mem)
  · have hg : D.g 1 = ∑ x : k, ((D.ω⁻¹) x +
        (D.ζ - 1) * ((D.ω⁻¹) x * ((Algebra.trace (ZMod p) k x).val : A)) +
        (D.ζ - 1) * ((D.ζ - 1) * ((D.ω⁻¹) x * r x))) := by
      unfold GSDatum.g gaussSum
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_one]
      change _ * psi p k D.ζ D.prim.pow_eq_one x = _
      rw [psi_apply, hr x]
      ring
    rw [hg, Finset.sum_add_distrib, Finset.sum_add_distrib, hs, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring

theorem val_g_one (h : 1 < p ^ f - 1) : Q.intValuation (D.g 1) = Q.intValuation (D.ζ - 1) := by
  obtain ⟨y, hy, hg⟩ := D.exists_g_one_eq h
  have hn : -1 + y ∉ Q.asIdeal := by
    intro hm
    have h1 : (1 : A) ∈ Q.asIdeal := by
      have := Q.asIdeal.sub_mem hy hm
      simpa using this
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rw [hg, map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr hn, mul_one]

end GSDatum

end DiscreteGroups.sglob.Stick
end
end

section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

theorem val_mul_le {χ₁ χ₂ : MulChar k A} (h : χ₁ * χ₂ ≠ 1) :
    Q.intValuation (gaussSum χ₁ D.ψ) * Q.intValuation (gaussSum χ₂ D.ψ) ≤
      Q.intValuation (gaussSum (χ₁ * χ₂) D.ψ) := by
  rw [← map_mul, ← jacobiSum_mul_nontrivial h D.ψ, map_mul]
  exact mul_le_of_le_one_right' (Q.intValuation_le_one _)

theorem gaussSum_pow_p (χ : MulChar k A) : gaussSum (χ ^ p) D.ψ = gaussSum χ D.ψ := by
  have : CharP k p := (Algebra.charP_iff (ZMod p) k p).1 inferInstance
  unfold gaussSum
  refine Fintype.sum_bijective (fun x : k => x ^ p) (frobeniusEquiv k p).bijective _ _ ?_
  intro x
  rw [MulChar.pow_apply' χ (Fact.out : p.Prime).ne_zero, map_pow]
  congr 1
  exact (psi_pow p k D.ζ D.prim.pow_eq_one x).symm

theorem ω_pow_add_inv (a b : ℕ) : (D.ω ^ (a + b))⁻¹ = (D.ω ^ a)⁻¹ * (D.ω ^ b)⁻¹ := by
  rw [pow_add, mul_inv]

theorem ω_pow_inv_ne_one {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) : (D.ω ^ a)⁻¹ ≠ 1 := by
  rw [Ne, inv_eq_one]
  exact D.ω_pow_ne_one h0 ha

theorem pow_le_val_g_small {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.ζ - 1) ^ a ≤ Q.intValuation (D.g a) := by
  induction a with
  | zero => rw [D.g_zero, pow_zero, Valuation.map_neg, map_one]
  | succ a ih =>
    have h1 : 1 < p ^ f - 1 := by omega
    have hne : (D.ω ^ a)⁻¹ * (D.ω ^ 1)⁻¹ ≠ 1 := by
      rw [← D.ω_pow_add_inv]
      exact D.ω_pow_inv_ne_one (Nat.succ_pos a) ha
    have h2 := D.val_mul_le hne
    rw [← D.ω_pow_add_inv] at h2
    have h3 : Q.intValuation (D.g a) * Q.intValuation (D.g 1) ≤ Q.intValuation (D.g (a + 1)) := h2
    rw [D.val_g_one h1] at h3
    rw [pow_succ]
    exact le_trans (mul_le_mul_left (ih (by omega)) _) h3

theorem pow_dsum_le_val_g {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.ζ - 1) ^ dsum p a ≤ Q.intValuation (D.g a) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | h0
    · rw [dsum_of_lt hp (by omega)]
      exact D.pow_le_val_g_small ha
    · have hdiv : a / p < a := Nat.div_lt_self h0 hp
      have hmod : a % p ≤ a := Nat.mod_le a p
      have hdec : (D.ω ^ a)⁻¹ = (D.ω ^ (a % p))⁻¹ * ((D.ω ^ (a / p))⁻¹) ^ p := by
        rw [inv_pow, ← pow_mul, ← D.ω_pow_add_inv, mul_comm (a / p) p, Nat.mod_add_div]
      have hne : (D.ω ^ (a % p))⁻¹ * ((D.ω ^ (a / p))⁻¹) ^ p ≠ 1 := by
        rw [← hdec]
        exact D.ω_pow_inv_ne_one h0 ha
      have h2 := D.val_mul_le hne
      rw [← hdec, D.gaussSum_pow_p] at h2
      have h3 : Q.intValuation (D.g (a % p)) * Q.intValuation (D.g (a / p)) ≤
          Q.intValuation (D.g a) := h2
      rw [dsum_rec hp a, pow_add]
      exact le_trans (mul_le_mul' (D.pow_le_val_g_small (by omega)) (ih _ hdiv (by omega))) h3

theorem val_neg_one (χ : MulChar k A) : Q.intValuation (χ (-1)) = 1 := by
  have h : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have h1 : Q.intValuation (χ (-1)) * Q.intValuation (χ (-1)) = 1 := by
    rw [← map_mul, h, map_one]
  refine le_antisymm (Q.intValuation_le_one _) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Q.intValuation (χ (-1)) * Q.intValuation (χ (-1)) := h1.symm
    _ ≤ Q.intValuation (χ (-1)) := mul_le_of_le_one_right' (Q.intValuation_le_one _)

theorem val_g_mul_val_g_compl {a : ℕ} (h0 : 0 < a) (ha : a < p ^ f - 1) :
    Q.intValuation (D.g a) * Q.intValuation (D.g (p ^ f - 1 - a)) =
      Q.intValuation (D.ζ - 1) ^ (f * (p - 1)) := by
  have hprim : D.ψ.IsPrimitive := psi_isPrimitive p k D.ζ D.prim
  have hne := D.ω_pow_inv_ne_one h0 ha
  have hinv : (D.ω ^ (p ^ f - 1 - a))⁻¹ = ((D.ω ^ a)⁻¹)⁻¹ := by
    rw [inv_inv, inv_eq_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel ha.le, D.ω_pow_card]
  have hcard := gaussSum_mul_gaussSum_eq_card hne hprim
  have hshift := gaussSum_mulShift ((D.ω ^ a)⁻¹)⁻¹ D.ψ (-1 : kˣ)
  have hψ : AddChar.mulShift D.ψ ((-1 : kˣ) : k) = D.ψ⁻¹ := by
    rw [AddChar.inv_mulShift]; simp
  rw [hψ] at hshift
  have hv : Q.intValuation (gaussSum ((D.ω ^ a)⁻¹)⁻¹ D.ψ⁻¹) =
      Q.intValuation (gaussSum ((D.ω ^ a)⁻¹)⁻¹ D.ψ) := by
    rw [← hshift, map_mul]
    have : (((-1 : kˣ) : k)) = -1 := by simp
    rw [this, val_neg_one, one_mul]
  unfold g
  rw [hinv, ← hv, ← map_mul, hcard, D.card_eq, Nat.cast_pow, map_pow, D.val_p, ← pow_mul,
    mul_comm f]

end GSDatum

end DiscreteGroups.sglob.Stick
end
end

section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

theorem val_g {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.g a) = Q.intValuation (D.ζ - 1) ^ dsum p a := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases Nat.eq_zero_or_pos a with rfl | h0
  · rw [D.g_zero, dsum_of_lt hp2 (by omega)]; simp
  have hb : p ^ f - 1 - a < p ^ f - 1 := by omega
  have h1 := D.pow_dsum_le_val_g ha
  have h2 := D.pow_dsum_le_val_g hb
  have h3 := D.val_g_mul_val_g_compl h0 ha
  have h4 := dsum_compl hp2 f a ha.le
  have hπ := D.val_ζ_sub_one_ne_zero
  rw [← h4, pow_add] at h3
  refine le_antisymm ?_ h1
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a) :=
    zero_lt_iff.2 (pow_ne_zero _ hπ)
  have : Q.intValuation (D.ζ - 1) ^ dsum p a * Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a) <
      Q.intValuation (D.g a) * Q.intValuation (D.g (p ^ f - 1 - a)) :=
    mul_lt_mul hlt h2 hpos zero_le
  exact absurd h3 this.ne'

end GSDatum

end DiscreteGroups.sglob.Stick
end
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] {x : M} {N a b : ℕ} (h : x ^ N = 1)
    (hab : a ≡ b [MOD N]) : x ^ a = x ^ b := by
  have e1 : ∀ c : ℕ, x ^ c = x ^ (c % N) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c N, pow_add, pow_mul, h, one_pow, mul_one]
  rw [e1 a, e1 b, show a % N = b % N from hab]

theorem modEq_twist {N t u k b e : ℕ} (htu : t * u ≡ 1 [MOD N]) :
    t * ((u * k + b * e) % N) ≡ k + e * (t * b) [MOD N] := by
  have h1 : t * ((u * k + b * e) % N) ≡ t * (u * k + b * e) [MOD N] :=
    (Nat.mod_modEq _ _).mul_left t
  have h2 : t * (u * k + b * e) = t * u * k + e * (t * b) := by ring
  have h3 : t * u * k + e * (t * b) ≡ 1 * k + e * (t * b) [MOD N] :=
    (htu.mul_right k).add_right _
  rw [one_mul] at h3
  rw [h2] at h1
  exact h1.trans h3

theorem modEq_twist0 {N t u k : ℕ} (htu : t * u ≡ 1 [MOD N]) : t * (u * k % N) ≡ k [MOD N] := by
  have h := modEq_twist (b := 0) (e := 0) (k := k) htu
  simpa using h

theorem exists_eq_pow_of_injective {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (Ω θ : G →* ℂˣ) (hΩ : Function.Injective Ω) : ∃ k : ℕ, θ = Ω ^ k := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf γ = Fintype.card G :=
    (orderOf_eq_card_of_forall_mem_zpowers hγ).trans Nat.card_eq_fintype_card
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have h1 : IsPrimitiveRoot γ (Fintype.card G) := hord ▸ IsPrimitiveRoot.orderOf γ
  have hprim : IsPrimitiveRoot ((Ω γ : ℂˣ) : ℂ) (Fintype.card G) :=
    (h1.map_of_injective hΩ).map_of_injective (f := Units.coeHom ℂ) Units.val_injective
  have hθ : ((θ γ : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hθ
  refine ⟨k, MonoidHom.ext fun z => Units.ext ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, γ ^ j = z := by
    have hz := hγ z
    rw [← mem_powers_iff_mem_zpowers] at hz
    exact hz
  rw [MonoidHom.pow_apply, map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, ← hk, ← pow_mul, ← pow_mul, mul_comm]

theorem dsum_eq_of_pow_eq {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k]
    [Algebra (ZMod p) k] {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
    (D : Stick.GSDatum p f k A Q) {a₁ a₂ a₃ a₄ r : ℕ} (h₁ : a₁ < p ^ f - 1) (h₂ : a₂ < p ^ f - 1)
    (h₃ : a₃ < p ^ f - 1) (h₄ : a₄ < p ^ f - 1) (hr : 0 < r)
    (h : (D.g a₁ * D.g a₂) ^ r = (D.g a₃ * D.g a₄) ^ r) :
    Stick.dsum p a₁ + Stick.dsum p a₂ = Stick.dsum p a₃ + Stick.dsum p a₄ := by
  have hv := congrArg Q.intValuation h
  simp only [map_pow, map_mul, D.val_g h₁, D.val_g h₂, D.val_g h₃, D.val_g h₄, ← pow_add,
    ← pow_mul] at hv
  have h0 : 0 < Q.intValuation (D.ζ - 1) := zero_lt_iff.2 D.val_ζ_sub_one_ne_zero
  have h1 : Q.intValuation (D.ζ - 1) < 1 := (Q.intValuation_lt_one_iff_mem _).2 D.ζ_sub_one_mem
  have := (pow_right_strictAnti₀ h0 h1).injective hv
  exact Nat.eq_of_mul_eq_mul_right hr this

theorem addChar_apply_eq_pow {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) (y : ZMod g) :
    ((ψ₀ y : Circle) : ℂ) = ((ψ₀ 1 : Circle) : ℂ) ^ y.val := by
  have h : y = y.val • (1 : ZMod g) := by rw [nsmul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [h, AddChar.map_nsmul_eq_pow]
  rw [Circle.coe_pow]

theorem sum_units_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] (F : K → ℂ) (hF : F 0 = 0) :
    ∑ u : Kˣ, F u = ∑ x : K, F x := by
  rw [← Finset.sum_erase Finset.univ hF,
    Finset.sum_subtype (Finset.univ.erase (0 : K)) (p := fun x => x ≠ 0) (by simp) F]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

theorem gs_eq {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type*} [Field K]
    [Fintype K] [Algebra (ZMod g) K] {A : Type*} [CommRing A] (Φ : A →+* ℂ) (ω : MulChar K A)
    (ζ : A) (hζ : ζ ^ g = 1) (hΦζ : Φ ζ = ((ψ₀ 1 : Circle) : ℂ)) (η : Kˣ →* ℂˣ) (a : ℕ)
    (hη : ∀ z : Kˣ, ((η z : ℂˣ) : ℂ) = Φ (ω z) ^ a) :
    (∑ᶠ z : Kˣ, (((η⁻¹) z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ)) =
      Φ (gaussSum (ω ^ a)⁻¹ (Stick.psi g K ζ hζ)) := by
  classical
  rw [finsum_eq_sum_of_fintype, gaussSum, map_sum]
  rw [← sum_units_eq (fun x => Φ ((ω ^ a)⁻¹ x * Stick.psi g K ζ hζ x))
    (by rw [MulChar.map_zero, zero_mul, map_zero])]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, Stick.psi_apply, map_pow, hΦζ, ← addChar_apply_eq_pow, MulChar.inv_apply',
    ← Units.val_inv_eq_inv_val, MulChar.pow_apply_coe, map_pow, ← hη, MonoidHom.inv_apply,
    ← map_inv]

end DiscreteGroups.sglob.DzPin
end
end

section
noncomputable section

namespace DiscreteGroups.sglob.Stick

open NumberField IsDedekindDomain nonZeroDivisors

universe u

theorem eq_of_pow_eq_one_of_mk_eq {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) {n : ℕ}
    (hn : (n : A) ∉ P) {a b : A} (ha : a ^ n = 1) (hb : b ^ n = 1)
    (h : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  by_contra hab
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h1 : (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) = 0 := by
    rw [(Commute.all a b).geom_sum₂_mul, ha, hb, sub_self]
  have h2 : ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i) = 0 :=
    (mul_eq_zero.mp h1).resolve_right hsub
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have h3 : (n : A ⧸ P) * Ideal.Quotient.mk P b ^ (n - 1) = 0 := by
    have := congrArg (Ideal.Quotient.mk P) h2
    rw [map_sum, map_zero] at this
    rw [← this]
    have : ∀ i ∈ Finset.range n, Ideal.Quotient.mk P (a ^ i * b ^ (n - 1 - i)) =
        Ideal.Quotient.mk P b ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, h, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 : (n : A ⧸ P) = 0 := by
    have h5 : Ideal.Quotient.mk P b ^ (n - 1) * Ideal.Quotient.mk P b = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← map_pow, hb, map_one]
    calc (n : A ⧸ P) = (n : A ⧸ P) * (Ideal.Quotient.mk P b ^ (n - 1) * Ideal.Quotient.mk P b) := by
          rw [h5, mul_one]
      _ = 0 := by rw [← mul_assoc, h3, zero_mul]
  apply hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, h4]

theorem natCast_not_mem_of_dvd {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] {k : Type*}
    [Field k] [Fintype k] (ι : k →+* A ⧸ P) {n : ℕ} (hn : n ∣ Fintype.card k - 1) :
    (n : A) ∉ P := by
  intro hmem
  have h0 : (n : A ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨m, hm⟩ := hn
  have hq : ((Fintype.card k : ℕ) : A ⧸ P) = 0 := by
    rw [← map_natCast ι, Nat.cast_card_eq_zero, map_zero]
  have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
  have h1 : ((Fintype.card k - 1 : ℕ) : A ⧸ P) = 0 := by
    rw [hm, Nat.cast_mul, h0, zero_mul]
  have h2 : ((Fintype.card k - 1 + 1 : ℕ) : A ⧸ P) = 1 := by
    rw [Nat.cast_add, h1, Nat.cast_one, zero_add]
  rw [Nat.sub_add_cancel hpos, hq] at h2
  exact zero_ne_one h2

theorem isPrimitiveRoot_mk {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) {n : ℕ}
    (hn : (n : A) ∉ P) {μ : A} (hμ : IsPrimitiveRoot μ n) :
    IsPrimitiveRoot (Ideal.Quotient.mk P μ) n := by
  refine ⟨by rw [← map_pow, hμ.pow_eq_one, map_one], fun l hl => ?_⟩
  apply hμ.dvd_of_pow_eq_one
  refine eq_of_pow_eq_one_of_mk_eq P hn ?_ (one_pow n) (by rw [map_pow, hl, map_one])
  rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

theorem exists_powResChar {A : Type*} [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime]
    {k : Type*} [Field k] [Fintype k] (ι : k →+* A ⧸ P) {n : ℕ} (hn : n ∣ Fintype.card k - 1)
    {μ : A} (hμ : IsPrimitiveRoot μ n) :
    ∃ ρ : MulChar k A,
      (∀ x, Ideal.Quotient.mk P (ρ x) = ι x ^ ((Fintype.card k - 1) / n)) ∧ ρ ^ n = 1 := by
  classical
  have hnP : (n : A) ∉ P := natCast_not_mem_of_dvd P ι hn
  have hq1 : 0 < Fintype.card k - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hn
    omega
  have : NeZero n := ⟨hn0⟩
  set m := (Fintype.card k - 1) / n with hm
  have hmn : m * n = Fintype.card k - 1 := Nat.div_mul_cancel hn
  have hm0 : m ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hmn
    omega
  have hprim := isPrimitiveRoot_mk P hnP hμ
  have hex : ∀ x : kˣ, ∃ y : A, y ^ n = 1 ∧ Ideal.Quotient.mk P y = ι (x : k) ^ m := by
    intro x
    have hx : (ι (x : k) ^ m) ^ n = 1 := by
      rw [← pow_mul, hmn, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ x.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hx
    refine ⟨μ ^ i, ?_, by rw [map_pow, hi]⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  choose φ hφ1 hφ2 using hex
  let Φ : kˣ →* A :=
    { toFun := φ
      map_one' := by
        refine eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 1) (one_pow n) ?_
        rw [hφ2, Units.val_one, map_one, one_pow, map_one]
      map_mul' := by
        intro x y
        refine eq_of_pow_eq_one_of_mk_eq P hnP (hφ1 _) ?_ ?_
        · rw [mul_pow, hφ1, hφ1, one_mul]
        · rw [hφ2, map_mul, hφ2, hφ2, Units.val_mul, map_mul, mul_pow] }
  refine ⟨MulChar.ofUnitHom Φ.toHomUnits, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero, map_zero, map_zero, zero_pow hm0]
    · obtain ⟨u, rfl⟩ := (isUnit_iff_ne_zero.mpr hx)
      rw [MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
      exact hφ2 u
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits,
      MulChar.one_apply_coe]
    exact hφ1 u

end DiscreteGroups.sglob.Stick
end
end

section
noncomputable section

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem exists_maximal_above (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime] :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 L)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) _ hker
  refine ⟨Q, hQ, ?_⟩
  have h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 L)) Q := hQc ▸ Ideal.subset_span rfl
  simpa using h

theorem exists_iota (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime]
    (Q : Ideal (𝓞 L)) [hQ : Q.IsMaximal] (hpQ : (p : 𝓞 L) ∈ Q) {N : ℕ} {μ : 𝓞 L}
    (hμ : IsPrimitiveRoot μ N) (hNQ : (N : 𝓞 L) ∉ Q) (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod p) K] (hK : Fintype.card K = N + 1) : Nonempty (K →+* 𝓞 L ⧸ Q) := by
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have hpz : ((p : ℕ) : 𝓞 L ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact hpQ
  haveI : CharP (𝓞 L ⧸ Q) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpz)
  letI : Algebra (ZMod p) (𝓞 L ⧸ Q) := ZMod.algebra _ p
  haveI := FiniteField.isSplittingField_sub K (ZMod p)
  have hμ' : IsPrimitiveRoot (Ideal.Quotient.mk Q μ) N := Stick.isPrimitiveRoot_mk Q hNQ hμ
  have hs : (map (algebraMap (ZMod p) (𝓞 L ⧸ Q)) (X ^ Fintype.card K - X)).Splits := by
    have e : (X ^ Fintype.card K - X : (𝓞 L ⧸ Q)[X]) = X * (X ^ N - C 1) := by
      rw [hK, C_1]; ring
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, e]
    exact Splits.X.mul (X_pow_sub_one_splits hμ')
  exact ⟨(IsSplittingField.lift K (X ^ Fintype.card K - X) hs).toRingHom⟩

theorem exists_emb (m : ℕ) [NeZero m] (L : Type) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (c : ℂ)
    (hc : IsPrimitiveRoot c m) : ∃ φ : L →+* ℂ, φ ζ = c := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)
  let x : primitiveRoots m ℂ := ⟨c, (mem_primitiveRoots (NeZero.pos m)).2 hc⟩
  refine ⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩
  have h := congrArg Subtype.val ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).apply_symm_apply x)
  rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] at h
  exact h

theorem exists_setup (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K]
    [Fintype K] [Algebra (ZMod p) K] (hK : Fintype.card K = p ^ n) (ψ₀ : AddChar (ZMod p) Circle)
    (hψ₀ : ψ₀ ≠ 1) :
    ∃ (Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ)))
      (ω : MulChar K (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ))) (Ω : Kˣ →* ℂˣ),
      Function.Injective Ω ∧
      ∀ t : ℕ, t.Coprime (p * (p ^ n - 1)) →
        ∃ (Φ : 𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ) →+* ℂ) (D : Stick.GSDatum p n K _ Q),
          Function.Injective Φ ∧ D.ω = ω ∧ Φ D.ζ = ((ψ₀ 1 : Circle) : ℂ) ∧
          ∀ z : Kˣ, Φ (ω z) = ((Ω z : ℂˣ) : ℂ) ^ t := by
  classical
  have hp2 := hp.out.two_le
  have hpn : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  set N := p ^ n - 1 with hNdef
  have hN1 : N + 1 = p ^ n := by omega
  have hN0 : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.out.ne_zero (by omega)⟩
  haveI : NeZero (((p * N : ℕ)) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  haveI : IsCyclotomicExtension {p * N} ℚ (CyclotomicField (p * N) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (p * N) ℚ
    all_goals rfl
  have hζL := IsCyclotomicExtension.zeta_spec (p * N) ℚ (CyclotomicField (p * N) ℚ)
  let z : 𝓞 (CyclotomicField (p * N) ℚ) := hζL.toInteger
  have hzL : algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ) z = IsCyclotomicExtension.zeta (p * N) ℚ (CyclotomicField (p * N) ℚ) := rfl
  have hz : IsPrimitiveRoot z (p * N) := hζL.toInteger_isPrimitiveRoot
  have hμ : IsPrimitiveRoot (z ^ p) N := hz.pow (NeZero.pos _) rfl
  obtain ⟨Q0, hQmax, hpQ⟩ := exists_maximal_above (CyclotomicField (p * N) ℚ) p
  have hNQ : (N : 𝓞 (CyclotomicField (p * N) ℚ)) ∉ Q0 := by
    intro h
    have h1 : (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n ∈ Q0 := Ideal.pow_mem_of_mem _ hpQ n (by omega)
    have h2 : (1 : 𝓞 (CyclotomicField (p * N) ℚ)) = (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n - N := by
      have e : ((N + 1 : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) = ((p ^ n : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) := by rw [hN1]
      push_cast at e
      rw [← e]; ring
    exact hQmax.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ Q0.sub_mem h1 h))
  obtain ⟨ι⟩ := exists_iota (CyclotomicField (p * N) ℚ) p Q0 hpQ hμ hNQ K (by omega)
  have hne : Q0 ≠ ⊥ := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) ((Submodule.mem_bot _).1 hpQ)
  let Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * N) ℚ)) := ⟨Q0, hQmax.isPrime, hne⟩
  obtain ⟨ω, hω1, hωN⟩ := Stick.exists_powResChar Q0 ι (n := N) (by rw [hK]) hμ
  have hdiv : (Fintype.card K - 1) / N = 1 := by rw [hK, ← hNdef, Nat.div_self hN0]
  have mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x := by
    intro x
    have h := hω1 x
    rw [hdiv, pow_one] at h
    exact h
  have hωu : ∀ y : Kˣ, ω y ^ N = 1 := by
    intro y; rw [← MulChar.pow_apply_coe, hωN, MulChar.one_apply_coe]

  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))
  have hc : IsPrimitiveRoot c (p * N) := Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  have hemb : ∀ t : ℕ, t.Coprime (p * N) →
      ∃ Φ : 𝓞 (CyclotomicField (p * N) ℚ) →+* ℂ, Function.Injective Φ ∧ Φ z = c ^ t := by
    intro t ht
    obtain ⟨φ, hφ⟩ := exists_emb (p * N) (CyclotomicField (p * N) ℚ) hζL (c ^ t) (hc.pow_of_coprime t ht)
    exact ⟨φ.comp (algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), φ.injective.comp (IsFractionRing.injective (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)),
      by rw [RingHom.comp_apply, hzL, hφ]⟩
  obtain ⟨Φ1, hΦ1i, hΦ1z⟩ := hemb 1 (Nat.coprime_one_left _)

  let Ω : Kˣ →* ℂˣ := (Units.map Φ1.toMonoidHom).comp ω.toUnitHom
  have hΩ : ∀ y : Kˣ, ((Ω y : ℂˣ) : ℂ) = Φ1 (ω y) := fun y => rfl
  refine ⟨Q, ω, Ω, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : Φ1 (ω y₁) = Φ1 (ω y₂) := by rw [← hΩ, ← hΩ, h]
    have h2 := congrArg (Ideal.Quotient.mk Q.asIdeal) (hΦ1i h1)
    rw [mk_ω, mk_ω] at h2
    exact Units.ext (ι.injective h2)
  · intro t ht
    obtain ⟨Φ, hΦi, hΦz⟩ := hemb t ht

    have hpow : ∀ x : 𝓞 (CyclotomicField (p * N) ℚ), x ^ N = 1 → Φ x = Φ1 x ^ t := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hx
      simp only [map_pow, hΦz, hΦ1z, pow_one]
      ring

    have hw : IsPrimitiveRoot ((ψ₀ 1 : Circle) : ℂ) p := by
      have h1 : ((ψ₀ 1 : Circle) : ℂ) ^ p = 1 := by
        rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self,
          AddChar.map_zero_eq_one, Circle.coe_one]
      have h2 : ((ψ₀ 1 : Circle) : ℂ) ≠ 1 := by
        intro h
        apply hψ₀
        refine AddChar.ext_iff.2 fun y => Circle.coe_injective ?_
        rw [addChar_apply_eq_pow, h, one_pow, AddChar.one_apply, Circle.coe_one]
      have h3 := IsPrimitiveRoot.orderOf ((ψ₀ 1 : Circle) : ℂ)
      rwa [orderOf_eq_prime h1 h2] at h3
    have hzN : IsPrimitiveRoot (Φ (z ^ N)) p := by
      rw [map_pow, hΦz]
      exact (hc.pow_of_coprime t ht).pow (NeZero.pos _) (by ring)
    obtain ⟨j, -, hj⟩ := hzN.eq_pow_of_pow_eq_one hw.pow_eq_one
    have hΦζ : Φ ((z ^ N) ^ j) = ((ψ₀ 1 : Circle) : ℂ) := by rw [map_pow, hj]
    have hprim : IsPrimitiveRoot ((z ^ N) ^ j) p :=
      IsPrimitiveRoot.of_map_of_injective (f := Φ) (by rw [hΦζ]; exact hw) hΦi
    let D : Stick.GSDatum p n K (𝓞 (CyclotomicField (p * N) ℚ)) Q :=
      { card_eq := hK, ι := ι, ω := ω, mk_ω := mk_ω, ζ := (z ^ N) ^ j, prim := hprim }
    refine ⟨Φ, D, hΦi, rfl, hΦζ, fun y => ?_⟩
    rw [hpow _ (hωu y), hΩ]

theorem nm_eq {g : ℕ} [hg : Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod g) K] (hK : Fintype.card K = g ^ n) (Ω : Kˣ →* ℂˣ) (m : ℕ) :
    ((Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ m).comp
        (Units.map (Algebra.norm (ZMod g) : K →* ZMod g)) = Ω ^ ((g ^ n - 1) / (g - 1) * m) := by
  have hg2 := hg.out.two_le
  have hfin : Module.finrank (ZMod g) K = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hK] at h
    exact (Nat.pow_right_injective hg2 h).symm
  refine MonoidHom.ext fun z => ?_
  have hz : Units.map (algebraMap (ZMod g) K).toMonoidHom
      (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z) = z ^ ((g ^ n - 1) / (g - 1)) := by
    refine Units.ext ?_
    simp only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    rw [FiniteField.algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum, Nat.card_zmod, hfin,
      Nat.geomSum_eq hg2]
  rw [MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hz, map_pow, ← pow_mul,
    MonoidHom.pow_apply]

end DiscreteGroups.sglob.DzPin
end
end

section
noncomputable section

set_option linter.style.haveILetI false

namespace DiscreteGroups.sglob.DzType

open NumberField IsDedekindDomain

theorem lPin_of_dig (hD : Dig) : LPin := by
  intro g _ n hn2 hbig K _ _ hcard ψ₀ hψ₀ θ ξ hθ hξ hH
  classical
  have hgp : g.Prime := Fact.out
  have hg2 := hgp.two_le
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have hg2n : g ^ 2 ≤ g ^ n := Nat.pow_le_pow_right (by omega) hn2
  have hg4 : 4 ≤ g ^ 2 := by nlinarith
  set N := g ^ n - 1 with hNdef
  have hN1 : N + 1 = g ^ n := by omega
  have hN0 : 0 < N := by omega
  have hN1lt : 1 < N := by omega
  obtain ⟨Q, ω, Ω, hΩi, hdat⟩ := DzPin.exists_setup g n (by omega) K hK ψ₀ hψ₀
  obtain ⟨k, hk⟩ := DzPin.exists_eq_pow_of_injective Ω θ hΩi
  obtain ⟨k', hk'⟩ := DzPin.exists_eq_pow_of_injective Ω ξ hΩi
  have hΩN : Ω ^ N = 1 := by
    refine MonoidHom.ext fun z => ?_
    have hz : z ^ N = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, hNdef, ← hK]
      exact FiniteField.pow_card_sub_one_eq_one _ z.ne_zero)
    rw [MonoidHom.pow_apply, ← map_pow, hz, map_one, MonoidHom.one_apply]
  have hreg : ∀ {η : Kˣ →* ℂˣ} {m : ℕ}, η = Ω ^ m → GlobalTheory.Published.IsRegularChar g n η →
      ∀ i j, i < n → j < n → m * g ^ i ≡ m * g ^ j [MOD g ^ n - 1] → i = j := by
    intro η m hηm hr i j hi hj hm
    refine hr i j hi hj ?_
    rw [hηm, ← pow_mul, ← pow_mul]
    exact DzPin.pow_eq_pow_of_modEq hΩN hm
  have hmain : ∀ u b : ℕ, u.Coprime (g ^ n - 1) →
      (Nat.digits g ((u * k + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k' % (g ^ n - 1))).sum =
        (Nat.digits g ((u * k' + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k % (g ^ n - 1))).sum := by
    intro u b hu
    haveI : NeZero N := ⟨by omega⟩
    set t0 := ((ZMod.unitOfCoprime u hu)⁻¹ : (ZMod N)ˣ).val.val with ht0def
    have h0 : u * t0 ≡ 1 [MOD N] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [ht0def, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime u hu, Units.mul_inv]
    set t := t0 + N * (t0 + 1) with htdef
    have htu : t * u ≡ 1 [MOD N] := by
      have e : t * u = u * t0 + N * ((t0 + 1) * u) := by rw [htdef]; ring
      unfold Nat.ModEq
      rw [e, Nat.add_mul_mod_self_left]
      exact h0
    have htN : t.Coprime N := Nat.coprime_of_mul_modEq_one u htu
    have htg : t.Coprime g := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
      intro hdt
      have h1 : g ∣ t + 1 := by
        have e : t + 1 = g ^ n * (t0 + 1) := by rw [← hN1, htdef]; ring
        rw [e]
        exact Dvd.dvd.mul_right (dvd_pow_self g (by omega)) _
      have h2 : g ∣ 1 := (Nat.dvd_add_right hdt).mp h1
      exact hgp.one_lt.ne' (Nat.dvd_one.mp h2)
    obtain ⟨Φ, D, hΦi, hDω, hΦζ, hΦω⟩ := hdat t (Nat.Coprime.mul_right htg htN)
    have hG : ∀ (η : Kˣ →* ℂˣ) (a : ℕ), η = Ω ^ (t * a) → gs ψ₀ η⁻¹ = Φ (D.g a) := by
      intro η a hη
      exact DzPin.gs_eq ψ₀ Φ D.ω D.ζ D.prim.pow_eq_one hΦζ η a (fun z => by
        rw [hη, hDω, hΦω, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, pow_mul])
    set e := (g ^ n - 1) / (g - 1) with hedef
    let χ₀ : (ZMod g)ˣ →* ℂˣ := (Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ (t * b)
    have hnm : nmChar K χ₀ = Ω ^ (e * (t * b)) := DzPin.nm_eq hK Ω (t * b)
    obtain ⟨r, hr, hrr⟩ := hH χ₀
    have h1 : θ * nmChar K χ₀ = Ω ^ (t * ((u * k + b * e) % N)) := by
      rw [hnm, hk, ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h2 : ξ = Ω ^ (t * (u * k' % N)) := by
      rw [hk']
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    have h3 : ξ * nmChar K χ₀ = Ω ^ (t * ((u * k' + b * e) % N)) := by
      rw [hnm, hk', ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h4 : θ = Ω ^ (t * (u * k % N)) := by
      rw [hk]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    rw [hG _ _ h1, hG _ _ h2, hG _ _ h3, hG _ _ h4, ← map_mul, ← map_mul, ← map_pow,
      ← map_pow] at hrr
    exact DzPin.dsum_eq_of_pow_eq D (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0)
      (Nat.mod_lt _ hN0) hr (hΦi hrr)
  obtain ⟨i, hi⟩ := hD g n hgp hn2 hbig k k' (hreg hk hθ) (hreg hk' hξ) hmain
  refine ⟨i, fun z => ?_⟩
  rw [hk', hk, DzPin.pow_eq_pow_of_modEq hΩN hi, MonoidHom.pow_apply, MonoidHom.pow_apply, map_pow,
    ← pow_mul, mul_comm]

end DiscreteGroups.sglob.DzType
end
end
