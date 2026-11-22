module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination

@[expose] public section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.ResDisj

variable {p : ℕ} [hp : Fact p.Prime]

theorem const_of_pow_eq {f : ℕ} (hf : f ≠ 0) (a : LaurentSeries (ZMod p)) (ha : a ^ p ^ f = a) :
    a = HahnSeries.C (a.coeff 0) := by
  haveI : CharP (LaurentSeries (ZMod p)) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p))]; simp)
  by_contra hne
  have hb : a - HahnSeries.C (a.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have hpow : (a - HahnSeries.C (a.coeff 0)) ^ p ^ f = a - HahnSeries.C (a.coeff 0) := by
    rw [sub_pow_char_pow, ha, ← map_pow, ZMod.pow_card_pow]
  have h0 : (a - HahnSeries.C (a.coeff 0)).coeff 0 = 0 := by simp
  generalize a - HahnSeries.C (a.coeff 0) = b at hb hpow h0
  have ho := HahnSeries.order_pow b (p ^ f)
  rw [hpow, nsmul_eq_mul] at ho
  have h1 : (1 : ℤ) < ((p ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_lt_pow hf hp.out.one_lt
  have h2 : b.order = 0 := by
    have : (((p ^ f : ℕ) : ℤ) - 1) * b.order = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact h
  exact hb (HahnSeries.coeff_order_eq_zero.1 (by rw [h2]; exact h0))

theorem coeff_rel_of_pow {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι]
    (φ : LaurentSeries (ZMod p) →+* k) {f : ℕ} (hf : f ≠ 0) (ε : ι → k) (hε : ∀ t, ε t ^ p ^ f = ε t)
    (s : Finset ι) : ∀ b : ι → LaurentSeries (ZMod p), (∀ t, t ∉ s → b t = 0) → ∑ t, ε t * φ (b t) = 0 →
      ∀ r, ∑ t, ε t * algebraMap (ZMod p) k ((b t).coeff r) = 0 := by
  classical
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) k)]; simp)
  have hC : ∀ c : ZMod p, φ (HahnSeries.C c) = algebraMap (ZMod p) k c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) c
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hb hrel r
  by_cases hA : ∃ l : ι → ZMod p, (∀ t, t ∉ s → l t = 0) ∧ ∑ t, ε t * algebraMap (ZMod p) k (l t) = 0 ∧ ∃ u, l u = 1
  · obtain ⟨l, hl, hlr, u, hu⟩ := hA
    have hus : u ∈ s := by
      by_contra h
      rw [hl u h] at hu; exact zero_ne_one hu
    have := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => b t - HahnSeries.C (l t) * b u) ?_ ?_ r
    · simp only [HahnSeries.coeff_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
        map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr] at this
      simpa using this
    · intro t ht
      by_cases htu : t = u
      · subst htu; simp [hu]
      · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
        simp [hb t this, hl t this]
    · simp only [map_sub, map_mul, hC, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr, hrel]
      simp
  · have hb0 : ∀ u, b u = 0 := by
      intro u
      by_contra hu
      have hus : u ∈ s := by
        by_contra h
        exact hu (hb u h)
      have hq : p ^ f ≠ 0 := pow_ne_zero _ hp.out.ne_zero
      set c : ι → LaurentSeries (ZMod p) := fun t => b t * (b u)⁻¹ with hc
      have hcu : c u = 1 := mul_inv_cancel₀ hu
      have hcs : ∀ t, t ∉ s → c t = 0 := fun t ht => by simp [hc, hb t ht]
      have hcr : ∑ t, ε t * φ (c t) = 0 := by
        simp only [hc, map_mul, ← mul_assoc, ← Finset.sum_mul, hrel, zero_mul]
      have hcr' : ∑ t, ε t * φ (c t ^ p ^ f) = 0 := by
        have := congrArg (· ^ p ^ f) hcr
        simp only [sum_pow_char_pow, mul_pow, hε, zero_pow hq] at this
        simpa only [map_pow] using this
      have hi := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => c t ^ p ^ f - c t) ?_ ?_
      · have hfix : ∀ t, c t ^ p ^ f = c t := by
          intro t
          rw [← sub_eq_zero]
          ext r'
          by_contra hne
          apply hA
          refine ⟨fun t' => (c t' ^ p ^ f - c t').coeff r' * ((c t ^ p ^ f - c t).coeff r')⁻¹, ?_, ?_, t,
            mul_inv_cancel₀ hne⟩
          · intro t' ht'
            simp [hcs t' ht', zero_pow hq]
          · simp only [map_mul, ← mul_assoc, ← Finset.sum_mul, hi r', zero_mul]
        apply hA
        refine ⟨fun t => (c t).coeff 0, fun t ht => by simp [hcs t ht], ?_, u, by simp [hcu]⟩
        rw [← hcr]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hC, ← const_of_pow_eq hf _ (hfix t)]
      · intro t ht
        by_cases htu : t = u
        · subst htu; simp [hcu]
        · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
          simp [hcs t this, zero_pow hq]
      · simp only [map_sub, mul_sub, Finset.sum_sub_distrib, hcr, hcr', sub_self]
    simp [hb0]

theorem exists_pow_eq {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι] (ε : ι → k)
    (h : ∀ t, IsAlgebraic (ZMod p) (ε t)) : ∃ f : ℕ, f ≠ 0 ∧ ∀ t, ε t ^ p ^ f = ε t := by
  let K := IntermediateField.adjoin (ZMod p) (Set.range ε)
  haveI : FiniteDimensional (ZMod p) K :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨t, rfl⟩; exact (h t).isIntegral)
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) K)]; simp)
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  refine ⟨n, n.ne_zero, fun t => ?_⟩
  have := FiniteField.pow_card (⟨ε t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ : K)
  rw [hn] at this
  exact congrArg Subtype.val this

end GlobalTheory.K5.ResDisj
