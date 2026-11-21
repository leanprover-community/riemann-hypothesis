import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOneStatement

section
open scoped BigOperators

namespace GlobalTheory

theorem pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3

end GlobalTheory

alias _root_.GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt := _root_.GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt
end

section
section
open scoped BigOperators

namespace GlobalTheory

private lemma one_add_X_pow_prime_pow_sub_one {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (m : ℕ) : (1 + Polynomial.X : Polynomial k) ^ (l ^ m) - 1 = Polynomial.X ^ (l ^ m) := by
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]

private lemma coeff_zero_aeval_of_coeff_zero_eq_zero {k σ : Type} [Field k] (g : σ → Polynomial k)
    (hg : ∀ q, (g q).coeff 0 = 0) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p q hp =>
    classical
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.mul_coeff_zero, hg, mul_zero,
      MvPolynomial.coeff_mul_X']
    simp

theorem coeff_aeval_one_add_X_pow_sub_one_ne_zero :
    ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  intro k σ _ _ l M _ _ D u n e hu hD hlt
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hgX : ∀ q, ((1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) = Polynomial.X ^ (l ^ e q) :=
    fun q => one_add_X_pow_prime_pow_sub_one l (e q)
  simp only [hgX]

  have hideal : ∀ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      (Polynomial.X : Polynomial k) ^ (l ^ M) ∣
        MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)) r := by
    intro r hr
    have hle : Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) ≤
        Ideal.comap (MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)))
          (Ideal.span {(Polynomial.X : Polynomial k) ^ (l ^ M)}) := by
      rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, MvPolynomial.aeval_X, ← pow_mul, pow_mul',
        Ideal.mem_span_singleton]
      exact dvd_pow_self _ (pow_pos hl _).ne'
    exact Ideal.mem_span_singleton.mp (hle hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      D = u * ∏ q, MvPolynomial.X q ^ n q + r := ⟨_, hD, by ring⟩
  rw [map_add, Polynomial.coeff_add, (Polynomial.X_pow_dvd_iff.mp (hideal r hr)) _ hlt, add_zero,
    map_mul, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ q, l ^ e q * n q = ∑ q, n q * l ^ e q :=
    Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hsum, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_aeval_of_coeff_zero_eq_zero _ _ u]
  · exact hu
  · intro q
    rw [Polynomial.coeff_X_pow, if_neg (pow_pos hl _).ne]

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  atlas_forward_decl GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero
end

section
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
private theorem C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd {O σ : Type} [CommRing O] [Fintype σ] (ϖ : O)
    (g : σ → Polynomial O) (k : σ → ℕ) (hg : ∀ q, Polynomial.C ϖ ∣ g q - Polynomial.X ^ k q)
    (m : σ → ℕ) :
    Polynomial.C ϖ ∣ ∏ q, g q ^ m q - Polynomial.X ^ (∑ q, m q * k q) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hq := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hg q))
  rw [map_pow, hq, ← map_pow, ← pow_mul, mul_comm]

open scoped BigOperators in
private theorem C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow {O : Type} [CommRing O] (ϖ : O) (l e : ℕ)
    (hl : l.Prime) (h : ϖ ∣ (l : O)) :
    Polynomial.C ϖ ∣ (1 + Polynomial.X : Polynomial O) ^ (l ^ e) - 1 - Polynomial.X ^ (l ^ e) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_X_pow]
  have hN : l ^ e ≠ 0 := (pow_pos hl.pos _).ne'
  by_cases h0 : i = 0
  · subst h0
    simp [hN.symm]
  by_cases hN' : i = l ^ e
  · subst hN'
    simp [h0, hl.ne_zero]
  · simp only [h0, hN', if_false, sub_zero]
    exact h.trans (Nat.cast_dvd_cast (hl.dvd_choose_pow h0 hN'))

open scoped BigOperators in

theorem _root_.GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  intro O _ _ _ ϖ _ σ _ l μ hl hϖl F e m₀ hlow hm₀ hoth
  classical
  set W := ∑ q, m₀ q * l ^ e q with hW
  set g : σ → Polynomial O := fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1 with hgdef
  set c : (σ →₀ ℕ) → O := fun m => (∏ q, g q ^ m q).coeff W with hc
  have hexp : (MvPolynomial.aeval g F).coeff W = ∑ m ∈ F.support, F.coeff m * c m := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hcong : ∀ m : σ →₀ ℕ, ϖ ∣ c m - if W = ∑ q, m q * l ^ e q then 1 else 0 := by
    intro m
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd ϖ g (fun q => l ^ e q)
      (fun q => by simpa [g] using C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow ϖ l (e q) hl hϖl) m) W
    simpa [Polynomial.coeff_X_pow] using h
  have hvanish : ∀ m : σ →₀ ℕ, W < m.degree → c m = 0 := by
    intro m hm
    have hX : ∀ q, Polynomial.X ∣ g q := fun q => by
      rw [Polynomial.X_dvd_iff]
      simp [g, Polynomial.coeff_one_add_X_pow]
    have hdvd : Polynomial.X ^ (∑ q, m q) ∣ ∏ q, g q ^ m q := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q _ => pow_dvd_pow_of_dvd (hX q) _
    rw [Finsupp.degree_eq_sum] at hm
    exact (Polynomial.X_pow_dvd_iff.1 hdvd) W hm
  have hdeg : ∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m q * l ^ e q := by
    intro m
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl.pos _)
  have hterm : ∀ m, m ≠ m₀ → ϖ ^ (μ + 1) ∣ F.coeff m * c m := by
    intro m hne
    by_cases hw : ∑ q, m q * l ^ e q ≤ W
    · exact dvd_mul_of_dvd_left (hoth m hne hw) _
    by_cases hd : m.degree ≤ W
    · have h1 := hcong m
      rw [if_neg (by omega), sub_zero] at h1
      rw [pow_succ]
      exact mul_dvd_mul (hlow m hd) h1
    · rw [hvanish m (by omega), mul_zero]
      exact dvd_zero _
  have hmain : ϖ ^ (μ + 1) ∣ F.coeff m₀ * c m₀ - F.coeff m₀ := by
    have h1 := hcong m₀
    rw [if_pos rfl] at h1
    rw [← mul_sub_one, pow_succ]
    exact mul_dvd_mul (hlow m₀ (hdeg m₀)) h1
  have hmem : m₀ ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    exact hm₀ (h0 ▸ dvd_zero _)
  intro hdiv
  rw [hexp, ← Finset.add_sum_erase _ _ hmem] at hdiv
  have hrest : ϖ ^ (μ + 1) ∣ ∑ m ∈ F.support.erase m₀, F.coeff m * c m :=
    Finset.dvd_sum fun m hm => hterm m (Finset.ne_of_mem_erase hm)
  have h2 := (dvd_add_left hrest).1 hdiv
  exact hm₀ (by simpa using dvd_sub h2 hmain)

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  atlas_forward_decl GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one
end

section
section
namespace GlobalTheory

open IsDiscreteValuationRing

theorem exists_toNat_addVal_algebraMap_eq_mul (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [Algebra O O'] [IsLocalHom (algebraMap O O')] (hinj : Function.Injective (algebraMap O O')) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ x : O,
      (addVal O' (algebraMap O O' x)).toNat = e * (addVal O x).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : algebraMap O O' ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (hinj (by simpa using h))
  have h1 : addVal O' (algebraMap O O' ϖ) ≠ ⊤ := by
    rwa [Ne, addVal_eq_top_iff]
  have h2 : addVal O' (algebraMap O O' ϖ) ≠ 0 := by
    rw [Ne, addVal_eq_zero_iff]
    intro h
    exact hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 h1
  refine ⟨e, ?_, fun x => ?_⟩
  · rintro rfl
    exact h2 (by rw [← he]; rfl)
  · by_cases hx : x = 0
    · subst hx
      simp
    · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
      have hv : addVal O x = n := addVal_def x u hϖ n hu
      have hu0 : addVal O' (algebraMap O O' (u : O)) = 0 := by
        rw [addVal_eq_zero_iff]
        exact u.isUnit.map _
      have hv' : addVal O' (algebraMap O O' x) = ((e * n : ℕ) : ℕ∞) := by
        rw [hu, map_mul, map_pow, addVal_mul, addVal_pow, hu0, ← he, zero_add, nsmul_eq_mul]
        push_cast
        ring
      rw [hv, hv', ENat.toNat_natCast, ENat.toNat_natCast]

theorem nval_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  intro O _ _ _ O' _ _ _ _ _ hinj l x
  obtain ⟨e, he, h⟩ := exists_toNat_addVal_algebraMap_eq_mul O O' hinj
  have hl : (l : O') = algebraMap O O' (l : O) := (map_natCast _ l).symm
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hl, h, h]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast he)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuation_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  atlas_forward_decl GlobalTheory.nval_algebraMap_eq
end

section
section
open IsDiscreteValuationRing

namespace GlobalTheory.PolyCycloValue

theorem card_double_min (S : Set ℕ) (a : ℕ → ℕ) (q : ℕ → ℝ) (w : ℕ) (hw : w ∈ S)
    (hq : ∀ k, 1 ≤ k → 0 < q k) (hqa : ∀ k k', 1 ≤ k → k < k' → q k' < q k) :
    ∃ BB : Finset ℕ, BB.card ≤ w + a w ∧ ∀ k, 1 ≤ k → k ∉ BB → ∀ i ∈ S, ∀ j ∈ S,
      (∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k) →
      (∀ m ∈ S, (a j : ℝ) + j * q k ≤ a m + m * q k) → i = j := by
  classical
  let M : ℕ → ℕ → Prop := fun k i => i ∈ S ∧ ∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k
  let B : Set ℕ := {k | 1 ≤ k ∧ ∃ i j, i < j ∧ M k i ∧ M k j}
  have hch : ∀ k, ∃ i j, k ∈ B → i < j ∧ M k i ∧ M k j := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨-, i, j, h⟩ := hk
      exact ⟨i, j, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose I J hIJ using hch

  have hA : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m ≤ i → a i ≤ a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k ≤ i * q k :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmi) (hq k hk).le
    have : (a i : ℝ) ≤ a m := by linarith
    exact_mod_cast this
  have hA' : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m < i → a i < a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k < i * q k :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hmi) (hq k hk)
    have : (a i : ℝ) < a m := by linarith
    exact_mod_cast this
  have hB : ∀ k k', 1 ≤ k → k < k' → ∀ m m', M k m → M k' m' → m ≤ m' := by
    intro k k' hk hkk m m' hm hm'
    by_contra hlt
    have hlt' : (m' : ℝ) < m := by exact_mod_cast (not_le.mp hlt)
    have h1 := hm.2 m' hm'.1
    have h2 := hm'.2 m hm.1
    have h3 := hqa k k' hk hkk
    nlinarith [mul_pos (sub_pos.mpr hlt') (sub_pos.mpr h3)]
  let φ : ℕ → ℕ := fun k => if I k < w then I k else w + a (J k)
  have hmaps : Set.MapsTo φ B (Finset.range (w + a w) : Set ℕ) := by
    intro k hk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    split_ifs with h
    · omega
    · have := hA' k hk.1 (J k) w hj hw (by omega)
      omega
  have hne : ∀ k ∈ B, ∀ k' ∈ B, k < k' → φ k ≠ φ k' := by
    intro k hk k' hk' hkk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    obtain ⟨hlt', hi', hj'⟩ := hIJ k' hk'
    have h1 := hB k k' hk.1 hkk _ _ hj hi'
    have h2 := hA' k' hk'.1 (J k') (J k) hj' hj.1 (by omega)
    simp only [φ]
    split_ifs <;> omega
  have hinj : Set.InjOn φ B := by
    intro k hk k' hk' h
    rcases lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd h (hne k hk k' hk' h1)
    · exact h1
    · exact absurd h.symm (hne k' hk' k hk h1)
  have hfin : B.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have := Finset.card_le_card_of_injOn (s := hfin.toFinset) (t := Finset.range (w + a w)) φ
      (by simpa using hmaps) (by simpa using hinj)
    simpa using this
  · intro k hk hkB i hi j hj hmi hmj
    rw [Set.Finite.mem_toFinset] at hkB
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkB ⟨hk, i, j, h, ⟨hi, hmi⟩, ⟨hj, hmj⟩⟩
    · exact hkB ⟨hk, j, i, h, ⟨hj, hmj⟩, ⟨hi, hmi⟩⟩

section Val

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_ne_top {x : R} (hx : x ≠ 0) : addVal R x ≠ ⊤ := by
  rwa [Ne, addVal_eq_top_iff]

theorem toNat_addVal_pos {x : R} (hx : x ≠ 0) (hu : ¬ IsUnit x) : 0 < (addVal R x).toNat := by
  have h1 := addVal_ne_top hx
  have h2 : addVal R x ≠ 0 := by rwa [Ne, addVal_eq_zero_iff]
  exact Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem nval_mul_pow (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (x * y ^ n) =
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x + n * Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  have : addVal R (x * y ^ n) = ((s + n * t : ℕ) : ℕ∞) := by
    rw [(addVal R).map_mul, (addVal R).map_pow, ← hs, ← ht]; simp
  rw [this, ← hs, ← ht]
  simp only [ENat.toNat_coe]
  push_cast
  ring

theorem addVal_lt_of_nval_lt (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y) : addVal R x < addVal R y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval at h
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  rw [← hs, ← ht] at h ⊢
  simp only [ENat.toNat_coe] at h
  have : (s : ℝ) < t := lt_of_not_ge fun hge =>
    absurd h (not_lt.mpr (div_le_div_of_nonneg_right hge (Nat.cast_nonneg _)))
  exact_mod_cast this

theorem sum_unique_min (l : ℕ) (S : Finset ℕ) (t : ℕ → R) (ht : ∀ i ∈ S, t i ≠ 0) (i₀ : ℕ)
    (hi₀ : i₀ ∈ S)
    (h : ∀ i ∈ S, i ≠ i₀ → Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i)) :
    ∑ i ∈ S, t i ≠ 0 ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (∑ i ∈ S, t i) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) := by
  have h0 := addVal_ne_top (ht i₀ hi₀)
  have h1 : addVal R (t i₀) < addVal R (∑ i ∈ S.erase i₀, t i) :=
    (addVal R).map_lt_sum h0 fun i hi =>
      addVal_lt_of_nval_lt l (ht i₀ hi₀) (ht i (Finset.mem_of_mem_erase hi))
        (h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have h2 : addVal R (∑ i ∈ S, t i) = addVal R (t i₀) := by
    rw [← Finset.add_sum_erase S t hi₀]
    exact (addVal R).map_add_eq_of_lt_left h1
  refine ⟨fun hz => h0 ?_, ?_⟩
  · rw [← h2, hz]; simp
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval; rw [h2]

end Val

theorem value_at_root_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  intro O _ _ _ l hl hl0 hlu h w hw
  set e : ℝ := ((addVal O (l : O)).toNat : ℝ) with he
  have hepos : 0 < e := by rw [he]; exact_mod_cast toNat_addVal_pos hl0 hlu
  have hphi : ∀ k, (0 : ℝ) < (Nat.totient (l ^ k) : ℝ) := fun k => by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hl.pos k)
  let a : ℕ → ℕ := fun i => (addVal O (h.coeff i)).toNat
  let q : ℕ → ℝ := fun k => e / (Nat.totient (l ^ k) : ℝ)
  have hwS : w ∈ h.support := Polynomial.mem_support_iff.mpr hw
  obtain ⟨BB, hcard, hBB⟩ := card_double_min (h.support : Set ℕ) a q w hwS
    (fun k _ => div_pos hepos (hphi k)) (by
      intro k k' hk hkk
      refine div_lt_div_of_pos_left hepos (hphi k) ?_
      rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)]
      have h1 : l ^ (k - 1) < l ^ (k' - 1) := Nat.pow_lt_pow_right hl.one_lt (by omega)
      have h2 : 0 < l - 1 := by have := hl.one_lt; omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right h1 h2)
  have hmin : ∀ k, ∃ i ∈ h.support, ∀ m ∈ h.support, (a i : ℝ) + i * q k ≤ a m + m * q k :=
    fun k => Finset.exists_min_image h.support (fun i => (a i : ℝ) + i * q k) ⟨w, hwS⟩
  choose I hIS hI using hmin
  have hform : ∀ k i : ℕ, Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff i) + i / (Nat.totient (l ^ k) : ℝ)
      = ((a i : ℝ) + i * q k) / e := by
    intro k i
    have := hphi k
    simp only [Formalism.MainNotions.BlochKatoReduction.Gen.nval, a, q, ← he]
    field_simp
  refine ⟨BB, fun k => ((a (I k) : ℝ) + I k * q k) / e, hcard, fun k hk hkB => ⟨?_, ?_⟩⟩
  · rw [hform]
    exact div_le_div_of_nonneg_right (hI k w hwS) hepos.le
  · intro O' _ _ _ _ _ hinj ζ hζ
    have hl0' : (l : O') ≠ 0 := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hl0 (hinj (by rw [h0, map_zero]))
    have hlu' : ¬ IsUnit (l : O') := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hlu (IsLocalHom.map_nonunit _ h0)
    obtain ⟨hz, hv⟩ := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one O' l k hl hk hl0' hlu' ζ hζ
    have hc : ∀ i ∈ h.support, algebraMap O O' (h.coeff i) ≠ 0 := fun i hi h0 =>
      Polynomial.mem_support_iff.mp hi (hinj (by rw [h0, map_zero]))
    have hval : ∀ i ∈ h.support,
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
          = ((a i : ℝ) + i * q k) / e := by
      intro i hi
      rw [nval_mul_pow l (hc i hi) hz, hv, GlobalTheory.T.normalizedValuation_algebraMap_eq O O' hinj, ← hform, mul_one_div]
    have key := sum_unique_min l h.support
      (fun i => algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
      (fun i hi => mul_ne_zero (hc i hi) (pow_ne_zero _ hz)) (I k) (hIS k) (by
        intro i hi hne
        rw [hval i hi, hval _ (hIS k)]
        refine div_lt_div_of_pos_right ?_ hepos
        refine lt_of_le_of_ne (hI k i hi) fun heq => hne ?_
        exact hBB k hk hkB i hi (I k) (hIS k) (fun m hm => heq ▸ hI k m hm) (hI k))
    rw [hval _ (hIS k)] at key
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact key

end GlobalTheory.PolyCycloValue
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_polynomial_at_root_of_unity_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  atlas_forward_decl GlobalTheory.PolyCycloValue.value_at_root_sub_one
end

section
section
open scoped BigOperators

namespace GlobalTheory

open PowerSeries

open scoped BigOperators in
open PowerSeries in

theorem _root_.GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  intro O _ _ _ ϖ hϖ D g f m₀ v nT MT hD hg hv hM hf
  classical
  have hnu : ∀ x : O, ¬ IsUnit x → ϖ ∣ x := fun x hx => by
    have hmax : x ∈ IsLocalRing.maximalIdeal O := hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
    exact hmax
  by_contra hcon
  push_neg at hcon
  have hDg : ∀ i ≤ (v + 1) * m₀, ϖ ^ (v + 1) ∣ PowerSeries.coeff i (D * g) := by
    intro i hi
    have h1 := dvd_trans (pow_dvd_pow ϖ hv) (hf i (hi.trans hM))
    have h2 := hcon i hi
    have : PowerSeries.coeff i (D * g) = PowerSeries.coeff i f - PowerSeries.coeff i (f - D * g) := by
      simp
    rw [this]
    exact dvd_sub h2 h1
  have hD' : ∃ m, m ≤ m₀ ∧ IsUnit (PowerSeries.coeff m D) := hD
  set m₁ := Nat.find hD' with hm₁
  have hm₁le : m₁ ≤ m₀ := (Nat.find_spec hD').1
  have hm₁u : IsUnit (PowerSeries.coeff m₁ D) := (Nat.find_spec hD').2
  have hlow : ∀ a < m₁, ϖ ∣ PowerSeries.coeff a D := fun a ha =>
    hnu _ fun hu => Nat.find_min hD' ha ⟨(ha.trans_le hm₁le).le, hu⟩
  have claim : ∀ j ≤ v + 1, ∀ i, i + j * m₁ ≤ (v + 1) * m₀ → ϖ ^ j ∣ PowerSeries.coeff i g := by
    intro j
    induction j with
    | zero => intro _ i _; simp
    | succ j ihj =>
      intro hj i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hsplit := (Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal (i + m₁))
          (fun p : ℕ × ℕ => PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g)
          (a := (m₁, i)) (by simp [add_comm])).symm
        rw [← PowerSeries.coeff_mul] at hsplit
        have hrest : ϖ ^ (j + 1) ∣ ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + m₁)).erase (m₁, i),
            PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g := by
          apply Finset.dvd_sum
          rintro ⟨a, b⟩ hp
          simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
          obtain ⟨hne, hab⟩ := hp
          rcases lt_trichotomy a m₁ with h | h | h
          · rw [pow_succ, mul_comm (ϖ ^ j)]
            exact mul_dvd_mul (hlow a h) (ihj (by omega) b (by nlinarith))
          · exact absurd ⟨h, by omega⟩ hne
          · exact dvd_mul_of_dvd_right (ihi b (by omega) (by nlinarith)) _
        have htot : ϖ ^ (j + 1) ∣ PowerSeries.coeff (i + m₁) (D * g) :=
          dvd_trans (pow_dvd_pow ϖ hj) (hDg _ (by nlinarith))
        rw [hsplit] at htot
        have := (dvd_add_left hrest).1 htot
        exact (hm₁u.dvd_mul_left).1 this
  exact hg (by simpa using claim (v + 1) le_rfl 0 (by simpa using Nat.mul_le_mul_left (v + 1) hm₁le))

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_low_coeff_not_dvd_of_congr_mul' : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  atlas_forward_decl GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul
end

section
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in

theorem _root_.GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  intro ρ S hS
  have hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y)) :=
    Pi.Lex.wellFounded _ (fun _ => wellFounded_lt)
  refine ⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩
  set m := hwf.min S hS with hm
  intro c hc a ha hne
  have hnl := hwf.not_lt_min S ha
  have hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hi]⟩
  set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef
  have hk : a k ≠ m k := (Finset.mem_filter.1 (Finset.max'_mem _ hd)).2
  have hgt : ∀ j, k < j → a j = m j := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  have hlt : m k < a k := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl
    · exact h
  have key : ∀ i, m i * c i + (if i = k then c k else 0) ≤
      a i * c i + (if i < k then m i * c i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne]
    · subst h
      simp only [if_true, lt_irrefl, if_false, add_zero]
      nlinarith
    · simp [h.ne', not_lt.2 h.le, hgt i h]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k := by ext; simp
  rw [hI] at hsum
  have := hc k
  omega

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  atlas_forward_decl GlobalTheory.exists_exponent_strictly_least_weight
end

section
section
open scoped BigOperators

namespace GlobalTheory

theorem exists_limit_family_of_finite_coefficients (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩

end GlobalTheory
end

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_family_of_finite_coefficients' : ∀ (σ I R : Type) [Finite σ] [Finite I] [Finite R] (F : ℕ → I → (σ →₀ ℕ) → R), ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧ ∀ x m, m.degree ≤ N → F M x m = G x m := by
  atlas_forward_decl GlobalTheory.exists_limit_family_of_finite_coefficients
end

section
section
open scoped BigOperators

namespace GlobalTheory.OrderEval

theorem addVal_le_iff_not_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (x : O) (n : ℕ) :
    IsDiscreteValuationRing.addVal O x ≤ n ↔ ¬ ϖ ^ (n + 1) ∣ x := by
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, not_le]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  exact (ENat.lt_add_one_iff (ENat.coe_ne_top n)).symm

theorem degree_le_weight {σ : Type} [Fintype σ] {l : ℕ} (hl : 0 < l) (e : σ → ℕ) (m : σ →₀ ℕ) :
    m.degree ≤ ∑ q, m q * l ^ e q := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl _)

theorem aeval_subst {O O' σ : Type} [CommRing O] [CommRing O'] [Algebra O O'] (l : ℕ) (e : σ → ℕ)
    (ζ : O') (F : MvPolynomial σ O) :
    Polynomial.aeval (ζ - 1)
      (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F)
      = MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) F := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp

theorem le_totient_pow {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : 1 ≤ k) : k ≤ Nat.totient (l ^ k) := by
  rw [Nat.totient_prime_pow hl hk]
  have h1 : k - 1 < l ^ (k - 1) := Nat.lt_pow_self hl.one_lt
  have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
  calc k ≤ l ^ (k - 1) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem exists_low_coeff_of_limit (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime) (hd : ϖ ∣ (l : O))
    (σ : Type) [Fintype σ] (ρ : ℕ) (τ : Fin ρ ≃ σ) (D M₀ : ℕ) (I : Type) [Finite I] (μ : I → ℕ)
    (F : ℕ → I → MvPolynomial σ O)
    (hF : ∀ M, M₀ ≤ M → ∀ x, ∃ m : σ →₀ ℕ, m.degree ≤ D ∧ ¬ ϖ ^ (μ x + 1) ∣ (F M x).coeff m) :
    ∃ a : ℕ, ∀ e : σ → ℕ, (∀ i' i : Fin ρ, i' < i → e (τ i') + a ≤ e (τ i)) →
      ∃ W : ℕ, ∀ M₁, ∃ M, M₁ ≤ M ∧ ∀ x, ∃ w ≤ W, ¬ ϖ ^ (μ x + 1) ∣
        (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1)
          (F M x)).coeff w := by
  classical
  obtain ⟨K, hK⟩ := (Set.finite_range μ).bddAbove
  have hK' : ∀ x, μ x ≤ K := fun x => hK ⟨x, rfl⟩
  obtain ⟨G₀, hG₀⟩ := GlobalTheory.T.exists_limit_family_of_finite_coefficients' σ I (Fin (K + 2) → Prop)
    (fun M x m j => ϖ ^ (j : ℕ) ∣ (F M x).coeff m)
  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → ℕ → Prop, ∀ N M₁ : ℕ, ∃ M, M₁ ≤ M ∧ ∀ x m,
      m.degree ≤ N → ∀ j, j ≤ K + 1 → (ϖ ^ j ∣ (F M x).coeff m ↔ G x m j) := by
    refine ⟨fun x m j => ∀ h : j < K + 2, G₀ x m ⟨j, h⟩, fun N M₁ => ?_⟩
    obtain ⟨M, hM, h⟩ := hG₀ N M₁
    refine ⟨M, hM, fun x m hm j hj => ?_⟩
    have h2 := h x m hm
    constructor
    · intro h3 h4
      rw [← h2]; exact h3
    · intro h3
      have h4 := h3 (by omega)
      rw [← h2] at h4; exact h4
  have ex0 : ∀ x, ∃ m, ¬ G x m (μ x + 1) := by
    intro x
    obtain ⟨M, hM, h⟩ := hG D M₀
    obtain ⟨m, hm, h2⟩ := hF M hM x
    exact ⟨m, fun h3 => h2 ((h x m hm _ (by have := hK' x; omega)).2 h3)⟩
  have ex : ∀ x, ∃ j, ∃ m, ¬ G x m (j + 1) := fun x => ⟨μ x, ex0 x⟩
  have hν : ∀ x, Nat.find (ex x) ≤ μ x := fun x => Nat.find_min' _ (ex0 x)
  have hS : ∀ x, ∃ m₀ : σ →₀ ℕ, ¬ G x m₀ (Nat.find (ex x) + 1) ∧ ∀ c : σ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m₀ (τ i') * c (τ i') < c (τ i)) → ∀ m : σ →₀ ℕ,
      ¬ G x m (Nat.find (ex x) + 1) → m ≠ m₀ → ∑ q, m₀ q * c q < ∑ q, m q * c q := by
    intro x
    obtain ⟨m1, hm1⟩ := Nat.find_spec (ex x)
    obtain ⟨m, ⟨m₀, hm₀, rfl⟩, h⟩ := GlobalTheory.T.exists_least_weight_exponent ρ
      {a | ∃ m : σ →₀ ℕ, ¬ G x m (Nat.find (ex x) + 1) ∧ (fun i => m (τ i)) = a}
      ⟨_, m1, hm1, rfl⟩
    refine ⟨m₀, hm₀, fun c hc m hm hne => ?_⟩
    have h2 := h (fun i => c (τ i)) hc (fun i => m (τ i)) ⟨m, hm, rfl⟩ (by
      intro h3
      apply hne
      ext q
      simpa using congrFun h3 (τ.symm q))
    rw [← τ.sum_comp (fun q => m₀ q * c q), ← τ.sum_comp (fun q => m q * c q)]
    exact h2
  choose m₀ hm₀ hmin using hS
  obtain ⟨B, hB⟩ := (Set.finite_range (fun p : I × σ => m₀ p.1 p.2)).bddAbove
  have hB' : ∀ x q, m₀ x q ≤ B := fun x q => hB ⟨(x, q), rfl⟩
  refine ⟨ρ * B, fun e he => ?_⟩
  obtain ⟨W, hW⟩ := (Set.finite_range (fun x => ∑ q, m₀ x q * l ^ e q)).bddAbove
  have hW' : ∀ x, ∑ q, m₀ x q * l ^ e q ≤ W := fun x => hW ⟨x, rfl⟩
  refine ⟨W, fun M₁ => ?_⟩
  obtain ⟨M, hM, h⟩ := hG W M₁
  refine ⟨M, hM, fun x => ⟨_, hW' x, ?_⟩⟩
  have hc : ∀ i, ∑ i' ∈ Finset.Iio i, m₀ x (τ i') * l ^ e (τ i') < l ^ e (τ i) := by
    intro i
    have h1 : (∑ i' ∈ Finset.Iio i, m₀ x (τ i') * l ^ e (τ i')) * l ^ (ρ * B)
        ≤ ρ * B * l ^ e (τ i) := by
      rw [Finset.sum_mul]
      calc _ ≤ (Finset.Iio i).card • (B * l ^ e (τ i)) := by
            apply Finset.sum_le_card_nsmul
            intro i' hi'
            rw [mul_assoc, ← pow_add]
            exact Nat.mul_le_mul (hB' _ _)
              (Nat.pow_le_pow_right hl.pos (he i' i (Finset.mem_Iio.1 hi')))
        _ ≤ _ := by
            rw [smul_eq_mul, mul_assoc]
            apply Nat.mul_le_mul_right
            simpa using (Finset.card_le_univ (Finset.Iio i))
    have h2 : ρ * B < l ^ (ρ * B) := Nat.lt_pow_self hl.one_lt
    have h3 : 0 < l ^ e (τ i) := pow_pos hl.pos _
    apply lt_of_mul_lt_mul_right (a := l ^ (ρ * B)) _ (Nat.zero_le _)
    calc _ ≤ _ := h1
      _ < l ^ (ρ * B) * l ^ e (τ i) := Nat.mul_lt_mul_of_pos_right h2 h3
      _ = _ := mul_comm _ _
  have hx := hK' x
  have hνx := hν x
  have key := GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one O ϖ hϖ σ l (Nat.find (ex x)) hl hd (F M x) e (m₀ x) ?_ ?_ ?_
  · exact fun h5 => key ((pow_dvd_pow ϖ (by omega)).trans h5)
  · intro m hm
    rcases Nat.eq_zero_or_pos (Nat.find (ex x)) with h0 | h0
    · rw [h0]; simp
    · have h6 := Nat.find_min (ex x) (m := Nat.find (ex x) - 1) (by omega)
      rw [h x m (hm.trans (hW' x)) _ (by omega)]
      by_contra h7
      exact h6 ⟨m, by rwa [Nat.sub_add_cancel h0]⟩
  · rw [h x _ ((degree_le_weight hl.pos e _).trans (hW' x)) _ (by omega)]
    exact hm₀ x
  · intro m hne hm
    rw [h x _ ((degree_le_weight hl.pos e _).trans (hm.trans (hW' x))) _ (by omega)]
    by_contra h7
    exact absurd (hmin x (fun q => l ^ e q) hc m h7 hne) (not_lt.2 hm)

def lowIdeal {O : Type} [CommRing O] (p : O) (T : ℕ) : Ideal (Polynomial O) where
  carrier := {h | ∀ i ≤ T, p ∣ h.coeff i}
  add_mem' := fun ha hb i hi => by
    rw [Polynomial.coeff_add]; exact dvd_add (ha i hi) (hb i hi)
  zero_mem' := fun i _ => by simp
  smul_mem' := fun c h hh i hi => by
    rw [smul_eq_mul, Polynomial.coeff_mul]
    refine Finset.dvd_sum fun x hx => Dvd.dvd.mul_left (hh _ ?_) _
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    omega

theorem pow_sub_one_mem_lowIdeal {O : Type} [CommRing O] (ϖ : O) (l : ℕ) (hl : l.Prime)
    (hd : ϖ ∣ (l : O)) (n T a : ℕ) (ha : n + T ≤ a) :
    (1 + Polynomial.X : Polynomial O) ^ (l ^ a) - 1 ∈ lowIdeal (ϖ ^ n) T := by
  intro i hi
  rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one]
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp
  · rw [if_neg h0.ne', sub_zero]
    have h1 : T + 1 < l ^ (T + 1) := Nat.lt_pow_self hl.one_lt
    have h2 := GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt l a T i hl h0 (by omega)
    have h3 : l ^ n ∣ (l ^ a).choose i := (pow_dvd_pow l (by omega)).trans h2
    have h4 : ((l ^ n : ℕ) : O) ∣ (((l ^ a).choose i : ℕ) : O) := Nat.cast_dvd_cast h3
    rw [Nat.cast_pow] at h4
    exact (pow_dvd_pow_of_dvd hd n).trans h4

theorem coeff_zero_subst {O σ : Type} [CommRing O] (l : ℕ) (e : σ → ℕ) (g : MvPolynomial σ O) :
    (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) g).coeff 0
      = g.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_aeval_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [map_sub, map_pow, map_add, map_one, Polynomial.aeval_X, add_zero, one_pow, sub_self]
  rw [MvPolynomial.aeval_zero']
  rfl

theorem map_subst {O k σ : Type} [CommRing O] [CommRing k] (φ : O →+* k) (l : ℕ) (e : σ → ℕ)
    (g : MvPolynomial σ O) :
    (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) g).map φ
      = MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1)
        (g.map φ) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p q hp => simp [Polynomial.map_mul, hp]

theorem exists_low_coeff_of_factor (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime)
    (hd : ϖ ∣ (l : O)) (R nmax V s : ℕ) :
    ∃ E W : ℕ, ∀ e : Fin R ⊕ Fin R → ℕ, (∀ i, e (Sum.inl i) ≤ s) → (∀ i, E ≤ e (Sum.inr i)) →
      ∀ M, E ≤ M → ∀ v, v ≤ V → ∀ f Dd g : MvPolynomial (Fin R ⊕ Fin R) O,
      f - Dd * g ∈ Ideal.span (Set.range (fun i : Fin R =>
        (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
        Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) →
      ¬ ϖ ^ (v + 1) ∣ g.coeff 0 →
      ∀ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ),
      u.coeff 0 ≠ 0 → (∀ i, n i ≤ nmax) →
      Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈
        Ideal.span (Set.range fun q => (MvPolynomial.X q :
          MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M)) →
      ∃ w ≤ W, ¬ ϖ ^ (v + 1) ∣
        (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1)
          f).coeff w := by
  set m₀ := R * (nmax * l ^ s) with hm₀
  refine ⟨V + 1 + (V + 1) * m₀, (V + 1) * m₀, ?_⟩
  intro e he1 he2 M hM v hv f Dd g hf hg u n hu hn hD
  set S : MvPolynomial (Fin R ⊕ Fin R) O →ₐ[O] Polynomial O :=
    MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) with hS
  have hvm : (v + 1) * m₀ ≤ (V + 1) * m₀ := Nat.mul_le_mul_right _ (by omega)
  have hmem : S (f - Dd * g) ∈ lowIdeal (ϖ ^ (V + 1)) ((V + 1) * m₀) := by
    refine (Ideal.span_le (I := (lowIdeal (ϖ ^ (V + 1)) ((V + 1) * m₀)).comap S)).2 ?_ hf
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change S _ ∈ lowIdeal _ _
      simp only [hS, MvPolynomial.aeval_X]
      exact pow_sub_one_mem_lowIdeal ϖ l hl hd _ _ _ (he2 i)
    · change S _ ∈ lowIdeal _ _
      simp only [hS, map_sub, map_pow, map_add, map_one, MvPolynomial.aeval_X, add_sub_cancel]
      rw [← pow_mul, ← pow_add]
      exact pow_sub_one_mem_lowIdeal ϖ l hl hd _ _ _ (by omega)
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact fun h => hϖ.not_isUnit (isUnit_of_dvd_unit hd h)
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  have hw : ∑ q, Sum.elim n (fun _ => 0) q * l ^ e q ≤ m₀ := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
    calc _ ≤ (Finset.univ : Finset (Fin R)).card • (nmax * l ^ s) := by
          apply Finset.sum_le_card_nsmul
          intro i _
          exact Nat.mul_le_mul (hn i) (Nat.pow_le_pow_right hl.pos (he1 i))
      _ = m₀ := by simp [hm₀]
  have hlt : m₀ < l ^ M := by
    have h1 : M < l ^ M := Nat.lt_pow_self hl.one_lt
    have h2 : m₀ ≤ (V + 1) * m₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h4 := GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' (IsLocalRing.ResidueField O) (Fin R ⊕ Fin R) l M
    (Dd.map (IsLocalRing.residue O)) u (Sum.elim n (fun _ => 0)) e hu
    (by simpa [Fintype.prod_sum_type] using hD) (hw.trans_lt hlt)
  rw [← map_subst, Polynomial.coeff_map, IsLocalRing.residue_ne_zero_iff_isUnit] at h4
  obtain ⟨i, hi, h5⟩ := GlobalTheory.T.exists_low_coeff_not_dvd_of_congr_mul' O ϖ hϖ (S Dd : Polynomial O) (S g : Polynomial O)
    (S f : Polynomial O) m₀ v (V + 1) ((V + 1) * m₀)
    ⟨_, hw, by rw [Polynomial.coeff_coe]; exact h4⟩
    (by rw [Polynomial.coeff_coe, hS, coeff_zero_subst]; exact hg) (by omega) hvm
    (by
      intro i hi
      rw [← Polynomial.coe_mul, ← Polynomial.coe_sub, Polynomial.coeff_coe, ← map_mul, ← map_sub]
      exact hmem i hi)
  rw [Polynomial.coeff_coe] at h5
  exact ⟨i, hi.trans hvm, h5⟩

theorem exists_levels (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime) (h0 : (l : O) ≠ 0) (hu : ¬ IsUnit (l : O))
    (J : Type) [Finite J] (v : J → ℕ) (W : ℕ) :
    ∃ N : ℕ, ∀ h : J → Polynomial O, (∀ y, ∃ w ≤ W, ¬ ϖ ^ (v y + 1) ∣ (h y).coeff w) →
      ∃ BB : Finset ℕ, BB.card ≤ N ∧ ∀ k, 1 ≤ k → k ∉ BB →
        ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
          [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') →
          ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → ∀ y, Polynomial.aeval (ζ - 1) (h y) ≠ 0 ∧
            Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) (h y)) ≤
              (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ)
                + W / (Nat.totient (l ^ k) : ℝ) := by
  classical
  haveI := Fintype.ofFinite J
  refine ⟨∑ y, (W + v y), fun h hh => ?_⟩
  choose w hw hd using hh
  have hne : ∀ y, (h y).coeff (w y) ≠ 0 := fun y h1 => hd y (by rw [h1]; exact dvd_zero _)
  have hval : ∀ y, (IsDiscreteValuationRing.addVal O ((h y).coeff (w y))).toNat ≤ v y :=
    fun y => ENat.toNat_le_of_le_coe ((addVal_le_iff_not_dvd hϖ _ _).2 (hd y))
  choose BB c hc hB using fun y => GlobalTheory.T.valuation_polynomial_at_root_of_unity_sub_one O l hl h0 hu (h y) (w y) (hne y)
  refine ⟨Finset.univ.biUnion BB, Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ =>
    (hc y).trans (Nat.add_le_add (hw y) (hval y))), ?_⟩
  intro k hk hkB O' _ _ _ _ _ hinj ζ hζ y
  obtain ⟨h1, h2⟩ := hB y k hk (fun h3 => hkB (Finset.mem_biUnion.2 ⟨y, Finset.mem_univ _, h3⟩))
  obtain ⟨h3, h4⟩ := h2 O' hinj ζ hζ
  refine ⟨h3, h4 ▸ h1.trans (add_le_add ?_ ?_)⟩
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
    exact div_le_div_of_nonneg_right (by exact_mod_cast hval y) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hw y) (Nat.cast_nonneg _)

theorem order_eval : ∀ (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Finite (IsLocalRing.ResidueField O₀)] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)], Function.Injective (algebraMap O₀ O) → ∀ (l : ℕ), l.Prime → (l : O₀) ≠ 0 → ¬ IsUnit (l : O₀) → ∀ (R D nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : I → ℕ) (v : J → ℕ) (F : ℕ → I → MvPolynomial (Fin R ⊕ Fin R) O₀) (f Dd g : ℕ → J → MvPolynomial (Fin R ⊕ Fin R) O), (∀ M, M₀ ≤ M → ∀ x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ D ∧ IsDiscreteValuationRing.addVal O₀ ((F M x).coeff m) ≤ μ x) → (∀ M, M₀ ≤ M → ∀ y, f M y - Dd M y * g M y ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪ Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧ IsDiscreteValuationRing.addVal O ((g M y).coeff 0) ≤ v y ∧ ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧ (Dd M y).map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈ Ideal.span (Set.range fun q => (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))) → ∀ ε : ℝ, 0 < ε → ∃ (M k : ℕ) (e : Fin R ⊕ Fin R → ℕ), M₀ ≤ M ∧ 1 ≤ k ∧ k ≤ M ∧ (∀ q, e q < k ∧ (l : ℝ) ^ e q / (Nat.totient (l ^ k) : ℝ) ≤ ε) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → (∀ x, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O)) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O))) ≤ (μ x : ℝ) / ((IsDiscreteValuationRing.addVal O₀ (l : O₀)).toNat : ℝ) + ε) ∧ (∀ y, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y)) ≤ (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) + ε) := by
  intro O₀ _ _ _ _ O _ _ _ _ _ hinj₀ l hl hl0 hlu R D nmax M₀ I J _ _ μ v F f Dd g hF hf ε hε
  classical
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0' : (l : O) ≠ 0 := by
    rw [← map_natCast (algebraMap O₀ O)]
    exact fun h => hl0 (hinj₀ (by rw [h, map_zero]))
  have hlu' : ¬ IsUnit (l : O) := by
    rw [← map_natCast (algebraMap O₀ O)]
    exact fun h => hlu (IsLocalHom.map_nonunit _ h)
  have hdv : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (π : A),
      Irreducible π → ¬ IsUnit (l : A) → π ∣ (l : A) := by
    intro A _ _ _ π hπ h
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact h
  obtain ⟨a, ha⟩ := exists_low_coeff_of_limit O₀ ϖ₀ hϖ₀ l hl (hdv _ _ hϖ₀ hlu) (Fin R ⊕ Fin R)
    (R + R) finSumFinEquiv.symm D M₀ I μ F (fun M hM x => by
      obtain ⟨m, h1, h2⟩ := hF M hM x
      exact ⟨m, h1, (addVal_le_iff_not_dvd hϖ₀ _ _).1 h2⟩)
  obtain ⟨V, hV⟩ := (Set.finite_range v).bddAbove
  obtain ⟨E, W₂, hE⟩ := exists_low_coeff_of_factor O ϖ hϖ l hl (hdv _ _ hϖ hlu') R nmax V (a * R)
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : Fin R ⊕ Fin R → ℕ,
      (∀ i' i : Fin (R + R), i' < i →
        e (finSumFinEquiv.symm i') + a ≤ e (finSumFinEquiv.symm i)) ∧
      (∀ i, e (Sum.inl i) ≤ a * R) ∧ (∀ i, E ≤ e (Sum.inr i)) := by
    refine ⟨Sum.elim (fun i => a * i) (fun i => a * (i + R) + E), ?_, ?_, ?_⟩
    · intro i' i hi
      obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i'
      obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective i
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have aux : ∀ s t : ℕ, s < t → a * s + a ≤ a * t := fun s t h =>
        Nat.mul_le_mul_left a (Nat.succ_le_of_lt h)
      have h2 := aux _ _ (Fin.lt_def.1 hi)
      rcases p with p | p <;> rcases q with q | q
      · simpa using h2
      · simp at h2 ⊢; omega
      · exfalso
        have h3 := Fin.lt_def.1 hi
        have h4 := q.2
        simp at h3; omega
      · simp at h2 ⊢; omega
    · intro i
      exact Nat.mul_le_mul_left a i.2.le
    · intro i
      exact Nat.le_add_left _ _
  obtain ⟨W₁, hW₁⟩ := ha e he0
  obtain ⟨N₁, hN₁⟩ := exists_levels O₀ ϖ₀ hϖ₀ l hl hl0 hlu I μ W₁
  obtain ⟨N₂, hN₂⟩ := exists_levels O ϖ hϖ l hl hl0' hlu' J v W₂
  obtain ⟨C, hC⟩ := (Set.finite_range (fun q => l ^ e q)).bddAbove
  have hC' : ∀ q, l ^ e q ≤ C := fun q => hC ⟨q, rfl⟩
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge (((C + W₁ + W₂ : ℕ) : ℝ) / ε)
  obtain ⟨M, hM, hMF⟩ := hW₁ (M₀ + E + (k₁ + C + 1 + (N₁ + N₂)))
  obtain ⟨B₁, hB₁, hb₁⟩ := hN₁ _ hMF
  obtain ⟨B₂, hB₂, hb₂⟩ := hN₂ (fun y => MvPolynomial.aeval
      (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) (f M y)) (fun y => by
    obtain ⟨h1, h2, u, n, h3, h4, h5⟩ := hf M (by omega) y
    exact hE e he1 he2 M (by omega) (v y) (hV ⟨y, rfl⟩) _ _ _ h1
      ((addVal_le_iff_not_dvd hϖ _ _).1 h2) u n h3 h4 h5)
  obtain ⟨k, hk, hkB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := B₁ ∪ B₂) (t := Finset.Icc (k₁ + C + 1) (k₁ + C + 1 + (N₁ + N₂))) (by
      have := Finset.card_union_le B₁ B₂
      rw [Nat.card_Icc]; omega)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_union, not_or] at hkB
  have hk1 : 1 ≤ k := by omega
  have hsm : ∀ c : ℕ, c ≤ C + W₁ + W₂ → (c : ℝ) / (Nat.totient (l ^ k) : ℝ) ≤ ε := by
    intro c hc
    have h1 : (k₁ : ℝ) ≤ Nat.totient (l ^ k) := by
      have := le_totient_pow hl hk1
      exact_mod_cast (by omega : k₁ ≤ Nat.totient (l ^ k))
    have h2 : (0 : ℝ) < Nat.totient (l ^ k) := by
      have := le_totient_pow hl hk1
      exact_mod_cast (by omega : 0 < Nat.totient (l ^ k))
    have h3 : (c : ℝ) ≤ ((C + W₁ + W₂ : ℕ) : ℝ) := by exact_mod_cast hc
    rw [div_le_iff₀ hε] at hk₁
    rw [div_le_iff₀ h2]
    nlinarith
  refine ⟨M, k, e, by omega, hk1, by omega, fun q => ⟨?_, ?_⟩, ?_⟩
  · have h1 : e q < l ^ e q := Nat.lt_pow_self hl.one_lt
    have := hC' q
    omega
  · have := hsm (l ^ e q) (by have := hC' q; omega)
    rwa [Nat.cast_pow] at this
  intro O' _ _ _ _ _ hinj ζ hζ
  constructor
  · intro x
    letI : Algebra O₀ O' := ((algebraMap O O').comp (algebraMap O₀ O)).toAlgebra
    haveI : IsScalarTower O₀ O O' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsLocalHom (algebraMap O₀ O') :=
      RingHom.isLocalHom_comp (algebraMap O O') (algebraMap O₀ O)
    have h := hb₁ k hk1 hkB.1 O' (hinj.comp hinj₀) ζ hζ x
    rw [aeval_subst] at h
    rw [MvPolynomial.aeval_map_algebraMap]
    exact ⟨h.1, h.2.trans (add_le_add le_rfl (hsm W₁ (by omega)))⟩
  · intro y
    have h := hb₂ k hk1 hkB.2 O' hinj ζ hζ y
    rw [aeval_subst] at h
    exact ⟨h.1, h.2.trans (add_le_add le_rfl (hsm W₂ (by omega)))⟩

end GlobalTheory.OrderEval
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants : ∀ (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Finite (IsLocalRing.ResidueField O₀)] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)], Function.Injective (algebraMap O₀ O) → ∀ (l : ℕ), l.Prime → (l : O₀) ≠ 0 → ¬ IsUnit (l : O₀) → ∀ (R D nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : I → ℕ) (v : J → ℕ) (F : ℕ → I → MvPolynomial (Fin R ⊕ Fin R) O₀) (f Dd g : ℕ → J → MvPolynomial (Fin R ⊕ Fin R) O), (∀ M, M₀ ≤ M → ∀ x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ D ∧ IsDiscreteValuationRing.addVal O₀ ((F M x).coeff m) ≤ μ x) → (∀ M, M₀ ≤ M → ∀ y, f M y - Dd M y * g M y ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪ Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧ IsDiscreteValuationRing.addVal O ((g M y).coeff 0) ≤ v y ∧ ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧ (Dd M y).map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈ Ideal.span (Set.range fun q => (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))) → ∀ ε : ℝ, 0 < ε → ∃ (M k : ℕ) (e : Fin R ⊕ Fin R → ℕ), M₀ ≤ M ∧ 1 ≤ k ∧ k ≤ M ∧ (∀ q, e q < k ∧ (l : ℝ) ^ e q / (Nat.totient (l ^ k) : ℝ) ≤ ε) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → (∀ x, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O)) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O))) ≤ (μ x : ℝ) / ((IsDiscreteValuationRing.addVal O₀ (l : O₀)).toNat : ℝ) + ε) ∧ (∀ y, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y)) ≤ (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) + ε) := by
  atlas_forward_decl GlobalTheory.OrderEval.order_eval
end
