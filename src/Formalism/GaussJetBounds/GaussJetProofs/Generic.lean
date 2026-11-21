import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementM
import Formalism.GaussJetBounds.StatementK
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.GaussJetBounds.StatementB

section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem frameA_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero,
      norm_zero]
    exact norm_nonneg _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hV : ‖∑ b ∈ S, U b‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)
    obtain ⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) =
        U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by
      refine ⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖U a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU a)
      have h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
      have h3 := IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)
      calc ‖U a‖ ^ k * ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) * ‖(((l ^ e).choose k / l : ℕ) : K)‖
          ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) =
        ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R := by
      rw [hReq]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖R‖ ≤ ‖(l : K)‖ * 1 := by gcongr
      _ = ‖(l : K)‖ := mul_one _

theorem frameA_letter {K : Type u} [NormedField K] [IsUltrametricDist K] (J N0 : ℕ)
    (lam : Fin J → Fin N0 → K) (y : Fin N0 → Fin N0 → K) (hlam : ∀ i a, ‖lam i a‖ ≤ 1)
    (hy : ∀ k a, ‖y k a‖ ≤ 1) (e : Fin J → Fin N0) (he : Function.Injective e)
    (top : Fin N0 → Prop) [DecidablePred top] (htop : ∀ i, ¬ top (e i))
    (hdet : ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1) :
    ∃ (x T : Fin N0 → Fin N0 → K), (∀ k a, ‖x k a‖ ≤ 1) ∧ (∀ i k, ‖T i k‖ ≤ 1) ∧
      (∀ k a, top k → x k a = y k a) ∧
      (∀ i a, ¬ top i → y i a = ∑ k, (if top k then 0 else T i k) * x k a) ∧
      (∀ i k, ¬ top k → k ≠ e i → ∑ a, lam i a * x k a = 0) := by
  classical
  set A : Matrix (Fin J) (Fin J) K := Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a
    with hA
  let c : Fin N0 → Fin J → K := fun k i => ∑ a, lam i a * y k a
  have hc : ∀ k i, ‖c k i‖ ≤ 1 := fun k i =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => by
      rw [norm_mul]; exact mul_le_one₀ (hlam i a) (norm_nonneg _) (hy k a))
  have hAc : ∀ i i', A i i' = c (e i') i := fun _ _ => rfl
  have hAint : ∀ i i', ‖A i i'‖ ≤ 1 := fun i i' => hc _ _
  have hAinv : ∀ i i', ‖A⁻¹ i i'‖ ≤ 1 := norm_inv_entry_le_one A hAint hdet
  have hne : A.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  let z : Fin J → Fin N0 → K := fun i' a => ∑ i'', A⁻¹ i'' i' * y (e i'') a
  have hz : ∀ i a, ‖z i a‖ ≤ 1 := fun i a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i'' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hAinv _ _) (norm_nonneg _) (hy _ _))
  have hcz : ∀ k a, ‖∑ i', c k i' * z i' a‖ ≤ 1 := fun k a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hc _ _) (norm_nonneg _) (hz _ _))

  have hlz : ∀ i i', ∑ a, lam i a * z i' a = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ a, lam i a * z i' a = ∑ i'', A i i'' * A⁻¹ i'' i' := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i'' _ => ?_)
      rw [hAc]
      simp only [c, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]

  have hzy : ∀ i'' a, ∑ i', c (e i'') i' * z i' a = y (e i'') a := by
    intro i'' a
    have h1 : ∑ i', c (e i'') i' * z i' a = ∑ m, (∑ i', A⁻¹ m i' * A i' i'') * y (e m) a := by
      simp only [z, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i' _ => ?_))
      rw [hAc]; ring
    rw [h1]
    simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
    simp
  let x : Fin N0 → Fin N0 → K := fun k a =>
    if top k then y k a else if h : ∃ i, e i = k then z h.choose a
      else y k a - ∑ i', c k i' * z i' a
  let T : Fin N0 → Fin N0 → K := fun i k =>
    (if (∃ i', e i' = i) then 0 else if k = i then 1 else 0) + ∑ i', if k = e i' then c i i' else 0
  have hxe : ∀ i a, x (e i) a = z i a := by
    intro i a
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    have hch : hex.choose = i := he hex.choose_spec
    simp only [x]
    rw [if_neg (htop i), dif_pos hex, hch]
  have hxn : ∀ k a, ¬ top k → (¬ ∃ i, e i = k) → x k a = y k a - ∑ i', c k i' * z i' a := by
    intro k a h1 h2
    simp only [x]
    rw [if_neg h1, dif_neg h2]
  have hsumT : ∀ i k, (∑ i', if k = e i' then c i i' else 0) = 0 ∨
      ∃ i', (∑ i', if k = e i' then c i i' else 0) = c i i' := by
    intro i k
    by_cases h : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h
      right
      refine ⟨i0, ?_⟩
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (he h).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · left
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [if_neg (fun hk => h ⟨i', hk.symm⟩)]
  refine ⟨x, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro k a
    by_cases h1 : top k
    · simp only [x]; rw [if_pos h1]; exact hy _ _
    · by_cases h2 : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := h2
        rw [hxe]; exact hz _ _
      · rw [hxn k a h1 h2, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ _) ?_)
        rw [norm_neg]; exact hcz _ _
  · intro i k
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · rcases hsumT i k with h | ⟨i', h⟩
      · rw [h]; simp
      · rw [h]; exact hc _ _
  · intro k a h1
    simp only [x]; rw [if_pos h1]
  · intro i a hi
    have hT0 : ∀ k, (if top k then 0 else T i k) = T i k := by
      intro k
      split_ifs with hk
      · symm
        have h1 : k ≠ i := fun h => hi (h ▸ hk)
        have h2 : (∑ i', if k = e i' then c i i' else 0) = 0 :=
          Finset.sum_eq_zero (fun i' _ => by
            rw [if_neg (fun h : k = e i' => htop i' (h ▸ hk))])
        simp only [T]
        rw [h2, if_neg h1]
        simp
      · rfl
    simp only [hT0]
    have hsecond : ∑ k, (∑ i', if k = e i' then c i i' else 0) * x k a = ∑ i', c i i' * z i' a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Finset.sum_eq_single (e i')]
      · rw [if_pos rfl, hxe]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [T, add_mul, Finset.sum_add_distrib]
    rw [hsecond]
    by_cases h2 : ∃ i', e i' = i
    · simp only [if_pos h2, zero_mul, Finset.sum_const_zero, zero_add]
      obtain ⟨i0, rfl⟩ := h2
      exact (hzy i0 a).symm
    · simp only [if_neg h2]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hxn i a hi h2]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro i k hk hne'
    by_cases h2 : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h2
      simp only [hxe]
      rw [hlz, if_neg (fun h : i = i0 => hne' (h ▸ rfl))]
    · simp only [hxn k _ hk h2, mul_sub, Finset.sum_sub_distrib]
      have h3 : ∑ a, lam i a * ∑ i', c k i' * z i' a = ∑ i', c k i' * ∑ a, lam i a * z i' a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => by ring))
      rw [h3]
      simp only [hlz]
      simp [c]

theorem thmAFrame_of : ThmAGen.{u} → ThmAFrame.{u} := by
  intro hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa J lab hlabinj hlab lam hlam hlampos hlamneg
    e he hetop hdet
  classical
  have hL := fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s)
    (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)
  choose xs T hxs hT hxtop hrec hdual using hL
  let x : ZMod d × Fin N0 × Fin N0 → K := fun y => xs y.1 y.2.1 y.2.2
  let spec : ZMod d × Fin N0 → Option (ZMod d × ℤ) := fun r =>
    if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none
  have hspec_e : ∀ s i, spec (s, e s i) = some (lab s i) := by
    intro s i
    have hex : ∃ i', e s i' = e s i := ⟨i, rfl⟩
    have hch : hex.choose = i := he s hex.choose_spec
    show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _
    rw [dif_pos hex, hch]
  have hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i := by
    intro s k h
    by_contra hcon
    apply h
    show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _
    rw [dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]
  refine hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU
    ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec ?_ ?_ ?_
  · intro s i b
    by_cases hi : s ∈ TT ∧ i.val = 0
    · simp only [effMat, if_pos hi]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
        exact (hxtop s i b hi).symm
      · intro k _ hk
        rw [if_neg hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [effMat, if_neg hi]
      exact hrec s i b hi
  · intro s k s0 j hsp
    obtain ⟨i, rfl⟩ := hspec_some s k (by rw [hsp]; simp)
    rw [hspec_e] at hsp
    have hlb : lab s i = (s0, j) := Option.some.inj hsp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hlab s s0 j).mp ⟨i, hlb⟩
    exact ⟨h1, h2, h3, hetop s i, h4, h5⟩
  · rintro ⟨s, k⟩ ⟨s', k'⟩ hne heq
    obtain ⟨i, rfl⟩ := hspec_some s k hne
    obtain ⟨i', rfl⟩ := hspec_some s' k' (by rw [← heq]; exact hne)
    rw [hspec_e, hspec_e] at heq
    have hlb : lab s i = lab s' i' := Option.some.inj heq
    have e1 := ((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1
    have e2 := ((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1
    have hss : s = s' := by rw [e1, e2, hlb]
    subst hss
    have hii : i = i' := hlabinj s hlb
    rw [hii]
  · intro s0 hs0 s k j hk hj hs hpos hneg hsp
    obtain ⟨i, hi⟩ := (hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩
    have hki : k ≠ e s i := by
      intro h
      apply hsp
      rw [h, hspec_e, hi]
    have hzero : ∑ b, lam s i b * xs s k b = 0 := hdual s i k hk hki
    have hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b) := fun b =>
      hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩
    have hi1 : (lab s i).1 = s0 := by rw [hi]
    have hi2 : (lab s i).2 = j := by rw [hi]
    split_ifs with hj0
    · have hjpos : 0 < j := by
        rcases hj with ⟨m, hm⟩
        omega
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b := by
        intro b
        have := hlampos s i b (by rw [hi2]; exact hjpos)
        rw [hi1, hi2] at this
        rw [this, hx0]
      simp only [hl1]
      show ‖∑ b, lam s i b * xs s k b‖ ≤ _
      rw [hzero, norm_zero]
      exact norm_nonneg _
    · have hjneg : j < 0 := not_le.mp hj0
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat) := by
        intro b
        have := hlamneg s i b (by rw [hi2]; exact hjneg)
        rw [hi1, hi2] at this
        rw [this, hx0]
      have hfr := frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by
        rw [norm_mul]; exact mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat
        Finset.univ
      rw [hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg] at hfr
      simp only [hl1]
      show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _
      simpa only [mul_pow] using hfr

theorem theorem_A_frame : ThmAFrame.{u} := thmAFrame_of thmAGen

end Formalism.DworkPowerSeriesWeights
end
end

section
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds






section Pure

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

def spLdeg (lt : ι → σ) (t : σ) (n : ι →₀ ℕ) : ℕ := ∑ k, if lt k = t then n k else 0





variable (lt : ι → σ) (N : σ → ι → R)



variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN






end Pure


section Minor

variable {R : Type*} [CommRing R] {m p : ℕ}

def spV (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    MvPolynomial (Fin m × Fin (p + 1)) R :=
  o.elim (MvPolynomial.C (top c)) (fun k => MvPolynomial.X (k, c))

def spEx (o : Option (Fin m)) (c : Fin (p + 1)) : Fin m × Fin (p + 1) →₀ ℕ :=
  o.elim 0 (fun k => Finsupp.single (k, c) 1)

def spCo (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) : R :=
  o.elim (top c) (fun _ => 1)




end Minor


end Formalism.DworkPowerSeriesWeights
end
end

section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem generic_mono_det {R : Type*} [CommRing R] [Nontrivial R] {d N0 n : ℕ} (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (γ : Fin n → Fin N0) (hγ : Function.Injective γ)
    (hL : ∀ i, L i ≠ 0) (hinj : Function.Injective fun i => (t i, L i)) :
    (Matrix.of fun (r c : Fin n) =>
      (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)).det ≠ 0 := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)) (σ i) i)
        = MvPolynomial.monomial (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) 1 := by
    intro σ
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [MvPolynomial.X_pow_eq_monomial]
  have hval : ∀ (f : Fin n → ZMod d) (g : Fin n → ℕ) (i : Fin n),
      (∑ j, Finsupp.single (f j, z, γ j) (g j)) (f i, z, γ i) = g i := by
    intro f g i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have hval2 : ∀ (i : Fin n) (u : ZMod d),
      (∑ j, Finsupp.single (t j, z, γ j) (L j)) (u, z, γ i) = if t i = u then L i else 0 := by
    intro i u
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · rw [Finsupp.single_apply]
      by_cases h : t i = u
      · simp [h]
      · rw [if_neg, if_neg h]
        intro h'
        exact h (Prod.ext_iff.mp h').1
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have key : ∀ σ : Equiv.Perm (Fin n),
      (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) = ∑ i, Finsupp.single (t i, z, γ i) (L i) → σ = 1 := by
    intro σ h
    ext i
    have h1 : (∑ j, Finsupp.single (t (σ j), z, γ j) (L (σ j))) (t (σ i), z, γ i)
        = (∑ j, Finsupp.single (t j, z, γ j) (L j)) (t (σ i), z, γ i) := by rw [h]
    rw [hval (fun j => t (σ j)) (fun j => L (σ j)) i, hval2] at h1
    by_cases ht : t i = t (σ i)
    · rw [if_pos ht] at h1
      have : σ i = i := hinj (Prod.ext ht.symm h1)
      simp [this]
    · rw [if_neg ht] at h1
      exact absurd h1 (hL (σ i))
  intro hdet
  have hc := congrArg (MvPolynomial.coeff (∑ i, Finsupp.single (t i, z, γ i) (L i))) hdet
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))] at hc
  · rw [hprod] at hc
    simp at hc
  · intro σ _ hσ
    rw [hprod, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg]
    · simp
    · exact fun h => hσ (key σ h)
  · simp

theorem generic_minor_norm {K : Type u} [NormedField K] {l d N0 n : ℕ} (hl : l.Prime)
    (Y : ZMod d × Fin N0 × Fin N0 → K) (hY : IsGeneric l Y) (s : ZMod d) (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (e : Fin n → Fin N0) (he : Function.Injective e)
    (hn : n ≤ N0) (hts : ∀ i, t i ≠ s) (hL : ∀ i, L i ≠ 0)
    (hinj : Function.Injective fun i => (t i, L i)) :
    ‖(Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det‖ = 1 := by
  classical
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  set P : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℤ := (Matrix.of fun (i i' : Fin n) =>
    ∑ a, MvPolynomial.X (t i, z, a) ^ (L i) * MvPolynomial.X (s, e i', a)).det with hP
  have hev : MvPolynomial.aeval Y P
      = (Matrix.of fun (i i' : Fin n) => ∑ a, Y (t i, z, a) ^ (L i) * Y (s, e i', a)).det := by
    rw [hP, AlgHom.map_det]
    congr 1
    ext i i'
    simp
  rw [← hev]
  refine hY P ?_
  intro h0
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod l)) P = (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a)).det := by
    rw [hP, RingHom.map_det]
    congr 1
    ext i i'
    simp
  rw [hmap] at h0
  let f : ZMod d × Fin N0 × Fin N0 → MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l) :=
    fun v => if v.1 = s then (if v.2.1 = v.2.2 then 1 else 0) else MvPolynomial.X v
  have h1 := congrArg (MvPolynomial.bind₁ f) h0
  rw [map_zero, AlgHom.map_det] at h1
  have h2 : (MvPolynomial.bind₁ f).mapMatrix (Matrix.of fun (i i' : Fin n) =>
      ∑ a, (MvPolynomial.X (t i, z, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L i)
        * MvPolynomial.X (s, e i', a))
      = Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, e c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) (ZMod l)) ^ (L r) := by
    ext i i'
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_pow,
      MvPolynomial.bind₁_X_right, f, if_neg (hts i), if_true]
    rw [Finset.sum_eq_single (e i')]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  rw [h2] at h1
  exact generic_mono_det z t L e he hL hinj h1

theorem generic_norm_one {K : Type u} [NormedField K] {σ : Type} {l : ℕ} (hl : l.Prime)
    (Y : σ → K) (hY : IsGeneric l Y) (y : σ) : ‖Y y‖ = 1 := by
  haveI : Fact (1 < l) := ⟨hl.one_lt⟩
  have h := hY (MvPolynomial.X y) (by
    rw [MvPolynomial.map_X]
    exact MvPolynomial.X_ne_zero y)
  simpa using h

theorem theorem_A_generic : ThmAGeneric.{u} := by
  intro K _ _ _ l d N0 N1 _ hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab hJ m hm
  classical
  have hYn : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hxg : ∀ y, ‖genFrame TT l m Y y‖ ≤ 1 := by
    intro y
    simp only [genFrame]
    split_ifs <;> simp [norm_pow, hYn]
  have hw : ∀ s (i : Fin (J s)), (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧
      s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) := by
    intro s i
    have := (hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hxg0 : ∀ s0 ∈ TT, ∀ a, genFrame TT l m Y (s0, ⟨0, h0⟩, a) = Y (s0, ⟨0, h0⟩, a) ^ l ^ m := by
    intro s0 hs0 a
    simp [genFrame, hs0]
  let E : (s : ZMod d) → Fin (J s) → ℕ := fun s i => ((m : ℤ) + (lab s i).2).toNat
  let lam : (s : ZMod d) → Fin (J s) → Fin N0 → K := fun s i a => Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ E s i
  have hlam1 : ∀ s i a, ‖lam s i a‖ ≤ 1 := by
    intro s i a
    simp [lam, norm_pow, hYn]
  have hpos : ∀ s i a, 0 < (lab s i).2 →
      lam s i a = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ (lab s i).2.toNat := by
    intro s i a hj
    rw [hxg0 _ (hw s i).1, ← pow_mul, ← pow_add]
    simp only [lam, E]
    congr 2
    omega
  have hneg : ∀ s i a, (lab s i).2 < 0 →
      lam s i a ^ l ^ (-(lab s i).2).toNat = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) := by
    intro s i a hj
    have hmm := hm s i
    rw [hxg0 _ (hw s i).1]
    simp only [lam, E]
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  let e : (s : ZMod d) → Fin (J s) → Fin N0 := fun s i =>
    ⟨i + (if s ∈ TT then 1 else 0), by
      have h := hJ s
      have hi := i.isLt
      split_ifs at h ⊢ <;> omega⟩
  have he_inj : ∀ s, Function.Injective (e s) := by
    intro s i i' h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [e] at h'
    omega
  have he0 : ∀ s i, ¬(s ∈ TT ∧ ((e s i : Fin N0) : ℕ) = 0) := by
    intro s i h
    obtain ⟨hs, hz0⟩ := h
    simp [e, hs] at hz0
  have hdet : ∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) =>
      ∑ a : Fin N0, lam s i a * genFrame TT l m Y (s, e s i', a)).det‖ = 1 := by
    intro s
    have hx : ∀ i' a, genFrame TT l m Y (s, e s i', a) = Y (s, e s i', a) := by
      intro i' a
      simp only [genFrame]
      rw [if_neg (he0 s i')]
    simp only [hx]
    have hts : ∀ i, (lab s i).1 ≠ s := by
      intro i h
      obtain ⟨_, hodd, hss⟩ := hw s i
      rw [h] at hss
      have hx0 : (((lab s i).2 : ℤ) : ZMod d) = 0 := by simpa using hss
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
      have hev : Even ((d : ℕ) : ℤ) := (Int.even_coe_nat d).mpr he
      obtain ⟨k, hk⟩ := hdvd
      have : Even (lab s i).2 := by
        rw [hk]
        exact hev.mul_right k
      exact (Int.not_even_iff_odd.mpr hodd) this
    have hLn : ∀ i, l ^ E s i ≠ 0 := fun i => pow_ne_zero _ hl.ne_zero
    have hinj' : Function.Injective fun i => ((lab s i).1, l ^ E s i) := by
      intro i i' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨ha1, ha2⟩ := h
      have hE := Nat.pow_right_injective hl.two_le ha2
      simp only [E] at hE
      have hm1 := hm s i
      have hm2 := hm s i'
      have ho1 := (hw s i).2.1
      have ho2 := (hw s i').2.1
      have hn1 : (lab s i).2 ≠ 0 := fun h => by rw [h] at ho1; exact absurd ho1 (by decide)
      have hn2 : (lab s i').2 ≠ 0 := fun h => by rw [h] at ho2; exact absurd ho2 (by decide)
      have hj : (lab s i).2 = (lab s i').2 := by omega
      exact hinj s (Prod.ext ha1 hj)
    have hn : J s ≤ N0 := by
      have h := hJ s
      split_ifs at h <;> omega
    exact generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (fun i => l ^ E s i) (e s)
      (he_inj s) hn hts hLn hinj'
  exact theorem_A_frame K l d N0 N1 hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I
    (genFrame TT l m Y) hxg nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab lam hlam1 hpos hneg e he_inj he0 hdet

end Formalism.DworkPowerSeriesWeights
end
end
