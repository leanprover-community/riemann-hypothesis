import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.Development

section
open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

theorem ptp_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  set L := ℓ ^ n.factorization ℓ with hL
  set m := n / L with hm
  have hcop : Nat.Coprime L m := by
    have := Nat.coprime_ordCompl hℓ hx.ne'
    exact Nat.Coprime.pow_left _ this
  have hnm : L * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have : NeZero m := ⟨by intro h0; rw [h0, mul_zero] at hnm; omega⟩
  set u := (((L : ℕ) : ZMod m)⁻¹).val with hu
  have hmod : L * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hu, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one L hcop
  have hptp : primeToPart ℓ x = x ^ (L * u) := rfl
  rw [hptp, ← pow_mul, ← pow_mod_orderOf x L, ← pow_mod_orderOf x (L * u * L)]
  congr 1
  show L ≡ L * u * L [MOD orderOf x]
  rw [← hn, ← hnm]
  have := Nat.ModEq.mul_left' L hmod
  rw [mul_one] at this
  rw [mul_comm (L * u) L]
  exact this.symm

theorem ptp_eq_imp {M : Type*} [CommMonoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : M)
    (hx : 0 < orderOf x) (hy : 0 < orderOf y) (h : primeToPart ℓ x = primeToPart ℓ y) :
    ∃ j, x ^ (ℓ ^ j) = y ^ (ℓ ^ j) := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  rw [pow_add, pow_mul, ptp_pow ℓ hℓ x hx, h, ← pow_mul, mul_comm, pow_mul,
    ← ptp_pow ℓ hℓ y hy, ← pow_mul, ← pow_add, add_comm]

open Classical in

theorem card_ppRoots_le {K : Type*} [Field K] (N : ℕ) (hN : 2 ≤ N) :
    ((Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1)).card ≤ ppSum N := by
  have hN0 : 0 < N := by omega
  have hsub : (Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1) ⊆
      N.primeFactors.biUnion (fun p => Polynomial.nthRootsFinset (p ^ N.factorization p) (1 : K)) := by
    intro y hy
    rw [Finset.mem_filter, Polynomial.mem_nthRootsFinset hN0] at hy
    obtain ⟨hyN, ℓ, hℓ, j, hj⟩ := hy
    rw [Finset.mem_biUnion]
    have hdvd : orderOf y ∣ ℓ ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
    have hoN : orderOf y ∣ N := orderOf_dvd_of_pow_eq_one hyN
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    ·
      have hy1 : y = 1 := by
        rw [h0, pow_zero, orderOf_eq_one_iff] at hoi; exact hoi
      refine ⟨N.minFac, ?_, ?_⟩
      · exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd N, by omega⟩
      · rw [Polynomial.mem_nthRootsFinset (pow_pos (Nat.minFac_pos N) _), hy1, one_pow]
    · have hℓN : ℓ ^ i ∣ N := hoi ▸ hoN
      have hmem : ℓ ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hℓ, (dvd_pow_self ℓ hpos.ne').trans hℓN, by omega⟩
      refine ⟨ℓ, hmem, ?_⟩
      rw [Polynomial.mem_nthRootsFinset (pow_pos hℓ.pos _)]
      rw [← orderOf_dvd_iff_pow_eq_one, hoi]
      exact pow_dvd_pow ℓ ((hℓ.pow_dvd_iff_le_factorization (by omega)).1 hℓN)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  unfold ppSum
  refine Finset.sum_le_sum (fun p hp => ?_)
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

end PI.SqfRootShift.W
end
end

section
open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

theorem frob_fix (x : Fbar g) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hfr := IntermediateField.adjoin.finrank hint
  have : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let _ := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  have hc : Fintype.card (IntermediateField.adjoin (ZMod g) {x}) =
      g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod g), Nat.card_zmod, hfr]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ :
      IntermediateField.adjoin (ZMod g) {x})
  rw [hc] at h
  exact congrArg Subtype.val h

def Good (c : (ZMod g)ˣ) (P : (ZMod g)[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ j : ℕ,
    P ∣ X ^ (ℓ ^ j) - C ((c : ZMod g) ^ (ℓ ^ j))

theorem aeval_eq_zero_of_dvd' {P Q : (ZMod g)[X]} (h : P ∣ Q) {z : Fbar g}
    (hz : aeval z P = 0) : aeval z Q = 0 := by
  obtain ⟨q, rfl⟩ := h
  simp [hz]

theorem good_root (c : (ZMod g)ˣ) (P : (ZMod g)[X]) (hP : Good c P) (z : Fbar g)
    (hz : z ∈ (P.map (algebraMap (ZMod g) (Fbar g))).roots) :
    (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (g ^ P.natDegree - 1) = 1 ∧
      ∃ ℓ, ℓ.Prime ∧ ∃ j, (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (ℓ ^ j) = 1 := by
  obtain ⟨hmon, hirr, ℓ, hℓ, j, hdvd⟩ := hP
  set c' := algebraMap (ZMod g) (Fbar g) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by
    rw [hc']; exact (_root_.map_ne_zero _).2 c.ne_zero
  have hz0 : aeval z P = 0 := by
    rw [mem_roots_map hmon.ne_zero] at hz
    rwa [aeval_def]
  have hmin : P = minpoly (ZMod g) z := minpoly.eq_of_irreducible_of_monic hirr hz0 hmon
  have hfix : z ^ (g ^ P.natDegree) = z := by rw [hmin]; exact frob_fix z
  have hℓj : z ^ (ℓ ^ j) = c' ^ (ℓ ^ j) := by
    have := aeval_eq_zero_of_dvd' hdvd hz0
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    rw [sub_eq_zero] at this
    exact this
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hℓ.pos j).ne'] at hℓj
    exact pow_ne_zero _ hc0 hℓj.symm
  have hcfix : c' ^ (g ^ P.natDegree) = c' := by
    rw [hc', ← map_pow, ZMod.pow_card_pow]
  set y := z * c'⁻¹ with hy
  have hy0 : y ≠ 0 := mul_ne_zero hzne (inv_ne_zero hc0)
  have hyfix : y ^ (g ^ P.natDegree) = y := by
    rw [hy, mul_pow, inv_pow, hfix, hcfix]
  have hpos : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  refine ⟨?_, ℓ, hℓ, j, ?_⟩
  · have h2 : y ^ (g ^ P.natDegree - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hyfix, one_mul]
    exact mul_right_cancel₀ hy0 h2
  · rw [hy, mul_pow, inv_pow, hℓj, mul_inv_cancel₀ (pow_ne_zero _ hc0)]

end PI.SqfRootShift.W
end
end

section
open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

open Classical in

theorem count_good (c : (ZMod g)ˣ) (hg : 3 ≤ g) (k : ℕ) (hk : 1 ≤ k)
    (Q : Finset (ZMod g)[X]) (hQ : ∀ P ∈ Q, Good c P ∧ P.natDegree = k) :
    k * Q.card ≤ ppSum (g ^ k - 1) := by
  set alg := algebraMap (ZMod g) (Fbar g) with halg
  set c' := alg (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := (_root_.map_ne_zero _).2 c.ne_zero
  set R : (ZMod g)[X] → Finset (Fbar g) := fun P => (P.map alg).roots.toFinset with hRdef
  have hR : ∀ P ∈ Q, (R P).card = k := by
    intro P hP
    obtain ⟨⟨hmon, hirr, -⟩, hdeg⟩ := hQ P hP
    have hsep : (P.map alg).Separable := (PerfectField.separable_of_irreducible hirr).map
    rw [hRdef, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  have hdisj : (Q : Set (ZMod g)[X]).PairwiseDisjoint R := by
    intro P hP P' hP' hne
    refine Finset.disjoint_left.2 (fun z hz hz' => hne ?_)
    obtain ⟨⟨hmon, hirr, -⟩, -⟩ := hQ P hP
    obtain ⟨⟨hmon', hirr', -⟩, -⟩ := hQ P' hP'
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon.ne_zero] at hz
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon'.ne_zero] at hz'
    rw [minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr
        (by rw [aeval_def]; exact hz) hmon,
      minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr'
        (by rw [aeval_def]; exact hz') hmon']
  have hcard : (Q.biUnion R).card = k * Q.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hR, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hgk : g ≤ g ^ k := Nat.le_self_pow (by omega) g
  have hN : 2 ≤ g ^ k - 1 := by omega
  rw [← hcard]
  refine le_trans ?_ (card_ppRoots_le (K := Fbar g) (g ^ k - 1) hN)
  refine Finset.card_le_card_of_injOn (fun z => z * c'⁻¹) ?_ ?_
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    obtain ⟨hgood, hdeg⟩ := hQ P hP
    rw [hRdef, Multiset.mem_toFinset] at hzP
    have h := good_root c P hgood z hzP
    rw [hdeg] at h
    rw [Finset.mem_coe, Finset.mem_filter, Polynomial.mem_nthRootsFinset (by omega)]
    exact h
  · intro z1 _ z2 _ h
    exact mul_right_cancel₀ (inv_ne_zero hc0) h

theorem monic_ext {h1 h2 : (ZMod g)[X]} {m : ℕ} (hm1 : h1.Monic) (hm2 : h2.Monic)
    (hd1 : h1.natDegree = m) (hd2 : h2.natDegree = m)
    (hc : ∀ i < m, h1.coeff i = h2.coeff i) : h1 = h2 := by
  ext n
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact hc n hlt
  · have e1 : h1.coeff m = 1 := by rw [← hd1]; exact hm1.coeff_natDegree
    have e2 : h2.coeff m = 1 := by rw [← hd2]; exact hm2.coeff_natDegree
    rw [heq, e1, e2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem divByMonic_facts {r : ℕ} {f P : (ZMod g)[X]} (hf : IsLab g r f) (hP : P.Monic)
    (hdvd : P ∣ f) :
    f = P * (f /ₘ P) ∧ (f /ₘ P).Monic ∧ (f /ₘ P).natDegree = r - P.natDegree := by
  have hmod : f %ₘ P = 0 := (modByMonic_eq_zero_iff_dvd hP).2 hdvd
  have heq : f = P * (f /ₘ P) := by
    have := modByMonic_add_div f P
    rw [hmod, zero_add] at this
    exact this.symm
  refine ⟨heq, ?_, ?_⟩
  · apply hP.of_mul_monic_left
    rw [← heq]; exact hf.1
  · rw [natDegree_divByMonic f hP, hf.2.1]

open Classical in

theorem count_mult (r : ℕ) (T : Finset (ZMod g)[X]) (hT : ∀ f ∈ T, IsLab g r f)
    (P : (ZMod g)[X]) (hP : P.Monic) :
    (T.filter (fun f => P ∣ f)).card ≤ g ^ (r - P.natDegree) := by
  have hu : (Finset.univ : Finset (Fin (r - P.natDegree) → ZMod g)).card =
      g ^ (r - P.natDegree) := by
    simp [ZMod.card]
  rw [← hu]
  refine Finset.card_le_card_of_injOn (fun f (i : Fin (r - P.natDegree)) => (f /ₘ P).coeff i)
    ?_ ?_
  · intro f _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_coe, Finset.mem_filter] at hf1 hf2
    obtain ⟨e1, m1, d1⟩ := divByMonic_facts (hT f1 hf1.1) hP hf1.2
    obtain ⟨e2, m2, d2⟩ := divByMonic_facts (hT f2 hf2.1) hP hf2.2
    have hq : f1 /ₘ P = f2 /ₘ P := monic_ext m1 m2 d1 d2 (fun i hi => congrFun h ⟨i, hi⟩)
    rw [e1, e2, hq]

end PI.SqfRootShift.W
end
end

section
open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

theorem eiii_factor {g : ℕ} [Fact g.Prime] {r : ℕ} (c : (ZMod g)ˣ) {f : (ZMod g)[X]}
    (hf : Eiii g r c f) :
    ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r := by
  obtain ⟨hlab, -, hneg⟩ := hf
  push Not at hneg
  obtain ⟨ℓ, hℓ, -, x, hx, hxc⟩ := hneg
  have hf0 : f ≠ 0 := hlab.1.ne_zero
  have hxroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots_map hf0] at hx
    rw [aeval_def]; exact hx
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hPd : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hxroot
    exact hlab.2.2 ((_root_.map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).1 hxroot)
  have hfix := frob_fix x
  have hg2 := (Fact.out : g.Prime).two_le
  have hpos : 1 ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.one_le_pow _ _ (by omega)
  have hgk : g ≤ g ^ (minpoly (ZMod g) x).natDegree := Nat.le_self_pow (by omega) g
  have hxo : 0 < orderOf x := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩
    have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have hco : 0 < orderOf (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨g - 1, by omega, ?_⟩
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one]
  obtain ⟨j, hj⟩ := ptp_eq_imp ℓ hℓ x _ hxo hco hxc
  refine ⟨minpoly (ZMod g) x, ⟨minpoly.monic hint, minpoly.irreducible hint, ℓ, hℓ, j,
    minpoly.dvd _ _ ?_⟩, minpoly.dvd _ _ hxroot, hPd, ?_⟩
  · simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hj, sub_self]
  · have := natDegree_le_of_dvd (minpoly.dvd _ _ hxroot) hf0
    rw [hlab.2.1] at this
    exact this

theorem countP : CountP := by
  intro g r _ hg hr c T hT
  classical
  have hex : ∀ f ∈ T, ∃ P, Good c P ∧ P ∣ f ∧ 1 ≤ P.natDegree ∧ P.natDegree ≤ r :=
    fun f hf => eiii_factor c (hT f hf)
  choose! Pf hPf using hex
  have hlab : ∀ f ∈ T, IsLab g r f := fun f hf => (hT f hf).1
  have h1 : T.card ≤ ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) := by
    rw [Finset.card_eq_sum_card_image Pf T]
    refine Finset.sum_le_sum (fun P hP => ?_)
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    refine le_trans (Finset.card_le_card ?_) (count_mult r T hlab (Pf f0) (hPf f0 hf0).1.1)
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, hf.2 ▸ (hPf f hf.1).2.1⟩
  have hmaps : ∀ P ∈ T.image Pf, P.natDegree ∈ Finset.Icc 1 r := by
    intro P hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_Icc.2 ⟨(hPf f0 hf0).2.2.1, (hPf f0 hf0).2.2.2⟩
  have h2 : ∑ P ∈ T.image Pf, g ^ (r - P.natDegree) = ∑ k ∈ Finset.Icc 1 r,
      ((T.image Pf).filter (fun P => P.natDegree = k)).card * g ^ (r - k) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]),
      Finset.sum_const, smul_eq_mul]
  have h3 : ∀ k ∈ Finset.Icc 1 r,
      k * ((T.image Pf).filter (fun P => P.natDegree = k)).card ≤ ppSum (g ^ k - 1) := by
    intro k hk
    refine count_good c hg k (Finset.mem_Icc.1 hk).1 _ (fun P hP => ?_)
    rw [Finset.mem_filter] at hP
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hP.1
    exact ⟨(hPf f0 hf0).1, hP.2⟩
  have h12 : (T.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 r,
      (((T.image Pf).filter (fun P => P.natDegree = k)).card : ℝ) * (g : ℝ) ^ (r - k) := by
    have := h1.trans h2.le
    exact_mod_cast this
  refine h12.trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [le_div_iff₀ (by linarith)]
  have := h3 k hk
  rw [mul_comm]
  exact_mod_cast this

end PI.SqfRootShift.W
end
end
