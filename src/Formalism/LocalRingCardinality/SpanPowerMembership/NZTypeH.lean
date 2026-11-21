import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
import Mathlib
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms

theorem pow_primeToPart {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    primeToPart ℓ x ^ (ℓ ^ (orderOf x).factorization ℓ) = x ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  have hn0 : n ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  set a := n.factorization ℓ
  set m := n / ℓ ^ a with hm
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hc : Nat.Coprime (ℓ ^ a) m := (Nat.coprime_ordCompl hℓ hn0).pow_left a
  set u := (((ℓ ^ a : ℕ) : ZMod m)⁻¹).val
  have h1 : ((ℓ ^ a * u : ℕ) : ZMod m) = 1 := by
    have hm0 : NeZero m := ⟨fun h => hn0 (by rw [← hnm, h, mul_zero])⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hc
  have h2 : ℓ ^ a * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, h1, Nat.cast_one]
  unfold primeToPart
  rw [← pow_mul]
  have h3 : ℓ ^ a * u * ℓ ^ a ≡ ℓ ^ a [MOD n] := by
    have := h2.mul_left' (ℓ ^ a)
    rw [mul_one, hnm] at this
    rwa [mul_comm (ℓ ^ a * u) (ℓ ^ a)]
  rw [← pow_mod_orderOf x (ℓ ^ a * u * ℓ ^ a), ← pow_mod_orderOf x (ℓ ^ a)]
  exact congrArg _ h3

theorem exists_pow_eq {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x y : M) (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart ℓ x = primeToPart ℓ y) : ∃ c : ℕ, x ^ ℓ ^ c = y ^ ℓ ^ c := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  have h1 := pow_primeToPart hℓ x hx
  have h2 := pow_primeToPart hℓ y hy
  rw [pow_add, pow_mul, ← h1, h, ← pow_mul, mul_comm, pow_mul, h2, ← pow_mul]

theorem exc_of_dvd {g d e ℓ c : ℕ} (hg : 2 ≤ g) (hℓ : ℓ.Prime) (hd : 1 ≤ d) (he : 2 * Nat.gcd d e ≤ d)
    (h : g ^ d - 1 ∣ ℓ ^ c * (g ^ e - 1)) : Exc g d ℓ := by
  refine ⟨hℓ, ?_⟩
  set G := g ^ d with hG
  have hG3 : 3 ≤ G := by
    have h2 : 2 ≤ d := by
      have : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
      omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
      _ ≤ g ^ d := Nat.pow_le_pow_right (by omega) h2
  have hn0 : G - 1 ≠ 0 := by omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set v := padicValNat ℓ (G - 1) with hv
  have hfac : (G - 1).factorization ℓ = v := Nat.factorization_def _ hℓ
  set B := (G - 1) / ℓ ^ v with hB
  have hAB : ℓ ^ v * B = G - 1 := by
    have := Nat.ordProj_mul_ordCompl_eq_self (G - 1) ℓ
    rwa [hfac] at this
  have hcop : Nat.Coprime ℓ B := by
    have := Nat.coprime_ordCompl hℓ hn0
    rwa [hfac] at this
  have hB1 : B ∣ g ^ e - 1 :=
    (Nat.Coprime.pow_left c hcop).symm.dvd_of_dvd_mul_left ((Dvd.intro_left _ hAB).trans h)
  have hB2 : B ∣ g ^ Nat.gcd d e - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (Dvd.intro_left _ hAB) hB1
  set s := Nat.gcd d e
  have hs1 : 1 ≤ s := Nat.gcd_pos_of_pos_left e hd
  have hgs : 2 ≤ g ^ s := le_trans hg (Nat.le_self_pow (by omega) g)
  have hBle : B ≤ g ^ s - 1 := Nat.le_of_dvd (by omega) hB2
  have hBsq : B * B ≤ G - 1 := by
    have h1 : g ^ s * g ^ s ≤ G := by
      rw [← pow_add, hG]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : B * B ≤ (g ^ s - 1) * (g ^ s - 1) := Nat.mul_le_mul hBle hBle
    have h3 : (g ^ s - 1) * (g ^ s - 1) + 1 ≤ g ^ s * g ^ s := by
      obtain ⟨t, ht⟩ : ∃ t, g ^ s = t + 2 := ⟨g ^ s - 2, by omega⟩
      rw [ht]; simp only [show t + 2 - 1 = t + 1 by omega]; nlinarith
    omega
  set A := ℓ ^ v
  have hA2 : G - 1 ≤ A * A := by
    have h1 : (A * A) * (B * B) = (G - 1) * (G - 1) := by rw [← hAB]; ring
    by_contra hlt
    push Not at hlt
    have hBpos : 0 < B * B := by
      rcases Nat.eq_zero_or_pos (B * B) with h0 | h0
      · rw [h0, mul_zero] at h1
        have : 0 < (G - 1) * (G - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · exact h0
    have : (A * A) * (B * B) < (G - 1) * (G - 1) :=
      calc (A * A) * (B * B) < (G - 1) * (B * B) := Nat.mul_lt_mul_of_pos_right hlt hBpos
        _ ≤ (G - 1) * (G - 1) := Nat.mul_le_mul_left _ hBsq
    omega
  have hA4 : ℓ ^ (4 * v) = (A * A) * (A * A) := by
    show ℓ ^ (4 * v) = (ℓ ^ v * ℓ ^ v) * (ℓ ^ v * ℓ ^ v)
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hA4]
  have h5 : (G - 1) * (G - 1) ≤ (A * A) * (A * A) := Nat.mul_le_mul hA2 hA2
  have h6 : G < (G - 1) * (G - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, G = t + 3 := ⟨G - 3, by omega⟩
    rw [ht]; simp only [show t + 3 - 1 = t + 2 by omega]; nlinarith
  omega

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder

variable {g : ℕ} [hg : Fact g.Prime]

theorem one_lt_pow_g {d : ℕ} (hd : 1 ≤ d) : 2 ≤ g ^ d := by
  calc 2 ≤ g := hg.out.two_le
    _ ≤ g ^ d := Nat.le_self_pow (by omega) g

theorem coprime_n (d : ℕ) (hd : 1 ≤ d) : Nat.Coprime (g ^ d - 1) g := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hg.out]
  intro h
  have h2 : g ∣ g ^ d := dvd_pow_self g (by omega)
  have h3 := Nat.dvd_sub h2 h
  have h4 : g ^ d - (g ^ d - 1) = 1 := by
    have := one_lt_pow_g (g := g) hd
    omega
  rw [h4] at h3
  exact hg.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_gen (d : ℕ) (hd : 1 ≤ d) : ∃ u : (Fbar g)ˣ, orderOf u = g ^ d - 1 := by
  classical
  haveI : Fintype (GaloisField g d) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := (GaloisField g d)ˣ)
  let φ : GaloisField g d →ₐ[ZMod g] Fbar g := IsAlgClosed.lift
  refine ⟨Units.map φ.toRingHom.toMonoidHom x, ?_⟩
  rw [orderOf_injective (Units.map φ.toRingHom.toMonoidHom) (Units.map_injective φ.toRingHom.injective) x,
    orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units]
  congr 1
  first
    | exact GaloisField.card g d (by omega)
    | (rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g d (by omega))
    | simpa [Nat.card_eq_fintype_card] using GaloisField.card g d (by omega)

variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)

include hd hu in
theorem pow_gd : u ^ (g ^ d) = u := by
  have := one_lt_pow_g (g := g) hd
  rw [show g ^ d = g ^ d - 1 + 1 by omega, pow_succ, ← hu, pow_orderOf_eq_one, one_mul]

include hd hu in
theorem pow_g_add (j : ℕ) : u ^ (g ^ (j + d)) = u ^ (g ^ j) := by
  rw [pow_add, mul_comm, pow_mul, pow_gd hd u hu]

include hd hu in

theorem dvd_of_pow_eq {i j a : ℕ} (hij : i ≤ j) (h : u ^ (g ^ i * a) = u ^ (g ^ j * a)) :
    g ^ d - 1 ∣ a * (g ^ (j - i) - 1) := by
  rw [pow_eq_pow_iff_modEq, hu] at h
  have hle : g ^ i * a ≤ g ^ j * a := Nat.mul_le_mul_right a (Nat.pow_le_pow_right hg.out.pos hij)
  have h1 : g ^ d - 1 ∣ g ^ j * a - g ^ i * a := (Nat.modEq_iff_dvd' hle).1 h
  have hp : 1 ≤ g ^ (j - i) := Nat.one_le_pow _ _ hg.out.pos
  have hgj : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  have h2 : g ^ j * a - g ^ i * a = g ^ i * (a * (g ^ (j - i) - 1)) := by
    rw [hgj]
    have hle2 : a ≤ a * g ^ (j - i) := Nat.le_mul_of_pos_right a hp
    zify [hp, hle, hle2, hgj ▸ hle]
    ring
  rw [h2] at h1
  exact ((coprime_n d hd).pow_right i).dvd_mul_left.1 h1

include hd hu in
theorem orbit_inj {i j : ℕ} (hi : i < d) (hj : j < d) (h : u ^ (g ^ i) = u ^ (g ^ j)) : i = j := by
  rcases le_total i j with hij | hij
  · by_contra hne
    have hlt : i < j := lt_of_le_of_ne hij hne
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (j - i) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (j - i) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega
  · by_contra hne
    have hlt : j < i := lt_of_le_of_ne hij (Ne.symm hne)
    have hdv := dvd_of_pow_eq hd u hu (a := 1) hij (by simpa using h.symm)
    rw [one_mul] at hdv
    have h1 : 1 < g ^ (i - j) := Nat.one_lt_pow (by omega) hg.out.one_lt
    have h2 : g ^ (i - j) < g ^ d := Nat.pow_lt_pow_right hg.out.one_lt (by omega)
    have := Nat.le_of_dvd (by omega) hdv
    omega

def orbQ (d : ℕ) (u : (Fbar g)ˣ) : (Fbar g)[X] := ∏ i ∈ Finset.range d, (X - C ((u : Fbar g) ^ (g ^ i)))

theorem orbQ_monic : (orbQ d u).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem orbQ_natDegree : (orbQ d u).natDegree = d := by
  rw [orbQ, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

include hd hu in
theorem orbQ_frob : (orbQ d u).map (frobenius (Fbar g) g) = orbQ d u := by
  have hf : ∀ i, (X - C ((u : Fbar g) ^ g ^ i)).map (frobenius (Fbar g) g) =
      X - C ((u : Fbar g) ^ g ^ (i + 1)) := fun i => by
    simp only [Polynomial.map_sub, map_X, map_C, frobenius_def, ← pow_mul, pow_succ]
  have hd' : (u : Fbar g) ^ g ^ d = u := by
    have := congrArg Units.val (pow_gd hd u hu)
    simpa using this
  unfold orbQ
  rw [Polynomial.map_prod]
  simp_rw [hf]
  apply mul_right_cancel₀ (X_sub_C_ne_zero ((u : Fbar g) ^ g ^ 0))
  rw [← Finset.prod_range_succ' (fun i => X - C ((u : Fbar g) ^ g ^ i)), Finset.prod_range_succ, hd',
    pow_zero, pow_one]

include hd hu in
theorem exists_orbP : ∃ P : (ZMod g)[X], P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u ∧
    P.natDegree = d ∧ P.Monic := by
  have frob_fixed : ∀ y : Fbar g, y ^ g = y → y ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
    intro y hy
    classical
    by_contra hy'
    have hf0 : (X ^ g - X : (Fbar g)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hg.out.one_lt
    have hsub : insert y (Finset.univ.image (algebraMap (ZMod g) (Fbar g))) ⊆
        (X ^ g - X : (Fbar g)[X]).roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hy
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
        rw [← map_pow, ZMod.pow_card]
    have hny : y ∉ Finset.univ.image (algebraMap (ZMod g) (Fbar g)) := fun h => by
      obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
      exact hy' ⟨c, hc⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hny, Finset.card_image_of_injective _ (algebraMap (ZMod g) (Fbar g)).injective,
      Finset.card_univ, ZMod.card] at hc
    have h2 := (Multiset.toFinset_card_le _).trans (card_roots' (X ^ g - X : (Fbar g)[X]))
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hg.out.one_lt] at h2
    omega
  have hc : ∀ n, (orbQ d u).coeff n ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := fun n => by
    have h := congrArg (fun p => p.coeff n) (orbQ_frob hd u hu)
    simp only [coeff_map, frobenius_def] at h
    exact frob_fixed _ h
  have hl : orbQ d u ∈ Polynomial.lifts (algebraMap (ZMod g) (Fbar g)) := (lifts_iff_coeff_lifts _).2 hc
  obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (orbQ_monic u)
  exact ⟨P, hPmap, hPdeg.trans (orbQ_natDegree u), hPmonic⟩

theorem mem_roots_orbQ {y : Fbar g} : y ∈ (orbQ d u).roots ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  have h0 := (orbQ_monic (d := d) u).ne_zero
  unfold orbQ at h0 ⊢
  rw [roots_prod _ _ h0]
  simp only [roots_X_sub_C, Multiset.mem_bind, Finset.mem_val, Finset.mem_range, Multiset.mem_singleton]

variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)

include hP in
theorem mem_rootsBar_P {y : Fbar g} : y ∈ rootsBar P ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  rw [rootsBar, hP]
  exact mem_roots_orbQ u

include hd hu hP in

theorem le_natDegree_of_dvd {q : (ZMod g)[X]} (hq : q ∣ P) (hq0 : q.natDegree ≠ 0) : d ≤ q.natDegree := by
  classical
  have hq0' : q ≠ 0 := by
    rintro rfl
    simp at hq0
  have hqm : q.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := Polynomial.map_ne_zero hq0'
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap (ZMod g) (Fbar g))) (by
    rw [degree_map]
    intro h
    exact hq0 (natDegree_eq_of_degree_eq_some h))
  have hyP : y ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm]
    exact hy.dvd (Polynomial.map_dvd _ hq)
  obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P u hP).1 hyP
  have hcomp : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) = algebraMap (ZMod g) (Fbar g) :=
    RingHom.ext fun c => by simp [frobenius_def, ← map_pow, ZMod.pow_card]
  have hfrob : ∀ z, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot z →
      (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot (z ^ g) := by
    intro z hz
    simp only [IsRoot, eval_map] at hz ⊢
    have h := Polynomial.hom_eval₂ q (algebraMap (ZMod g) (Fbar g)) (frobenius (Fbar g) g) z
    rw [hcomp, hz, map_zero, frobenius_def] at h
    exact h.symm
  have hiter : ∀ k, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ (i + k)) := by
    intro k
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      have h := hfrob _ ih
      rw [← pow_mul, ← pow_succ] at h
      exact h
  have hall : ∀ j < d, (q.map (algebraMap (ZMod g) (Fbar g))).IsRoot ((u : Fbar g) ^ g ^ j) := by
    intro j hj
    have h1 := hiter (d - i + j)
    have h2 : i + (d - i + j) = j + d := by omega
    rw [h2] at h1
    have h3 := congrArg Units.val (pow_g_add hd u hu j)
    simp only [Units.val_pow_eq_pow_val] at h3
    rwa [h3] at h1
  have hsub : (Finset.range d).image (fun j => (u : Fbar g) ^ g ^ j) ⊆
      (q.map (algebraMap (ZMod g) (Fbar g))).roots.toFinset := fun z hz => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
    rw [Multiset.mem_toFinset, mem_roots hqm]
    exact hall j (Finset.mem_range.1 hj)
  have hinj : Set.InjOn (fun j => (u : Fbar g) ^ g ^ j) (Finset.range d) := fun a ha b hb hab =>
    orbit_inj hd u hu (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) (Units.ext (by simpa using hab))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  calc d ≤ _ := hc
    _ ≤ Multiset.card (q.map (algebraMap (ZMod g) (Fbar g))).roots := Multiset.toFinset_card_le _
    _ ≤ (q.map (algebraMap (ZMod g) (Fbar g))).natDegree := card_roots' _
    _ = q.natDegree := natDegree_map _

include hd hu hP in
theorem irreducible_P (hPd : P.natDegree = d) : Irreducible P := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hPd
    omega
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · by_contra hne
    push_neg at hne
    have hab' : a * b ≠ 0 := hab ▸ hP0
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab'
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab'
    have ha : a.natDegree ≠ 0 := fun h =>
      hne.1 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq ha0).2 h))
    have hb : b.natDegree ≠ 0 := fun h =>
      hne.2 (isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq hb0).2 h))
    have h1 := le_natDegree_of_dvd hd u hu hP (Dvd.intro b hab.symm) ha
    have h2 := le_natDegree_of_dvd hd u hu hP (Dvd.intro_left a hab.symm) hb
    have h3 : P.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
    omega

include hP in
theorem coeff_zero_P : P.coeff 0 ≠ 0 := by
  intro h0
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  have h0r : (0 : Fbar g) ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
  obtain ⟨i, -, hi⟩ := (mem_rootsBar_P u hP).1 h0r
  exact pow_ne_zero _ u.ne_zero hi.symm

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder

variable {g : ℕ} [hg : Fact g.Prime]

section One

variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)

include hd hu in
theorem finOrd (i : ℕ) : IsOfFinOrder ((u : Fbar g) ^ (g ^ i)) := by
  have h2 := one_lt_pow_g (g := g) hd
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨g ^ d - 1, by omega, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
  simp

include hd hu in
theorem no_prime_power {q0 ℓ : ℕ} (hℓ : ℓ.Prime) (hq0 : q0.Prime) (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1)
    (hqg : q0 ∣ g - 1) (i c : ℕ) : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) ≠ 1 := by
  intro h
  have h1 : u ^ (g ^ i * ℓ ^ c) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_mul, h]; rfl)
  have h2 : g ^ d - 1 ∣ ℓ ^ c :=
    ((coprime_n d hd).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  have h3 : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have e1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp
    (Nat.prime_two.dvd_of_dvd_pow ((h2g.trans h3).trans h2))
  have e2 := (Nat.prime_dvd_prime_iff_eq hq0 hℓ).mp (hq0.dvd_of_dvd_pow ((hqg.trans h3).trans h2))
  exact hq2 (e2.trans e1.symm)

include hd hu in
theorem exc_same {ℓ : ℕ} (hℓ : ℓ.Prime) {i j c : ℕ} (hi : i < d) (hj : j < d) (hij : i ≠ j)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((u : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g d ℓ := by
  have key : ∀ {i j : ℕ}, i < j → j < d → u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) → Exc g d ℓ := by
    intro i j hij hj h
    refine exc_of_dvd (e := j - i) hg.out.two_le hℓ hd ?_ (dvd_of_pow_eq hd u hu hij.le h)
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left d (j - i)
    have h1 : Nat.gcd d (j - i) ≤ j - i := Nat.gcd_le_right _ (by omega)
    have h0 : 0 < Nat.gcd d (j - i) := Nat.gcd_pos_of_pos_left _ hd
    have ht2 : 2 ≤ t := by
      by_contra hlt
      interval_cases t
      · omega
      · omega
    calc 2 * Nat.gcd d (j - i) = Nat.gcd d (j - i) * 2 := mul_comm _ _
      _ ≤ Nat.gcd d (j - i) * t := Nat.mul_le_mul_left _ ht2
      _ = d := ht.symm
  have h' : u ^ (g ^ i * ℓ ^ c) = u ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key h1 hj h'
  · exact key h1 hi h'.symm

end One

theorem exc_cross {p s ℓ : ℕ} (hℓ : ℓ.Prime) (hp : 2 ≤ p) (hs : 1 ≤ s) (hc : Nat.Coprime p s)
    (u w : (Fbar g)ˣ) (hu : orderOf u = g ^ p - 1) (hw : orderOf w = g ^ s - 1) (i j c : ℕ)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((w : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g p ℓ := by
  have h' : u ^ (g ^ i * ℓ ^ c) = w ^ (g ^ j * ℓ ^ c) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_mul, pow_mul, h])
  have h1 : u ^ (g ^ i * (ℓ ^ c * (g ^ s - 1))) = 1 := by
    rw [← mul_assoc, pow_mul, h', ← pow_mul, mul_comm, pow_mul, ← hw, pow_orderOf_eq_one, one_pow]
  have h2 : g ^ p - 1 ∣ ℓ ^ c * (g ^ s - 1) :=
    ((coprime_n p (by omega)).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  exact exc_of_dvd hg.out.two_le hℓ (by omega) (by rw [hc]; omega) h2

structure LabelOK (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  c0 : f.coeff 0 ≠ 0
  sqf : Squarefree f
  inj : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB N g → ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f,
    primeToPart ℓ x = primeToPart ℓ y → x = y
  ne1 : ∀ ℓ : ℕ, ℓ.Prime → ∀ x ∈ rootsBar f, primeToPart ℓ x ≠ primeToPart ℓ (1 : Fbar g)

theorem exists_labels (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB q : (ZMod g)[X], LabelOK N fA ∧ LabelOK N fB ∧
      (∀ r : (ZMod g)[X], r ∣ fA → r.natDegree ≠ 0 → N ≤ r.natDegree) ∧
      Irreducible q ∧ q ∣ fB ∧ q.natDegree = p := by
  have hN : 1 ≤ N := by omega
  set s := N - p with hs
  have hs1 : 1 ≤ s := by omega
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨uN, huN⟩ := exists_gen (g := g) N hN
  obtain ⟨up, hup⟩ := exists_gen (g := g) p hp1
  obtain ⟨us, hus⟩ := exists_gen (g := g) s hs1
  obtain ⟨PN, hPN, dN, mN⟩ := exists_orbP hN uN huN
  obtain ⟨Pp, hPp, dp, mp⟩ := exists_orbP hp1 up hup
  obtain ⟨Ps, hPs, ds, ms⟩ := exists_orbP hs1 us hus
  have iN := irreducible_P hN uN huN hPN dN
  have ip := irreducible_P hp1 up hup hPp dp
  have is := irreducible_P hs1 us hus hPs ds
  have one_fin : IsOfFinOrder (1 : Fbar g) := IsOfFinOrder.one
  have hcop : Nat.Coprime p s := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have memB : ∀ y, y ∈ rootsBar (Pp * Ps) ↔ y ∈ rootsBar Pp ∨ y ∈ rootsBar Ps := fun y => by
    unfold rootsBar
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (by rw [hPp]; exact (orbQ_monic up).ne_zero)
      (by rw [hPs]; exact (orbQ_monic us).ne_zero)), Multiset.mem_add]
  refine ⟨PN, Pp * Ps, Pp, ⟨mN, dN, coeff_zero_P uN hPN, iN.squarefree, ?_, ?_⟩,
    ⟨mp.mul ms, by rw [mp.natDegree_mul ms, dp, ds]; omega, ?_, ?_, ?_, ?_⟩,
    fun r hr hr0 => le_natDegree_of_dvd hN uN huN hPN hr hr0, ip, Dvd.intro _ rfl, dp⟩
  · intro ℓ hℓ hBB x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P uN hPN).mp hy
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) (finOrd hN uN huN j) hxy
    by_contra hne
    exact hBB (Or.inr ⟨N, hN, le_rfl, exc_same hN uN huN hℓ hi hj (fun e => hne (by rw [e])) hc⟩)
  · intro ℓ hℓ x hx hxy
    obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P uN hPN).mp hx
    obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hN uN huN i) one_fin hxy
    exact no_prime_power hN uN huN hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
  · rw [mul_coeff_zero]; exact mul_ne_zero (coeff_zero_P up hPp) (coeff_zero_P us hPs)
  · refine squarefree_mul_iff.mpr ⟨ip.isRelPrime_iff_not_dvd.mpr fun hdv => ?_, ip.squarefree, is.squarefree⟩
    have := natDegree_le_of_dvd hdv ms.ne_zero
    omega
  · intro ℓ hℓ hBB x hx y hy hxy
    have hBp : ¬ Exc g p ℓ := fun h => hBB (Or.inr ⟨p, hp1, by omega, h⟩)
    have hBs : ¬ Exc g s ℓ := fun h => hBB (Or.inr ⟨s, hs1, by omega, h⟩)
    rcases (memB x).mp hx with hx | hx <;> rcases (memB y).mp hy with hy | hy
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hp1 up hup j) hxy
      by_contra hne
      exact hBp (exc_same hp1 up hup hℓ hi hj (fun e => hne (by rw [e])) hc)
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) (finOrd hs1 us hus j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus i j c hc)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P up hPp).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hp1 up hup j) hxy
      exact (hBp (exc_cross hℓ hp.two_le hs1 hcop up us hup hus j i c hc.symm)).elim
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨j, hj, rfl⟩ := (mem_rootsBar_P us hPs).mp hy
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) (finOrd hs1 us hus j) hxy
      by_contra hne
      exact hBs (exc_same hs1 us hus hℓ hi hj (fun e => hne (by rw [e])) hc)
  · intro ℓ hℓ x hx hxy
    rcases (memB x).mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P up hPp).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hp1 up hup i) one_fin hxy
      exact no_prime_power hp1 up hup hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])
    · obtain ⟨i, hi, rfl⟩ := (mem_rootsBar_P us hPs).mp hx
      obtain ⟨c, hc⟩ := exists_pow_eq hℓ _ _ (finOrd hs1 us hus i) one_fin hxy
      exact no_prime_power hs1 us hus hℓ hq0 hq2 h2g hqg i c (by rw [hc, one_pow])

theorem exists_good (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB : (ZMod g)[X], fA ≠ fB ∧ (fA.Monic ∧ fA.natDegree = N ∧ fA.coeff 0 ≠ 0) ∧
      (fB.Monic ∧ fB.natDegree = N ∧ fB.coeff 0 ≠ 0) ∧
      ∀ (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
        IsGood N g (fun v => if t v then fA else fB) (fun (_ : PP) (_ : J) => (1 : (ZMod g)ˣ)) := by
  obtain ⟨fA, fB, q, hA, hB, hdiv, hq, hqB, hqd⟩ := exists_labels (g := g) N p q0 hp h1 h2 hq0 hq2 h2g hqg
  refine ⟨fA, fB, fun e => ?_, ⟨hA.monic, hA.deg, hA.c0⟩, ⟨hB.monic, hB.deg, hB.c0⟩,
    fun PP J t ⟨vA, hvA⟩ ⟨vB, hvB⟩ => ?_⟩
  · have := hdiv q (e ▸ hqB) (by rw [hqd]; exact hp.ne_zero)
    omega
  have hOK : ∀ v, LabelOK N (if t v then fA else fB) := fun v => by split_ifs <;> assumption
  refine ⟨fun v => ⟨(hOK v).monic, (hOK v).deg, (hOK v).c0⟩, fun v => (hOK v).sqf,
    fun ℓ hℓ hBB v => (hOK v).inj ℓ hℓ hBB, fun ℓ hℓ _ v _ x hx => ?_, fun a ha1 ha2 => ⟨vA, ?_⟩,
    ⟨vB, q, hq, ?_, hqd ▸ hp, by omega, by omega⟩⟩
  · rw [Units.val_one, map_one]; exact (hOK v).ne1 ℓ hℓ x hx
  · rintro ⟨r, hr, hra⟩
    simp only [hvA, if_true] at hr
    have := hdiv r hr (by omega)
    omega
  · simp only [hvB]; exact hqB

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

attribute [local instance] Classical.propDecidable

section Eval

variable {K : Type} [Field K]

def evS {Γ : Type} [Finite Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : K :=
  letI := Fintype.ofFinite Γ
  ∑ g, x.coeff g * ψ g

theorem evS_eq {Γ : Type} [Fintype Γ] (ψ : Γ → K) (x : MonoidAlgebra K Γ) : evS ψ x = ∑ g, x.coeff g * ψ g := by
  unfold evS
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem evS_zero {Γ : Type} [Finite Γ] (ψ : Γ → K) : evS ψ (0 : MonoidAlgebra K Γ) = 0 := by
  simp [evS]

theorem evS_sub {Γ : Type} [Finite Γ] (ψ : Γ → K) (x y : MonoidAlgebra K Γ) : evS ψ (x - y) = evS ψ x - evS ψ y := by
  simp [evS, sub_mul, Finset.sum_sub_distrib]

theorem evS_sum {Γ ι : Type} [Finite Γ] (ψ : Γ → K) (s : Finset ι) (x : ι → MonoidAlgebra K Γ) :
    evS ψ (∑ i ∈ s, x i) = ∑ i ∈ s, evS ψ (x i) := by
  unfold evS
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem evS_one {Γ : Type} [Group Γ] [Finite Γ] (ψ : Γ → K) : evS ψ (1 : MonoidAlgebra K Γ) = ψ 1 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq, Finset.sum_eq_single 1]
  · simp
  · intro g _ hg
    rw [one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem evS_tens (ψ : ∀ i, G i → K) (x : ∀ i, MonoidAlgebra K (G i)) :
    evS (fun g : ∀ i, G i => ∏ i, ψ i (g i)) (tens x) = ∏ i, evS (ψ i) (x i) := by
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  rw [evS_eq]
  simp only [evS_eq, tens_coeff, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable {L : I → Type} [∀ i, Fintype (L i)] (E : ∀ i, L i → MonoidAlgebra K (G i)) (S : (∀ i, L i) → Prop)


theorem lift_scalar {Γ V : Type} [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (Ψ : Γ →* K)
    (F : Γ →* Module.End K V) (hF : ∀ g, F g = Ψ g • 1) (x : MonoidAlgebra K Γ) :
    MonoidAlgebra.lift K (Module.End K V) Γ F x = evS Ψ x • 1 := by
  have := Fintype.ofFinite Γ
  rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ (fun a b => b • F a) (fun _ => zero_smul _ _), evS_eq,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun g _ => by rw [hF, smul_smul]

end Eval

section Triv

variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]

def eT : MonoidAlgebra K Γ := MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun _ => ((Nat.card Γ : K))⁻¹

variable {K Γ}

theorem eT_coeff (g : Γ) : (eT K Γ).coeff g = ((Nat.card Γ : K))⁻¹ := rfl

theorem card_ne [CharZero K] : (Nat.card Γ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

theorem eT_idem [CharZero K] : eT K Γ * eT K Γ = eT K Γ := by
  have := Fintype.ofFinite Γ
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype]
  simp only [eT_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [← mul_assoc, mul_inv_cancel₀ card_ne, one_mul]

theorem eT_central (a : MonoidAlgebra K Γ) : eT K Γ * a = a * eT K Γ :=
  commute_of_single _ (fun g => by
    apply MonoidAlgebra.coeff_injective
    ext h
    rw [coeff_mul_single_apply, coeff_single_mul_apply, eT_coeff, eT_coeff, mul_one, one_mul]) a

theorem eT_ne_zero [CharZero K] : eT K Γ ≠ 0 := fun h =>
  inv_ne_zero (card_ne (K := K) (Γ := Γ)) (congrArg (fun x => x.coeff 1) h)

theorem one_sub_eT_ne_zero [CharZero K] (g : Γ) (hg : g ≠ 1) : 1 - eT K Γ ≠ 0 := fun h => by
  have h1 := congrArg (fun x => x.coeff g) h
  simp only [coeff_sub, Finsupp.sub_apply, eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hg),
    zero_sub] at h1
  exact inv_ne_zero (card_ne (K := K) (Γ := Γ)) (neg_eq_zero.mp h1)

theorem evS_eT_one [CharZero K] : evS (fun _ : Γ => (1 : K)) (eT K Γ) = 1 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq]
  simp only [eT_coeff, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  exact mul_inv_cancel₀ card_ne

theorem evS_eT_ne (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) : evS ψ (eT K Γ) = 0 := by
  have := Fintype.ofFinite Γ
  rw [evS_eq]
  simp only [eT_coeff, ← Finset.mul_sum]
  have h1 : ψ g * ∑ x, ψ x = ∑ x, ψ x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g) (fun x => ψ x)]
    exact Finset.sum_congr rfl fun x _ => (map_mul ψ g x).symm
  have h2 : (ψ g - 1) * ∑ x, ψ x = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rw [(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hg), mul_zero]

end Triv

section Family

variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)

def esZ (f : Λ) : MonoidAlgebra K Γ := if f = fA then 1 - eT K Γ else if f = fB then eT K Γ else 0

def cfQ (f : Λ) (h : Γ) : ℚ :=
  if f = fA then (if (1 : Γ) = h then 1 else 0) - ((Nat.card Γ : ℚ))⁻¹
  else if f = fB then ((Nat.card Γ : ℚ))⁻¹ else 0

theorem esZ_coeff [CharZero K] (f : Λ) (h : Γ) : (esZ K Γ fA fB f).coeff h = (cfQ Γ fA fB f h : K) := by
  unfold esZ cfQ
  split_ifs <;> simp [eT_coeff, one_def, MonoidAlgebra.coeff_single_apply, *]

variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)

theorem esZ_idem (f : Λ) : esZ K Γ fA fB f * esZ K Γ fA fB f = esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, mul_sub, eT_idem, one_mul, one_mul, mul_one, sub_self, sub_zero]
  · exact eT_idem
  · simp

omit [CharZero K] in
theorem esZ_central (f : Λ) (a) : esZ K Γ fA fB f * a = a * esZ K Γ fA fB f := by
  unfold esZ
  split_ifs
  · rw [sub_mul, mul_sub, eT_central, one_mul, mul_one]
  · exact eT_central a
  · simp

theorem esZ_orth (f f' : Λ) (h : f ≠ f') : esZ K Γ fA fB f * esZ K Γ fA fB f' = 0 := by
  unfold esZ
  split_ifs with h1 h2' h3 h4 h5 h6
  · exact absurd (h1.trans h2'.symm) h
  · rw [sub_mul, eT_idem, one_mul, sub_self]
  · simp
  · rw [mul_sub, eT_idem, mul_one, sub_self]
  · exact absurd (h4.trans h6.symm) h
  all_goals simp

omit [CharZero K] in
include hAB in
theorem esZ_sum (S : Finset Λ) (hA : fA ∈ S) (hB : fB ∈ S) : ∑ f ∈ S, esZ K Γ fA fB f = 1 := by
  have e : ∀ f, esZ K Γ fA fB f = (if f = fA then 1 - eT K Γ else 0) + if f = fB then eT K Γ else 0 := fun f => by
    unfold esZ
    by_cases h1 : f = fA
    · rw [if_pos h1, if_pos h1, if_neg (fun h => hAB (h1.symm.trans h)), add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hA, if_pos hB, sub_add_cancel]

include hAB in

theorem evS_esZ_one (f : Λ) : evS (fun _ : Γ => (1 : K)) (esZ K Γ fA fB f) = if f = fB then 1 else 0 := by
  unfold esZ
  by_cases h1 : f = fA
  · rw [if_pos h1, if_neg (fun h => hAB (h1.symm.trans h)), evS_sub, evS_one, evS_eT_one, sub_self]
  · rw [if_neg h1]
    split_ifs
    · exact evS_eT_one
    · exact evS_zero _

include hAB in

theorem evS_esZ_ne (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) (f : Λ) :
    evS ψ (esZ K Γ fA fB f) = if f = fA then 1 else 0 := by
  unfold esZ
  by_cases h1 : f = fA
  · rw [if_pos h1, if_pos h1, evS_sub, evS_one, evS_eT_ne ψ g hg, map_one, sub_zero]
  · rw [if_neg h1, if_neg h1]
    split_ifs
    · exact evS_eT_ne ψ g hg
    · exact evS_zero _

end Family

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {R : Ranks} (H : Host R)

set_option synthInstance.maxHeartbeats 400000 in

def ndL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NData R H what₂ where
  Om := AlgC
  plOm := ⟨fun v => placeOf AlgC v, fun v => isPlaceOver_placeOf AlgC v⟩
  ldat p _ := toyLocalData H p
  sha_eq := fun p _ e h1 h2 n hn => by
    rw [h.hsha p e h1 h2, hn]
    simp
  Loc := Empty
  l i := i.elim
  lPrime i := i.elim
  j i := i.elim
  j_range i := i.elim
  mu i := i.elim
  w i := i.elim
  w_l i := i.elim
  mu_w i := i.elim
  w_tw i := i.elim
  locs _ _ := ∅
  locs_mem _ _ i := i.elim
  O i := i.elim
  instO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  finO i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  O_complete i := i.elim
  embK i := i.elim
  embK_w i := i.elim
  X i := i.elim
  finX i := i.elim
  neX i := i.elim
  T i := i.elim
  T_local i := i.elim
  T_sep i := i.elim
  Mt i := i.elim
  acgMt i := i.elim
  modMt i := i.elim
  freeMt i := i.elim
  finMt i := i.elim
  act i := i.elim
  act_inj i := i.elim
  prMt i := i.elim
  prMt_span i := i.elim
  prMt_lat i := i.elim
  eig_ne i := i.elim
  chi i := i.elim
  chi_cont i := i.elim
  chi_def i := i.elim
  Z i := i.elim
  Zgood i := i.elim
  s0 i := i.elim
  restNLevelExponent_of_odd i := i.elim
  restNLevelExponent_of_two i := i.elim
  S i := i.elim
  Q i := i.elim
  SQ_disj i := i.elim
  SQ_l i := i.elim
  S_def i := i.elim
  hT i := i.elim
  T_gen i := i.elim
  gam0 i := i.elim
  locNd_chebotarevPlace_mem i := i.elim
  chi_ram_Q i := i.elim
  Bj i := i.elim
  acgBj i := i.elim
  modBj i := i.elim
  freeBj i := i.elim
  finBj i := i.elim
  g_split := h.hg
  PlG _ := Fin R.f
  card_PlG _ := Fintype.card_fin _
  lab := lab
  lab_monic := hlab
  chiT _ _ _ := 1
  restN_card_levelGroup_eq := h.hcard
  SQ_split i := i.elim
  restN_tameGenerator_generates i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def ntwL {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    NTw R H what₂ LL0 (ndL H what₂ h lab hlab) where
  cc := conjAlgC
  cc_cm := isCMConjOm_conjAlgC H
  Tw := Empty
  O_l i := i.elim
  topO i := i.elim
  trO i := i.elim
  O_adic i := i.elim
  delta_open i := i.elim
  twistCharacterFamily_unramified i := i.elim
  twistCharacterFamily_at_auxiliaryPlaces i := i.elim
  twistCharacterFamily_tame i := i.elim
  hk_zero i := i.elim
  jL_range i := i.elim
  lamG i := i.elim
  lamG_cont i := i.elim
  lamG_unr i := i.elim
  lamG_pD i := i.elim
  lamG_anti i := i.elim
  Xv_def i := i.elim
  qs_conj i := i.elim
  twOf i := i.elim
  twSide i := i.elim
  twOf_l i := i.elim
  twist₂ i := i.elim
  twO_emb i := i.elim
  psiL i := i.elim
  psiL_ord i := i.elim
  psiL_open i := i.elim
  psiL_anti i := i.elim
  psiL_ram i := i.elim
  psiL_l i := i.elim
  chi_tw i := i.elim
  art_univ i := i.elim
  l i := i.elim
  lPrime i := i.elim
  O0 i := i.elim
  crO0 i := i.elim
  twistBaseCoefficientRing_isDomain i := i.elim
  twistBaseCoefficientRing_isDVR i := i.elim
  algO0 i := i.elim
  twistBaseCoefficientRing_finite_padic i := i.elim
  twistBaseCoefficientRing_residueField_finite i := i.elim
  topO0 i := i.elim
  twistBaseCoefficientRing_topologicalRing i := i.elim
  twistBaseCoefficientRing_isAdic i := i.elim
  emb0 i := i.elim
  emb0b i := i.elim
  restX_coefficientEmbedding_conj i := i.elim
  O i := i.elim
  crO i := i.elim
  domO i := i.elim
  dvrO i := i.elim
  algO i := i.elim
  O_inj i := i.elim
  resO_ac i := i.elim
  O_complete i := i.elim
  Ok i := i.elim
  crOk i := i.elim
  domOk i := i.elim
  dvrOk i := i.elim
  algOk i := i.elim
  Ok_inj i := i.elim
  Ok_fin i := i.elim
  zk i := i.elim
  zk_prim i := i.elim
  Ok_gen i := i.elim
  pD i := i.elim
  pD_eq i := i.elim
  delta i := i.elim
  delta_anti i := i.elim
  delta_ram i := i.elim
  delta_15 i := i.elim
  delta_tame i := i.elim
  chi1 i := i.elim
  twistCharacterFamily_continuous i := i.elim
  Sig i := i.elim
  finSig i := i.elim
  jS i := i.elim
  jS_range i := i.elim
  side i := i.elim
  rhoS i := i.elim
  rhoS_cont i := i.elim
  S0 i := i.elim
  twistExcludedPlaces_contains_residueChar i := i.elim
  placesOver_subset_exceptional i := i.elim
  primes_subset_exceptional i := i.elim
  B i := i.elim
  acgB i := i.elim
  modB i := i.elim
  freeB i := i.elim
  finB i := i.elim
  Theta i := i.elim
  ThetaPsi i := i.elim
  ThetaPsi_one i := i.elim
  hk i := i.elim
  hEig i := i.elim
  abelian₂ i := i.elim
  finLam i := i.elim
  jL i := i.elim
  sideL i := i.elim
  s2 i := i.elim
  Xv i := i.elim
  qs i := i.elim
  qs_sq i := i.elim
  RCG i := i.elim
  grpRCG i := i.elim
  finRCG i := i.elim
  RCG_l i := i.elim
  art i := i.elim
  art_surj i := i.elim
  art_cont i := i.elim
  art_anti i := i.elim
  art_unr i := i.elim
  res i := i.elim
  res_art i := i.elim
  th i := i.elim

open Polynomial in
set_option synthInstance.maxHeartbeats 400000 in

def nautL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NAut (ndL H what₂ h lab hlab) where
  iotaQ i := i.elim
  iotaQC i := i.elim
  iota_LL i := i.elim
  iotaQ_alg i := i.elim
  locV_unr i := i.elim
  LP _ := Multiset ℂˣ
  lpDim := fun a => Multiset.card a
  lpZero _ := 0
  lpSum := fun a b => a + b
  lpTw := fun {w} a s => a.map (· * qPow H w s)
  lpChar := fun a χ => a.map (· * χ.prod)
  lpUnr _ m := m.map toU
  mono0 := fun _ => True
  unr := fun _ => True
  frobEig := fun a => a.map Units.val
  tempered := fun a => ∀ α ∈ a.map Units.val, ‖α‖ = 1
  tempered_unr _ _ := Iff.rfl
  lpDim_char _ _ _ := Multiset.card_map _ _
  unr_char _ _ _ _ _ := trivial
  monomial_char_iff _ _ _ := Iff.rfl
  inePol := fun a _ => (X - 1) ^ Multiset.card a
  items₂ _ _ _ := 1
  lpDim_zero _ := rfl
  lpDim_sum a b := Multiset.card_add a b
  lpDim_tw a s := Multiset.card_map _ _
  lpUnr_spec _ m hm := ⟨trivial, by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl (fun z hz => val_toU (fun h0 => hm (h0 ▸ hz)))).trans (Multiset.map_id' m),
    Multiset.card_map _ _⟩
  unr_sum _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  monomial_sum_iff _ _ := ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  frobEig_sum a b _ _ := Multiset.map_add _ a b
  unr_tw _ _ := Iff.rfl
  monomial_twist_iff _ _ := Iff.rfl
  frobEig_tw a s _ := by rw [Multiset.map_map, Multiset.map_map]; rfl
  frobEig_char a χ c _ _ _ hχ := by
    obtain ⟨u, rfl, rfl⟩ := Multiset.map_eq_singleton.mp hχ
    rw [Multiset.map_map, Multiset.map_map, Multiset.prod_singleton]; rfl
  lpZero_unr _ := trivial
  frobEig_zero _ := rfl
  lpSum_zero a := add_zero a
  lpSum_comm a b := add_comm a b
  lpSum_assoc a b c := add_assoc a b c
  lpTw_zero a := by simp [qPow_zero]
  lpTw_add a s t := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun z _ => by simp only [Function.comp, mul_assoc, qPow_add])
  lpTw_sum a b s := Multiset.map_add _ a b
  unr_eq_lpUnr a _ := by
    rw [Multiset.map_map]
    exact ((Multiset.map_congr rfl (fun z _ => toU_val z)).trans (Multiset.map_id' a)).symm
  unr_mono0 _ _ := trivial
  frobEig_ne_zero a _ := fun h0 => by
    obtain ⟨u, -, hu⟩ := Multiset.mem_map.mp h0
    exact u.ne_zero hu
  frobEig_card a _ := Multiset.card_map _ _
  inePol_sum a b _ := by rw [Multiset.card_add, pow_add]
  inePol_tw a s _ _ := by rw [Multiset.card_map]
  unr_iff_ine _ := ⟨fun _ => ⟨trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  inertiaCharpoly_zero _ _ := rfl
  inertiaCharpoly_add _ _ _ _ := (one_mul 1).symm
  CG a := {f : PlE H → Multiset ℂˣ // ∀ w, Multiset.card (f w) = a}
  csd := fun π => ∀ w w', IsConjPl H w w' → π.1 w' = (π.1 w).map (·⁻¹)
  csd_unr := fun π w w' h hc _ => ⟨trivial, by
    rw [h w w' hc, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => Units.val_inv_eq_inv_val u)⟩
  csd_tw := fun π χ hχ hπ w w' hc => by
    show (π.1 w').map (· * (χ.1 w').prod) = ((π.1 w).map (· * (χ.1 w).prod)).map (·⁻¹)
    rw [hπ w w' hc, hχ w w' hc, Multiset.prod_map_inv', Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun u _ => (mul_inv u _).symm)
  ralg := fun {a} _ => ∀ _ : H.E →+* ℂ, (Multiset.replicate a (0 : ℂ)).Nodup ∧
    ∀ z ∈ Multiset.replicate a (0 : ℂ), ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  ralg_def := fun _ => Iff.rfl
  locG := fun π w => π.1 w
  locG_dim := fun π w => π.2 w
  locG_unr_ae := fun _ => Filter.Eventually.of_forall fun _ => trivial
  tw := fun π χ => ⟨fun w => (π.1 w).map (· * (χ.1 w).prod), fun w => (Multiset.card_map _ _).trans (π.2 w)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun {a} _ _ => Multiset.replicate a 0
  infG_tw := fun _ _ _ s hs => by
    rw [Multiset.replicate_one, Multiset.singleton_inj] at hs
    simp [← hs]
  infG_card := fun _ _ => Multiset.card_replicate _ _
  muC i := i.elim
  etaT := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaTinv := ⟨fun _ => {-1}, fun _ => rfl⟩
  etaT_unr _ := trivial
  etaT_inert _ _ := by simp
  etaTinv_def _ := ⟨trivial, by simp⟩
  etaT_split _ _ _ _ a b ha hb := by
    simp only [Multiset.map_singleton, Multiset.singleton_inj, Units.val_neg, Units.val_one] at ha hb
    rw [← ha, ← hb]; norm_num
  muC_csd i := i.elim
  lab_loc i := i.elim
  wdOf_dim i := i.elim
  wdOf_unr i := i.elim
  wdOf_frob i := i.elim
  wdOf_ine i := i.elim
  wdOf_mono0 i := i.elim
  jumpsInf_def i := i.elim
  locAut_hodgeTateWeightsLevelZero_def i := i.elim
  chi_mu i := i.elim
  AV i := i.elim
  finAV i := i.elim
  ptV i := i.elim
  typeV i := i.elim
  typeV_ne i := i.elim
  typeV_indep i := i.elim
  typeV_top i := i.elim
  pt_surj i := i.elim
  eig_dim i := i.elim
  locV i := i.elim
  satV i := i.elim
  pt_loc i := i.elim
  infWt i := i.elim
  locW i := i.elim
  satW i := i.elim
  plGw k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose
  plGw_over k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.1
  plGw_inj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.1
  plGw_nconj k := (exists_halfPlaces H _ (H.g_prime k) (h.hg k)).choose_spec.2.2
  wdOf i := i.elim
  IsCrysW i := i.elim
  IsPotCrysW i := i.elim
  IsdRW i := i.elim
  jumpsW i := i.elim
  wdOf_unrL i := i.elim
  wdOf_mono0L i := i.elim
  jumpsInf i := i.elim
  locAutHodgeTateWeightsLevelZero i := i.elim
  kFbar i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def nbcL (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NBC (nautL H what₂ h lab hlab) where
  AU _ := Empty
  multAU _ π := π.elim
  sphAU _ π := π.elim
  locAU _ π := π.elim
  satAU _ π := π.elim
  satAU_card _ π := π.elim
  Wt _ := Empty
  infW _ W := W.elim
  infW_card _ W := W.elim
  infW_alg _ W := W.elim
  wtAU _ π := π.elim
  embAV i := i.elim
  embAV_inj i := i.elim
  embAV_loc i := i.elim
  embAV_sat i := i.elim
  embAV_sph i := i.elim
  embAV_inf i := i.elim

set_option synthInstance.maxHeartbeats 400000 in

def nexpL {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r)
    (eL : G0g (ndL H what₂ h lab hlab) → LL0) :
    NExp R H what₂ LL0 (ndL H what₂ h lab hlab) (ntwL H LL0 h lab hlab) where
  Fm i := i.elim
  eLL0 := eL
  eAlg_def i := i.elim
  thPsi_one i := i.elim
  twPsi_one i := i.elim
  eH i := i.elim
  eH_idem i := i.elim
  MtLat_fg i := i.elim
  MtLat_span i := i.elim
  embB i := i.elim
  embB_inj i := i.elim
  acgFm i := i.elim
  modFmK i := i.elim
  modFmO i := i.elim
  towFm i := i.elim
  fdFm i := i.elim
  actG i := i.elim
  U := ⊥
  psiU i := i.elim
  eAlg i := i.elim
  eAlg_idem i := i.elim
  eAlg_central i := i.elim
  Bsup i := i.elim
  Dat i := i.elim
  th i := i.elim
  lev i := i.elim
  thPsi i := i.elim
  thU i := i.elim
  twPsi i := i.elim
  twDel i := i.elim
  delU i := i.elim
  delU_unr i := i.elim
  delU_l i := i.elim
  delU_anti i := i.elim
  delU_open i := i.elim
  delU_res i := i.elim
  delU_conj i := i.elim
  MtV i := i.elim
  acgMt i := i.elim
  modMtK i := i.elim
  modMtO i := i.elim
  towMt i := i.elim
  fdMt i := i.elim
  MtLat i := i.elim
  thP i := i.elim
  hkF i := i.elim

theorem l_Z_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    ∀ i x, x ∈ (ndL H what₂ h lab hlab).Z i ↔ x ∈ Formalism.MainNotions.N.ZN (ndL H what₂ h lab hlab) (nautL H what₂ h lab hlab) i :=
  fun i => i.elim

theorem l_Zgood_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) :
    ∀ i x, x ∈ (ndL H what₂ h lab hlab).Zgood i ↔
      x ∈ Formalism.MainNotions.N.ZgoodN (ndL H what₂ h lab hlab) (nautL H what₂ h lab hlab) i :=
  fun i => i.elim

theorem l_etaJ_tie (what₂ : Rows.Data R) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) (hη : ∀ j w, what₂.etaJ j w = 0) :
    ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ (ndL H what₂ h lab hlab).locs j w, (ndL H what₂ h lab hlab).etaLoc i := by
  intro j w _ _
  rw [hη]
  rfl

variable {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  (LL0 : IntermediateField ℚ what₂.LL) (h : NHyp H what₂)
    (lab : ∀ k, what₂.FT → Fin R.f → Polynomial (ZMod (H.g k)))
    (hlab : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r)
    (eL : G0g (ndL H what₂ h lab hlab) → LL0)

set_option synthInstance.maxHeartbeats 400000 in

def nthL : NTh R H what₂ LL0 (ndL H what₂ h lab hlab) (ntwL H LL0 h lab hlab) (nexpL H LL0 h lab hlab eL) where
  iC := fun i => i.elim
  iC_int := fun i => i.elim
  aL := fun i => i.elim
  aL_g := fun i => i.elim
  aL_off := fun i => i.elim
  Pt := fun i => i.elim
  ev := fun i => i.elim
  ev_smul := fun i => i.elim
  ev_inj := fun i => i.elim
  Lt := fun i => i.elim
  acgLt := fun i => i.elim
  modLt := fun i => i.elim
  freeLt := fun i => i.elim
  finLt := fun i => i.elim
  Let := fun i => i.elim
  finLet := fun i => i.elim
  Harm := fun i => i.elim
  thV := fun i => i.elim
  datPhi := fun i => i.elim
  datP := fun i => i.elim
  recDet := fun i => i.elim
  Ctr := fun i => i.elim
  ctrC := fun i => i.elim
  Harm_def := fun i => i.elim
  thV_add := fun i => i.elim
  thV_smul := fun i => i.elim
  thV_addP := fun i => i.elim
  thV_smulP := fun i => i.elim
  actK_one := fun i => i.elim
  actK_mul := fun i => i.elim
  recDet_act := fun i => i.elim
  recDetq_act := fun i => i.elim
  hkIdx := fun i => i.elim
  finHk := fun i => i.elim
  hkMove := fun i => i.elim
  hkU := fun i => i.elim
  hk_ev := fun i => i.elim
  MaximalUnramifiedExtension := fun i => i.elim
  FmUr := fun i => i.elim
  FmUr_smul := fun i => i.elim
  FmUr_span := fun i => i.elim
  Bsup_def := fun i => i.elim
  Kq := fun i => i.elim
  grpKq := fun i => i.elim
  actK := fun i => i.elim
  recDetq := fun i => i.elim
  recDetq_mem := fun i => i.elim

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

structure Lbl where
  fA : ∀ k, (ZMod (H.g k))[X]
  fB : ∀ k, (ZMod (H.g k))[X]
  ne : ∀ k, fA k ≠ fB k
  okA : ∀ k, (fA k).Monic ∧ (fA k).natDegree = R.r ∧ (fA k).coeff 0 ≠ 0
  okB : ∀ k, (fB k).Monic ∧ (fB k).natDegree = R.r ∧ (fB k).coeff 0 ≠ 0
  good : ∀ k (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => if t v then fA k else fB k) (fun (_ : PP) (_ : J) => (1 : (ZMod (H.g k))ˣ))

theorem lbl_nonempty (ht : THyp H) (p : ℕ) (hp : p.Prime) (h1 : R.r < 2 * p) (h2 : p + 3 ≤ R.r) :
    Nonempty (Lbl H) := by
  have hd : ∀ k, H.QS * H.q * H.d ∣ H.g k - 1 := fun k => by
    have h := Nat.div_add_mod (H.g k) (H.QS * H.q * H.d)
    rw [ht.cond k] at h
    exact ⟨H.g k / (H.QS * H.q * H.d), by omega⟩
  have hq2 : H.q ≠ 2 := fun e => by have := H.hyp.2.2.1; omega
  have key := fun k => exists_good (g := H.g k) R.r p H.q hp h1 h2 H.hyp.1 hq2
    (((((dvd_pow_self 2 (by omega)).trans H.tower_dvd : 2 ∣ H.QS).mul_right H.q).mul_right H.d).trans (hd k))
    ((Dvd.intro (H.QS * H.d) (by ring)).trans (hd k))
  choose fA fB h using key
  exact ⟨⟨fA, fB, fun k => (h k).1, fun k => (h k).2.1, fun k => (h k).2.2.1, fun k => (h k).2.2.2⟩⟩

variable {H} (Lb : Lbl H)

def tupL (k : Fin 2) (v : Fin R.f) : (ZMod (H.g k))[X] := if decide (v.1 ≠ 0) then Lb.fA k else Lb.fB k

theorem two_le_f (R : Ranks) : 2 ≤ R.f := by
  have : 0 < R.n := by unfold Ranks.n; positivity
  unfold Ranks.f; omega

theorem tupL_good (J : Type) (k : Fin 2) :
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (tupL Lb k) (fun (_ : Fin R.f) (_ : J) => (1 : (ZMod (H.g k))ˣ)) :=
  Lb.good k (Fin R.f) J (fun v => decide (v.1 ≠ 0)) ⟨⟨1, two_le_f R⟩, by simp⟩
    ⟨⟨0, by have := two_le_f R; omega⟩, by simp⟩

def labL {FT : Type} (k : Fin 2) (_ : FT) (v : Fin R.f) : (ZMod (H.g k))[X] := tupL Lb k v

theorem labL_monic {FT : Type} (k : Fin 2) (σ : FT) (v : Fin R.f) :
    (labL Lb k σ v).Monic ∧ (labL Lb k σ v).natDegree = R.r := by
  unfold labL tupL
  split_ifs
  · exact ⟨(Lb.okA k).1, (Lb.okA k).2.1⟩
  · exact ⟨(Lb.okB k).1, (Lb.okB k).2.1⟩

variable (H) in

def zL (k : Fin 2) : GL (Fin R.r) (ZMod (H.g k)) := -1

variable (H) in
theorem zL_ne_one (ht : THyp H) (k : Fin 2) : zL H k ≠ 1 := by
  intro h
  have hr : 0 < R.r := Nat.pos_of_ne_zero (r_ne_zero R)
  have h1 := congrArg (fun u : GL (Fin R.r) (ZMod (H.g k)) => (u : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g k))) ⟨0, hr⟩ ⟨0, hr⟩) h
  simp only [zL, Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
  have h2 : (2 : ZMod (H.g k)) = 0 := by linear_combination -h1
  have h3 : ((2 : ℕ) : ZMod (H.g k)) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact (ht.jac k).1 ((Nat.prime_dvd_prime_iff_eq (H.g_prime k) Nat.prime_two).mp h3)

def esL (K : Type) [Field K] (k : Fin 2) : (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))) :=
  esZ K (GL (Fin R.r) (ZMod (H.g k))) (Lb.fA k) (Lb.fB k)

variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

abbrev ndG : NData R H what₂ := ndL H what₂ h (labL Lb) (labL_monic Lb)

theorem goodT_tupL : GoodT (ndG H Lb what₂ h) (tupL Lb) := fun k =>
  ⟨tupL_good Lb _ k, by
    have e : (fun (v : Fin R.f) (j : Fin R.m) => ((1 : (ZMod (H.g k))ˣ))⁻¹) = fun _ _ => 1 := by
      funext _ _; exact inv_one
    show Formalism.CyclotomicNorms.IsGood R.r (H.g k) (tupL Lb k) (fun (v : Fin R.f) (j : Fin R.m) => ((1 : (ZMod (H.g k))ˣ))⁻¹)
    rw [e]; exact tupL_good Lb _ k⟩


section Field

variable (K : Type) [Field K] [CharZero K]

def e0L : MonoidAlgebra K (G0g (ndG H Lb what₂ h)) := e0F (ndG H Lb what₂ h) (esL Lb K)

theorem labelIdempotent_idem : e0L H Lb what₂ h K * e0L H Lb what₂ h K = e0L H Lb what₂ h K :=
  seriesIdempotent_idem _ _ (fun k f => esZ_idem f) (fun k f f' hf => esZ_orth f f' hf)

theorem labelIdempotent_central (a) : e0L H Lb what₂ h K * a = a * e0L H Lb what₂ h K :=
  seriesIdempotent_central _ _ (fun k f a => esZ_central f a) a

theorem labelIdempotent_ne_zero (ht : THyp H) : e0L H Lb what₂ h K ≠ 0 :=
  seriesIdempotent_ne_zero _ _ (fun k f => esZ_idem f) (fun k f f' hf => esZ_orth f f' hf)
    (tupL Lb) (goodT_tupL H Lb what₂ h) (fun k v => by
      unfold esL esZ tupL
      by_cases hv : decide (v.1 ≠ 0) = true
      · rw [if_pos hv, if_pos rfl]; exact one_sub_eT_ne_zero (zL H k) (zL_ne_one H ht k)
      · rw [if_neg hv, if_neg (Lb.ne k).symm, if_pos rfl]; exact eT_ne_zero)

def qcL (g : G0g (ndG H Lb what₂ h)) : ℚ := (e0L H Lb what₂ h ℚ).coeff g

theorem labelIdempotent_coeff (g) : (e0L H Lb what₂ h K).coeff g = (qcL H Lb what₂ h g : K) := by
  unfold qcL e0L e0F
  rw [eSum_coeff, eSum_coeff, Rat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    show (esZ K _ _ _ _).coeff _ = ((esZ ℚ _ _ _ _).coeff _ : K)
    rw [esZ_coeff, esZ_coeff, Rat.cast_id]
  · simp

end Field

theorem labelIdempotent_mem_center : e0L H Lb what₂ h ℂ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) :=
  Subalgebra.mem_center_iff.mpr fun b => (labelIdempotent_central H Lb what₂ h ℂ b).symm

def omL (ht : THyp H) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) →ₐ[ℂ] ℂ :=
  (exists_char _ (labelIdempotent_mem_center H Lb what₂ h) (labelIdempotent_idem H Lb what₂ h ℂ) (labelIdempotent_ne_zero H Lb what₂ h ℂ ht)).choose

theorem labelCharacter_idempotent_one (ht : THyp H) : omL H Lb what₂ h ht ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ = 1 :=
  (exists_char _ (labelIdempotent_mem_center H Lb what₂ h) (labelIdempotent_idem H Lb what₂ h ℂ) (labelIdempotent_ne_zero H Lb what₂ h ℂ ht)).choose_spec

set_option synthInstance.maxHeartbeats 400000 in

def ntypesL (ht : THyp H) (htm : TameHyp H) : NTypes (nautL H what₂ h (labL Lb) (labL_monic Lb)) where
  Mray := H.E
  Mray_gal := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  Mray_ab := galK_comm H
  Mray_unr := discr_prime H
  g_Mray := h.hg
  g_cond := ht.cond
  BB_disj := ht.bb
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    rw [Multiset.mem_singleton.mp hp]; exact ⟨Nat.pos_of_ne_zero (r_ne_zero R), one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by simp
  tg := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose
  tg_mem := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose_spec.1
  tg_gen := fun k v => (htm k _ ((nautL H what₂ h (labL Lb) (labL_monic Lb)).plGw_over k v)).choose_spec
  inertiaCharpoly_type := fun k v L hL => by
    have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have h0 : Multiset.card (L : Multiset ℂˣ) = 0 := hL.symm.trans natDegree_one
    show (X - 1 : ℂ[X]) ^ Multiset.card (L : Multiset ℂˣ) =
      ((Formalism.CyclotomicNorms.rootsBar (1 : (ZMod (H.g k))[X])).map fun x => X - C (@teichToC (H.g k) ⟨H.g_prime k⟩ x)).prod
    rw [h0]
    simp [Formalism.CyclotomicNorms.rootsBar]
  chiT_tg := fun i => i.elim
  heckeLoc_gamma_places := fun i => i.elim
  iota := fun k _ w => @teichIota (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩
  iota_inj := fun k _ w => @teichIota_inj (H.g k) (what₂.places.resChar w) ⟨H.g_prime k⟩
    ⟨what₂.places.resChar_prime w⟩
  teichC := fun k => @teichToC (H.g k) ⟨H.g_prime k⟩
  teichC_inj := fun k _ _ _ _ e => @teichToC_injective (H.g k) ⟨H.g_prime k⟩ _ _ e
  eSer := esL Lb ℂ
  eSer_idem := fun k f => esZ_idem (K := ℂ) f
  eSer_central := fun k f a => esZ_central (K := ℂ) f a
  eSer_orth := fun k f f' hff => esZ_orth (K := ℂ) f f' hff
  eSer_zero := fun k f hf => by
    unfold esL esZ
    rw [if_neg (fun e : f = Lb.fA k => hf (e ▸ Lb.okA k)), if_neg (fun e : f = Lb.fB k => hf (e ▸ Lb.okB k))]
  eSer_sum := fun k => by
    have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
    have hfin : {f : (ZMod (H.g k))[X] | f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0}.Finite := by
      apply (Set.finite_range (fun a : Fin R.r → ZMod (H.g k) => Formalism.CyclotomicNorms.monicOf a)).subset
      rintro f ⟨hm, hd, -⟩
      exact ⟨fun i => f.coeff i, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
    exact ⟨hfin.toFinset, fun f => by simp, esZ_sum (K := ℂ) (Lb.ne k) _ (by simpa using Lb.okA k)
      (by simpa using Lb.okB k)⟩
  cenAmb := fun μ => (Algebra.ofId ℂ (Module.End ℂ (what₂.Amb μ))).comp (omL H Lb what₂ h ht)
  cenMt := fun μ j => (Algebra.ofId ℂ (Module.End ℂ (what₂.Mt μ j))).comp (omL H Lb what₂ h ht)
  Par := Empty
  labPar := fun _ σ => σ.elim
  labPar_monic := fun _ σ => σ.elim
  locPar := fun σ => σ.elim
  locPar_dim := fun σ => σ.elim
  labPar_def := fun _ σ => σ.elim
  MtPar := fun _ _ σ => σ.elim
  AmbPar := fun _ σ => σ.elim

theorem labelNewtypes_idempotent_eq (ht htm) : (ntypesL H Lb what₂ h ht htm).e0 = e0L H Lb what₂ h ℂ := e0_eq _


theorem ntypesL_E0Tie (ht htm) (hA : ∀ μ, what₂.eOp μ = 1) (hM : ∀ μ j, what₂.eMt μ j = 1) :
    (ntypesL H Lb what₂ h ht htm).IdempotentMatchesAction := by
  have key : (⟨(ntypesL H Lb what₂ h ht htm).e0, idempotent_mem_center _⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h)))) = ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ :=
    Subtype.ext (labelNewtypes_idempotent_eq H Lb what₂ h ht htm)
  refine ⟨fun μ => ?_, fun μ j => ?_⟩
  · rw [hA, ambientAction_idempotent, key]
    show (1 : Module.End ℂ (what₂.Amb μ)) = Algebra.ofId ℂ _ (omL H Lb what₂ h ht _)
    rw [labelCharacter_idempotent_one, map_one]
  · rw [hM, matrixAction_idempotent, key]
    show (1 : Module.End ℂ (what₂.Mt μ j)) = Algebra.ofId ℂ _ (omL H Lb what₂ h ht _)
    rw [labelCharacter_idempotent_one, map_one]

theorem labelIdempotent_baseField [NumberField what₂.LL] (LL0 : IntermediateField ℚ what₂.LL) (ht htm) (g) :
    what₂.embLL (((qcL H Lb what₂ h g : ℚ) : ↥LL0) : what₂.LL) = (ntypesL H Lb what₂ h ht htm).e0.coeff g := by
  rw [labelNewtypes_idempotent_eq, labelIdempotent_coeff]
  simp

end Formalism.BasicNotions.Examples₂.NZ
end
end
