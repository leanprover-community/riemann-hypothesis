import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs

section
noncomputable section

namespace PI.WGL.LTB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem initMinor_perm {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (σ : Equiv.Perm (Fin s)) :
    initMinor R (n := m) (I ∘ σ) hs = (Equiv.Perm.sign σ : ℤ) • initMinor R (n := m) I hs := by
  unfold initMinor
  first
  | (rw [zsmul_eq_mul, ← Matrix.det_permute]; rfl)
  | (rw [← Units.smul_def, ← Matrix.det_permute]; rfl)

theorem initMinor_not_inj {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (hI : ¬ Function.Injective I) : initMinor R (n := m) I hs = 0 := by
  unfold initMinor
  unfold Function.Injective at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq hne (by ext q; simp [hij])

theorem initMinor_std {R : Type*} [CommRing R] {r m s : ℕ} (hr : s ≤ r) (hs : s ≤ m) :
    initMinor R (n := m) (fun p : Fin s => (⟨p.1, lt_of_lt_of_le p.2 hr⟩ : Fin r)) hs = lpMinor R s hr hs := by
  rfl

theorem unl_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) (σ : Equiv.Perm (Fin m)) :
    unl h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • unl h ρ hm := by
  unfold unl
  exact initMinor_perm (eRow h ∘ ρ) hm σ

theorem liftRows_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (σ : Equiv.Perm (Fin m)) :
    liftRows h (ρ ∘ σ) = liftRows h ρ ∘ (σ.viaFintypeEmbedding Fin.castSuccEmb) := by
  funext p
  induction p using Fin.lastCases with
  | last =>
    have hnot : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) := by
      rintro ⟨y, hy⟩
      have h1 : y.val = m := by
        have := congrArg Fin.val hy
        exact this
      have h2 := y.2
      omega
    rw [Function.comp_apply]
    first
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range _ _ hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range hnot]
    | rw [Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range hnot]
    simp [liftRows]
  | cast i =>
    rw [Function.comp_apply]
    have e := Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i
    rw [show Fin.castSucc i = (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) i from rfl, e]
    simp [liftRows]

theorem lif_perm {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (σ : Equiv.Perm (Fin m)) :
    lif h (ρ ∘ σ) hm = (Equiv.Perm.sign σ : ℤ) • lif h ρ hm := by
  unfold lif
  rw [liftRows_perm, initMinor_perm]
  rw [show Equiv.Perm.sign (σ.viaFintypeEmbedding Fin.castSuccEmb) = Equiv.Perm.sign σ from
    Equiv.Perm.sign_extendDomain σ _]

theorem unl_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N)
    (hρ : ¬ Function.Injective ρ) : unl h ρ hm = 0 := by
  unfold unl
  exact initMinor_not_inj _ hm (fun hinj => hρ hinj.of_comp)

theorem lif_not_inj {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N)
    (hρ : ¬ Function.Injective ρ) : lif h ρ hm = 0 := by
  unfold lif
  refine initMinor_not_inj _ hm (fun hinj => hρ (fun a b hab => ?_))
  have h2 : liftRows h ρ (Fin.castSucc a) = liftRows h ρ (Fin.castSucc b) := by
    simp [liftRows, hab]
  exact Fin.castSucc_inj.mp (hinj h2)

theorem sum_cnt_lt {n K : ℕ} {sz : Fin K → ℕ} (J : ∀ k, Fin (sz k) → Fin n) (t : ℕ) :
    ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), tupCnt J a := by
  unfold tupCnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := J k) (t := Finset.univ.filter fun a : Fin n => a.1 < t)
    (by intro p hp; simpa using hp)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hp => hp.2
  · intro hp
    exact ⟨by rw [hp]; exact ha, hp⟩

private theorem card_filter_fin_val_lt' {n c : ℕ} (hc : c ≤ n) :
    (Finset.univ.filter fun a : Fin n => a.1 < c).card = c := by
  have e : (Finset.univ.filter fun a : Fin n => a.1 < c).card = (Finset.range c).card := by
    apply Finset.card_bij (fun a _ => a.1)
    · intro a ha
      simpa using ha
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      have hb' : b < c := by simpa using hb
      exact ⟨⟨b, by omega⟩, by simpa using hb', rfl⟩
  rw [e, Finset.card_range]

theorem sum_shape_lt {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (t : ℕ) (ht : t ≤ n) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), shapeDeg sz a = ∑ k, min t (sz k) := by
  unfold shapeDeg
  have e : ∀ k : Fin K, min t (sz k) = (Finset.univ.filter fun a : Fin n => a.1 < t ∧ a.1 < sz k).card := by
    intro k
    rw [← card_filter_fin_val_lt' (n := n) (c := min t (sz k)) (le_trans (min_le_left _ _) ht)]
    apply congrArg Finset.card
    ext a
    simp [lt_min_iff]
  simp only [e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a.1 < t <;> simp [ha]

theorem top_entries {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hc : tupCnt J = shapeDeg sz) : ∀ k p, (J k p).1 < sz k := by
  intro k p
  have key : ∀ t, t ≤ n → ∀ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = min t (sz k) := by
    intro t ht
    have hle : ∀ k ∈ Finset.univ, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card ≤ min t (sz k) := by
      intro k _
      refine le_min ?_ ?_
      · calc _ ≤ (Finset.univ.filter fun a : Fin n => a.1 < t).card :=
              Finset.card_le_card_of_injOn (J k) (by intro p hp; simpa using hp)
                (by intro a _ b _ hab; exact hinj k hab)
          _ = t := card_filter_fin_val_lt' ht
      · exact (Finset.card_filter_le _ _).trans (by simp)
    have hsum : ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card = ∑ k, min t (sz k) := by
      rw [sum_cnt_lt J t, hc, sum_shape_lt sz hsz t ht]
    exact fun k => (Finset.sum_eq_sum_iff_of_le hle).mp hsum k (Finset.mem_univ _)
  have h1 := key (sz k) (hsz k) k
  rw [min_self] at h1
  have h2 : (Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h1]
    simp
  have h3 : p ∈ Finset.univ.filter fun q : Fin (sz k) => (J k q).1 < sz k := by
    rw [h2]
    exact Finset.mem_univ _
  simpa using h3

theorem top_perm {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (J : ∀ k, Fin (sz k) → Fin n)
    (hinj : ∀ k, Function.Injective (J k)) (hlt : ∀ k p, (J k p).1 < sz k) :
    ∀ k, ∃ σ : Equiv.Perm (Fin (sz k)), J k = stdT sz hsz k ∘ σ := by
  intro k
  let f : Fin (sz k) → Fin (sz k) := fun p => ⟨(J k p).1, hlt k p⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj k
    exact Fin.ext (by simpa [f] using congrArg Fin.val hab)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  funext p
  exact Fin.ext rfl

theorem card_eq_val {m n : ℕ} (a : Fin n) :
    (Finset.univ.filter fun p : Fin m => p.1 = a.1).card = if a.1 < m then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨a.1, h⟩, ?_⟩
    ext p
    simp [Fin.ext_iff]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    exact h (by have := p.2; omega)

theorem tupCnt_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : tupCnt (stdT sz hsz) = shapeDeg sz := by
  funext a
  unfold tupCnt shapeDeg
  rw [Finset.card_filter (fun k : Fin K => a.1 < sz k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← card_eq_val (m := sz k) a]
  apply congrArg Finset.card
  ext p
  simp [stdT, Fin.ext_iff]

theorem prod_sz {M : Type*} [CommMonoid M] {K : ℕ} (sz : Fin K → ℕ) (s : Finset (Fin K)) (bnd : ℕ)
    (hb : ∀ k ∈ s, sz k < bnd) (F : ℕ → M) :
    ∏ k ∈ s, F (sz k) = ∏ y ∈ Finset.range bnd, F y ^ (s.filter fun k => sz k = y).card := by
  rw [Finset.prod_comp F sz]
  apply Finset.prod_subset
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Finset.mem_range.mpr (hb k hk)
  · intro y _ hy
    rw [Finset.mem_image] at hy
    have e : s.filter (fun k => sz k = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk hky
      exact hy ⟨k, hk, hky⟩
    rw [e, Finset.card_empty, pow_zero]

theorem count_succ {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (s : Fin n) :
    (Finset.univ.filter fun k => sz k = s.1 + 1).card = shapeDeg sz s - nuNext (shapeDeg sz) s := by
  unfold nuNext shapeDeg
  split_ifs with h
  · try simp only [Fin.val_mk]
    have hsub : (Finset.univ.filter fun k : Fin K => s.1 + 1 < sz k) ⊆ Finset.univ.filter fun k : Fin K => s.1 < sz k := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    first
    | rw [← Finset.card_sdiff_of_subset hsub]
    | rw [← Finset.card_sdiff hsub]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  · rw [Nat.sub_zero]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hsz k
    have h2 := s.2
    omega

theorem bidet_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (ν : Fin n → ℕ) (hsh : shapeDeg sz = ν) :
    bideterminant ℤ sz hsz (stdT sz hsz) = hw ℤ (r := n) le_rfl ν := by
  subst hsh
  unfold bideterminant hw
  let F : ℕ → MvPolynomial (Fin n × Fin n) ℤ := fun y => if hy : y ≤ n then lpMinor ℤ y hy hy else 1
  have h1 : ∀ k, initMinor ℤ (stdT sz hsz k) (hsz k) = F (sz k) := by
    intro k
    have e : F (sz k) = lpMinor ℤ (sz k) (hsz k) (hsz k) := dif_pos (hsz k)
    rw [e]
    exact initMinor_std (hsz k) (hsz k)
  simp only [h1]
  rw [prod_sz sz Finset.univ (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) F, Finset.prod_range_succ']
  have h0 : F 0 = 1 := by
    have e : F 0 = lpMinor ℤ 0 (Nat.zero_le n) (Nat.zero_le n) := dif_pos (Nat.zero_le n)
    rw [e]
    simp [lpMinor]
  rw [h0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [count_succ sz hsz s]
  have e : F (s.1 + 1) = lpMinor ℤ (s.1 + 1) (by have := s.2; omega) (by have := s.2; omega) :=
    dif_pos (by have := s.2; omega)
  rw [e]

theorem prod_zsmul' {R : Type*} [CommRing R] {K : ℕ} (a : Fin K → ℤ) (x : Fin K → R) :
    ∏ k, (a k • x k) = (∏ k, a k) • ∏ k, x k := by
  simp only [zsmul_eq_mul, Finset.prod_mul_distrib, Int.cast_prod]

theorem natW_last {n : ℕ} (sg : DomWeight n) (hn : 0 < n) : sg.natW ⟨n - 1, by omega⟩ = 0 := by
  simp [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, hn]

theorem natW_add {n : ℕ} (sg : DomWeight n) (i : Fin n) : ((sg.natW i : ℕ) : ℤ) + sg.detShift = sg.w i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hle : sg.detShift ≤ sg.w i := by
    unfold Formalism.BasicNotions.DomWeight.detShift
    rw [dif_pos hn]
    exact sg.anti (Fin.le_iff_val_le_val.mpr (by show i.1 ≤ n - 1; have := i.2; omega))
  simp only [Formalism.BasicNotions.DomWeight.natW]
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
  ring

theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (k : Fin K) (hk : 0 < sz k) : sz k < n := by
  have hn : 0 < n := lt_of_lt_of_le hk (hsz k)
  by_contra hcon
  have heq : sz k = n := le_antisymm (hsz k) (not_lt.mp hcon)
  have h1 := congrFun hsh ⟨n - 1, by omega⟩
  rw [natW_last sg hn] at h1
  unfold shapeDeg at h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ k) (by simp; omega)

theorem lif_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hk : sz k < n) (hm : sz k + 1 ≤ N) :
    lif h (stdT sz hsz k) hm = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk⟩) hm := by
  unfold lif
  congr 1
  funext p
  simp [liftRows, rowsZ, stdT, eRow]
  have hp := p.2
  split_ifs <;> first | rfl | (exfalso; omega)

theorem unl_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hm : sz k ≤ N) : unl h (stdT sz hsz k) hm = lpMinor ℤ (r := N) (n := N) (sz k) hm hm := by
  unfold unl
  exact initMinor_std hm hm

private theorem card_filter_not_mem_sz_eq_succ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) (s : Fin n) :
    (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      if s.1 + 1 = n then 0 else (aa h lam sg s).toNat := by
  unfold Interlace at hI
  unfold GoodL at hL
  have hs0 := s.2
  have e1 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => k ∈ L) =
      Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have e2 : ((Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).filter fun k => ¬ k ∈ L) =
      Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have htot : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card +
      (Finset.univ.filter fun k => ¬ k ∈ L ∧ sz k = s.1 + 1).card =
      (Finset.univ.filter fun k : Fin K => sz k = s.1 + 1).card := by
    rw [← e1, ← e2]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_not _
  have hc := count_succ sz hsz s
  rw [hsh] at hc
  unfold nuNext at hc
  split_ifs with hs
  · rw [dif_neg (show ¬ (s.1 + 1 < n) by omega)] at hc
    have hlast : sg.natW s = 0 := by
      have e : s = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e]
      exact natW_last sg (by omega)
    omega
  · have hs' : s.1 + 1 < n := by omega
    have hL1 : s.1 + 1 < N := by omega
    rw [dif_pos hs'] at hc
    have hb : (Finset.univ.filter fun k => k ∈ L ∧ sz k = s.1 + 1).card =
        (lam.w ⟨s.1 + 1, hL1⟩ - sg.w ⟨s.1 + 1, hs'⟩).toNat := by
      have := hL.2 ⟨s.1 + 1, hs'⟩
      rw [if_neg (show ¬ (((⟨s.1 + 1, hs'⟩ : Fin n) : ℕ) = 0) by simp)] at this
      exact this
    have hI1 : lam.w ⟨s.1 + 1, hL1⟩ ≤ sg.w s := (hI s).2
    have hI2 : sg.w ⟨s.1 + 1, hs'⟩ ≤ lam.w ⟨s.1 + 1, hL1⟩ := (hI ⟨s.1 + 1, hs'⟩).1
    have ha : ((sg.natW s : ℕ) : ℤ) + sg.detShift = sg.w s := natW_add sg s
    have hb2 : ((sg.natW ⟨s.1 + 1, hs'⟩ : ℕ) : ℤ) + sg.detShift = sg.w ⟨s.1 + 1, hs'⟩ := natW_add sg _
    have hX := Int.toNat_of_nonneg (sub_nonneg.mpr hI1)
    have hY := Int.toNat_of_nonneg (sub_nonneg.mpr hI2)
    show _ = (sg.w s - lam.w ⟨s.1 + 1, hL1⟩).toNat
    omega

theorem mlift_std {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hsh : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg := by
  have hL' := hL
  unfold GoodL at hL'
  have hN : ∀ k, sz k + 1 ≤ N := fun k => by have := hsz k; omega
  unfold Mlift xi
  rw [Finset.prod_ite]
  let A : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j < n then initMinor ℤ (n := N) (rowsZ h ⟨j, hj⟩) (by show j + 1 ≤ N; omega) else 1
  let B : ℕ → MvPolynomial (Fin N × Fin N) ℤ := fun j =>
    if hj : j ≤ N then lpMinor ℤ (r := N) (n := N) j hj hj else 1
  have hA : ∀ k ∈ Finset.univ.filter (fun k => k ∈ L), lif h (stdT sz hsz k) (hN k) = A (sz k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hk' : sz k < n := sz_lt sg sz hsz hsh k (hL'.1 k hk)
    rw [lif_std h sz hsz k hk' (hN k)]
    have e : A (sz k) = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk'⟩) (hN k) := dif_pos hk'
    rw [e]
  have hB : ∀ k ∈ Finset.univ.filter (fun k => ¬ k ∈ L),
      unl h (stdT sz hsz k) (by have := hsz k; omega) = B (sz k) := by
    intro k _
    have hk' : sz k ≤ N := by have := hsz k; omega
    rw [unl_std h sz hsz k hk']
    have e : B (sz k) = lpMinor ℤ (r := N) (n := N) (sz k) hk' hk' := dif_pos hk'
    rw [e]
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB]
  rw [prod_sz sz (Finset.univ.filter fun k => k ∈ L) n
    (fun k hk => sz_lt sg sz hsz hsh k (hL'.1 k (by simpa using hk))) A]
  rw [prod_sz sz (Finset.univ.filter fun k => ¬ k ∈ L) (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) B,
    Finset.prod_range_succ']
  have hB0 : B 0 = 1 := by
    have e : B 0 = lpMinor ℤ (r := N) (n := N) 0 (Nat.zero_le N) (Nat.zero_le N) := dif_pos (Nat.zero_le N)
    rw [e]
    simp [lpMinor]
  rw [hB0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  unfold C0
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi := i.2
  have cL : ((Finset.univ.filter fun k => k ∈ L).filter fun k => sz k = i.1).card =
      if i.1 = 0 then 0 else (bb h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact hL'.2 i
  have cN : ((Finset.univ.filter fun k => ¬ k ∈ L).filter fun k => sz k = i.1 + 1).card =
      if i.1 + 1 = n then 0 else (aa h lam sg i).toNat := by
    rw [Finset.filter_filter]
    exact card_filter_not_mem_sz_eq_succ h lam sg hI sz hsz hsh L hL i
  have eA : A i.1 = initMinor ℤ (n := N) (rowsZ h i) (by omega) := dif_pos hi
  have eB : B (i.1 + 1) = lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega) := dif_pos (by omega)
  rw [cL, cN, eA, eB]
  split_ifs <;> ring

theorem top_component_formula : TopPart := by
  intro n N h lam sg hI K sz hsz hsh L hL
  have hext : bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg := by
    rw [bidet_std sz hsz _ hsh]
    unfold extremal
    rfl
  refine ⟨?_, (tupCnt_std sz hsz).trans hsh, hext, mlift_std h lam sg hI sz hsz hsh L hL⟩
  intro J hJ
  by_cases hinj : ∀ k, Function.Injective (J k)
  · have hlt := top_entries sz hsz J hinj (hJ.trans hsh.symm)
    choose σ hσ using top_perm sz hsz J hinj hlt
    refine ⟨∏ k, (Equiv.Perm.sign (σ k) : ℤ), ?_, ?_⟩
    · have e1 : bideterminant ℤ sz hsz J = (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • bideterminant ℤ sz hsz (stdT sz hsz) := by
        unfold bideterminant
        rw [← prod_zsmul']
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k, initMinor_perm]
      rw [e1, hext]
    · have e2 : Mlift h lam sg sz hsz L J =
          (∏ k, (Equiv.Perm.sign (σ k) : ℤ)) • Mlift h lam sg sz hsz L (stdT sz hsz) := by
        unfold Mlift
        rw [← mul_smul_comm, ← prod_zsmul']
        congr 1
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [hσ k]
        split_ifs
        · exact lif_perm h _ _ _
        · exact unl_perm h _ _ _
      rw [e2, mlift_std h lam sg hI sz hsz hsh L hL]
  · obtain ⟨k0, hk0⟩ := not_forall.mp hinj
    refine ⟨0, ?_, ?_⟩
    · rw [zero_smul]
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (initMinor_not_inj _ _ hk0)
    · rw [zero_smul]
      unfold Mlift
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ k0)
      try dsimp only
      split_ifs
      · exact lif_not_inj h _ _ hk0
      · exact unl_not_inj h _ _ hk0

end PI.WGL.LTB
end
end

section
noncomputable section

namespace PI.WGL.LTA

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def upd {m r : ℕ} (ρ : Fin m → Fin r) (S : Finset (Fin m)) (a : Fin r) : Fin m → Fin r :=
  fun p => if p ∈ S then a else ρ p

def gmin {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) : MvPolynomial (Fin r × Fin c) ℤ :=
  (Matrix.of fun p q : Fin m => (X (ρ p, κ q) : MvPolynomial (Fin r × Fin c) ℤ)).det

theorem rowGen_Xz {r c : ℕ} (a b : Fin r) (v : Fin r × Fin c) :
    rowGen ℤ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  unfold rowGen
  rw [aeval_X]

theorem rowGen_gmin {r c m : ℕ} (a b : Fin r) (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    rowGen ℤ a b (gmin ρ κ) =
      ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
        Polynomial.X ^ S.card * Polynomial.C (gmin (upd ρ S a) κ) else 0 := by
  classical
  set A : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => Polynomial.C (X (ρ i, κ (σ i))) with hA
  set B : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => if ρ i = b then Polynomial.X * Polynomial.C (X (a, κ (σ i))) else 0 with hB
  have h1 : rowGen ℤ a b (gmin ρ κ) =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, (B σ i + A σ i) := by
    unfold gmin
    rw [AlgHom.map_det, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowGen_Xz,
      hA, hB]
    ring
  have h2 : ∀ S : Finset (Fin m), gmin (upd ρ S a) κ =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ •
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
    intro S
    unfold gmin
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [h1]
  simp only [Finset.prod_add, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · rw [h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hBS : ∏ i ∈ S, B σ i =
        Polynomial.X ^ S.card * Polynomial.C (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [Finset.prod_congr rfl (fun i hi => show B σ i = Polynomial.X * Polynomial.C (X (a, κ (σ i))) by
        simp [hB, hS i hi])]
      rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
    have hAS : ∏ i ∈ Finset.univ \ S, A σ i =
        Polynomial.C (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [map_prod]
    have hprod : (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) *
        (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) =
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ S)]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, (Finset.mem_sdiff.mp hi).2]
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, hi]
    rw [hBS, hAS, ← hprod, Units.smul_def, Units.smul_def, map_zsmul, map_mul]
    simp only [zsmul_eq_mul]
    ring
  · push_neg at hS
    obtain ⟨p, hp, hpb⟩ := hS
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero hp (by simp [hB, hpb]), zero_mul, smul_zero]

def Exp {r c n m : ℕ} (e : Fin n → Fin r) (G : (Fin m → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) : Prop :=
  ∀ (a b : Fin n) (ρ : Fin m → Fin n), rowGen ℤ (e a) (e b) (G ρ) =
    ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
      Polynomial.X ^ S.card * Polynomial.C (G (upd ρ S a)) else 0

theorem exp_gmin {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (κ : Fin m → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (e ∘ ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (∀ p ∈ S, (e ∘ ρ) p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
    simp only [Function.comp_apply, he.eq_iff]
  have h2 : upd (e ∘ ρ) S (e a) = e ∘ upd ρ S a := by
    funext p
    simp only [upd, Function.comp_apply]
    split_ifs <;> rfl
  by_cases hc : ∀ p ∈ S, ρ p = b
  · rw [if_pos hc, if_pos (h1.mpr hc), h2]
  · rw [if_neg hc, if_neg (fun h => hc (h1.mp h))]

theorem sum_finset_castSucc {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Finset (Fin (m + 1)) → M)
    (hf : ∀ S, Fin.last m ∈ S → f S = 0) :
    ∑ S : Finset (Fin (m + 1)), f S = ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) := by
  classical
  have hm : ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).map (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding, f S := by
    rw [Finset.sum_map]
    rfl
  rw [hm]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro S _ hS
  apply hf
  by_contra hl
  apply hS
  rw [Finset.mem_map]
  refine ⟨S.preimage Fin.castSucc (Fin.castSucc_injective m).injOn, Finset.mem_univ _, ?_⟩
  ext x
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.mem_map, Finset.mem_preimage,
    Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    have hxl : x ≠ Fin.last m := fun h => hl (h ▸ hx)
    exact ⟨x.castPred hxl, by simpa using hx, by simp⟩

def liftR {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) : Fin (m + 1) → Fin r :=
  fun p => if hp : p.1 < m then e (ρ ⟨p.1, hp⟩) else z

theorem liftR_castSucc {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) (q : Fin m) :
    liftR e z ρ (Fin.castSucc q) = e (ρ q) := by
  simp [liftR]

theorem liftR_last {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) :
    liftR e z ρ (Fin.last m) = z := by
  simp [liftR]

theorem exp_lift {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (z : Fin r)
    (hz : ∀ b, e b ≠ z) (κ : Fin (m + 1) → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (liftR e z ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin, sum_finset_castSucc]
  · refine Finset.sum_congr rfl fun S _ => ?_
    beta_reduce
    have h1 : (∀ p ∈ S.map Fin.castSuccEmb, liftR e z ρ p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
      simp [liftR_castSucc, he.eq_iff]
    have h2 : upd (liftR e z ρ) (S.map Fin.castSuccEmb) (e a) = liftR e z (upd ρ S a) := by
      funext p
      induction p using Fin.lastCases with
      | last =>
        have hl : Fin.last m ∉ S.map Fin.castSuccEmb := by
          simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
          intro q _ hq
          exact (Fin.castSucc_lt_last q).ne hq
        simp [upd, hl, liftR_last]
      | cast q =>
        have hm : Fin.castSucc q ∈ S.map Fin.castSuccEmb ↔ q ∈ S := Finset.mem_map' Fin.castSuccEmb
        simp only [upd, liftR_castSucc, hm]
        split_ifs <;> rfl
    by_cases hc : ∀ p ∈ S, ρ p = b
    · rw [if_pos (h1.mpr hc), if_pos hc, h2, Finset.card_map]
    · rw [if_neg (fun h => hc (h1.mp h)), if_neg hc]
  · intro S hS
    beta_reduce
    rw [if_neg]
    intro hall
    exact hz b ((liftR_last e z ρ).symm.trans (hall _ hS)).symm

theorem rowDiv_prod {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    rowDiv ℤ (e a) (e b) t (C0 * ∏ k, G k (I k)) =
      ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
        C0 * ∏ k, G k (upd (I k) (F k) a) else 0 := by
  classical
  unfold rowDiv
  rw [map_mul, hC, map_prod, Finset.prod_congr rfl (fun k _ => hG k a b (I k)), Fintype.prod_sum,
    Finset.mul_sum, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.prod_ite_zero]
  by_cases hA : ∀ k ∈ (Finset.univ : Finset (Fin K)), ∀ p ∈ F k, I k p = b
  · rw [if_pos hA, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod Polynomial.C]
    rw [show Polynomial.C C0 * (Polynomial.X ^ (∑ k, (F k).card) *
          Polynomial.C (∏ k, G k (upd (I k) (F k) a))) =
        Polynomial.monomial (∑ k, (F k).card) (C0 * ∏ k, G k (upd (I k) (F k) a)) by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
      ring]
    rw [Polynomial.coeff_monomial]
    have hA' : ∀ k, ∀ p ∈ F k, I k p = b := fun k => hA k (Finset.mem_univ k)
    by_cases hs : ∑ k, (F k).card = t
    · rw [if_pos hs, if_pos ⟨hA', hs⟩]
    · rw [if_neg hs, if_neg (fun h => hs h.2)]
  · rw [if_neg hA, mul_zero, Polynomial.coeff_zero, if_neg]
    intro h
    exact hA (fun k _ => h.1 k)

def tmat {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) (I : ∀ k, Fin (sz k) → Fin n) :
    (∀ k, Fin (sz k) → Fin n) →₀ ℤ :=
  ∑ F : (∀ k, Finset (Fin (sz k))), if (∀ k, ∀ p ∈ F k, I k p = b) ∧ ∑ k, (F k).card = t then
    Finsupp.single (fun k => upd (I k) (F k) a) 1 else 0

def tlin {n K : ℕ} (sz : Fin K → ℕ) (a b : Fin n) (t : ℕ) :
    ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (tmat sz a b t)

theorem rowDiv_comb {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ) (a b : Fin n) (hC : rowGen ℤ (e a) (e b) C0 = Polynomial.C C0)
    (t : ℕ) (d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ) :
    rowDiv ℤ (e a) (e b) t (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (tlin sz a b t d) := by
  classical
  have hsm : ∀ (z : ℤ) (x : MvPolynomial (Fin r × Fin c) ℤ),
      rowDiv ℤ (e a) (e b) t (z • x) = z • rowDiv ℤ (e a) (e b) t x := by
    intro z x
    unfold rowDiv
    rw [map_smul, Polynomial.coeff_smul]
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · unfold rowDiv
    simp
  · intro f g hf hg
    rw [map_add, map_add, map_add]
    unfold rowDiv at hf hg ⊢
    rw [map_add, Polynomial.coeff_add, hf, hg]
  · intro J c
    unfold tlin
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, hsm,
      rowDiv_prod e sz G hG C0 a b hC t J]
    congr 1
    unfold tmat
    rw [map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs
    · rw [Finsupp.linearCombination_single, one_smul]
    · rw [map_zero]

def twd {n K : ℕ} (sz : Fin K → ℕ) : List (Fin n × Fin n × ℕ) →
    (((∀ k, Fin (sz k) → Fin n) →₀ ℤ) →ₗ[ℤ] ((∀ k, Fin (sz k) → Fin n) →₀ ℤ))
  | [] => LinearMap.id
  | x :: w => (tlin sz x.1 x.2.1 x.2.2).comp (twd sz w)

theorem applyWord_comb {r c n K : ℕ} (e : Fin n → Fin r) (sz : Fin K → ℕ)
    (G : ∀ k, (Fin (sz k) → Fin n) → MvPolynomial (Fin r × Fin c) ℤ) (hG : ∀ k, Exp e (G k))
    (C0 : MvPolynomial (Fin r × Fin c) ℤ)
    (hC : ∀ a b : Fin n, a ≠ b → rowGen ℤ (e a) (e b) C0 = Polynomial.C C0) :
    ∀ (w : List (Fin n × Fin n × ℕ)), OffDiag w → ∀ d,
      applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d) =
      Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) (twd sz w d)
  | [], _, _ => rfl
  | x :: w, hw, d => by
    have hx : x.1 ≠ x.2.1 := hw x List.mem_cons_self
    have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    show rowDiv ℤ (e x.1) (e x.2.1) x.2.2 (applyWord ℤ (w.map fun x => (e x.1, e x.2.1, x.2.2))
        (Finsupp.linearCombination ℤ (fun J => C0 * ∏ k, G k (J k)) d)) = _
    rw [applyWord_comb e sz G hG C0 hC w hw' d, rowDiv_comb e sz G hG C0 x.1 x.2.1 (hC _ _ hx)]
    rfl

end PI.WGL.LTA
end
end

section
noncomputable section

namespace PI.WGL.LTC

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM

theorem eRow_inj {n N : ℕ} (h : n + 1 = N) : Function.Injective (eRow h) := by
  intro a b hab
  have h1 := congrArg Fin.val hab
  simp only [eRow] at h1
  exact Fin.ext (by simpa using h1)

theorem eRow_ne_last {n N : ℕ} (h : n + 1 = N) (b : Fin n) : eRow h b ≠ ⟨N - 1, by omega⟩ := by
  intro hb
  have h1 := congrArg Fin.val hb
  have h2 := b.2
  simp [eRow] at h1
  omega

theorem exp_bidet {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K) :
    Exp (id : Fin n → Fin n) (fun ρ : Fin (sz k) → Fin n => initMinor ℤ (n := n) ρ (hsz k)) := exp_gmin id Function.injective_id (Fin.castLE (hsz k))

theorem exp_M {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) :
    Exp (eRow h) (fun ρ : Fin (sz k) → Fin n =>
      if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega)) := by
  intro a b ρ
  by_cases hk : k ∈ L
  · simp only [hk, if_true, ite_true]
    exact exp_lift (eRow h) (eRow_inj h) ⟨N - 1, by omega⟩ (eRow_ne_last h)
      (Fin.castLE (by have := hsz k; omega)) a b ρ
  · simp only [hk, if_false, ite_false]
    exact exp_gmin (eRow h) (eRow_inj h) (Fin.castLE (by have := hsz k; omega)) a b ρ

theorem rowGen_gmin_inv {r c m : ℕ} (a b : Fin r) (hab : a ≠ b) (ρ : Fin m → Fin r) (κ : Fin m → Fin c)
    (hρ : (∃ pa, ρ pa = a) ∨ ∀ p, ρ p ≠ b) :
    rowGen ℤ a b (gmin ρ κ) = Polynomial.C (gmin ρ κ) := by
  classical
  rw [rowGen_gmin, Finset.sum_eq_single ∅]
  · have hu : upd ρ ∅ a = ρ := by
      funext p
      simp [upd]
    simp [hu]
  · intro S _ hS
    split_ifs with hc
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rcases hρ with ⟨pa, hpa⟩ | hρ
      · have hne : pa ≠ p0 := by
          intro h
          apply hab
          rw [← hpa, h]
          exact hc p0 hp0
        have hpaS : pa ∉ S := fun h => hab (hpa.symm.trans (hc pa h))
        have hz : gmin (upd ρ S a) κ = 0 := by
          unfold gmin
          apply Matrix.det_zero_of_row_eq hne
          funext q
          simp [upd, hpaS, hp0, hpa]
        simp [hz]
      · exact absurd (hc p0 hp0) (hρ p0)
    · rfl
  · simp

theorem polarization_of_constant {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (a b : Fin n) (hab : a ≠ b) :
    rowGen ℤ (eRow h a) (eRow h b) (C0 h lam sg) = Polynomial.C (C0 h lam sg) := by
  have hab' : eRow h a ≠ eRow h b := fun h' => hab (eRow_inj h h')
  have hlp : ∀ i : Fin n, i.1 + 1 = n → ∀ (hr : i.1 + 1 ≤ N) (hc : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (lpMinor ℤ (i.1 + 1) hr hc) = Polynomial.C (lpMinor ℤ (i.1 + 1) hr hc) := by
    intro i hi hr hc
    have ha := a.2
    exact rowGen_gmin_inv _ _ hab' (Fin.castLE hr) (Fin.castLE hc)
      (Or.inl ⟨⟨a.1, by omega⟩, Fin.ext (by simp [eRow])⟩)
  have hrz : ∀ i : Fin n, i.1 = 0 → ∀ (hs : i.1 + 1 ≤ N),
      rowGen ℤ (eRow h a) (eRow h b) (initMinor ℤ (rowsZ h i) hs) = Polynomial.C (initMinor ℤ (rowsZ h i) hs) := by
    intro i hi hs
    refine rowGen_gmin_inv _ _ hab' (rowsZ h i) (Fin.castLE hs) (Or.inr fun p hp => ?_)
    have hp0 : p.1 = i.1 := by have := p.2; omega
    apply eRow_ne_last h b
    rw [← hp]
    simp [rowsZ, hp0]
  unfold C0
  simp only [map_prod, map_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  · split_ifs with hi
    · rw [map_pow, map_pow, hlp i hi]
    · simp
  · split_ifs with hi
    · rw [map_pow, map_pow, hrz i hi]
    · simp

theorem word_clause {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) :
    ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
      applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
      applyWord ℤ (liftWord h w) (Mlift h lam sg sz hsz L I) =
        d.sum (fun J c => c • Mlift h lam sg sz hsz L J) := by
  classical
  refine ⟨twd sz w (Finsupp.single I 1), ?_, ?_⟩
  · have hmap : w.map (fun x => (id x.1, id x.2.1, x.2.2)) = w := by
      induction w with
      | nil => rfl
      | cons x w ih => simp
    have h1 := applyWord_comb id sz (fun k ρ => initMinor ℤ (n := n) ρ (hsz k)) (exp_bidet sz hsz) 1
      (fun a b _ => by simp) w hw (Finsupp.single I 1)
    rw [hmap, Finsupp.linearCombination_single, one_smul] at h1
    simp only [one_mul, Finsupp.linearCombination_apply] at h1
    unfold bideterminant
    exact h1
  · have h2 := applyWord_comb (eRow h) sz
      (fun k ρ => if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (exp_M h sz hsz L) (C0 h lam sg) (fun a b hab => polarization_of_constant h lam sg a b hab) w hw (Finsupp.single I 1)
    rw [Finsupp.linearCombination_single, one_smul] at h2
    simp only [Finsupp.linearCombination_apply] at h2
    unfold Mlift
    exact h2

end PI.WGL.LTC
end
end

section
noncomputable section

namespace PI.WGL.LTD

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC

theorem sum_ite_val {n : ℕ} (f : Fin n → ℕ) (j : ℕ) :
    (∑ i : Fin n, if i.1 = j then f i else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i _ hi; rw [if_neg]; intro h'; exact hi (Fin.ext h')
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero; intro i _; rw [if_neg]; intro h'; exact hj (h' ▸ i.2)

theorem natW_sg_val {n : ℕ} (sg : DomWeight n) (i : Fin n) :
    ((sg.natW i : ℕ) : ℤ) = sg.w i - sg.w ⟨n - 1, by have := i.2; omega⟩ := by
  have hle : i ≤ ⟨n - 1, by have := i.2; omega⟩ := by rw [Fin.le_def]; simp; have := i.2; omega
  have := sg.anti hle
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n by have := i.2; omega)]
  rw [Int.toNat_of_nonneg (by omega)]

theorem card_lt_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (t : Fin n) : (Finset.univ.filter fun k => t.1 < sz k).card = sg.natW t := by
  rw [← hshape]; rfl

theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hshape : shapeDeg sz = sg.natW) (k : Fin K) : sz k < n ∨ sz k = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · right; have := hsz k; omega
  · left
    have h1 := card_lt_sz sg sz hshape ⟨n - 1, by omega⟩
    have h0 : sg.natW ⟨n - 1, by omega⟩ = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, dif_pos hn]
    rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have hk := h1 (Finset.mem_univ k)
    simp only [not_lt] at hk
    have := hsz k
    omega

theorem card_eq_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (i : ℕ) (hi : i + 1 < n) :
    (Finset.univ.filter fun k => sz k = i + 1).card = sg.natW ⟨i, by omega⟩ - sg.natW ⟨i + 1, hi⟩ := by
  have h1 := card_lt_sz sg sz hshape ⟨i, by omega⟩
  have h2 := card_lt_sz sg sz hshape ⟨i + 1, hi⟩
  simp only at h1 h2
  rw [← h1, ← h2]
  have : (Finset.univ.filter fun k => i < sz k) =
      (Finset.univ.filter fun k => i + 1 < sz k) ∪ (Finset.univ.filter fun k => sz k = i + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  rw [this, Finset.card_union_of_disjoint]
  · omega
  · rw [Finset.disjoint_filter]; intro k _ h1 h2; omega

theorem goodL_exists {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW) :
    ∃ L : Finset (Fin K), GoodL h lam sg sz L := by
  classical
  have hB : ∀ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) ≤
      (Finset.univ.filter fun k => sz k = i.1).card := by
    intro i
    split_ifs with hi0
    · exact Nat.zero_le _
    · obtain ⟨iv, hiv⟩ := i
      obtain ⟨j, rfl⟩ : ∃ j, iv = j + 1 := ⟨iv - 1, by simp at hi0; omega⟩
      have hc := card_eq_sz sg sz hshape j hiv
      simp only at hc ⊢
      rw [hc]
      have e1 := natW_sg_val sg ⟨j, by omega⟩
      have e2 := natW_sg_val sg ⟨j + 1, hiv⟩
      have hb := (hI ⟨j + 1, hiv⟩).1
      have ha := (hI ⟨j, by omega⟩).2
      unfold bb
      simp only at hb ha e1 e2 ⊢
      omega
  choose T hT using fun i : Fin n => Finset.exists_subset_card_eq (hB i)
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.mp hk
    have hs := (hT i).1 hki
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    by_cases hi0 : i.1 = 0
    · have hc := (hT i).2
      rw [if_pos hi0, Finset.card_eq_zero] at hc
      rw [hc] at hki; exact absurd hki (Finset.notMem_empty k)
    · omega
  · intro i
    rw [← (hT i).2]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j, hkj⟩, hsk⟩
      have hs := (hT j).1 hkj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have : j = i := Fin.ext (by omega)
      subst this; exact hkj
    · intro hki
      have hs := (hT i).1 hki
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact ⟨⟨i, hki⟩, hs⟩

end PI.WGL.LTD
end
end

section
noncomputable section

namespace PI.WGL.LTE

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

private theorem mul_mem_dualWeyl_int {N : ℕ} {ν ν' : Fin N → ℕ} {f g : MvPolynomial (Fin N × Fin N) ℤ}
    (hf : f ∈ dualWeyl ℤ N N ν) (hg : g ∈ dualWeyl ℤ N N ν') : f * g ∈ dualWeyl ℤ N N (ν + ν') := by
  unfold dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at hf hg ⊢
    exact hf.1.mul hg.1
  · have h1 := hf.2
    have h2 := hg.2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at h1 h2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, h1 l j hlj, h2 l j hlj]

private theorem one_mem_dualWeyl_int {N : ℕ} : (1 : MvPolynomial (Fin N × Fin N) ℤ) ∈ dualWeyl ℤ N N 0 := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one ℤ _
  · simp [Submodule.mem_iInf, LinearMap.mem_ker]

private theorem initMinor_mem_dualWeyl_int_initW {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    initMinor ℤ I hs ∈ dualWeyl ℤ N N (initW N s) := by
  have h := bidetMem ℤ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant ℤ (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor ℤ (n := N) I hs := by
    unfold bideterminant
    simp
  have e2 : shapeDeg (n := N) (fun _ : Fin 1 => s) = initW N s := by
    funext t
    unfold shapeDeg initW
    split_ifs with ht <;> simp [ht]
  rw [e1, e2] at h
  exact h

theorem pow_memZ {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) (k : ℕ) : f ^ k ∈ dualWeyl ℤ N N (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl_int
  | succ k ih => rw [pow_succ, succ_nsmul]; exact mul_mem_dualWeyl_int ih hf

theorem prod_memZ {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℤ)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl ℤ N N (ν i)) :
    ∏ i ∈ s, f i ∈ dualWeyl ℤ N N (∑ i ∈ s, ν i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (one_mem_dualWeyl_int (N := N))
  · intro a s ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_int (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ite_pow_memZ {N s : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N (initW N s)) (e : ℕ) :
    (if c then f ^ e else 1) ∈ dualWeyl ℤ N N ((if c then e else 0) • initW N s) := by
  split_ifs
  · exact pow_memZ _ f hf e
  · simpa using (one_mem_dualWeyl_int (N := N))

def colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Fin N → ℕ :=
  (∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • initW N (i.1 + 1))) +
  ∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k))

theorem Mlift_mem_colWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) :
    Mlift h lam sg sz hsz L I ∈ dualWeyl ℤ N N (colWt h lam sg sz L) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N), lpMinor ℤ s hr hc ∈ dualWeyl ℤ N N (initW N s) :=
    fun s hr hc => initMinor_mem_dualWeyl_int_initW (Fin.castLE hr) hc
  unfold Mlift colWt
  apply mul_mem_dualWeyl_int
  · unfold C0
    refine prod_memZ Finset.univ _ _ fun i _ => ?_
    exact mul_mem_dualWeyl_int (ite_pow_memZ _ _ (hlp _ _ _) _) (ite_pow_memZ _ _ (initMinor_mem_dualWeyl_int_initW _ _) _)
  · refine prod_memZ Finset.univ _ _ fun k _ => ?_
    split_ifs
    · unfold lif
      exact initMinor_mem_dualWeyl_int_initW _ _
    · unfold unl
      exact initMinor_mem_dualWeyl_int_initW _ _

theorem lam_natW_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (t : ℕ) (ht : t < N) :
    ((lam.natW ⟨t, ht⟩ : ℕ) : ℤ) = lam.w ⟨t, ht⟩ - lam.w ⟨n, by omega⟩ := by
  subst h
  have hds : lam.detShift = lam.w ⟨n, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos (by omega)]
    exact congrArg lam.w (Fin.ext (by simp))
  have hle : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨t, ht⟩ :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by show t ≤ n; omega))
  unfold DomWeight.natW
  rw [hds]
  omega

theorem lam_detShift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) :
    lam.detShift = lam.w ⟨n, by omega⟩ := by
  subst h
  unfold DomWeight.detShift
  rw [dif_pos (by omega)]
  exact congrArg lam.w (Fin.ext (by simp))

theorem sg_detShift {n : ℕ} (sg : DomWeight n) (hn : 0 < n) :
    sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
  unfold DomWeight.detShift
  rw [dif_pos hn]

theorem aLast_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (hn : 0 < n) :
    (((aa h lam sg ⟨n - 1, by omega⟩).toNat : ℕ) : ℤ) = sg.w ⟨n - 1, by omega⟩ - lam.w ⟨n, by omega⟩ := by
  have h2 := (hI ⟨n - 1, by omega⟩).2
  have e : lam.w ⟨(⟨n - 1, by omega⟩ : Fin n).1 + 1, by omega⟩ = lam.w ⟨n, by omega⟩ :=
    congrArg lam.w (Fin.ext (by simp only; omega))
  unfold aa
  omega

theorem b_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : ℕ) (ht : t < n) :
    (((bb h lam sg ⟨t, ht⟩).toNat : ℕ) : ℤ) = lam.w ⟨t, by omega⟩ - sg.w ⟨t, ht⟩ := by
  have h1 := (hI ⟨t, ht⟩).1
  have e : lam.w ⟨(⟨t, ht⟩ : Fin n).1, by omega⟩ = lam.w ⟨t, by omega⟩ := rfl
  unfold bb
  omega

theorem colWt_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) : colWt h lam sg sz L = lam.natW := by
  classical
  funext t
  obtain ⟨tv, htv⟩ := t
  unfold colWt
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]

  have hP : (∑ i : Fin n, (if i.1 + 1 = n then (aa h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * initW N (n - 1 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (aa h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) (n - 1)]
    apply Finset.sum_congr rfl
    intro i _
    have := i.2
    by_cases hi : i.1 + 1 = n
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega), zero_mul]
  have hQ : (∑ i : Fin n, (if i.1 = 0 then (bb h lam sg i).toNat else 0) * initW N (i.1 + 1) ⟨tv, htv⟩) =
      if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * initW N (0 + 1) ⟨tv, htv⟩ else 0 := by
    rw [← sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat * initW N (i.1 + 1) ⟨tv, htv⟩) 0]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 = 0
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, zero_mul]

  have hK : (∑ k : Fin K, (if k ∈ L then initW N (sz k + 1) else initW N (sz k)) ⟨tv, htv⟩) =
      (Finset.univ.filter fun k => tv < sz k).card +
        (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ L
    · simp only [hk, if_true, true_and, initW]
      split_ifs <;> omega
    · simp only [hk, if_false, false_and, initW]
      split_ifs <;> omega
  rw [hP, hQ, hK]
  by_cases htn : tv < n
  · have hn : 0 < n := by omega
    have h1 := card_lt_sz sg sz hshape ⟨tv, htn⟩
    have h2 := hL.2 ⟨tv, htn⟩
    simp only at h1 h2
    rw [h1, h2, dif_pos (by omega), dif_pos hn]
    have e1 := natW_sg_val sg ⟨tv, htn⟩
    have e2 := lam_natW_val h lam tv htv
    have e3 := aLast_val h lam sg hI hn
    have e4 := b_val h lam sg hI tv htn
    have hw1 : initW N (n - 1 + 1) ⟨tv, htv⟩ = 1 := by simp only [initW]; rw [if_pos (by simp; omega)]
    rw [hw1, mul_one]
    by_cases ht0 : tv = 0
    · subst ht0
      have hw2 : initW N (0 + 1) ⟨0, htv⟩ = 1 := by simp [initW]
      rw [hw2, mul_one, if_pos rfl]
      simp only at e1 e2 e3 e4 ⊢
      have := sg.anti (show (⟨0, htn⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by rw [Fin.le_def]; simp)
      omega
    · have hw2 : initW N (0 + 1) ⟨tv, htv⟩ = 0 := by simp only [initW]; rw [if_neg (by simp; omega)]
      rw [hw2, mul_zero, if_neg ht0]
      simp only at e1 e2 e3 e4 ⊢
      omega
  · have htn' : tv = n := by omega
    subst htn'
    have h1 : (Finset.univ.filter fun k => tv < sz k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro k _; have := hsz k; omega
    have h2 : (Finset.univ.filter fun k => k ∈ L ∧ sz k = tv).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := hL.1 k hk.1
      rcases sz_lt sg sz hsz hshape k with h3 | h3 <;> omega
    rw [h1, h2]
    have e2 := lam_natW_val h lam tv htv
    have hz : lam.natW ⟨tv, htv⟩ = 0 := by
      have : (⟨tv, htv⟩ : Fin N) = ⟨tv, by omega⟩ := rfl
      omega
    rw [hz]
    have hw1 : ∀ j, j ≤ tv → initW N j ⟨tv, htv⟩ = 0 := by
      intro j hj; simp only [initW]; rw [if_neg (by simp; omega)]
    split_ifs with ha hb
    · rw [hw1 _ (by omega), hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · rw [hw1 _ (by omega)]; simp
    · simp

end PI.WGL.LTE
end
end

section
noncomputable section

namespace PI.WGL.LTF

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem gmin_rowW {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    IsWeightedHomogeneous (rowW r c) (gmin ρ κ) (∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)) := by
  classical
  unfold gmin
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun p => (X (ρ (σ p), κ p) : MvPolynomial (Fin r × Fin c) ℤ))
    (fun p => rowW r c (ρ (σ p), κ p)) (fun p _ => isWeightedHomogeneous_X ℤ _ _)
  have hsum : ∑ p, rowW r c (ρ (σ p), κ p) = ∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ) := by
    simp only [rowW]
    exact Equiv.sum_comp σ (fun p => (Pi.single (ρ p) 1 : Fin r → ℕ))
  rw [hsum] at hp
  simpa [Matrix.of_apply] using hp

theorem bidet_rowW {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I) := by
  unfold bideterminant
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k))
    (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))
  convert hp using 1
  funext a
  simp only [tupCnt, Finset.sum_apply, Pi.single_apply]
  simp [eq_comm]

def w0r {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Fin N → ℕ :=
  ∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))

theorem ite_pow_rowW {N : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ) (w : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f w) (e : ℕ) :
    IsWeightedHomogeneous (rowW N N) (if c then f ^ e else 1) ((if c then e else 0) • w) := by
  split_ifs
  · exact hf.pow e
  · simpa using isWeightedHomogeneous_one ℤ (rowW N N)

theorem constant_weighted_homogeneous {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    IsWeightedHomogeneous (rowW N N) (C0 h lam sg) (w0r h lam sg) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N),
      IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (initW N s) := by
    intro s hr hc
    have hg : IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc)
        (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) := gmin_rowW (Fin.castLE hr) (Fin.castLE hc)
    have hw : (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) = initW N s := by
      funext t
      simp only [Finset.sum_apply, Pi.single_apply, initW, Fin.ext_iff, Fin.coe_castLE]
      rw [show (∑ p : Fin s, if (t : ℕ) = (p : ℕ) then 1 else 0) = ∑ p : Fin s, if (p : ℕ) = t.1 then 1 else 0 from
        Finset.sum_congr rfl (fun p _ => by simp only [eq_comm])]
      rw [sum_ite_val (fun _ => 1) t.1]
      simp
    rw [hw] at hg
    exact hg
  unfold C0 w0r
  refine IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ => ?_
  refine IsWeightedHomogeneous.mul ?_ ?_
  · exact ite_pow_rowW _ _ _ (hlp _ _ _) _
  · exact ite_pow_rowW _ _ _ (gmin_rowW (rowsZ h i) (Fin.castLE _)) _

def wk {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (lifted : Prop) [Decidable lifted] : Fin N → ℕ :=
  (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) +
    (if lifted then (Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 : Fin N → ℕ) else 0)

theorem G_rowW {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) (ρ : Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N)
      (if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (wk h ρ (k ∈ L)) := by
  unfold wk
  split_ifs with hk
  · unfold lif
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (liftRows h ρ) (by have := hsz k; omega : sz k + 1 ≤ N))
        (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) :=
      gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))
    have hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) =
        (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 := by
      rw [Fin.sum_univ_castSucc]
      simp [liftRows]
    rw [hw] at hg
    exact hg
  · unfold unl
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (eRow h ∘ ρ) (by have := hsz k; omega : sz k ≤ N))
        (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) :=
      gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))
    rw [add_zero]
    exact hg

theorem constant_weight_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (av : ℕ) (hav : av < N) :
    w0r h lam sg ⟨av, hav⟩ =
      (if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * (if av < n then 1 else 0) else 0) +
      (if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * (if av = n then 1 else 0) else 0) := by
  unfold w0r
  have key : ∀ i : Fin n, (((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
      (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))
        ⟨av, hav⟩) =
      (if i.1 = n - 1 then (aa h lam sg i).toNat * (if av < n then 1 else 0) else 0) +
      (if i.1 = 0 then (bb h lam sg i).toNat * (if av = n then 1 else 0) else 0) := by
    intro i
    have hi2 := i.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · by_cases hi : i.1 + 1 = n
      · rw [if_pos hi, if_pos (by omega)]
        simp only [initW, hi]
      · rw [if_neg hi, if_neg (by omega), zero_mul]
    · by_cases hi : i.1 = 0
      · rw [if_pos hi, if_pos hi]
        congr 1
        rw [Finset.sum_apply]
        have e : ∀ p : Fin (i.1 + 1), (Pi.single (rowsZ h i p) 1 : Fin N → ℕ) ⟨av, hav⟩ =
            if av = n then 1 else 0 := by
          intro p
          have hp := p.2
          have hr : rowsZ h i p = ⟨N - 1, by omega⟩ := by
            simp only [rowsZ]
            rw [if_pos (by omega)]
          rw [hr, Pi.single_apply]
          by_cases hav' : av = n
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hav']
          · rw [if_neg (fun he => hav' (by have := congrArg Fin.val he; simp only at this; omega)), if_neg hav']
        rw [Finset.sum_congr rfl (fun p _ => e p), Finset.sum_const, Finset.card_univ, Fintype.card_fin, hi,
          smul_eq_mul, zero_add, one_mul]
      · rw [if_neg hi, if_neg hi, zero_mul]
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, sum_ite_val,
    sum_ite_val]

theorem cardL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) :
    L.card = ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL.2 i]
    congr 1
    ext k
    simp [Finset.mem_filter]
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range]
    replace hk := Finset.mem_coe.mp hk
    rcases sz_lt sg sz hsz hshape k with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))

theorem sumB {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    ((∑ i : Fin n, (bb h lam sg i).toNat : ℕ) : ℤ) = degZ lam sg - lam.detShift := by
  subst h
  have hb : ∀ i : Fin n, (((bb rfl lam sg i).toNat : ℕ) : ℤ) = lam.w (Fin.castSucc i) - sg.w i :=
    fun i => b_val rfl lam sg hI i.1 i.2
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_sub_distrib]
  unfold degZ wsum
  rw [Fin.sum_univ_castSucc (f := lam.w), lam_detShift rfl lam,
    show (Fin.last n) = (⟨n, by omega⟩ : Fin (n + 1)) from rfl]
  ring

end PI.WGL.LTF
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

namespace LTF

open PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem Mlift_rowW {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I) (liftWt h lam sg (tupCnt I)) := by
  classical
  have hH : IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I)
      (w0r h lam sg + ∑ k, wk h (I k) (k ∈ L)) :=
    (constant_weighted_homogeneous h lam sg).mul (IsWeightedHomogeneous.prod _ _ _ (fun k _ => G_rowW h sz hsz L k (I k)))
  convert hH using 1
  funext a
  obtain ⟨av, hav⟩ := a
  simp only [Pi.add_apply, Finset.sum_apply, wk, constant_weight_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
    Finset.sum_add_distrib, liftWt]
  by_cases ha : av < n
  · have hn : 0 < n := by omega
    rw [dif_pos ha, dif_pos (by omega), dif_pos hn, if_pos ha, if_neg (by omega)]
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : (⟨av, hav⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ := fun e => by rw [Fin.mk.injEq] at e; omega
      simp [hne]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) =
        tupCnt I ⟨av, ha⟩ := by
      simp only [tupCnt, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro q _
      have : ((⟨av, hav⟩ : Fin N) = eRow h (I k q)) ↔ (I k q = ⟨av, ha⟩) := by
        simp only [eRow, Fin.ext_iff]; exact eq_comm
      by_cases hq : I k q = ⟨av, ha⟩
      · rw [if_pos (this.2 hq), if_pos hq]
      · rw [if_neg (fun e => hq (this.1 e)), if_neg hq]
    rw [hS1, hS2]
    have e3 := aLast_val h lam sg hI hn
    have e4 := sg_detShift sg hn
    have e5 := lam_detShift h lam
    omega
  · have hav' : av = n := by omega
    simp only [dif_neg ha, if_neg ha, if_pos hav', mul_zero, mul_one]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro q _
      rw [if_neg]
      intro e
      simp only [eRow, Fin.ext_iff] at e
      have := (I k q).2
      omega
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) =
        L.card := by
      rw [Finset.sum_congr rfl (g := fun k => if k ∈ L then 1 else 0)]
      · rw [← Finset.card_filter]; congr 1; ext k; simp
      · intro k _
        rw [if_pos (Fin.ext (by simp; omega))]
    rw [hS1, hS2, cardL h lam sg sz hsz hshape L hL]
    have hsplit : (∑ i : Fin n, (bb h lam sg i).toNat) =
        (∑ i : Fin n, if i.1 = 0 then (bb h lam sg i).toNat else 0) +
          ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat) 0] at hsplit
    have e6 := sumB h lam sg hI
    unfold dLast
    split_ifs at hsplit ⊢ with h1 h2 <;> omega

end LTF

theorem tuple_decomposition_formula : TupleCore := by
  intro n N h lam sg hI K sz hsz hshape
  obtain ⟨L, hL⟩ := LTD.goodL_exists h lam sg hI sz hshape
  obtain ⟨htop, hstd1, hstd2, hstd3⟩ := LTB.top_component_formula n N h lam sg hI K sz hsz hshape L hL
  refine ⟨LTM.Mlift h lam sg sz hsz L, fun I => ⟨?_, LTF.Mlift_rowW h lam sg hI sz hsz hshape L hL I,
    LTF.bidet_rowW sz hsz I⟩, fun I w hw => LTC.word_clause h lam sg sz hsz L I w hw, htop,
    ⟨LTM.stdT sz hsz, hstd1, hstd2, hstd3⟩⟩
  have hm := LTE.Mlift_mem_colWt h lam sg sz hsz L I
  rw [LTE.colWt_eq h lam sg hI sz hsz hshape L hL] at hm
  exact hm

end PI.WGL
end
end
