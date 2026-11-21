import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma qs_dom_up {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hs : HStrip lam kap b) : Dominant kap := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hy : y.1 - 1 < n := by have := y.2; omega
    have h1 : (⟨y.1 - 1, hy⟩ : Fin n).1 + 1 < n := by
      have := y.2; have := Fin.lt_def.1 hlt; simp only; omega
    have h2 := hs.2.1 ⟨y.1 - 1, hy⟩ h1
    have h3 : (⟨(⟨y.1 - 1, hy⟩ : Fin n).1 + 1, h1⟩ : Fin n) = y := by
      apply Fin.ext; have := Fin.lt_def.1 hlt; simp only; omega
    rw [h3] at h2
    have h4 : lam ⟨y.1 - 1, hy⟩ ≤ lam x := hl (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact h2.trans (h4.trans (hs.1 x))

omit [NeZero n] in
lemma qs_dom_down {lam kap : Fin n → ℤ} {b : ℕ} (hk : Dominant kap) (hs : HStrip lam kap b) : Dominant lam := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have h1 : x.1 + 1 < n := by have := y.2; have := Fin.lt_def.1 hlt; omega
    have h2 := hs.2.1 x h1
    have h4 : kap y ≤ kap ⟨x.1 + 1, h1⟩ := hk (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact (hs.1 y).trans (h4.trans h2)

lemma qs_colH_strip {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (c : ℤ) : colH kap c = colH lam c ∨ colH kap c = colH lam c + 1 := by
  have h1 : colH lam c ≤ colH kap c := by
    by_contra hcon
    have hlt : colH kap c < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le lam c)
    have h2 := (qb_lt_colH_iff hl c ⟨colH kap c, hlt⟩).1 (not_le.1 hcon)
    have h3 := (qb_lt_colH_iff hk c ⟨colH kap c, hlt⟩).2 (h2.trans (hs.1 _))
    exact lt_irrefl _ h3
  have h2 : colH kap c ≤ colH lam c + 1 := by
    by_contra hcon
    have hlt : colH lam c + 1 < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le kap c)
    have h2 := (qb_lt_colH_iff hk c ⟨colH lam c + 1, hlt⟩).1 (not_le.1 hcon)
    have h3 := hs.2.1 ⟨colH lam c, by omega⟩ hlt
    have h4 := (qb_lt_colH_iff hl c ⟨colH lam c, by omega⟩).2 (h2.trans h3)
    exact lt_irrefl _ h4
  omega

def qs_D (lam kap : Fin n → ℤ) : Finset ℤ :=
  (Finset.Ioc (lam (lastIdx n)) (kap 0)).filter fun c => colH kap c = colH lam c + 1

lemma qs_D_sub (lam kap : Fin n → ℤ) : qs_D lam kap ⊆ Finset.Ioc (lam (lastIdx n)) (kap 0) := Finset.filter_subset _ _

lemma qs_mem_D {lam kap : Fin n → ℤ} (hl : Dominant lam) (hk : Dominant kap) (c : ℤ) :
    c ∈ qs_D lam kap ↔ colH kap c = colH lam c + 1 := by
  simp only [qs_D, mem_filter, mem_Ioc, and_iff_right_iff_imp]
  intro h
  constructor
  · by_contra hcon
    have := qs_colH_low hl (not_lt.1 hcon)
    have := colH_le kap c
    omega
  · by_contra hcon
    have := qs_colH_high hk (not_le.1 hcon)
    omega

def qs_mc (lam kap : Fin n → ℤ) : ↥(qs_D lam kap) → Fin n := fun c =>
  ⟨colH lam c.1, by have := (Finset.mem_filter.1 c.2).2; have := colH_le kap c.1; omega⟩

lemma qs_cnt_mc {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (x : Fin n) : ((qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = kap x - lam x := by
  have h1 : (univ.filter fun c : ↥(qs_D lam kap) => qs_mc lam kap c = x).map (Function.Embedding.subtype _) =
      Finset.Ioc (lam x) (kap x) := by
    ext c
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
      exists_and_right, exists_eq_right, mem_Ioc]
    have e1 := qb_lt_colH_iff hl c x
    have e2 := qb_lt_colH_iff hk c x
    constructor
    · rintro ⟨hc, hx⟩
      have h3 := (qs_mem_D hl hk c).1 hc
      have h4 : colH lam c = x.1 := congrArg Fin.val hx
      constructor
      · by_contra hcon; have := e1.2 (not_lt.1 hcon); omega
      · exact e2.1 (by omega)
    · rintro ⟨h3, h4⟩
      have h5 := e2.2 h4
      have h6 : ¬ x.1 < colH lam c := fun h => absurd (e1.1 h) (not_le.2 h3)
      have h7 := qs_colH_strip hl hk hs c
      exact ⟨(qs_mem_D hl hk c).2 (by omega), Fin.ext (by simp only [qs_mc]; omega)⟩
  rw [qs_cnt, ← Finset.card_map (Function.Embedding.subtype _), h1, Int.card_Ioc,
    Int.toNat_of_nonneg (by have := hs.1 x; omega)]

lemma qs_card_D {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b) :
    Fintype.card ↥(qs_D lam kap) = b := by
  have h1 := qs_sum_cnt (qs_mc lam kap)
  have h2 : ((∑ x, qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = (b : ℤ) := by
    rw [← hs.2.2]; push_cast
    exact Finset.sum_congr rfl fun x _ => qs_cnt_mc hl hk hs x
  rw [h1] at h2
  exact_mod_cast h2

omit [NeZero n] in
lemma qs_sg_ini (h : ℕ) (hh : h < n) : qs_sg (qs_ini h) (⟨h, hh⟩ : Fin n) = 1 := by
  have : (qs_ini h : Finset (Fin n)).filter ((⟨h, hh⟩ : Fin n) < ·) = ∅ := by
    ext x; simp only [qs_ini, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and, not_lt]
    intro hx; exact Fin.le_def.2 (by simp only; omega)
  rw [qs_sg, this]; simp

omit [NeZero n] in
lemma qs_ini_erase (h : ℕ) (hh : h < n) : (qs_ini (h + 1) : Finset (Fin n)).erase ⟨h, hh⟩ = qs_ini h := by
  ext x
  simp only [qs_ini, mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega

lemma qs_can_iff {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (m : ↥(qs_D lam kap) → Fin n) :
    ((∀ c : ↥(qs_D lam kap), m c ∈ qs_ext kap (canT kap) c.1) ∧
      qs_ext lam (canT lam) = qs_rem (qs_D lam kap) (qs_ext kap (canT kap)) m) ↔ m = qs_mc lam kap := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    have h3 := h1 c
    have h4 := congrFun h2 c.1
    have h5 := (qs_mem_D hl hk c.1).1 c.2
    rw [qs_rem_mem, qs_ext_can hl, qs_ext_can hk] at h4
    rw [qs_ext_can hk] at h3
    have h6 : m c ∉ (qs_ini (colH lam c.1) : Finset (Fin n)) := by rw [h4]; simp
    simp only [qs_ini, mem_filter, mem_univ, true_and] at h3 h6
    exact Fin.ext (by simp only [qs_mc]; omega)
  · rintro rfl
    refine ⟨fun c => ?_, ?_⟩
    · have h5 := (qs_mem_D hl hk c.1).1 c.2
      rw [qs_ext_can hk]
      simp only [qs_ini, qs_mc, mem_filter, mem_univ, true_and]; omega
    · funext c
      by_cases hc : c ∈ qs_D lam kap
      · have h5 := (qs_mem_D hl hk c).1 hc
        have h6 := qs_rem_mem (qs_D lam kap) (qs_ext kap (canT kap)) (qs_mc lam kap) ⟨c, hc⟩
        simp only at h6
        rw [h6, qs_ext_can hl, qs_ext_can hk, h5]
        exact (qs_ini_erase _ _).symm
      · rw [qs_rem_not _ _ _ hc, qs_ext_can hl, qs_ext_can hk]
        have h7 := qs_colH_strip hl hk hs c
        have h8 := (qs_mem_D hl hk c).not.1 hc
        congr 1; omega

lemma qs_rem_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (K : ℤ → Finset (Fin n)) (hK : ∀ c, (K c).card = colH kap c) (m : ↥(qs_D lam kap) → Fin n)
    (hm : ∀ c : ↥(qs_D lam kap), m c ∈ K c.1) (c : ℤ) : (qs_rem (qs_D lam kap) K m c).card = colH lam c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_rem_mem (qs_D lam kap) K m ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_erase_of_mem (hm ⟨c, hc⟩), hK, h5]; rfl
  · rw [qs_rem_not _ _ _ hc, hK]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

lemma qs_add_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (J : ℤ → Finset (Fin n)) (hJ : ∀ c, (J c).card = colH lam c) (a : ↥(qs_D lam kap) → Fin n)
    (ha : ∀ c : ↥(qs_D lam kap), a c ∉ J c.1) (c : ℤ) : (qs_add (qs_D lam kap) J a c).card = colH kap c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_add_mem (qs_D lam kap) J a ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_insert_of_notMem (ha ⟨c, hc⟩), hJ, h5]
  · rw [qs_add_not _ _ _ hc, hJ]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

open Classical in

def qs_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D mu nu) → Fin n,
    if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0)
    else 0

open Classical in

def qs_mid (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D mu nu), ((qs_sg (qs_ext mu J c.1) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0),
            qs_mn (qs_gC n) (qs_add (qs_D mu nu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0

open Classical in
theorem qs_ps_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_mid b mu nu J α K := by
  have hT : ∀ I, TMat mu J I = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ le_rfl (hs.1 0) J I
  have hm : ∀ m : ↥(qs_D mu nu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0), qs_mn (qs_gC n) (qs_ext mu J c) (qs_rem (qs_D mu nu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D mu nu), qs_gC n (a c) (m c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gC n) b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymMat n b α β *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_rem_card hmu hnu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gC n) (qs_card_D hmu hnu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D mu nu) → Fin n, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_ps, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core (qs_gC n) _ _ (qs_D_sub mu nu)]
  · simp only [if_neg h, Finset.sum_const_zero]

open Classical in
theorem qs_ps_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_mid b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ (hs.1 _) le_rfl K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D mu nu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((E c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D mu nu) → Fin n,
        if (∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_add (qs_D mu nu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_ps, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D mu nu) (qs_ext mu J) (qs_ext nu K') a
    by_cases h : (∀ c : ↥(qs_D mu nu), a c ∈ qs_ext nu K' c.1) ∧ qs_ext mu J = qs_rem (qs_D mu nu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.1 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_add_card hmu hnu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    have h3 : ∀ c : ↥(qs_D mu nu), (qs_add (qs_D mu nu) (qs_ext mu J) a c.1).erase (a c) = qs_ext mu J c.1 := by
      intro c; rw [qs_add_mem, Finset.erase_insert (h c)]
    simp only [h3]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp

theorem qs_ps_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b) :
    qs_ps b mu nu (canT mu, qs_mon (qs_card_D hmu hnu hs) (qs_mc mu nu)) (canT nu) = 1 := by
  rw [qs_ps, Finset.sum_eq_single (qs_mc mu nu)]
  · rw [if_pos ((qs_can_iff hmu hnu hs _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu, (qs_mem_D hmu hnu c.1).1 c.2]
    have hlt : colH mu c.1 < n := (qs_mc mu nu c).2
    show qs_sg ((qs_ini (colH mu c.1 + 1)).erase ⟨colH mu c.1, hlt⟩) ⟨colH mu c.1, hlt⟩ = 1
    rw [qs_ini_erase, qs_sg_ini]
  · intro m _ hm
    rw [if_neg (fun h => hm ((qs_can_iff hmu hnu hs _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero n] in
lemma qs_gC_torus : (qs_gC n).map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (1 : ℤ)) (1 : ℤ) := by
  ext a b
  simp only [Matrix.map_apply, qs_gC, Matrix.of_apply, qb_evGL_algebraMap, genMat, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X]
  rfl

omit [NeZero n] in
lemma qs_prod_torus (ε : ℤ) (f : Fin n → ℕ) :
    ∏ x, (AddMonoidAlgebra.single (Pi.single x ε : Fin n → ℤ) (1 : ℤ)) ^ (f x) =
      AddMonoidAlgebra.single (fun x => ε * (f x : ℤ)) 1 := by
  simp_rw [AddMonoidAlgebra.single_pow, one_pow]
  rw [qb_prod_single]
  congr 1
  funext y
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

omit [NeZero n] in
open Classical in
lemma qs_mem_strUp {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := (Finset.mem_filter.1 h).2

theorem symStrip_of : CntSym → SymStrip := by
  intro hc n _ b
  refine ⟨fun α x => ((α.1 x : ℕ) : ℤ), qs_ps b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by have := congrFun h x; simp only at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymMat_eq, qs_SM_map, qs_gC_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_up hmu (qs_mem_strUp hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    ext ⟨J, α⟩ K
    exact (qs_ps_left b hmu hnu' hs J α K).trans (qs_ps_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    refine ⟨qs_mon (qs_card_D hmu hnu' hs) (qs_mc mu nu), ?_, Or.inl (qs_ps_lead b hmu hnu' hs)⟩
    funext x
    exact qs_cnt_mc hmu hnu' hs x
  · intro mu hmu
    exact hc n mu b hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

open Classical in

def qs_psD (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D nu mu) → Fin n,
    if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0)
    else 0

open Classical in

def qs_midD (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D nu mu), ((qs_sg ((qs_ext mu J c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
            qs_mn (qs_gC n) (qs_rem (qs_D nu mu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0

open Classical in
theorem qs_psD_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_midD b mu nu J α K := by
  have hT : ∀ I, TMat mu J I =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ (hs.1 _) le_rfl J I
  have hm : ∀ m : ↥(qs_D nu mu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D nu mu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ nu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (nu (lastIdx n)) (mu 0),
                qs_mn (qs_gC n) (qs_ext mu J c) (qs_add (qs_D nu mu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D nu mu), qs_gI n (m c) (a c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gI n).transpose b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D nu mu), ((qs_sg (qs_ext nu K c.1) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymDMat n b α β *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧ qs_ext mu I = qs_add (qs_D nu mu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymDMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_add_card hnu hmu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gI n).transpose (qs_card_D hnu hmu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; simp only [Matrix.transpose_apply]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b,
      TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D nu mu) → Fin n, TMat mu J y.1 * SymDMat n b α y.2 *
        (((if (∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu K c.1) ∧
            qs_ext mu y.1 = qs_add (qs_D nu mu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D nu mu), qs_sg (qs_ext nu K c.1) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_psD, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core_inv (qs_gC n) (qs_gI n) (qs_gC_mul_gI n) _ _ (qs_D_sub nu mu)]
  · simp only [if_neg h, Finset.sum_const_zero]

open Classical in
theorem qs_psD_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_midD b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K =
      qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ le_rfl (hs.1 0) K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D nu mu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D nu mu), ((qs_sg (E c.1) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (nu (lastIdx n)) (Finset.Ioc (nu (lastIdx n)) (mu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D nu mu) → Fin n,
        if (∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_rem (qs_D nu mu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_psD, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D nu mu) (qs_ext nu K') (qs_ext mu J) a
    by_cases h : (∀ c : ↥(qs_D nu mu), a c ∉ qs_ext nu K' c.1) ∧
        qs_ext mu J = qs_add (qs_D nu mu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.2 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_midD]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_rem_card hnu hmu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D nu mu), a c ∈ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    simp only [qs_rem_mem]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp

theorem qs_psD_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b) :
    qs_psD b mu nu (canT mu, qs_mon (qs_card_D hnu hmu hs) (qs_mc nu mu)) (canT nu) = 1 := by
  have hiff : ∀ m : ↥(qs_D nu mu) → Fin n, ((∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu (canT nu) c.1) ∧
      qs_ext mu (canT mu) = qs_add (qs_D nu mu) (qs_ext nu (canT nu)) m) ↔ m = qs_mc nu mu := fun m =>
    (qs_rem_iff_add _ _ _ m).symm.trans (qs_can_iff hnu hmu hs m)
  rw [qs_psD, Finset.sum_eq_single (qs_mc nu mu)]
  · rw [if_pos ((hiff _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu]
    exact qs_sg_ini _ _
  · intro m _ hm
    rw [if_neg (fun h => hm ((hiff _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero n] in
lemma qs_gI_torus : (qs_gI n).transpose.map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1 : ℤ)) (1 : ℤ) := by
  have h1 : (qs_gC n).map (evGL (torusPt n)) * (qs_gI n).map (evGL (torusPt n)) = 1 := by
    rw [← Matrix.map_mul, qs_gC_mul_gI]; simp
  have h2 : (qs_gC n).map (evGL (torusPt n)) = (torusPt n).val := qs_gC_torus
  have h3 : (qs_gI n).map (evGL (torusPt n)) = (torusPt n).inv := by
    calc (qs_gI n).map (evGL (torusPt n)) = ((torusPt n).inv * (torusPt n).val) * (qs_gI n).map (evGL (torusPt n)) := by
          rw [(torusPt n).inv_val, Matrix.one_mul]
      _ = (torusPt n).inv := by rw [Matrix.mul_assoc, ← h2, h1, Matrix.mul_one]
  rw [Matrix.transpose_map, h3]
  exact Matrix.diagonal_transpose _

omit [NeZero n] in
open Classical in
lemma qs_mem_strDown {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b :=
  (Finset.mem_filter.1 h).2

theorem symDStrip_of : CntSymD → SymDStrip := by
  intro hc n _ b
  refine ⟨fun α x => -((α.1 x : ℕ) : ℤ), qs_psD b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by
      have := congrFun h x; simp only [neg_inj] at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymDMat_eq, qs_SM_map, qs_gI_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_down hmu (qs_mem_strDown hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    ext ⟨J, α⟩ K
    exact (qs_psD_left b hmu hnu' hs J α K).trans (qs_psD_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    refine ⟨qs_mon (qs_card_D hnu' hmu hs) (qs_mc nu mu), ?_, Or.inl (qs_psD_lead b hmu hnu' hs)⟩
    funext x
    have := qs_cnt_mc hnu' hmu hs x
    show -((qs_cnt (qs_mc nu mu) x : ℕ) : ℤ) = nu x - mu x
    omega
  · intro mu hmu
    exact hc n mu b hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
