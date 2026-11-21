import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColHSuccLe
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qr_ext {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  if e then insert (Fin.last m) (S.map Fin.castSuccEmb) else S.map Fin.castSuccEmb

section Ext

variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))

lemma qr_last_notMem : Fin.last m ∉ S.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h

lemma qr_mem_castSucc (a : Fin m) : a.castSucc ∈ qr_ext e S ↔ a ∈ S := by
  unfold qr_ext
  split_ifs <;> simp [(Fin.castSucc_lt_last a).ne]

lemma qr_mem_last : Fin.last m ∈ qr_ext e S ↔ e := by
  unfold qr_ext
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; exact qr_last_notMem S

lemma qr_ext_card : (qr_ext e S).card = S.card + if e then 1 else 0 := by
  unfold qr_ext
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (qr_last_notMem S), Finset.card_map]
  · rw [Finset.card_map]; rfl

lemma qr_ext_inj {S S' : Finset (Fin m)} (h : qr_ext e S = qr_ext e S') : S = S' := by
  ext a
  rw [← qr_mem_castSucc e S a, h, qr_mem_castSucc]

lemma qr_ext_surj (K : Finset (Fin (m + 1))) (h : Fin.last m ∈ K ↔ e) :
    K = qr_ext e (univ.filter fun a : Fin m => a.castSucc ∈ K) := by
  ext x
  induction x using Fin.lastCases with
  | last => rw [qr_mem_last, h]
  | cast a => rw [qr_mem_castSucc]; simp

lemma qr_filter_castSucc (t : Fin m) :
    ((qr_ext e S).filter (· ≤ t.castSucc)) = (S.filter (· ≤ t)).map Fin.castSuccEmb := by
  ext x
  induction x using Fin.lastCases with
  | last =>
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨_, h⟩; exact absurd h (not_le.2 (Fin.castSucc_lt_last t))
    · rintro ⟨a, _, h⟩; exact absurd h (Fin.castSucc_lt_last a).ne
  | cast a =>
    simp only [Finset.mem_filter, qr_mem_castSucc, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_inj,
      exists_eq_right, Fin.castSucc_le_castSucc_iff]

lemma qr_filter_last : ((qr_ext e S).filter (· ≤ Fin.last m)) = qr_ext e S := by
  apply Finset.filter_true_of_mem
  intro x _; exact Fin.le_last x

lemma qr_emb_map {k : ℕ} (h : S.card = k) (h' : (S.map Fin.castSuccEmb).card = k) :
    ⇑((S.map Fin.castSuccEmb).orderEmbOfFin h') = fun a => (S.orderEmbOfFin h a).castSucc := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a; simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono hab)

lemma qr_emb_insert {k : ℕ} (h : S.card = k) (h' : (insert (Fin.last m) (S.map Fin.castSuccEmb)).card = k + 1) :
    ⇑((insert (Fin.last m) (S.map Fin.castSuccEmb)).orderEmbOfFin h') =
      Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (S.orderEmbOfFin h a).castSucc) (Fin.last m) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    induction a using Fin.lastCases with
    | last => simp
    | cast a => simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Fin.castSucc_lt_last _
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.2 (Fin.le_last _))
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hab))

end Ext

section Block

variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

lemma qr_det_cast (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (fun a => (r a).castSucc) (fun a => (c a).castSucc)).det = (g1.val.submatrix r c).det := by
  congr 1
  ext a b
  exact hb.1 _ _

lemma qr_det_snoc (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).det =
      (t : R) * (g1.val.submatrix r c).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have h1 : ((h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).submatrix
        (Fin.last k).succAbove (Fin.last k).succAbove) = g1.val.submatrix r c := by
      ext a b
      simp [Fin.succAbove_last, hb.1]
    rw [h1]
    simp [hb.2.1, ← two_mul]
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
    simp [(hb.2.2 _).2]
  · simp

lemma qr_det_block (hb : IsBlock h g1 t) : h.val.det = (t : R) * g1.val.det := by
  have := qr_det_snoc hb (id : Fin m → Fin m) id
  have h1 : (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a : Fin m => (id a).castSucc) (Fin.last m)) = id := by
    funext a
    induction a using Fin.lastCases <;> simp
  rw [h1] at this
  simpa using this

lemma qr_minor_ext (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K' S : Finset (Fin m)) {k k' : ℕ}
    (hK' : K'.card = k') (hS' : S.card = k') (hK : (qr_ext e K').card = k) (hS : (qr_ext e S).card = k) :
    (h.val.submatrix ((qr_ext e K').orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det =
      (if e then (t : R) else 1) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
  by_cases he : e
  · have hk : k = k' + 1 := by rw [← hK, qr_ext_card, hK', if_pos he]
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k' + 1) (hB : B.card = k' + 1),
        A = insert (Fin.last m) (K'.map Fin.castSuccEmb) → B = insert (Fin.last m) (S.map Fin.castSuccEmb) →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (t : R) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_insert K' hK', qr_emb_insert S hS', qr_det_snoc hb]
    rw [if_pos he]
    exact key _ _ hK hS (by rw [qr_ext, if_pos he]) (by rw [qr_ext, if_pos he])
  · have hk : k = k' := by rw [← hK, qr_ext_card, hK', if_neg he]; rfl
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k) (hB : B.card = k),
        A = K'.map Fin.castSuccEmb → B = S.map Fin.castSuccEmb →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_map K' hK', qr_emb_map S hS', qr_det_cast hb]
    rw [if_neg he, one_mul]
    exact key _ _ hK hS (by rw [qr_ext, if_neg he]) (by rw [qr_ext, if_neg he])

lemma qr_minor_zero (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K : Finset (Fin (m + 1))) (S : Finset (Fin m))
    {k : ℕ} (hK : K.card = k) (hS : (qr_ext e S).card = k) (hne : ¬ (Fin.last m ∈ K ↔ e)) :
    (h.val.submatrix (K.orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det = 0 := by
  by_cases he : e
  · have hl : Fin.last m ∉ K := fun hl => hne ⟨fun _ => he, fun _ => hl⟩
    have h1 : Fin.last m ∈ Set.range ((qr_ext e S).orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact (qr_mem_last e S).2 he
    obtain ⟨b0, hb0⟩ := h1
    apply Matrix.det_eq_zero_of_column_eq_zero b0
    intro a
    rw [Matrix.submatrix_apply, hb0]
    have h2 : K.orderEmbOfFin hK a ≠ Fin.last m := fun h3 => hl (h3 ▸ Finset.orderEmbOfFin_mem K hK a)
    obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← ha']
    exact (hb.2.2 a').1
  · have hl : Fin.last m ∈ K := by
      by_contra hl; exact hne ⟨fun h => absurd h hl, fun h => absurd h he⟩
    have h1 : Fin.last m ∈ Set.range (K.orderEmbOfFin hK) := by
      rw [Finset.range_orderEmbOfFin]; exact hl
    obtain ⟨a0, ha0⟩ := h1
    apply Matrix.det_eq_zero_of_row_eq_zero a0
    intro b
    rw [Matrix.submatrix_apply, ha0]
    have h2 : (qr_ext e S).orderEmbOfFin hS b ≠ Fin.last m := fun h3 =>
      he ((qr_mem_last e S).1 (h3 ▸ Finset.orderEmbOfFin_mem _ hS b))
    obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← hb']
    exact (hb.2.2 b').2

end Block

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_lastIdx (m : ℕ) : lastIdx (m + 1) = Fin.last m := rfl

section Cols

variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_colH_le (hi : Interl lam nu) (c : ℤ) : colH nu c ≤ colH lam c := by
  unfold colH
  rw [← Finset.card_map Fin.castSuccEmb]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha.trans (hi a).1

lemma qr_colH_le' (hi : Interl lam nu) (c : ℤ) : colH lam c ≤ colH nu c + 1 := by
  unfold colH
  rw [← Finset.card_map (Fin.succEmb m)]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le (0 : Fin (m + 1)) _)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  induction x using Fin.cases with
  | zero => left; rfl
  | succ a => right; exact ⟨a, hx.trans (hi a).2, rfl⟩

lemma qr_colH_eq (hi : Interl lam nu) (c : ℤ) :
    colH lam c = colH nu c + if colH lam c = colH nu c + 1 then 1 else 0 := by
  have h1 := qr_colH_le hi c
  have h2 := qr_colH_le' hi c
  split_ifs with h <;> omega

lemma qr_sum_colH {n : ℕ} (mu : Fin n → ℤ) (L U : ℤ) (h : ∀ a, L ≤ mu a ∧ mu a ≤ U) :
    ∑ c ∈ Finset.Ioc L U, (colH mu c : ℤ) = ∑ a, (mu a - L) := by
  have h1 : ∀ c, (colH mu c : ℤ) = ∑ a, if c ≤ mu a then 1 else 0 := by
    intro c
    rw [colH, Finset.card_filter]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (Finset.Ioc L U).filter (fun c => c ≤ mu a) = Finset.Ioc L (mu a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have := (h a).2
    constructor
    · rintro ⟨⟨h3, _⟩, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h3, h4⟩; exact ⟨⟨h3, h4.trans this⟩, h4⟩
  rw [h2, Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.2 (h a).1)]

end Cols

section J

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

lemma qr_le_last (hn : Dominant nu) (a : Fin m) : nu (lastIdx m) ≤ nu a := by
  apply hn
  rw [Fin.le_def]
  show a.1 ≤ m - 1
  have := a.2
  omega

lemma qr_le_zero {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hn : Dominant mu) (a : Fin n) : mu a ≤ mu 0 := hn (Fin.zero_le a)

lemma qr_lam_last_le (hi : Interl lam nu) : lam (Fin.last m) ≤ nu (lastIdx m) := by
  have h := (hi (lastIdx m)).2
  have h1 : (lastIdx m).succ = Fin.last m := by
    apply Fin.ext
    show m - 1 + 1 = m
    have := NeZero.pos m
    omega
  rwa [h1] at h

lemma qr_nu_zero_le (hi : Interl lam nu) : nu 0 ≤ lam 0 := (hi 0).1

lemma qr_TCols_sub (hi : Interl lam nu) {c : ℤ} (hc : c ∈ TCols nu) : c ∈ TCols lam := by
  simp only [TCols, Finset.mem_Ioc, qr_lastIdx] at hc ⊢
  exact ⟨lt_of_le_of_lt (qr_lam_last_le hi) hc.1, hc.2.trans (qr_nu_zero_le hi)⟩

lemma qr_colH_low (hn : Dominant nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) : colH nu c = m := by
  rw [colH, Finset.filter_true_of_mem]
  · simp
  · intro a _; exact hc.trans (qr_le_last hn a)

lemma qr_colH_high (hn : Dominant nu) {c : ℤ} (hc : nu 0 < c) : colH nu c = 0 := by
  rw [colH, Finset.filter_false_of_mem]
  · simp
  · intro a _; exact not_le.2 (lt_of_le_of_lt (qr_le_zero hn a) hc)

lemma qr_subsing (hn : Dominant nu) {c : ℤ} (hc : c ∉ TCols nu) :
    Subsingleton {S : Finset (Fin m) // S.card = colH nu c} := by
  simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  constructor
  rintro ⟨S, hS⟩ ⟨S', hS'⟩
  apply Subtype.ext
  show S = S'
  rcases hc with hc | hc
  · rw [qr_colH_low hn hc] at hS hS'
    rw [Finset.eq_univ_of_card S (by simpa using hS), Finset.eq_univ_of_card S' (by simpa using hS')]
  · rw [qr_colH_high hn hc] at hS hS'
    rw [Finset.card_eq_zero.1 hS, Finset.card_eq_zero.1 hS']

def qr_can (nu : Fin m → ℤ) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  ⟨(univ : Finset (Fin (colH nu c))).map (Fin.castLEEmb (colH_le nu c)), by simp⟩

def qr_base (I' : TIdx nu) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  if h : c ∈ TCols nu then I' ⟨c, h⟩ else qr_can nu c

lemma qr_base_can (c : ℤ) : qr_base (canT nu) c = qr_can nu c := by
  unfold qr_base
  split_ifs <;> rfl

lemma qr_base_mem (I' : TIdx nu) (c : ↥(TCols nu)) : qr_base I' c = I' c := by
  unfold qr_base
  rw [dif_pos c.2]

def qr_j (hi : Interl lam nu) (I' : TIdx nu) : TIdx lam := fun c =>
  ⟨qr_ext (colH lam c = colH nu c + 1) (qr_base I' c).1, by
    rw [qr_ext_card, (qr_base I' c).2]; exact (qr_colH_eq hi c).symm⟩

lemma qr_j_inj (hi : Interl lam nu) : Function.Injective (qr_j (lam := lam) hi) := by
  intro I' K' h
  funext c
  have h1 := congrArg Subtype.val (congrFun h ⟨c.1, qr_TCols_sub hi c.2⟩)
  have h2 := qr_ext_inj _ h1
  rw [qr_base_mem, qr_base_mem] at h2
  exact Subtype.ext h2

lemma qr_j_surj (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam)
    (hK : ∀ c : ↥(TCols lam), (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1)) :
    ∃ K' : TIdx nu, qr_j hi K' = K := by
  have hc : ∀ c : ↥(TCols lam), (univ.filter fun a : Fin m => a.castSucc ∈ (K c).1).card = colH nu c := by
    intro c
    have h1 := congrArg Finset.card (qr_ext_surj _ (K c).1 (hK c))
    rw [qr_ext_card, (K c).2] at h1
    have h2 := qr_colH_eq hi c
    omega
  refine ⟨fun c => ⟨_, hc ⟨c.1, qr_TCols_sub hi c.2⟩⟩, ?_⟩
  funext c
  apply Subtype.ext
  show qr_ext _ _ = _
  rw [qr_ext_surj _ (K c).1 (hK c)]
  congr 1
  by_cases h : c.1 ∈ TCols nu
  · rw [qr_base, dif_pos h]
  · have := qr_subsing hn h
    exact congrArg Subtype.val (Subsingleton.elim (qr_base _ c.1) ⟨_, hc c⟩)

lemma qr_can_sub (c : ℤ) : (qr_can nu (c + 1)).1 ⊆ (qr_can nu c).1 := by
  intro x hx
  simp only [qr_can, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le nu c)⟩, rfl⟩

lemma qr_j_can_std (hi : Interl lam nu) : StdT (qr_j (lam := lam) hi (canT nu)) := by
  intro c hc t
  show ((qr_ext _ (qr_base (canT nu) (c.1 + 1)).1).filter (· ≤ t)).card ≤
    ((qr_ext _ (qr_base (canT nu) c.1).1).filter (· ≤ t)).card
  rw [qr_base_can, qr_base_can]
  induction t using Fin.lastCases with
  | last =>
    rw [qr_filter_last, qr_filter_last, qr_ext_card, qr_ext_card, (qr_can nu _).2, (qr_can nu _).2,
      ← qr_colH_eq hi, ← qr_colH_eq hi]
    exact qc_colH_succ_le lam c
  | cast t =>
    rw [qr_filter_castSucc, qr_filter_castSucc, Finset.card_map, Finset.card_map]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (qr_can_sub c.1))

end J

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_det_full {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = m)
    (S : Finset (Fin m)) (hS : S.card = k) :
    (A.submatrix (S.orderEmbOfFin hS) (S.orderEmbOfFin hS)).det = A.det := by
  subst hk
  exact Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (S.orderEmbOfFin hS).injective)) A

lemma qr_det_empty {m : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin m) (Fin m) R) {k : ℕ} (hk : k = 0)
    (r c : Fin k → Fin m) : (A.submatrix r c).det = 1 := by
  subst hk
  exact Matrix.det_fin_zero

section TM

variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

lemma qr_dU_block (hb : IsBlock h g1 t) : qc_dU h = t * qc_dU g1 := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qr_det_block hb]

lemma qr_TMat_zero (hb : IsBlock h g1 t) (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam) (I' : TIdx nu)
    (hK : ∀ K', qr_j hi K' ≠ K) : evGL h (TMat lam K (qr_j hi I')) = 0 := by
  have h1 : ∃ c : ↥(TCols lam), ¬ (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1) := by
    by_contra hcon
    obtain ⟨K', hK'⟩ := qr_j_surj hn hi K (fun c => by
      by_contra h2; exact hcon ⟨c, h2⟩)
    exact hK K' hK'
  obtain ⟨c, hc⟩ := h1
  simp only [TMat, map_mul, map_prod, qc_evGL_minorC]
  rw [Finset.prod_eq_zero (Finset.mem_univ c), mul_zero]
  exact qr_minor_zero hb _ _ _ _ _ hc

def qr_mn (g1 : GL (Fin m) R) {k : ℕ} (x y : {S : Finset (Fin m) // S.card = k}) : R :=
  (g1.val.submatrix (x.1.orderEmbOfFin x.2) (y.1.orderEmbOfFin y.2)).det

def qr_G (g1 : GL (Fin m) R) (K' I' : TIdx nu) (c : ℤ) : R := qr_mn g1 (qr_base K' c) (qr_base I' c)

lemma qr_G_low (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) :
    qr_G g1 K' I' c = g1.val.det := by
  have h1 : c ∉ TCols nu := by
    simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt]; exact Or.inl hc
  have := qr_subsing hn h1
  rw [qr_G, Subsingleton.elim (qr_base K' c) (qr_base I' c)]
  exact qr_det_full _ (qr_colH_low hn hc) _ _

lemma qr_G_high (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : nu 0 < c) :
    qr_G g1 K' I' c = 1 :=
  qr_det_empty _ (qr_colH_high hn hc) _ _

lemma qr_prod_G (hn : Dominant nu) (hi : Interl lam nu) (K' I' : TIdx nu) :
    ∏ c ∈ TCols lam, qr_G g1 K' I' c =
      g1.val.det ^ (nu (lastIdx m) - lam (Fin.last m)).toNat *
        ∏ c : ↥(TCols nu), (g1.val.submatrix ((K' c).1.orderEmbOfFin (K' c).2)
          ((I' c).1.orderEmbOfFin (I' c).2)).det := by
  have h1 := qr_lam_last_le hi
  have h2 : nu (lastIdx m) ≤ nu 0 := qr_le_last hn 0
  have h3 := qr_nu_zero_le hi
  rw [TCols, qr_lastIdx, ← Finset.Ioc_union_Ioc_eq_Ioc h1 (h2.trans h3),
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), ← Finset.Ioc_union_Ioc_eq_Ioc h2 h3,
    Finset.prod_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.prod_congr rfl (fun c hc => qr_G_low hn K' I' (Finset.mem_Ioc.1 hc).2), Finset.prod_const,
    Int.card_Ioc,
    Finset.prod_congr (s₁ := Finset.Ioc (nu 0) (lam 0)) rfl (fun c hc => qr_G_high hn K' I' (Finset.mem_Ioc.1 hc).1),
    Finset.prod_const_one, mul_one]
  congr 1
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun c _ => ?_
  have e1 := qr_base_mem K' c
  have e2 := qr_base_mem I' c
  rw [qr_G, e1, e2]
  rfl

lemma qr_card_C (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu) :
    (((TCols lam).filter fun c => colH lam c = colH nu c + 1).card : ℤ) =
      ∑ a, lam a - ∑ a, nu a - lam (Fin.last m) := by
  have h1 : ∀ c, ((if colH lam c = colH nu c + 1 then 1 else 0 : ℕ) : ℤ) = (colH lam c : ℤ) - colH nu c := by
    intro c
    have := qr_colH_eq hi c
    omega
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, h1]
  rw [Finset.sum_sub_distrib, TCols, qr_lastIdx,
    qr_sum_colH lam _ _ (fun a => ⟨hl (Fin.le_last a), qr_le_zero hl a⟩),
    qr_sum_colH nu _ _ (fun a => ⟨(qr_lam_last_le hi).trans (qr_le_last hn a),
      (qr_le_zero hn a).trans (qr_nu_zero_le hi)⟩)]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem qr_TMat_j (hb : IsBlock h g1 t) (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (K' I' : TIdx nu) :
    evGL h (TMat lam (qr_j hi K') (qr_j hi I')) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) * evGL g1 (TMat nu K' I') := by
  simp only [TMat, map_mul, map_prod, qc_evGL_detU_zpow, qc_evGL_minorC]
  have h1 : ∀ c : ↥(TCols lam),
      (h.val.submatrix ((qr_j hi K' c).1.orderEmbOfFin (qr_j hi K' c).2)
        ((qr_j hi I' c).1.orderEmbOfFin (qr_j hi I' c).2)).det =
      (if colH lam c = colH nu c + 1 then (t : R) else 1) * qr_G g1 K' I' c := fun c =>
    qr_minor_ext hb _ _ _ (qr_base K' c).2 (qr_base I' c).2 _ _
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_mul_distrib,
    Finset.prod_coe_sort (TCols lam) (fun c => if colH lam c = colH nu c + 1 then (t : R) else 1),
    Finset.prod_coe_sort (TCols lam) (fun c => qr_G g1 K' I' c), qr_prod_G hn hi, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const_one, mul_one, qr_dU_block hb, qr_lastIdx]
  have hC := qr_card_C hl hn hi
  set N := ((TCols lam).filter fun c => colH lam c = colH nu c + 1).card
  set P := (nu (lastIdx m) - lam (Fin.last m)).toNat with hP
  have hP' : (P : ℤ) = nu (lastIdx m) - lam (Fin.last m) :=
    Int.toNat_of_nonneg (sub_nonneg.2 (qr_lam_last_le hi))
  have e1 : t ^ (∑ a, lam a - ∑ a, nu a) = t ^ lam (Fin.last m) * t ^ N := by
    rw [← zpow_natCast, ← zpow_add, hC]; congr 1; ring
  have e2 : qc_dU g1 ^ nu (lastIdx m) = qc_dU g1 ^ lam (Fin.last m) * qc_dU g1 ^ P := by
    rw [← zpow_natCast, ← zpow_add, hP']; congr 1; ring
  rw [e1, e2, mul_zpow]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, qc_dU_coe]
  ring

end TM

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_prim {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
    (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (I0 : TIdx mu) (hI0 : StdT I0) (d : ℤ)
    (hd : ∀ i, d ∣ ph i I0) : d ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hd
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu I0 = d • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨I0, hI0⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (d : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩

lemma qr_equiv {m : ℕ} [NeZero m] {M : GLMod (m + 1)} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
    (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (ph : Matrix M.ι (TIdx lam) ℤ)
    (hE : (M.A * ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) : Matrix _ _ _) =
      (ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) * TMat lam : Matrix _ _ _))
    {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ} (hb : IsBlock h g1 t)
    (i : M.ι) (I' : TIdx nu) :
    ∑ k, evGL h (M.A i k) * ((ph k (qr_j hi I') : ℤ) : R) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) *
        ∑ K' : TIdx nu, ((ph i (qr_j hi K') : ℤ) : R) * evGL g1 (TMat nu K' I') := by
  have h1 := congrArg (evGL h) (congrFun (congrFun hE i) (qr_j hi I'))
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, eq_intCast, map_intCast] at h1
  rw [h1, Finset.mul_sum]
  symm
  apply Finset.sum_of_injOn (qr_j hi) (qr_j_inj hi).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro K _ hK
    rw [qr_TMat_zero hb hn hi K I' (fun K' hK' => hK ⟨K', Finset.mem_coe.2 (Finset.mem_univ _), hK'⟩), mul_zero]
  · intro K' _
    rw [qr_TMat_j hb hl hn hi]
    ring

theorem closure_third_part_of (hA : LemmaA) (hS : SBasis) (hC : CntBranch) : ClosureBranching := by
  classical
  intro m _ M lam β hl hβ
  let Sg : Finset (Fin m → ℤ) :=
    (Fintype.piFinset fun a : Fin m => Finset.Icc (lam a.succ) (lam a.castSucc)).filter fun nu =>
      Dominant nu ∧ Interl lam nu
  have hSg : ∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu := by
    intro nu
    simp only [Sg, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
    rintro ⟨_, hi⟩ a
    exact ⟨(hi a).2, (hi a).1⟩
  have hex : ∀ I : TIdx lam, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk lam I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx lam) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk lam I := hc
  have hE := qc_equiv hA hS hl hβ ph hph
  refine ⟨Sg, fun nu i I' => ph i (qr_j ((hSg nu.1).1 nu.2).2 I'), hSg, ?_, ?_, ?_⟩
  · intro nu R _ h g1 t hb
    ext i I'
    exact qr_equiv hl ((hSg nu.1).1 nu.2).1 ((hSg nu.1).1 nu.2).2 ph hE hb i I'
  · intro nu
    have hpr := qr_prim hS hl hβ ph hph _ (qr_j_can_std (lam := lam) ((hSg nu.1).1 nu.2).2)
    constructor
    · intro p hp h0
      have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
      have h2 : p ∣ 1 := by exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · intro h0
      have h1 := hpr 0 fun i => by
        have := congrFun h0 i
        simp only [Pi.zero_apply, Int.cast_eq_zero] at this
        rw [this]
      simp at h1
  · rw [qc_card_eq hS hl hβ, hC m lam hl Sg hSg, Finset.sum_coe_sort Sg (fun nu => dMu nu)]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
