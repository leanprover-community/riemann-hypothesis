import Formalism.SatakeDualWeyl.StatementE
import Mathlib

section
namespace Formalism.UG.P

open Finset

def satakeInv {α : Type} [LinearOrder α] (s S : Finset α) : ℕ :=
  ∑ a ∈ S, ((s \ S).filter (fun l => a < l)).card

theorem satakeInv_insert_not_mem {α : Type} [LinearOrder α] (s' S : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hS : S ⊆ s') :
    satakeInv (insert m s') S = satakeInv s' S + S.card := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmS : m ∉ S := fun h => hmS' (hS h)
  unfold satakeInv
  rw [card_eq_sum_ones S, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have e : (insert m s' \ S).filter (fun l => a < l)
      = insert m ((s' \ S).filter (fun l => a < l)) := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS, hm a (hS ha)]
    · simp [hx]
  rw [e, card_insert_of_notMem (by simp [hmS'])]

theorem satakeInv_insert_mem {α : Type} [LinearOrder α] (s' T : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hT : T ⊆ s') :
    satakeInv (insert m s') (insert m T) = satakeInv s' T := by
  have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
  have hmT : m ∉ T := fun h => hmS' (hT h)
  unfold satakeInv
  rw [sum_insert hmT]
  have e : insert m s' \ insert m T = s' \ T := by
    ext x
    by_cases hx : x = m
    · simp [hx, hmS']
    · simp [hx]
  rw [e]
  have h0 : ((s' \ T).filter (fun l => m < l)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx
    exact not_lt.2 (le_of_lt (hm x (mem_sdiff.1 hx).1))
  rw [h0, zero_add]

theorem satake_qbinom (q : ℤ) {α : Type} [LinearOrder α] (s : Finset α) :
    ∀ j : ℕ, (∑ S ∈ s.powersetCard j, q ^ satakeInv s S) * ∏ i ∈ range j, (q ^ (i + 1) - 1) =
      ∏ i ∈ range j, (q ^ (s.card - i) - 1) := by
  induction s using Finset.induction_on_max
  next =>
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have h1 : powersetCard (k + 1) (∅ : Finset α) = ∅ := powersetCard_eq_empty.2 (by simp)
      rw [h1, sum_empty, zero_mul, prod_range_succ']
      simp
  next m s' hm ih =>
    have hmS' : m ∉ s' := fun h => lt_irrefl m (hm m h)
    intro j
    cases j with
    | zero => simp [satakeInv]
    | succ k =>
      have hdisj : Disjoint (powersetCard (k + 1) s') ((powersetCard k s').image (insert m)) := by
        rw [disjoint_left]
        intro S hS hS'
        obtain ⟨T, -, rfl⟩ := mem_image.1 hS'
        exact hmS' ((mem_powersetCard.1 hS).1 (mem_insert_self m T))
      have hinj : Set.InjOn (insert m) (powersetCard k s' : Set (Finset α)) := by
        intro T1 h1 T2 h2 h
        have h1' : m ∉ T1 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h1)).1 h')
        have h2' : m ∉ T2 := fun h' => hmS' ((mem_powersetCard.1 (mem_coe.1 h2)).1 h')
        calc T1 = (insert m T1).erase m := (erase_insert h1').symm
          _ = (insert m T2).erase m := by rw [h]
          _ = T2 := erase_insert h2'
      rw [powersetCard_succ_insert hmS', sum_union hdisj, sum_image hinj]
      have e1 : ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv (insert m s') S
          = q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S hS
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 hS
        rw [satakeInv_insert_not_mem s' S m hm hsub, hcard, pow_add]
        ring
      have e2 : ∑ T ∈ powersetCard k s', q ^ satakeInv (insert m s') (insert m T)
          = ∑ T ∈ powersetCard k s', q ^ satakeInv s' T :=
        sum_congr rfl (fun T hT => by
          rw [satakeInv_insert_mem s' T m hm (mem_powersetCard.1 hT).1])
      rw [e1, e2]
      have hP : ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
          = (∏ i ∈ range k, (q ^ (i + 1) - 1)) * (q ^ (k + 1) - 1) := prod_range_succ _ _
      have hR : ∏ i ∈ range (k + 1), (q ^ (s'.card + 1 - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card + 1) - 1) := by
        rw [prod_range_succ']
        simp only [Nat.add_sub_add_right, Nat.sub_zero]
      have hRk : ∏ i ∈ range (k + 1), (q ^ (s'.card - i) - 1)
          = (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * (q ^ (s'.card - k) - 1) :=
        prod_range_succ _ _
      have hsplit :
          (q ^ (k + 1) * ∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S
              + ∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1)
            = q ^ (k + 1) * ((∑ S ∈ powersetCard (k + 1) s', q ^ satakeInv s' S)
                * ∏ i ∈ range (k + 1), (q ^ (i + 1) - 1))
              + ((∑ T ∈ powersetCard k s', q ^ satakeInv s' T) * ∏ i ∈ range k, (q ^ (i + 1) - 1))
                * (q ^ (k + 1) - 1) := by
        rw [hP]; ring
      rw [card_insert_of_notMem hmS', hR, hsplit, ih (k + 1), ih k, hRk]
      by_cases hk : k ≤ s'.card
      · have hpow : q ^ (k + 1) * q ^ (s'.card - k) = q ^ (s'.card + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (∏ i ∈ range k, (q ^ (s'.card - i) - 1)) * hpow
      · have hz : ∏ i ∈ range k, (q ^ (s'.card - i) - 1) = 0 :=
          prod_eq_zero (i := s'.card) (mem_range.2 (by omega)) (by simp)
        rw [hz]; ring

private theorem satakeInv_insert_max_add_card {α : Type} [LinearOrder α] (s S : Finset α) (m : α)
    (hm : ∀ x ∈ S, x < m) (hms : m ∈ s) :
    satakeInv s (insert m S) + S.card = satakeInv s S + (s.filter (fun l => m < l)).card := by
  have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
  unfold satakeInv
  rw [sum_insert hmS]
  have h1 : (s \ insert m S).filter (fun l => m < l) = s.filter (fun l => m < l) := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨⟨hx, -⟩, h⟩
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, ?_⟩, h⟩
      rintro (rfl | hxS)
      · exact lt_irrefl _ h
      · exact lt_asymm h (hm x hxS)
  have h2 : ∀ a ∈ S, ((s \ S).filter (fun l => a < l)).card
      = ((s \ insert m S).filter (fun l => a < l)).card + 1 := by
    intro a ha
    have e : (s \ S).filter (fun l => a < l)
        = insert m ((s \ insert m S).filter (fun l => a < l)) := by
      ext x
      by_cases hx : x = m
      · simp [hx, hms, hmS, hm a ha]
      · simp [hx]
    rw [e, card_insert_of_notMem (by simp)]
  rw [h1, sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  ring

theorem satakeInv_two_mul {n : ℕ} (S : Finset (Fin n)) :
    2 * (satakeInv univ S : ℤ) =
      ∑ a ∈ S, ((n : ℤ) - 1 - 2 * (a : ℕ)) + (S.card : ℤ) * ((n : ℤ) - S.card) := by
  induction S using Finset.induction_on_max
  next => simp [satakeInv]
  next m S' hm ih =>
    have hmS' : m ∉ S' := fun h => lt_irrefl m (hm m h)
    have L := satakeInv_insert_max_add_card (univ : Finset (Fin n)) S' m hm (mem_univ m)
    have hc : ((univ : Finset (Fin n)).filter (fun l => m < l)).card = n - 1 - (m : ℕ) := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    rw [hc] at L
    have hlt : (m : ℕ) < n := m.isLt
    have hsub : (((n - 1 - (m : ℕ) : ℕ)) : ℤ) = (n : ℤ) - 1 - (m : ℕ) := by omega
    have L' := congrArg (fun x : ℕ => (x : ℤ)) L
    simp only [Nat.cast_add] at L'
    rw [hsub] at L'
    rw [sum_insert hmS', card_insert_of_notMem hmS']
    push_cast
    linear_combination 2 * L' + ih

end Formalism.UG.P
end

section
noncomputable section

open Matrix

namespace Formalism.UG.P

open Formalism.UG

variable {L : Type} [Field L] (O : Subring L) {n : ℕ}

abbrev satakePairs (S : Finset (Fin n)) : Type := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2}

theorem satakePairs_card (S : Finset (Fin n)) :
    Fintype.card (satakePairs S) = satakeInv Finset.univ S := by
  unfold satakeInv
  rw [Fintype.card_subtype, Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S) ?_]
  · refine Finset.sum_congr rfl fun a ha => ?_
    refine Eq.trans ?_ (Finset.card_image_of_injective (f := Prod.mk a) _ (fun x y h => congrArg Prod.snd h))
    congr 1
    ext ⟨b, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hb, hl, hbl⟩, rfl⟩
      exact ⟨l, ⟨hl, hbl⟩, rfl, rfl⟩
    · rintro ⟨l', ⟨hl', hal'⟩, rfl, rfl⟩
      exact ⟨⟨ha, hl', hal'⟩, rfl⟩
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact Finset.mem_coe.2 hp.2.1

def satakeN (S : Finset (Fin n)) (c : satakePairs S → O) : Matrix (Fin n) (Fin n) L :=
  fun a l => if h : a ∈ S ∧ l ∉ S ∧ a < l then ((c ⟨(a, l), h⟩ : O) : L) else 0

def satakeD (π : L) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.diagonal (fun a => if a ∈ S then π else 1)

private lemma satakeN_apply (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    satakeN O S c a l = if h : a ∈ S ∧ l ∉ S ∧ a < l then ((c ⟨(a, l), h⟩ : O) : L) else 0 := rfl

theorem satakeN_mem (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    satakeN O S c a l ∈ O := by
  rw [satakeN_apply]
  split_ifs with h
  · exact (c ⟨(a, l), h⟩).2
  · exact O.zero_mem

theorem satakeN_mul_self (S : Finset (Fin n)) (c c' : satakePairs S → O) :
    satakeN O S c * satakeN O S c' = 0 := by
  ext a l
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b ∈ S
  · rw [satakeN_apply O S c a b, dif_neg (fun h => h.2.1 hb), zero_mul]
  · rw [satakeN_apply O S c' b l, dif_neg (fun h => hb h.1), mul_zero]

theorem satakeN_mul_diag (S S' : Finset (Fin n)) (c : satakePairs S → O) (c' : satakePairs S' → O)
    (a : Fin n) : (satakeN O S c * satakeN O S' c') a a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a < b
  · rw [satakeN_apply O S' c' b a, dif_neg (fun h => absurd h.2.2 (lt_asymm hab)), mul_zero]
  · rw [satakeN_apply O S c a b, dif_neg (fun h => hab h.2.2), zero_mul]

theorem satakeN_diag (S : Finset (Fin n)) (c : satakePairs S → O) (a : Fin n) :
    satakeN O S c a a = 0 := by
  rw [satakeN_apply, dif_neg (fun h => lt_irrefl a h.2.2)]

theorem satakeN_lower (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) (h : l < a) :
    satakeN O S c a l = 0 := by
  rw [satakeN_apply, dif_neg (fun h' => absurd h'.2.2 (lt_asymm h))]

variable {O}

theorem satakeD_mul_inv {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) :
    satakeD π S * satakeD π⁻¹ S = 1 := by
  simp only [satakeD, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp [hπ]

theorem satakeD_inv_mul {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) :
    satakeD π⁻¹ S * satakeD π S = 1 := by
  simp only [satakeD, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp [hπ]

variable (O)

def satakeGL {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) : GL (Fin n) L where
  val := (1 + satakeN O S c) * satakeD π S
  inv := satakeD π⁻¹ S * (1 - satakeN O S c)
  val_inv := by
    have h : (1 + satakeN O S c) * (1 - satakeN O S c) = 1 := by
      rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, satakeN_mul_self, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]; abel
    rw [show (1 + satakeN O S c) * satakeD π S * (satakeD π⁻¹ S * (1 - satakeN O S c)) =
      (1 + satakeN O S c) * (satakeD π S * satakeD π⁻¹ S) * (1 - satakeN O S c) by
        simp only [Matrix.mul_assoc], satakeD_mul_inv hπ, Matrix.mul_one, h]
  inv_val := by
    have h : (1 - satakeN O S c) * (1 + satakeN O S c) = 1 := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, satakeN_mul_self, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]; abel
    rw [show satakeD π⁻¹ S * (1 - satakeN O S c) * ((1 + satakeN O S c) * satakeD π S) =
      satakeD π⁻¹ S * ((1 - satakeN O S c) * (1 + satakeN O S c)) * satakeD π S by
        simp only [Matrix.mul_assoc], h, Matrix.mul_one, satakeD_inv_mul hπ]

theorem satakeGL_apply {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l =
      ((1 : Matrix (Fin n) (Fin n) L) a l + satakeN O S c a l) * (if l ∈ S then π else 1) := by
  show ((1 + satakeN O S c) * satakeD π S) a l = _
  rw [satakeD, Matrix.mul_diagonal, Matrix.add_apply]

theorem satakeGL_lower {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n)
    (h : l < a) : ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l = 0 := by
  rw [satakeGL_apply, Matrix.one_apply_ne h.ne', satakeN_lower O S c a l h, add_zero, zero_mul]

theorem satakeGL_diag {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a : Fin n) :
    ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a = if a ∈ S then π else 1 := by
  rw [satakeGL_apply, Matrix.one_apply_eq, satakeN_diag, add_zero, one_mul]

theorem satake_mem_glint (g : GL (Fin n) L)
    (h1 : ∀ a b, (g : Matrix (Fin n) (Fin n) L) a b ∈ O)
    (h2 : ∀ a b, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) :
    g ∈ GLint (Fin n) O := by
  let φ : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L := O.subtype.mapMatrix
  have hφ : Function.Injective φ := fun x y h =>
    Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  let M : Matrix (Fin n) (Fin n) O := fun a b => ⟨(g : Matrix (Fin n) (Fin n) L) a b, h1 a b⟩
  let M' : Matrix (Fin n) (Fin n) O :=
    fun a b => ⟨((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b, h2 a b⟩
  have hM : φ M = (g : Matrix (Fin n) (Fin n) L) := rfl
  have hM' : φ M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
  have e1 : M * M' = 1 :=
    hφ (by rw [map_mul, map_one, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have e2 : M' * M = 1 :=
    hφ (by rw [map_mul, map_one, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one])
  unfold Formalism.UG.GLint
  exact MonoidHom.mem_range.2 ⟨⟨M, M', e1, e2⟩, Units.ext rfl⟩

theorem satake_glint_entry {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) (a b : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) a b ∈ O := by
  unfold Formalism.UG.GLint at hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hg
  exact ((x : Matrix (Fin n) (Fin n) O) a b).2

def satakeU (S : Finset (Fin n)) (c : satakePairs S → O) : GL (Fin n) L where
  val := 1 + satakeN O S c
  inv := 1 - satakeN O S c
  val_inv := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, satakeN_mul_self, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]; abel
  inv_val := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, satakeN_mul_self, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]; abel

theorem satakeU_mem (S : Finset (Fin n)) (c : satakePairs S → O) : satakeU O S c ∈ GLint (Fin n) O := by
  refine satake_mem_glint O _ (fun a b => ?_) (fun a b => ?_)
  · show (1 + satakeN O S c) a b ∈ O
    rw [Matrix.add_apply, Matrix.one_apply]
    exact O.add_mem (by split_ifs; exacts [O.one_mem, O.zero_mem]) (satakeN_mem O S c a b)
  · show (1 - satakeN O S c) a b ∈ O
    rw [Matrix.sub_apply, Matrix.one_apply]
    exact O.sub_mem (by split_ifs; exacts [O.one_mem, O.zero_mem]) (satakeN_mem O S c a b)

def satakeP (σ : Equiv.Perm (Fin n)) : GL (Fin n) L where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

theorem permMatrix_mem_integralGL (σ : Equiv.Perm (Fin n)) : satakeP (L := L) σ ∈ GLint (Fin n) O := by
  refine satake_mem_glint O _ (fun a b => ?_) (fun a b => ?_)
  · show σ.toPEquiv.toMatrix a b ∈ O
    rw [PEquiv.toMatrix_apply]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
  · show σ.symm.toPEquiv.toMatrix a b ∈ O
    rw [PEquiv.toMatrix_apply]
    split_ifs
    exacts [O.one_mem, O.zero_mem]

theorem satake_exists_perm (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, a ∈ S ↔ ((σ a : Fin n) : ℕ) < S.card := by
  have hk : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  let e : {a // a ∈ S} ≃ {i : Fin n // (i : ℕ) < S.card} := S.equivFin.trans (Fin.castLEquiv hk)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  by_cases ha : a ∈ S
  · exact iff_of_true ha (e.extendSubtype_mem a ha)
  · exact iff_of_false ha (e.extendSubtype_not_mem a ha)

theorem satakeGL_mem_doset {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) :
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * diagJ n π S.card * (b : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨σ, hσ⟩ := satake_exists_perm S
  refine ⟨satakeU O S c * satakeP σ, mul_mem (satakeU_mem O S c) (permMatrix_mem_integralGL O σ),
    satakeP σ.symm, permMatrix_mem_integralGL O σ.symm, ?_⟩
  show (1 + satakeN O S c) * satakeD π S =
    (1 + satakeN O S c) * σ.toPEquiv.toMatrix * diagJ n π S.card * σ.symm.toPEquiv.toMatrix
  rw [Matrix.mul_assoc (1 + satakeN O S c), Matrix.mul_assoc (1 + satakeN O S c)]
  congr 1
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
  ext a b
  simp only [Matrix.submatrix_apply, id_eq, satakeD, diagJ, Matrix.diagonal_apply, σ.injective.eq_iff, hσ]

theorem satakeGL_inv_mul_apply {π : L} (hπ : π ≠ 0) (S S' : Finset (Fin n)) (c : satakePairs S → O)
    (c' : satakePairs S' → O) (a l : Fin n) :
    (((satakeGL O hπ S c)⁻¹ * satakeGL O hπ S' c' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l =
      (if a ∈ S then π⁻¹ else 1) * ((1 - satakeN O S c) * (1 + satakeN O S' c')) a l *
        (if l ∈ S' then π else 1) := by
  show (satakeD π⁻¹ S * (1 - satakeN O S c) * ((1 + satakeN O S' c') * satakeD π S')) a l = _
  rw [← Matrix.mul_assoc, satakeD, satakeD, Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.diagonal_mul]

private lemma one_sub_satakeN_mul_one_add_satakeN_diag (S S' : Finset (Fin n)) (c : satakePairs S → O)
    (c' : satakePairs S' → O) (a : Fin n) :
    ((1 - satakeN O S c) * (1 + satakeN O S' c')) a a = 1 := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
    Matrix.add_apply, Matrix.one_apply_eq, satakeN_diag, satakeN_mul_diag, add_zero, sub_zero]

theorem satake_subset_of_mem {π : L} (hπ : π ≠ 0) (hπO : π⁻¹ ∉ O) (S S' : Finset (Fin n))
    (c : satakePairs S → O) (c' : satakePairs S' → O)
    (h : (satakeGL O hπ S c)⁻¹ * satakeGL O hπ S' c' ∈ GLint (Fin n) O) : S ⊆ S' := by
  intro a ha
  by_contra ha'
  have h1 := satake_glint_entry O h a a
  rw [satakeGL_inv_mul_apply, one_sub_satakeN_mul_one_add_satakeN_diag, if_pos ha, if_neg ha', mul_one, mul_one] at h1
  exact hπO h1

theorem satake_entry_of_mem {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c c' : satakePairs S → O)
    (h : (satakeGL O hπ S c)⁻¹ * satakeGL O hπ S c' ∈ GLint (Fin n) O) (p : satakePairs S) :
    π⁻¹ * (((c' p : O) : L) - ((c p : O) : L)) ∈ O := by
  obtain ⟨⟨a, l⟩, ha, hl, hal⟩ := p
  have h1 := satake_glint_entry O h a l
  rw [satakeGL_inv_mul_apply, if_pos ha, if_neg hl, mul_one, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_add, satakeN_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hal.ne, satakeN_apply O S c' a l,
    satakeN_apply O S c a l, dif_pos ⟨ha, hl, hal⟩, dif_pos ⟨ha, hl, hal⟩, zero_add] at h1
  exact h1

abbrev satakeRes (π : O) : Type := O ⧸ Ideal.span {π}

def satakeSec (π : O) (r : satakeRes O π) : O :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {π})) r

theorem satakeSec_mk (π : O) (r : satakeRes O π) : Ideal.Quotient.mk _ (satakeSec O π r) = r :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {π})) r

def satakeRep (π : O) (hπ : (π : L) ≠ 0) (j : ℕ)
    (i : Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes O π) : GL (Fin n) L :=
  satakeGL O hπ i.1.1 (fun p => satakeSec O π (i.2 p))

theorem satakeRep_inj (π : O) (hπ : (π : L) ≠ 0) (hπO : (π : L)⁻¹ ∉ O) (j : ℕ)
    (i i' : Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes O π)
    (h : (satakeRep O π hπ j i)⁻¹ * satakeRep O π hπ j i' ∈ GLint (Fin n) O) : i = i' := by
  obtain ⟨⟨S, hS⟩, r⟩ := i
  obtain ⟨⟨S', hS'⟩, r'⟩ := i'
  have hsub : S ⊆ S' := satake_subset_of_mem O hπ hπO S S' (fun p => satakeSec O π (r p))
    (fun p => satakeSec O π (r' p)) h
  have hSS : S = S' := Finset.eq_of_subset_of_card_le hsub (hS'.trans hS.symm).le
  subst hSS
  have hr : r = r' := by
    funext p
    have h2 : (π : L)⁻¹ * (((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L)) ∈ O :=
      satake_entry_of_mem O hπ S (fun p => satakeSec O π (r p)) (fun p => satakeSec O π (r' p)) h p
    have hmem : satakeSec O π (r' p) - satakeSec O π (r p) ∈ Ideal.span {π} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      apply Subtype.ext
      show ((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L) =
        (π : L) * ((π : L)⁻¹ * (((satakeSec O π (r' p) : O) : L) - ((satakeSec O π (r p) : O) : L)))
      rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact (satakeSec_mk O π (r p)).symm.trans
      ((Ideal.Quotient.eq.2 hmem).symm.trans (satakeSec_mk O π (r' p)))
  subst hr
  rfl

end Formalism.UG.P
end
end
