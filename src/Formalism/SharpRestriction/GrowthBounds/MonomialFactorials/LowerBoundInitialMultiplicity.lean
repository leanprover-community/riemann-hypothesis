import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RatioConditionOfSegFacts

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Comb

variable {s t : ℕ} (u : Fin t → Fin s)

open Classical in

def ovr (a : Fin s → ℕ) (n : Fin t → ℕ) : Fin s → ℕ :=
  fun l => if h : ∃ i, u i = l then n (Classical.choose h) else a l

theorem ovr_u (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) : ovr u a n (u i) = n i := by
  unfold ovr
  have h : ∃ i', u i' = u i := ⟨i, rfl⟩
  rw [dif_pos h]
  exact congrArg n (hu (Classical.choose_spec h))

theorem ovr_not (a : Fin s → ℕ) (n : Fin t → ℕ) (l : Fin s) (h : ¬ ∃ i, u i = l) : ovr u a n l = a l := dif_neg h

theorem ovr_ovr (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) :
    ovr u (ovr u a n) (fun i => a (u i)) = a := by
  funext l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    exact ovr_u u hu _ _ i
  · rw [ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem ovr_mem (hu : Function.Injective u) (W : Fin s → Finset ℕ) (a : Fin s → ℕ) (n : Fin t → ℕ)
    (ha : a ∈ Fintype.piFinset W) (hn : n ∈ Fintype.piFinset (fun i => W (u i))) :
    ovr u a n ∈ Fintype.piFinset W := by
  rw [Fintype.mem_piFinset] at ha hn ⊢
  intro l
  by_cases h : ∃ i, u i = l
  · obtain ⟨i, rfl⟩ := h
    rw [ovr_u u hu]
    exact hn i
  · rw [ovr_not u _ _ _ h]
    exact ha l

theorem ovr_update (hu : Function.Injective u) (a : Fin s → ℕ) (n : Fin t → ℕ) (i : Fin t) (v : ℕ) :
    Function.update (ovr u a n) (u i) v = ovr u a (Function.update n i v) := by
  funext l
  by_cases h : ∃ j, u j = l
  · obtain ⟨j, rfl⟩ := h
    by_cases hj : j = i
    · subst hj
      simp [ovr_u u hu]
    · rw [Function.update_of_ne (hu.ne hj), ovr_u u hu, ovr_u u hu, Function.update_of_ne hj]
  · have hl : l ≠ u i := fun e => h ⟨i, e.symm⟩
    rw [Function.update_of_ne hl, ovr_not u _ _ l h, ovr_not u _ _ l h]

theorem sum_ovr (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ) :
    ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, F a := by
  calc ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n)
      = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F (ovr u q.1 q.2) := by
        rw [Finset.sum_product]
    _ = ∑ q ∈ Fintype.piFinset W ×ˢ Fintype.piFinset (fun i => W (u i)), F q.1 := by
        refine Finset.sum_nbij' (fun q => (ovr u q.1 q.2, fun i => q.1 (u i)))
          (fun q => (ovr u q.1 q.2, fun i => q.1 (u i))) ?_ ?_ ?_ ?_ ?_
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ hq
          rw [Finset.mem_product] at hq ⊢
          refine ⟨ovr_mem u hu W a n hq.1 hq.2, ?_⟩
          have ha := hq.1
          rw [Fintype.mem_piFinset] at ha ⊢
          exact fun i => ha (u i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          exact Prod.ext (ovr_ovr u hu a n) (funext fun i => ovr_u u hu a n i)
        · rintro ⟨a, n⟩ _
          rfl
    _ = _ := by
        rw [Finset.sum_product, Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]

theorem box_of_fibres (hu : Function.Injective u) (W : Fin s → Finset ℕ) (F : (Fin s → ℕ) → ℝ)
    (G : Fin t → (Fin s → ℕ) → ℝ) (ε : ℝ) (hne : (Fintype.piFinset W).Nonempty)
    (h : ∀ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), F (ovr u a n) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n)) :
    ∑ a ∈ Fintype.piFinset W, F a ≤ ε * ∑ i, ∑ a ∈ Fintype.piFinset W, G i a := by
  obtain ⟨a0, ha0⟩ := hne
  have hmem : (fun i => a0 (u i)) ∈ Fintype.piFinset (fun i => W (u i)) := by
    rw [Fintype.mem_piFinset] at ha0 ⊢
    exact fun i => ha0 (u i)
  have hpos : (0 : ℝ) < ((Fintype.piFinset (fun i => W (u i))).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨_, hmem⟩)
  have hG : ∀ i, ∑ a ∈ Fintype.piFinset W, ∑ n ∈ Fintype.piFinset (fun i => W (u i)), G i (ovr u a n) =
      ((Fintype.piFinset (fun i => W (u i))).card : ℝ) * ∑ a ∈ Fintype.piFinset W, G i a :=
    fun i => sum_ovr u hu W (G i)
  have hsum := Finset.sum_le_sum h
  rw [sum_ovr u hu W F, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun i _ => hG i,
    ← Finset.mul_sum, mul_left_comm] at hsum
  exact le_of_mul_le_mul_left hsum hpos

theorem interval_eq (A : Finset ℕ) (hne : A.Nonempty) (hc : ∀ x ∈ A, ∀ y ∈ A, ∀ z, x ≤ z → z ≤ y → z ∈ A) :
    A = (Finset.range (A.sup id - sInf (A : Set ℕ) + 1)).image (fun k => sInf (A : Set ℕ) + 1 * k) := by
  have hmA : sInf (A : Set ℕ) ∈ A := Finset.mem_coe.1 (Nat.sInf_mem (Finset.coe_nonempty.2 hne))
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup A hne id
  have hle : ∀ x ∈ A, sInf (A : Set ℕ) ≤ x := fun x hx => Nat.sInf_le (Finset.mem_coe.2 hx)
  have hge : ∀ x ∈ A, x ≤ A.sup id := fun x hx => show x ≤ A.sup id from Finset.le_sup (f := id) hx
  ext x
  simp only [Finset.mem_image, Finset.mem_range, one_mul]
  constructor
  · intro hx
    have h1 := hle x hx
    have h2 := hge x hx
    exact ⟨x - sInf (A : Set ℕ), by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    refine hc _ hmA M hM _ (Nat.le_add_right _ _) ?_
    have h3 : A.sup id = M := hMe
    have h4 := hle M hM
    omega

end Comb

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Letters

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem letters_ext {N : ℕ} (L L' : Formalism.GM.M.Letters N) (h1 : L.vec = L'.vec) (h2 : L.deg = L'.deg) : L = L' := by
  cases L; cases L'; simp_all

theorem uTop_inj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [uTop] at h'
  exact Fin.ext (by omega)

abbrev lLL (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : Formalism.GM.M.Letters (2 * X.s + 1) :=
  (gB C0 CE1 CE2 X aTop 0 b).lettersAt x.1 x.2

abbrev gT (b : SegBlock X.s X.r) : Formalism.GM.M.TieData := (gB C0 CE1 CE2 X (fun _ => 0) 0 b).T

theorem deg_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) - x.1 i := by
  have hi := i.2
  simp only [SegData.t] at hi
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt, gB, gmB, gmL, gmT, blockData, BlockData.withMargin, blockBase, segChain, segTies]
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have hodd : ¬ (q : ℕ) % 2 = 0 := by omega
  have htop : topOf q h1 = uTop (X.S C0 CE1 CE2) i := Fin.ext (by simp only [topOf, uTop]; omega)
  have hnl : ¬ ((uTop (X.S C0 CE1 CE2) i : ℕ) < (X.S C0 CE1 CE2).sigma) := by simp only [uTop]; omega
  have hu : ¬ q = ⟨2 * X.s, by omega⟩ := by
    intro h
    exact h1 (by rw [h])
  rw [dif_neg h1, if_neg hodd, htop, if_neg hnl]
  simp only [hu, if_false, Nat.sub_zero]
  congr 1
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    apply if_neg
    show ¬ ((q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) ∨ (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) + 1)
    omega
  · intro h
    exact absurd (Finset.mem_univ i) h
  · exact if_pos (Or.inr (show (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 from hq))

theorem deg_other (aTop aTop' : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X)
    (hag : ∀ l : Fin X.s, (l : ℕ) < (X.S C0 CE1 CE2).sigma → aTop l = aTop' l)
    (q : Fin (2 * X.s + 1)) (hq : ¬ ∃ i : Fin (X.S C0 CE1 CE2).t, 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 = (q : ℕ)) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = (lLL C0 CE1 CE2 X aTop' b x).deg q := by
  have hLL : (gB C0 CE1 CE2 X aTop 0 b).LL.deg q = (gB C0 CE1 CE2 X aTop' 0 b).LL.deg q := by
    simp only [gB, gmB, gmL, blockData, BlockData.withMargin, blockBase, segChain]
    by_cases h : (q : ℕ) = 2 * X.s
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      have hv : ((topOf q h : Fin X.s) : ℕ) = (q : ℕ) / 2 := rfl
      have hlt : (q : ℕ) / 2 < X.s := by
        have := (topOf q h).2
        omega
      split_ifs with h2 h3 h3
      · rfl
      · rfl
      · simp only [coarseC]
        rw [hag _ h3]
      · exfalso
        apply hq
        refine ⟨⟨(q : ℕ) / 2 - (X.S C0 CE1 CE2).sigma, ?_⟩, ?_⟩
        · simp only [SegData.t]
          omega
        · simp only
          omega
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt]
  rw [hLL]
  rfl

theorem lLL_ovr (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    lLL C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x =
      (lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b)
        (fun i : Fin (X.S C0 CE1 CE2).t =>
          (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
  apply letters_ext
  · rfl
  · funext q
    simp only [Formalism.GM.M.Letters.setTies]
    split_ifs with h
    · have hc := Classical.choose_spec h
      have hp : (gT C0 CE1 CE2 X b).pos (Classical.choose h) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) := rfl
      have hjq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) + 1 := by
        omega
      rw [deg_eta C0 CE1 CE2 X _ b x _ q hjq]
      have he : ∃ i, uTop (X.S C0 CE1 CE2) i = uTop (X.S C0 CE1 CE2) (Classical.choose h) := ⟨_, rfl⟩
      have hov : ovr (uTop (X.S C0 CE1 CE2)) a n (uTop (X.S C0 CE1 CE2) (Classical.choose h)) = n (Classical.choose h) := by
        simp only [ovr, dif_pos he]
        rw [uTop_inj C0 CE1 CE2 X (Classical.choose_spec he)]
      simp only [coarseC, hov]
      rfl
    · rw [deg_other C0 CE1 CE2 X _ a b x ?_ q ?_]
      · intro l hl
        have hne : ¬ ∃ i, uTop (X.S C0 CE1 CE2) i = l := by
          rintro ⟨i, rfl⟩
          simp only [uTop] at hl
          omega
        simp only [ovr, dif_neg hne]
      · rintro ⟨i, hi⟩
        exact h ⟨i, hi⟩

end Letters

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Fibre

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

open Classical in

def Wl (dl : DCl X) (l : Fin X.s) : Finset ℕ :=
  X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c

theorem topA_eq (dl : DCl X) (l : Fin X.s) : topA C0 CE1 CE2 X dl l = (Wl C0 CE1 CE2 X dl l).sup id := rfl

private theorem mem_Wl_iff_mem_winA_and_dvd_sub (dl : DCl X) (l : Fin X.s) (v : ℕ) :
    v ∈ Wl C0 CE1 CE2 X dl l ↔
      v ∈ X.winA ∧ (∑ c, dl.2 l c ≤ v ∧ (X.S C0 CE1 CE2).P X.p l ∣ v - ∑ c, dl.2 l c) := by
  unfold Wl
  rw [Finset.mem_filter]

private theorem mem_cbox_iff_mem_piFinset_and_compat (dl : DCl X) (a : Fin X.s → ℕ) :
    a ∈ cbox C0 CE1 CE2 X dl ↔ a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl a := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem cbox_eq (dl : DCl X) (a0 : Fin X.s → ℕ) (h0 : a0 ∈ cbox C0 CE1 CE2 X dl) :
    cbox C0 CE1 CE2 X dl = Fintype.piFinset (Wl C0 CE1 CE2 X dl) := by
  have h0' := ((mem_cbox_iff_mem_piFinset_and_compat C0 CE1 CE2 X dl a0).1 h0).2
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock] at h0'
  ext a
  rw [mem_cbox_iff_mem_piFinset_and_compat, Fintype.mem_piFinset, Fintype.mem_piFinset]
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock, mem_Wl_iff_mem_winA_and_dvd_sub]
  constructor
  · rintro ⟨ha, -, -, h3⟩ i
    exact ⟨ha i, h3 i⟩
  · intro h
    exact ⟨fun i => (h i).1, h0'.1, h0'.2.1, fun i => (h i).2⟩

def cm (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) (v : ℕ) : ℕ :=
  (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i

def Nl (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) : Finset ℕ :=
  (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).image (cm C0 CE1 CE2 X dl x i)

theorem twoPow_pos (l : Fin X.s) : 0 < (X.S C0 CE1 CE2).P X.p l := by
  unfold SegData.P
  exact pow_pos X.std.1.prime.pos _

def LvlRoom (dl : DCl X) (x : Lv C0 CE1 CE2 X) : Prop :=
  ∀ i, ∀ v ∈ Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i),
    x.1 i ≤ (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)

variable {C0 CE1 CE2 X}

theorem cm_inj {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    Set.InjOn (cm C0 CE1 CE2 X dl x i) (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  intro v hv v' hv' he
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [Finset.mem_coe, mem_Wl_iff_mem_winA_and_dvd_sub] at hv hv'
  simp only [cm] at he
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at he
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at he
  have hkk : k = k' := by omega
  subst hkk
  omega

theorem cm_mono (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) {v v' : ℕ} (h : v ≤ v') :
    cm C0 CE1 CE2 X dl x i v ≤ cm C0 CE1 CE2 X dl x i v' := by
  unfold cm
  exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) _

theorem Nl_conv {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    ∀ y ∈ Nl C0 CE1 CE2 X dl x i, ∀ y' ∈ Nl C0 CE1 CE2 X dl x i, ∀ z, y ≤ z → z ≤ y' → z ∈ Nl C0 CE1 CE2 X dl x i := by
  intro y hy y' hy' z hyz hzy'
  simp only [Nl, Finset.mem_image] at hy hy' ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [mem_Wl_iff_mem_winA_and_dvd_sub, Formalism.MainNotions.flipOneThree.Inst.winA, Finset.mem_Icc] at hv hv' ⊢
  simp only [cm] at hyz hzy' ⊢
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at hyz
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at hzy'
  have hle1 : k ≤ z + x.1 i := by omega
  have hle2 : z + x.1 i ≤ k' := by omega
  have m1 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle1
  have m2 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle2
  refine ⟨(∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) + (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) * (z + x.1 i), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · omega
  · exact ⟨z + x.1 i, by omega⟩
  · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hPp, Nat.add_sub_cancel]

theorem cm_top {dl : DCl X} (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (hne : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) = (Nl C0 CE1 CE2 X dl x i).sup id := by
  rw [topA_eq]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id hne
  have hsup : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).sup id = m :=
    le_antisymm (Finset.sup_le fun v hv => hmax v hv) (Finset.le_sup (f := id) hm)
  rw [hsup]
  apply le_antisymm
  · exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hm)
  · apply Finset.sup_le
    intro y hy
    simp only [Nl, Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact cm_mono dl x i (hmax v hv)

variable (C0 CE1 CE2 X)

def XMof (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : flipOneThree.InstM where
  p := X.p
  hp := X.std.1.prime
  s := X.s
  r := X.r
  hr := X.hm
  LL := lLL C0 CE1 CE2 X a b x
  T := gT C0 CE1 CE2 X b
  a := X.L.a
  E := X.L.Y * kapS X
  Yl := fun i => (Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1
  n₀ := fun i => sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)
  dd := fun _ => 1
  ρ := ⟨X.r - 1, Nat.sub_lt (Nat.pos_of_ne_zero X.hm) one_pos⟩

def BADf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Formalism.GM.M.bad X.p (fun F G => Formalism.GM.M.fockN X.p ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
            ((gT C0 CE1 CE2 X b).phis X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) F) G)
    (Formalism.GM.M.YZ X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) (gT C0 CE1 CE2 X b).J
      (gT C0 CE1 CE2 X b).thr) D

def FRf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Module.finrank ℚ_[X.p] (Formalism.GM.M.Y X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
    (gT C0 CE1 CE2 X b).J (gT C0 CE1 CE2 X b).thr)

theorem bY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) (D : ℤ) :
    bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x D =
      BADf C0 CE1 CE2 X a b x D (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold BADf bY badY
  rw [hf, ← h]
  rfl

theorem dimY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) :
    dimY X.p (r := X.r) (gB C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) 0 b) x.1 x.2 =
      FRf C0 CE1 CE2 X a b x (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold FRf dimY
  rw [hf, ← h]
  rfl

end Fibre

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section TM

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def epsM (XM : flipOneThree.InstM) (i : Fin XM.T.t) : ℝ := XM.eps i

def RestTMHyp : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (XMof C0 CE1 CE2 X dl a x.1 x.2).Hyp

def RestTMEps (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, epsM (XMof C0 CE1 CE2 X dl a x.1 x.2) i ≤ (30 + CM) / X.L.Y

variable {C0 CE1 CE2 X}

theorem mem_levels {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) (h : x ∈ levels G) :
    G.LevelOK x.1 x.2 := by
  classical
  unfold levels at h
  exact (Finset.mem_filter.1 h).2

theorem chain_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (segChain X.p (X.S C0 CE1 CE2) aTop b).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) := by
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have h2 : ¬ (q : ℕ) % 2 = 0 := by omega
  have h3 : topOf q h1 = uTop (X.S C0 CE1 CE2) i := by
    unfold topOf uTop
    exact Fin.ext (by simp only; omega)
  have h4 : ¬ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) < (X.S C0 CE1 CE2).sigma := by
    unfold uTop; simp
  unfold segChain
  simp only
  rw [dif_neg h1, if_neg h2, h3, if_neg h4]

theorem lvlRoom_of {dl : DCl X} {a0 : Fin X.s → ℕ} (ha0 : a0 ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hb : x.1.ry = dl.2) (hx : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a) :
    LvlRoom C0 CE1 CE2 X dl x.2 := by
  classical
  intro i v hv
  have ha' : Function.update a0 (uTop (X.S C0 CE1 CE2) i) v ∈ cbox C0 CE1 CE2 X dl := by
    have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
    have ha0' := hbox ▸ ha0
    rw [hbox]
    rw [Fintype.mem_piFinset] at ha0' ⊢
    intro l
    by_cases hl : l = uTop (X.S C0 CE1 CE2) i
    · subst hl; rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hl]; exact ha0' l
  have h := hx _ ha'
  unfold idx at h
  rw [Finset.mem_sigma] at h
  have hl := h.2
  have hOK := ((mem_levels _ _ hl).1 i).2
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have e := chain_eta (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1 i
    ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
      by omega⟩ (by show min (2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) (2 * X.s + 1 - 1) = _; omega)
  have e2 : (gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).LL.deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ = (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := rfl
  have hOK' : x.2.1 i ≤ (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := by
    rw [← e2]; exact hOK
  rw [e] at hOK'
  unfold coarseC at hOK'
  rw [Function.update_self, hb] at hOK'
  exact hOK'

theorem reindex {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (f : (Fin (X.S C0 CE1 CE2).t → ℕ) → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        f (fun i => cm C0 CE1 CE2 X dl x i (n i)) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), f n := by
  classical
  unfold Nl
  rw [Fintype.piFinset_image, Finset.sum_image]
  intro n hn n' hn' h
  funext i
  exact cm_inj hr i (Fintype.mem_piFinset.1 hn i) (Fintype.mem_piFinset.1 hn' i) (congrFun h i)

theorem prog_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hr : LvlRoom C0 CE1 CE2 X dl x) (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    (XMof C0 CE1 CE2 X dl a b x).prog = Fintype.piFinset (Nl C0 CE1 CE2 X dl x) := by
  unfold flipOneThree.InstM.prog
  congr 1
  funext i
  exact (interval_eq _ ((hne i).image _) (Nl_conv hr i)).symm

theorem top_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) (i : Fin (X.S C0 CE1 CE2).t) :
    (XMof C0 CE1 CE2 X dl a b x).top i = cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  rw [cm_top x i (hne i)]
  have hmem : sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) ∈ Nl C0 CE1 CE2 X dl x i := by
    have := Nat.sInf_mem (s := ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)) (by
      obtain ⟨v, hv⟩ := (hne i).image (cm C0 CE1 CE2 X dl x i)
      exact ⟨v, by exact_mod_cast hv⟩)
    exact_mod_cast this
  have hle := Finset.le_sup (f := id) hmem
  show sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) +
    1 * ((Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1 - 1) = _
  simp only [id] at hle ⊢
  omega


theorem exponent_matrix_first_depth_eq (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (XMof C0 CE1 CE2 X dl a b x).D1 = D1r C0 CE1 CE2 X 1 := by
  show ((X.S C0 CE1 CE2).t : ℝ) * (X.L.Y * kapS X + kapS X) + kapS X = _
  unfold D1r
  rw [one_mul]

theorem fibre_ineq (D : Formalism.BasicNotions.D7) (ε : ℝ) {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x)
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty)
    (hM : ModelLatticeRank D (XMof C0 CE1 CE2 X dl a b x)) (hH : (XMof C0 CE1 CE2 X dl a b x).Hyp)
    (hε : ∀ i, epsM (XMof C0 CE1 CE2 X dl a b x) i ≤ ε) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) := by
  classical
  have h1 := hM hH
  rw [prog_eq a b hr hne, exponent_matrix_first_depth_eq] at h1
  have hc : (0 : ℝ) < ((Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).card : ℝ) := by
    have : (Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).Nonempty := by
      rw [Fintype.piFinset_nonempty]
      intro i
      exact (hne i).image _
    exact_mod_cast this.card_pos

  have hL : ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) := by
    rw [← reindex hr (fun n => (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [bY_ovr C0 CE1 CE2 X dl a n b hb x]

  have hR : ∀ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    intro i
    rw [← reindex hr (fun n => (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold upd
    rw [ovr_update _ (uTop_inj C0 CE1 CE2 X), dimY_ovr C0 CE1 CE2 X dl a _ b hb x, top_eq a b hne i]
    congr 2
    funext i'
    by_cases hi : i' = i
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [hL]
  simp only [hR]
  have h2 : ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) ≤
      ∑ i, epsM (XMof C0 CE1 CE2 X dl a b x) i * ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    have h3 := (div_le_iff₀ hc).1 h1
    calc _ ≤ _ := h3
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have key : ∀ (e S c : ℝ), c ≠ 0 → e * (S / c * c) = e * S := fun e S c hc' => by
          rw [div_mul_cancel₀ _ hc']
        rw [mul_assoc]
        exact (key _ _ _ hc.ne').trans rfl
  refine h2.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hε i) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

theorem restTM_of_rests (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM)
    (hF : RestFree C0 CE1 CE2 X) (hH : RestTMHyp C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) :
    RestTM C0 CE1 CE2 X 1 := by
  classical
  intro dl hdl a0 ha0 x hx
  have hxa : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a := fun a ha => by
    rw [← hF dl hdl a0 ha0 a ha]; exact hx
  have hb : x.1.ry = dl.2 := by
    have := hx
    unfold idx at this
    rw [Finset.mem_sigma, Finset.mem_filter] at this
    exact (congrArg Prod.snd this.1.2 : _)
  have hr := lvlRoom_of ha0 hb hxa
  have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
  have hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty := fun i =>
    ⟨a0 (uTop (X.S C0 CE1 CE2) i), Fintype.mem_piFinset.1 (hbox ▸ ha0) _⟩
  rw [hbox]
  refine box_of_fibres (uTop (X.S C0 CE1 CE2)) (uTop_inj C0 CE1 CE2 X) (Wl C0 CE1 CE2 X dl)
    (fun a => (bY C0 CE1 CE2 X a x.1 x.2 ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ))
    (fun i a => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl a i) 0 x.1) x.2.1 x.2.2 : ℝ))
    ((30 + 1) / X.L.Y) (hbox ▸ ⟨a0, ha0⟩) ?_
  intro a ha
  have ha' : a ∈ cbox C0 CE1 CE2 X dl := hbox ▸ ha
  exact fibre_ineq D _ a x.1 hb hr hne (hM _) (hH dl hdl a ha' x (hxa a ha'))
    (hE dl hdl a ha' x (hxa a ha'))

end TM

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Hyp

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestTMSize : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i) ∧
    (∀ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y ≤ 2 * X.L.a) ∧
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.z i ≤ 2 * X.L.a) ∧
    (∑ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y) ≤ 8 * X.L.a ∧
    1 ≤ X.L.a

variable {C0 CE1 CE2 X}

theorem lgA_ge_one (p a r : ℕ) (hp : 1 < p) (hr : 1 ≤ r) : 1 ≤ lgA p a r := by
  unfold lgA
  have : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg (by exact_mod_cast hp)
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  linarith

theorem r_ge_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : 2 ≤ X.r := by
  have h := hH.1.2.2.2.2.2.2.1
  have h1 := hH.1.2.2.2.2.2.1
  show 2 ≤ X.L.m
  omega

theorem p_ne_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : X.p ≠ 2 := by
  have h5 := X.std.1.five_le
  show X.L.p ≠ 2
  omega

private theorem setTies_deg_succ_pos_eq_of_strictMono {N : ℕ} (LL : GM.M.Letters N) (T : GM.M.TieData) (n : Fin T.t → ℕ)
    (hT : StrictMono T.pos) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  have hex : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := hT.injective (by have := Classical.choose_spec hex; omega)
  show (if h' : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 then n (Classical.choose h')
    else LL.deg ⟨T.pos i + 1, h⟩) = n i
  rw [dif_pos hex, hc]

set_option maxHeartbeats 400000 in

theorem restTMHyp_of {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : RestTMSize C0 CE1 CE2 X) : RestTMHyp C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  obtain ⟨hS1, hS2, hS3, hS4, hS5⟩ := hS dl hdl a ha x hx
  have hY : 1 ≤ X.L.Y := by
    obtain ⟨⟨hY, -⟩, -⟩ := hH
    exact hY
  set M := XMof C0 CE1 CE2 X dl a x.fst x.snd with hM
  have hpos : ∀ l : Fin M.T.t, M.T.pos l = 2 * ((uTop (X.S C0 CE1 CE2) l : Fin X.s) : ℕ) := fun l => rfl
  have hlt : ∀ l : Fin M.T.t, M.T.pos l + 1 < 2 * M.s + 1 := by
    intro l
    rw [hpos l]
    have := (uTop (X.S C0 CE1 CE2) l).isLt
    show _ < 2 * X.s + 1
    omega
  have hmono : StrictMono M.T.pos := by
    intro i j hij
    rw [hpos i, hpos j]
    have : (i : ℕ) < j := hij
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ))
    omega
  have hvec : ∀ y, M.LL.vec y = decide ((y : ℕ) % 2 = 0) := fun y => rfl
  have htop : ∀ i, M.top i ≤ 2 * X.L.a := by
    intro i
    have := hS2 ⟨M.T.pos i + 1, hlt i⟩
    rwa [setTies_deg_succ_pos_eq_of_strictMono _ _ _ hmono i (hlt i)] at this
  have hdd : ∀ i, M.dd i = 1 := fun i => rfl
  have hYl : ∀ i, M.Yl i = (Nl C0 CE1 CE2 X dl x.snd i).sup id
      - sInf ↑(Nl C0 CE1 CE2 X dl x.snd i) + 1 := fun i => rfl
  have hYl1 : ∀ i, 1 ≤ M.Yl i := fun i => by rw [hYl i]; omega
  have htop' : ∀ i, M.top i = M.n₀ i + (M.Yl i - 1) := fun i => by
    show M.n₀ i + M.dd i * (M.Yl i - 1) = _
    rw [hdd, one_mul]
  have hr2 : 2 ≤ X.r := r_ge_two hH
  have key : ∀ n : ℕ, n ≤ 8 * X.L.a + X.r → (n : ℝ) ≤ 8 * M.a + M.r := by
    intro n hn
    rw [show M.a = (X.L.a : ℝ) from rfl, show M.r = X.r from rfl]
    exact_mod_cast hn
  have hd : ∀ j, M.degAt j ≤ 2 * X.L.a := by
    intro j
    unfold InstM.degAt
    split
    · exact hS2 _
    · omega
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hS1, ?_⟩
  · exact p_ne_two hH
  · exact hr2
  · refine ⟨hmono, fun i => ⟨hlt i, ?_, ?_⟩, fun i => ⟨⟨i, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩⟩
    · rw [hvec]
      simp only [decide_eq_true_eq]
      rw [hpos]
      omega
    · rw [hvec]
      simp only [decide_eq_false_iff_not]
      rw [hpos]
      omega
    · show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨i, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = M.T.pos i + 1
      rw [dif_pos (show (i : ℕ) < (X.S C0 CE1 CE2).t from i.isLt)]
      rfl
  · intro y
    rfl
  · intro k
    by_cases hk : (k : ℕ) < (X.S C0 CE1 CE2).t
    · right
      refine ⟨⟨k, hk⟩, ?_⟩
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dif_pos hk]
      rfl
    · left
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dif_neg hk]
      rfl
  · show (1 : ℝ) ≤ X.L.a
    exact_mod_cast hS5
  · show 1 ≤ X.L.Y * kapS X
    have hp1 : 1 < X.p := by
      have := X.std.1.five_le
      show 1 < X.L.p
      omega
    have hl := lgA_ge_one X.p X.L.a X.r hp1 (by omega)
    have hr2' : (2 : ℝ) ≤ X.r := by exact_mod_cast hr2
    have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
    unfold kapS
    have h1 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 * lgA X.p X.L.a X.r := by nlinarith
    nlinarith
  · intro i
    refine ⟨hYl1 i, ?_, ?_⟩
    · rw [hdd]
      norm_num
    · rw [hdd, Nat.cast_one]
      exact isCoprime_one_left
  · refine ⟨?_, fun i => ⟨?_, ?_, ?_⟩⟩
    · apply key
      have : M.LLt.total ≤ 8 * X.L.a := hS4
      omega
    · apply key
      have h1 := hd (M.T.pos i)
      have h2 := hd (M.T.pos i + 1)
      have h3 := hS3 i
      have : M.r = X.r := rfl
      omega
    · apply key
      have := htop i
      have := htop' i
      omega
    · apply key
      have h1 : M.Si i ≤ M.n₀ i := hS1 i
      have := htop i
      have := htop' i
      omega

end Hyp

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem restTM_of (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM) (hF : RestFree C0 CE1 CE2 X)
    (hS : RestTMSize C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) : RestTM C0 CE1 CE2 X 1 :=
  restTM_of_rests D hM hF (restTMHyp_of hH hS) hE

theorem restTM_exists : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestFree C0 CE1 CE2 X → RestTMSize C0 CE1 CE2 X →
      RestTMEps C0 CE1 CE2 X CM → RestTM C0 CE1 CE2 X CM := by
  exact ⟨1, le_rfl, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF hS hE =>
    restTM_of C0 CE1 CE2 X hH D (alternative_mean_value_theorem D) hF hS hE⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

private theorem sort_get_lt_of_lt (s : Finset ℕ) (l u : Fin (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).length)
    (h : l < u) : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l < (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
  have hp := Finset.pairwise_sort s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hn := Finset.sort_nodup s (fun x1 x2 : ℕ => x1 ≤ x2)
  have hle : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≤ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u :=
    hp.rel_get_of_lt h
  have hne : (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get l ≠ (s.sort (fun x1 x2 : ℕ => x1 ≤ x2)).get u := by
    intro he
    have := (List.nodup_iff_injective_get.mp hn) he
    exact absurd this (ne_of_lt h)
  omega

theorem segDists_lt {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (l u : Fin (segS TT j)) (h : l < u) :
    (segDists TT j).get l < (segDists TT j).get u := sort_get_lt_of_lt _ l u h

theorem segDists_lt_G {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (u : Fin (segS TT j)) :
    (segDists TT j).get u < segG TT j := by
  have hm : (segDists TT j).get u ∈ segDists TT j := List.get_mem _ _
  unfold segDists at hm
  rw [Finset.mem_sort, Finset.mem_image] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  rw [Finset.mem_filter] at hx
  have e : (segDists TT j).get u = cdist (segStart TT j) x := hxe.symm
  rw [e]
  exact hx.2.2.2

theorem P_step (l u : Fin X.s) (h : l < u) :
    X.p * (X.S C0 CE1 CE2).P X.p u ≤ (X.S C0 CE1 CE2).P X.p l := by
  have h1 := segDists_lt X.L.TT X.j l u h
  have h2 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p * X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u) ≤
    X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get l)
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hp (by omega)

theorem p_le_P (u : Fin X.s) : X.p ≤ (X.S C0 CE1 CE2).P X.p u := by
  have h1 := segDists_lt_G X.L.TT X.j u
  have hp : 0 < X.p := by
    have := X.std.1.five_le
    show 0 < X.L.p
    omega
  show X.p ≤ X.p ^ (segG X.L.TT X.j - (segDists X.L.TT X.j).get u)
  calc X.p = X.p ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right hp (by omega)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem window_entry_le_two_mul_a (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (l : Fin X.s) :
    (a l : ℝ) ≤ 2 * X.L.a := by
  have h2 := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT l)).2
  have h3 : (a l : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
  exact (h3.trans (Nat.floor_le hS.hF.win0)).trans hS.hF.win_le

theorem r5 : (5 : ℝ) ≤ (X.r : ℝ) + 1 := by
  have : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hS.hF.m4
  show (5 : ℝ) ≤ (X.L.m : ℝ) + 1
  linarith

theorem b_small : 5 / 2 * X.L.b' ≤ X.L.a / 8 := by
  have h1 := hS.kb
  have h2 := r5 hS
  have hb := hS.hF.b0
  nlinarith

theorem chain_wt (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) * ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hA : ∀ l, (coarseA X.p (X.S C0 CE1 CE2) b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := fun l =>
    (coarseA_upper hS b l).trans (by have := b_small hS; have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _; linarith)
  have hC : ∀ l, (coarseC X.p (X.S C0 CE1 CE2) a b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := by
    intro l
    have h1 : coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l ≤ a l :=
      (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have h2 : ((coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l : ℕ) : ℝ) ≤ (a l : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (window_entry_le_two_mul_a hS a hT l)
  have hP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := Nat.cast_nonneg _
  have key : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) := by
    unfold segChain
    dsimp only
    rw [dif_neg hq]
    split_ifs with h2 h3 h3
    · exact Or.inl (hK.2.2.1 _ h3).2.1
    · exact Or.inl (hK.2.1 _ (not_lt.mp h3)).1
    · exact Or.inr (Nat.sub_le _ _)
    · exact Or.inr le_rfl
  rcases key with h | h
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hA _)
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hC _)

theorem oplus_le (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    (b.oPlus : ℝ) ≤ 2 * X.L.a := by
  have h0 := hK.2.2.2
  unfold Oplus at h0
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hB : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b' := hS.bTop
  have hcap := cap_le (p := X.p) (X.S C0 CE1 CE2) b hp1 hS.E0 (5 / 2 * X.L.b') hB X.s
  have hr5 := r5 hS
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hb := hS.hF.b0
  have hkb := hS.kb
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hLa0 := hS.hF.La0
  have hLa : X.L.La C0 / ((X.r : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith [hS.La4]
  have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
  have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by nlinarith
  have h4 : 4 / (X.p : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsum : (∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ)) ≤ (X.s : ℝ) * (2 * X.L.a / X.p) := by
    have : ∀ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 2 * X.L.a / X.p := by
      intro i
      have hP : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p i : ℝ) := by exact_mod_cast p_le_P i
      show 2 * (X.L.a : ℝ) / _ ≤ _
      exact div_le_div_of_nonneg_left (by positivity) hp0 hP
    calc _ ≤ ∑ _i : Fin X.s, 2 * (X.L.a : ℝ) / X.p := Finset.sum_le_sum fun i _ => this i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsp : (X.s : ℝ) * (2 * X.L.a / X.p) ≤ X.L.a / 5 := by
    rw [mul_div_assoc', div_le_div_iff₀ hp0 (by norm_num)]
    have h10 : 10 * (X.s : ℝ) ≤ (X.p : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h10 ha0
    linarith
  have hsum0 : 0 ≤ ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hmid : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2 := by
    show X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2
    linarith
  have hmid0 : 0 ≤ (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 := by
    show 0 ≤ X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2
    positivity
  have hT2 : ((X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) *
      ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.a / 10 := by
    have := mul_le_mul hmid (hsum.trans hsp) hsum0 (by norm_num)
    linarith
  have hBp : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hS.hF.bT_le _ (segNext_mem X.L.TT X.j)
  have hT3 : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) ≤ X.L.a / 10 := by
    have e : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) =
        X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
      show X.L.La C0 * _ / _ = _
      ring
    rw [e]
    have h5 := b_small hS
    have h6 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
    have h7 : X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 1 / 4 * (5 / 2 * X.L.b') :=
      mul_le_mul hLa hBp h6 (by norm_num)
    linarith
  have hsB : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ X.L.a / 2 := by
    have h1 : (X.s : ℝ) ≤ ((X.r : ℝ) + 1) / 2 := by linarith
    have h2 : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ ((X.r : ℝ) + 1) / 2 * (5 / 2 * X.L.b') :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have ha : (X.S C0 CE1 CE2).a = X.L.a := rfl
  rw [ha] at hcap
  linarith

theorem lLL_deg_le_chain (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ (segChain X.p (X.S C0 CE1 CE2) a b).deg q :=
  (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem lLL_deg_le (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ 2 * X.L.a := by
  have h1 := lLL_deg_le_chain hS a b x q
  have h2 : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ 2 * X.L.a := by
    by_cases hq : (q : ℕ) = 2 * X.s
    · have e := segChain_deg_last (p := X.p) (X.S C0 CE1 CE2) a b q hq
      rw [e]
      exact oplus_le hS b a hK
    · have hw := chain_wt hS a hT b hK q hq
      have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := by exact_mod_cast hS.P1 _
      have h0 : (0 : ℝ) ≤ ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) := Nat.cast_nonneg _
      nlinarith
  have h3 : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ 2 * X.L.a := by exact_mod_cast h2
  omega

end Deg

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

variable (C0 CE1 CE2 X) in

def aTopPt (dl : DCl X) (a : Fin X.s → ℕ) : Fin X.s → ℕ :=
  ovr (uTop (X.S C0 CE1 CE2)) a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

theorem digits_of_idx {dl : DCl X} {a : Fin X.s → ℕ} {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    Kept X.p X.r (X.S C0 CE1 CE2) a x.1 ∧ (x.1.rz, x.1.ry) = dl ∧ x.2 ∈ lv C0 CE1 CE2 X a x.1 := by
  classical
  unfold idx at hx
  simp only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

theorem Wl_ne {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    (Wl C0 CE1 CE2 X dl l).Nonempty := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  exact ⟨a l, Fintype.mem_piFinset.1 hW l⟩

theorem topA_mem_Wl {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ Wl C0 CE1 CE2 X dl l := by
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)
  rw [topA_eq, hMe]
  exact hM

theorem aTopPt_mem {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) :
    aTopPt C0 CE1 CE2 X dl a ∈ cbox C0 CE1 CE2 X dl := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  rw [hbox]
  exact ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)

theorem setTies_top {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2 := by
  have hb : x.1.ry = dl.2 := congrArg Prod.snd (digits_of_idx hx).2.1
  have e1 := lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2
  show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _
  unfold aTopPt
  rw [e1]
  congr 1
  funext i
  rw [top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]
  unfold cm
  rw [hb]

def RestSI : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i

theorem restTMSize_of (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (hSI : RestSI (C0 := C0) (CE1 := CE1)
    (CE2 := CE2) (X := X)) : RestTMSize C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  have hT' := (mem_cbox' ha').1
  have e := setTies_top ha hx
  refine ⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [e]
    exact lLL_deg_le hS _ hT' x.1 hK' x.2 y
  · intro i
    show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a
    have h1 := coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)
    have h2 := b_small hS
    have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
    have h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a := by nlinarith
    have h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a := by exact_mod_cast h3
    omega
  ·
    rw [e, Fin.sum_univ_castSucc]
    have hs : 2 * X.s + 2 ≤ X.r := hS.hF.s_le
    have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
    have hr5 := r5 hS
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
    have hlast := lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))
    have hone : ∀ q : Fin (2 * X.s),
        ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a := by
      intro q
      have hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s := by
        have := q.2
        simp only [Fin.val_castSucc]
        omega
      have h1 := chain_wt hS _ hT' x.1 hK' q.castSucc hq
      have h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤
          ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) := by
        exact_mod_cast lLL_deg_le_chain hS _ x.1 x.2 q.castSucc
      have h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) := by
        exact_mod_cast p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)
      calc ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) *
            ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) :=
            mul_le_mul h2 h3 hp0.le (Nat.cast_nonneg _)
        _ ≤ 2 * X.L.a := h1
    have hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) *
        X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc ∑ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ∑ _q : Fin (2 * X.s), 2 * (X.L.a : ℝ) := Finset.sum_le_sum fun q _ => hone q
        _ = (2 * X.s : ℕ) * (2 * X.L.a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p := by
      have h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast (by omega : 2 * X.s ≤ X.r)
      nlinarith
    have hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤
        2 * X.L.a := by
      have h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p := by nlinarith
      exact le_of_mul_le_mul_right (hsum.trans h1) hp0
    have hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤
        2 * X.L.a := by exact_mod_cast hsum2
    exact (Nat.add_le_add hsum3 hlast).trans (by omega)
  · exact_mod_cast hS.hF.a1

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section SI

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

private theorem lLL_deg_mul_segP_le_two_mul_a_of_kept (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA))
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hF := hS.hF
  have h1 := lLL_deg_le_chain hS a b x q
  obtain ⟨-, hK1, hK2, -⟩ := hK
  set v := topOf q hq with hv
  set P := SegData.P X.p (X.S C0 CE1 CE2) v with hPdef
  have hc : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ (X.S C0 CE1 CE2).bTop v / P ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ a v / P := by
    have hA : coarseA X.p (X.S C0 CE1 CE2) b v ≤ (X.S C0 CE1 CE2).bTop v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hC : coarseC X.p (X.S C0 CE1 CE2) a b v ≤ a v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [segChain, dif_neg hq]
    rw [← hv]
    split_ifs with h2 h3 h3
    · exact Or.inl ((hK2 v h3).2.1.trans hA)
    · exact Or.inl (((hK1 v (not_lt.mp h3)).1).trans hA)
    · exact Or.inr ((Nat.sub_le _ _).trans hC)
    · exact Or.inr hC
  have hbT : ((X.S C0 CE1 CE2).bTop v : ℝ) ≤ 2 * X.L.a := by
    have h5 := hS.bTop v
    have hb0 := hF.b0
    have hlt := hF.b_lt
    have hpm := hF.p_ge
    have hm := hF.m4
    have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hm
    have hp25 : (25 : ℝ) ≤ X.L.p := by nlinarith
    nlinarith
  have haT : (a v : ℝ) ≤ 2 * X.L.a := by
    have hmem := Fintype.mem_piFinset.mp hT v
    simp only [flipOneThree.Inst.winA, Finset.mem_Icc] at hmem
    have h2 := Nat.floor_le hF.win0
    have h3 : (a v : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) := by exact_mod_cast hmem.2
    linarith [hF.win_le]
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ 2 * X.L.a → (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ N / P →
      ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (P : ℝ) ≤ 2 * X.L.a := by
    intro N hN hd
    have h4 : (lLL C0 CE1 CE2 X a b x).deg q * P ≤ N :=
      (Nat.mul_le_mul_right P (h1.trans hd)).trans (Nat.div_mul_le_self N P)
    have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * P : ℕ) : ℝ) ≤ N := by exact_mod_cast h4
    push_cast at h5
    linarith
  rcases hc with hc | hc
  · exact hfin _ hbT hc
  · exact hfin _ haT hc

theorem S_bound (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) :
    ((gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
  have hF := hS.hF
  have hK' := hK
  obtain ⟨-, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hus : (u : ℕ) < X.s := u.2
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  have hSdef : (gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i =
      ∑ q : Fin (2 * X.s + 1), if (q : ℕ) ≤ 2 * (u : ℕ) then (lLL C0 CE1 CE2 X a b x).deg q else 0 := rfl
  rw [hSdef]
  push_cast
  rw [Finset.sum_mul]
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpm := hF.p_ge
  have hp : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have hb0 := hF.b0
  have hB : (0 : ℝ) ≤ 2 * X.L.a / X.p := by positivity
  have key : ∀ q : Fin (2 * X.s + 1),
      (if (q : ℕ) ≤ 2 * (u : ℕ) then ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) else 0) *
          (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
        (if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p := by
    intro q
    by_cases h : (q : ℕ) ≤ 2 * (u : ℕ)
    · rw [if_pos h]
      by_cases he : (q : ℕ) = 2 * (u : ℕ)
      · rw [if_pos he]
        have h1 := lLL_deg_le_chain hS a b x q
        rw [segChain_deg_even (X.S C0 CE1 CE2) a b q u he hσu] at h1
        have hA : coarseA X.p (X.S C0 CE1 CE2) b u ≤
            (X.S C0 CE1 CE2).bTop u / SegData.P X.p (X.S C0 CE1 CE2) u :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        have h4 : (lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u ≤
            (X.S C0 CE1 CE2).bTop u :=
          (Nat.mul_le_mul_right _ ((h1.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
        have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u : ℕ) : ℝ) ≤
            (X.S C0 CE1 CE2).bTop u := by exact_mod_cast h4
        push_cast at h5
        linarith [hS.bTop u]
      · rw [if_neg he, zero_add]
        have hq : (q : ℕ) ≠ 2 * X.s := by omega
        have h2 := lLL_deg_mul_segP_le_two_mul_a_of_kept hS a hT b hK x q hq
        have hvu : topOf q hq < u := by
          rw [Fin.lt_iff_val_lt_val]
          simp only [topOf]
          omega
        have h3 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) _ _ hvu
        have h3' : ((X.p : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
            (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) := by exact_mod_cast h3
        rw [le_div_iff₀ hp]
        have hd0 : (0 : ℝ) ≤ ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) := Nat.cast_nonneg _
        nlinarith
    · rw [if_neg h, zero_mul]
      split_ifs <;> positivity
  calc _ ≤ ∑ q : Fin (2 * X.s + 1),
        ((if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p) :=
        Finset.sum_le_sum (fun q _ => key q)
    _ = 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_eq_single (⟨2 * (u : ℕ), by omega⟩ : Fin (2 * X.s + 1))]
        · simp
        · intro c _ hc
          rw [if_neg]
          intro hc'
          exact hc (Fin.ext hc')
        · intro hc
          exact absurd (Finset.mem_univ _) hc

end SI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section N0

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem cast_sub_ge (w j : ℕ) : (w : ℝ) - j ≤ ((w - j : ℕ) : ℝ) := by
  rcases le_total j w with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (w : ℝ) ≤ j := by exact_mod_cast h
    linarith

theorem lower_bound_initial_multiplicity {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) (i : Fin (X.S C0 CE1 CE2).t) :
    (X.L.a : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) - 5 / 2 * X.L.b' ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
  obtain ⟨hK, hdl, hlv⟩ := digits_of_idx hx
  have hK' := hK
  obtain ⟨hDig, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  set P := SegData.P X.p (X.S C0 CE1 CE2) u with hPdef
  have hPpos : 0 < P := twoPow_pos C0 CE1 CE2 X u
  have hj : x.2.1 i ≤ x.1.o u := (((mem_lv _ _ _).mp hlv).1 i).1
  have hA : coarseA X.p (X.S C0 CE1 CE2) x.1 u ≤ (X.S C0 CE1 CE2).bTop u / P :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hjP : x.2.1 i * P ≤ (X.S C0 CE1 CE2).bTop u :=
    (Nat.mul_le_mul_right _ ((hj.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
  have hry : x.1.ry = dl.2 := by rw [← hdl]
  have hne : (Nl C0 CE1 CE2 X dl x.2 i).Nonempty := (Wl_ne ha u).image _
  have hn0 : (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i = sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) := rfl
  have hmem : sInf (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) ∈ (↑(Nl C0 CE1 CE2 X dl x.2 i) : Set ℕ) :=
    Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
  rw [Finset.mem_coe] at hmem
  obtain ⟨v, hv, hcm⟩ := Finset.mem_image.mp hmem
  simp only [Wl, Finset.mem_filter, flipOneThree.Inst.winA, Finset.mem_Icc] at hv
  obtain ⟨⟨hav, -⟩, hsv, hdvd⟩ := hv
  rw [← hu] at hsv hdvd
  rw [hn0, ← hcm]
  have hsum : ∑ c : Fin (X.r + 1), dl.2 u c ≤ (X.r + 1) * P := by
    calc ∑ c : Fin (X.r + 1), dl.2 u c ≤ ∑ _c : Fin (X.r + 1), P := by
          apply Finset.sum_le_sum
          intro c _
          rw [← hry]
          exact le_of_lt (hDig.1 u c).2
      _ = (X.r + 1) * P := by simp
  have hQ : (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P * P = v - ∑ c : Fin (X.r + 1), dl.2 u c :=
    Nat.div_mul_cancel hdvd
  have hc1 := cast_sub_ge hS ((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P) (x.2.1 i)
  have hcm' : cm C0 CE1 CE2 X dl x.2 i v = (v - ∑ c : Fin (X.r + 1), dl.2 u c) / P - x.2.1 i := rfl
  rw [hcm']
  have hQr : (((v - ∑ c : Fin (X.r + 1), dl.2 u c) / P : ℕ) : ℝ) * (P : ℝ) =
      (v : ℝ) - (∑ c : Fin (X.r + 1), dl.2 u c : ℕ) := by
    rw [← Nat.cast_sub hsv, ← Nat.cast_mul, hQ]
  have hsumR : ((∑ c : Fin (X.r + 1), dl.2 u c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by
    exact_mod_cast hsum
  have hjPR : ((x.2.1 i : ℕ) : ℝ) * (P : ℝ) ≤ 5 / 2 * X.L.b' := by
    have h1 : (((x.2.1 i * P : ℕ)) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u := by exact_mod_cast hjP
    push_cast at h1
    linarith [hS.bTop u]
  have havR : (X.L.a : ℝ) ≤ v := by exact_mod_cast hav
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem restSI_proved (hFree : RestFree C0 CE1 CE2 X) : RestSI (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) := by
  intro dl hdl a ha x hx i
  have hF := hS.hF
  have hinj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
    intro k k' h
    simp only [uTop, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  set n : Fin (X.S C0 CE1 CE2).t → ℕ := fun k => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) k) with hn
  set a' := ovr (uTop (X.S C0 CE1 CE2)) a n with haeq
  have ha' : a' ∈ cbox C0 CE1 CE2 X dl := by
    have hb := cbox_eq C0 CE1 CE2 X dl a ha
    rw [hb]
    apply ovr_mem _ hinj
    · rw [← hb]
      exact ha
    · exact Fintype.mem_piFinset.mpr (fun k => topA_mem_Wl ha _)
  have hx' : x ∈ idx C0 CE1 CE2 X dl a' := by
    rw [← hFree dl hdl a ha a' ha']
    exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  obtain ⟨-, hdl0, -⟩ := digits_of_idx hx
  have hry : x.1.ry = dl.2 := by rw [← hdl0]
  have hT' := (mem_cbox' ha').1
  have hSb := S_bound hS a' hT' x.1 hK' x.2 i
  have hn0 := lower_bound_initial_multiplicity hS ha hx i
  have htop : (XMof C0 CE1 CE2 X dl a x.1 x.2).top = fun k =>
      (n k - ∑ c : Fin (X.r + 1), x.1.ry (uTop (X.S C0 CE1 CE2) k) c) /
        SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) k) - x.2.1 k := by
    funext k
    have hne : (Nl C0 CE1 CE2 X dl x.2 k).Nonempty := (Wl_ne ha _).image _
    have h1 := cm_top (dl := dl) x.2 k (Wl_ne ha _)
    have h2 : sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) ≤ (Nl C0 CE1 CE2 X dl x.2 k).sup id := by
      have hm := Nat.sInf_mem (Finset.coe_nonempty.mpr hne)
      exact Finset.le_sup (f := id) hm
    rw [hry]
    show sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) +
        1 * ((Nl C0 CE1 CE2 X dl x.2 k).sup id - sInf (↑(Nl C0 CE1 CE2 X dl x.2 k) : Set ℕ) + 1 - 1) =
      cm C0 CE1 CE2 X dl x.2 k (n k)
    rw [h1]
    omega
  have hL : (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
      (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X a' x.1 x.2 := by
    rw [htop, haeq, lLL_ovr]
    rfl
  have hP : (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hsm : (2 * (X.s : ℝ) + 2) ≤ X.L.m := by exact_mod_cast hF.s_le
  have hpm := hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have h48 : (4 * (X.s : ℝ) + 8) ≤ X.p := by
    show (4 * (X.s : ℝ) + 8) ≤ X.L.p
    nlinarith
  have hb'p : X.L.b' ≤ (X.L.a : ℝ) / X.p := by
    rw [le_div_iff₀ hp0]
    have := hF.b_lt
    show X.L.b' * X.L.p ≤ X.L.a
    linarith
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hsum : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p) ≤ X.L.a := by
    calc (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) + 6 * ((X.L.a : ℝ) / X.p)
        = (4 * (X.s : ℝ) + 8) * ((X.L.a : ℝ) / X.p) := by ring
      _ ≤ (X.p : ℝ) * ((X.L.a : ℝ) / X.p) := mul_le_mul_of_nonneg_right h48 (by positivity)
      _ = X.L.a := by field_simp
  have hreal : ((GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i : ℕ) : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i : ℝ) *
        (SegData.P X.p (X.S C0 CE1 CE2) (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    linarith
  have hnat : GM.M.TieData.S (lLL C0 CE1 CE2 X a' x.1 x.2) (gT C0 CE1 CE2 X x.1) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i := by
    exact_mod_cast le_of_mul_le_mul_right hreal hP
  rw [hL]
  exact hnat

theorem restTMSize_proved (hFree : RestFree C0 CE1 CE2 X) : RestTMSize C0 CE1 CE2 X :=
  restTMSize_of hS hFree (restSI_proved hS hFree)

end N0

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
