import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem coarse_degree_gt_quotient {r : ℕ} (g P : ℕ) (f : Fin (r + 1) → ℕ) (hf : ∀ c, f c < P) (hs : ∑ c, f c ≤ g)
    (hd : P ∣ g - ∑ c, f c) (hP : 0 < P) :
    (g : ℝ) / P - ((r : ℝ) + 1) < (((g - ∑ c, f c) / P : ℕ) : ℝ) := by
  have h := (coarse_bounds g P f hf hs hd).2
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  rw [div_sub' (ne_of_gt hP'), div_lt_iff₀ hP']
  linarith

theorem coarse_degrees_large_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] (h : Std C0 Cde CE1 CE2 4 X) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) (A : ℕ)
    (hA : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ)) :
    X.k ^ 3 ≤ (A : ℝ) ∧ (∀ i, X.k ^ 3 ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ)) ∧
      (∀ i, X.k ^ 3 ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ)) ∧ X.k ^ 2 ≤ (X.p : ℝ) ∧ 10 ≤ X.k ∧
      1 ≤ X.La C0 ∧ 4 * X.La C0 ≤ X.k := by
  have hk5 := h.k5
  have hk0 : 0 < X.k := by linarith
  have hY := h.Y1
  have hQ1 := h.Q1
  have hN2 := h.N2
  have hN1 := h.one_le_level_alt
  have hLa := h.La1
  have hb := h.bpos
  have hba := h.ba
  have hde := h.de6
  have hLaK := h.LaK

  have hK240 : 240 * (X.N1 : ℝ) * X.La C0 < X.k := by
    have h1 : 40 * (X.N1 : ℝ) * X.La C0 / X.k < 1 / 6 := lt_of_le_of_lt hLaK hde
    rw [div_lt_iff₀ hk0] at h1
    linarith
  have hNLa : 1 ≤ (X.N1 : ℝ) * X.La C0 := one_le_mul_of_one_le_of_one_le hN1 hLa
  have hk10 : 10 ≤ X.k := by nlinarith
  have hLa4 : 4 * X.La C0 ≤ X.k := by nlinarith
  have hkp : X.k ^ 2 ≤ (X.p : ℝ) := by
    have := h.pk
    have hY2 : 1 ≤ X.Y ^ 2 := one_le_pow₀ hY
    nlinarith [sq_nonneg X.k]

  have hb4 : 4 * X.k ^ 3 * X.Q ≤ X.b' := by
    have hHb := h.Hb
    have hNQY : X.Q ≤ X.N * X.Q ^ 4 * X.Y := by
      have q4 : X.Q ≤ X.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
      have hN1' : (1 : ℝ) ≤ X.N := by linarith
      have : X.Q ^ 4 ≤ X.N * X.Q ^ 4 * X.Y := by
        have hq : 0 ≤ X.Q ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hN1' hq]
      linarith
    have hk3 : 0 ≤ 4 * X.k ^ 3 := by positivity
    calc 4 * X.k ^ 3 * X.Q ≤ 4 * X.k ^ 3 * (X.N * X.Q ^ 4 * X.Y) := mul_le_mul_of_nonneg_left hNQY hk3
      _ = 4 * X.k ^ 3 * X.N * X.Q ^ 4 * X.Y := by ring
      _ ≤ X.b' := hHb
  have hQ0 : 0 < X.Q := by linarith
  have hk3 : X.k ≤ X.k ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, hkp, hk10, hLa, hLa4⟩
  ·
    have hA0 := h.half_ratio_le_segment_base_of_std j
    have hfrac : X.N1 * X.La C0 / X.k ≤ 1 / 2 := by
      rw [div_le_iff₀ hk0]; nlinarith
    have hA0pos : 0 ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := le_trans (by positivity) hA0
    have h1 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / 2 ≤ (A : ℝ) := by
      have : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 / 2) ≤
          ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) :=
        mul_le_mul_of_nonneg_left (by linarith) hA0pos
      linarith
    have h2 : X.k ^ 3 ≤ (X.a : ℝ) / (2 * X.Q) / 2 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  · intro i
    have hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
      unfold SegData.P; exact pow_pos (by have := h.p5; omega) _
    have hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q := by
      have hl := h.levels j i
      exact le_trans hl.2.2.2.2 hl.2.2.2.1
    have hgt := coarse_degree_gt_quotient ((X.seg C0 CE1 CE2 j).bTop i) ((X.seg C0 CE1 CE2 j).P X.p i) (rz i)
      (fun c => (hd.1 i c).1) (hd.2.1 i).1 (hd.2.1 i).2 hPpos
    have hmem := (pos_mem X.TT j i).1
    have hbT : X.b' * (1 - be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (h.winB _ hmem).1
    have hbe : be X C0 ≤ 1 / 2 := by have := h.beLe; have := h.be0; have : 0 ≤ 18 * X.N1 * X.La C0 / X.k := by positivity
                                     linarith
    have hb2 : X.b' / 2 ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ) := by
      show X.b' / 2 ≤ (X.bT (segPos X.TT j i) : ℝ)
      nlinarith
    have hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by exact_mod_cast hPpos
    have h3 : X.b' / 2 / X.Q ≤ ((X.seg C0 CE1 CE2 j).bTop i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      calc X.b' / 2 / X.Q ≤ X.b' / 2 / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hP0 hPQ
        _ ≤ _ := div_le_div_of_nonneg_right hb2 hP0.le
    have h4 : 2 * X.k ^ 3 ≤ X.b' / 2 / X.Q := by
      rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
    have hkr : ((X.m : ℝ) + 1) = X.k := rfl
    show X.k ^ 3 ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i : ℝ)
    unfold coarseA
    show X.k ^ 3 ≤ ((((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)
    rw [hkr] at hgt
    linarith
  · intro i
    have hPpos : 0 < (X.seg C0 CE1 CE2 j).P X.p i := by
      unfold SegData.P; exact pow_pos (by have := h.p5; omega) _
    have hPQ : ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) ≤ X.Q := by
      have hl := h.levels j i
      exact le_trans hl.2.2.2.2 hl.2.2.2.1
    have hgt := coarse_degree_gt_quotient (segATop X.TT X.aT j i) ((X.seg C0 CE1 CE2 j).P X.p i) (ry i)
      (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2 hPpos
    have hmem := (pos_mem X.TT j i).1
    have haT : (X.a : ℝ) ≤ (segATop X.TT X.aT j i : ℝ) := (h.winA _ hmem).1
    have hP0 : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by exact_mod_cast hPpos
    have ha0 : (0 : ℝ) ≤ X.a := by positivity
    have h3 : (X.a : ℝ) / X.Q ≤ (segATop X.TT X.aT j i : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      calc (X.a : ℝ) / X.Q ≤ (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
            div_le_div_of_nonneg_left ha0 hP0 hPQ
        _ ≤ _ := div_le_div_of_nonneg_right haT hP0.le
    have h4 : 2 * X.k ^ 3 ≤ (X.a : ℝ) / X.Q := by
      rw [le_div_iff₀ hQ0]; nlinarith
    have hkr : ((X.m : ℝ) + 1) = X.k := rfl
    show X.k ^ 3 ≤ (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i : ℝ)
    unfold coarseC
    show X.k ^ 3 ≤ (((segATop X.TT X.aT j i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i : ℕ) : ℝ)
    rw [hkr] at hgt
    linarith

theorem coarse_degrees_large_holds : CoarseDegreesLargeBeyond :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 4)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      fun X _ hD hI hc j rz ry hd A hA =>
        coarse_degrees_large_of_std (std_of hCc hC0 h1 h2 (by norm_num : (1 : ℝ) ≤ 4) t1 t2 t3 t4 t5 hD hI hc) j rz ry hd A hA

section PFA

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

theorem pfa_rho_eq [NeZero r] (i : Fin s) : pairRho mu i.val = wbK mu (2 * i.val + 2) 0 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  unfold pairRho wbK
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega), dif_pos ⟨by omega, hr⟩]
  rfl

theorem pfa_odd_nonneg (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : ℕ) (hi : i ≤ s) :
    0 ≤ wbK mu (2 * i + 1) 0 := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; rw [wb_one hP 0]
  · exact (wb_shape hP hr i hi).1 0 h0

theorem pfa_rho_nonneg [NeZero r] (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : Fin s) :
    0 ≤ pairRho mu i.val := by
  rw [pfa_rho_eq]
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := (wb_vstep hP (2 * i.val + 1) (by omega) (Or.inr (by omega))).1 0 hr0
  have h2 := pfa_odd_nonneg hP hr i.val (by omega)
  linarith

theorem pfa_c_nonneg [NeZero r] (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (l : ℕ) : 0 ≤ pairC mu l := by
  have key : ∀ l, l ≤ s → 0 ≤ pairC mu l := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0; rw [pairC_zero hP.1]; exact Int.natCast_nonneg _
    · obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
      have h1 := (pf_rho_le_c hP.1 (⟨i, by omega⟩ : Fin s)).2
      have h2 := pfa_rho_nonneg hP hr (⟨i, by omega⟩ : Fin s)
      exact le_trans h2 h1
  rcases le_or_gt l s with hl | hl
  · exact key l hl
  · have e : pairC mu l = pairC mu s := by
      unfold pairC
      congr 1
      apply Fin.ext
      simp only [finPos]
      omega
    rw [e]; exact key s le_rfl

end PFA

section PFB

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

theorem pfa_prev_real [NeZero r] (hP : IsPair A Ai Ci mu lam) (i : Fin s) :
    ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ : ℤ) : ℝ) ≤
      ∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0 := by
  have h1 := pf_prev_le hP.1 i.val (by omega)
  have h2 : (∑ x : Fin s, if x.val < i.val then pairW mu x.val else 0) ≤
      ∑ x : Fin s, if x.val < i.val then (Ai x : ℤ) else 0 :=
    Finset.sum_le_sum fun x _ => by
      split_ifs
      · exact (pair_top hP.1 x).2.2.2.1
      · exact le_rfl
  have h3 := le_trans h1 h2
  have h4 := (Int.cast_le (R := ℝ)).2 h3
  push_cast at h4
  convert h4 using 2 with x

theorem pfa_rho_up [NeZero r] (hP : IsPair A Ai Ci mu lam) (q : ℝ)
    (hN : ∀ i : Fin s, (∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0) ≤ q * Ai i) (i : Fin s) :
    ((pairRho mu i.val : ℤ) : ℝ) ≤ (Ai i : ℝ) * (1 + q) := by
  have h1 := pf_rho_le hP.1 i
  have h2 := pfa_prev_real hP i
  have h3 : ((pairW mu i.val : ℤ) : ℝ) ≤ (Ai i : ℝ) := by exact_mod_cast (pair_top hP.1 i).2.2.2.1
  have h4 := (Int.cast_le (R := ℝ)).2 h1
  push_cast at h4
  have h5 := hN i
  nlinarith

theorem pfa_u_low [NeZero r] (hP : IsPair A Ai Ci mu lam) (q : ℝ)
    (hN : ∀ i : Fin s, (∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0) ≤ q * Ai i) (i : Fin s) :
    -(q * (Ai i : ℝ)) ≤ ((pairO mu Ai i - pairRho mu i.val : ℤ) : ℝ) := by
  have h1 := pf_u_ge hP.1 i
  have h2 := pfa_prev_real hP i
  have h3 : (0 : ℝ) ≤ ((pairSg mu Ai i : ℤ) : ℝ) := by exact_mod_cast (pair_top hP.1 i).2.2.2.2.1
  have h4 := (Int.cast_le (R := ℝ)).2 h1
  push_cast at h4 ⊢
  have h5 := hN i
  linarith

theorem pair_first_weight_bounds (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) [NeZero r] :
    0 ≤ lam ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ ∧ lam ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ ≤ pairC mu s := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  obtain ⟨i1, i2⟩ := hP.2 ⟨0, hr0⟩
  refine ⟨le_trans ?_ i1, ?_⟩
  · have h := pfa_odd_nonneg hP hr s le_rfl
    have e : wbK mu (2 * s + 1) 0 = mu (Fin.last _) (Fin.succ ⟨0, hr0⟩) := wb_last 0 hr0
    rw [e] at h; exact h
  · have e : pairC mu s = mu (Fin.last _) (Fin.castSucc ⟨0, hr0⟩) := by
      unfold pairC; rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]; rfl
    rw [e]; exact i2

theorem pfa_n_nonneg (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : Fin s) :
    0 ≤ pairN (s := s) lam i.val := by
  unfold pairN
  rw [dif_pos (by omega)]
  have hi := i.2
  obtain ⟨i1, i2⟩ := hP.2 ⟨r - s + i.val, by omega⟩
  have hsh := wb_shape hP hr s le_rfl
  have e : mu (Fin.last _) (Fin.castSucc ⟨r - s + i.val, by omega⟩) = wbK mu (2 * s + 1) (r - s + i.val - 1) := by
    rw [wb_last (r - s + i.val - 1) (by omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.coe_castSucc]
    omega
  have hle : wbK mu (2 * s + 1) (r - s + i.val - 1) ≤ 0 := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · rw [hsh.2.1 _ (by omega) (by omega)]
    · exact hsh.2.2 _ (by omega)
  rw [e] at i2
  linarith

end PFB

def NUpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
          IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ∀ i : Fin (segS X.TT j),
            ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2)

def RestNUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restPairFacts_of (h : RestNUp) : RestPairFacts := by
  have hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        fun X hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  refine TransportedAlt.mono ?_ (hstd.and h)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc ⟨hS, hN⟩ X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP
  have St := hS X hD hI hc
  have hr : 2 * segS X.TT j + 1 ≤ X.m := by
    have h1 := (St.segB j).2
    have h2 := St.N1k
    have h3 : (2 * (X.N1 : ℝ) + 3) ≤ (X.m : ℝ) + 1 := h2
    have h4 : 2 * X.N1 + 2 ≤ X.m := by exact_mod_cast (by linarith : (2 * (X.N1 : ℝ) + 2) ≤ (X.m : ℝ))
    omega
  have hN4 := coarse_degree_prefix_sum St le_rfl j rz ry hd
  have hNq : ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤
      4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ) := fun i => by
    have := hN4 i
    rw [mul_comm, mul_div_assoc'] at *
    linarith [this, show 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 =
      (clA C0 CE1 CE2 X j rz ry i : ℝ) * 4 / (X.p : ℝ) ^ 2 by ring]
  have hl0 := pair_first_weight_bounds hP hr
  have e0 : (0 : Fin X.m) = ⟨0, Nat.pos_of_ne_zero (NeZero.ne X.m)⟩ := Fin.ext (by simp)
  refine ⟨pairC_zero hP.1, fun l => pfa_c_nonneg hP hr l, fun i => ⟨pfa_rho_nonneg hP hr i, (pf_rho_le_c hP.1 i).1,
    pfa_rho_up hP _ hNq i, ?_⟩, by rw [e0]; exact hl0.1, by rw [e0]; exact hl0.2,
    fun i => ⟨pfa_n_nonneg hP hr i, hN X hD hI hc j rz ry hd A hA1 hA2 mu lam hP i⟩⟩
  have := pfa_u_low hP _ hNq i
  have e : 4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 = 4 / (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry i : ℝ) := by ring
  rw [e]; exact this

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section Follow

variable {s r A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

theorem nu_follow (hP : IsPair A Ai Ci mu lam) (hr : s ≤ r) (i : ℕ) :
    ∀ d : ℕ, i + d < s → wbK mu (2 * i + 3) (r - 1) ≤ wbK mu (2 * (i + d) + 3) (r - 1 - d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h0 := ih (by omega)
    have hv := (wb_vstep hP (2 * (i + d) + 3) (by omega) (Or.inr (by omega))).1 (r - 1 - d) (by omega)
    have hc := (wb_cstep hP (2 * (i + d) + 4) (by omega) (by omega)).2 (r - 1 - (d + 1)) (by omega)
    have e1 : 2 * (i + d) + 3 + 1 = 2 * (i + d) + 4 := rfl
    have e2 : r - 1 - (d + 1) + 1 = r - 1 - d := by omega
    have e3 : 2 * (i + d) + 4 + 1 = 2 * (i + (d + 1)) + 3 := by ring
    rw [e1] at hv
    rw [e2, e3] at hc
    linarith

theorem nu_le_last (hP : IsPair A Ai Ci mu lam) (hr : s ≤ r) (i : ℕ) (hi : i < s) :
    pairN (s := s) lam i ≤ -wbK mu (2 * i + 3) (r - 1) := by
  have hf := nu_follow hP hr i (s - 1 - i) (by omega)
  have e : 2 * (i + (s - 1 - i)) + 3 = 2 * s + 1 := by omega
  rw [e, wb_last _ (by omega)] at hf
  have hI := (hP.2 ⟨r - 1 - (s - 1 - i), by omega⟩).1
  have e2 : (⟨r - 1 - (s - 1 - i), by omega⟩ : Fin r).succ = ⟨r - 1 - (s - 1 - i) + 1, by omega⟩ := rfl
  rw [e2] at hI
  unfold pairN
  rw [dif_pos (by omega)]
  have e3 : (⟨r - s + i, by omega⟩ : Fin r) = ⟨r - 1 - (s - 1 - i), by omega⟩ := Fin.ext (by simp; omega)
  rw [e3]
  linarith

theorem last_ge_mass (hP : IsPair A Ai Ci mu lam) (hr : 1 ≤ r) (i : ℕ) (hi : i < s) :
    -wbK mu (2 * i + 3) (r - 1) ≤ ∑ x : Fin s, if x.val < i + 1 then (Ci x : ℤ) else 0 := by
  have hm := pf_mass hP.1 (i + 1) (by omega)
  have e : (⟨2 * (i + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * i + 3, by omega⟩ := Fin.ext (by simp; omega)
  rw [e] at hm
  have hw : wbK mu (2 * i + 3) (r - 1) = mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ := by
    unfold wbK
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  rw [hw]
  have h1 : -(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ) ≤
      max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ)) := le_max_right _ _
  have h2 : max 0 (-(mu ⟨2 * i + 3, by omega⟩ (⟨r - 1, by omega⟩ : Fin r).succ)) ≤
      pfMass (fun t : Fin r => mu ⟨2 * i + 3, by omega⟩ t.succ) := by
    unfold pfMass
    exact Finset.single_le_sum (f := fun t : Fin r => max 0 (-(mu ⟨2 * i + 3, by omega⟩ t.succ)))
      (fun t _ => le_max_left _ _) (Finset.mem_univ _)
  linarith

end Follow

theorem coarse_threshold_ratio_consecutive {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry))
    (l l' : Fin (segS X.TT j)) (hll : l.val + 1 = l'.val) :
    (X.p : ℝ) ^ 2 * (clC C0 CE1 CE2 X j rz ry l : ℝ) ≤ 2 * (clC C0 CE1 CE2 X j rz ry l' : ℝ) := by
  have hm := dist_strictMono X.TT j (show l < l' from Fin.lt_def.mpr (by omega))
  have ho1 := dist_odd hs.nEven X.TT j l
  have ho2 := dist_odd hs.nEven X.TT j l'
  have hlt := (dist_pos_lt X.TT j l').2
  obtain ⟨k1, hk1⟩ := ho1
  obtain ⟨k2, hk2⟩ := ho2
  have hdd : (segDists X.TT j).get l + 2 ≤ (segDists X.TT j).get l' := by omega
  set P := X.p ^ (segG X.TT j - (segDists X.TT j).get l) with hP
  set P' := X.p ^ (segG X.TT j - (segDists X.TT j).get l') with hP'
  have hp1 : 1 ≤ X.p := by have := hs.p5; omega
  have hPP : X.p ^ 2 * P' ≤ P := by
    rw [hP, hP', ← pow_add]
    exact Nat.pow_le_pow_right hp1 (by omega)
  have hPPr : (X.p : ℝ) ^ 2 * (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPP
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := hs.levels j l
  obtain ⟨hP0', -, -, -, hPQ'⟩ := hs.levels j l'
  have cb := coarse_bounds (X.aT (segPos X.TT j l)) P (ry l) (fun c => (hd.1 l c).2) (hd.2.2 l).1 (hd.2.2 l).2
  have cb' := coarse_bounds (X.aT (segPos X.TT j l')) P' (ry l') (fun c => (hd.1 l' c).2) (hd.2.2 l').1 (hd.2.2 l').2
  have wa := hs.winA _ (pos_mem X.TT j l).1
  have wa' := hs.winA _ (pos_mem X.TT j l').1
  have hk5 := hs.k5
  have hkQ := hs.kQ hH
  have hb := hs.bpos
  have hY := hs.Y1
  have eC : (clC C0 CE1 CE2 X j rz ry l : ℝ) = (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) := rfl
  have eC' : (clC C0 CE1 CE2 X j rz ry l' : ℝ) = (((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ) := rfl
  rw [eC, eC']
  have hC0 : (0 : ℝ) ≤ (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize (((X.aT (segPos X.TT j l) - ∑ c, ry l c) / P : ℕ) : ℝ) = C at cb hC0 ⊢
  generalize (((X.aT (segPos X.TT j l') - ∑ c, ry l' c) / P' : ℕ) : ℝ) = C' at cb' ⊢
  have hkk : ((X.m : ℝ) + 1) = X.k := rfl
  rw [hkk] at cb'
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hkP : X.k * (P' : ℝ) ≤ X.b' / 25 := by
    have h1 : X.k * (P' : ℝ) ≤ X.k * X.Q := mul_le_mul_of_nonneg_left (le_trans hPQ' hQ) hk0.le
    have hQ1 := hs.Q1
    have h3 : 25 * (X.k * X.Q) ≤ X.k ^ 3 * X.Q := by
      have h25 : (25 : ℝ) ≤ X.k ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ X.Q)) (by linarith : (0:ℝ) ≤ X.k ^ 2 - 25)]
    linarith
  have ha0 : (0 : ℝ) ≤ X.a := by linarith [wa.1, (Nat.cast_nonneg _ : (0:ℝ) ≤ (X.aT (segPos X.TT j l) : ℝ))]
  have hwin : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) ≤ X.a * (7 / 5) := by
    have : 2 / (X.k * X.Y) ≤ 2 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    nlinarith
  have e1 : (X.p : ℝ) ^ 2 * C * P' ≤ X.a * (7 / 5) := by
    calc (X.p : ℝ) ^ 2 * C * P' = C * ((X.p : ℝ) ^ 2 * P') := by ring
      _ ≤ C * P := mul_le_mul_of_nonneg_left hPPr hC0
      _ ≤ _ := le_trans cb.1 (le_trans wa.2 hwin)
  have e2 : (X.a : ℝ) - X.k * P' < C' * P' := lt_of_le_of_lt (sub_le_sub_right wa'.1 _) cb'.2
  have hP'pos : (0 : ℝ) < P' := hP0'
  have hab : X.b' ≤ (X.a : ℝ) := by
    have h1 := hs.pab
    have h5 : (5 : ℝ) ≤ (X.p : ℝ) := by exact_mod_cast hs.p5
    rw [lt_div_iff₀ hb] at h1
    have h6 : (1 : ℝ) * X.b' ≤ (X.p : ℝ) * X.b' := mul_le_mul_of_nonneg_right (by linarith only [h5]) hb.le
    linarith only [h1, h6]
  have key : (X.p : ℝ) ^ 2 * C * P' ≤ 2 * C' * P' := by linarith only [e1, e2, hkP, hab]
  exact le_of_mul_le_mul_right key hP'pos

theorem coarse_threshold_prefix_sum {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) :
    ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤
      4 * (clC C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 := by
  have hp : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  intro ⟨i, hi⟩
  induction i with
  | zero =>
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero]
    positivity
  | succ i ih =>
    have ih' := ih (by omega)
    have hstep := coarse_threshold_ratio_consecutive hs hH j rz ry hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
    have e : (∑ l : Fin (segS X.TT j), if l.val < i + 1 then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) =
        (∑ l : Fin (segS X.TT j), if l.val < i then (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) +
          (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by
      have h2 : (∑ l : Fin (segS X.TT j), if l = (⟨i, by omega⟩ : Fin (segS X.TT j)) then
          (clC C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by simp
      rw [← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : l.val < i
      · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
      · by_cases h3 : l.val = i
        · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
        · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
    rw [e]
    have hC : (0 : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2 := by linarith
    rw [div_eq_mul_inv] at ih' ⊢
    have hinv : (X.p : ℝ) ^ 2 * ((X.p : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    have hinv0 : ((X.p : ℝ) ^ 2)⁻¹ ≤ 1 / 25 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp
    nlinarith [inv_pos.mpr hp0]

theorem nUp_of_std {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    NUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A _ _ mu lam hP i
  have hs := hstd X hD hI hc
  have hroom : segS X.TT j ≤ X.m := by
    have h1 := (hs.segB j).2
    have h2 := hs.N1k
    have h3 : (2 * (X.N1 : ℝ) + 3 : ℝ) ≤ (X.m : ℝ) + 1 := h2
    have : 2 * X.N1 + 3 ≤ X.m + 1 := by exact_mod_cast h3
    omega
  have hr1 : 1 ≤ X.m := by have := i.2; omega
  have h1 := nu_le_last hP hroom i.val i.2
  have h2 := last_ge_mass hP hr1 i.val i.2
  have h3 := coarse_threshold_prefix_sum hs le_rfl j rz ry hd i
  have e : (∑ x : Fin (segS X.TT j), if x.val < i.val + 1 then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) =
      (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) +
        (clC C0 CE1 CE2 X j rz ry i : ℤ) := by
    have h2 : (∑ x : Fin (segS X.TT j), if x = i then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0) =
        (clC C0 CE1 CE2 X j rz ry i : ℤ) := by simp
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : x.val < i.val
    · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
    · by_cases h3 : x.val = i.val
      · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
      · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
  rw [e] at h2
  have hcast : ((∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℤ) else 0 : ℤ) : ℝ) =
      ∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0 := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h4 : ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤
      (∑ x : Fin (segS X.TT j), if x.val < i.val then (clC C0 CE1 CE2 X j rz ry x : ℝ) else 0) +
        (clC C0 CE1 CE2 X j rz ry i : ℝ) := by
    rw [← hcast]
    exact_mod_cast le_trans h1 h2
  have hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2 := pow_pos (by exact_mod_cast (show 0 < X.p by have := hs.p5; omega)) 2
  calc ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ 4 * (clC C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 +
        (clC C0 CE1 CE2 X j rz ry i : ℝ) := by linarith
    _ = (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) := by field_simp; ring

theorem restNUp : RestNUp :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      nUp_of_std fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

end Formalism.MainNotions.ColumnSystems.Pf
end
end
