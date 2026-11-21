import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeNeedPrice
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def PriceBoundLargePrimes (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      L.sc.p0 D.R.k ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

def PriceBoundSmallPrimes : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem priceBound_of_largePrimes_of_smallPrimes (C₀ : ℝ) (h1 : PriceBoundLargePrimes C₀) (h2 : PriceBoundSmallPrimes) : PriceBound C₀ := by
  intro D L X Y K hK1 hK2 hS hT hL u w hg _ t0 ht0 j hj
  rcases le_or_gt (L.sc.p0 D.R.k) ((D.what₂.places.resChar w : ℕ) : ℝ) with h | h
  · exact h1 D L X Y K hK1 hS hT hL u w hg h t0 ht0 j hj
  · exact h2 D L X Y K hK2 hS hT hL u w hg h t0 ht0 j hj

variable {n' k1 : ℕ}

theorem ne_abs (t r j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A Bt : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bt)
    (h : ∀ s : Fin n', IsOddPos s → (r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      A + (if s ∈ TT then Bt else 0)) :
    Pr t r lam0 w j ≤ n' * A + TT.card * Bt + (n' : ℝ) * r * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  have h2 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) ≤
      ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by split_ifs <;> linarith)
  have h3 : ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) = n' * A + TT.card * Bt := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith

theorem price_sum_single_edge (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A : ℝ) (E : Fin n' → ℝ) (hA : 0 ≤ A)
    (h : ∀ s : Fin n', IsOddPos s → ((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      if s ∈ TT then E s else A) :
    Pr t 1 lam0 w j ≤ ∑ s ∈ TT.filter IsOddPos, E s + n' * A + (n' : ℝ) * ((1 : ℕ) : ℝ) * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      (((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (if s ∈ TT then E s else A) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  rw [Finset.sum_ite] at h1
  have e1 : (univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∈ TT) = TT.filter IsOddPos := by
    ext s; simp [and_comm]
  rw [e1, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT)).card : ℝ) ≤ n' := by
    have := Finset.card_le_univ ((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 hA
  exact add_le_add (le_trans h1 (add_le_add le_rfl h3)) le_rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_lamI_last (s : Fin (G.P.n' v)) : lamI (G.P.lam0 v) s (G.P.m + 1) = G.P.lam0 v s (Fin.last G.P.m) := by
  unfold lamI
  rw [dif_pos ⟨by omega, le_rfl⟩]
  rfl

theorem ne_lamI_le (s : Fin (G.P.n' v)) (a : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    lamI (G.P.lam0 v) s a ≤ (Fl.c : ℤ) + (if s ∈ Fl.TT v ∧ a = 1 then Fl.a v s else 0) := by
  have hc : (0 : ℤ) ≤ Fl.c := Int.natCast_nonneg _
  unfold lamI
  by_cases h : 1 ≤ a ∧ a ≤ G.P.m + 1
  · rw [dif_pos h]
    by_cases hs : s ∈ Fl.TT v
    · obtain ⟨h1, h2, h3⟩ := (Fl.base v s).1 hs
      by_cases ha : a = 1
      · subst ha
        rw [if_pos ⟨hs, rfl⟩]
        have : G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s := h1
        omega
      · rw [if_neg (fun h' => ha h'.2)]
        by_cases hl : a = G.P.m + 1
        · subst hl
          have : G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s := h2
          have := hb hs
          omega
        · have := (abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2
          omega
    · rw [if_neg (fun h' => hs h'.1)]
      have := (abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2
      omega
  · rw [dif_neg h, if_neg (fun h' => h ⟨by omega, by omega⟩)]
    omega

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_kaJ_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
  unfold Formalism.MainNotions.G.kaJ
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

theorem ne_w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  exact div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in

theorem ne_w_non (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ L.sc.w'' D.R.n + L.etaSz := by
  obtain ⟨_, h2, _, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT := fun h => hs (h2.2 h)
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_neg (fun h => hn h.2)]
  have h5 := (X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))
    ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in

theorem ne_w_top (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) + L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨_, h2, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj, (h3 hs).2]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := h2.1 hs
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_pos ⟨rfl, hn⟩]
  have h5 := (X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in
theorem ne_nP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
  unfold Formalism.MainNotions.G.nP
  rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]

theorem ne_Nm (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 ≤ Formalism.MainNotions.G.Nm D := by
  unfold Formalism.MainNotions.G.Nm Ranks.N
  have h1 : (j : ℝ) ≤ D.R.m := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have h2 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1),
    mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]

end Orbit

open Classical in

theorem price_bound_large_primes : PriceBoundLargePrimes 1 := by
  intro D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj
  have hr : (D.gat u w hg).P.r = 1 := by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L := by
    have := ne_w''_nonneg (L := L)
    have := L.etaSz_pos
    have := nc_cG_nonneg (L := L)
    linarith
  rw [hr]
  have h1 := price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L)
    (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) hA
    (fun s _ => by
      have e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1 := rfl
      rw [e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]
      split_ifs with hs
      · rw [((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]
        push_cast
        linarith
      · have h2 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h3 := (abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2
        have h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := by
          exact_mod_cast h3
        push_cast
        linarith)
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr
  rw [if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf, ne_nP X Y hT hL u w hg t0 ht0, ht]
  have e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
      (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) =
      ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
        (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, nc_iota Y u w hg t0 s) -
          (Formalism.MainNotions.G.bL L (nc_iota Y u w hg t0 s) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨_, _, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
    rw [h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]
  rw [e1]
  have hN := ne_Nm (D := D) j hj
  have hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := Nat.cast_nonneg _
  have hNm : 0 ≤ Formalism.MainNotions.G.Nm D := le_trans (by positivity) hN
  have h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤
      K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) *
        (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) := by
    have := mul_le_mul_of_nonneg_right hK
      (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))
    linarith
  have h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D := by
    have := mul_le_mul_of_nonneg_left hN hn
    push_cast
    linarith
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_sum_le (s : Fin (G.P.n' v)) (r : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      r * Fl.c + (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
  have h1 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), ((Fl.c : ℝ) + (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0)) := by
    apply Finset.sum_le_sum
    intro a _
    have := ne_lamI_le Fl v s a hm hb
    by_cases hc : s ∈ Fl.TT v ∧ a = 1
    · rw [if_pos hc] at this ⊢
      exact_mod_cast this
    · rw [if_neg hc] at this ⊢
      exact_mod_cast this
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Icc (G.P.m + 2 - r) (G.P.m + 1)).card : ℝ) ≤ r := by
    rw [Nat.card_Icc]
    have : G.P.m + 1 + 1 - (G.P.m + 2 - r) ≤ r := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg Fl.c : (0 : ℝ) ≤ Fl.c)
  have h4 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0) =
      (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
    by_cases hs : s ∈ Fl.TT v
    · simp only [hs, true_and]
      rw [Finset.sum_ite_eq' (Icc (G.P.m + 2 - r) (G.P.m + 1)) 1 (fun _ => (Fl.a v s : ℝ))]
      have : (1 ∈ Icc (G.P.m + 2 - r) (G.P.m + 1)) ↔ G.P.m + 1 ≤ r := by
        rw [Finset.mem_Icc]; omega
      simp only [this]
    · simp [hs]
  rw [h4] at h1
  linarith

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def ne_CX : ℝ := Real.exp (Real.exp (34 / 3))

theorem ne_k_pos : (1 : ℝ) ≤ D.R.k := by
  have h2 := D.R.m_add_three_le_k
  have : 1 ≤ D.R.k := by omega
  exact_mod_cast this


theorem ne_bT_le (hS : Formalism.MainNotions.SizesAt L) (t) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hLa := hS.2.2.2.2.2.2.2.2.1
  have hRho := hS.2.2.2.2.2.2.2.2.2.1
  have hBot := hS.2.2.2.2.2.2.2.2.2.2.1 t
  unfold Formalism.MainNotions.SizeRho at hRho
  have hk := ne_k_pos (D := D)
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg L.sc.x_pos.le _) hLa.1
  have h1 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg L.sc.x_pos.le _) (Real.log_nonneg hx.le)) hLa0) (by linarith)
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h3 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h5 := mul_le_mul_of_nonneg_right h3 L.sc.b'_pos.le
  linarith

theorem ne_aT_le (t) : (L.aT t : ℝ) ≤ 2 * L.sc.a := by
  have h1 := (L.aT_win t).2
  have hk := ne_k_pos (D := D)
  have hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self L.sc.a_pos.le (by nlinarith)
  linarith


end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

theorem price_linear_combination_le (n N rr w2 η cg NM b1 jt : ℝ) (hn : 0 ≤ n) (hN : 0 ≤ N) (hr : 0 ≤ rr) (hcg : 0 ≤ cg) (hjt : jt ≤ NM) :
    n * (rr * (w2 + η + cg)) + N * (rr * (2 * b1)) + n * rr * jt ≤
      rr * (N * (2 * b1 + cg) + n * (w2 + η + cg + NM)) := by
  nlinarith [mul_nonneg (mul_nonneg hr hN) hcg, mul_nonneg (mul_nonneg hn hr) (sub_nonneg.mpr hjt)]

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem ne_b_top (hS : Formalism.MainNotions.SizesAt L) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    L.sc.b' ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ∧
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).2]
  unfold Formalism.MainNotions.G.bL
  rw [dif_pos (h2.1 hs)]
  exact ⟨L.bT_ge _, ne_bT_le hS _⟩

include hL ht0 in
theorem ne_a_top (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).a (Y.vOf u w hg t0) s : ℝ) ≤ 2 * L.sc.a := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).1]
  unfold Formalism.MainNotions.G.aL
  rw [dif_pos (h2.1 hs)]
  exact ne_aT_le _

end Orbit


def priceThreshold : ℝ := 9

theorem price_threshold_ge_nine : 9 ≤ priceThreshold := by norm_num [priceThreshold]

open Classical in

theorem price_bound_small_primes : PriceBoundSmallPrimes := by
  intro D L X Y K hK hS hT hL u w hg hp t0 ht0 j hj
  obtain ⟨hrk, hx2⟩ := hK
  have hr : (D.gat u w hg).P.r = Formalism.MainNotions.G.rG L.sc := by rw [(hL u w hg).2.2.2.1, if_pos hp]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hm := nc_m_ge hT u w hg
  have hk := hT.gat_k u w hg
  have hno : ¬ ((D.gat u w hg).P.m + 1 ≤ Formalism.MainNotions.G.rG L.sc) := by omega
  have hr0 : (0 : ℝ) ≤ (Formalism.MainNotions.G.rG L.sc : ℝ) := Nat.cast_nonneg _
  have hw := ne_w''_nonneg (L := L)
  have hη := L.etaSz_pos
  have hcG := nc_cG_nonneg (L := L)
  have hb' := L.sc.b'_pos
  rw [hr]
  have h1 := ne_abs (Y.Fl u w hg).t (Formalism.MainNotions.G.rG L.sc) j ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
    ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (2 * L.sc.b'))
    (by positivity) (by positivity)
    (fun s _ => by
      have hsum := ne_sum_le (Y.Fl u w hg) (Y.vOf u w hg t0) s (Formalism.MainNotions.G.rG L.sc) hm (fun hs => by
        have h0 := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).1
        have : (0 : ℝ) ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) := by linarith
        exact_mod_cast this)
      rw [if_neg (fun h => hno h.2)] at hsum
      have h7 := mul_le_mul_of_nonneg_left hc hr0
      have h11 := mul_nonneg hr0 hw
      by_cases hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
      · rw [if_pos hs]
        have hwt := ne_w_top X Y hT hL u w hg t0 ht0 j hj s hs
        have hb := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).2
        have hx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx2
        have h5 := mul_le_mul_of_nonneg_left
          (show ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 2 * L.sc.b' + L.etaSz by linarith) hr0
        nlinarith [h5, h7, hsum, h11]
      · rw [if_neg hs]
        have hwn := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h5 := mul_le_mul_of_nonneg_left hwn hr0
        nlinarith [h5, h7, hsum])
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr Formalism.MainNotions.G.Nv
  rw [if_neg (not_le.2 hp), nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj,
    ne_nP X Y hT hL u w hg t0 ht0, ht]
  have hN := ne_Nm (D := D) j hj
  have hfin := price_linear_combination_le ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ)
    (Formalism.MainNotions.G.rG L.sc : ℝ) (L.sc.w'' D.R.n) L.etaSz (Formalism.MainNotions.G.cG L) (Formalism.MainNotions.G.Nm D) L.sc.b'
    ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr0 hcG hN
  have e : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 =
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) := by ring
  rw [e]
  exact hfin

theorem priceBoundLargePrimes_priceThreshold : PriceBoundLargePrimes priceThreshold :=
  fun D L X Y K hK => price_bound_large_primes D L X Y K (by linarith [price_threshold_ge_nine])

theorem ne_priceThreshold : PriceBound priceThreshold :=
  priceBound_of_largePrimes_of_smallPrimes priceThreshold priceBoundLargePrimes_priceThreshold price_bound_small_primes


theorem numericalComparisonUniform_of_size (hS : nd_NeedSize) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_threshold priceThreshold price_threshold_ge_nine (nc_need3_of priceThreshold hS ne_priceThreshold)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem nd_al_le (s : Fin (G.P.n' v)) (hs : s ∈ Fl.TT v) (hm : 2 ≤ G.P.m) :
    al (Fl.TT v) (G.P.lam0 v) s ≤ Fl.a v s + (Fl.c : ℤ) := by
  unfold al
  rw [if_pos hs, lambda_index_one v s hm, lambda_index_two v s hm]
  have hb := (Fl.base v s).1 hs
  have := (abs_le.1 (hb.2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).1
  have h0 : G.P.lam0 v s ⟨0, by omega⟩ = Fl.a v s := hb.1
  omega

theorem nd_c_le_w (s : Fin (G.P.n' v)) (l : ℕ) (hl : 1 ≤ l) : (Fl.c : ℤ) ≤ Fl.w v l s :=
  le_trans (le_trans (le_max_left _ _) (Fl.w_ge v s)) (nc_w_ge Fl v s l hl)

theorem nd_lam_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ G.P.m + 1)
    (h : s ∈ Fl.TT v → 2 ≤ i) : lamI (G.P.lam0 v) s i ≤ (Fl.c : ℤ) := by
  unfold lamI
  rw [dif_pos ⟨h1, h2⟩]
  have hb := Fl.base v s
  by_cases hs : s ∈ Fl.TT v
  · have h3 := (abs_le.1 ((hb.1 hs).2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).2
    have hd : Antitone (G.P.lam0 v s) := G.P.dom v s
    have h4 := hd (show (⟨1, by omega⟩ : Fin (G.P.m + 1)) ≤ ⟨i - 1, by omega⟩ by
      rw [Fin.le_def]; have := h hs; simp only; omega)
    omega
  · exact (abs_le.1 (hb.2 hs _)).2

theorem nd_lsz_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (j : ℕ) (hj : 1 ≤ j) :
    lsz Fl.t (Fl.TT v) (G.P.lam0 v) (Fl.w v) j s ≤ (NN G.P.m Fl.t j : ℤ) * ((Fl.c : ℤ) + Fl.w v j s) := by
  unfold lsz
  have h1N : 1 ∈ Icc 1 (NN G.P.m Fl.t j) := Finset.mem_Icc.2 ⟨le_rfl, by unfold NN; omega⟩
  have e : ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - al (Fl.TT v) (G.P.lam0 v) s =
      ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' _ 1, if_pos h1N]
  rw [e]
  have hb : ∀ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) ≤ (Fl.c : ℤ) + Fl.w v j s := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold nu
    by_cases hik : i ≤ G.P.m + 1
    · rw [if_pos ⟨hi.1, hik⟩]
      by_cases hi1 : i = 1
      · subst hi1
        rw [if_pos rfl]
        unfold al
        by_cases hs : s ∈ Fl.TT v
        · rw [if_pos hs]
          have := nd_lam_le Fl v s hm 2 (by omega) (by omega) (fun _ => le_rfl)
          omega
        · rw [if_neg hs]
          have := nd_lam_le Fl v s hm 1 le_rfl (by omega) (fun h => absurd h hs)
          omega
      · rw [if_neg hi1]
        have := nd_lam_le Fl v s hm i hi.1 hik (fun _ => by omega)
        omega
    · rw [if_neg (fun h => hik h.2), if_pos ⟨by omega, hi.2⟩, if_neg (by omega)]
      have := nd_c_le_w Fl v s ((i - (G.P.m + 2)) / (Fl.t + 1) + 1) (Nat.le_add_left 1 _)
      have hc : (0 : ℤ) ≤ (Fl.c : ℤ) := Int.natCast_nonneg _
      omega
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
  simpa using this

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nd_x_ge : (1 : ℝ) ≤ L.sc.x := le_of_lt L.sc.one_lt_alt

theorem nd_b'_nonneg : 0 ≤ L.sc.b' := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  unfold Scale.b' Scale.a Scale.X' Scale.b
  exact div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le

theorem nd_b'_le : L.sc.b' ≤ L.sc.a := by
  have hx : (1 : ℝ) < L.sc.x := L.sc.one_lt_alt
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  unfold Scale.b'
  apply div_le_self ha
  unfold Scale.X'
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem nd_n_ge : (1 : ℝ) ≤ (D.R.n : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 : 1 ≤ D.R.n := by unfold Ranks.n; omega
  exact_mod_cast h3

theorem nd_w''_le : L.sc.w'' D.R.n ≤ L.sc.b' := by
  unfold Scale.w''
  exact div_le_self nd_b'_nonneg (one_le_mul_of_one_le_of_one_le nd_x_ge nd_n_ge)

theorem nd_m_ge : (2 : ℝ) ≤ (D.R.m : ℝ) := by
  exact_mod_cast D.R.two_le_m

theorem nd_k_ge : (5 : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have h3 : 5 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem nd_eta_le (hS : Formalism.MainNotions.SizesAt L) : L.etaSz ≤ L.sc.a := by
  unfold Formalism.MainNotions.SizesAt at hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS
  unfold Formalism.MainNotions.SizeEta at hE
  have h2 := hE.2.1
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.rank_add_five_le
    have h : 1 ≤ D.R.t := by omega
    exact_mod_cast h
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    have h : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
    exact_mod_cast h
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hd : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf) (one_le_pow₀ hk)
  calc L.etaSz ≤ _ := h2
    _ ≤ L.sc.b := div_le_self hb hd
    _ ≤ L.sc.a := by unfold Scale.a; exact le_mul_of_one_le_left hb hx

theorem nd_Sc_le (hS : Formalism.MainNotions.SizesAt L) : 4 * L.Sc ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := nd_n_ge
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := nd_m_ge
  have hb' : 0 ≤ L.sc.b' := nd_b'_nonneg
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    exact div_nonneg hb' (mul_nonneg hx0.le (by positivity))
  have heta : 0 ≤ L.etaSz := le_trans (by positivity) h1
  have hSc : 0 < L.Sc := L.Sc_pos
  have hL : L.sc.L ≤ L.sc.x := by
    unfold Scale.L
    calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith [L.sc.eps_lt])
      _ = L.sc.x := Real.rpow_one _
  have hwx : L.sc.w'' D.R.n * L.sc.x ≤ L.sc.b' := by
    unfold Scale.w''
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hx0 (by linarith))]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx0.le hn) hb'
  have hX : 2 ≤ L.sc.X' := by
    unfold Scale.X'
    have h1' : (1 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx (by linarith [L.sc.eps_pos])
    linarith [Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))]
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg hx0.le (Real.exp_pos _).le
  have hb'a : 2 * L.sc.b' ≤ L.sc.a := by
    unfold Scale.b'
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hX ha]
  linarith [mul_le_mul_of_nonneg_left hL hw0, mul_le_mul_of_nonneg_right hm (add_nonneg hSc.le heta)]

theorem nd_bT_le (hS : Formalism.MainNotions.SizesAt L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨hN, -, hK, -, -, -, -, -, hLa, -, hBot, -⟩ := hS'
  unfold Formalism.MainNotions.SizeN at hN
  unfold Formalism.MainNotions.SizeK at hK
  unfold Formalism.MainNotions.SizeLa at hLa
  unfold Formalism.MainNotions.SizeBot at hBot
  have hb := hBot t
  unfold Formalism.MainNotions.szNst at hb
  unfold Formalism.MainNotions.szTh at hN hK hLa
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hLa0 : 0 ≤ L.LaG := le_trans hxe0 hLa.1
  have hn0 : (0 : ℝ) ≤ (D.R.n : ℝ) := by positivity
  have hkey : (D.R.n : ℝ) * L.sc.x ^ L.sc.eps * L.LaG ≤ (D.R.k : ℝ) := by
    calc (D.R.n : ℝ) * L.sc.x ^ L.sc.eps * L.LaG
        ≤ L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ L.sc.eps *
            L.sc.x ^ (L.sc.eps + L.sc.eps / 100) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hN.2 hxe0) hLa.2 hLa0
            (mul_nonneg (Real.rpow_nonneg hx0.le _) hxe0)
      _ = L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100 + L.sc.eps + (L.sc.eps + L.sc.eps / 100)) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - L.sc.eps / 100) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ (D.R.k : ℝ) := hK.1
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hd0 : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg hx0.le _
  have hb' : 0 ≤ L.sc.b' := nd_b'_nonneg
  have hE : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      2 * L.sc.b' := by
    rw [div_le_iff₀ hk0]
    nlinarith [mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0) hb'),
      mul_le_mul_of_nonneg_right hd1 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb') hk0.le)]
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg hx0.le (Real.exp_pos _).le
  have hX : 12 / 5 ≤ L.sc.X' := by
    unfold Scale.X'
    have h1' : (1 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx (by linarith)
    first
    | nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ L.sc.x ^ (L.sc.eps / 3) by linarith)]
    | (have h2' := Real.exp_le_exp.mpr h1'; have h3' := Real.exp_one_gt_d9; linarith)
  have hb'a : 3 * L.sc.b' ≤ 5 / 4 * L.sc.a := by
    unfold Scale.b'
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hX ha]
  linarith

theorem nd_aT_le (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.a := by
  have hw := (L.aT_win t).2
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a Scale.b
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by have := nd_k_ge (D := D); linarith
  have hp : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx (by unfold Scale.A; norm_num)
  have hd : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self ha (one_le_mul_of_one_le_of_one_le hk hp)
  linarith

theorem nd_N_le (hS : Formalism.MainNotions.SizesAt L) : (D.R.N D.R.m : ℝ) ≤ L.sc.a := by
  have hS' := hS
  unfold Formalism.MainNotions.SizesAt at hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := hS'
  unfold Formalism.MainNotions.SizeEta at hE
  obtain ⟨h1, h2, -⟩ := hE
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hmf := D.R.m_le_f
  have htr := D.R.rank_add_five_le
  have hf : 2 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
  have ht : 1 ≤ D.R.t := by omega
  have hk : 5 ≤ D.R.k := by omega
  have hNn : D.R.N D.R.m ≤ D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by
    have e1 : D.R.m * (D.R.t + 1) ≤ D.R.k * (D.R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    have e2 : D.R.k * (D.R.t + 2) ≤ D.R.k * (3 * D.R.t) := Nat.mul_le_mul_left _ (by omega)
    have e3 : 3 ≤ D.R.f * D.R.k ^ 2 := by nlinarith
    have e4 : D.R.t * 3 ≤ D.R.t ^ 3 * (D.R.f * D.R.k ^ 2) :=
      Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) e3
    unfold Ranks.N
    calc D.R.k + D.R.m * (D.R.t + 1) ≤ D.R.k * (D.R.t + 2) := by nlinarith [e1]
      _ ≤ D.R.k * (3 * D.R.t) := e2
      _ = D.R.k * (D.R.t * 3) := by ring
      _ ≤ D.R.k * (D.R.t ^ 3 * (D.R.f * D.R.k ^ 2)) := Nat.mul_le_mul_left _ e4
      _ = D.R.t ^ 3 * D.R.f * D.R.k ^ 3 := by ring
  have hNr : (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by exact_mod_cast hNn
  have ht0 : (0 : ℝ) < D.R.t := by exact_mod_cast (show 0 < D.R.t by omega)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (show 0 < D.R.k by omega)
  have hdpos : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    mul_pos (mul_pos (pow_pos ht0 3) hf0) (pow_pos hk0 3)
  have ht1 : (1 : ℝ) ≤ L.etaSz := le_trans (by exact_mod_cast ht) h1
  have hde : (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz ≤ L.sc.b := by
    rw [le_div_iff₀ hdpos] at h2
    linarith
  calc (D.R.N D.R.m : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := hNr
    _ ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 * L.etaSz := le_mul_of_one_le_right hdpos.le ht1
    _ ≤ L.sc.b := hde
    _ ≤ L.sc.a := by unfold Scale.a; exact le_mul_of_one_le_left hb hx

theorem nd_fill_le (X : Formalism.MainNotions.G.Inst D L) (hS : Formalism.MainNotions.SizesAt L) (j : ℕ) (hj : 1 ≤ j) (t : Formalism.MainNotions.G.HH D) :
    Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) ≤ 4 * L.sc.a := by
  have hx : (1 : ℝ) ≤ L.sc.x := nd_x_ge
  have hb'a : L.sc.b' ≤ L.sc.a := nd_b'_le
  have hb'0 : 0 ≤ L.sc.b' := nd_b'_nonneg
  have heta : L.etaSz ≤ L.sc.a := nd_eta_le hS
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' := nd_w''_le
  have hka : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
    unfold Formalism.MainNotions.G.kaJ
    have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
    apply div_nonneg _ (by norm_num)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (j : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  dsimp only
  split_ifs with hc
  · have ht : t ∈ D.host.TT := hc.2
    have htop : Formalism.MainNotions.G.IsTopPl D (false, t) := by
      unfold Formalism.MainNotions.G.IsTopPl
      exact ⟨rfl, ht⟩
    have ho := (X.off_top j (false, t) htop).2
    have hbl : ((Formalism.MainNotions.G.bL L t : ℤ) : ℝ) ≤ 5 / 4 * L.sc.a := by
      unfold Formalism.MainNotions.G.bL
      rw [dif_pos ht]
      exact nd_bT_le hS ⟨t, ht⟩
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx
    linarith
  · have hthin : Formalism.MainNotions.G.IsThinPl D (false, t) := by
      unfold Formalism.MainNotions.G.IsThinPl Formalism.MainNotions.G.IsTopPl Formalism.MainNotions.G.IsThickPl
      dsimp only
      exact ⟨fun h => hc ⟨rfl, h.2⟩, fun h => Bool.false_ne_true h.1⟩
    have ho := (X.off_thin j (false, t) hthin).2
    linarith

theorem nd_size : nd_NeedSize := by
  intro D L X Y hS hT hL u w hg _ t0 ht0 j hj
  have hm := nc_m_ge hT u w hg
  obtain ⟨_, ht, hc, _, _, _, hloc⟩ := hL u w hg
  obtain ⟨_, hs⟩ := hloc t0 ht0
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have ha := nc_a_ge (L := L)
  have hc' : ((Y.Fl u w hg).c : ℝ) ≤ L.sc.a := le_trans hc (by unfold Formalism.MainNotions.G.cG; exact nd_Sc_le hS)
  refine ⟨fun s => ?_, fun s => ?_⟩
  · by_cases hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
    · obtain ⟨_, hTT, hab, _⟩ := hs s
      have h1 := nd_al_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hsT hm
      have h2 := (hab hsT).1
      have h3 : (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤
          (((Y.Fl u w hg).a (Y.vOf u w hg t0) s + ((Y.Fl u w hg).c : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2] at h3
      push_cast at h3
      have h4 : (Formalism.MainNotions.G.aL L (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) : ℝ) ≤ 2 * L.sc.a := by
        unfold Formalism.MainNotions.G.aL
        rw [dif_pos (hTT.1 hsT)]
        exact nd_aT_le _
      nlinarith
    · unfold al
      rw [if_neg hsT]
      push_cast
      positivity
  · obtain ⟨_, _, _, hw⟩ := hs s
    have h1 := nd_lsz_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hm j hj1
    have h2 : (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
        ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤
        (((NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℤ) *
          (((Y.Fl u w hg).c : ℤ) + (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hk := hT.gat_k u w hg
    have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      unfold NN Ranks.N
      rw [ht]
      have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
        rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
      exact_mod_cast this
    have hN := le_trans hN1 (nd_N_le hS)
    have hw1 : ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 4 * L.sc.a := by
      rw [hw j hj]; exact nd_fill_le X hS j hj1 _
    have hw0 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by
      have h5 := nd_c_le_w (Y.Fl u w hg) (Y.vOf u w hg t0) s j hj1
      have h6 : (((Y.Fl u w hg).c : ℤ) : ℝ) ≤ ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := Nat.cast_nonneg _
      push_cast at h6
      linarith
    have h8 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) *
        (((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)) ≤ L.sc.a * (5 * L.sc.a) :=
      mul_le_mul hN (by linarith) hw0 (by linarith)
    have h9 : L.sc.a * (5 * L.sc.a) ≤ (2 * L.sc.a) ^ 4 := by
      have : 1 ≤ L.sc.a ^ 2 := by nlinarith
      nlinarith [sq_nonneg (L.sc.a ^ 2)]
    linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
namespace Formalism.MainNotions.FormalGroupSystem.Pf

theorem stmtNumE : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform := numericalComparisonUniform_of_size nd_size

end Formalism.MainNotions.FormalGroupSystem.Pf
end
