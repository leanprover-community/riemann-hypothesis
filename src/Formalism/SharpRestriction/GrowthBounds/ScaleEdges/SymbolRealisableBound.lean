import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.FramesOf
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono

section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem one_le_orbitWindowCount (r : ℕ) (de h x : ℝ) : 1 ≤ orbitWindowCount r de h x := by
  unfold orbitWindowCount
  omega

theorem rank_le_orbitWindowCount (r : ℕ) (de h x : ℝ) (hde : 0 < de) : r ≤ orbitWindowCount r de h x := by
  have hGU : r * goodU de ≤ goodG' r de h x := by
    show r * goodU de ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de)
    calc r * goodU de ≤ (6 * r + 1) * goodU de := Nat.mul_le_mul_right _ (by omega)
      _ = 1 * ((6 * r + 1) * goodU de) := (one_mul _).symm
      _ ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) := Nat.mul_le_mul_right _ (by omega)
  have hU : (1 : ℝ) ≤ (goodU de : ℝ) * de := by
    have h1 : 1 / de ≤ (goodU de : ℝ) := Nat.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right h1 hde.le
    rwa [one_div_mul_cancel hde.ne'] at h2
  have hc : (r : ℝ) * (goodU de : ℝ) ≤ (goodG' r de h x : ℝ) := by exact_mod_cast hGU
  have h3 := mul_le_mul_of_nonneg_right hc hde.le
  have h4 : (r : ℝ) ≤ r * ((goodU de : ℝ) * de) := le_mul_of_one_le_right (Nat.cast_nonneg r) hU
  have hpos : 0 ≤ (goodG' r de h x : ℝ) * de := mul_nonneg (Nat.cast_nonneg _) hde.le
  have he : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
  have h5 : (r : ℝ) ≤ 6 * Real.exp 1 * (goodG' r de h x : ℝ) * de := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * Real.exp 1 - 1) hpos]
  have h6 : (r : ℝ) ≤ max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) :=
    le_max_of_le_left h5
  have h7 : r ≤ ⌈max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x)⌉₊ := by
    exact_mod_cast le_trans h6 (Nat.le_ceil _)
  show r ≤ ⌈max (6 * Real.exp 1 * (goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x)⌉₊ + 1
  omega

structure Basic (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ : ℕ) (de h x a Y : ℝ) : Prop where
  N_pos : 1 ≤ TT.card
  two_le_a : 2 ≤ a
  one_le_depth_alt : 1 ≤ L₁
  rank_le_level : r ≤ orbitWindowCount r de h x
  depth_le_good_exponent : L₁ ≤ goodG' r de h x
  r_le_N : r ≤ TT.card
  m_ge : 6 ≤ m
  de_pos : 0 < de
  two_le_Y : 2 ≤ Y

set_option maxHeartbeats 800000 in

theorem hyps_basic {C : ℝ} (hC : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) :
    Basic p n' m r TT L₁ de h x a Y := by
  obtain ⟨hp, hr, hOrb, hNsq, _, hrY, _, hNm, hL1, _, hcS, ha⟩ := H
  obtain ⟨_, h2L, hL2U, _⟩ := hOrb
  have hN1 : 1 ≤ orbitWindowCount r de h x := one_le_orbitWindowCount r de h x
  have hU0 : 0 < ⌈1 / de⌉₊ := by
    have : 0 < goodU de := by omega
    exact this
  have hde : 0 < de := one_div_pos.mp (Nat.ceil_pos.mp hU0)
  have hrN1 : r ≤ orbitWindowCount r de h x := rank_le_orbitWindowCount r de h x hde
  have hcard : 1 ≤ TT.card := by
    rcases Nat.eq_zero_or_pos TT.card with h0 | h0
    · rw [h0, mul_zero] at hNsq
      have : 1 ≤ orbitWindowCount r de h x ^ 2 := Nat.one_le_pow _ _ hN1
      omega
    · exact h0
  have hrN : r ≤ TT.card := by
    have h1 : r * r ≤ r * TT.card := le_trans (by rw [← sq]; exact Nat.pow_le_pow_left hrN1 2) hNsq
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have hUG : goodU de ≤ goodG' r de h x := by
    show goodU de ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de)
    calc goodU de = 1 * (1 * goodU de) := by rw [one_mul, one_mul]
      _ ≤ (orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * goodU de) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
  have hY : (2 : ℝ) ≤ Y := le_trans (by exact_mod_cast hr) hrY
  have hmk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hc1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hcard
  have hk2 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [sq]
    exact one_le_mul_of_one_le_of_one_le hmk hmk
  have hL1pos : 1 ≤ L₁ := by
    by_contra hcon
    have hL0 : L₁ = 0 := by omega
    rw [hL0] at hL1
    have hz : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by norm_num
    rw [hz] at hL1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hinv : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
    have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
    have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast hp
    have hY2 : (4 : ℝ) ≤ Y ^ 2 := by
      have := mul_le_mul hY hY (by norm_num) (le_trans (by norm_num) hY)
      rw [sq]
      linarith
    have hA : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (TT.card : ℝ) := one_le_mul_of_one_le_of_one_le hk2 hc1
    have hB := mul_le_mul hA hY2 (by norm_num) (le_trans zero_le_one hA)
    have hq := mul_le_mul_of_nonneg_left hp13 hinv0
    linarith
  have hk3 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 := by
    rw [pow_succ]
    exact one_le_mul_of_one_le_of_one_le hk2 hmk
  have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have h2r : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have := mul_le_mul h2r h2r (by norm_num) (le_trans (by norm_num) h2r)
    rw [sq]
    linarith
  have hQ5 : (1 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := by
    have : 1 ≤ (p ^ goodG' r de h x) ^ 5 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by omega))
    exact_mod_cast this
  have hcs : (8 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h9 : (8 : ℝ) ≤ cStar := by exact_mod_cast (by omega : 8 ≤ cStar)
    have h10 : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  have e1 := mul_le_mul hC hk3 zero_le_one (le_trans zero_le_one hC)
  have e2 := mul_le_mul e1 hr4 (by norm_num) (le_trans (by norm_num) e1)
  have e3 := mul_le_mul e2 hc1 zero_le_one (le_trans (by norm_num) e2)
  have e4 := mul_le_mul e3 hQ5 zero_le_one (le_trans (by norm_num) e3)
  have e5 := mul_le_mul e4 hcs (by norm_num) (le_trans (by norm_num) e4)
  have e6 := mul_le_mul e5 hY (by norm_num) (le_trans (by norm_num) e5)
  have h2a : (2 : ℝ) ≤ a := le_trans (by norm_num) (le_trans e6 ha)
  exact ⟨hcard, h2a, hL1pos, hrN1, le_trans (by omega) hUG, hrN, by omega, hde, hY⟩

theorem hyps_mono {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ}
    {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C' p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) :
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar := by
  have hB := hyps_basic (le_trans hC hCC) H
  obtain ⟨hp, hr, hOrb, hNsq, hW, hrY, hLa, hNm, hL1, hDp, hcS, ha⟩ := H
  have ha2 : (2 : ℝ) ≤ a := hB.two_le_a
  have hY0 : (0 : ℝ) ≤ Y := le_trans (by norm_num) hB.two_le_Y
  have hlog : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.logb p a := Real.logb_nonneg (by exact_mod_cast (by omega : 1 < p)) (by linarith)
  have hd : 0 ≤ C' - C := by linarith
  unfold Hyps
  refine ⟨hp, hr, hOrb, hNsq, hW, hrY, le_trans ?_ hLa, hNm, hL1, le_trans ?_ hDp, hcS, le_trans ?_ ha⟩
  · unfold tableLineDegreeFive.La
    linarith [mul_nonneg hd (mul_nonneg (sq_nonneg ((orbitWindowCount r de h x : ℕ) : ℝ)) hlog)]
  · linarith [mul_nonneg hd (mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) TT.card)
      (sq_nonneg ((m + 1 : ℕ) : ℝ))) hlogb)]
  · have hX : 0 ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) * Y := mul_nonneg (by positivity) hY0
    linarith [mul_nonneg hd hX]

theorem counting_hypotheses_of_hyps {C : ℝ} (hC : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) (Ns : ℕ)
    (hNs1 : Ns ≤ orbitWindowCount r de h x) (hNs2 : Ns ≤ 2 * TT.card) :
    Formalism.CountingSumsFrames.HypII C p r TT.card (orbitWindowCount r de h x) Ns 1 (m + 1) n' L₁ (goodG' r de h x) Y a c0 cpp Dp cStar := by
  have hB := hyps_basic hC H
  obtain ⟨hp, hr, hOrb, hNsq, hW, hrY, hLa, hNm, hL1, hDp, hcS, ha⟩ := H
  have hz : ((L₁ : ℤ) - 1) = ((L₁ - 1 : ℕ) : ℤ) := by
    have := hB.one_le_depth_alt
    omega
  rw [hz, zpow_natCast] at hL1
  unfold Formalism.CountingSumsFrames.HypII
  exact ⟨hp, hr, hB.rank_le_level, hNsq, hrY, hLa, by omega, hL1, hDp, hcS, ha, hB.one_le_depth_alt, hB.depth_le_good_exponent, hNs1, hNs2,
    le_rfl, by rw [one_mul]; exact hB.r_le_N⟩

def flatDeg {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') : ℕ := (lam0 s 0 - lam0 s 1).toNat

theorem flatDeg_bounds {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    (ha : 0 ≤ a) {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (s : Fin n')
    (hs : s ∈ TT) : a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a := by
  obtain ⟨hB, _, hW3⟩ := hW
  obtain ⟨h0, _, hmid⟩ := (hB s).1 hs
  obtain ⟨hA1, hA2, _⟩ := hW3 s hs
  have hv : ((1 : Fin (m + 1)) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m + 1)
  have h1 := hmid 1 (by rw [hv]; omega) (by rw [hv]; omega)
  have hl1 := abs_le.mp h1
  have hc1 : ((lam0 s 1 : ℤ) : ℝ) ≤ cpp := by exact_mod_cast hl1.2
  have hc2 : -(cpp : ℝ) ≤ ((lam0 s 1 : ℤ) : ℝ) := by exact_mod_cast hl1.1
  have haT : ((lam0 s 0 : ℤ) : ℝ) = (aT s : ℝ) := by rw [h0]
  have hD : 0 ≤ lam0 s 0 - lam0 s 1 := by
    have : ((0 : ℤ) : ℝ) ≤ ((lam0 s 0 - lam0 s 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hcast : ((flatDeg lam0 s : ℕ) : ℝ) = ((lam0 s 0 : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by
    have e := Int.toNat_of_nonneg hD
    have e' : (((lam0 s 0 - lam0 s 1).toNat : ℤ) : ℝ) = ((lam0 s 0 - lam0 s 1 : ℤ) : ℝ) := by rw [e]
    push_cast at e'
    exact e'
  rw [hcast]
  constructor <;> linarith

section Fr

variable {n' r : ℕ} [NeZero n']

theorem fr_mono {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  obtain ⟨_, _, hmono, _⟩ := hV
  intro i hi
  induction i with
  | zero => exact le_rfl
  | succ k ih => exact le_trans (ih (by omega)) (le_of_lt (hmono j k (by omega)))

theorem Qj_le {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (j : ℤ) : Qj F p j ≤ p ^ G' := by
  obtain ⟨_, hV, hGap, _⟩ := hF
  have h1 := hGap (j + 1)
  rw [add_sub_cancel_right] at h1
  have h2 := fr_mono hV j (r - 1) (by omega)
  show p ^ (zF F (j + 1) - zF F j).toNat ≤ p ^ G'
  apply Nat.pow_le_pow_right hp
  show (F.fr (j + 1) (r - 1) - F.fr j (r - 1)).toNat ≤ G'
  omega

theorem alphaMax_le {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (k : ℕ) : alphaMax p F k ≤ 1 + r * k * p ^ G' := by
  unfold alphaMax
  apply Finset.sup_le
  intro j _
  have hQ := Qj_le hF hr p hp (j : ℤ)
  show (if (j : ℤ) = 0 then 1 else 0) + r * (k - r) * (Qj F p (j : ℤ) - 1) ≤ 1 + r * k * p ^ G'
  have h1 : (if (j : ℤ) = 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h2 : r * (k - r) * (Qj F p (j : ℤ) - 1) ≤ r * k * p ^ G' :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (le_trans (Nat.sub_le _ _) hQ)
  exact Nat.add_le_add h1 h2

theorem letters_card_le {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r}
    (hF : FramesOK TT L₁ L₂ N₁ G' F) (hG : G' ≤ n') (j : ℤ) : (F.letters j).card ≤ TT.card := by
  obtain ⟨hTT, _, hGap, _⟩ := hF
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hJ := hGap j
  apply Finset.card_le_card_of_injOn (posOf n')
  · intro x hx
    have hx : x ∈ F.letters j := hx
    have hm := (Finset.mem_filter.mp hx).2
    show posOf n' x ∈ TT
    rw [← hTT]
    exact hm
  · intro x hx y hy hxy
    have hx : x ∈ F.letters j := hx
    have hy : y ∈ F.letters j := hy
    have hx' := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
    have hy' := Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1
    have hv : (x % (n' : ℤ)).toNat % n' = (y % (n' : ℤ)).toNat % n' := congrArg Fin.val hxy
    have ex1 := Int.emod_nonneg x (ne_of_gt hn)
    have ex2 := Int.emod_lt_of_pos x hn
    have ey1 := Int.emod_nonneg y (ne_of_gt hn)
    have ey2 := Int.emod_lt_of_pos y hn
    have hx2 : (x % (n' : ℤ)).toNat % n' = (x % (n' : ℤ)).toNat := Nat.mod_eq_of_lt (by omega)
    have hy2 : (y % (n' : ℤ)).toNat % n' = (y % (n' : ℤ)).toNat := Nat.mod_eq_of_lt (by omega)
    have hm : x % (n' : ℤ) = y % (n' : ℤ) := by omega
    have hd : (n' : ℤ) ∣ y - x := Int.ModEq.dvd hm
    have h0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega

theorem dist_le {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r} (hF : FramesOK TT L₁ L₂ N₁ G' F)
    (j x : ℤ) (hx : x ∈ F.letters j) : F.dist j x ≤ G' := by
  obtain ⟨_, _, hGap, _⟩ := hF
  have hx' := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  have h1 := hGap j
  show (F.fr j (r - 1) - x).toNat ≤ G'
  omega

end Fr

def GainBoundAt (CLa Crk Cdeg : ℝ) (p n' : ℕ) [NeZero n'] (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K]
    (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ Ns mStar : ℕ) (E' : Fin n' → ℕ) (a Y Q : ℝ) : Prop :=
  let k : ℝ := ((r + K : ℕ) : ℝ)
  let La : ℝ := CLa * (Ns : ℝ) ^ 2 * Real.log a
  let Bo : ℤ → ℤ → ℝ := fun j x =>
    (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x)
  let mg : ℤ → ℤ → ℤ := fun j x => (mStar : ℤ) + (⌊Bo j x / (k ^ 2 * Y)⌋₊ : ℤ)
  let th : ℤ → ℤ → ℝ := fun j x => Bo j x / 2
  let o : ℤ → ℤ → ℝ := fun j x =>
    La * a / ((p : ℝ) * k * (p : ℝ) ^ F.dist j x) +
      (if Even x then (10 : ℝ) else 1) * a * (p : ℝ) ^ (-((L₁ : ℤ) + (F.dist j x : ℤ)))
  let d : Fin n' → ℕ := fun t => if t ∈ F.TT then deg t - E' t else 0
  let XXs : ℤ → Submodule O (SegRing O r K) := fun j => XX' O r K F j (mg j) (th j) (o j)
  let NN : Submodule O (RRing O n' (r + K)) := Submodule.span O (Gen O p K F XXs d)
  let bound : ℝ := (1 - Crk * (F.TT.card : ℝ) * (r : ℝ) ^ 2 * k / Y) *
    ∏ t ∈ F.TT, ((Nat.choose (deg t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)
  (∃ Sg : Submodule O (RRing O n' (r + K)), Sg ≤ NN ∧ (∃ T : Submodule O (RRing O n' (r + K)), IsCompl Sg T) ∧
      (∃ (ιb : Type) (b : Module.Basis ιb O Sg), ∀ i, (b i : RRing O n' (r + K)) ∈ Gen O p K F XXs d) ∧
      ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * bound ≤ (Module.finrank O Sg : ℝ) ∧
      ∀ (FF : Type) [Field FF] [Fintype FF], Fintype.card FF = p ^ n' →
        bound / (nPl FF (r + K) r : ℝ) ≤ (Module.finrank O Sg : ℝ)) ∧
  ∀ P ∈ NN, ∀ mm ∈ P.support,
    (vsDeg mm : ℝ) ≤ Cdeg * (F.TT.card : ℝ) * (La * a / ((p : ℝ) * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * Q)

def E0 (p r k N₁ G' c' : ℕ) : ℕ := 15 * c' * (N₁ + r * k) * (p ^ G') ^ 2

set_option maxHeartbeats 800000 in

theorem symbol_space_at (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C →
    ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
      [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
      (n' m r : ℕ) [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
      (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
      UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
      ∀ (K : ℕ) [NeZero r] [NeZero K], m + 1 = r + K →
      ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
      ∀ E' : Fin n' → ℕ,
        (∀ t ∈ TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) →
        GainBoundAt CLa Crk Cdeg p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) E' a Y
          ((p : ℝ) ^ goodG' r de h x) := by
  refine ⟨3041 + |Ck|, by linarith [abs_nonneg Ck], ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar
    hS H K _ _ hk F hF E' hE
  have hC1 : 1 ≤ C := by linarith [abs_nonneg Ck]
  have hB := hyps_basic hC1 H
  have hF' := hF
  obtain ⟨hp, hr, hOrb, hNsq, hW, hrY, hLa, hNm, hL1, hDp, hcS, ha⟩ := H
  obtain ⟨_, _, _, h3G⟩ := hOrb
  obtain ⟨hTT, hV, hGap, _⟩ := hF
  have hm2 : 2 ≤ m := by have := hB.m_ge; omega
  have hGn : goodG' r de h x ≤ n' := by omega
  have hG1 : 1 ≤ goodG' r de h x := le_trans hB.one_le_depth_alt hB.depth_le_good_exponent
  have ha2 : (2 : ℝ) ≤ a := hB.two_le_a
  have hY2 : (2 : ℝ) ≤ Y := hB.two_le_Y
  unfold tableLineDegreeFive.La at hLa
  rw [hk] at hLa hL1 hNm ha
  set N1 := orbitWindowCount r de h x with hN1def
  set G' := goodG' r de h x with hG'def
  set Ns := min N1 (2 * TT.card) with hNsdef
  set cp := cPrime n' r TT.card c0 cpp cStar with hcpdef
  have hNsN1 : Ns ≤ N1 := min_le_left _ _
  have hNs2 : Ns ≤ 2 * TT.card := min_le_right _ _
  refine h26 p n' W Qq O Kf ι σ j w hS hp r K hr F (flatDeg lam0) L₁ N1 Ns
    (E0 p r (r + K) N1 G' cp) (mStar p F (r + K) N1 (p ^ G') cp) E' a Y ((p : ℝ) ^ G') hV ?_ ?_ hNsN1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact flatDeg_bounds hm2 (by linarith) hW t (hTT ▸ ht)
  · intro jj
    obtain ⟨_, _, _, _, _, _, _, hlet, _⟩ := hV
    exact le_min (hlet jj) (le_trans (letters_card_le hF' hGn jj) (by omega))
  · rw [hTT]
    exact hNs2
  · omega
  · intro jj xx hxx
    have := Nat.pow_le_pow_right (by omega : p > 0) (dist_le hF' jj xx hxx)
    exact_mod_cast this
  · linarith
  · have hlog : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    have hNsq2 : (Ns : ℝ) ^ 2 ≤ (N1 : ℝ) ^ 2 := by
      have := Nat.pow_le_pow_left hNsN1 2
      exact_mod_cast this
    have s1 : Ck * ((Ns : ℝ) ^ 2 * Real.log a) ≤ |Ck| * ((Ns : ℝ) ^ 2 * Real.log a) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (sq_nonneg _) hlog)
    have s2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNsq2 hlog) (abs_nonneg Ck)
    have s3 : 0 ≤ (C - |Ck|) * ((N1 : ℝ) ^ 2 * Real.log a) :=
      mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hlog)
    linarith
  · have hNs2R : (Ns : ℝ) ≤ 2 * (TT.card : ℝ) := by exact_mod_cast hNs2
    have hq : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hNs2R hq
    linarith
  · intro t ht
    exact hE t (hTT ▸ ht)
  · have hr1 : 1 ≤ r := by omega
    have sq_level_le_degree : N1 + 3 * r ≤ r + K := by omega
    have hQ1 : 1 ≤ p ^ G' := Nat.one_le_pow _ _ (by omega)
    have hpQ : p ≤ p ^ G' := Nat.le_self_pow (by omega) p
    have hcp1 : 1 ≤ cp := le_trans (by omega : 1 ≤ cStar) (Nat.le_add_right _ _)
    have hα : alphaMax p F (r + K) ≤ 1 + r * (r + K) * p ^ G' := alphaMax_le hF' hr1 p (by omega) (r + K)
    have hrk : 1 ≤ r * (r + K) := by
      have := Nat.mul_le_mul hr1 (by omega : 1 ≤ r + K)
      simpa using this
    have b1 : cp ≤ cp * (r * (r + K) * p ^ G') := by
      have := Nat.mul_le_mul_left cp (Nat.mul_le_mul hrk hQ1)
      simpa using this
    have b2 : cp * p ^ G' ≤ cp * (r * (r + K) * p ^ G') := by
      have := Nat.mul_le_mul_right (p ^ G') hrk
      exact Nat.mul_le_mul_left cp (by simpa using this)
    have b3 : (r + K) * p ^ G' ≤ cp * (r * (r + K) * p ^ G') := by
      calc (r + K) * p ^ G' = 1 * 1 * ((r + K) * p ^ G') := by ring
        _ ≤ cp * r * ((r + K) * p ^ G') := Nat.mul_le_mul_right _ (Nat.mul_le_mul hcp1 hr1)
        _ = cp * (r * (r + K) * p ^ G') := by ring
    have hcα : cp * alphaMax p F (r + K) ≤ cp + cp * (r * (r + K) * p ^ G') := by
      have := Nat.mul_le_mul_left cp hα
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    have hinner : (2 * p ^ G' + 3) * cp + (r + K) * p ^ G' + cp * alphaMax p F (r + K) + 3 * cp ≤
        11 * (cp * (r * (r + K) * p ^ G')) := by linarith
    have hmS : mStar p F (r + K) N1 (p ^ G') cp ≤ (N1 + 1) * (11 * (cp * (r * (r + K) * p ^ G'))) := by
      show (N1 + 1) * ((2 * p ^ G' + 3) * cp + (r + K) * p ^ G' + cp * alphaMax p F (r + K) + 3 * cp) ≤ _
      exact Nat.mul_le_mul_left _ hinner
    have hNrk : N1 + r * (r + K) ≤ 2 * (r * (r + K)) := by
      have : r + K ≤ r * (r + K) := by
        have := Nat.mul_le_mul_right (r + K) hr1
        simpa using this
      linarith
    have hE0 : E0 p r (r + K) N1 G' cp ≤ 30 * (cp * (r * (r + K) * p ^ G')) * p ^ G' :=
      calc E0 p r (r + K) N1 G' cp = 15 * cp * (N1 + r * (r + K)) * (p ^ G') ^ 2 := rfl
        _ ≤ 15 * cp * (2 * (r * (r + K))) * (p ^ G') ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hNrk)
        _ = 30 * (cp * (r * (r + K) * p ^ G')) * p ^ G' := by ring
    have hB1 : 1 ≤ cp * (r * (r + K) * p ^ G') := le_trans hcp1 b1
    have hsum : E0 p r (r + K) N1 G' cp + mStar p F (r + K) N1 (p ^ G') cp + 1 ≤
        cp * (r * (r + K) * p ^ G') * (30 * p ^ G' + 11 * (N1 + 1) + 1) := by linarith
    have f1Q : Ns * p ^ G' ≤ 2 * TT.card * p ^ G' := Nat.mul_le_mul_right _ hNs2
    have f2 : Ns * N1 ≤ r * TT.card :=
      le_trans (Nat.mul_le_mul_right N1 hNsN1) (by rw [← sq]; exact hNsq)
    have g2 : r * TT.card ≤ r * TT.card * p ^ G' := by
      have := Nat.mul_le_mul_left (r * TT.card) hQ1
      simpa using this
    have g0 : TT.card ≤ r * TT.card := by
      have := Nat.mul_le_mul_right TT.card hr1
      simpa using this
    have g1 : TT.card * p ^ G' ≤ r * TT.card * p ^ G' := Nat.mul_le_mul_right _ g0
    have g3 : TT.card ≤ r * TT.card * p ^ G' := le_trans g0 g2
    have hX : Ns * (30 * p ^ G' + 11 * (N1 + 1) + 1) ≤ 95 * (r * TT.card * p ^ G') := by linarith
    have hnat : 32 * p * (r + K) ^ 2 * Ns * (p ^ G') ^ 2 *
        (E0 p r (r + K) N1 G' cp + mStar p F (r + K) N1 (p ^ G') cp + 1) ≤
        3040 * ((r + K) ^ 3 * r ^ 2 * TT.card * (p ^ G') ^ 5 * cp) := by
      calc 32 * p * (r + K) ^ 2 * Ns * (p ^ G') ^ 2 *
            (E0 p r (r + K) N1 G' cp + mStar p F (r + K) N1 (p ^ G') cp + 1)
          ≤ 32 * p ^ G' * (r + K) ^ 2 * Ns * (p ^ G') ^ 2 *
            (cp * (r * (r + K) * p ^ G') * (30 * p ^ G' + 11 * (N1 + 1) + 1)) := by gcongr
        _ = 32 * (r + K) ^ 3 * (p ^ G') ^ 4 * cp * r * (Ns * (30 * p ^ G' + 11 * (N1 + 1) + 1)) := by ring
        _ ≤ 32 * (r + K) ^ 3 * (p ^ G') ^ 4 * cp * r * (95 * (r * TT.card * p ^ G')) :=
          Nat.mul_le_mul_left _ hX
        _ = 3040 * ((r + K) ^ 3 * r ^ 2 * TT.card * (p ^ G') ^ 5 * cp) := by ring
    have hR : ((32 * p * (r + K) ^ 2 * Ns * (p ^ G') ^ 2 *
        (E0 p r (r + K) N1 G' cp + mStar p F (r + K) N1 (p ^ G') cp + 1) : ℕ) : ℝ) ≤
        ((3040 * ((r + K) ^ 3 * r ^ 2 * TT.card * (p ^ G') ^ 5 * cp) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hcpR : (cp : ℝ) = (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
      rw [hcpdef]
      unfold cPrime
      push_cast
      ring
    push_cast at hR
    rw [hcpR] at hR
    have hY0 : (0 : ℝ) ≤ Y := by linarith
    have hZ : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ G') ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hR hY0
    have h2 := mul_nonneg (mul_nonneg (by linarith [abs_nonneg Ck] : (0 : ℝ) ≤ C - 3040) hZ) hY0
    push_cast at ha h2 ⊢
    linarith

set_option maxHeartbeats 800000 in

theorem hypII_at (CLa' CD Csz : ℝ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C →
    ∀ (p n' m r : ℕ) [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
      (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
      Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
      ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
        SourceCleaning.HypII CLa' CD Csz p F (m + 1) L₁ (orbitWindowCount r de h x) (goodG' r de h x) (flatDeg lam0) ⌈a⌉₊ Y c0 0
          (cStar + 2 * r * n' * cpp) (Dp : ℝ) ∧
        cPrime n' r F.TT.card c0 0 (cStar + 2 * r * n' * cpp) = cPrime n' r TT.card c0 cpp cStar := by
  refine ⟨1 + 2 * |CLa'| + 2 * |CD| + |Csz|, by linarith [abs_nonneg CLa', abs_nonneg CD, abs_nonneg Csz], ?_⟩
  intro C hC p n' m r _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H F hF
  have hC1 : 1 ≤ C := by linarith [abs_nonneg CLa', abs_nonneg CD, abs_nonneg Csz]
  have hB := hyps_basic hC1 H
  obtain ⟨hp, hr, hOrb, hNsq, hW, hrY, hLa, hNm, hL1, hDp, hcS, ha⟩ := H
  obtain ⟨hTT, hV, hGap, _⟩ := hF
  have hm2 : 2 ≤ m := by have := hB.m_ge; omega
  have ha2 : (2 : ℝ) ≤ a := hB.two_le_a
  have hY0 : (0 : ℝ) ≤ Y := le_trans (by norm_num) hB.two_le_Y
  have hca1 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
  have hca2 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hcpos : (0 : ℝ) < (⌈a⌉₊ : ℝ) := by linarith
  have hcsq : (⌈a⌉₊ : ℝ) ≤ a ^ 2 := by
    have h2 : 2 * a ≤ a * a := mul_le_mul_of_nonneg_right ha2 (by linarith)
    rw [sq]
    linarith
  have hlog : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hlogc : Real.log (⌈a⌉₊ : ℝ) ≤ 2 * Real.log a := by
    have h3 := Real.log_le_log hcpos hcsq
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hlogc0 : 0 ≤ Real.log (⌈a⌉₊ : ℝ) := Real.log_nonneg (by linarith)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlogbc : Real.logb p (⌈a⌉₊ : ℝ) ≤ 2 * Real.logb p a := by
    unfold Real.logb
    rw [mul_div_assoc']
    gcongr
    all_goals first | exact hlp.le | exact hlogc
  have hlogb0 : 0 ≤ Real.logb p (⌈a⌉₊ : ℝ) := Real.logb_nonneg hp1 (by linarith)
  have hlogba : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
  refine ⟨?_, ?_⟩
  · unfold SourceCleaning.HypII
    dsimp only
    refine ⟨?_, ?_, ?_, hrY, ?_, hNm, ?_, ?_, ?_, ?_⟩
    · intro j
      exact le_of_lt (hGap j)
    · rw [hTT]
      exact_mod_cast hNsq
    · intro s hs
      have hs' : s ∈ TT := hTT ▸ hs
      obtain ⟨hd1, hd2⟩ := flatDeg_bounds hm2 (by linarith : (0 : ℝ) ≤ a) hW s hs'
      have hcl : ⌈a⌉₊ ≤ flatDeg lam0 s := Nat.ceil_le.mpr hd1
      have hcl' : (⌈a⌉₊ : ℝ) ≤ (flatDeg lam0 s : ℝ) := by exact_mod_cast hcl
      push_cast
      constructor <;> linarith
    · unfold tableLineDegreeFive.La at hLa
      have hT : (0 : ℝ) ≤ ((orbitWindowCount r de h x : ℕ) : ℝ) ^ 2 := sq_nonneg _
      have s1 : CLa' * (((orbitWindowCount r de h x : ℕ) : ℝ) ^ 2 * Real.log (⌈a⌉₊ : ℝ)) ≤
          |CLa'| * (((orbitWindowCount r de h x : ℕ) : ℝ) ^ 2 * Real.log (⌈a⌉₊ : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hT hlogc0)
      have s2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogc hT) (abs_nonneg CLa')
      have s4 : 0 ≤ (C - 2 * |CLa'|) * (((orbitWindowCount r de h x : ℕ) : ℝ) ^ 2 * Real.log a) :=
        mul_nonneg (by linarith [abs_nonneg CD, abs_nonneg Csz]) (mul_nonneg hT hlog)
      linarith
    · rw [hTT]
      exact hL1
    · rw [hTT]
      have hS : (0 : ℝ) ≤ (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have s1 : CD * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p (⌈a⌉₊ : ℝ)) ≤
          |CD| * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p (⌈a⌉₊ : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hS hlogb0)
      have s2 : (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p (⌈a⌉₊ : ℝ) ≤
          (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * (2 * Real.logb p a) :=
        mul_le_mul_of_nonneg_left hlogbc hS
      have s3 := mul_le_mul_of_nonneg_left s2 (abs_nonneg CD)
      have s4 : 0 ≤ (C - 2 * |CD|) * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) :=
        mul_nonneg (by linarith [abs_nonneg CLa', abs_nonneg Csz]) (mul_nonneg hS hlogba)
      linarith
    · have h8 : 8 * (Dp + 1) ≤ cStar + 2 * r * n' * cpp := le_trans hcS (Nat.le_add_right _ _)
      exact_mod_cast h8
    · rw [hTT]
      have hCsz : Csz ≤ C := by linarith [le_abs_self Csz, abs_nonneg CLa', abs_nonneg CD]
      have hX : 0 ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
          ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) * Y := mul_nonneg (by positivity) hY0
      have hh := mul_nonneg (sub_nonneg.mpr hCsz) hX
      push_cast at ha hh ⊢
      linarith
  · rw [hTT]
    unfold cPrime
    ring

end Formalism.MainNotions.Pf14
end
end

section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def vecE (n' : ℕ) : Fin n' → Bool := fun s => decide (Even s.val)

def flW {n' m : ℕ} (d : Fin n' → ℕ) : Fin n' → Fin (m + 1) → ℤ := fun s => Pi.single 0 (d s : ℤ)

theorem isFlat_flW {n' m : ℕ} (d : Fin n' → ℕ) : IsFlat (m := m) (vecE n') d (flW d) := by
  intro s
  by_cases hs : Even s.val
  · simp [lamAt, vecE, flW, hs]
  · funext i
    simp only [lamAt, vecE, flW, hs, if_false, decide_false, Bool.false_eq_true]
    by_cases hi : i = Fin.last m
    · subst hi
      simp
    · have hr : i.rev ≠ 0 := by
        intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      simp [hi, hr]


section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_shift (c : Kf) (hc : c ≠ 0) (a b : ℕ) (M : Submodule O X) {x : X}
    (hx : x ∈ scale (c ^ ((a + b : ℕ) : ℤ)) M) : (c ^ (-(a : ℤ))) • x ∈ scale (c ^ (b : ℤ)) M := by
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [smul_smul, ← zpow_add₀ hc, show -(a : ℤ) + ((a + b : ℕ) : ℤ) = b by push_cast; ring]

end Scale

def IsFlatIdent {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) [Algebra (WF p n') O] {m : ℕ} (r : ℕ)
    (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (vec : Fin n' → Bool)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0)) : Prop :=
  (∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
    InA (O := O) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ↔
    Θ F ∈ HL (O := O) ι σ lam0 (colSpan W h)) ∧
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
      ∀ (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (i : ℕ),
        InWjRg p n' O w r (flatLetters vec) g
          (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) i ↔
        Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (Re p ι σ w r lam0 e)

theorem flatSrc (hEP : EdgePlane) (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field Kf] [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (m r : ℕ) (d : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)),
      IsFlatIdent ι σ w φ r d (flW d) (vecE n') h Θ →
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ (c' o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O))
      (Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
      HasMultideg sig d → subst p n' O w n' r g (Fsig : MvPolynomial (TV n' (m + 1)) (KK O)) = sig →
      Realisable p n' w n' r g c' o sig →
      ∃ Fv : Vsp Kf (flW (m := m) d),
        Fv ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (HL (O := O) ι σ (flW d) (colSpan W h)) ∧
        Fv - Θ Fsig ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e) ∧
        ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = colSpan W h → e' ≠ e →
          Fv ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e') := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ g hg e he c' o sig Fsig hsig hsub hreal
  obtain ⟨F, hFA, hFdeg, hFW, hFo⟩ := hreal
  obtain ⟨F', rfl⟩ : ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) = F := ⟨⟨F, hFdeg d hsig⟩, rfl⟩
  have hc0 : algebraMap O Kf w ≠ 0 := w_ne_zero hS
  obtain ⟨hE1, -, hE3⟩ := hEP p n' W Qq O Kf ι σ j w hS φ hφ m r h hh
  refine ⟨(algebraMap O Kf w ^ (-(o : ℤ))) • Θ F', ?_, ?_, ?_⟩
  · exact mem_scale.mpr ⟨Θ F', (hΘ.1 F').mp hFA, rfl⟩
  · have key : InWjRg p n' O w r (flatLetters (vecE n')) g
        ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + c') := by
      show InWj w (subst p n' O w n' r g _) (o + c')
      have hx : ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) =
          (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) -
            C (algebraMap O (KK O) (w ^ o)) * (Fsig : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) := by
        rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, ← algebraMap_smul (KK O), smul_eq_C_mul]
      rw [hx, map_sub, map_mul, hsub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        MvPolynomial.algebraMap_eq]
      exact hFW
    have hmem := scale_shift (algebraMap O Kf w) hc0 o c' _ ((hΘ.2 g hg e he _ (o + c')).mp key)
    have heq : (algebraMap O Kf w ^ (-(o : ℤ))) • Θ (F' - (w ^ o) • Fsig) =
        (algebraMap O Kf w ^ (-(o : ℤ))) • Θ F' - Θ Fsig := by
      rw [map_sub, map_smul, ← algebraMap_smul Kf (w ^ o), smul_sub, smul_smul, map_pow,
        ← zpow_natCast, ← zpow_add₀ hc0, neg_add_cancel, zpow_zero, one_smul]
    rwa [heq] at hmem
  · intro e' he' hsrc hne
    obtain ⟨g', hg', hb'⟩ := hE1 e' he' hsrc
    have hrat : ratPlane p n' r g' ≠ ratPlane p n' r g := fun hr =>
      hne ((hE3 g' g e' e hg' hg hb' he).mpr hr)
    exact scale_shift (algebraMap O Kf w) hc0 o c' _
      ((hΘ.2 g' hg' e' hb' F' (o + c')).mp (hFo g' hg' hrat))

end Formalism.MainNotions.Pf14
end
end

section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def symbolSpaces (CLa : ℝ) (p n' : ℕ) [NeZero n'] (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K]
    (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ Ns mStar : ℕ) (a Y : ℝ) : ℤ → Submodule O (SegRing O r K) :=
  let k : ℝ := ((r + K : ℕ) : ℝ)
  let La : ℝ := CLa * (Ns : ℝ) ^ 2 * Real.log a
  let Bo : ℤ → ℤ → ℝ := fun j x =>
    (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x)
  let mg : ℤ → ℤ → ℤ := fun j x => (mStar : ℤ) + (⌊Bo j x / (k ^ 2 * Y)⌋₊ : ℤ)
  let th : ℤ → ℤ → ℝ := fun j x => Bo j x / 2
  let o : ℤ → ℤ → ℝ := fun j x =>
    La * a / ((p : ℝ) * k * (p : ℝ) ^ F.dist j x) +
      (if Even x then (10 : ℝ) else 1) * a * (p : ℝ) ^ (-((L₁ : ℤ) + (F.dist j x : ℤ)))
  fun j => XX' O r K F j (mg j) (th j) (o j)

def G2d {n' r : ℕ} (F : Frames n' r) (deg E' : Fin n' → ℕ) : Fin n' → ℕ :=
  fun t => if t ∈ F.TT then deg t - E' t else 0

def dT {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → ℕ :=
  fun s => if s ∈ TT then flatDeg lam0 s else 0

def restW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  lam0 - flW (dT TT lam0)

def castV {n' m r K : ℕ} (hk : m + 1 = r + K) : Fin n' × Fin (r + K) → Fin n' × Fin (m + 1) :=
  fun v => (v.1, Fin.cast hk.symm v.2)

def toK {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) P)

section Lift

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O)

def SPtrue {r k : ℕ} (F : Frames n' r) (hrk : r ≤ k) (g : Matrix (Fin k) (Fin k) (WF p n')) (c' Q : ℕ) :
    MvPolynomial (TV n' k) (KK O) :=
  (R0 p n' O F g) ^ c' * (∏ j ∈ Finset.range F.J, (Del p n' O F g j) ^ c') *
    DtopProd p n' O F hrk g ((2 * Q + 3) * c' + k * Q)

def symB {m r K : ℕ} (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (c' Q : ℕ) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  toK hk P * subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q)

def SymbolRealisableAt {m r K : ℕ} [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) : Prop :=
  ∃ E' : Fin n' → ℕ, (∀ t ∈ F.TT, E' t ≤ E₀ ∧ E' t ≤ deg t) ∧
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ P ∈ Gen O p K F XXs (G2d F deg E'), ∀ T : ℕ, (∀ mm ∈ P.support, vsDeg mm ≤ T) →
      ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') (m + 1) dTop).restrictScalars O),
        (∀ o, HasMultideg (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' (m + 1)) (KK O))) dTop ∧
          InWj w (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' (m + 1)) (KK O))) 0 ∧
          Realisable p n' w n' r g c' o (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' (m + 1)) (KK O)))) ∧
        ∑ o ∈ Finset.range (T + 1), subst p n' O w n' r g (Fs o : MvPolynomial (TV n' (m + 1)) (KK O)) =
          symB p n' O w hk hrk F g c' Q P

end Lift

def CloudAt (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Algebra (WF p n') O]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) {m r : ℕ}
    (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cStar c0 : ℕ) (a bS bT bD : ℝ)
    (e : Edge W Qq (m + 1)) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
    IsFlatIdent ι σ w φ r (dT TT lam0) (flW (dT TT lam0)) (vecE n') h Θ ∧
    ∃ (n2 oS tT D1 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
      (oS : ℝ) ≤ bS ∧ (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
      (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e ∧
        sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ (restW TT lam0) e.src)) ∧
      (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (dimV Kf lam0 : ℝ) ≤
        (∏ t ∈ TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ)) * n2 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

def SymbolRealisableBound (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    letI : Algebra (WF p n') O := algOfIdent j φ
    SymbolRealisableAt p n' O w hk hrk F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
      (flatDeg lam0) (dT TT lam0) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
      (E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar))

def CloudStep (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      CloudAt p n' ι σ w φ (r := r) TT lam0 cStar c0 a (om r TT.card n' c0 cpp)
        (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp)
        (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e hm FsB

def SourcesRealisable (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → SymbolRealisableBound C CLa

def RestCloud (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudStep C Ct0 CD1 CLa

end Formalism.MainNotions.Pf14
end
end
