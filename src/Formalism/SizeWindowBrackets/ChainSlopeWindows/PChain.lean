import Formalism.SizeWindowBrackets.SChain
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr


theorem small_costs_split : SmallCostsSplit := by
  intro x ε f b η θ Cd CL
  exact Iff.rfl

theorem size_windows_split : SizeWindowsSplit := by
  intro C ε x n nT nT2 m b k aE Err
  unfold SizeWindows RestSize errorBracketSizeWindows
  tauto

theorem chain_top_bound : ChainTop := by
  rintro Cd eD eL ε x ⟨K, cHH, eK, CL, hCore, hx3, h26, hLX, hMove⟩
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩ := hCore
  subst hx hε
  obtain ⟨j1, j2, j3, j4, j5⟩ := hId
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC

  have hLX' : LargeX Dd.x Dd.ε K C.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)

  have hTop : topExcess D N ell TT a w ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a :=
    joint_error_bound (H := H) top_from_weighted_mean Dd C Xpp eK K D N ell TT T2 a w eT eP
      (uniform_bound_statement Dd C Xpp) l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 hWin hLX' hBN.1 hBN.2 j1 j2 j3 j4 j5
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := l1.2.2.1
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr C * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hTop' := le_trans hTop (mul_le_mul_of_nonneg_right hExp hBr)
  obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8⟩, r9, r10⟩ := hRest
  refine ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, Dd.b, Dd.b', η, X', θ, CL,
    Dd.x ^ ((eD + eL + 3) * Dd.ε)
      * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a,
    Dd.k, Dd.a, hHost, ⟨hx3, hb, r1, r2, r3, r4, r5, r6, r7, r8, hTop', r9, r10⟩,
    (small_costs_split _ _ _ _ _ _ _ _).2 ⟨hMove, hCost⟩, ?_⟩
  refine (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, w2, by linarith,
    Fintype.card_pos, hb, ha, Finset.card_le_univ T2, w7, w8⟩

theorem chain_at_alt : ChainAt := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  refine ⟨Cd, hCd, fun eD eL ε x h => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩ := chain_top_bound Cd eD eL ε x h
  have := proposition_at_point (eD + eL + 3) ε x
    ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD,
      ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩
  have e : eD + eL + 3 + 3 = eD + eL + 6 := by ring
  rwa [e] at this


lemma moveCostEv (Cd CL ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) := by
  set A : ℝ := 4 * |Cd| + 15 + 12 * |CL| with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 (A ^ 4), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxA : A ^ 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ ((1 : ℝ) / 4) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyA : A ≤ y := by
    have h1 := Real.rpow_le_rpow (by positivity) hxA (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 : (A ^ 4) ^ ((1 : ℝ) / 4) = A := by
      have := Real.pow_rpow_inv_natCast hA0 (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at this ⊢
      exact this
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * y := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hy] at this
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog1 : Real.log (x + 1) ≤ 1 + Real.log x := by
    have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hCL : CL * Real.log x ≤ |CL| * (4 * y) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hlog0) (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
  have hyy : y * y ≤ x ^ ((1 : ℝ) / 2 + ε) := by
    rw [hy, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hCd : Cd ≤ |Cd| := le_abs_self Cd
  have hCd0 : 0 ≤ |Cd| := abs_nonneg Cd
  have h1 : moveCost x Cd CL ≤ A * y := by
    unfold moveCost
    have e1 : 4 * |Cd| ≤ 4 * |Cd| * y := by nlinarith
    have e2 : A * y = 4 * |Cd| * y + 15 * y + 12 * |CL| * y := by rw [hA]; ring
    rw [e2]
    nlinarith
  exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hyA (by linarith)) hyy)

lemma le_rpow_26 (ε x : ℝ) (hε : 0 < ε) (h1 : (26 : ℝ) ^ (8 / (3 * ε)) ≤ x) : 26 ≤ x ^ (3 * ε / 8) := by
  have h2 : 0 ≤ 3 * ε / 8 := by positivity
  have h3 := Real.rpow_le_rpow (by positivity) h1 h2
  rw [← Real.rpow_mul (by norm_num)] at h3
  have h4 : 8 / (3 * ε) * (3 * ε / 8) = 1 := by field_simp
  rwa [h4, Real.rpow_one] at h3

theorem x_large_eventually : XLargeEv := by
  intro K cHH eK Cd CL ε hε
  obtain ⟨x₁, hx₁⟩ := large_x_eventually ε K cHH eK hε
  obtain ⟨x₂, hx₂⟩ := moveCostEv Cd CL ε hε
  refine ⟨max (max x₁ x₂) (max 3 ((26 : ℝ) ^ (8 / (3 * ε)))), fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  · exact le_rpow_26 ε x hε (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
  · exact hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  · exact hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)


section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

def sLog (D0 : Data U0 W Top m f) (u0 : U0) : ℝ :=
  ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)

def compl (D0 : Data U0 W Top m f) (C : Consts) : Data U0 (fun _ => Unit) Top m f where
  x := D0.x
  ε := D0.ε
  a := D0.a
  b := D0.b
  b' := D0.b'
  k := D0.k
  L := D0.L
  La := D0.La
  B0 := D0.B0
  Nc := D0.Nc
  gam := D0.gam
  LpL := D0.LpL
  v := Real.pi
  lg := 0
  logGam := 0
  aT := D0.aT
  w := D0.w
  d := fun _ _ => 1
  T := fun u0 _ => Real.exp (sLog D0 u0)
  muN := fun u0 _ => D0.ASK u0 - D0.LoP C
  muMaxN := fun u0 _ => D0.ASK u0 - D0.LoP C
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun u0 => D0.ASK u0 - D0.LoP C
  muMinCC := fun u0 => D0.ASK u0 - D0.LoP C
  Fo := fun _ => 0
  Ga := fun u0 => D0.ASK u0 - D0.LoP C
  Ta := fun _ => 0
  ASK := D0.ASK
  IO := fun _ => 0
  HH := fun _ => D0.x ^ C.cHH * D0.b
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0






end


namespace Model

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma model_sigma_add_self : (sgc0 : E0 × H) + sgc0 = 0 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  simp [sgc0, h11]

def Id : AddSubgroup (E0 × H) where
  carrier := {x | x = 0 ∨ x = sgc0}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact model_sigma_add_self
  neg_mem' := by
    rintro a (rfl | rfl)
    · left; simp
    · right; exact neg_eq_of_add_eq_zero_left model_sigma_add_self

def DA : ArithData H where
  q1 := 11
  d := 7
  inertia p := if p = 7 then Id else ⊥
  frob _ := 0

lemma hostFacts_DA : HostFacts (DA (H := H)) where
  first_prime_prime := by show Nat.Prime 11; norm_num
  d_prime := by show Nat.Prime 7; norm_num
  first_prime_ne_two := by show (11 : ℕ) ≠ 2; norm_num
  d_ne_two := by show (7 : ℕ) ≠ 2; norm_num
  firstPrime_ne_secondPrime := by show (11 : ℕ) ≠ 7; norm_num
  unram := by
    intro p _ _ _ h7
    have h7' : p ≠ 7 := h7
    show (if p = 7 then Id else ⊥) = ⊥
    rw [if_neg h7']
  split_inertia := by
    intro p hp x hx
    have h7 : p ≠ 7 := by
      rcases hp with rfl | rfl
      · norm_num
      · show (11 : ℕ) ≠ 7; norm_num
    have hx' : x ∈ (if p = 7 then Id else (⊥ : AddSubgroup (E0 × H))) := hx
    rw [if_neg h7, AddSubgroup.mem_bot] at hx'
    subst hx'
    simp [InPhi]
  split_frob := by
    intro p _
    show InPhi (0 : E0 × H)
    simp [InPhi]
  inertia_d := by
    intro x
    show x ∈ (if (7 : ℕ) = 7 then Id else (⊥ : AddSubgroup (E0 × H))) ↔ _
    rw [if_pos rfl]
    exact Iff.rfl

lemma fPl_eq : fPl H = 2 * (Fintype.card H : ℝ) := by
  unfold fPl PhiSet
  have : (univ.filter (InPhi (H := H))) = (({((0:ZMod 2),(0:ZMod 2)), (0,1)} : Finset E0) ×ˢ (univ : Finset H)) := by
    ext ⟨⟨a, b⟩, h⟩
    simp only [mem_filter, mem_univ, true_and, InPhi, mem_product, mem_insert, mem_singleton, Prod.mk.injEq, and_true]
    revert a b; decide
  rw [this, card_product]
  simp [Finset.card_univ]

def wM : H → Fin 1 → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then 2 ^ 60 else 2 ^ 56

def aM : H → ℝ := fun _ => 65536 * 2 ^ 60

def fM (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℕ := (PhiSet (H := H)).card

def ePM : Fin (fM H) ≃ PhiSet (H := H) := (Finset.equivFin _).symm

def modelData : Data H (fun _ => Unit) (univ : Finset H) 1 (fM H) where
  x := 65536
  ε := 1
  a := 65536 * 2 ^ 60
  b := 2 ^ 60
  b' := 2 ^ 56
  k := 65536
  L := 60
  La := 100
  B0 := 0
  Nc := 0
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => 65536 * 2 ^ 60
  w := fun u0 j ρ => wM u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin 1, ASK DA 1048576 (aM t) t (wM u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

def CM : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩



lemma fM_pos : 0 < fM H := Fin.pos (ePM.symm ⟨0, by simp [PhiSet, InPhi]⟩)



end

end Model


end Formalism.LFunctionChainParameters.LChain

section Check
open Formalism.LFunctionChainParameters.LChain
end Check

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr


lemma errX5at_le {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (hW : ErrWindows D C Xpp eK K) (hX : LargeX D.x D.ε K C.cHH eK) (u0 : U0) :
    ErrX5at D C Xpp u0 ≤ D.x ^ (CErr C * D.ε) * ErrText D := by
  obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  obtain ⟨hlog, hbig⟩ := hX
  have hx0 : 0 < D.x := by linarith only [hx]
  have hy : 1 ≤ D.x ^ D.ε := Real.one_le_rpow hx hε.le
  have hyD : 1 ≤ D.x ^ (C.eDiv * D.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
  have hyL : 1 ≤ D.x ^ (C.eLoss * D.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have hbxb : D.b ≤ D.x * D.b := le_mul_of_one_le_left hb0 hx
  have hba : D.b ≤ D.a := hbxb.trans hxb
  have ha1 : 1 ≤ D.a := hb.trans hba
  have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk : 0 < D.k := by linarith only [hk1]
  have hmx : (m : ℝ) ≤ D.x := by
    refine hm.trans ?_
    calc D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ≤ D.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
      _ = D.x := Real.rpow_one _
  have hMk : (m : ℝ) ≤ D.k := (le_mul_of_one_le_left hM hx).trans hxm
  have hMb : (m : ℝ) * D.b ≤ D.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
  have hsA0 : 0 ≤ D.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
  have hsA : D.sumA ≤ 2 * (D.nT * D.a) := by
    unfold Data.sumA Data.nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, 2 * D.a := Finset.sum_le_sum (fun t _ => (haT t).2)
      _ = 2 * ((Fintype.card Top : ℝ) * D.a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlWk : Real.log (Fintype.card (W u0) : ℝ) ≤ D.a :=
    ((hlW u0).trans (sub_three_mul_log_two_le hk.le)).trans hka
  have hlk0 : 0 ≤ Real.log D.k := Real.log_nonneg hk1
  have hlk : Real.log D.k ≤ (1 + eK) * D.x ^ D.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hlH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
  have hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε :=
    log_one_add_rpow_le hx hHH hlog hy
  obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
  have hpow : D.x ^ (CErr C * D.ε)
      = D.x ^ (C.eDiv * D.ε) * D.x ^ (C.eLoss * D.ε) * D.x ^ D.ε * D.x ^ D.ε * D.x ^ D.ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    unfold CErr
    ring
  rw [hpow]
  unfold KBig at hbig
  have := core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := Real.log (Fintype.card (W u0) : ℝ)) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (y := D.x ^ D.ε) (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε)) (K := K)
    (h := 1 + C.cHH) (g := 1 + eK)
    hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
    hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
    (by linarith only [hHH]) (by linarith only [heK]) hbig
  unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
  exact this








namespace ModelEv

open Model

def SizesAt (K cHH eK ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (Top : Type) (_ : Fintype Top) (m f : ℕ)
    (D0 : Data H (fun _ => Unit) Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    D0.x = x ∧ D0.ε = ε ∧ C.eDiv ≤ 1 ∧ C.eLoss ≤ 1 ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧ Ident D0 D N ell TT a w eT eP ∧ ErrWindows D0 C Xpp eK K ∧ BNBounds D0 T2 ∧
    GrowthInequalitySizes TT T2 a w N D0.x D0.b D0.b' η X' θ ∧ 0 < θ ∧ CostWindows D0.x (fPl H) D0.b η θ ∧
    RestSize D0.ε D0.x (Fintype.card H) TT.card T2.card m D0.b D0.k D0.a ∧
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ∧
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) ∧
    (∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C)


section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def wE (m : ℕ) (b : ℝ) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then b else 1

def DE (x ε b : ℝ) (m N : ℕ) : Data H (fun _ => Unit) (univ : Finset H) m (fM H) where
  x := x
  ε := ε
  a := x * b
  b := b
  b' := 1
  k := x * m
  L := Real.log b
  La := Real.log b
  B0 := (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
  Nc := ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => x * b
  w := fun u0 j ρ => wE m b u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin m, ASK DA N (x * b) t (wE m b u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

lemma wE_cases (m : ℕ) (b : ℝ) (u0 : H) (j : Fin m) (ρ : E0 × H) : wE m b u0 j ρ = b ∨ wE m b u0 j ρ = 1 := by
  unfold wE; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma geo7 (a : ℝ) (N : ℕ) : ∑ i ∈ Icc 1 N, a / (7 : ℝ) ^ i + a / (6 * 7 ^ N) = a / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [← ih]
    field_simp
    ring

lemma askDA_le (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 ≤ a) (hw : ∀ ρ, 0 ≤ w ρ) :
    ASK (DA (H := H)) N a t w ≤ a := by
  classical
  have hd : (((DA (H := H)).d : ℕ) : ℝ) = 7 := by
    show (((7 : ℕ) : ℕ) : ℝ) = 7
    norm_num
  have h2 : askD (DA (H := H)) N a t w ≤ a / 6 := by
    unfold askD
    rw [hd]
    refine le_trans (Finset.sum_le_sum (g := fun i => a / (7 : ℝ) ^ i) fun i _ => ?_) ?_
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {(sgc0 : E0 × H)}) ?_
        (fun _ _ _ => le_max_right _ _)) ?_
      · intro g hg
        obtain ⟨-, hg1, hg2⟩ := Finset.mem_filter.1 hg
        have e : g - i • (DA (H := H)).frob (DA (H := H)).d = g := by
          show g - i • (0 : E0 × H) = g
          simp
        rw [e] at hg1
        rcases (hostFacts_DA.inertia_d g).1 hg1 with h | h
        · exact absurd (by rw [h]; simp [InPhi]) hg2
        · exact Finset.mem_singleton.2 h
      · rw [Finset.sum_singleton]
        exact max_le (by linarith [hw (partner t sgc0)]) (by positivity)
    · have := geo7 a N
      have h4 : 0 ≤ a / (6 * 7 ^ N) := by positivity
      linarith
  have h0 : 0 ≤ askD (DA (H := H)) N a t w := by
    unfold askD
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
  unfold ASK
  rw [Finset.sum_eq_zero, hd, zero_add]
  · have hl : Real.log 7 ≤ 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hl0 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    nlinarith
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
    exact absurd (by show InPhi (0 : E0 × H); simp [InPhi]) hp2.2.2.2.2

set_option maxHeartbeats 1600000 in
lemma sizesOf (x ε b : ℝ) (m N n : ℕ) (hcard : Fintype.card H = n)
    (hx : 3 ≤ x) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : x ≤ n) (hb : b = 12 * n * (x + 1) * x)
    (hm1 : x ^ ((1 : ℝ) / 2 - ε) ≤ m) (hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) (hmx : (m : ℝ) ≤ x)
    (hk : x * m ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) (hL : Real.log b ≤ 2 * x ^ ε) (hN : x * b ≤ N)
    (hl3 : 3 ≤ Real.log x) :
    SizesAt 1 1 2 ε x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hbx : x ≤ b := by
    rw [hb]
    have : 1 ≤ 12 * (n : ℝ) * (x + 1) := by nlinarith
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm1
  have hm1' : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hxe' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hnT : (DE (H := H) x ε b m N).nT = n := by
    unfold Data.nT
    rw [Fintype.card_coe, Finset.card_univ, hcard]
  have hcu : (univ : Finset H).card = n := by rw [Finset.card_univ, hcard]
  have hf : fPl H = 2 * (n : ℝ) := by rw [fPl_eq, hcard]
  have hlogw : ∀ (u0 : H) (j : Fin m) (ρ : E0 × H), 0 ≤ Real.log (wE m b u0 j ρ) ∧ Real.log (wE m b u0 j ρ) ≤ Real.log b := by
    intro u0 j ρ
    rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
    · exact ⟨hlb, le_refl _⟩
    · simpa using hlb
  refine ⟨H, inferInstance, inferInstance, inferInstance, (univ : Finset H), inferInstance, m, fM H,
    DE x ε b m N, CM, 0, DA, fun _ => 0, N, univ, univ, fun _ => x * b, wE m b, Equiv.refl _, ePM,
    0, x * b, 1 / (2 * fPl H * (x + 1) * x), rfl, rfl, le_refl _, le_refl _, le_refl _, hostFacts_DA,
    ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [DE], fun _ => rfl⟩, ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩, ?_, ?_, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hn1, hm2, le_refl _, by norm_num, ?_, ?_, ?_, hlb, hL, hlb, hL,
      zero_le_one, ?_, le_refl _, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, fun _ => ?_, by norm_num [DE], le_refl _, le_refl _, ?_⟩
    · show 1 ≤ x * m
      nlinarith
    · show x * m ≤ x ^ (2 : ℝ)
      rw [Real.rpow_two]
      nlinarith
    · show x * m ≤ x * b
      nlinarith
    · show x * m * 1 ≤ x * b
      nlinarith
    · show 0 ≤ x * b
      positivity
    · show 0 ≤ x * b
      positivity
    · show x * b ≤ 2 * (x * b)
      nlinarith [mul_pos hx0 hb0]
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
      positivity
    · show 0 ≤ ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
        / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      refine mul_nonneg ?_ hl2
      show 0 ≤ x * m - 3
      nlinarith
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]
  ·
    rw [hnT]
    show ((0 : ℝ) + 4 * Real.sqrt 0) * (x ^ CM.cHH * b) ≤ 1 * x ^ ε * ((n : ℝ) * (x * b))
    rw [Real.sqrt_zero]
    have : 0 ≤ 1 * x ^ ε * ((n : ℝ) * (x * b)) := by positivity
    simpa using this
  ·
    refine ⟨le_refl _, by positivity, zero_lt_one, ?_, by rw [hf]; positivity, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · show (1 : ℝ) * (x * b) ≤ x * b
      linarith
    · show |x * b / b - x| ≤ 1
      rw [mul_div_assoc, div_self hb0.ne']
      simp
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    · have : wE m b u0 j ρ = b := by unfold wE; rw [if_pos h]
      rw [this]
      exact ⟨le_refl _, by show b ≤ b + 0 + 1; linarith⟩
    · have : wE m b u0 j ρ = 1 := by unfold wE; rw [if_neg h]
      rw [this]
      show (1 : ℝ) ≤ 2 * 1
      norm_num
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
      · rw [mul_div_assoc, div_self hb0.ne']
        nlinarith
      · simpa using hN
  · rw [hf]; positivity
  ·
    show 2 * fPl H * (x + 1) * (1 / (2 * fPl H * (x + 1) * x)) ≤ 1 / x
    rw [hf]
    apply le_of_eq
    field_simp
  ·
    show 6 * fPl H * (x + 1) * (0 + 1) ≤ b / x
    rw [hf, hb]
    apply le_of_eq
    field_simp
    ring
  · show x * b ≤ 2 * x * b
    nlinarith [mul_pos hx0 hb0]
  · have : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-(ε / 8)) * (n : ℝ) / 2 ≤ (n : ℝ)
    nlinarith
  · have : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-ε) ≤ (n : ℝ) / (n : ℝ)
    rw [div_self hn0.ne']
    exact this
  · exact hm1
  · rw [hcard]
    exact hk
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (ePM ρ)).1
  · intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ CM.cCount * (m : ℝ) * Real.log b
    simpa [CM] using h3
  ·
    intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have hxb : 0 < x * b := by positivity
    have hA : (DE (H := H) x ε b m N).ASK u0 ≤ ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b := by
      refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ => askDA_le N (x * b) t _ hxb.le fun ρ => ?_
      rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    have hM : ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b ≤ (DE (H := H) x ε b m N).Main u0 := by
      unfold Data.Main
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => ?_
      show x * b ≤ x * b * (Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ))
      have hg := Real.eulerMascheroniConstant_lt_two_thirds
      have hlm : Real.log (x * b) = Real.log x + Real.log b := Real.log_mul hx0.ne' hb0.ne'
      have := h1 j
      have h5 : 1 ≤ Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) := by linarith
      calc x * b = x * b * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 hxb.le
    have hE : ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b = ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      ring
    have e1 : 0 ≤ CM.cDiv * (DE (H := H) x ε b m N).nT * (DE (H := H) x ε b m N).a * (DE (H := H) x ε b m N).La := by
      rw [hnT]
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).a = x * b := rfl
      have q3 : (DE (H := H) x ε b m N).La = Real.log b := rfl
      rw [q1, q2, q3]
      exact mul_nonneg (by positivity) hlb
    have e2 : 0 ≤ CM.cDiv * (m : ℝ) * ((DE (H := H) x ε b m N).B0 + (DE (H := H) x ε b m N).Nc)
        * (DE (H := H) x ε b m N).x ^ (CM.eDiv * (DE (H := H) x ε b m N).ε) := by
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).B0 = (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε := rfl
      have q3 : (DE (H := H) x ε b m N).Nc = ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
          / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε))) := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q3, q4]
      positivity
    have e3 : 0 ≤ (DE (H := H) x ε b m N).LoP CM := by
      unfold Data.LoP
      rw [hnT]
      have q1 : CM.cLoss = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).b = b := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q4]
      positivity
    linarith

end



end ModelEv


namespace ModelText

lemma ev_rpow_le_exp (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in Filter.atTop, x ^ c ≤ Real.exp (x ^ δ) := by
  have hc : 0 < (|c| + 1)⁻¹ := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
  have hxpos : 0 < x := by linarith
  have h1 : (|c| + 1) * Real.log x ≤ x ^ δ := by
    have : (|c| + 1) * Real.log x ≤ (|c| + 1) * ((|c| + 1)⁻¹ * x ^ δ) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at this
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.2
  have hlog0 := Real.log_nonneg hx1
  have : Real.log x * c ≤ Real.log x * |c| := by gcongr; exact le_abs_self c
  nlinarith [abs_nonneg c]

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def kTx (x ε : ℝ) : ℝ := x ^ ((9 : ℝ) / 2 + 10 * ε)

def etaTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 4))

def thTx (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 8)))

def wF (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ =>
  if IsThickAt T2 u0 ρ then bTx x ε + etaTx x ε
  else if ρ ∈ TT.image topPl then 2 * bpTx x ε else wppTx x ε (Fintype.card H)

def NF (H : Type) [Fintype H] (x ε : ℝ) : ℕ := ⌈XppTx x ε (Fintype.card H)⌉₊

def textData (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Data H (fun _ => Unit) TT m (Model.fM H) where
  x := x
  ε := ε
  a := aTx x ε
  b := bTx x ε
  b' := bpTx x ε
  k := kTx x ε
  L := x ^ ε
  La := Real.log (aTx x ε) + x ^ (ε / 3)
  B0 := (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
  Nc := (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => aTx x ε
  w := fun u0 j ρ => wF x ε m TT T2 u0 j (Model.ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ TT, ∑ j : Fin m, ASK Model.DA (NF H x ε) (aTx x ε) t (wF x ε m TT T2 u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := x ^ (-1 : ℝ)
  eBar := 0

def CF : Consts := ⟨1, 1, 1, 1, 2, 1, 1, 1, 1, 1⟩

def AllSizes (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Prop :=
  HostFacts (Model.DA (H := H)) ∧
  Ident (textData x ε m TT T2) Model.DA (NF H x ε) (fun _ => 0) TT (fun _ => aTx x ε) (wF x ε m TT T2)
    (Equiv.refl _) Model.ePM ∧
  ErrWindows (textData x ε m TT T2) CF (XppTx x ε (Fintype.card H)) 15 2 ∧
  BNBounds (textData x ε m TT T2) T2 ∧
  GrowthInequalitySizes TT T2 (fun _ => aTx x ε) (wF x ε m TT T2) (NF H x ε) x (bTx x ε) (bpTx x ε) (etaTx x ε) (XpTx x ε)
    (thTx x ε) ∧
  CostWindows x (fPl H) (bTx x ε) (etaTx x ε) (thTx x ε) ∧
  RestSize ε x (Fintype.card H) TT.card T2.card m (bTx x ε) (kTx x ε) (aTx x ε) ∧
  (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)) ∧
  (∀ u0, ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
    ≤ CF.cCount * (m : ℝ) * (textData x ε m TT T2).L)

theorem famAt (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hx : 3 ≤ x)
    (hT : 1 ≤ x ∧ 1 ≤ bTx x ε ∧ Real.log (bTx x ε) = x ^ ε ∧ Real.log (aTx x ε) + x ^ (ε / 3) ≤ 2 * x ^ ε ∧
      kTx x ε ≤ aTx x ε ∧ 0 ≤ bpTx x ε ∧ kTx x ε * bpTx x ε ≤ aTx x ε ∧
      0 ≤ XppTx x ε (Fintype.card H) ∧ XppTx x ε (Fintype.card H) ≤ aTx x ε)
    (hnlo : x ^ (2 + 8 * ε) ≤ (Fintype.card H : ℝ))
    (hmlo : x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m) (hmhi : (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16))
    (h2 : 2 ≤ x ^ (9 * ε / 16))
    (hTT : x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 ≤ TT.card)
    (hT2 : x ^ (-ε) * (Fintype.card H : ℝ) ≤ T2.card)
    (hc1 : 2 * (2 * (Fintype.card H : ℝ)) * (x + 1) * thTx x ε ≤ 1 / x)
    (hc2 : 6 * (2 * (Fintype.card H : ℝ)) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x)
    (hw1 : 1 ≤ wppTx x ε (Fintype.card H)) : AllSizes x ε m TT T2 := by
  obtain ⟨hx1, hb1, hlogb, hLa, hka, hbp0, hkbp, hX0, hXa⟩ := hT
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := by linarith
  have ha : aTx x ε = x * bTx x ε := rfl
  have ha0 : 0 < aTx x ε := by rw [ha]; positivity
  have hab : bTx x ε ≤ aTx x ε := by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1
  have hXp0 : 0 < XpTx x ε := Real.exp_pos _
  have hbp : 0 < bpTx x ε := div_pos ha0 hXp0
  have hn0 : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hxe1 : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε0.le
  have hk_x : x ≤ kTx x ε := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)
    rwa [Real.rpow_one] at this
  have hk0 : 0 < kTx x ε := by linarith
  have heta0 : 0 < etaTx x ε := Real.exp_pos _
  have hetab : etaTx x ε ≤ bTx x ε :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hbpb : bpTx x ε ≤ bTx x ε := by
    have h1 : x * bpTx x ε ≤ x * bTx x ε := le_trans (mul_le_mul_of_nonneg_right hk_x hbp.le) hkbp
    exact le_of_mul_le_mul_left h1 hx0
  have hwpp0 : 0 < wppTx x ε (Fintype.card H) := by linarith
  have hwppbp : wppTx x ε (Fintype.card H) ≤ bpTx x ε := by
    unfold wppTx
    exact div_le_self hbp.le (by nlinarith)
  have hnT : (textData x ε m TT T2).nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_coe]
  have hTTpos : (0 : ℝ) < TT.card := lt_of_lt_of_le (by positivity) hTT
  have hTT1 : (1 : ℝ) ≤ TT.card := by
    have : 0 < TT.card := by exact_mod_cast hTTpos
    exact_mod_cast this
  have hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    have e : x ^ ((1 : ℝ) / 2 + ε / 2) = x ^ (9 * ε / 16) * x ^ ((1 : ℝ) / 2 - ε / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [e]
    exact hmhi.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _))
  have hxm : x * m ≤ kTx x ε := by
    have h1 : x * m ≤ x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2) := by
      rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hm_hi hx0.le
    rw [← Real.rpow_add hx0] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

  have hw : ∀ u0 j ρ, wppTx x ε (Fintype.card H) ≤ wF x ε m TT T2 u0 j ρ ∧ wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε := by
    intro u0 j ρ
    unfold wF
    split_ifs
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  have hlogw : ∀ u0 j ρ, 0 ≤ Real.log (wF x ε m TT T2 u0 j ρ) ∧ Real.log (wF x ε m TT T2 u0 j ρ) ≤ 2 * x ^ ε := by
    intro u0 j ρ
    obtain ⟨h1, h2'⟩ := hw u0 j ρ
    refine ⟨Real.log_nonneg (by linarith), ?_⟩
    have h3 := Real.log_le_log (by linarith) h2'
    rw [Real.log_mul (by norm_num) hb0.ne', hlogb] at h3
    have h4 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hf : (0 : ℝ) < (Model.fM H : ℝ) := by exact_mod_cast Model.fM_pos
  refine ⟨Model.hostFacts_DA, ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [textData], fun _ => rfl⟩, ⟨?_, ?_⟩,
    ⟨le_refl _, le_refl _⟩, ?_, ⟨?_, ?_⟩, ⟨?_, hTT, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hTT1, hm_hi, hxm, by norm_num, by
      show (1 : ℝ) ≤ kTx x ε
      linarith, ?_, hka, Real.rpow_nonneg hx0.le _, ?_, ?_, hLa, hbp0, hkbp, hX0, hXa, fun _ => ⟨ha0.le, ?_⟩, ?_, ?_,
      fun _ => ?_, by show (0 : ℝ) ≤ 1 / 2; norm_num, Real.rpow_nonneg hx0.le _, le_refl _, ?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    · show x ^ ε ≤ 2 * x ^ ε
      linarith
    · show 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ aTx x ε)
      have := Real.rpow_nonneg hx0.le (ε / 3)
      linarith
    · show aTx x ε ≤ 2 * aTx x ε
      linarith
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
      positivity
    · show 0 ≤ (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      exact mul_nonneg (by show 0 ≤ kTx x ε - 3; linarith) (Real.log_nonneg (by norm_num))
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CF]
  ·
    rw [hnT]
    show (x ^ (-1 : ℝ) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * bTx x ε) ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε)
    rw [Real.sqrt_zero, mul_zero, add_zero, ← mul_assoc, ← Real.rpow_add hx0]
    norm_num
    have h1 : aTx x ε ≤ (TT.card : ℝ) * aTx x ε := le_mul_of_one_le_left ha0.le hTT1
    have h3 : (TT.card : ℝ) * aTx x ε ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  ·
    refine ⟨heta0.le, hXp0, hbp, ?_, (Real.exp_pos _).le, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · have : bpTx x ε * XpTx x ε = aTx x ε := div_mul_cancel₀ _ hXp0.ne'
      rw [this, ha]
    · have : aTx x ε / bTx x ε = x := by rw [ha]; field_simp
      rw [this]; simp
    · linarith [(hw u0 j ρ).1]
    · have : wF x ε m TT T2 u0 j ρ = bTx x ε + etaTx x ε := by unfold wF; rw [if_pos h]
      rw [this]
      constructor <;> linarith
    · unfold wF
      rw [if_neg h]
      split_ifs
      · exact le_refl _
      · linarith
    · have h1 : aTx x ε / wF x ε m TT T2 u0 j ρ ≤ aTx x ε / wppTx x ε (Fintype.card H) :=
        div_le_div_of_nonneg_left ha0.le hwpp0 (hw u0 j ρ).1
      exact h1.trans (Nat.le_ceil _)
  · rw [Model.fPl_eq]; exact hc1
  · rw [Model.fPl_eq]; exact hc2
  · rw [ha]; nlinarith [mul_pos hx0 hb0]
  · rw [le_div_iff₀ hn0]; exact hT2
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hmlo
  · have h1 : (x ^ (2 + 8 * ε)) ^ 2 ≤ (Fintype.card H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hnlo 2
    have h3 : kTx x ε ≤ (x ^ (2 + 8 * ε)) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := by
      rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact h3.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _))
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (Model.ePM ρ)).1
  · intro u0
    have h1 : ∀ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
        ≤ 2 * x ^ ε := by
      intro j
      have h2' : ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ ∑ _ρ : Fin (Model.fM H), 2 * x ^ ε :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (Model.ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2'
      calc (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ (1 / (Model.fM H : ℝ)) * ((Model.fM H : ℝ) * (2 * x ^ ε)) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = 2 * x ^ ε := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ (2 : ℝ) * (m : ℝ) * x ^ ε
    linarith

end

lemma h18 {x : ℝ} (hxpos : 0 < x) : x ^ (18 : ℝ) = x ^ (15 : ℝ) * x * x * x := by
  rw [show (18 : ℝ) = 15 + 1 + 1 + 1 by norm_num, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_add hxpos,
    Real.rpow_one]

lemma cost1 {x ε n : ℝ} (h48 : 48 ≤ x) (_hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f1 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 8))) : 2 * (2 * n) * (x + 1) * thTx x ε ≤ 1 / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  unfold thTx
  rw [Real.exp_neg, le_div_iff₀ hxpos]
  have hE : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
  have h1 : 2 * (2 * n) * (x + 1) * x ≤ Real.exp (x ^ (ε / 8)) := by
    refine le_trans ?_ f1
    rw [h18 hxpos]
    have h2 : 2 * (2 * n) * (x + 1) * x ≤ 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x := by gcongr
    have h3 : 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 4 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x = (x ^ (15 : ℝ) * x) * (4 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 2 * (2 * n) * (x + 1) * (Real.exp (x ^ (ε / 8)))⁻¹ * x
      = (2 * (2 * n) * (x + 1) * x) * (Real.exp (x ^ (ε / 8)))⁻¹ := by ring
    _ ≤ Real.exp (x ^ (ε / 8)) * (Real.exp (x ^ (ε / 8)))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hE.ne'

lemma cost2 {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f2 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 4))) (f5 : 2 ≤ x ^ (3 * ε / 4)) :
    6 * (2 * n) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [le_div_iff₀ hxpos]
  unfold etaTx bTx
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (x ^ (ε / 4)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hEE : E * E ≤ Real.exp (x ^ ε) := by
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (3 * ε / 4) * x ^ (ε / 4) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 4)
    nlinarith
  rw [← hE] at f2 ⊢
  have h1 : 6 * (2 * n) * (x + 1) * x * 2 ≤ E := by
    refine le_trans ?_ f2
    rw [h18 hxpos]
    have h2 : 6 * (2 * n) * (x + 1) * x * 2 ≤ 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 := by gcongr
    have h3 : 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 24 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 = (x ^ (15 : ℝ) * x) * (24 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 6 * (2 * n) * (x + 1) * (E + 1) * x ≤ 6 * (2 * n) * (x + 1) * (2 * E) * x := by
        gcongr; linarith
    _ = (6 * (2 * n) * (x + 1) * x * 2) * E := by ring
    _ ≤ E * E := by gcongr
    _ ≤ Real.exp (x ^ ε) := hEE

lemma wpp1 {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f3 : x ^ (15 : ℝ) ≤ Real.exp (x ^ (ε / 3))) (f6 : 2 ≤ x ^ (2 * ε / 3)) : 1 ≤ wppTx x ε n := by
  have hxpos : 0 < x := by linarith
  unfold wppTx bpTx aTx bTx XpTx
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (x ^ (ε / 3)) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  have hXX : X * X ≤ Real.exp (x ^ ε) := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 3)
    nlinarith
  rw [← hX] at f3 ⊢
  have hnX : n ≤ X := hn15.trans f3
  rw [le_div_iff₀ (by positivity), le_div_iff₀ hX0]
  have h : n * X ≤ Real.exp (x ^ ε) := (mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX
  calc 1 * (x * n) * X = x * (n * X) := by ring
    _ ≤ x * Real.exp (x ^ ε) := by gcongr

def FamAt (ε x : ℝ) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (m : ℕ) (TT T2 : Finset (ZMod n)),
    x ^ (2 + 8 * ε) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) ∧
    x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m ∧ (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16) ∧
    (TT.card : ℝ) < x ^ (-(ε / 8)) * n / 2 + 1 ∧ (T2.card : ℝ) < x ^ (-ε) * n + 1 ∧
    AllSizes x ε m TT T2

theorem family (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FamAt ε x := by
  obtain ⟨x1, hx1⟩ := text_sizes_windows ε 15 hε0
  have e1 := ev_rpow_le_exp 18 (ε / 8) (by positivity)
  have e2 := ev_rpow_le_exp 18 (ε / 4) (by positivity)
  have e3 := ev_rpow_le_exp 15 (ε / 3) (by positivity)
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (9 * ε / 16) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (3 * ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e6 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (((((((e1.and e2).and e3).and e4).and e5).and e6).and (Filter.eventually_ge_atTop (48 : ℝ))).and
      (Filter.eventually_ge_atTop x1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, h48⟩, hxx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith

  set y : ℝ := x ^ (2 + 8 * ε) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1' (by linarith)
  set n : ℕ := ⌈y⌉₊ with hn
  have hnpos : 0 < n := Nat.ceil_pos.2 (by linarith)
  have : NeZero n := ⟨hnpos.ne'⟩
  have hnlo : y ≤ (n : ℝ) := Nat.le_ceil y
  have hnhi : (n : ℝ) ≤ 2 * y := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn15 : (n : ℝ) ≤ x ^ (15 : ℝ) := by
    have h1 : 2 * y ≤ x ^ (1 : ℝ) * y := by rw [Real.rpow_one]; nlinarith
    rw [hy, ← Real.rpow_add hxpos] at h1
    exact hnhi.trans (h1.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)))

  set z : ℝ := x ^ ((1 : ℝ) / 2 - ε / 16) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1' (by linarith)
  set m : ℕ := ⌈z⌉₊ with hm
  have hmlo : z ≤ (m : ℝ) := Nat.le_ceil z
  have hmhi : (m : ℝ) ≤ 2 * z := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ z)).le
    linarith
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n

  have hd1 : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd1' : 0 < x ^ (-(ε / 8)) := Real.rpow_pos_of_pos hxpos _
  have hd2 : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd2' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hxpos _
  obtain ⟨TT, -, hTTc⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-(ε / 8)) * n / 2⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  obtain ⟨T2, -, hT2c⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-ε) * n⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  have hk15 : kTx x ε ≤ x ^ (15 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hk0 : 0 < kTx x ε := Real.rpow_pos_of_pos hxpos _
  have hT := hx1 x (kTx x ε) n (x ^ (ε / 3)) hxx1 hk0 hk15 hn0 hn15 (le_refl _)
  refine ⟨n, inferInstance, m, TT, T2, hnlo, hnhi, hmlo, hmhi, ?_, ?_, ?_⟩
  · rw [hTTc]; exact Nat.ceil_lt_add_one (by positivity)
  · rw [hT2c]; exact Nat.ceil_lt_add_one (by positivity)
  · refine famAt x ε m TT T2 hε0 hε1 (by linarith) ?_ ?_ hmlo hmhi f4 ?_ ?_ ?_ ?_ ?_
    · rw [hcard]; exact hT
    · rw [hcard]; exact hnlo
    · rw [hcard, hTTc]; exact Nat.le_ceil _
    · rw [hcard, hT2c]; exact Nat.le_ceil _
    · rw [hcard]; exact cost1 h48 hn0 hn15 f1
    · rw [hcard]; exact cost2 h48 hn0 hn15 f2 f5
    · rw [hcard]; exact wpp1 h48 hn0 hn15 f3 f6

end ModelText


end Formalism.LFunctionChainParameters.LChain

section Check2
open Formalism.LFunctionChainParameters.LChain
end Check2
