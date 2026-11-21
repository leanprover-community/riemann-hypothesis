import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem rpow_le_exp_rpow_eventually {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, x ^ c ≤ Real.exp (x ^ ε) := by
  have h := ((tendsto_exp_div_rpow_atTop (c / ε)).comp (tendsto_rpow_atTop hε)).eventually_ge_atTop 1
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  simp only [Function.comp] at h1
  rw [← Real.rpow_mul h2.le, mul_div_cancel₀ _ hε.ne', le_div_iff₀ (Real.rpow_pos_of_pos h2 _), one_mul] at h1
  exact h1

theorem poly_sizes_ranks_weights : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Fm.Ct ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) ∧ ((Fm.D x i).R.m : ℝ) ≤ x ∧ ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) ∧ ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) ∧ (Fm.L x i).sc.x = x ∧ (Fm.L x i).sc.a = x * (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.L ∧ (Fm.L x i).sc.L ≤ x ∧ x ^ (Fm.Ct + 6) ≤ (Fm.L x i).sc.b ∧ (∀ t, (0 : ℝ) ≤ (Fm.L x i).aT t ∧ ((Fm.L x i).aT t : ℝ) ≤ 2 * x * (Fm.L x i).sc.b) ∧ (Fm.L x i).B0 ≤ x ^ (5 : ℝ) * (Fm.L x i).sc.b ∧ 0 ≤ (Fm.L x i).B0) := by
  intro eps Fm
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := rpow_le_exp_rpow_eventually heps (Fm.Ct + 6)
  refine ⟨max x0 4, fun x hx hx1 i => ?_⟩
  have hexp := hx0 x (le_trans (le_max_left _ _) hx)
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLx := Fm.L_x x i hx1
  have hLe := Fm.L_eps x i
  have hCt := Fm.Ct_eq x i
  generalize Fm.L x i = L at *
  generalize Fm.Ct = Ct at *
  obtain ⟨hN, hM, hK, -, -, -, -, hTT, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have htw := L.t_win
  have haw := L.aT_win
  have hN2 := hN.2
  have hM2 := hM.2
  have hK2 := hK.2
  have hTT2 := hTT.2
  unfold szNst at hTT2
  unfold szTh at hN2 hM2 hK2
  unfold Scale.delta1 at hM2 hTT2
  rw [hLx, hLe] at hN2 hM2 hK2 hTT2
  rw [hLx, hCt] at htw
  have hd : x ^ (-(eps / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1x (by linarith)
  have hd0 : 0 < x ^ (-(eps / 8)) := Real.rpow_pos_of_pos h0x _
  have hs2 : (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
  have hfn : ((Fm.D x i).R.f : ℝ) = 2 * (Fm.D x i).R.n := by unfold Ranks.f; push_cast; ring
  have hf : ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) := by
    have h1 : ((Fm.D x i).R.n : ℝ) ≤ x ^ (5 / 2 : ℝ) :=
      hN2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
    rw [hfn, show (3 : ℝ) = 1 / 2 + 5 / 2 by norm_num, Real.rpow_add h0x]
    exact mul_le_mul hs2 h1 (by positivity) (by positivity)
  have hm : ((Fm.D x i).R.m : ℝ) ≤ x := by
    have h1 : x ^ (eps / 100) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
    have h2 : Real.sqrt (x * x ^ (-(eps / 8))) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (by nlinarith)
    refine hM2.trans ((mul_le_mul h1 h2 (by positivity) (by positivity)).trans ?_)
    exact (Real.mul_self_sqrt h0x.le).le
  have hk : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) :=
    hK2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
  have hCt0 : 0 ≤ Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg (show (1 : ℝ) < x by linarith) (not_le.1 hc)
    linarith [htw.1, htw.2]
  have h6 : 3 * x ≤ x ^ (6 : ℝ) := by
    have : x ^ ((2 : ℕ) : ℝ) ≤ x ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
    rw [Real.rpow_natCast] at this
    nlinarith
  have hT0 : 0 < x ^ Ct := Real.rpow_pos_of_pos h0x _
  have hbig : 3 * x * (Fm.D x i).R.t ≤ x ^ (Ct + 6) := by
    rw [add_comm, Real.rpow_add h0x]
    exact mul_le_mul h6 htw.2 (by positivity) (by positivity)
  have hrt := (Fm.D x i).R.rank_add_five_le
  have h2m := (Fm.D x i).R.two_le_m
  have hk3 := (Fm.D x i).R.m_add_three_le_k
  have hNm : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.N (Fm.D x i).R.m ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by
      unfold Ranks.N
      have a1 : (Fm.D x i).R.k ≤ (Fm.D x i).R.t := by omega
      have a2 : 1 ≤ (Fm.D x i).R.t := by omega
      nlinarith
    have h2 : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    gcongr
  have hnV : ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.nV ≤ 2 * (Fm.D x i).R.t := by
      unfold Ranks.nV Ranks.r; omega
    have h2 : ((Fm.D x i).R.nV : ℝ) ≤ 2 * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    have := htw.1
    nlinarith
  have hTTc : ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) := by
    refine hTT2.trans (le_trans ?_ hf)
    rw [hfn]
    exact mul_le_of_le_one_right (by positivity) hd
  have ha : L.sc.a = x * L.sc.b := by unfold Scale.a; rw [hLx]
  have hL : L.sc.L = x ^ eps := by unfold Scale.L; rw [hLx, hLe]
  have hL1 : 1 ≤ L.sc.L := by rw [hL]; exact Real.one_le_rpow h1x heps.le
  have hL2 : L.sc.L ≤ x := by
    rw [hL]
    calc x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  have hb : L.sc.b = Real.exp (x ^ eps) := by unfold Scale.b; rw [hL]
  have hb0 : 0 < L.sc.b := by rw [hb]; positivity
  have hB0 : L.B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * L.sc.b * L.sc.L := by
    unfold SizeData₂.B0 sizeBudget bSize
    rw [hb, hL, hLx, hLe]
  refine ⟨hCt0, hf, hm, hk, hNm, hnV, hTTc, hLx, ha, hL1, hL2, hb ▸ hexp, fun t => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := haw t
    have ha0 : 0 < L.sc.a := by rw [ha]; positivity
    have hk1 : (1 : ℝ) ≤ (Fm.D x i).R.k := by
      have : 1 ≤ (Fm.D x i).R.k := by omega
      exact_mod_cast this
    have hA : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
    have h3 := div_le_self ha0.le (one_le_mul_of_one_le_of_one_le hk1 hA)
    refine ⟨by linarith, ?_⟩
    rw [mul_assoc, ← ha]; linarith
  · rw [hB0, show (5 : ℝ) = 3 + 1 + 1 by norm_num, Real.rpow_add h0x, Real.rpow_add h0x, Real.rpow_one]
    calc ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * L.sc.b * L.sc.L ≤ x ^ (3 : ℝ) * x * L.sc.b * x := by
          gcongr
      _ = _ := by ring
  · rw [hB0]; positivity

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem natCard_GL_zmod_le (r g : ℕ) (hg : 0 < g) :
    Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r * r) := by
  haveI : NeZero g := ⟨hg.ne'⟩
  have h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  have h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r) := by
    show Nat.card (Fin r → Fin r → ZMod g) = _
    simp [Nat.card_fun, pow_mul]
  exact h2 ▸ h1

theorem log_levelGroup_le_and_level_large : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, lam0 (Fm.D x i) ≤ x ^ (15 : ℝ) ∧ 8 * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.r : ℝ) / ((min ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) : ℕ) : ℝ) ≤ 1 / 3 ∧ 1 ≤ (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := poly_sizes_ranks_weights eps Fm
  refine ⟨max x0 8, fun x hx hx1 i => ?_⟩
  obtain ⟨hCt, hf, hm, hk, -, -, -, hLx, -, hL1, hL2, hb, -⟩ :=
    hx0 x (le_trans (le_max_left _ _) hx) hx1 i
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLe := Fm.L_eps x i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have hb1 : 1 ≤ L.sc.b := le_trans (Real.one_le_rpow h1x (by linarith)) hb
  have h2m := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by omega
    exact_mod_cast this
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrk' : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
  have hg8 : ∀ j, (D.R.k : ℝ) ^ 8 ≤ (D.host.g j : ℝ) := fun j =>
    le_trans (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hb1) 8) (hG j j).1
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) ^ 8 := by positivity
  have hgpos : ∀ j, 0 < D.host.g j := fun j => by
    have := lt_of_lt_of_le hkpos (hg8 j)
    exact_mod_cast this
  have hlog : ∀ j, Real.log (D.host.g j : ℝ) ≤ x := fun j => by
    refine (hG j j).2.2.trans ?_
    unfold szTh Scale.L
    rw [hLx, hLe, ← Real.rpow_add h0x]
    calc x ^ (eps / 100 + eps) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  refine ⟨?_, ?_, hb1⟩
  · have hc : D.what₂.restRowsFiniteGroupCard ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by
      rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_pow, pow_mul _ (D.R.r * D.R.r),
        pow_mul _ (D.R.r * D.R.r)]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 0)) _)
        (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 1)) _)
    have hc' : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤
        ((D.host.g 0 : ℝ) * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by exact_mod_cast hc
    have hp : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos
    have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast hgpos 0
    have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast hgpos 1
    have hr5 : (D.R.r : ℝ) ≤ 2 * x ^ (5 : ℝ) := by linarith
    unfold lam0
    refine (Real.log_le_log hp hc').trans ?_
    rw [Real.log_pow, Real.log_mul hg0.ne' hg1.ne']
    push_cast
    have hl0 : 0 ≤ Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
      add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    have hl2 : Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) ≤ 2 * x := by
      linarith [hlog 0, hlog 1]
    have e5 : x ^ (5 : ℝ) = x ^ 5 := by exact_mod_cast Real.rpow_natCast x 5
    have e3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
    have e15 : x ^ (15 : ℝ) = x ^ 15 := by exact_mod_cast Real.rpow_natCast x 15
    rw [e5] at hr5
    rw [e3] at hf
    rw [e15]
    calc (D.R.r : ℝ) * D.R.r * D.R.f * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ))
        ≤ (2 * x ^ 5) * (2 * x ^ 5) * x ^ 3 * (2 * x) := by gcongr
      _ = 8 * x ^ 14 := by ring
      _ ≤ x * x ^ 14 := by gcongr
      _ = x ^ 15 := by ring
  · have hmin : (D.R.k : ℝ) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
      push_cast
      exact le_min (hg8 0) (hg8 1)
    rw [div_le_iff₀ (lt_of_lt_of_le hkpos hmin)]
    have h1 : 8 * (D.R.f : ℝ) * D.R.r ≤ 8 * (D.R.k : ℝ) * (2 * D.R.k) := by gcongr
    have h2 : (5 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 6 := by gcongr
    have h3 : (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by ring
    have h4 : (5 : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (D.R.k : ℝ)]

end GlobalTheory
end
