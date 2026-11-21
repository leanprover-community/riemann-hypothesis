import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfGram
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe

section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

private theorem isLocPt_and_ptG_pos_of_vec_ne_zero {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : p.V G Q ≠ 0) :
    D.IsLocPt Q (P.r + 1) ∧ 0 < D.ptG (TBB.TTp p) P.r Q := by
  by_contra hn
  exact hQ (by unfold KB.Pl.V D.vecV; exact dif_neg hn)

private theorem vecV_eq_zero_of_not_isLocPt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : ¬ D.IsLocPt Q (P.r + 1)) :
    D.vecV p.T.base p.ν' p.m₀ G Q = 0 := by
  unfold D.vecV
  exact dif_neg fun hh => hQ hh.1

private theorem hsInner_zero_left_right_and_hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X : Wq →L[ℂ] Wp) :
    B.hsInner 0 X = 0 ∧ B.hsInner X 0 = 0 ∧ B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    rfl
  unfold B.hsInner
  rw [h0]
  exact ⟨inner_zero_right _, inner_zero_left _, rfl⟩

private theorem rr_succ_eq_ite_hsInner_else_leading {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Q Q' : C.LPt) :
    p.RR F (P.r + 1) w Q Q' =
      if w = [] then B.hsInner (p.V F Q) (p.V F Q')
      else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w Q Q' := by
  unfold KB.Pl.RR D.RRplace
  by_cases hl : D.IsLocPt Q (P.r + 1) ∧ D.IsLocPt Q' (P.r + 1)
  · rw [dif_pos hl, dif_neg (by omega), if_pos rfl]
    rfl
  · rw [dif_neg hl]
    have hz : ∀ G : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
        D.vecV p.T.base p.ν' p.m₀ G Q = 0 ∨ D.vecV p.T.base p.ν' p.m₀ G Q' = 0 := by
      intro G
      rcases not_and_or.mp hl with h | h
      · exact Or.inl (vecV_eq_zero_of_not_isLocPt p G Q h)
      · exact Or.inr (vecV_eq_zero_of_not_isLocPt p G Q' h)
    split_ifs with hw
    · rcases hz F with h | h
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).1]
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).2.1]
    · unfold Top.topOf
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rcases hz (p.Θ.Θ w e F) with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, mul_zero]
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, mul_zero]

theorem top_level_gram : TopGram1 := by
  intro Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw hnn
  have hnc : 0 < TBB.normC nn w := by
    unfold TBB.normC
    apply List.prod_pos
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    exact hnn l.2
  by_cases hw0 : w = []
  · subst hw0
    refine ⟨Unit, inferInstance, fun _ => 1 / TBB.normC nn [], fun _ => F,
      fun _ => GermRateSplit.hsLE (ContinuousLinearMap.id ℂ Wp), fun _ => by positivity, fun _ => hF, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_pos rfl, Fintype.sum_unique, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.id_comp, List.length_nil, omT, pow_zero, Real.sqrt_one, mul_one]
    unfold B.hsInner
    push_cast
    ring
  · have hT : ∀ e : Wd.Ix (Fin w.length), ∃ F', KB.CptCoef p.T.base F' ∧
        (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧ ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a :=
      fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw
    choose G hG _ hGV using hT
    refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance,
      fun i => √(Top.cW P p.l0 w i.1 i.2).re * √(Top.cW P p.l0 w i.1 i.2).re / TBB.normC nn w,
      fun i => G i.1, fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => by positivity, fun i => hG i.1, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_neg hw0]
    unfold Top.topOf
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hV : ∀ a, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) a = p.V (G e) a := hGV e
    rw [hV, hV, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    have key : ∀ R : C.LPt, p.V (G e) R ≠ 0 →
        √(TBB.nPt P.k P.r (TBB.TTp p) R) *
            Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w R e ρ =
          omT p w.length R * √(Top.cW P p.l0 w e ρ).re := by
      intro R hR
      have hpos := (isLocPt_and_ptG_pos_of_vec_ne_zero p (G e) R hR).2
      have hwp : 0 ≤ Top.wPt (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r R :=
        div_nonneg (Complex.normSq_nonneg _) hpos.le
      unfold Top.dH omT
      rw [Real.sqrt_mul (pow_nonneg hwp _)]
      unfold TBB.TTp
      ring
    by_cases hz : p.V (G e) Q = 0 ∨ p.V (G e) Q' = 0
    · rcases hz with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_right]
        simp
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_left]
        simp
    · push Not at hz
      have hreal : √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') /
            TBB.normC nn w *
            (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
              Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
          √(Top.cW P p.l0 w e ρ).re * √(Top.cW P p.l0 w e ρ).re / TBB.normC nn w *
            (omT p w.length Q' * omT p w.length Q) := by
        rw [div_mul_eq_mul_div,
          show √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') *
              (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q) *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ) *
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q') *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) by ring,
          key Q hz.1, key Q' hz.2]
        ring
      unfold B.hsInner
      have hc := congrArg (fun x : ℝ => (x : ℂ) *
        inner ℂ (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q'))) (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q)))) hreal
      push_cast at hc ⊢
      linear_combination hc

private theorem continuousAt_omT_append_last_of_ptG_pos {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N m : ℕ) (h : C.LPt) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hG : 0 < D.ptG (TBB.TTp p) P.r (h ++ [(m, c0)])) :
    ContinuousAt (fun c : ℂ => omT p N (h ++ [(m, c)])) c0 := by
  have hgg : (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) =
      fun c => (Complex.normSq c - TBB.TTp p, c) := by
    funext c
    simp [D.ptGG, D.ptLast]
  have hn : ContinuousAt (fun c : ℂ => TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m, c)])) c0 := by
    have h1 := (LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m h 1).continuousAt
      (x := (D.ptGG (TBB.TTp p) (h ++ [(m, c0)]), c0))
      ((isOpen_univ.prod isOpen_compl_singleton).mem_nhds ⟨trivial, hc0⟩)
    have h2 : ContinuousAt (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) c0 := by
      rw [hgg]
      exact ((Complex.continuous_normSq.sub continuous_const).prodMk continuous_id).continuousAt
    exact h1.comp (f := fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) h2
  have hw : ContinuousAt (fun c : ℂ => Top.wPt (TBB.TTp p) P.r (h ++ [(m, c)])) c0 := by
    unfold Top.wPt
    exact (Complex.continuous_normSq.comp (LastBlockContinuity.ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt.div
      (LastBlockContinuity.ptG_cont (TBB.TTp p) P.r h m).continuousAt hG.ne'
  unfold omT
  exact (hn.sqrt).mul ((hw.pow N).sqrt)

theorem top_level_Y_continuity : YCont := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF N m h hh hm hsz c0 hc0
  have hc0' : c0 ≠ 0 := hc0
  have hA := LastBlockContinuity.smulV_continuousAt P p F' hF h hh m hm hsz (fun c => omT p N (h ++ [(m, c)]))
    (ContinuousLinearMap.id ℂ Wp) c0 hc0' (fun hG => continuousAt_omT_append_last_of_ptG_pos p N m h c0 hc0' hG)
  simp only [ContinuousLinearMap.id_comp] at hA
  exact hA.continuousWithinAt

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.GermRateSplit Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def l1T (m : ℕ) : ℂ := (-1) ^ (m + 3) / Complex.I ^ (m + 2)

def l2T (m : ℕ) : ℂ := Complex.I * l1T m

theorem norm_l1T (m : ℕ) : ‖l1T m‖ = 1 := by
  simp [l1T]

theorem top_base_ne_zero (m : ℕ) : l1T m ≠ 0 := by
  intro h
  simpa [h] using norm_l1T m

theorem norm_l2T (m : ℕ) : ‖l2T m‖ = 1 := by
  rw [l2T, norm_mul, Complex.norm_I, norm_l1T, one_mul]

theorem top_root_ne_zero (m : ℕ) : l2T m ≠ 0 := by
  intro h
  simpa [h] using norm_l2T m

theorem top_root_pow_eq (m : ℕ) : l2T m ^ (m + 2) = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by
  have hI : Complex.I ^ (m + 2) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h1 : Complex.I ^ (m + 2) * l1T m = (-1) ^ (m + 3) := by
    rw [l1T, mul_div_cancel₀ _ hI]
  calc l2T m ^ (m + 2) = (Complex.I ^ (m + 2) * l1T m) * l1T m ^ (m + 1) := by
        rw [l2T]
        ring
    _ = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by rw [h1]

theorem psi_l (m : ℕ) (w : ℂ) : G.psi U.betaU (l2T m / l1T m * w) = conj (G.psi ((2 : ℝ) : ℂ) w) := by
  have hl : l2T m / l1T m = Complex.I := by
    rw [l2T, mul_div_assoc, div_self (top_base_ne_zero m), mul_one]
  have key : U.betaU * (Complex.I * w) = -(((2 : ℝ) : ℂ) * w) := by
    simp only [U.betaU, Formalism.QuantumDeterminants.cStd]
    push_cast
    linear_combination (2 * w) * Complex.I_sq
  rw [hl, G.psi, G.psi, key, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem const_match1 (k r : ℕ) (TT : ℝ) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = r + 2) (hk : 1 ≤ k)
    (h : C.LPt) (hsz : D.ptSize h = b - 1) :
    ∃ Kh : ℝ,
      (∀ x D : ℂ, x ≠ 0 → D ≠ 0 →
        ‖x‖ ^ (s - 1) * √(TBB.nPt k r TT (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) *
            (qU ^ ((s - 1) + (Fintype.card (G.UT (s - 1)) + (s - 1))))⁻¹ =
          Kh * ‖D‖ ^ (k - 1) * ‖x⁻¹‖ ^ ((s - 1) ^ 2) *
            (√((Complex.normSq (x ^ (s - 1) * D) - TT) ^ (k - 1)) / ‖x ^ (s - 1) * D‖ ^ (k - 1))) ∧
      (∀ u : ℂ, u ≠ 0 →
        Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ * √(TBB.nPt k r TT (h ++ [(s, u)])) *
            (qU ^ Fintype.card (G.UT s))⁻¹ =
          Kh * ‖u ^ s‖ ^ (k - 1) * ((s : ℝ)⁻¹ * ‖u‖ ^ ((s - 1) ^ 2))) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain rfl : r = c + m + 1 := by omega
  rw [show c + 1 - 1 = c by omega] at hsz
  rw [show m + 2 - 1 = m + 1 by omega, show k' + 1 - 1 = k' by omega]
  have hsing : ∀ (GG : ℝ) (bb ss : ℕ) (t : ℂ), C.nAux (k' + 1) (c + m + 1) GG (fun _ _ => 1) bb [(ss, t)] =
      (if bb + ss - 1 = c + m + 1 + 1 ∧ ss = 1 then GG ^ (k' + 1 - 1)
        else ((1 : ℝ) * ‖t‖) ^ (2 * (ss : ℤ) * (C.Mlev (k' + 1) (c + m + 1) (bb + ss - 1) + ss - 3))) := by
    intro GG bb ss t
    simp only [C.nAux, mul_one]
  have hpos : ∀ (l : C.LPt) (bb : ℕ), 0 ≤ C.nAux (k' + 1) (c + m + 1) 0 (fun _ _ => 1) bb l := by
    intro l
    induction l with
    | nil => intro bb; simp [C.nAux]
    | cons a l ih =>
      intro bb
      obtain ⟨ss, t⟩ := a
      simp only [C.nAux]
      refine mul_nonneg ?_ (ih _)
      split_ifs
      · positivity
      · exact zpow_nonneg (by positivity) _
  set N : ℝ := C.nAux (k' + 1) (c + m + 1) 0 (fun _ _ => 1) 1 h with hNdef
  have hN0 : 0 ≤ N := hpos h 1
  have hind : ∀ GG : ℝ, C.nAux (k' + 1) (c + m + 1) GG (fun _ _ => 1) 1 h = N := fun GG =>
    PBD.weight_product_indep_of_real_parameter _ _ GG 0 _ h 1 le_rfl (by rw [hsz]; omega)
  have hq : qU ≠ 0 := by rw [qU_eq]; positivity
  have hcard : Fintype.card (G.UT (m + 2)) = Fintype.card (G.UT (m + 1)) + (m + 1) := by
    rw [G5.card_UT, G5.card_UT, Finset.sum_range_succ]
  refine ⟨√N * (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹, fun x d0 hx hD => ?_,
    fun u hu => ?_⟩
  · have hL : h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)] =
        (h ++ [(m + 1, x⁻¹)]) ++ [(1, x ^ (m + 1) * d0)] := by simp
    have hGG : FourierDecayAlt.D.ptGG TT (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)]) =
        Complex.normSq (x ^ (m + 1) * d0) - TT := by
      simp [FourierDecayAlt.D.ptGG, FourierDecayAlt.D.ptLast]
    have hsz2 : FourierDecayAlt.D.ptSize (h ++ [(m + 1, x⁻¹)]) = c + (m + 1) := by
      simp [FourierDecayAlt.D.ptSize] at hsz ⊢
      omega
    have hn : TBB.nPt (k' + 1) (c + m + 1) TT (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d0)]) =
        N * ‖x‖⁻¹ ^ (((m + 1) * (k' + m + 2)) * 2) * (Complex.normSq (x ^ (m + 1) * d0) - TT) ^ k' := by
      rw [TBB.nPt, hGG, hL, PBD.weight_product_append, PBD.weight_product_append, hind, hsz, hsz2, hsing, hsing]
      rw [if_neg (show ¬(1 + c + (m + 1) - 1 = c + m + 1 + 1 ∧ m + 1 = 1) by omega),
        if_pos (show 1 + (c + (m + 1)) + 1 - 1 = c + m + 1 + 1 ∧ 1 = 1 by omega),
        one_mul, norm_inv, show k' + 1 - 1 = k' by omega, ← zpow_natCast (‖x‖⁻¹)]
      congr 3
      simp only [C.Mlev]
      push_cast [Nat.cast_sub (show 1 ≤ 1 + c + (m + 1) by omega)]
      ring
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hD' : ‖d0‖ ≠ 0 := norm_ne_zero_iff.2 hD
    rw [hn, Real.sqrt_mul (mul_nonneg hN0 (by positivity)), Real.sqrt_mul hN0, pow_mul,
      Real.sqrt_sq (by positivity), norm_inv, norm_mul, norm_pow, mul_pow]
    simp only [inv_pow, inv_inv]
    field_simp
    ring
  · have hsz3 : FourierDecayAlt.D.ptSize h = c := hsz
    have hn : TBB.nPt (k' + 1) (c + m + 1) TT (h ++ [(m + 2, u)]) =
        N * ‖u‖ ^ (((m + 2) * (k' + m + 1)) * 2) := by
      rw [TBB.nPt, PBD.weight_product_append, hind, hsz3, hsing,
        if_neg (show ¬(1 + c + (m + 2) - 1 = c + m + 1 + 1 ∧ m + 2 = 1) by omega),
        one_mul, ← zpow_natCast (‖u‖)]
      congr 2
      simp only [C.Mlev]
      push_cast [Nat.cast_sub (show 1 ≤ 1 + c + (m + 2) by omega)]
      ring
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    rw [hn, Real.sqrt_mul hN0, pow_mul, Real.sqrt_sq (by positivity), norm_pow, hcard, qU_eq]
    simp only [inv_pow, inv_inv]
    field_simp
    ring

section core

theorem top_level_germ_leading : TopCore1 := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF' N b s hb hs hbs h hh K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hszH : D.ptSize h = b - 1 := hh.2
  have hk : 1 ≤ P.k := by have := p.hl.2.2; omega
  have hTT : 0 < TBB.TTp p := mul_pos p.T.base.T_pos p.T.base.T'_pos
  obtain ⟨ε0, hε0, hεG⟩ := hF'.2.2
  have hsmall : ∀ q : C.LPt, p.V F' q ≠ 0 → ε0 ≤ D.ptG (TBB.TTp p) P.r q := by
    intro q hq
    by_contra hlt
    exact hq (PBO.vecV_zero_small p.T.base p.ν' p.m₀ hεG q (not_le.1 hlt))
  obtain ⟨Φ0, hΦs, hΦc, hΦd, hΦV⟩ := phi_zero_hermitian_curvature Wp Wq P p F' hF'
  obtain ⟨σh, dh, Ψ0, hdh, hΨ0, hblk, hlng⟩ :=
    vec_om (p.V F') Φ0 ⟨hΦs, hΦc, hΦd⟩ (fun a σ d ha hm => hΦV a σ d ha hm) h hh.1 m (by omega)
  have hlng' : ∀ z : ℂ, z ≠ 0 → p.V F' (h ++ [(m + 2, z)]) =
      (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (z) := hlng
  have hqE : ∀ n : ℕ, (((qU ^ n)⁻¹ : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (inv_pos.2 (pow_pos qU_pos n)).ne'
  obtain ⟨Kh, hc1, hc2⟩ := const_match1 P.k P.r (TBB.TTp p) b (m + 2) hb hs hbs hk h hszH
  rw [show m + 2 - 1 = m + 1 by omega] at hc1 hc2
  set K' : Set ℂ := (fun d => d / l1T m ^ (m + 1)) '' K with hK'def
  have hK' : IsCompact K' := hK.image (continuous_id.div_const _)
  have hK'0 : (0 : ℂ) ∉ K' := by
    rintro ⟨d, hd, hd0⟩
    have : d = 0 := by simpa [top_base_ne_zero m] using hd0
    exact hK0 (this ▸ hd)
  obtain ⟨MK, hMK⟩ := hK'.isBounded.exists_norm_le
  obtain ⟨mK, hmK, hball⟩ := Metric.isOpen_iff.1 hK'.isClosed.isOpen_compl 0 hK'0
  have hmKle : ∀ y ∈ K', mK ≤ ‖y‖ := by
    intro y hy
    by_contra hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using not_le.1 hlt) hy
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ → ℂ → ℝ, ∀ x y : ℂ, ρ x y =
      √((Complex.normSq (x ^ (m + 1) * y) - TBB.TTp p) ^ (P.k - 1)) / ‖x ^ (m + 1) * y‖ ^ (P.k - 1) *
        √((Complex.normSq (x ^ (m + 1) * y) / (Complex.normSq (x ^ (m + 1) * y) - TBB.TTp p)) ^ N) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨C0, hC0⟩ := germ_core m (D.ptSize h) σh dh hdh Ψ0 hΨ0 (l1T m) (l2T m) (top_base_ne_zero m) (top_root_pow_eq m) 2
    (psi_l m) K' hK' hK'0 ρ (√(((ε0 / (max (Complex.normSq (D.ptMatN h (D.ptSize h)).det) 1 * ‖l1T m‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N))
    ((((P.k - 1 : ℕ) : ℝ) + N * ((ε0 / (max (Complex.normSq (D.ptMatN h (D.ptSize h)).det) 1 * ‖l1T m‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) * (TBB.TTp p / mK ^ 2)) (by
      intro x' y hx' hy hne
      have hy0 : y ≠ 0 := fun h0 => hK'0 (h0 ▸ hy)
      have ht0 : l1T m * x'⁻¹ ≠ 0 := mul_ne_zero (top_base_ne_zero m) (inv_ne_zero hx')
      have hc0 : x' ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx') hy0
      have hV : p.V F' (h ++ [(m + 1, l1T m * x'⁻¹), (1, x' ^ (m + 1) * y)]) ≠ 0 := by
        rw [hblk _ _ ht0 hc0]
        exact smul_ne_zero (hqE _) hne
      have hG := hsmall _ hV
      rw [ptG_Px (TBB.TTp p) h (m + 1) (by omega) P.r (by omega)] at hG
      have hnc : Complex.normSq (x' ^ (m + 1) * y) = ‖x'‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2 := by
        rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_pow]
        ring
      rw [hρdef]
      exact rho_bound (TBB.TTp p) ε0 (Complex.normSq (D.ptMatN h (D.ptSize h)).det) MK mK hTT hε0
        (Complex.normSq_nonneg _) hmK (P.k - 1) N m (l1T m) x' y (x' ^ (m + 1) * y) (top_base_ne_zero m) hx' hy0 hc0
        (hMK y hy) (hmKle y hy) hnc hG)
  obtain ⟨MD, hMD⟩ := hK.isBounded.exists_norm_le
  refine ⟨|Kh| * (max MD 1) ^ (P.k - 1) * C0, fun x hx d hd => ?_⟩
  have hd0 : d ≠ 0 := fun h0 => hK0 (h0 ▸ hd)
  have hx1 : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hcne : x ^ (m + 1) * d ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hd0
  have ht : l1T m * (l1T m * x)⁻¹ = x⁻¹ := by field_simp [top_base_ne_zero m]
  have hcx : (l1T m * x) ^ (m + 1) * (d / l1T m ^ (m + 1)) = x ^ (m + 1) * d := by
    field_simp [top_base_ne_zero m]
    ring
  have hnx : ‖l1T m * x‖ = ‖x‖ := by rw [norm_mul, norm_l1T, one_mul]
  have hgerm := hC0 (l1T m * x) (mul_ne_zero (top_base_ne_zero m) hx) (d / l1T m ^ (m + 1)) ⟨d, hd, rfl⟩
  rw [ht, hcx, hnx] at hgerm
  have hT0 : (coT (m + 2) x none * (omT p N (ptT (m + 2) h x d none) : ℂ)) • p.V F' (ptT (m + 2) h x d none) =
      ((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) •
        G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d)) := by
    show (((‖x‖ ^ (m + 1) : ℝ) : ℂ) * (omT p N (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) : ℂ)) •
        p.V F' (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) = _
    by_cases hB : G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) = 0
    · rw [hblk _ _ hx1 hcne, hB]
      simp
    have hV : p.V F' (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)]) ≠ 0 := by
      rw [hblk _ _ hx1 hcne]
      exact smul_ne_zero (hqE _) hB
    have hG := hsmall _ hV
    have hw := wPt_Px (TBB.TTp p) h (m + 1) (by omega) P.r (by omega) x⁻¹ (x ^ (m + 1) * d)
      (lt_of_lt_of_le hε0 hG).ne'
    have e1 := hc1 x d hx hd0
    have hreal : ‖x‖ ^ (m + 1) * (√(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * d)])) *
          √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N)) *
          (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹ =
        Kh * ‖d‖ ^ (P.k - 1) * (‖x⁻¹‖ ^ ((m + 1) ^ 2) *
          (√((Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p) ^ (P.k - 1)) / ‖x ^ (m + 1) * d‖ ^ (P.k - 1) *
            √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N))) := by
      linear_combination √((Complex.normSq (x ^ (m + 1) * d) / (Complex.normSq (x ^ (m + 1) * d) - TBB.TTp p)) ^ N) * e1
    rw [hblk _ _ hx1 hcne, smul_smul, smul_smul, hρdef, hcx]
    congr 1
    simp only [omT, hw]
    exact_mod_cast hreal
  have hroots : G.rootSet (m + 2) (epsT (m + 2) * d) = (G.rootSet (m + 2) (d / l1T m ^ (m + 1))).image (fun z => l2T m * z) := by
    ext z
    simp only [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots (show 0 < m + 2 by omega),
      Finset.mem_image]
    have hm1 : ((-1 : ℂ)) ^ (m + 3) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    constructor
    · intro hz
      refine ⟨z / l2T m, ?_, by field_simp [top_root_ne_zero m]⟩
      rw [div_pow, hz, top_root_pow_eq, epsT]
      field_simp [top_base_ne_zero m]
      try ring
    · rintro ⟨w, hw, rfl⟩
      rw [mul_pow, top_root_pow_eq, hw, epsT]
      field_simp [top_base_ne_zero m]
      try ring
  have hsum : ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)), (coT (m + 2) x (some (l2T m * z)) *
        (omT p N (ptT (m + 2) h x d (some (l2T m * z))) : ℂ)) • p.V F' (ptT (m + 2) h x d (some (l2T m * z))) =
      -(((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
        (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z))) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z ^ (m + 2) = d / l1T m ^ (m + 1) :=
      (Polynomial.mem_nthRoots (show 0 < m + 2 by omega)).1 (Multiset.mem_toFinset.1 hz)
    have hd' : d / l1T m ^ (m + 1) ≠ 0 := div_ne_zero hd0 (pow_ne_zero _ (top_base_ne_zero m))
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz'
      exact hd' hz'.symm
    have hu : l2T m * z ≠ 0 := mul_ne_zero (top_root_ne_zero m) hz0
    have hud : ‖(l2T m * z) ^ (m + 2)‖ = ‖d‖ := by
      rw [mul_pow, top_root_pow_eq, hz']
      simp [norm_l1T]
    show (-(G.psi U.betaU (((m + 2 : ℕ) : ℂ) * (l2T m * z) * x) *
        ((Real.pi ^ (m + 1) * (((m + 2 : ℕ) : ℝ) * ‖l2T m * z‖ ^ (m + 1))⁻¹ : ℝ) : ℂ)) *
        (omT p N (h ++ [(m + 2, l2T m * z)]) : ℂ)) • p.V F' (h ++ [(m + 2, l2T m * z)]) = _
    by_cases hL : G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z) = 0
    · rw [hlng' _ hu, hL]
      simp
    have hV : p.V F' (h ++ [(m + 2, l2T m * z)]) ≠ 0 := by
      rw [hlng' _ hu]
      exact smul_ne_zero (hqE _) hL
    have hG := hsmall _ hV
    have hw := PBL.wPt_big (TBB.TTp p) h (m + 2) (l2T m * z) P.r (by omega) (by omega)
      (lt_of_lt_of_le hε0 hG)
    have hpsi : G.psi U.betaU (((m + 2 : ℕ) : ℂ) * (l2T m * z) * x) =
        conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x))) := by
      rw [← psi_l m]
      congr 1
      field_simp [top_base_ne_zero m]
      push_cast
      ring
    have e2 := hc2 (l2T m * z) hu
    rw [hud] at e2
    have e2c := congrArg (fun t : ℝ => (t : ℂ)) e2
    rw [hlng' _ hu, smul_smul, smul_smul, smul_smul, ← neg_smul]
    congr 1
    simp only [omT, hw, one_pow, Real.sqrt_one, mul_one, hpsi]
    push_cast at e2c ⊢
    linear_combination (-conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) * e2c
  have heq : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) (epsT (m + 2) * d)),
      (coT (m + 2) x j * (omT p N (ptT (m + 2) h x d j) : ℂ)) • p.V F' (ptT (m + 2) h x d j) =
      ((Kh * ‖d‖ ^ (P.k - 1) : ℝ) : ℂ) • (((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) -
          ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
            (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
              G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z)) := by
    rw [Finset.sum_insertNone, hroots,
      Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ (top_root_ne_zero m) hab)]
    beta_reduce
    rw [hT0, hsum, smul_sub, sub_eq_add_neg]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hdle : ‖d‖ ^ (P.k - 1) ≤ (max MD 1) ^ (P.k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ((hMD d hd).trans (le_max_left _ _)) _
  have h0 : 0 ≤ C0 * ‖x‖⁻¹ := (norm_nonneg _).trans hgerm
  calc |Kh| * ‖d‖ ^ (P.k - 1) * ‖(((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ (l1T m * x) (d / l1T m ^ (m + 1)) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (x⁻¹) (x ^ (m + 1) * d) -
          ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) (d / l1T m ^ (m + 1)),
            (((‖l2T m * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi ((2 : ℝ) : ℂ) (((m : ℂ) + 2) * z * (l1T m * x)))) •
              G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize h) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2T m * z))‖
      ≤ |Kh| * (max MD 1) ^ (P.k - 1) * (C0 * ‖x‖⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdle (abs_nonneg _)) hgerm (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))
    _ = |Kh| * (max MD 1) ^ (P.k - 1) * C0 * ‖x‖⁻¹ := by ring

end core

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem norm_sum_le_of_gram' {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (v : ι → H) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, ⟪v (P j), v (P l)⟫_ℂ = ∑ i, (c i : ℂ) * ⟪Y i (P j), Y i (P l)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, a j • Y i (P j)‖ := by
  set u := ∑ j ∈ J, a j • v (P j) with hu
  set y : I → W := fun i => ∑ j ∈ J, a j • Y i (P j) with hy
  have hinner : ⟪u, u⟫_ℂ = ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ := by
    have e1 : ⟪u, u⟫_ℂ = ∑ j ∈ J, ∑ l ∈ J, ∑ i,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      show ⟪∑ j ∈ J, a j • v (P j), ∑ j ∈ J, a j • v (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
      rw [hk j hj l hl, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e2 : ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ = ∑ i, ∑ j ∈ J, ∑ l ∈ J,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      show (c i : ℂ) * ⟪∑ j ∈ J, a j • Y i (P j), ∑ j ∈ J, a j • Y i (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [e1, e2]
    calc _ = ∑ j ∈ J, ∑ i, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hsq : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E), ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    intro E _ _ x
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hle : ‖u‖ ^ 2 ≤ ∑ i, (√(c i) * ‖y i‖) ^ 2 := by
    rw [← hsq u, hinner]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, hsq, mul_pow, Real.sq_sqrt (hc i), Complex.norm_real, Real.norm_of_nonneg (hc i)]
  have hsum : ∑ i, (√(c i) * ‖y i‖) ^ 2 ≤ (∑ i, √(c i) * ‖y i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnn : 0 ≤ ∑ i, √(c i) * ‖y i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((∑ i, √(c i) * ‖y i‖) ^ 2) := Real.sqrt_le_sqrt (hle.trans hsum)
    _ = ∑ i, √(c i) * ‖y i‖ := Real.sqrt_sq hnn

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

theorem cvec_utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x : ℂ) (hx : x ≠ 0) (cc : ℂ) :
    PBK.cvec s (utT p N c Fi L s h) x cc = vecT p N c Fi L ((h ++ [(s - 1, x⁻¹)]) ++ [(1, cc)]) := by
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
    Complex.ofReal_one, one_smul]
  simp

theorem inner_vecT_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq)
    (hV : VecHyp p nn F w c Fi L) (Q Q' : C.LPt) :
    ⟪vecT p w.length c Fi L Q, vecT p w.length c Fi L Q'⟫_ℂ = TBB.NP p nn F (P.r + 1) w Q' Q := by
  rw [inner_vecT p w.length c hV.hc Fi L Q Q', hV.gram Q' Q]

end place

theorem germDataTopAll_of_parts (hTG : TopGram1) (hTC : TopCore1) (hFT : FibreTop) (hYC : YCont)
    (hMU : FieldMemU) (hSU : FieldSup) (hME : FieldMeas) (hLO : FieldLoc) : GermDataTopAll := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn
  intro b s hb hs hbs hlev h hh w hw hN hBdd
  have hbs' : b + s = P.r + 2 := by omega
  have hr2 : b + s - 2 = P.r := by omega
  have hr1 : b + s - 1 = P.r + 1 := by omega
  obtain ⟨I, _, c, Fi, L, hc, hFi, hgram⟩ := hTG Wp Wq P p nn F w Cb hCb hF hw.1 hnn
  have hFib := hFT hA Wp Wq P p nn F w Cb hCb hF hw.1
  have hV : VecHyp p nn F w c Fi L :=
    { hc := hc, hFi := hFi, gram := hgram, int := fun a ha => (hFib a a ha ha).1,
      fibre := fun a a' ha ha' => (hFib a a' ha ha').2,
      cont := fun i m h' hh' hm hsz => hYC Wp Wq P p (Fi i) (hFi i) w.length m h' hh' hm hsz }
  obtain ⟨SS, hSS⟩ := hBdd w (TBBx5.isExt_self P p.l0 Y N K w hw (by omega))
  have hs0 : s ≠ 0 := by omega
  have hsz : D.ptSize h = b - 1 := hh.2

  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) P.r := by
    intro t ht
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.1 hq with hq | hq
      · exact hh.1 q hq
      · simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨by simp only; omega, ht⟩
    · have e : D.ptSize (h ++ [(s - 1, t)]) = D.ptSize h + (s - 1) := by simp [D.ptSize]
      rw [e, hsz]
      omega
  set ut := utT p w.length c Fi L s h with hut
  set bt := btT p w.length c Fi L s h with hbt
  have hpi : (1 : ℝ) ≤ Real.pi ^ (s - 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  refine ⟨HT I Wp Wq, inferInstance, inferInstance, inferInstance, ut, bt, U.betaU, epsT s, -1, SS, 1,
    ((Real.pi ^ (s - 1))⁻¹) ^ 2, by positivity, ?_, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : ((Real.pi ^ (s - 1))⁻¹) ^ 2 ≤ 1 := by
      have : (Real.pi ^ (s - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
      have h0 : 0 ≤ (Real.pi ^ (s - 1))⁻¹ := by positivity
      nlinarith
    linarith [Real.pi_gt_three]
  ·
    refine ⟨hs0, Formalism.FourierDecayAlt.P.scale_matching.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [epsT]
    · intro _ _ x hx
      exact hMU p nn F w c Fi L hV b s hb hs hbs' h hh x hx
    · intro _ _ x hx
      rw [hSU p nn F w c Fi L hV b s hb hs hbs' h hh x hx]
      have := hSS ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      simp only at this
      rwa [hr2] at this
    · intro _ _
      exact hME p nn F w c Fi L hV b s hb hs hbs' h hh
    · intro _ _ K' hK' hK0
      exact hLO p nn F w c Fi L hV b s hb hs hbs' h hh K' hK' hK0
    · intro _ _ K' hK' hK0
      choose Ci hCi using fun i => hTC Wp Wq P p (Fi i) (hFi i) w.length b s hb hs hbs' h hh K' hK' hK0
      refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      have heD : epsT s * D ≠ 0 := mul_ne_zero (by simp [epsT]) hD0
      have hroot : ∀ z ∈ G.rootSet s (epsT s * D), z ≠ 0 := by
        intro z hz h0
        unfold G.rootSet at hz
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
        rw [h0, zero_pow hs0] at hz
        exact heD hz.symm

      have hsum : ut x D - PBK.mainD s U.betaU (epsT s) bt x D =
          ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), coT s x j • vecT p w.length c Fi L (ptT s h x D j) := by
        rw [Finset.sum_insertNone, sub_eq_add_neg]
        refine congrArg₂ (· + ·) rfl ?_
        · unfold PBK.mainD
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun z hzm => ?_
          simp only [hbt, btT, if_neg (hroot z hzm), coT, ptT, smul_smul, neg_smul, neg_mul]
      rw [hsum]
      have hk : ∀ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), ∀ l ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          ⟪vecT p w.length c Fi L (ptT s h x D j), vecT p w.length c Fi L (ptT s h x D l)⟫_ℂ =
            ∑ i, (c i : ℂ) * ⟪(omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j)),
              (omT p w.length (ptT s h x D l) : ℂ) • L i (p.V (Fi i) (ptT s h x D l))⟫_ℂ :=
        fun j _ l _ => inner_vecT p w.length c hc Fi L _ _
      refine (norm_sum_le_of_gram' (vecT p w.length c Fi L) c hc
        (fun i Q => (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)) _ (ptT s h x D) hk (coT s x)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have e : ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          coT s x j • ((omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j))) =
          L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_smul]
      rw [e]
      have h3 := hCi i x hx D hD
      have hsq := Real.sqrt_nonneg (c i)
      calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j))‖
          ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
        _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
        _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring
  ·
    intro σ z
    have hbU : U.betaU = 2 * Complex.I := by
      unfold U.betaU Formalism.QuantumDeterminants.cStd; ring
    unfold P5.fsv G.psi
    rw [hbU]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  ·
    intro t t' ht ht'
    have hx : t⁻¹ ≠ 0 := inv_ne_zero ht
    have hx' : t'⁻¹ ≠ 0 := inv_ne_zero ht'
    have hg : PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹) =
        ∫ cc : ℂ, TBB.NP p nn F (P.r + 1) w ((h ++ [(s - 1, t')]) ++ [(1, cc)]) ((h ++ [(s - 1, t)]) ++ [(1, cc)]) := by
      unfold PBK.gramL PBK.Uc
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only [hut]
      rw [cvec_utT p w.length c Fi L s h _ hx, cvec_utT p w.length c Fi L s h _ hx', inv_inv, inv_inv,
        inner_vecT_np p nn F w c Fi L hV]
    have hn : TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]) =
        conj (PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹)) := by
      rw [hg, hr2, hV.fibre _ _ (hloc t ht) (hloc t' ht'), ← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only
      rw [← inner_vecT_np p nn F w c Fi L hV, ← inner_vecT_np p nn F w c Fi L hV, inner_conj_symm]
    rw [hn, RCLike.norm_conj, one_mul]
  ·
    intro z hz
    have hQ : TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = ‖vecT p w.length c Fi L (h ++ [(s, z)])‖ ^ 2 := by
      unfold TBB.Ew
      rw [hr1, ← inner_vecT_np p nn F w c Fi L hV, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hbz : PBK.bz s bt z = ((Real.pi ^ (s - 1) : ℝ) : ℂ) • vecT p w.length c Fi L (h ++ [(s, z)]) := by
      simp only [PBK.bz, hbt, btT, if_neg hz, smul_smul, ← Complex.ofReal_mul]
      congr 2
      have hpos : (0 : ℝ) < (s : ℝ) * ‖z‖ ^ (s - 1) := by
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      field_simp
    rw [hQ, hbz, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

theorem vecT_cont (hV : VecHyp p nn F w c Fi L) {h : C.LPt} (hh : ∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) :
    ContinuousOn (fun z : ℂ => vecT p w.length c Fi L (h ++ [(m, z)])) {0}ᶜ := by
  have hcomp : ∀ i, ContinuousOn (fun z : ℂ =>
      ((√(c i) * omT p w.length (h ++ [(m, z)]) : ℝ) : ℂ) • L i (p.V (Fi i) (h ++ [(m, z)]))) {0}ᶜ := by
    intro i
    have := ((L i).continuous.comp_continuousOn (hV.cont i m h hh hm hsz)).const_smul ((√(c i) : ℝ) : ℂ)
    refine this.congr fun z _ => ?_
    show _ = (((√(c i) : ℝ) : ℂ)) • L i ((omT p w.length (h ++ [(m, z)]) : ℂ) • p.V (Fi i) (h ++ [(m, z)]))
    rw [map_smul, smul_smul, Complex.ofReal_mul]
  exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 hcomp)

theorem norm_vecT_sq (hV : VecHyp p nn F w c Fi L) (Q : C.LPt) :
    ‖vecT p w.length c Fi L Q‖ ^ 2 = (TBB.NP p nn F (P.r + 1) w Q Q).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecT p w.length c hV.hc Fi L Q Q, hV.gram Q Q]
  rfl

def gT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

theorem gT_cont (hV : VecHyp p nn F w c Fi L) {b s : ℕ} (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = P.r + 2) {h : C.LPt}
    (hh : D.IsLocPt h (b - 1)) : ContinuousOn (gT p w.length c Fi L s h) {0}ᶜ := by
  have hv := vecT_cont hV hh.1 (m := s) (by omega) (by rw [hh.2]; omega)
  have hsc : ContinuousOn
      (fun u : ℂ => (((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ)) : ℂ)) {0}ᶜ := by
    refine Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_const.mul (continuous_norm.continuousOn.pow _)) fun u hu => ?_
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hu))
  exact hsc.smul hv

theorem btT_eq_piecewise (s : ℕ) (h : C.LPt) :
    btT p w.length c Fi L s h = ({0}ᶜ : Set ℂ).piecewise (gT p w.length c Fi L s h) (fun _ => 0) := by
  funext u
  by_cases hu : u = 0
  · simp [btT, Set.piecewise, hu]
  · simp [btT, gT, Set.piecewise, hu]

end place

set_option maxHeartbeats 1000000 in
theorem field_measurability : FieldMeas := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh
  rw [btT_eq_piecewise]
  letI : MeasurableSpace (HT I Wp Wq) := borel _
  haveI : BorelSpace (HT I Wp Wq) := ⟨rfl⟩
  exact ((gT_cont hV hb hs hbs hh).measurable_piecewise continuousOn_const
    (measurableSet_singleton 0).compl).stronglyMeasurable

theorem field_locality : FieldLoc := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh K hK h0
  have hsub : K ⊆ {0}ᶜ := fun z hz hz0 => h0 (by rwa [Set.mem_singleton_iff.mp hz0] at hz)
  have hg := (gT_cont hV hb hs hbs hh).mono hsub
  refine ContinuousOn.integrableOn_compact hK ?_
  have hc : ContinuousOn
      (fun z => ‖(((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • gT p w.length c Fi L s h z‖ ^ 2) K := by
    have h1 : ContinuousOn (fun z : ℂ => ((((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ)) : ℂ)) K :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuous_norm.continuousOn.pow _))
    exact (h1.smul hg).norm.pow 2
  refine hc.congr fun z hz => ?_
  have hz0 : z ≠ 0 := fun e => h0 (e ▸ hz)
  simp only [PBK.bz, btT, gT, hz0, if_false]

theorem field_supremum : FieldSup := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  rw [← PBK.integral_norm_cvec_sq s (utT p w.length c Fi L s h) x hx]
  simp_rw [hcv, norm_vecT_sq hV]
  rw [TBB.Ew, hV.fibre a a hloc hloc]
  exact integral_re (hV.int a hloc)

theorem field_mem_unitary : FieldMemU := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  refine (PBK.memLp_cvec s (utT p w.length c Fi L s h) x hx).2 ?_
  have hfun : PBK.cvec s (utT p w.length c Fi L s h) x = fun cc => vecT p w.length c Fi L (a ++ [(1, cc)]) :=
    funext hcv
  rw [hfun]
  have hcont := vecT_cont hV hloc.1 (m := 1) le_rfl (by rw [hloc.2])
  have hmeas : AEStronglyMeasurable (fun cc => vecT p w.length c Fi L (a ++ [(1, cc)])) volume := by
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℂ)).compl
    first
      | rwa [restrict_compl_singleton] at this
      | rwa [Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))] at this
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine ((hV.int a hloc).re).congr (Filter.Eventually.of_forall fun cc => ?_)
  exact (norm_vecT_sq hV _).symm

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem germ_data_top_level : GermDataTopAll :=
  GT.germDataTopAll_of_parts GT.top_level_gram GT.top_level_germ_leading GT.top_level_fibre GT.top_level_Y_continuity
    GT.field_mem_unitary GT.field_supremum GT.field_measurability GT.field_locality

end Formalism.FourierDecayAlt.P.CutBP
end
