import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section smul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_smul' (M : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Wd.Ix S → RadSp k r z z' π π') (a : ℂ) :
    P5.act M (fun e => a • x e) = fun e => a • P5.act M x e := by
  funext e
  simp only [P5.act, map_smul, Finset.smul_sum]

theorem rrform_smul (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ) :
    P5.RRform L st μ i w (fun e => a • x e) (fun e => a • y e) c = a * conj a * P5.RRform L st μ i w x y c := by
  unfold P5.RRform
  rw [act_smul']
  unfold P5.form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [HerA.pairAt_smul_left, HerA.pairAt_smul_right, ← Finset.mul_sum]
  ring

end smul

theorem isLocPt_snoc {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) {t : ℂ} (ht : t ≠ 0) :
    D.IsLocPt (h ++ [(1, t)]) (j + 1) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, ht⟩
  · unfold D.ptSize at h2 ⊢
    rw [List.map_append, List.sum_append, h2]
    simp

theorem levW_below (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) {t : ℂ} (ht : t ≠ 0) :
    ‖t‖ ^ (-2 : ℤ) * (‖t‖ ^ (2 * (P.r - j) + P.k)) ^ 2 = KB.levW P (j + 1) t := by
  have hj' : j + 1 ≠ P.r + 1 := by omega
  unfold KB.levW
  rw [if_neg hj']
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ ht']
  congr 1
  unfold C.Mlev
  push_cast [Nat.cast_sub (show j ≤ P.r by omega)]
  ring

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of (hOne : PBO.FormOne) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2
  obtain ⟨ε₂, hε₂, hx'⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2'
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)}, min ε₁ ε₂ ≤ ε' →
      JC.NiceCoef (p.T.bs (j + 1)) ε' G → JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) G :=
    fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2 e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2' e) := fun e => mono (min_le_right _ _) (hx' e)

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs w x2 x2' Φ2 Φ2' (min ε₁ ε₂) hε hxn hxn' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hl, hl'⟩, dif_pos hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section cell

variable {k ρ : ℕ}

theorem finRange_one_add (ρ : ℕ) :
    List.finRange (1 + ρ) = (⟨0, by omega⟩ : Fin (1 + ρ)) :: (List.finRange ρ).map PBH.shS := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rcases i with _ | i
    · simp
    · simp [PBH.shS]

theorem weyl_cell_shift_eq_level_embedding (a : Fin ρ) (x : ℂ) : w1 k (1 + ρ) (PBH.shS a) x = ιLev k 1 ρ (w1 k ρ a x) := by
  ext ⟨p, hp⟩ ⟨q, hq⟩
  have ha := a.isLt
  unfold w1 ιLev
  simp only [eI, esI, PBH.shS, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

theorem iota_list_prod (l : List (Mx k ρ)) : ιLev k 1 ρ l.prod = (l.map (ιLev k 1 ρ)).prod := by
  induction l with
  | nil => simpa using Formalism.FourierDecayAlt.P.Dx2.Tower.lev_one (k := k) 1 ρ
  | cons a l ih => rw [List.prod_cons, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, ih, List.map_cons, List.prod_cons]

theorem wCell_consC (t : ℂ) (c : Fin ρ → ℂ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) =
      w1 k (1 + ρ) ⟨0, by omega⟩ t * ιLev k 1 ρ (wCell k ρ (Fin.last ρ) c) := by
  unfold wCell
  rw [List.filter_eq_self.2 (fun a _ => by simp),
    List.filter_eq_self.2 (fun a _ => by simp), finRange_one_add, iota_list_prod]
  rw [List.map_cons, List.prod_cons, PBH.consC_zero, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun a _ => ?_)
  simp only [Function.comp, PBH.consC_sh, weyl_cell_shift_eq_level_embedding]

theorem weyl_cell_zero_eq_embedding {t : ℂ} (ht : t ≠ 0) :
    w1 k (1 + ρ) ⟨0, by omega⟩ t = U.mMap k 1 ρ (Matrix.of fun _ _ => t) 1 := by
  have hinv : ((Matrix.of fun _ _ : Fin 1 => t)ᴴ)⁻¹ = Matrix.of fun _ _ : Fin 1 => (star t)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, ht]
  ext i l
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective l
  rw [U.mMap, PBH.weyl_lift_eq_pair, Matrix.mul_one, Matrix.one_mul, hinv, Ux3.block3_apply]
  have hX : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inl (Sum.inl x)) = ⟨0, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_first_val]; simp)
  have hV : ∀ v : Fin (2 * ρ + k + 1), U.eB k 1 ρ (Sum.inl (Sum.inr v)) = ⟨1 + v.val, by omega⟩ := fun v =>
    Fin.ext (by rw [Ux3.block_index_middle_val])
  have hS : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inr x) = ⟨2 * (1 + ρ) + k, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_last_val]; have := x.isLt; simp; omega)
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.one_apply, hX, hV, hS] <;>
    unfold w1 <;>
    simp only [eI, esI, Fin.ext_iff] <;>
    (have hx := x.isLt; have hy := y.isLt; split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega))

theorem cell_iota {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) * ιLev k 1 ρ g =
      U.mMap k 1 ρ (Matrix.of fun _ _ => t) (wCell k ρ (Fin.last ρ) c * g) := by
  rw [wCell_consC, Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, weyl_cell_zero_eq_embedding ht,
    ← Formalism.FourierDecayAlt.P.Dx2.MN.embG_eq, Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG, Matrix.one_mul]

theorem gauge_consC (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ a : Fin (1 + ρ), (if a.val < (Fin.last (1 + ρ)).val then ‖PBH.consC t c a‖ ^ (Mdim k (1 + ρ) a - 1)
      else 1 : ℝ)) =
      ‖t‖ ^ (2 * (1 + ρ) + k) *
        ∏ a : Fin ρ, (if a.val < (Fin.last ρ).val then ‖c a‖ ^ (Mdim k ρ a - 1) else 1 : ℝ) := by
  rw [Finset.prod_congr rfl (fun a _ => if_pos (by rw [Fin.val_last]; exact a.isLt)),
    Finset.prod_congr rfl (fun (a : Fin ρ) _ => if_pos (by rw [Fin.val_last]; exact a.isLt))]
  rw [← Fintype.prod_equiv (finCongr (Nat.add_comm ρ 1))
    (fun a : Fin (ρ + 1) => ‖PBH.consC t c (finCongr (Nat.add_comm ρ 1) a)‖ ^
      (Mdim k (1 + ρ) (finCongr (Nat.add_comm ρ 1) a) - 1)) _ (fun _ => rfl)]
  rw [Fin.prod_univ_succ]
  refine congrArg₂ (· * ·) ?_ ?_
  · have h0 : finCongr (Nat.add_comm ρ 1) (0 : Fin (ρ + 1)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [h0, PBH.consC_zero]
    congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    have hs : finCongr (Nat.add_comm ρ 1) a.succ = PBH.shS a := Fin.ext (by simp [PBH.shS])
    rw [hs, PBH.consC_sh]
    congr 1
    simp only [Mdim, PBH.shS]
    omega

theorem resG_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (J : Mx k (1 + ρ) → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k (1 + ρ) (Fin.last (1 + ρ)) J (PBH.consC t c) (ιLev k 1 ρ g) =
      ((‖t‖ ^ (2 * (1 + ρ) + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) c g := by
  unfold resG
  rw [cell_iota ht, smul_smul, gauge_consC, ← Complex.ofReal_mul]

theorem resG_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (hn : n = 1 + ρ) {t : ℂ} (ht : t ≠ 0)
    (J : Mx k n → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k n (Fin.last n) J (fun l => PBH.consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn.symm (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) c g := by
  subst hn
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact resG_consC ht J c g

end cell

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of_headPic (hHP : HeadPic) : KB.RadHead :=
  pb_radHead_of module_form_eq_radial_form_one exists_zeta_normalized_haar hHP

end Formalism.FourierDecayAlt.P
end
end
