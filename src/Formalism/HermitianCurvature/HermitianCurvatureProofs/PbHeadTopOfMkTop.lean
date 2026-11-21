import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameParameterRegularity

section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXHead

theorem cd_lhOf_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (a b : Fin p) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => LeftFubiniLemmas.lhOf σ v a b) := by
  unfold LeftFubiniLemmas.lhOf U.lowW
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
  refine ContDiff.sum fun j _ => ?_
  refine ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_const.mul ?_
  refine contDiff_const.add ?_
  split_ifs
  · exact contDiff_apply ℝ ℂ _
  · exact contDiff_const

theorem cd_subS_lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => U.subS (LeftFubiniLemmas.lhOf σ v)) := by
  unfold U.subS
  refine ContDiff.sum fun i _ => ?_
  split_ifs
  · exact cd_lhOf_entry σ _ _
  · exact contDiff_const

theorem cd_psiH (h : C.LPt) :
    ContDiff ℝ ∞ (fun v : PBQ.XH h => G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v))) := by
  have h2 := cd_subS_lhOf (D.ptPerm h)
  unfold G.psi
  have hre : ContDiff ℝ ∞ (fun v : PBQ.XH h => ((U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)).re : ℂ)) := by
    have hm : ContDiff ℝ ∞ (fun v : PBQ.XH h => U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) :=
      contDiff_const.mul h2
    exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hm)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hre)

private theorem exists_bound_unitriangular_of_ldu_bounded {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (B : ℝ) :
    ∃ C : ℝ, ∀ L V : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) → (∀ i, L i i = 1) →
      (∀ i j, j < i → V i j = 0) → (∀ i, V i i = 1) →
      (∀ i j, ‖(L * Matrix.diagonal d * V) i j‖ ≤ B) → ∀ i j, ‖L i j‖ ≤ C := by
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L V : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) →
      (∀ i, L i i = 1) → (∀ i j, j < i → V i j = 0) → (∀ i, V i i = 1) →
      (∀ i j, ‖(L * Matrix.diagonal d * V) i j‖ ≤ B) →
      ∀ c : Fin n, c.val < k → ∀ a, ‖L a c‖ ≤ C ∧ ‖V c a‖ ≤ C := by
    intro k
    induction k with
    | zero => exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ c hc _ => absurd hc (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨Dm, hDm0, hdle⟩ : ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ i, ‖d i‖ ≤ Dm :=
        ⟨∑ j, ‖d j‖, Finset.sum_nonneg fun j _ => norm_nonneg _, fun i =>
          Finset.single_le_sum (f := fun j => ‖d j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)⟩
      have hCDC : 0 ≤ C * Dm * C := mul_nonneg (mul_nonneg hC0 hDm0) hC0
      obtain ⟨T, hT0, hTdef⟩ : ∃ T : ℝ, 0 ≤ T ∧ |B| + n * (C * Dm * C) ≤ T :=
        ⟨_, add_nonneg (abs_nonneg B) (mul_nonneg (Nat.cast_nonneg n) hCDC), le_rfl⟩
      have hS0 : 0 ≤ ∑ c, T / ‖d c‖ := Finset.sum_nonneg fun c _ => div_nonneg hT0 (norm_nonneg _)
      refine ⟨max C (1 + ∑ c, T / ‖d c‖), le_trans hC0 (le_max_left _ _), ?_⟩
      intro L V hL1 hL2 hV1 hV2 hN c hc a
      have hdc : 0 < ‖d c‖ := norm_pos_iff.mpr (hd c)
      have hcT : T / ‖d c‖ ≤ max C (1 + ∑ c, T / ‖d c‖) := by
        have hsg : T / ‖d c‖ ≤ ∑ i, T / ‖d i‖ :=
          Finset.single_le_sum (f := fun i => T / ‖d i‖) (fun i _ => div_nonneg hT0 (norm_nonneg _))
            (Finset.mem_univ c)
        exact le_trans (by linarith) (le_max_right _ _)
      have h1 : (1 : ℝ) ≤ max C (1 + ∑ c, T / ‖d c‖) := le_trans (by linarith) (le_max_right _ _)
      have core : ∀ x y : Fin n, (x = c ∨ y = c) → ‖L x c * d c * V c y‖ ≤ T := by
        intro x y hxy
        have hsum : (L * Matrix.diagonal d * V) x y = L x c * d c * V c y +
            ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y := by
          have h := Finset.add_sum_erase Finset.univ (fun e => L x e * d e * V e y) (Finset.mem_univ c)
          rw [h]
          rw [Matrix.mul_apply]
          simp only [Matrix.mul_diagonal]
        have hterm : ∀ e ∈ Finset.univ.erase c, ‖L x e * d e * V e y‖ ≤ C * Dm * C := by
          intro e he
          have hne : e ≠ c := Finset.ne_of_mem_erase he
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hek : e.val < k := by
              have : e.val < c.val := hlt
              omega
            rw [norm_mul, norm_mul]
            have hA := (hC L V hL1 hL2 hV1 hV2 hN e hek x).1
            have hB := (hC L V hL1 hL2 hV1 hV2 hN e hek y).2
            exact mul_le_mul (mul_le_mul hA (hdle e) (norm_nonneg _) hC0) hB (norm_nonneg _)
              (mul_nonneg hC0 hDm0)
          · have hz : L x e * d e * V e y = 0 := by
              rcases hxy with rfl | rfl
              · rw [hL1 _ _ hgt]; ring
              · rw [hV1 _ _ hgt]; ring
            rw [hz, norm_zero]
            exact hCDC
        have hrest : ‖∑ e ∈ Finset.univ.erase c, L x e * d e * V e y‖ ≤ n * (C * Dm * C) := by
          refine le_trans (norm_sum_le _ _) ?_
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.univ.erase c).card : ℝ) ≤ n := by
            have : (Finset.univ.erase c).card ≤ n := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
              omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hcard hCDC
        have hNxy := hN x y
        rw [hsum] at hNxy
        calc ‖L x c * d c * V c y‖
            = ‖(L x c * d c * V c y + ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y)
                - ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y‖ := by rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
          _ ≤ |B| + n * (C * Dm * C) := add_le_add (le_trans hNxy (le_abs_self B)) hrest
          _ ≤ T := hTdef
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [hL1 _ _ hac, hV1 _ _ hac, norm_zero]
        exact ⟨le_trans zero_le_one h1, le_trans zero_le_one h1⟩
      · rw [hL2, hV2, norm_one]
        exact ⟨h1, h1⟩
      · constructor
        · have hx := core a c (Or.inr rfl)
          rw [hV2, mul_one, norm_mul] at hx
          exact le_trans ((le_div_iff₀ hdc).mpr hx) hcT
        · have hx := core c a (Or.inl rfl)
          rw [hL2, one_mul, norm_mul] at hx
          exact le_trans ((le_div_iff₀ hdc).mpr (by rw [mul_comm]; exact hx)) hcT
  obtain ⟨C, -, hC⟩ := key n
  exact ⟨C, fun L V hL1 hL2 hV1 hV2 hN i j => (hC L V hL1 hL2 hV1 hV2 hN j j.isLt i).1⟩

private theorem wP_mul_wP_symm_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ * U.wP σ.symm = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Equiv.symm_apply_eq, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

private theorem lhOf_mul_hMat_eq_wP_mul_lowW_mul_diagonal (h : C.LPt) (v : PBQ.XH h) :
    LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) =
      U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) := by
  have hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b,
      (U.wP τ * X) a b = X (τ a) b := by
    intro τ X a b
    simp [U.wP, Matrix.mul_apply]
  have hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm := Matrix.inv_eq_right_inv hmul
  simp only [LeftFubiniLemmas.lhOf, U.hMat, hinv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]

private theorem det_lhOf_mul_hMat_ptPerm_ne_zero (h : C.LPt) (hh1 : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (v : PBQ.XH h) :
    (LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
  rw [lhOf_mul_hMat_eq_wP_mul_lowW_mul_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hwdet : (U.wP (D.ptPerm h)).det ≠ 0 := by
    have hd := congrArg Matrix.det (wP_mul_wP_symm_eq_one (D.ptPerm h))
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact left_ne_zero_of_mul_eq_one hd
  have hbt : (U.lowW (D.ptPerm h) v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [U.lowW, Matrix.one_apply_ne hij'.ne, not_lt_of_gt hij']
  have hlow : (U.lowW (D.ptPerm h) v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ hbt]
    simp [U.lowW]
  rw [hlow, one_mul]
  exact mul_ne_zero hwdet (Finset.prod_ne_zero_iff.mpr fun i _ => PBJ.Asm.ptScal_ne h hh1 i i.isLt)

theorem head_bound (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (K1 : Set (Fin j → Fin j → ℂ)) (hK1 : IsCompact K1) :
    ∃ R : ℝ, ∀ v : PBQ.XH h, R < ‖v‖ → ∀ u : Matrix (Fin j) (Fin j) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u →
      Matrix.of.symm (Matrix.of (PBQ.zxH h j hh.2 v) * u) ∉ K1 := by
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  obtain ⟨B, hB⟩ := hK1.isBounded.exists_norm_le
  have hd : ∀ i, D.ptDiag h i ≠ 0 := fun i => PBJ.Asm.ptScal_ne h hh1 i i.isLt
  obtain ⟨C, hC⟩ := exists_bound_unitriangular_of_ldu_bounded (D.ptDiag h) hd B
  refine ⟨max C 0, fun v hv u hu hmem => ?_⟩
  have hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b,
      (U.wP τ * X) a b = X (τ a) b := by
    intro τ X a b
    simp [U.wP, Matrix.mul_apply]
  have hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm := Matrix.inv_eq_right_inv hmul
  have hz : PBQ.zxH h (D.ptSize h) rfl v =
      U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) := by
    simp only [PBQ.zxH, LeftFubiniLemmas.lhOf, U.hMat, finCongr_refl, Matrix.reindex_refl_refl, Equiv.refl_apply, hinv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]
  rw [hz] at hmem
  have hN : ∀ i k, ‖(U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h) * u) i k‖ ≤ B := by
    intro i k
    have hm := hB _ hmem
    have he := (norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) *
      (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * u) ((D.ptPerm h).symm i)) k).trans
      (norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) *
      (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * u)) ((D.ptPerm h).symm i))
    refine le_trans (le_of_eq ?_) (le_trans he hm)
    show _ = ‖(U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) * u)
      ((D.ptPerm h).symm i) k‖
    rw [Matrix.mul_assoc (U.wP _), hwP, Equiv.apply_symm_apply]
  have hL := hC (U.lowW (D.ptPerm h) v) u
    (fun i k hik => by simp [U.lowW, Matrix.one_apply_ne hik.ne, not_lt_of_gt hik])
    (fun i => by simp [U.lowW])
    (fun i k hik => hu.1 hik) hu.2 hN
  have hvle : ‖v‖ ≤ max C 0 := by
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr ?_
    rintro ⟨⟨a, b⟩, hq⟩
    have hab := hL a b
    have he : U.lowW (D.ptPerm h) v a b = v ⟨(a, b), hq⟩ := by
      simp [U.lowW, hq, Matrix.one_apply_ne (ne_of_gt hq.1)]
    rw [he] at hab
    exact le_trans hab (le_max_left _ _)
  linarith

end Formalism.FourierDecayAlt.P.CutEXHead

open Formalism.FourierDecayAlt.P.CutEXHead in
theorem Formalism.FourierDecayAlt.P.head_family_exhaustion : Formalism.FourierDecayAlt.P.CutEX.HeadFam := by
  unfold Formalism.FourierDecayAlt.P.CutEX.HeadFam
  intro Wp Wq _ _ _ _ _ _ P p h hh f hf K hK hKU hsupp
  have hZ : ContDiff ℝ ∞ (fun v : Formalism.FourierDecayAlt.P.PBQ.XH h =>
      Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v)) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Formalism.FourierDecayAlt.P.PBQ.zxH, Matrix.of_symm_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact ContDiff.sum fun c _ => (cd_lhOf_entry _ _ _).mul contDiff_const
  refine ⟨?_, ?_⟩
  · rintro q₀ ⟨-, hq₀2⟩ hlev
    have hdet : (Matrix.of (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1)).det ≠ 0 := by
      show (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1).det ≠ 0
      simp only [Formalism.FourierDecayAlt.P.PBQ.zxH]
      rw [Matrix.det_reindex_self]
      exact det_lhOf_mul_hMat_ptPerm_ne_zero h hh.1 q₀.1
    obtain ⟨U', F', hU'o, hmem', hF', hagree⟩ := hf (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1, q₀.2) ⟨hdet, hq₀2⟩ hlev
    have hΦ : ContDiff ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) =>
        (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) :=
      (hZ.comp contDiff_fst).prodMk contDiff_snd
    refine ⟨(fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U',
      fun q => Formalism.FourierDecayAlt.P.PBQ.ellH h q.1 (F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2)), hU'o.preimage hΦ.continuous, hmem', ?_, ?_⟩
    · have h1 : ContDiffOn ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2))
          ((fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U') :=
        hF'.comp hΦ.contDiffOn (Set.mapsTo_preimage _ _)
      have h2 := ((cd_psiH h).comp contDiff_fst).contDiffOn
        (s := (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U')
      refine (h2.smul h1).congr fun q _ => ?_
      simp [Formalism.FourierDecayAlt.P.PBQ.ellH]
    · intro q hq hlev'
      exact congrArg _ (hagree _ hq hlev')
  · obtain ⟨R, hR⟩ := head_bound h P.r hh (Prod.fst '' K) (hK.image continuous_fst)
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun v hv y hy => ?_⟩
    by_contra hne
    obtain ⟨u, hu, huK⟩ := hsupp (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v, y) hy hne
    have hvR : R < ‖v‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hv
    exact hR v hvR u hu ⟨_, huK, rfl⟩
end
end

section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbEquiv

section clm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

theorem integral_clm_leftInv (L M : E →L[ℂ] E) (hML : ∀ v, M (L v) = v) (f : α → E) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  by_cases hf : Integrable f μ
  · exact L.integral_comp_comm hf
  · have hLf : ¬ Integrable (fun x => L (f x)) μ := by
      intro h
      apply hf
      have := M.integrable_comp h
      simpa [hML] using this
    rw [integral_undef hf, integral_undef hLf, map_zero]

end clm

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def post (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

def pre (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B'

theorem post_apply (A : Wp →L[ℂ] Wp) (f : Wq →L[ℂ] Wp) : post A f = A.comp f := rfl

theorem pre_apply (B' : Wq →L[ℂ] Wq) (f : Wq →L[ℂ] Wp) : pre B' f = f.comp B' := rfl

end ops

section homeo

variable {k r : ℕ}

def conjHomeo (a : B.Mat k r) (ha : IsUnit a.det) : Mt k r ≃ₜ Mt k r where
  toFun x := a * Matrix.of x * a⁻¹
  invFun x := a⁻¹ * Matrix.of x * a
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * a⁻¹) * a = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
      Matrix.one_mul]; rfl
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * a) * a⁻¹ = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
      Matrix.one_mul]; rfl
  continuous_toFun := by
    show Continuous fun x : Mt k r => a * Matrix.of x * a⁻¹
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Mt k r => a⁻¹ * Matrix.of x * a
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const

end homeo

section kr

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem unit_of_uw {z : Fin (2 * r + k + 1) → ℂ} {w : B.Mat k r} (hw : w ∈ UWset k r z) : IsUnit w.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hw.1

theorem kr_right_uw (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x w : B.Mat k r)
    (hw : w ∈ UWset k r Bs.z') : PBG.Kr Bs F (x * w) = (PBG.Kr Bs F x).comp (Bs.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k r Bs.z' := LieBracketMultiplication.uw_inv hw
  have := PBG.sigmaFinite_of_haar Bs.haarN
  have := PBG.sigmaFinite_of_haar Bs.haarW'
  set e1 := (PBG.lmulHomeo w hU).toMeasurableEquiv
  set e2 := (conjHomeo w hU).toMeasurableEquiv
  set Φ : Mt k r × Mt k r ≃ᵐ Mt k r × Mt k r := MeasurableEquiv.prodCongr e1 e2
  have hmp1 : MeasurePreserving e1 Bs.μW' Bs.μW' := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM w := by funext x; rfl
    rw [ee]; exact Bs.haarW'.left w hw
  have hmp2 : MeasurePreserving e2 Bs.μN Bs.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM w := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r Bs.z' Bs.μN Bs.z'_mem Bs.T'_pos Bs.haarN w hw
  have hmp : MeasurePreserving Φ (Bs.μW'.prod Bs.μN) (Bs.μW'.prod Bs.μN) := hmp1.prod hmp2
  set f : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  set g : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * w * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  have hK1 : PBG.Kr Bs F x = ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) := (hmp.integral_comp' f).symm
  have hae : ∀ᵐ p ∂(Bs.μW'.prod Bs.μN), (Matrix.of p.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW')
  have hK2 : ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) = ∫ p, pre (Bs.π' w⁻¹) (g p) ∂(Bs.μW'.prod Bs.μN) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have hpsi : psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹) = psi k r Bs.z' cStd (Matrix.of p.2) := by
      have := Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bs.z' cStd w⁻¹ hwi (Matrix.of p.2)
      rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this
    have hmat : x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1) = x * w * Matrix.of p.2 * Matrix.of p.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc w⁻¹ w, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    have hpi : Bs.π' (w * Matrix.of p.1)⁻¹ = (Bs.π' (Matrix.of p.1)⁻¹).comp (Bs.π' w⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact Bs.π'_rep.2 _ (LieBracketMultiplication.uw_inv hp) _ hwi
    show star (psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹)) •
        (F (x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1))).comp (Bs.π' (w * Matrix.of p.1)⁻¹) = _
    rw [hpsi, hmat, hpi, pre_apply, ContinuousLinearMap.smul_comp]
    rfl
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (Bs.π' w) (pre (Bs.π' w⁻¹) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw,
      Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
    rfl
  have hK3 : PBG.Kr Bs F x = (PBG.Kr Bs F (x * w)).comp (Bs.π' w⁻¹) := by
    rw [hK1, hK2, integral_clm_leftInv _ _ hML]
    rfl
  rw [hK3, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw, Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
  rfl

end kr

section pb

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem pbF_right_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g w : B.Mat k n) (hw : w ∈ UWset k n B0.z') :
    PBQ.pbF Bj B0 e H (g * w) = (PBQ.pbF Bj B0 e H g).comp (B0.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k n B0.z' := LieBracketMultiplication.uw_inv hw
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (B0.π' w⁻¹) (pre (B0.π' w) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← B0.π'_rep.2 _ hw _ hwi,
      Matrix.mul_nonsing_inv _ hU, B0.π'_rep.1]
    rfl
  unfold PBQ.pbF
  rw [← pre_apply, ← integral_clm_leftInv _ _ hML]
  congr 1
  funext x
  unfold PBQ.pbI
  rw [← Matrix.mul_assoc, kr_right_uw B0 H _ w hw, pre_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]

theorem pbF_left_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (h : B.Mat k ρ) (hh : h ∈ UWset k ρ Bj.z) (g : B.Mat k n) :
    PBQ.pbF Bj B0 e H (D.castM e (U.embG k p ρ h) * g) = (Bj.π h).comp (PBQ.pbF Bj B0 e H g) := by
  have hU := unit_of_uw hh
  have hi : h⁻¹ ∈ UWset k ρ Bj.z := LieBracketMultiplication.uw_inv hh
  have hiU := unit_of_uw hi
  have := PBG.sigmaFinite_of_haar Bj.haarN
  have := PBG.sigmaFinite_of_haar Bj.haarW
  haveI : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  set e1 := (PBG.lmulHomeo h⁻¹ hiU).toMeasurableEquiv
  set e2 := (conjHomeo h⁻¹ hiU).toMeasurableEquiv
  set Φ : PBQ.XP k p ρ ≃ᵐ PBQ.XP k p ρ := MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e1 e2)
    (MeasurableEquiv.refl _)
  have hmp1 : MeasurePreserving e1 Bj.μW Bj.μW := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM h⁻¹ := by funext x; rfl
    rw [ee]; exact Bj.haarW.left h⁻¹ hi
  have hmp2 : MeasurePreserving e2 Bj.μN Bj.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM h⁻¹ := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k ρ Bj.z Bj.μN Bj.z_mem Bj.T_pos Bj.haarN h⁻¹ hi
  have hmp : MeasurePreserving Φ (PBQ.muXP (p := p) Bj) (PBQ.muXP (p := p) Bj) :=
    (hmp1.prod hmp2).prod (MeasurePreserving.id _)
  have hML : ∀ v : Wq →L[ℂ] Wp, post (Bj.π h⁻¹) (post (Bj.π h) v) = v := by
    intro v
    rw [post_apply, post_apply, ← ContinuousLinearMap.comp_assoc, ← Bj.π_rep.2 _ hi _ hh,
      Matrix.nonsing_inv_mul _ hU, Bj.π_rep.1]
    rfl
  have hF : PBQ.pbF Bj B0 e H g = ∫ x, PBQ.pbI Bj B0 e H g (Φ x) ∂(PBQ.muXP Bj) :=
    (hmp.integral_comp' (PBQ.pbI Bj B0 e H g)).symm
  rw [hF, ← post_apply, ← integral_clm_leftInv _ _ hML]
  unfold PBQ.pbF
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP Bj] with x hx
  have hx1 : (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z := hx.1
  have hx2 : (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ := hx.2
  have hΦ : PBQ.GoodP Bj (Φ x) :=
    ⟨LieBracketMultiplication.uw_mul hi hx1, (Formalism.QuantumDeterminants.uWNormal k ρ Bj.z Bj.z_mem h⁻¹ hi _ hx2).1⟩
  have hsP : D.castM e (PBQ.sP Bj x) * (D.castM e (U.embG k p ρ h) * g) = D.castM e (PBQ.sP Bj (Φ x)) * g := by
    rw [← Matrix.mul_assoc, ← PBQ.castM_mul]
    congr 2
    unfold PBQ.sP
    rw [if_pos hx, if_pos hΦ]
    show U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹) * U.embG k p ρ h =
      U.Rn k p ρ (-x.2) * U.embG k p ρ ((h⁻¹ * Matrix.of x.1.1)⁻¹ * (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹)⁻¹)
    rw [Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul]
    congr 2
    rw [Matrix.nonsing_inv_nonsing_inv h hU]
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv h hU, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hcP : PBQ.cP Bj (Φ x) = PBQ.cP Bj x := by
    unfold PBQ.cP
    show psi k ρ Bj.z cStd (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹) * _ = _
    rw [Matrix.nonsing_inv_nonsing_inv h hU, Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bj.z cStd h hh]
    rfl
  have hπ : Bj.π (Matrix.of x.1.1) = (Bj.π h).comp (Bj.π (h⁻¹ * Matrix.of x.1.1)) := by
    rw [← Bj.π_rep.2 _ hh _ (LieBracketMultiplication.uw_mul hi hx1), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  unfold PBQ.pbI
  rw [hsP, ← hcP, hπ, post_apply, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_assoc]
  rfl

end pb

end Formalism.FourierDecayAlt.P.CutEXPbEquiv

namespace Formalism.FourierDecayAlt.P

open CutEXPbEquiv

theorem pullback_equivalence : CutEX.PbEquiv := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z _ μ _ h hh h' hh'
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hw : D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h') ∈
      UWset P.k P.r p.T.base.z' := by
    have h1 := Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW (k := P.k) P.r (P.r - P.r) _ h' hh'
    rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG] at h1
    have h2 := Formalism.FourierDecayAlt.P.Dx2.Tower.castM_UW (by omega : P.r + (P.r - P.r) = P.r) _ _ h1
    rw [p.T.z'_lev P.r le_rfl] at h2
    exact h2
  have hpi : p.T.base.π' (D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h')) =
      (p.T.bs P.r).π' h' := by
    rw [p.T.π'_lev P.r le_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
    rfl
  unfold CutEX.pbTop PBQ.pbT CutEX.xT
  rw [LeftFubiniLemmas.embedding_map_embedded_group, PBQ.castM_mul, PBQ.castM_mul, pbF_right_uw _ _ _ _ _ _ hw, pbF_left_uw _ _ _ _ _ hh, hpi,
    ContinuousLinearMap.comp_assoc]

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

open Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lemmas

variable {k : ℕ}

theorem contDiff_castM {a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact contDiff_id

theorem ms_mMap {r : ℕ} (q₀ : (Fin r → Fin r → ℂ) × Mt k (r - r)) (h₀ : (Matrix.of q₀.1).det ≠ 0) :
    MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ := by
  have hZ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.1) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_fst
  have hμ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.2) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_snd
  have hZi : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr h₀)
  unfold U.mMap
  exact Formalism.FourierDecayAlt.P.PBI.measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
    (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)

theorem contDiffOn_xT (r : ℕ) :
    ContDiffOn ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => xT k r (Matrix.of q.1) (Matrix.of q.2))
      {q | (Matrix.of q.1).det ≠ 0} := by
  intro q₀ h₀
  have hm := ms_mMap q₀ h₀
  have hc : ContDiffAt ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hm i l
  exact ((contDiff_castM (k := k) (by omega : r + (r - r) = r)).contDiffAt.comp q₀ hc).contDiffWithinAt

theorem dmin_xT (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) :
    Dmin k r z z' (xT k r Z μ) ⟨r, by omega⟩ = Z.det := by
  unfold xT
  rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM (by omega) z z' _ r (by omega) (by omega),
    Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r (r - r)]
  have e := Formalism.FourierDecayAlt.P.hat_z_on_slice k r (r - r) 0 0 Z μ
  rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
  unfold U.DjU
  rw [e]

theorem xT_GV (r : ℕ) {Z : Matrix (Fin r) (Fin r) ℂ} {μ : B.Mat k (r - r)} (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k (r - r)) :
    xT k r Z μ ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV _ ((Formalism.FourierDecayAlt.P.slice_membership k r (r - r)).1 Z μ hZ hμ)

theorem gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem inWb_castV {a b : ℕ} (e : a = b) {z : Fin (2 * a + k + 1) → ℂ} (h : inWb k a z) : inWb k b (D.castV e z) := by
  subst e
  rwa [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

end lemmas

theorem pullback_smooth_formula : PbSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p G hG q₀ hq₀ hG₀
  obtain ⟨⟨hsm, ⟨R, hR⟩, -⟩, -⟩ := hG
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hHC : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → G g = 0 := by
    intro g hg hn
    by_contra hne
    exact hn (hR g hg hne)
  have hΩ := PBQ.isOpen_domP P.k P.r P.r p.T.base.z p.T.base.z'
  have hP := proper_left_variables_domain Wp Wq P p P.r le_rfl _ hCs
  have hG₀' : Matrix.of q₀.2 ∈ B.GV P.k (P.r - P.r) := hG₀.1
  have hgf : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2)) := by
    unfold xT
    rw [gf_castM]
    have e := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r)
      (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z) (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z')
      (inWb_castV _ p.T.base.z_mem) (inWb_castV _ p.T.base.z'_mem) 0 0 (Matrix.of q₀.1) (Matrix.of q₀.2)
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
    rw [e, MkCptPf.lowV_top p.T _, MkCptPf.lowV_top' p.T _, MkCptPf.gf_eq_ggl (by omega)]
    exact mul_pos (Complex.normSq_pos.2 hq₀.1) hq₀.2
  have hyΩ : xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2) ∈ PBQ.domP P.k P.r P.r p.T.base.z p.T.base.z' := by
    refine ⟨fun l hl1 hl2 => ?_, hgf⟩
    have hl : l = ⟨P.r, by omega⟩ := Fin.ext (by show (l : ℕ) = P.r; omega)
    rw [hl, dmin_xT]; exact hq₀.1
  have hyG := xT_GV P.r hq₀.1 hG₀'
  have hz : p.T.base.z = D.castV (by omega : P.r + (P.r - P.r) = P.r) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) :=
    (p.T.z_lev P.r le_rfl).symm
  obtain ⟨V, f', hV, hyV, hf', hag⟩ := partial_bessel_smooth_compact_support P.k P.r (P.r - P.r) P.r Wp Wq (p.T.bs P.r) p.T.base
    (by omega) hz G _ hsm hCs hHC _ hΩ hP _ hyΩ hyG
  have hxc := contDiffOn_xT (k := P.k) P.r
  have hOD : IsOpen {q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (continuous_fst)) continuous_const
  refine ⟨{q | (Matrix.of q.1).det ≠ 0} ∩
      (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)) ⁻¹' V,
    fun q => f' (xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)), hxc.continuousOn.isOpen_inter_preimage hOD hV,
    ⟨hq₀.1, hyV⟩, hf'.comp (hxc.mono Set.inter_subset_left) (fun q hq => hq.2), fun q hq hqG => ?_⟩
  exact hag _ hq.2 (xT_GV P.r hq.1 hqG.1)

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem pullback_smooth : CutEX.PbSmooth := CutEX.pullback_smooth_formula

end Formalism.FourierDecayAlt.P
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_integral_level_reduction (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))) volume ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  have hz1 : B0.z = liftVec k p ρ Bj.z := by rw [← hz, JCTx5.castV_rfl]
  have hz1' : B0.z' = liftVec k p ρ Bj.z' := by rw [← hz', JCTx5.castV_rfl]
  have hπ1 : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Dx2.MN.castM_rfl, Dx2.Tower.lev_eq_embG]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    refine hHc.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Ux3.zhDmin]
    exact hx.2
  obtain ⟨hi, heq⟩ := SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz1' hπ1 hW' hW0' hNj hN0 g hg H hHc' R hR
  refine ⟨?_, ?_⟩
  · simpa only [Dx2.MN.castM_rfl] using hi
  · rw [JCTx5.castV_rfl, JCTx5.castV_rfl, hz1, hz1']
    simp only [Dx2.MN.castM_rfl]
    exact heq

end gen

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_gen (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hG : B.CkOn ⊤ (B.GV P.k P.r) G) (R : ℝ) (hR : ∀ x ∈ B.GV P.k P.r, G x ≠ 0 → B.gN x ≤ R)
    (h : C.LPt) (j : ℕ) (hjr : j ≤ P.r) (hh : D.IsLocPt h j) (hj1 : 1 ≤ j) (γ : B.Mat P.k (P.r - j))
    (hOm : γ ∈ JF.Om P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z') :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ)))) ∧
    B.JF (p.T.bs j) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
      ∫ v, PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ))) := by
  obtain ⟨hh1, rfl⟩ := hh
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hzj := p.T.z_lev (D.ptSize h) hjr
  have hzj' := p.T.z'_lev (D.ptSize h) hjr
  have hπj : ∀ y, (p.T.bs (D.ptSize h)).π' y = p.T.base.π' (D.castM e (ιLev P.k _ _ y)) :=
    fun y => p.T.π'_lev _ hjr y
  obtain ⟨hWj, hW'j, hNj⟩ := p.hT (D.ptSize h) hjr
  obtain ⟨hW0, hW'0, hN0⟩ := p.hT 0 (Nat.zero_le _)
  have hW0' : p.T.base.μW' = (p.T.bs (D.ptSize h)).μW'.map (PBM.levMt (D.ptSize h) (P.r - D.ptSize h) e) :=
    PBM.haar_lev _ _ e _ _ hzj' _ _ p.T.base.haarW' (p.T.bs _).haarW' hW'0 hW'j
  have hGc : ContinuousOn G {x | x ∈ B.GV P.k P.r ∧
      Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    (PBE.ckOn_continuousOn' subset_rfl hG).mono fun x hx => hx.1
  obtain ⟨H1i, H1e⟩ := slice_integral_level_reduction e hj1 (D.ptPerm h) (D.ptDiag h) (CutHB.ptDiag_ne ⟨hh1, rfl⟩)
    (p.T.bs (D.ptSize h)) p.T.base hzj hzj' hπj hW'j hW0' hNj hN0 γ hOm G hGc R hR
  have hcf : ∀ (e' : P.r - D.ptSize h = P.r - D.ptSize h) (F : B.Mat P.k (P.r - D.ptSize h) → (Wq →L[ℂ] Wp)),
      D.castF e' F = F := fun e' F => by
    funext x
    simp only [D.castF, Dx2.MN.castM_rfl]
  refine ⟨?_, ?_⟩
  · simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    simp only [SliceIntegralLemmas.psiH] at H1i
    exact H1i
  · rw [hcf, D.sliceAt, dif_pos hjr]
    simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact H1e

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  have h0 : ∀ (hl : 0 < 0 + 2), Dmin k 0 z z' γ ⟨0, hl⟩ = 1 := by
    intro hl
    simp [Dmin]
  have h1 : Dmin k 0 z z' γ (Fin.last (0 + 1)) = Q.zetaL k 0 z z' (Fin.last 0) γ := by
    rw [PBI.zetaL_eq_zhat]
    simp [Dmin, Matrix.det_unique]
  refine ⟨hγ, ?_, ?_⟩
  · intro l hl
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simpa using hl)
    rw [hl0, h0]
    exact one_ne_zero
  · unfold Gf
    rw [h1, h0]
    simpa [Q.GGl] using hG

end top

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem sliceTop_pos (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : 1 ≤ P.r) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm : γ ∈ JF.Om P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' :=
    om_zero (Nat.sub_self _) _ _ γ hγ hGG
  obtain ⟨R, hR⟩ := hG.1.2.1
  exact slice_gen P p G hG.1.1 R hR h P.r le_rfl hh hr γ hOm

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P

theorem slice_top_exhaustion : CutEX.SliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh γ hγ hGG
  rcases Nat.eq_zero_or_pos P.r with h0 | h1
  · exact CutEXSl0.sliceTop_zero Wp Wq P p h0 G hG h hh γ hγ hGG
  · exact CutEXSlice.sliceTop_pos Wp Wq P p h1 G hG h hh γ hγ hGG

end Formalism.FourierDecayAlt.P
end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXUw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gloc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOpG (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) →
    ∀ x ∈ O, x ∈ B.GV k r → T f₁ x = T f₂ x

theorem locOpG_top (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    LocOpG (k := k) (r := r) (E := E) (Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b) := by
  intro O hO f₁ f₂ h x hx hxG
  exact PBG.top_congr' O hO u a b h x hx hxG

theorem locOpG_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOpG T) →
    LocOpG (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx hxG
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOpG_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx hxG

theorem locOpG_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOpG_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx hxG
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOpG_top _ _ _

theorem locOpG_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOpG (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOpG (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOpG_AAop _ _ _ O hO f₁ f₂ h x hx hxG]
  · rw [locOpG_AAvop _ _ _ O hO f₁ f₂ h x hx hxG]

theorem uwG_congrG (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, x ∈ B.GV k r →
      D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx hxG
    simp only [D.uwG]
    exact locOpG_vLet z z' j hj l _ O hO _ _ (uwG_congrG z z' j hj hO h w _) x hx hxG

theorem top_zero (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
  exact PBG.eabH_zero a b g

theorem foldr_zero : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))),
    (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) → L.foldr (fun T h => T h) (fun _ => (0 : E)) = fun _ => 0
  | [], _ => rfl
  | T :: L, hL => by
    simp only [List.foldr_cons]
    rw [foldr_zero L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))]
    exact hL T List.mem_cons_self

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (EabH (Hpk k r)) a b u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  rw [foldr_zero _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT; exact top_zero _ _ _)]
  funext g
  simp

theorem AAop_zero (m : ℕ) (hm : m ≤ r) (u : ℂ) : C3.AAop k r m hm u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    C3.AAvop k r m hm ell (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAvop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    D.vLet k r z z' j hj l e (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [AAop_zero]; simp
  · rw [AAvop_zero]; simp

theorem uwG_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' (fun _ : B.Mat k r => (0 : E)) j hj w e = fun _ => 0
  | [], _ => rfl
  | l :: w, e => by
    simp only [D.uwG]
    rw [uwG_zero z z' j hj w _]
    exact vLet_zero z z' j hj l _

end gloc

theorem continuous_gN {k r : ℕ} : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

theorem topCls_uwG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : CutEX.TopCls Bs F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    CutEX.TopCls Bs (D.uwG k r Bs.z Bs.z' F r le_rfl w e) := by
  obtain ⟨⟨hsm, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, ⟨K, hK, h0K, hDK⟩⟩ := hF
  let S : Set (B.Mat k r) := {x | x ∈ B.GV k r ∧ F x ≠ 0}
  have hDc : Continuous (fun x : B.Mat k r => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _).continuous
  have hvan : ∀ x ∈ (closure S)ᶜ, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x = 0 := by
    intro x hx hxG
    have hz : ∀ y ∈ (closure S)ᶜ, y ∈ B.GV k r → F y = (fun _ => (0 : Wq →L[ℂ] Wp)) y := by
      intro y hy hyG
      by_contra hne
      exact hy (subset_closure ⟨hyG, hne⟩)
    rw [uwG_congrG Bs.z Bs.z' r le_rfl isClosed_closure.isOpen_compl hz w e x hx hxG, uwG_zero]
  have hcl : ∀ x, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x ≠ 0 → x ∈ closure S := by
    intro x hxG hne
    by_contra hx
    exact hne (hvan x hx hxG)
  have hDcl : ∀ x ∈ closure S, Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩ ∈ K := by
    have hsub : S ⊆ (fun x => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) ⁻¹' K := fun x hx => hDK x hx.1 hx.2
    exact fun x hx => closure_minimal hsub (hK.isClosed.preimage hDc) hx
  refine ⟨⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩, ⟨K, hK, h0K, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hD : Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩ = 0
    · have hg₀S : g₀ ∈ (closure S)ᶜ := fun h => h0K (hD ▸ hDcl g₀ h)
      exact ⟨(closure S)ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hg₀S, contDiffOn_const,
        fun x hx hxG => hvan x hx hxG⟩
    · exact PBG.uwG_mem Bs.z Bs.z' r le_rfl hsm w e g₀ hD hg₀
  · intro g hg hne
    have hsub : S ⊆ {x | B.gN x ≤ R} := fun x hx => hR x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_gN continuous_const) (hcl g hg hne)
  · intro g hg hne
    have hsub : S ⊆ {x | ε ≤ Gf k r Bs.z Bs.z' x} := fun x hx => hεG x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _)) (hcl g hg hne)
  · intro g hg hne
    exact hDcl g (hcl g hg hne)

end Formalism.FourierDecayAlt.P.CutEXUw

namespace Formalism.FourierDecayAlt.P

theorem unipotent_weight_top : CutEX.UwTop := by
  intro Wp Wq _ _ _ _ _ _ P p F hF w e
  exact CutEXUw.topCls_uwG p.T.base F hF w e

end Formalism.FourierDecayAlt.P
end
end

section
namespace Formalism.FourierDecayAlt.P

theorem pb_exhPic_of_mkTop (hMk : CutEX.MkTop) : PBI.ExhPic :=
  CutEX.exhPic_of_leaves CutEX.exceptional_assumption_holds unipotent_weight_top slice_top_exhaustion pullback_smooth
    pullback_right_action pullback_support pullback_equivalence hMk compact_truncation_construction top_point_existence
    determinant_exceptional_holds head_family_exhaustion radial_slice_top radial_of_function_exceptional radial_extension_exceptional
    residue_top_exceptional_level frame_parameter_regularity (pb_radWordSliceOfHeadPic head_picture) level_zero_picture_of_slice

theorem pb_headTop_of_mkTop (hMk : CutEX.MkTop) : KB.HeadTop :=
  pb_headTop_of top_unipotent_integral (pb_exhPic_of_mkTop hMk)

end Formalism.FourierDecayAlt.P
end
