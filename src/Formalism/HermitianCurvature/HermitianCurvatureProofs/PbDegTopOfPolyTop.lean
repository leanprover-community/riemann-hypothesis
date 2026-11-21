import Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacquetRaisingOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

theorem minor_cell_of_parts : PBN.MinorCellOfParts := by
  intro hRR hLR hTC hGP k r Wp Wq _ _ _ _ _ _ Bs F y hF x hx
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨hf, hLf, hRf, -⟩ := Formalism.FourierDecayAlt.P.bessel_function_finite_class k r Wp Wq Bs F ε hε hn
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D (B.JF Bs F), cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl

  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    refine (vAB_loc y r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1

  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D (B.JF Bs F)) (B.JF Bs F) (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {n r : ℕ}

theorem liftM_star (M : SlopeTestRemainingChoices (Fin n) A) : liftM (star M) = star (liftM M) := by
  ext z z'
  simp only [Matrix.star_apply, liftM_apply]
  by_cases h : z 0 = z' 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem liftM_neg (M : SlopeTestRemainingChoices (Fin n) A) : liftM (-M) = -liftM M := by
  rw [← liftRingHom_apply_eq_liftM, map_neg, liftRingHom_apply_eq_liftM]

theorem liftM_sub (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M - N) = liftM M - liftM N := by
  rw [← liftRingHom_apply_eq_liftM, map_sub, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM]

theorem liftM_pow (M : SlopeTestRemainingChoices (Fin n) A) (m : ℕ) : liftM (M ^ m) = liftM M ^ m := by
  rw [← liftRingHom_apply_eq_liftM, map_pow, liftRingHom_apply_eq_liftM]

theorem matrix_two_map_lift (a b c d : SlopeTestRemainingChoices (Fin n) A) :
    (!![a, b; c, d] : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = !![liftM a, liftM b; liftM c, liftM d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

structure Lifted (f : FrameData (Fin n) A) (f' : FrameData (Fin (n + 1)) A) : Prop where
  F : f'.F = liftM f.F
  ee : ∀ Y, f'.ee Y = liftM (f.ee Y)
  x : ∀ Y, f'.x Y = liftM (f.x Y)
  xi : ∀ Y, f'.xi Y = liftM (f.xi Y)
  c : f'.c = liftM f.c
  ci : f'.ci = liftM f.ci
  q : f'.q = f.q
  N : f'.N = f.N

variable (L : LevelData A r)

theorem io_lift (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := io_succ x

theorem lifted_l {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.l L Y = liftM (f.l L Y) := by
  simp only [FrameData.l, kapL, liftM_add, liftM_mul, hf.ee Y, io_lift]

theorem lifted_m {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.m L Y = liftM (f.m L Y) := by
  simp only [FrameData.m, FrameData.d, FrameData.di, wt, wti, liftM_mul, liftM_pow, hf.N, hf.c, hf.ci,
    lifted_l L hf, liftM_star, io_lift]

theorem lifted_DD {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y Ya : ℂ) :
    f'.DD Y Ya = liftM (f.DD Y Ya) := by
  simp only [FrameData.DD, liftM_smul, liftM_sub, hf.ee]

theorem tz_lift : (tz L : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (tz L) := io_succ _

theorem lifted_plus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (a : Fin n)
    (Ya : ℂ) : Lifted (f.plus L a Ya) (f'.plus L a.succ Ya) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.plus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_l L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.plus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      lifted_DD hf, tz_lift]
  · simp only [FrameData.plus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus, hf.q]
  · simp only [FrameData.plus, hf.N]

theorem lifted_minus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (b : Fin n)
    (Yb : ℂ) : Lifted (f.minus L b Yb) (f'.minus L b.succ Yb) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.minus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_m L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.minus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      hf.q, lifted_DD hf, tz_lift]
  · simp only [FrameData.minus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus, hf.q]
  · simp only [FrameData.minus, hf.N]

theorem lifted_ofWord (st : Start A) :
    ∀ u : List (Letter ℂ (Fin n)), Lifted (ofWord L st u) (ofWord L st (u.map upL))
  | [] => ⟨by simp [ofWord, Start.frame, liftM_one], fun Y => io_succ _, fun Y => io_succ _, fun Y => io_succ _,
      by simp [ofWord, Start.frame, liftM_one], by simp [ofWord, Start.frame, liftM_one], rfl, rfl⟩
  | l :: u => by
    have ih := lifted_ofWord st u
    rw [List.map_cons]
    by_cases hp : l.plus
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).plus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_plus L ih l.intersection_update_fsHerm_neg_one l.pt
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).minus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_minus L ih l.intersection_update_fsHerm_neg_one l.pt

theorem bT_lift (σ : Site A) : ∀ u : List (Letter ℂ (Fin n)), bT σ (u.map upL) = liftM (bT σ u)
  | [] => by simp [bT, liftM_one]
  | l :: u => by
    rw [List.map_cons, bT, bT, bT_lift σ u, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)) =
      liftM (ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)))
    rw [liftZero_succ_eq_map, ins_succ]

theorem bTA_lift (u : List (Letter ℂ (Fin n))) : TL.bTA L (u.map upL) = liftM (TL.bTA L u) := by
  simp only [TL.bTA, bT_lift]
  rw [← liftRingHom_apply_eq_liftM, map_list_prod, List.map_map]
  rfl

end slots

end Formalism.FourierDecayAlt.P.PBN
end
end

section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section row

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n r : ℕ}

theorem unit_matrix_zero_mul_apply (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (i : Fin 2) (e : Ix (Fin n)) (m : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      if (0 : Fin 2) = i then N (Fin.cons 0 e) m else 0 := by
  rw [Matrix.mul_apply]
  simp only [insert_unit_matrix_zero_apply, ite_mul, one_mul, zero_mul]
  by_cases hi : (0 : Fin 2) = i
  · subst hi
    simp
  · simp [hi]

theorem row_sum (col : Fin 2 → SlopeTestRemainingChoices (Fin (n + 1)) A) (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (e : Ix (Fin n))
    (m : Ix (Fin (n + 1))) :
    ((∑ i : Fin 2, eU (0 : Fin (n + 1)) i 0 * col i) * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      (col 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m := by
  rw [Finset.sum_mul, Matrix.sum_apply, Fin.sum_univ_two, mul_assoc, mul_assoc, unit_matrix_zero_mul_apply, unit_matrix_zero_mul_apply]
  simp

theorem io_mul_apply {S : Type} [Fintype S] [DecidableEq S] (x : A) (N : SlopeTestRemainingChoices S A) (z m : Ix S) :
    (io x * N : SlopeTestRemainingChoices S A) z m = x * N z m := by
  rw [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem firstRow (hWS : TL.WordStep) (L : LevelData A r) (st : Start A) (hA : TL.AHyp L st) (y : ℂ)
    (u : List (Letter ℂ (Fin n))) (hadm : admitted st (⟨true, 0, y⟩ :: u.map upL)) (e : Ix (Fin n)) :
    ((ofWord L st (⟨true, 0, y⟩ :: u.map upL)).F * TL.bTA L (⟨true, 0, y⟩ :: u.map upL)) (Fin.cons 0 e) e1 =
      TL.aP L y * ((ofWord L st u).F * TL.bTA L u) e e1 := by
  rw [hWS A (Fin (n + 1)) r L st ⟨true, 0, y⟩ (u.map upL) hA hadm (Fin.cons 0 e)]
  rw [(lifted_ofWord L st u).F, bTA_lift, ← liftM_mul]
  dsimp only
  rw [row_sum]
  simp only [TL.letterCol, ↓reduceIte, Matrix.cons_val_zero]
  rw [io_mul_apply, liftM_apply]
  congr 1

end row

section act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_e1Vec (M : SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (x : Ix S) :
    P5.act M (Top.firstStateVector Φ) x = (M x e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (e1 : Ix S)]
  · split_ifs with h
    · rfl
    · exact absurd rfl h
  · intro b _ hb
    have hb' : ¬(b = fun _ => 0) := hb
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

end act

theorem cutWord_tail {P : M.Par} {l0 : ℕ} {l : C.Letter} {w : List C.Letter} (h : KB.CutWord P l0 (l :: w)) :
    KB.CutWord P l0 w := by
  refine ⟨fun a => h.1 a.succ, fun a b hab => h.2 a.succ b.succ fun e => hab (Fin.succ_injective _ e)⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rad_plus (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq) (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter) (y : ℝ)
    (hcut : KB.CutWord P p.l0 ((true, y) :: w)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (e : Ix (Fin w.length)) :
    P5.act ((Fr.ofWord L st (D.positionted ((true, y) :: w))).F * P5.bTall L (D.positionted ((true, y) :: w)))
        (Top.firstStateVector Φ) (Fin.cons 0 e) =
      (TL.aP L (y : ℂ)).1 (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  have hA := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st p.l0 hD).1
  have hOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' st p.l0 p.hP.1 p.hl.1
    p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 ((true, y) :: w) hcut.1 hcut.2
  have hadm := hOK.1
  rw [act_e1Vec, act_e1Vec]
  rw [positioned_cons] at hadm ⊢
  exact congrArg (fun x : Q.Pr _ => x.1 Φ) (firstRow hWS L st hA (y : ℂ) (D.positionted w) hadm e)

end main

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

end Formalism.FourierDecayAlt.P
end
end

section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R

def lstN (K m : ℕ) (y : Fin K → ℝ) : List ℝ :=
  List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lstN_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    lstN K ((a : ℕ) + 1) (Function.update y a t) = t :: lstN K a y := by
  unfold lstN
  rw [List.ofFn_succ]
  congr 1
  · rw [dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dif_pos (by simp; omega), dif_pos (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lstN_full (K : ℕ) (z : Fin K → ℝ) : lstN K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold lstN
  congr 1
  funext b
  rw [dif_pos (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

theorem cutWord_plusW {P : M.Par} {l0 : ℕ} {w : List C.Letter} :
    ∀ ys : List ℝ, KB.CutWord P l0 (KB.plusW ys w) → KB.CutWord P l0 w
  | [], h => h
  | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def aaIter {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (F0 : B.Mat k r → (Wq →L[ℂ] Wp)) :
    List ℝ → B.Mat k r → (Wq →L[ℂ] Wp)
  | [] => F0
  | y :: ys => aaTop Bs y (aaIter Bs F0 ys)

def aPIter {V : Type} [AddCommGroup V] [Module ℂ V] {r : ℕ} (L : R.LevelData (Q.Pr V) r) : List ℝ → V → V
  | [], Ψ => Ψ
  | y :: ys, Ψ => (TL.aP L (y : ℂ)).1 (aPIter L ys Ψ)

theorem aaIter_rad (hRA : RadAATop) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ)
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) {F0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF0 : KB.CptCoef Bs F0) {Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (hΨ : Top.IsRadOf P Bs Ψ F0) :
    ∀ ys : List ℝ, KB.CptCoef Bs (aaIter Bs F0 ys) ∧ Top.IsRadOf P Bs (aPIter L ys Ψ) (aaIter Bs F0 ys)
  | [] => ⟨hF0, hΨ⟩
  | y :: ys => by
    obtain ⟨h1, h2⟩ := aaIter_rad hRA P Bs X μ L st l0 hD hF0 hΨ ys
    obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1
    exact ⟨h3, h4 _ h2⟩

theorem rad_plusW (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter)
    (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (e : Ix (Fin w.length)) :
    ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      P5.act ((Fr.ofWord L st (D.positionted (KB.plusW ys w))).F * P5.bTall L (D.positionted (KB.plusW ys w)))
          (Top.firstStateVector Φ) (KB.firstSt ys e) =
        aPIter L ys (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e)
  | [], _ => rfl
  | y :: ys, hc => by
    have ih := rad_plusW hWS P p X μ L st hD w Φ e ys (cutWord_tail hc)
    have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e)
    exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) ih)

end deg

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

theorem degree_top_of_parts : PBN.DegTopOfParts := by
  intro hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  have hcw : KB.CutWord P p.l0 w := cutWord_plusW _ (hcut fun _ => 0)
  obtain ⟨F0, hF0, hF0eq, hV0⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw
  obtain ⟨Φ, hΦ⟩ := radExists p hF
  have hΨ := isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq
  have hIt := aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ

  have hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) =
        p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)]) := by
    intro ys hc
    obtain ⟨Fn, hFn, hFneq, hVn⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc
    rw [hVn]
    have hrad := isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq
    rw [rad_plusW hWS P p X μ L st hD w Φ e ys hc] at hrad
    exact vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _
  set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)])
    with hW
  have hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W := by
    intro a y
    obtain ⟨c, hc, hpoly⟩ := hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1
    refine ⟨c, hc, fun t' => ?_⟩
    simp only [hW]
    rw [lstN_succ]
    exact hpoly t'
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hE
  have hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) := by
    simp only [hW, lstN, List.ofFn_zero, aaIter]
    rw [hV0]
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW]
  rw [lstN_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2, hVit _ (hcut _)]

end Formalism.FourierDecayAlt.P
end
end

section
namespace Formalism.FourierDecayAlt.P

theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

theorem minor_cell : PBN.MinorCell :=
  minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity

theorem radial_raising_top : PBN.RadAATop :=
  radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support

theorem pb_degTop_of_polyTop (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of radial_raising_top hPT

end Formalism.FourierDecayAlt.P
end
