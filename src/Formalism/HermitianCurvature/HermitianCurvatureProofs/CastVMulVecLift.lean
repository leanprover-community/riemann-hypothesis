import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GenCapRepIntertwine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

section
open Matrix MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

private lemma scalar_pow_mul_diagonal {A S : Type} [Ring A] [Fintype S] [DecidableEq S] (a : A) (n : ℕ)
    (D : Ix S → A) :
    (Matrix.scalar (Ix S) a) ^ n * Matrix.diagonal D = Matrix.diagonal (fun e => a ^ n * D e) := by
  rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem dw_pt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (ws : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 ws)
    (Y₀ : ℝ) (e : Ix S) (p : Polynomial ℂ)
    (hp : ∀ ρ : M.Ty P, p.eval (M.xC P ρ (Y₀ : ℂ)) = Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)
    (y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) (hx : (c, g) ∈ DomR P.k P.r z z')
    (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ) (hBs : IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs) (v : Wq) :
    (act ((Fr.ofWord L st ws).d L) y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
      (((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) ^ ws.length) •
        (y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
          (Polynomial.aeval (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2)) p v) := by
  have hD' := hD
  obtain ⟨hPl, -, hAL, hQQ, hq, -, -, hLS⟩ := hD'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := id hAL
  obtain ⟨κ, hκx, hκxi, -⟩ := Formalism.FourierDecayAlt.P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual
    Formalism.FourierDecayAlt.P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hxiw : ∀ l ∈ ws, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1) := by
    intro l hl
    obtain ⟨-, h1, h2, -⟩ := hw.1.2.2.1 l hl
    exact ⟨(hκxi _ h1).symm, (hκxi _ h2).symm⟩
  have hc : (Fr.ofWord L st ws).c =
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e := by
    rw [← Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr L st st' rfl rfl ws hxiw,
      (Formalism.FourierDecayAlt.P.c_diagonal _ S P.r L st' (M.Ty P) κ (M.x0 P l0) (fun Y => hκx Y) (fun Y => rfl) ws).2.2,
      ← hq]
  have hd : (Fr.ofWord L st ws).d L = Matrix.diagonal (fun e => (L.ζ * L.ζb * L.GGi) ^ ws.length *
      κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)) := by
    rw [Fr.FrameData.d, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_N, hc]
    exact scalar_pow_mul_diagonal _ _ _
  set K := κ (fun ρ => M.xC P ρ (Y₀ : ℂ)) with hKdef
  have hs : M.sgn P l0 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hK : K.1 = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have t := hLS.tau (Y₀ : ℂ)
    rw [hQQ, hκx, Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul, map_smul] at t
    have t1 := congrArg (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) t
    rw [map_mul, map_smul, Matrix.smul_apply, map_smul] at t1
    change M.sgn P l0 • X.t (Y₀ : ℂ) 1 1 = L.GG.1 * (M.sgn P l0 • K.1) at t1
    rw [hGG, mul_smul_comm] at t1
    have h4 : X.fn 4 * K.1 = X.t (Y₀ : ℂ) 1 1 := (smul_right_injective _ hs t1).symm
    have h54 : X.fn 5 * X.fn 4 = 1 := by
      have := congrArg Prod.fst L.GGi_GG
      rw [hGGi, hGG] at this
      exact this
    rw [← h4, ← mul_assoc, h54, one_mul]
  have hκf : κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e) = Polynomial.aeval K p :=
    Formalism.FourierDecayAlt.P5.Kfp.kappa_aeval (NFData.mk L κ (fun _ => 0)) (Y₀ : ℂ) p _ hp
  have hκf1 : (κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 = Polynomial.aeval K.1 p := by
    rw [hκf]
    exact (Polynomial.aeval_algHom_apply (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) K p).symm
  have hT : ∀ (Ψ : RadSp P.k P.r z z' π π') (w : Wq),
      ((K.1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g w =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2) w) := by
    intro Ψ w
    rw [hK]
    exact Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hPl.2.1 hPl.2.2.1 hPl.2.2.2.2.2.2.2.1 hPl.2.2.2.2.2.2.2.2.1 hx Bs hBs _ Ψ w
  have hA := Formalism.FourierDecayAlt.P5.Kfp.aeval_act K.1 _ hT p
  have hpow := Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply X L hAL ws.length
    ((κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 (y e)) (c, g) hx
  have hmul : ∀ a b : Pr (RadSp P.k P.r z z' π π'), (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  rw [hd, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.act_diagonal, hmul, Module.End.mul_apply, hpow,
    _root_.smul_apply, hκf1, hA]
  congr 1
  simp only [fnVal]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
  rfl

end

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section lift

variable {k : ℕ}

theorem frame_lift_list {i r' m : ℕ} (vs : List (Fin (2 * r' + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k (i + r') (vs.map (liftVec k i r')) (fun c => liftVec k i r' (Bs c)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => (PI.QnLevBasicsW.level_group_isotropic_vector k i r' (Bs a) (h1 a)).1, fun a b => ?_, fun a x hx => ?_⟩
  · rw [PIQnLT.herm_liftVec]; exact h2 a b
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    rw [PIQnLT.herm_liftVec]
    exact h3 a v hv

theorem frame_lift_cast {i r' n m : ℕ} (hn : i + r' = n) (vs : List (Fin (2 * r' + k + 1) → ℂ))
    (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k n (vs.map fun v => D.castV hn (liftVec k i r' v)) (fun c => D.castV hn (liftVec k i r' (Bs c))) := by
  subst hn
  simp only [JCTx5.castV_rfl]
  exact frame_lift_list vs Bs h

theorem capRep_lift_cast {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {i r' n m : ℕ} (hn : i + r' = n)
    (π0 : Mx k n → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    capRep k n π0 (fun c => D.castV hn (liftVec k i r' (Bs c))) w v =
      capRep k r' (fun y => π0 (D.castM hn (ιLev k i r' y))) Bs w v := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact JCTx5.capRep_lift π0 Bs w v

theorem castV_mulVec_lift {i r' n : ℕ} (hn : i + r' = n) (M : B.Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    D.castM hn (ιLev k i r' M) *ᵥ D.castV hn (liftVec k i r' v) = D.castV hn (liftVec k i r' (M *ᵥ v)) := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact PIQnLT.mulVec_liftVec M v

end lift

section types

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tp_eigen_lev {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (ρ : M.Ty P) (w : ℂ) (u : Wp) :
    capRep P.k (P.r - P.r) (p.T.bs P.r).π (fun a => m₀r *ᵥ Bs' a) w (p.TP.E ρ u) =
      M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • p.TP.E ρ u := by
  have hn : P.r + (P.r - P.r) = P.r := by omega
  obtain ⟨hν, hm, hbase⟩ := hLF
  have hB1 := Topx1.vecw_frame_fwd (p.T.bs P.r) hbase hB
  have hB2 := frame_lift_cast hn _ _ hB1
  have ez : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have ee : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← castV_mulVec_lift hn, hm, hν]
  simp only [List.map_cons, List.map_nil, ez, ee] at hB2
  have h := p.TP.eigen _ hB2 ρ w u
  rw [capRep_lift_cast hn] at h
  have hπ : (fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y))) = (p.T.bs P.r).π :=
    funext fun y => (p.T.π_lev P.r le_rfl y).symm
  rw [hπ] at h
  exact h

theorem aeval_intertwine (V : Wq →L[ℂ] Wp) (R : Module.End ℂ Wq) (Lf : Module.End ℂ Wp)
    (h : ∀ v, V (R v) = Lf (V v)) (p : Polynomial ℂ) : ∀ v, V (Polynomial.aeval R p v) = Polynomial.aeval Lf p (V v) := by
  induction p using Polynomial.induction_on with
  | C a => intro v; simp
  | add p q hp hq => intro v; simp [hp, hq]
  | monomial n a ih =>
    intro v
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eR : Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n) * R := by rw [map_mul, Polynomial.aeval_X]
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    rw [e1, eR, eL, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_eigen (Lf : Module.End ℂ Wp) (x : Wp) (c : ℂ) (h : Lf x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval Lf p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a ih =>
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    have ev : (Polynomial.C a * Polynomial.X ^ n * Polynomial.X).eval c =
        (Polynomial.C a * Polynomial.X ^ n).eval c * c := by rw [Polynomial.eval_mul, Polynomial.eval_X]
    rw [e1, eL, Module.End.mul_apply, h, map_smul, ih, smul_smul, ev, mul_comm]

theorem poly_types {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (V : Wq →L[ℂ] Wp)
    (hV : PBI.GrpInt (p.T.bs P.r) ν'r m₀r V) (hex : ∑ ρ : M.Ty P, (p.TP.E ρ).comp V = V)
    (Y₀ : ℂ) (q : Polynomial ℂ) (v : Wq) :
    V (Polynomial.aeval (qdet (Qr.EB (p.T.bs P.r).π' Bs') (Y₀ + ((P.k : ℂ) - 2) / 2)) q v) =
      ∑ ρ : M.Ty P, q.eval (M.xC P ρ Y₀) • p.TP.E ρ (V v) := by
  set S := p.T.bs P.r
  have hbase := hLF.2.2
  have hBz' : IsFrameOf P.k (P.r - P.r) [S.z'] Bs' :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBz : IsFrameOf P.k (P.r - P.r) [S.z] (fun a => m₀r *ᵥ Bs' a) :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (Topx1.vecw_frame_fwd S hbase hB)
  have hglR := Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k (P.r - P.r) (P.k - 1) S.z' S.π' Bs' ⟨S.π'_rep, S.π'_cont⟩ hBz'
  have hglL := Formalism.FourierDecayAlt.P.frame_general_linear Wp P.k (P.r - P.r) (P.k - 1) S.z S.π (fun a => m₀r *ᵥ Bs' a)
    ⟨S.π_rep, S.π_cont⟩ hBz
  set w0 : ℂ := Y₀ + ((P.k : ℂ) - 2) / 2
  have hint : ∀ v, V (qdet (Qr.EB S.π' Bs') w0 v) = qdet (Qr.EB S.π (fun a => m₀r *ᵥ Bs' a)) w0 (V v) := by
    intro v
    rw [← hglR.2, ← hglL.2]
    exact (PBI.gen_capRep_intertwine S hbase V hV hB w0 v).symm
  rw [aeval_intertwine V _ _ hint q v]
  conv_lhs => rw [← hex]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine aeval_eigen _ _ _ ?_ q
  rw [← hglL.2, tp_eigen_lev p ν'r m₀r hLF hB ρ w0 (V v)]
  congr 2
  ring

end types

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end
