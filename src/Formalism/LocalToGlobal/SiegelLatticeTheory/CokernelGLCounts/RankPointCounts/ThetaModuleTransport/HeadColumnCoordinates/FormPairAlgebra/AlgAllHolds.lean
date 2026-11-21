import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LiftRepMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.LamSZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG

section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

private theorem exists_cj_combination_of_isUnit_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (y' : Fin (r + 1) → O) :
    ∃ w : Fin (r + 1) → E, ∀ b, (y' b : E) = ∑ a, cj (Z.map O.subtype a b) * w a := by
  set N : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (Z.map O.subtype).transpose.map cj with hN
  have hdet : IsUnit N.det := by
    have h1 : N.det = cj (Z.map O.subtype).det := by
      rw [hN, ← Matrix.det_transpose (Z.map O.subtype)]
      exact (RingHom.map_det cj _).symm
    rw [h1]
    exact hu.map cj
  refine ⟨N⁻¹.mulVec (fun j => (y' j : E)), fun b => ?_⟩
  have h2 : N.mulVec (N⁻¹.mulVec (fun j => (y' j : E))) = fun j => (y' j : E) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have h3 := congrFun h2 b
  rw [← h3]
  simp [Matrix.mulVec, dotProduct, hN]

theorem pair_eG (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁) (p : PairSet O cj hO Z₁ Z₂) :
    p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  have hlam : lamS O cj Z₂ y₂' = lamS O cj Z₁ (Pi.single (Fin.last r) 1) :=
    p.2.2.1 (Pi.single (Fin.last r) 1) y₂' hy₂'.symm
  set d : Fin (r + 1) → O := y₂' - Pi.single (Fin.last r) 1 with hd
  obtain ⟨w, hw⟩ := exists_cj_combination_of_isUnit_det O cj Z₂ hu₂ d
  have hlast : w (Fin.last r) = 0 := by
    rw [← lamS_cjT O cj Z₂ hu₂ d w hw, hd, lamS_sub, hlam, lamS_e', lamS_e', hκ, sub_self]
  have hmem : ∀ a, w a ∈ O := by
    intro a
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1.symm (Submodule.Quotient.mk (Pi.single a 1)))
    have h1 : p.1.1 (Submodule.Quotient.mk c) = Submodule.Quotient.mk (Pi.single a 1) := by
      rw [hc]
      simp
    have hB := p.2.2.2 c (Pi.single (Fin.last r) 1) (Pi.single a 1) y₂' h1 hy₂'.symm
    have hL := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 c (Pi.single a 1) h1
    have hsplit : y₂' = d + Pi.single (Fin.last r) 1 := by
      rw [hd]
      abel
    rw [hsplit, bRaw_add_right, bRaw_e, bRaw_e, hL, add_sub_cancel_right,
      bRaw_cjT O cj hcj Z₂ hu₂ _ d w hw] at hB
    have hs : (∑ b : Fin (r + 1), cj (w b) * ((Pi.single a (1 : O) : Fin (r + 1) → O) b : E)) = cj (w a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hs] at hB
    have := hO _ hB
    rwa [hcj] at this
  have hdmem : d ∈ headCols (cjT O cj hO Z₂) := by
    rw [mem_headCols_iff]
    refine ⟨fun a => ⟨w a, hmem a⟩, Subtype.ext hlast, ?_⟩
    funext b
    apply Subtype.ext
    rw [cjT_mulVec_coe]
    exact hw b
  rw [← hy₂']
  exact (Submodule.Quotient.eq _).2 hdmem

section Bwd

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
  (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
  (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
  (hκ : kap O Z₂ = kap O Z₁)
  (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
  (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)

include hcj hu₁ hu₂ hκ hG₁ hG₂ in

theorem form_diff (p : PairSet O cj hO Z₁ Z₂) (Y Y₂ W W₂ : Ix r → O)
    (hy : p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j))
    (hy' : p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j))
    (hw : p.1.1 (Submodule.Quotient.mk fun j => W (Sum.inl j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inl j))
    (hw' : p.1.2 (Submodule.Quotient.mk fun j => W (Sum.inr j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inr j)) :
    formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : lamC (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Y (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hy
  have hs : lamStarC cj (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Y (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hy'
  have hlw : lamC (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((W (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hw
  have hsw : lamStarC cj (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((W (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hw'
  obtain ⟨hc1, hc2⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ _ _ hG₁ hG₂ hκ Y Y₂ hl hs
  have hb1 := p.2.2.2 _ _ _ _ hy hw'
  have hb2 := p.2.2.2 _ _ _ _ hw hy'
  rw [formC_eqG O cj hcj Z₂ hu₂ _ _ hG₂, formC_eqG O cj hcj Z₁ hu₁ _ _ hG₁, hc1, hc2, hlw, hsw]
  have key : ∀ a b c d X X' : E,
      (a + cj b + X + X') - (c + cj d + X + X') = (a - c) + cj (b - d) := by
    intro a b c d X X'
    rw [map_sub]
    ring
  rw [key]
  exact add_mem hb1 (hO _ hb2)

end Bwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

section
namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

private theorem bwdEx_lemma {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
    (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O) {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) ≃ₗ[O] LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂))
    (hb : γ (LocCntCommon.bCls Z₁) = LocCntCommon.bCls Z₂) (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂)
    (hbs : γs (LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₂))
    (hes : γs (LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₂))
    (Y : LocCntCommon.Ix r → O) :
    LocCnt0LAlg.thetaOf O cj hO t t' γ γs hb he hbs hes (Submodule.Quotient.mk Y) =
      iL O cj hO Z₂ t t' (γ (Submodule.Quotient.mk fun j => Y (Sum.inl j))) +
        iR O cj hO Z₂ t t' (γs (Submodule.Quotient.mk fun j => Y (Sum.inr j))) := by
  have h1 := LocCnt0LAlg.liftOf_spec O (γ : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
    (fun j => Y (Sum.inl j))
  have h2 := LocCnt0LAlg.liftOf_spec O (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) →ₗ[O]
    LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂)) (fun j => Y (Sum.inr j))
  rw [LinearEquiv.coe_coe] at h1 h2
  rw [← h1, ← h2, ← mk_elim]
  rfl

private theorem linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero {E : Type} [CommRing E] (O : Subring E) {r : ℕ}
    {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂) (y : Fin (r+1) → O)
    (hy : ∀ a : Fin r, y a.castSucc = 0) :
    γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
  have hy' : y = y (Fin.last r) • Pi.single (Fin.last r) (1 : O) := by
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp
    · simp [hy a, Pi.single_apply, Fin.castSucc_ne_last]
  rw [hy', Submodule.Quotient.mk_smul, map_smul]
  unfold LocCntCommon.eCl at he
  rw [he, ← Submodule.Quotient.mk_smul]

theorem bwdEx : BwdEx := by
  intro E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hZ₁ hZ₂ hk hG₁ hG₂ p
  have hb := p.2.1.1
  have he := p.2.1.2
  have hbs := LocCnt0LAlg.pair_b O cj hcj hO hZ₁ hZ₂ p
  have hes := pair_eG O cj hcj hO hZ₁ hZ₂ hk p
  set θ := LocCnt0LAlg.thetaOf O cj hO t t' p.1.1 p.1.2 hb he hbs hes with hθdef
  have hθ := bwdEx_lemma O cj hO t t' p.1.1 p.1.2 hb he hbs hes
  rw [← hθdef] at hθ
  have hlift : ∀ Y : LocCntCommon.Ix r → O, ∃ Y₃ : LocCntCommon.Ix r → O,
      θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₃ ∧
      p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inl j)) ∧
      p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inr j)) := by
    intro Y
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
    obtain ⟨b, hb'⟩ := Submodule.Quotient.mk_surjective _
      (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
    refine ⟨Sum.elim a b, ?_, ha.symm, hb'.symm⟩
    rw [hθ, ← ha, ← hb', mk_elim]
  have hsplit : ∀ Y₂ : LocCntCommon.Ix r → O,
      (Submodule.Quotient.mk Y₂ : LocCntCommon.DDc O cj (Z₂.map O.subtype) ↑t ↑t') =
        iL O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)) +
          iR O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)) := by
    intro Y₂
    rw [← mk_elim]
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    obtain ⟨Y₃, hY3, hY3l, hY3r⟩ := hlift Y
    obtain ⟨W₃, hW3, hW3l, hW3r⟩ := hlift W
    have hfd := form_diff O cj hcj hO t t' hZ₁ hZ₂ hk hG₁ hG₂ p Y Y₃ W W₃ hY3l hY3r hW3l hW3r
    rw [hY3] at hY
    rw [hW3] at hW
    have e1 := (Submodule.Quotient.eq _).1 hY.symm
    have e2 := (Submodule.Quotient.eq _).1 hW.symm
    have f1 := LocCnt0LAlg.formC_rel_left O cj (Z₂.map O.subtype) ↑t ↑t' hG₂ hO _ W₂ e1
    have f2 := LocCnt0LAlg.formC_rel_right O cj hcj (Z₂.map O.subtype) ↑t ↑t' ht ht' hG₂ hO Y₃ _ e2
    rw [LocCnt0LAlg.formC_sub_left] at f1
    rw [LocCnt0LAlg.formC_sub_right] at f2
    have hsum := O.add_mem (O.add_mem f1 f2) hfd
    convert hsum using 1
    ring
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y (Sum.inl j)) hY0
      have hs := p.2.2.1 _ _ hy₂'.symm
      refine ⟨Sum.elim (fun j => Y (Sum.inl j)) y₂', fun a => hY0 a, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ, hl, ← hy₂', mk_elim]
      · exact hs.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)))
      have hp2 : p.1.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j) := by
        rw [hy', LinearEquiv.apply_symm_apply]
      have hs := p.2.2.1 _ _ hp2
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y₂ (Sum.inl j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim (fun j => Y₂ (Sum.inl j)) y'), ↑(Y₂ (Sum.inl (Fin.last r))),
        LocCntCommon.lamStarC cj (Z₁.map O.subtype) fun b => ↑(y' b)),
        ⟨Sum.elim (fun j => Y₂ (Sum.inl j)) y', fun a => hY0 a, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hl, hp2, hsplit]
      · exact hs.symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y (Sum.inr j)) hY0
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hy₂.symm)
      refine ⟨Sum.elim y₂ (fun j => Y (Sum.inr j)), fun b => hY0 b, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ, hr, ← hy₂, mk_elim]
      · exact hl.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)))
      have hp1 : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j) := by
        rw [hy, LinearEquiv.apply_symm_apply]
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hp1)
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y₂ (Sum.inr j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim y (fun j => Y₂ (Sum.inr j))),
        LocCntCommon.lamC (Z₁.map O.subtype) (fun a => ↑(y a)), ↑(Y₂ (Sum.inr (Fin.last r)))),
        ⟨Sum.elim y (fun j => Y₂ (Sum.inr j)), fun b => hY0 b, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hr, hp1, hsplit]
      · exact hl.symm
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iL_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim y 0 : LocCntCommon.Ix r → O) (Sum.inr j)) :
        LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁)) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, add_zero]
    rfl
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iR_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim 0 y : LocCntCommon.Ix r → O) (Sum.inl j)) :
        LocCntCommon.MbMod Z₁) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, zero_add]
    rfl

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end

section
namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem stepPairG_holds : StepPairG := stepPairG_of_fwd_bwd fwdEx bwdEx

theorem algAll_holds : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := algAll_of stepPairG_holds

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
