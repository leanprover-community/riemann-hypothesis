import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatDistributionEqZeroBaire
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

section
open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}

def cols (X : Matrix (Fin n) (Fin m) k) : Fin m → Fin n → k := fun j r => X r j

theorem exists_coeff (X : Matrix (Fin n) (Fin m) k) (j : Fin m)
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) :
    ∃ c : Fin m → k, (∀ i, ¬ j < i → c i = 0) ∧ ∀ r, ∑ i, c i * X r i = X r j := by
  obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).1 hj
  refine ⟨l, fun i hi => ?_, fun r => ?_⟩
  · by_contra h
    exact hi (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hx
    have := congrFun hx r
    simpa [Finset.sum_apply, cols] using this

open Classical in

noncomputable def coef (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k :=
  Matrix.of fun i j => if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then
    (exists_coeff X j h).choose i else 0

theorem coef_of_not_mem (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)) (i : Fin m) : coef X i j = 0 := by
  unfold coef
  simp [hj]

theorem sum_coef (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) (r : Fin n) :
    ∑ i, X r i * coef X i j = X r j := by
  unfold coef
  simp only [of_apply, dif_pos hj]
  rw [← (exists_coeff X j hj).choose_spec.2 r]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

noncomputable def clr (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k := 1 - coef X

open Classical in
theorem mul_clr (X : Matrix (Fin n) (Fin m) k) (r : Fin n) (j : Fin m) :
    (X * clr X) r j = if cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0 else X r j := by
  rw [clr, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, mul_apply]
  split_ifs with hj
  · rw [sum_coef X hj, sub_self]
  · simp [coef_of_not_mem X hj]

theorem linInd (X : Matrix (Fin n) (Fin m) k) :
    LinearIndependent k
      (fun j : {j : Fin m // cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)} => cols X j.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  by_contra hne
  set T := s.filter (fun i => g i ≠ 0) with hTdef
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  set j := T.min' hT with hjdef
  have hjT : j ∈ T := T.min'_mem hT
  obtain ⟨hjs, hgj⟩ := Finset.mem_filter.1 hjT
  apply j.2
  have key : g j • cols X j.1 = - ∑ i ∈ s.erase j, g i • cols X i.1 := by
    rw [← Finset.add_sum_erase s _ hjs] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hmem : ∑ i ∈ s.erase j, g i • cols X i.1 ∈ Submodule.span k (cols X '' Set.Ioi j.1) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hgi : g i = 0
    · simp [hgi]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, ?_, rfl⟩)
      have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hi, hgi⟩
      have hle : j ≤ i := T.min'_le i hiT
      have hne : i ≠ j := Finset.ne_of_mem_erase hi
      exact (lt_of_le_of_ne hle (Ne.symm hne) : j < i)
  have : cols X j.1 = (g j)⁻¹ • (g j • cols X j.1) := by rw [smul_smul, inv_mul_cancel₀ hgj, one_smul]
  rw [this, key]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)

theorem exists_decomp (X : Matrix (Fin n) (Fin m) k) :
    ∃ (g : GL (Fin n) k) (s : Matrix (Fin n) (Fin m) k), (∀ i j, s i j = 0 ∨ s i j = 1) ∧
      X * clr X = (g : Matrix (Fin n) (Fin n) k) * s := by
  classical
  have hli := linInd X
  let B := Module.Basis.sumExtend hli
  have hB : ∀ j, B (Sum.inl j) = cols X j.1 := by
    intro j
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  let b := B.reindex e
  have hb : ∀ j, b (e (Sum.inl j)) = cols X j.1 := by
    intro j
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  let G : Matrix (Fin n) (Fin n) k := Matrix.of fun r l => b l r
  have hG : G = (Pi.basisFun k (Fin n)).toMatrix b := by
    ext r l
    simp [G, Module.Basis.toMatrix_apply]
  have hdet : G.det ≠ 0 := by
    rw [hG]
    have := (Pi.basisFun k (Fin n)).invertibleToMatrix b
    exact (isUnit_det_of_invertible _).ne_zero
  let s : Matrix (Fin n) (Fin m) k := Matrix.of fun r j =>
    if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0
    else if r = e (Sum.inl ⟨j, h⟩) then 1 else 0
  refine ⟨GeneralLinearGroup.mkOfDetNeZero G hdet, s, fun i j => ?_, ?_⟩
  · simp only [s, of_apply]
    split_ifs <;> simp
  · ext r j
    rw [mul_clr, GeneralLinearGroup.val_mkOfDetNeZero, mul_apply]
    simp only [s, of_apply]
    split_ifs with hj
    · simp
    · rw [Finset.sum_eq_single (e (Sum.inl ⟨j, hj⟩))]
      · have := congrFun (hb ⟨j, hj⟩) r
        simp only [G, of_apply, if_pos rfl, mul_one, dif_neg hj]
        rw [this]
        simp [cols]
      · intro l _ hl
        simp [hl, dif_neg hj]
      · simp

end GlobalTheory.OrbitsGLParab
end

section
noncomputable section

open Matrix

namespace GlobalTheory.StabPair

theorem det_one_add_vecMulVec {m : Type} [Fintype m] [DecidableEq m] {k : Type} [Field k] (a b : m → k) :
    (1 + vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem stab (k : Type) [Field k] (n x x' : ℕ) (hx : x < n) (t : kˣ) (X : Matrix (Fin n) (Fin (x + x')) k) :
    ∃ (g : GL (Fin n) k) (p : GlobalTheory.SmGL.parab k (GlobalTheory.ThK.MidJac.e2 x x')),
      (g : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((p : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X ∧
      Matrix.GeneralLinearGroup.det g *
        Matrix.GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (GlobalTheory.ThK.MidJac.e2 x x') p 0) = t := by
  set e := GlobalTheory.ThK.MidJac.e2 x x' with he
  by_cases h : ∃ i j, X i (e ⟨1, j⟩) ≠ 0
  · obtain ⟨I, j, hIj⟩ := h
    set J : Fin (x + x') := e ⟨1, j⟩ with hJ
    set c : k := ((t⁻¹ : kˣ) : k) - 1 with hc
    set u : Fin (x + x') → k := Pi.single J 1 with hu
    set ψ : Fin n → k := Pi.single I (X I J)⁻¹ with hψ
    have hψu : ψ ⬝ᵥ (X *ᵥ u) = 1 := by
      rw [hψ, single_dotProduct, hu]
      simp [mulVec, dotProduct_single, inv_mul_cancel₀ hIj]
    set G0 : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (c • (X *ᵥ u)) ψ with hG0
    set P : Matrix (Fin (x + x')) (Fin (x + x')) k := 1 + vecMulVec (ψ ᵥ* X) (c • u) with hP
    have hdetG0 : G0.det = ((t⁻¹ : kˣ) : k) := by
      rw [hG0, det_one_add_vecMulVec, dotProduct_smul, hψu, hc]; simp
    have hdetP : P.det = ((t⁻¹ : kˣ) : k) := by
      rw [hP, det_one_add_vecMulVec, smul_dotProduct, hc]
      have : u ⬝ᵥ (ψ ᵥ* X) = ψ ⬝ᵥ (X *ᵥ u) := by
        rw [dotProduct_comm, dotProduct_mulVec]
      rw [this, hψu]; simp
    have hne : ((t⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
    set g0 : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G0 (hdetG0 ▸ hne)
    set pG : GL (Fin (x + x')) k := Matrix.GeneralLinearGroup.mkOfDetNeZero P (hdetP ▸ hne)
    have hpG : (pG : Matrix _ _ k) = P := rfl
    have hg0 : (g0 : Matrix _ _ k) = G0 := rfl
    have hmem : pG ∈ GlobalTheory.SmGL.parab k e := by
      rw [GlobalTheory.SmGL.mem_parab]
      intro a b hab
      have hb : b ≠ J := by
        rintro rfl
        rw [hJ, GlobalTheory.SmGL.blk_apply] at hab
        have := (GlobalTheory.SmGL.blk e a).isLt
        rw [Fin.lt_def] at hab
        simp at hab
        omega
      have hab' : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
      rw [hpG, hP]
      simp [vecMulVec_apply, hu, Pi.single_apply, hb, one_apply, hab']
    refine ⟨g0⁻¹, ⟨pG, hmem⟩, ?_, ?_⟩
    · have hT : (P)ᵀ = 1 + vecMulVec (c • u) (ψ ᵥ* X) := by
        rw [hP, transpose_add, transpose_one, transpose_vecMulVec]
      have hXQ : X * (1 + vecMulVec (c • u) (ψ ᵥ* X)) = G0 * X := by
        rw [hG0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul, mulVec_smul]
      change ((g0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose (pG : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
      rw [hpG, hT, Matrix.mul_assoc, hXQ, ← Matrix.mul_assoc, ← hg0, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    · have hblk : GlobalTheory.SmGL.leviProj k e ⟨pG, hmem⟩ 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i i'
        rw [GlobalTheory.SmGL.leviProj_apply]
        have hne' : e ⟨0, i'⟩ ≠ J := by
          rw [hJ]; intro hh
          have := congrArg Sigma.fst (e.injective hh)
          simp at this
        simp only [hpG, hP, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, hu, Pi.single_apply, hne',
          if_false, smul_eq_mul, mul_zero, add_zero, Units.val_one]
        by_cases hii : i = i'
        · subst hii; simp
        · have : e ⟨0, i⟩ ≠ e ⟨0, i'⟩ := fun hh => hii (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective hh)).2)
          rw [one_apply_ne this, one_apply_ne hii]
      rw [hblk, map_one, mul_one, map_inv]
      have : Matrix.GeneralLinearGroup.det g0 = t⁻¹ := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hg0, hdetG0]
      rw [this, inv_inv]
  · push_neg at h

    let Y : Matrix (Fin n) (Fin x) k := fun a i => X a (e ⟨0, i⟩)
    have hker : LinearMap.ker (Yᵀ).mulVecLin ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hx)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    have hwX : w ᵥ* X = 0 := by
      funext b
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective b
      match a, i with
      | 0, i =>
        have hi : ∑ r, X r (e ⟨0, i⟩) * w r = 0 := congrFun hw i
        simp only [vecMul, dotProduct, Pi.zero_apply]
        rw [← hi]
        exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
      | 1, i => simp [vecMul, dotProduct, h]
    obtain ⟨r, hr⟩ : ∃ r, w r ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hw0 (funext hcon)
    set v : Fin n → k := Pi.single r (w r)⁻¹ with hv
    have hwv : w ⬝ᵥ v = 1 := by rw [hv, dotProduct_single, mul_inv_cancel₀ hr]
    set G : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (((t : k) - 1) • v) w with hG
    have hdetG : G.det = (t : k) := by
      rw [hG, det_one_add_vecMulVec, dotProduct_smul, hwv]; simp
    set gG : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hdetG ▸ Units.ne_zero t)
    have hgG : (gG : Matrix (Fin n) (Fin n) k) = G := rfl
    refine ⟨gG, 1, ?_, ?_⟩
    · rw [OneMemClass.coe_one, Units.val_one, transpose_one, Matrix.mul_one, hgG, hG, Matrix.add_mul,
        Matrix.one_mul, vecMulVec_mul, hwX]
      ext a b; simp [vecMulVec_apply]
    · rw [map_one, Pi.one_apply, map_one, mul_one]
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hgG]; exact hdetG

end GlobalTheory.StabPair
end
end

section
noncomputable section

namespace GlobalTheory.LocRankBig

open GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected : TotallyDisconnectedSpace k := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem nonarchimedeanGroup_GL (n : ℕ) : NonarchimedeanGroup (GL (Fin n) k) := by
  haveI := totallyDisconnected (k := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (GL (Fin n) k) :=
    ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin n) k => g.val) Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI : NonarchimedeanGroup (KO k (Fin n)) := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  exact NonarchimedeanGroup.nonarchimedean_of_emb (KO k (Fin n)).subtype
    GlobalTheory.SplitFlip.isOpen_KO.isOpenEmbedding_subtypeVal

@[reducible] def act (k : Type) [Field k] (n x x' : ℕ) :
    MulAction (GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x')) (Matrix (Fin n) (Fin (x + x')) k) where
  smul γ X := (γ.1 : Matrix (Fin n) (Fin n) k) * X *
    Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
  one_smul X := by
    show ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
    simp
  mul_smul γ δ X := by
    show ((γ.1 * δ.1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      Matrix.transpose ((γ.2.1 * δ.2.1 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) =
      (γ.1 : Matrix (Fin n) (Fin n) k) * ((δ.1 : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((δ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)) *
        Matrix.transpose ((γ.2 : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)
    simp [Matrix.transpose_mul, Matrix.mul_assoc]

def chi (n x x' : ℕ) (α β : kˣ →* ℂˣ) : GL (Fin n) k × parab k (GlobalTheory.ThK.MidJac.e2 x x') →* ℂˣ :=
  ((deltaHalf k _ * GlobalTheory.ThK.DetProd.twoDet x x' α β).comp
      ((leviProj k (GlobalTheory.ThK.MidJac.e2 x x')).comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * absPow k ((-(n : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp
      ((parab k (GlobalTheory.ThK.MidJac.e2 x x')).subtype.comp (MonoidHom.snd _ _))) *
    ((detChar _ (β * α⁻¹ * absPow k ((-((x + x' : ℕ) : ℝ) / 2 : ℝ) : ℂ)))⁻¹.comp (MonoidHom.fst _ _))

end Local

end GlobalTheory.LocRankBig
end
end
