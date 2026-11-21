import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LeadingMinorSecondProj

section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Asm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ind_det (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R} (γ : IsoMbe Z₁.Z Z₂.Z)
    (θ θ' : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (h : Ind hs γ θ) (h' : Ind hs γ θ') : θ = θ' := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H l =>
    obtain ⟨l₂, hl₂⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk l))
    exact (h l l₂ hl₂.symm).trans (h' l l₂ hl₂.symm).symm

theorem map_cj_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map M.L.cj = Zh := by
  ext a b; simp [M.L.cj_cj]

theorem det_map_cj {n : Type} [Fintype n] [DecidableEq n] (Zh : Matrix n n E) :
    (Zh.map M.L.cj).det = M.L.cj Zh.det := by
  have := RingHom.map_det (M.L.cj : E →+* E) Zh
  simpa [RingHom.mapMatrix_apply] using this.symm

theorem head_map_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ((Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← det_map_cj]
  rfl

theorem gHyp_cj {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ : M.Mat (r + 1)}
    (h : GHyp M g T T' TT Zh Z Zσ) : GHyp M g T T' TT (Zh.map M.L.cj) Zσ Z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h5, by rw [map_cj_cj]; exact h4, by rw [det_map_cj]; exact h6.map _, ?_⟩
  rw [det_map_cj, head_map_cj, M.L.cj_cj, M.L.cj_cj, mul_comm (M.L.cj Zh.det),
    mul_comm (M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)]
  exact h7

theorem kapEq_cj {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : KapEq Zh₁ Zh₂) :
    KapEq (Zh₁.map M.L.cj) (Zh₂.map M.L.cj) := by
  unfold KapEq at h ⊢
  rw [det_map_cj, det_map_cj, head_map_cj, head_map_cj, ← map_mul, ← map_mul, h]

end Asm


end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

def StepZsig0 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] →
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
      Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' → IsUnit Zh.det →
      (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      (∃ TT : M.R, g.e (TT : E) = (T, T')) ∧ IsUnit (Z.map M.R.subtype).det ∧
      ∃ Zσ : M.Mat (r + 1), Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T'

def SplitIsometryCountIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), T ∈ 𝒪[F] → (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    (Zh₁.submatrix Fin.castSucc Fin.castSucc).det = 0 → (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem splitIsoCount_of_components (hZ : StepZsig0) (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : SplitIsometryCountIntegral := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT huv hc Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ s₁ s₂
  obtain ⟨⟨TT, hTT⟩, hZ₁, Zσ₁, hσ₁⟩ := hZ F E M g hs r T T' hT huv hc Zh₁ Z₁ e₁ u₁ s₁
  obtain ⟨_, hZ₂, Zσ₂, hσ₂⟩ := hZ F E M g hs r T T' hT huv hc Zh₂ Z₂ e₂ u₂ s₂
  let W₁ : M.Mat (r + 1) := ⟨Z₁, hZ₁⟩
  let W₂ : M.Mat (r + 1) := ⟨Z₂, hZ₂⟩
  have gh : ∀ {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {W Wσ : M.Mat (r + 1)},
      W.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' →
      Wσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' →
      IsUnit Zh.det → (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0 →
      GHyp M g T T' TT Zh W Wσ := by
    intro Zh W Wσ hW hWσ hu hz
    refine ⟨huv, hc, hTT, hW, hWσ, hu, ?_⟩
    rw [hz, map_zero, zero_mul, mul_zero, sub_zero]
    exact hu.mul (hu.map M.L.cj)
  have G₁ : GHyp M g T T' TT Zh₁ W₁ Zσ₁ := gh e₁ hσ₁ u₁ s₁
  have G₂ : GHyp M g T T' TT Zh₂ W₂ Zσ₂ := gh e₂ hσ₂ u₂ s₂
  have K : KapEq Zh₁ Zh₂ := by
    unfold KapEq
    rw [s₁, s₂, mul_zero, mul_zero]
  have Gσ₁ := gHyp_cj G₁
  have Gσ₂ := gHyp_cj G₂
  have Kσ := kapEq_cj (M := M) K
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K]
  refine Nat.card_eq_of_bijective
    (fun p => (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose)
    ⟨?_, ?_⟩
  · intro p p' hpp
    have i1 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.2.1 p.2.2.2.1).choose_spec
    have i2 := (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p'.1.1 p'.2.1 p'.2.2.2.1).choose_spec
    simp only at hpp
    rw [hpp] at i1
    have q1 : p.1.1 = p'.1.1 := ind_det hs _ _ _ i1 i2
    have hb := p'.2.2.2.2.2
    rw [← q1] at hb
    have q2 : p.1.2 = p'.1.2 :=
      h5 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K p.1.1 p.1.2 p'.1.2 p.2.2.2.2.2 hb
    exact Subtype.ext (Prod.ext q1 q2)
  · intro γ
    obtain ⟨θ₁, o₁, m₁, i₁⟩ := h2 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨γ', hγ'⟩ := h4 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K γ
    obtain ⟨θ₂, o₂, m₂, i₂⟩ := h2 F E M g hs r T T' TT (Zh₁.map M.L.cj) (Zh₂.map M.L.cj)
      Zσ₁ Zσ₂ W₁ W₂ Gσ₁ Gσ₂ Kσ γ'
    refine ⟨⟨(θ₁, θ₂), o₁, o₂, m₁, m₂, hγ' θ₁ θ₂ i₁ i₂⟩, ?_⟩
    exact h3 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ _ γ
      (h1 F E M g hs r T T' TT Zh₁ Zh₂ W₁ W₂ Zσ₁ Zσ₂ G₁ G₂ K θ₁ o₁ m₁).choose_spec i₁

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzplus_det_unit (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) (h0 : (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det := by
  have hne : ∀ i : Fin r, (Fin.castSucc i = Fin.last r) = False := fun i => eq_false (Fin.castSucc_ne_last i)
  have h1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph1 g) =
      ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map (ph1 g) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, firstProj_apply, zz_comp hs,
      hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul]
  have h2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph2 g) =
      (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map (ph2 g)).transpose := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      secondProj_apply, zz_comp hs, hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul, neg_mul]
  have hS1 : ph1 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h1, Matrix.det_smul, ← det_ph, h0, map_zero, mul_zero]
  have hS2 : ph2 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h2, Matrix.det_smul, Matrix.det_transpose, ← det_ph, h0, map_zero, mul_zero]
  have hS : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    apply g.e.injective
    rw [map_zero]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_zero, ← firstProj_apply]
      exact hS1
    · rw [Prod.snd_zero, ← secondProj_apply]
      exact hS2
  have hm : (ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc =
      (HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [ZZm, Matrix.submatrix_apply, Matrix.add_apply, Matrix.of_apply, cor, hne, false_and, if_false,
      add_zero]
  have key : HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (-(g.e.symm (-T / (g.q : F), T' / (g.q : F)))) := by
    ext a b
    simp only [ZZm, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  rw [key, det_add_cor, hm, hS, mul_zero, add_zero]
  exact unit_zzm hs Zh T T' hu

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

private theorem mem_R_of_split_coords_integral_congr (hs : M.split = some g) (x : E) (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) (hd : ∃ c : 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c) : x ∈ M.R := by
  obtain ⟨c, hc⟩ := hd
  unfold Model.R
  rw [hs]
  refine Subring.mem_comap.2 (Subring.mem_map.2 ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩)
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨c, Subtype.ext ?_⟩
    simp [hc, mul_comm]
  · rfl

theorem zsig_mem (hs : M.split = some g) (T T' : F) (c : 𝒪[F]) (hc : T - T' = (g.q : F) ^ 2 * c)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (a b : Fin (r + 1)) :
    HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  have hmem : HermSp.ZZplusOf M Zh T T' b a ∈ M.R := by
    have := congrFun (congrFun hZ b) a
    simp only [Matrix.map_apply, Subring.coe_subtype] at this
    rw [← this]
    exact (Z b a).2
  obtain ⟨u1, u2, d, hd⟩ := comp_of_mem_R hs hmem
  rw [zz_comp hs] at u1 u2 hd
  dsimp only at u1 u2 hd
  have hT : T = T' + (g.q : F) ^ 2 * c := by linear_combination hc
  by_cases hab : a = Fin.last r ∧ b = Fin.last r
  · simp only [if_pos hab.symm] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, if_pos hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - -T / g.q =
          -(-((g.e (Zh a b)).2 / g.q) - T' / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u2) (mul_mem g.q.2 c.2)
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - T' / g.q =
          -((g.e (Zh b a)).1 / g.q - -T / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u1) (mul_mem g.q.2 c.2)
    · rw [← hd]
      ring
  · have hba : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h => hab (And.symm h)
    simp only [if_neg hba] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, if_neg hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - 0 = -(-((g.e (Zh a b)).2 / g.q) - 0) by ring]
      exact neg_mem u2
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - 0 = -((g.e (Zh b a)).1 / g.q - 0) by ring]
      exact neg_mem u1
    · rw [← hd]
      ring

theorem stepZsig0 : StepZsig0 := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT _ hcex Zh Z hZ hu h0
  obtain ⟨c, hc⟩ := hcex
  have hcj : IsUnit (Zh.map M.L.cj).det := by
    rw [det_map_cj]
    exact hu.map M.L.cj
  have hcj0 : ((Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [show (Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc =
        (Zh.submatrix Fin.castSucc Fin.castSucc).map M.L.cj from rfl, det_map_cj, h0, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · have hT' : T' ∈ 𝒪[F] := by
      rw [show T' = T - (g.q : F) ^ 2 * c by linear_combination -hc]
      exact sub_mem hT (mul_mem (pow_mem g.q.2 2) c.2)
    refine ⟨⟨g.e.symm (T, T'), mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨g.q * c, ?_⟩⟩, ?_⟩
    · simpa using hT
    · simpa using hT'
    · simp only [AlgEquiv.apply_symm_apply]
      push_cast
      rw [hc]
      ring
    · exact g.e.apply_symm_apply _
  · rw [hZ]
    exact zzplus_det_unit hs Zh T T' hu h0
  · refine ⟨⟨Matrix.of fun a b => ⟨HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b,
      zsig_mem hs T T' c hc Zh Z hZ a b⟩, ?_⟩, ?_⟩
    · have hmap : ((Matrix.of fun a b => (⟨HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b,
          zsig_mem hs T T' c hc Zh Z hZ a b⟩ : M.R)).map M.R.subtype) =
          HermSp.ZZplusOf M (Zh.map M.L.cj) T T' := by
        ext a b
        rfl
      rw [hmap]
      exact zzplus_det_unit hs _ T T' hcj hcj0
    · ext a b
      rfl

theorem thetaMbe0_of_detG_coordG_splitIsoCount (h0 : DetG) (h1 : CoordG) (h2 : SplitIsometryCountIntegral) (M : Model F E) (r n : ℕ) :
    ThetaMbe0 M r n true := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hD2 : H.Dl f₂ f₂' r = 0 := dl_zero_two hyp hD
  have hh1 : ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [← dl_eq_det]; exact hD
  have hh2 : ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [← dl_eq_det]; exact hD2
  have hU1 : IsUnit (H.Zhat t₁.f t₁.f').det := by
    have := dl_succ_unit hyp
    rwa [dl_full] at this
  have hU2 : IsUnit (H.Zhat f₂ f₂').det := by
    refine h0 F E M g hs r _ t₁.T t₁.T' hh2 ?_
    rw [← e₂]; exact Z₂.unit
  have hR : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    rw [← e₂]
    exact (Z₂.Z a b).2
  have hsp := hyp.1.1.2.2.2.2.2 g hs
  have hT0 : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  rw [h1 F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD (by rw [dl_full]; exact hU2) hR]
  exact h2 F E M g hs r t₁.T t₁.T' hT0 hsp.1 hsp.2.1 _ _ Z₁.Z Z₂.Z e₁ e₂ hU1 hU2 hh1 hh2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
