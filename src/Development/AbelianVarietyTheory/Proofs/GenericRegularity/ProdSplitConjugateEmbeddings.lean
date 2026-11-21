import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameExBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal

section
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.WeightLie

open ReciprocityTheory.ChartRestriction.G GlobalTheory.FrameNormLie

theorem norm_diag_eq_norm_diag {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {A B : Matrix n n ℂ} (hA : Supp t w A) (hB : Supp t w B)
    (hB0 : ∀ j, B j j ≠ 0) (d : n → ℂ) (hd : ∀ j, d j ≠ 0)
    (h : Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ)) = Bᵀ * (Matrix.diagonal d * B.map (starRingEnd ℂ)))
    (a : n) : ‖A a a‖ = ‖B a a‖ := by
  have hu : IsUnit B.det := by
    rw [PerBor.det_of_support t w hinj B hB, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hB0 j
  have hi : Supp t w B⁻¹ := PerBor.inv_support t w B hu hB
  have h1 := norm_diag_eq_one hinj (hA.mul hi) d hd (by
    have e : B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]; simp
    have e' : B⁻¹ᵀ * Bᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    calc _ = B⁻¹ᵀ * (Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ))) * B⁻¹.map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᵀ * Bᵀ) * Matrix.diagonal d * (B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ)) := by
          rw [h]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [e, e', Matrix.one_mul, Matrix.mul_one]) a
  rw [Supp.mul_diag hinj hA hi, PerBor.inv_diag t w hinj B hu hB, norm_mul, norm_inv] at h1
  exact (mul_inv_eq_one₀ (norm_ne_zero_iff.2 (hB0 a))).1 h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem moveMat_diag_ne {Ψ : Finset (E →+* ℂ)} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r) {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (j : Fin g) : PerBor.moveMat q idx b j j ≠ 0 := by
  rw [PerBor.moveMat_diag _ idx hb]
  split_ifs
  · exact PerMove.bor_diag_ne hb _ _
  · exact inv_ne_zero (PerMove.bor_diag_ne hb _ _)

theorem exists_tri_pair {α : Type} [Fintype α] (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {t : Fin g → α}
    {w : Fin g → ℕ} (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (hs : ∀ b ∈ Bor X.Ψ r, Supp t w (PerBor.moveMat X.p0 idx b)) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ T T' : Matrix (Fin g) (Fin g) ℂ, Supp t w T ∧ Supp t w T' ∧ (∀ j, T j j ≠ 0) ∧
      (∀ j, T' j j = T j j * (PerBor.moveMat X.p0 idx b j j)⁻¹) ∧
      (∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T *ᵥ perVec X idx x v) (T *ᵥ perVec X idx x v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ)) ∧
      ∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T' *ᵥ perVec X idx (rmul (lact γ x) b) v)
        (T' *ᵥ perVec X idx (rmul (lact γ x) b) v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ) := by
  obtain ⟨x₀, b₀, hb₀, hgr, rfl⟩ :=
    (UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  have hd : IsUnit (PerBor.moveMat X.p0 idx b).det := by
    rw [PerBor.det_of_support t w hinj _ (hs b hb), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => moveMat_diag_ne _ idx hb j
  have hm : ∀ b ∈ Bor X.Ψ r, ∀ y v, PerBor.moveMat X.p0 idx b *ᵥ perVec X idx y v = perVec X idx (rmul y b) v :=
    fun b hb y v => (PerBor.moveMat_mulVec X.p0 idx hb X.Gm y v (perVec X idx y v) (perVec X idx (rmul y b) v)
      (fun _ => rfl) (fun _ => rfl)).symm
  have hi : Supp t w (PerBor.moveMat X.p0 idx b)⁻¹ := PerBor.inv_support t w _ hd (hs b hb)
  have he : rmul (lact γ x) b₀ = lact γ (rmul x b₀) := funext fun τ =>
    Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b₀ τ)
  have h2 : ∀ v, (PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹) *ᵥ
      perVec X idx (rmul (lact γ x) b) v = perVec X idx (lact γ (rmul x b₀)) v := fun v => by
    rw [← hm b hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, hm b₀ hb₀, he]
  refine ⟨PerBor.moveMat X.p0 idx b₀, PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹, hs b₀ hb₀,
    (hs b₀ hb₀).mul hi, moveMat_diag_ne _ idx hb₀, fun j => ?_, fun v v' => ?_, fun v v' => ?_⟩
  · rw [Supp.mul_diag hinj (hs b₀ hb₀) hi, PerBor.inv_diag t w hinj _ hd (hs b hb)]
  · rw [hm b₀ hb₀, hm b₀ hb₀, im_diag_ortho X idx _ hgr]
  · rw [h2, h2, im_diag_ortho X idx _ fun τ => (AR.Up.PairUnfoldPf.gram_lact X hγ _ τ).trans (hgr τ)]

end GlobalTheory.WeightLie
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.BorelDiag

open GlobalTheory.FrameNormLie GlobalTheory.WeightLie

set_option maxHeartbeats 1000000 in

theorem norm_diag_eq_norm_bdiag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom), ∀ γ ∈ (U.X k).Γ, ∀ b ∈ Bor (U.X k).Ψ r, ∀ (hx : rmul (lact γ x.1) b ∈ (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) (U.un k ⟨_, hx⟩) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ‖toC (t (some ⟨τ, i⟩) : CAt σ)‖ = ‖bdiag (U.X k) b (relab c σ τ) i‖ := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k' x γ hγ b hb hx' t hB τ₀ i₀
  obtain ⟨x', hxx, hB⟩ : ∃ x' : (U.X k').dom, x'.1 = rmul (lact γ x.1) b ∧ FrBor t (U.un k' x) (U.un k' x') :=
    ⟨⟨_, hx'⟩, rfl, hB⟩
  obtain ⟨hr, hty0, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨hp0, hty⟩ := hty0 k'
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k' x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  replace hbij : Function.Bijective (relab c σ) := hbij
  replace hrt : ∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := hrt
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k').Ψ (U.X k').cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (U.X k').Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ (U.X k').Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ (U.X k').Ψ ∧
        (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  have hper : ∀ (x : Frame (U.X k').Ψ r) v j, perFr (U.X k') x v (relab c σ (e j).1)
      (e j).2 = perVec (U.X k') idx x v j := by
    intro x v j
    unfold perVec
    have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ (U.X k').Ψ from hτ), dif_pos hn]
      rfl
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ b ∈ Bor (U.X k').Ψ r, Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ))
      (PerBor.moveMat (U.X k').p0 idx b) := by
    intro b hb j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · rw [if_neg (by omega)] at h2
      exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by simp only; omega⟩
    · rw [if_neg (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      omega
    · rw [if_pos (by omega)] at h2
      exact ⟨hbij.1 (by rw [← hcc (relab c σ (e j).1), ← b1, ← h1, b2, hcc]), by simp only; omega⟩
  obtain ⟨T, T', hT, hT', hT0, hTT, hTf, hTf'⟩ := exists_tri_pair (U.X k') idx hinj hs x.1 x.2 hγ hb
  rw [← hxx] at hTf'
  have hPv : ∀ a, P a = perVec (U.X k') idx x.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP a j).trans (hper _ _ _)
  have hPv' : ∀ a, P' a = perVec (U.X k') idx x'.1 (φ k' a : Fin r → E) := fun a => funext fun j =>
    (hP' a j).trans (hper _ _ _)
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g _ F (ik k') (ik k') P' P p' p
    (by rw [← hPx, ← hPx', hB.1])
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k' x).u τ) _ (hv τ) (cf τ i)
      ((U.un k' x').u τ i)).1 (hPx ▸ hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F _ P' p' _ P h.toLinearMap p hex _ _).1 (hv' τ i)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hAe : ∀ j τ i, A j (e.symm ⟨τ, i⟩) =
      ∑ i', (show ℂ from cf τ i i') * (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) j := by
    intro j τ i
    have := congrFun (hcol τ i) j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply] at this
    exact this
  have hA : Supp (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) A := by
    intro j j' hne
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j'
    rw [hAe] at hne
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hi'
    obtain rfl : j = e.symm ⟨τ, i'⟩ := by
      by_contra hj
      exact h2 (Pi.single_eq_of_ne hj _)
    beta_reduce
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨rfl, ?_⟩
    dsimp only
    by_contra hlt
    exact h1 (hcf2 τ i i' (by rw [Fin.lt_def]; omega))
  have key := UnitDet.eq_of_im_hermForm_eq _ p'.2.2.2.1
    ((T * A)ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * (T * A).map (starRingEnd ℂ)))
    (T'ᵀ * (Matrix.diagonal (diagXi (U.X k') idx) * T'.map (starRingEnd ℂ))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← UnitDet.hermForm_mulVec, ← UnitDet.hermForm_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hAv, hAv, ← hh, ← hh, hPv, hPv, hPv', hPv', hTf, hTf', ← hEF, ← hEF, hiso])
  have hdiag : ∀ j, ‖toC (t (some (e j)) : CAt σ)‖ = ‖(PerBor.moveMat (U.X k').p0 idx b j j)⁻¹‖ := by
    intro j
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
    have h1 := norm_diag_eq_norm_diag hinj (hT.mul hA) hT'
      (fun j => by rw [hTT]; exact mul_ne_zero (hT0 j) (inv_ne_zero (moveMat_diag_ne _ idx hb j))) _
      (diagXi_ne _ idx) key (e.symm ⟨τ, i⟩)
    rw [Supp.mul_diag hinj hT hA, hTT, norm_mul, norm_mul, mul_right_inj' (norm_ne_zero_iff.2 (hT0 _)), hAe,
      Finset.sum_eq_single i, Pi.single_eq_same, mul_one, hcf1] at h1
    · rw [Equiv.apply_symm_apply]
      exact h1
    · intro i' _ hi'
      refine mul_eq_zero_of_right _ (Pi.single_eq_of_ne (fun h0 => hi' ?_) _)
      have := e.symm.injective h0
      exact (eq_of_heq (Sigma.mk.inj this).2).symm
    · simp
  have h0 := hdiag (e.symm ⟨τ₀, i₀⟩)
  have h1 := hi (e.symm ⟨τ₀, i₀⟩)
  rw [PerBor.moveMat_diag _ idx hb] at h0
  generalize idx (e.symm ⟨τ₀, i₀⟩) = s at h0 h1
  rw [Equiv.apply_symm_apply] at h0 h1
  obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := s
  dsimp only at h0 h1
  rw [h0]
  unfold bdiag
  rcases h1 with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
  · rw [if_neg (by omega), inv_inv, dif_pos a, dif_pos hn]
  · rw [if_pos (by omega), dif_neg a,
      dif_pos (show conjEmb (relab c σ τ₀) ∈ (U.X k').Ψ from hτ), dif_pos hn]
    rfl

end GlobalTheory.BorelDiag
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.BorelChar



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {l : Level H} {r : ℕ}






variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}


end GlobalTheory.BorelChar
end
end
