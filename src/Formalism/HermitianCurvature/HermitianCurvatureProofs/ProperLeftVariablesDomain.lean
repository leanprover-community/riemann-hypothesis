import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section fubini

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def psiH {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : ℂ := G.psi U.betaU (U.subS (lhOf σ v))

theorem volume_empty_blocks_real (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

def regroup (σ : Equiv.Perm (Fin p)) :
    XL k p ρ σ ≃ᵐ PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ) :=
  MeasurableEquiv.prodAssoc.symm

theorem regroup_apply (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : regroup σ x = ((x.1, x.2.1), x.2.2) := rfl

theorem regroup_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (regroup σ) (muL Bj σ)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  exact (measurePreserving_prodAssoc (Bj.μW.prod Bj.μN) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))).symm

def fH (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ)
    (q : PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) : Wq →L[ℂ] Wp :=
  psiH σ q.2.2 • PBQ.pbI Bj B0 rfl H (U.mMap k p ρ (lhOf σ q.2.2 * U.hMat σ d) g) q.1

theorem ellL_eq (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) = fH Bj B0 σ d H g (regroup σ x) := by
  have hP : PBQ.GoodP Bj (x.1, x.2.1) := hx
  have hs : sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g =
      D.castM rfl (PBQ.sP Bj (x.1, x.2.1)) * U.mMap k p ρ (lhOf σ x.2.2.2 * U.hMat σ d) g := by
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, sxL, if_pos hx, PBQ.sP, if_pos hP]
    have e := embedding_map_lower_unipotent k p ρ (lhOf σ x.2.2.2) (U.hMat σ d) 1 g (lh_unit σ x.2.2.2)
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.mul_one] at e
    rw [e]
    have e2 := embedded_group_measure_preserving k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
      ((lhOf σ x.2.2.2)ᴴ⁻¹)
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← Matrix.mul_assoc (U.muP k p ρ _) (U.embG k p ρ _), ← e2, Matrix.mul_assoc]
  rw [hs, regroup_apply]
  unfold fH ellL PBQ.pbI cL PBQ.cP psiH
  simp only [_root_.smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceInt (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g) := by
  obtain ⟨hint, hJ⟩ := core_lf hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hsf : SigmaFinite (PBQ.muXP (p := p) Bj) := by unfold PBQ.muXP; infer_instance
  have hae : (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) =ᵐ[muL Bj σ]
      fun x => fH Bj B0 σ d H g (regroup σ x) := by
    filter_upwards [ae_goodL Bj σ] with x hx
    exact ellL_eq Bj B0 σ d H g x hx
  have mp := regroup_mp Bj σ
  have hint2 : Integrable (fH Bj B0 σ d H g)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) :=
    (mp.integrable_comp_emb (regroup σ).measurableEmbedding).1 ((hint.congr hae))
  have hJ2 : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, fH Bj B0 σ d H g q ∂((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) ×
        (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))) := by
    rw [hJ, integral_congr_ae hae, mp.integral_comp' (fH Bj B0 σ d H g)]
  have hin : ∀ c : ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ),
      ∫ xP, fH Bj B0 σ d H g (xP, c) ∂(PBQ.muXP Bj) =
        psiH σ c.2 • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ c.2 * U.hMat σ d) g) := by
    intro c
    unfold fH PBQ.pbF
    exact integral_smul (psiH σ c.2) _
  have hR1 := hint2.integral_prod_right
  simp only [hin] at hR1
  have hR2 := hR1.integral_prod_right
  simp only [integral_const, volume_empty_blocks_real, one_smul] at hR2
  refine ⟨hR2, ?_⟩
  rw [hJ2, integral_prod_symm _ hint2]
  simp only [hin]
  rw [integral_fun_snd (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)),
    volume_empty_blocks_real, one_smul]

end fubini

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem slice_integral_jacobian_factor {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ,
          G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g) :=
  SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

def ProperLeftVariablesDomain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (PBQ.domP P.k P.r j p.T.base.z p.T.base.z')

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceIntN (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + ρ) ∧ Dmin k (p + ρ) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    ext x
    show _ ∧ _ ↔ _ ∧ _
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p ρ B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := hset ▸ hHc
  have h := (Formalism.FourierDecayAlt.P.slice_integral_jacobian_factor hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR).2
  have hF : D.castF (rfl : p + ρ = p + ρ) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + ρ) + k + 1) → ℂ, D.castV (rfl : p + ρ = p + ρ).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end gen

section pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slice_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (H : B.Mat k r → E) (a : C.LPt) (hle : D.ptSize a ≤ r)
    (h2 : r - D.ptSize a = r - D.ptSize a) (e : D.ptSize a + (r - D.ptSize a) = r) :
    D.castF h2 (D.sliceAt k r z z' H a) =
      U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm z) (D.castV e.symm z')
        (D.castF e H) (fun a => a.elim0) := by
  funext y
  unfold D.castF
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dif_pos hle]
  rfl

theorem mMap_castM {k j a b : ℕ} (h : a = b) (Z : Matrix (Fin j) (Fin j) ℂ) (g : B.Mat k a) :
    U.mMap k j b Z (D.castM h g) = D.castM (by omega : j + a = j + b) (U.mMap k j a Z g) := by
  subst h
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem pt_eq {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : IsUnit Z.det) (τ : ℂ) (hτ : τ ≠ 0)
    (γ : B.Mat k (r - (j + 1))) (e0 : j + (r - j) = r) (h1 : 1 + (r - (j + 1)) = r - j) :
    D.castM e0 (U.mMap k j (r - j) Z (D.castM h1 (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ))) =
      LevelPointCoordinates.x0 k r j hj Z τ γ := by
  rw [mMap_castM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]
  unfold LevelPointCoordinates.x0 LevelPointCoordinates.zfull
  have hM : D.castM (Formalism.FourierDecayAlt.P.PBH.hs' k j (r - (j + 1)))
      (U.mMap k j (1 + (r - (j + 1))) Z (U.mMap k 1 (r - (j + 1)) (Matrix.of fun _ _ => τ) γ)) =
      U.mMap k (j + 1) (r - (j + 1)) (U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)) γ :=
    Formalism.FourierDecayAlt.P.PBH.M2 (k := k) (ρ := r - (j + 1)) Z hZ τ hτ γ
  rw [← hM, Formalism.FourierDecayAlt.P.PBH.asm_castM_castM]

end pt

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end
