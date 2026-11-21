import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopLocPf

section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT, Formalism.L2.SG.Pf.CarrierBase.herm_bvec]
  have h0 : (Formalism.QuantumDeterminants.Hpk k r *ᵥ Formalism.QuantumDeterminants.bvec j) (Formalism.QuantumDeterminants.eI k r a) = 0 := by
    simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Matrix.col_apply]
    unfold Formalism.QuantumDeterminants.Hpk
    have ha := a.2
    have hv : (Formalism.QuantumDeterminants.eI k r a).val = a.val := rfl
    rw [if_neg (fun h => by have h' := h.2; rw [hv] at h'; omega),
      if_neg (fun h => by have h' := h.1; omega),
      if_neg (fun h => by have h' := h.1; rw [hv] at h'; omega)]
  rw [h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
end
end

section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := C.isT τ
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

theorem n_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have h := (PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card
  omega

theorem trG_mul_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  unfold trG
  calc C.Qi τ * uMat γ * C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ)
      = C.Qi τ * uMat γ * (C.Q τ * C.Qi τ) * uMat γ⁻¹ * C.Q τ := by simp only [Matrix.mul_assoc]
    _ = C.Qi τ * (uMat γ * uMat γ⁻¹) * C.Q τ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul_inv, Matrix.mul_one, h1]

theorem trG_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (trG (C.Q τ) (C.Qi τ) γ)⁻¹ = trG (C.Q τ) (C.Qi τ) γ⁻¹ :=
  Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)

theorem trG_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (a * b) = trG (C.Q τ) (C.Qi τ) a * trG (C.Q τ) (C.Qi τ) b := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc C.Qi τ * (uMat a * uMat b) * C.Q τ = C.Qi τ * uMat a * (C.Q τ * C.Qi τ) * uMat b * C.Q τ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem haarTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarTr C u u' τ := by
  intro γ μRv hH
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hT := trHyp_C C u τ
  have hT' := trHyp_C C u' τ
  set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf
  have hemb : Topology.IsClosedEmbedding f := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hme : MeasurableEmbedding f := hemb.measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := fun y => y.2

  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩
    show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS
    rw [trG_inv, ← trG_mul, ← trG_mul]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ; exact hme.sigmaFinite_map
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
        (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ := by
        rw [trG_inv]
        show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul]
      congr 1
      show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem y_inv_mem (τ : D.what₂.Tau) : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hu := Formalism.L2.SG.Pf.LocJEq.unit_det_y C τ
  show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  conv_lhs => rw [← hy]
  rw [Matrix.conjTranspose_nonsing_inv]
  calc ((C.y τ)ᴴ)⁻¹ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹
      = (((C.y τ)ᴴ)⁻¹ * (C.y τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star),
          Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

set_option maxHeartbeats 1000000 in

theorem quotTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : QuotTr C u u' τ := by
  intro γ μRv ν hH hq
  obtain ⟨hσ, -, -, -⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  set F : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hF
  have hemb : Topology.IsClosedEmbedding F := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hFm : Measurable F := hemb.continuous.measurable
  set cj : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j with hcjdef
  have hcj : Measurable cj := by
    have : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hSm : Measurable (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ) := (Formalism.L2.SG.Pf.LocJEq.smap_cont C τ γ).measurable
  set y' := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (y_inv_mem C τ)) with hy'
  have hty' : trG (C.Q τ) (C.Qi τ) y' = (C.y τ)⁻¹ := by
    show C.Qi τ * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * C.Q τ = _
    simp only [← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

  have key : ∀ σ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      (fun i j => (Matrix.of (cj (F σ)) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) =
        F (γ⁻¹ * (σ * z) * y') := by
    intro σ z
    have hs : Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) = trG (C.Q τ) (C.Qi τ) (γ⁻¹ * z) * (C.y τ)⁻¹ := by
      rw [Formalism.L2.SG.Pf.LocJEq.smap_val]; rfl
    have hgg : trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := trG_mul_inv C τ γ
    have hM : (gB C τ γ)⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) =
        trG (C.Q τ) (C.Qi τ) (γ⁻¹ * (σ * z) * y') := by
      rw [hs, trG_inv, trG_mul, trG_mul, trG_mul, trG_mul, hty']
      calc trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ *
          (trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹)
          = trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ *
            (trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹) * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    funext i j
    exact congrFun (congrFun hM i) j
  intro f hf
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map F) = _
  rw [lintegral_map hf hFm]
  haveI : SigmaFinite μRv := hσ
  have hfm2 : Measurable fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) := by
    refine hf.comp ?_
    have : Continuous fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
      continuous_snd.matrix_mul continuous_fst
    exact this.measurable
  have hinner : Measurable fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂((μRv.map F).map cj) :=
    hfm2.lintegral_prod_right'
  rw [lintegral_map hinner hSm]
  have hin : ∀ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      ∂((μRv.map F).map cj) = ∫⁻ σ, f (F (γ⁻¹ * (σ * z) * y')) ∂μRv := by
    intro z
    have hm3 : Measurable fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) :=
      hfm2.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hm3 hcj]
    rw [lintegral_map (f := fun a => f fun i j => (Matrix.of (cj a) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      (hm3.comp hcj) hFm]
    refine lintegral_congr fun σ => ?_
    rw [key]
  simp only [hin]
  have hg : Measurable fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (F (γ⁻¹ * w * y')) :=
    hf.comp (hFm.comp ((continuous_mul_right y').measurable.comp (continuous_mul_left γ⁻¹).measurable))
  rw [← hq _ hg]
  symm
  calc ∫⁻ x, f (F (γ⁻¹ * x * y')) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (fun w => f (F (γ⁻¹ * w))) (x * y') ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
        simp only [mul_assoc]
    _ = ∫⁻ x, f (F (γ⁻¹ * x)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_right_eq_self (fun w => f (F (γ⁻¹ * w))) y'
    _ = ∫⁻ x, f (F x) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_left_eq_self (fun w => f (F w)) γ⁻¹

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal Pointwise

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

section Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {v : InfinitePlace X.B.I.F} {lam : ℂ}
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}

theorem trHyp_gen (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u v) Q Qi (fun a : Fin D.R.rS => lam ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := hT
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

theorem trG_mul_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    trG Q Qi (a * b) = trG Q Qi a * trG Q Qi b := by
  obtain ⟨-, h2, -, -⟩ := hT
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc Qi * (uMat a * uMat b) * Q = Qi * uMat a * (Q * Qi) * uMat b * Q := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trG_inv_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (γ : Formalism.REAL.UJ (X.B.I.ε v)) :
    (trG Q Qi γ)⁻¹ = trG Q Qi γ⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← trG_mul_g hT, mul_inv_cancel]
  obtain ⟨h1, -, -, -⟩ := hT
  show Qi * uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) * Q = 1
  simp [uMat, h1]

theorem transp_mem_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Q * m * Qi ∈ UJset (X.B.I.ε v) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := hT
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) = Formalism.REAL.Jm (X.B.I.ε v)
  have e1 : (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) =
      Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hH, hm', ← hH]
  have e2 : Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

variable (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u u' : D.what₂.Word) (γ : Formalism.REAL.UJ (X.B.I.ε v))
  (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)))
include hT

theorem emb_g : Topology.IsClosedEmbedding
    (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ hT.2.1

theorem haar_measure_transport_invariant (hH : IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v)
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ) μRv) :
    (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) (Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ))ᶜ = 0 ∧
    (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ),
      (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))).map (Formalism.QuantumDeterminants.lmulM a) = μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) ∧
    μRv.map (fun x => Matrix.of.symm (trG Q Qi x)) ≠ 0 := by
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  have h1 := hT.1
  have h2 := hT.2.1
  have hTu := trHyp_gen hT u
  have hTu' := trHyp_gen hT u'
  set F : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun x => Matrix.of.symm (trG Q Qi x) with hF
  have hme : MeasurableEmbedding F := (emb_g hT).measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ,
      trG Q Qi y ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hTu (hU y) hy1, ?_⟩
    rw [trG_inv_g hT, ← trG_mul_g hT, ← trG_mul_g hT]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hTu' (hU _) hy2
  refine ⟨?_, ?_, ?_⟩
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := transp_mem_g hT hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (Q * s * Qi) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hTu hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = Q * ((trG Q Qi γ)⁻¹ * s * trG Q Qi γ) * Qi := by
        rw [trG_inv_g hT]
        show uMat (γ⁻¹ * y0 * γ) = Q * (Qi * uMat γ⁻¹ * Q * s * (Qi * uMat γ * Q)) * Qi
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (Q * s * Qi) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hTu' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ F = F ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hF, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul_g hT]
      congr 1
      show s = Qi * (Q * s * Qi) * Q
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h

theorem fin_g (ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (hq : IsQuotLoc μRv ν) (K : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
    (hK : IsCompact K) : (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) K < ∞ := by
  have hemb := emb_g hT
  rw [hemb.measurableEmbedding.map_apply]
  set Cc := (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ⁻¹' K
  have hC : IsCompact Cc := hemb.isCompact_preimage hK

  have hν : ν ≠ 0 := by
    intro h0
    have h := hq (fun _ => 1) measurable_const
    rw [h0] at h
    simp only [lintegral_const, Measure.coe_zero, Pi.zero_apply, mul_zero, lintegral_zero_measure] at h
    have : Formalism.REAL.muG (X.B.I.ε v) Set.univ = 0 := by simpa using h
    exact (isOpen_univ.measure_pos (Formalism.REAL.muG (X.B.I.ε v)) Set.univ_nonempty).ne' this

  obtain ⟨m, hm⟩ : ∃ m, 0 < ν (compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m) := by
    by_contra hcon
    push_neg at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
  set V := compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m
  have hV : IsCompact V := isCompact_compactCovering _ m
  have hCV : IsCompact (Cc * V) := hC.mul hV
  have hfin : Formalism.REAL.muG (X.B.I.ε v) (Cc * V) < ∞ := hCV.measure_lt_top
  have hmeas : MeasurableSet (Cc * V) := hCV.isClosed.measurableSet
  have hW := hq ((Cc * V).indicator 1) (measurable_one.indicator hmeas)
  rw [lintegral_indicator_one hmeas] at hW
  have hlow : μRv Cc * ν V ≤ ∫⁻ x, (∫⁻ s, (Cc * V).indicator 1 (s * x) ∂μRv) ∂ν := by
    rw [← lintegral_indicator_const (hV.isClosed.measurableSet)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx, ← lintegral_indicator_one hC.isClosed.measurableSet]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ Cc
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (Set.mul_mem_mul hs hx)]; exact le_rfl
      · rw [Set.indicator_of_notMem hs]; exact bot_le
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  rw [← hW] at hlow
  by_contra hinf
  rw [not_lt, top_le_iff] at hinf
  rw [hinf, ENNReal.top_mul hm.ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hfin) (lt_irrefl _)

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem haarAtC_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarAtC C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨-, -, -, hH, hq⟩ := hP
  have hT := Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)
  obtain ⟨hc, hl, hne⟩ := haar_measure_transport_invariant hT u u' γ μRv hH
  exact ⟨hc, hl, fun K hK => fin_g hT μRv ν hq K hK, hne⟩

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.LocWSOf Formalism.BasicNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem cutAt_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (A₀ : ℝ)
    (hA : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1 (fcAt C u u' τ a b ξ ξ' c)) : CutAt C u u' τ a b ξ ξ' c :=
  cutAt_of_haar C u u' τ a b ξ ξ' c (haarAtC_holds C u u' τ) A₀ hA hCC

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

def ccOne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) : ℂ :=
  lamPl (cOf hB u τ) (sclOf hB u u' τ)
    (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
    (muN_eq_haarLie D.R.k D.R.rS).choose

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem ccOne_ne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) :
    ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  exact lamPl_ne _ _ _ D θ _ hcO hscl
    (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec.1 h0 h1
    (Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem pinAt_one (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hTT : HypTT D u u') (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ)) (ξ' : X.Vloc u' (vOf X τ))
    (hpin1 : CoefPin hB u u' τ a b ξ ξ' 1) (hscl : sclOf hB u u' τ ≠ 0) (hcO : cOf hB u τ ≠ 0) (A₀ : ℝ)
    (hA₀ : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A₀)
    (hCC : Formalism.FourierDecayAlt.B.InCC A₀ 1
      (fcAt C u u' τ a b ξ ξ' (ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)))
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hP : PinHypAt C u u' τ γ μRv ν) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
        (fcAt C u u' τ a b ξ ξ' (ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl)) := by
  set cc := ccOne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl with hcc
  have hc0 : cc ≠ 0 := ccOne_ne C hB hJ large₂ hCl hH0 u u' τ hTT hW hA hT hT' a b ξ ξ' hpin1 hscl hcO
  have hκ := (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose_spec
  obtain ⟨h0, h1, hN⟩ := (muN_eq_haarLie D.R.k D.R.rS).choose_spec
  have hCut := cutAt_holds C u u' τ a b ξ ξ' cc A₀ hA₀ hCC
  obtain ⟨hGv, hMono, hRel, hH, hQ⟩ := id hP
  have hLz := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz
  have hLz' := (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT').hz'
  have hWc := muWc_eq C u τ hLz.1 hLz.2
  have hWc' := muWc_eq C u' τ hLz'.1 hLz'.2
  have hH' := haarTr_holds C u u' τ γ μRv hH
  obtain ⟨νB, hq⟩ := orbQuot_exists (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
    (gB_mem C u τ γ) hH'
  have hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData
      (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB :=
    ⟨gB_mem C u τ γ, gf_B C u u' τ γ hGv, mono_B C u u' τ γ hMono,
      relStab_of_relevant C hB u u' τ hW hA hT hT' γ hRel, hH', hq, quotTr_holds C u u' τ γ μRv ν hH hQ⟩
  have hpinAt := pinAt C hB u u' τ hW hA hT hT' a b ξ ξ' cc hc0 _ hκ.1 hκ.2 _ h0 h1 hN hWc hWc' hcO hscl γ μRv ν νB
    hcell (Formalism.L2.SG.Pf.LocJEq.integrand_aesm C hB u u' τ γ ν) (hCut γ μRv ν hP)
  rw [hpinAt]
  have e : lamPl (cOf hB u τ) (sclOf hB u u' τ)
      (ampVec_carrier hJ large₂ hCl hH0 hB u u' τ hTT hW hA hT hT' a b ξ ξ' 1 hpin1 hscl).choose D θ
      (muN_eq_haarLie D.R.k D.R.rS).choose * cc⁻¹ = 1 := by
    rw [hcc]; exact mul_inv_cancel₀ hc0
  rw [e, one_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinCov_carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (Hj : ∀ j : Fin (nfE D),
      ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j)))),
        Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
          (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
          (tauE X e j) γ μRv ν →
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
          Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
          Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
            (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
            (Formalism.L2.SG.Pf.Carrier.CarPinTor.fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (cc j))) :
    Formalism.L2.SG.Pf.Carrier.JointPin.PinCov
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo) := by
  intro v γ μRv ν hH
  obtain ⟨j, rfl⟩ := (tauE X e).surjective v
  have key : ∀ (j' : Fin (nfE D)) (h' : X.pl.symm (e (plE D j')) = tauE X e j),
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
        Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
        ((castLoc X u h').toContinuousLinearEquiv.toContinuousLinearMap :
            X.Vloc u (tauE X e j') →L[ℂ] X.Vloc u (tauE X e j)).comp
          ((Formalism.FourierDecayAlt.D.orbJ (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
              (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
              (fcT X C e u u' a b ξ ξ' cc j')).comp
            ((castLoc X u' h').symm.toContinuousLinearEquiv.toContinuousLinearMap :
              X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u' (tauE X e j'))) := by
    intro j' h'
    have hj : j' = j := (tauE X e).injective h'
    subst hj
    rw [towersOf_base, Hj j' γ μRv ν hH]
    ext x
    rfl
  exact key _ (tauE_symm X e (tauE X e j))

end Formalism.L2.SG.Pf.CarrierT
end
end

section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.Pf.BaseOf in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem pinCov_ccOne (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : NumberField.InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j)
      (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀)))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hCC : ∀ j, Formalism.FourierDecayAlt.B.InCC Ac 1 (fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j)
      (ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)))) :
    JointPin.PinCov (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ'
      (fun j => ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j)
        (hpin1 j) (hscl j)) c ν' m₀ Θ TP A₀) Mo) := by
  refine pinCov_carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo ?_
  intro j γ μRv ν hH
  have hP := pinHyp_at X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' _ c ν' m₀ Θ TP A₀ Mo j γ μRv ν hH
  exact pinAt_one C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j)
    (hscl j) (hcO j) Ac hAc (hCC j) γ μRv ν hP

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

theorem xLeafAt_of_pins {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)
    (hJ : PI.BesselMapUniq.BesselMapUniq) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (sc : ℝ) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn : ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j))
    (hTT : HypTT D u u')
    (hW : ∀ j, GoodW D (e (plE D j)) u u' θ (locW C u u' (e (plE D j))))
    (hA : ∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j))))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (hpin1 : ∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1)
    (hscl : ∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) (hcO : ∀ j, cOf hB u (e (plE D j)) ≠ 0)
    (h : Fin (nfE D) → ℝ) (hlam : ∀ j, Formalism.QuantumDeterminants.IsHCParam (lamD D (e (plE D j))))
    (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (h j))
    (hok : ∀ j, Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (h j))
    (Ac : ℝ) (hAc : Formalism.FourierDecayAlt.P.orbital_integral_converges.choose * ((D.R.rS : ℝ) + 1) ^ 2 *
      ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ Ac)
    (hAc0 : 0 ≤ Ac) (hAch : ∀ j, Ac ≤ h j / 2)
    (cc : Fin (nfE D) → ℂ)
    (hcc : cc = fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
      hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) :
    XLeafAt X C u u' e he hv CA de de' l i0 i0' sc FdN FdN' νq jn a b ξ ξ' cc := by
  subst hcc
  refine ⟨fun j => (hpin1 j).1, fun j => (hpin1 j).2.1, fun Θ TP A₀ => ?_⟩
  exact Formalism.L2.SG.Pf.Carrier.CarPinTor.pinCov_ccOne C hB hJ large₂ hCl hH0 u u' e he hv CA de de' l (gridT e l) (grid1T e l)
    a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO cutStd (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀ (modelsOf _) Ac hAc
    (fun j => Formalism.L2.SG.Pf.CoefCCT.fcT_inCC C e u u' a b ξ ξ'
      (fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne C hB hJ large₂ hCl hH0 u u' (e (plE D j)) hTT (hW j) (hA j)
        hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j)) h hlam hgap hok hAc0 hAch (fun j => (hpin1 j).1) (fun j => (hpin1 j).2.1) j 1)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ac_le (c Cl L : ℝ) (r k f : ℕ) (hCl : 1000 + |c| ≤ Cl) (hf : 2 ≤ f) (hL : 1 / 2 ≤ L) :
    max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) 0 ≤
      Cl * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn]
  have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hrn : (r : ℝ) + 1 ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hCl0 : 0 ≤ Cl := by linarith [abs_nonneg c]
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (f : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf' 5
    norm_num at this
    linarith
  have hP0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) := by positivity
  have hn19 : 0 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := by positivity
  have hP : ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by
    have h1 : ((r : ℝ) + 1) ^ 2 ≤ (2 * (r : ℝ) + k + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hrn 2
    have h2 : (r : ℝ) * (2 * (r : ℝ) + k + 1) + 1 ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 2 := by
      linarith [mul_nonneg hr0 hk0, mul_nonneg hr0 hr0, mul_nonneg hk0 hk0]
    have h3 : (2 * (r : ℝ) + k + 1) ^ 4 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)
        ≤ (2 * (r : ℝ) + k + 1) ^ 2 * (2 * (2 * (r : ℝ) + k + 1) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (2 * (r : ℝ) + k + 1) ^ 4 := by ring
      _ ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by linarith
  have hA : 0 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 := mul_nonneg hCl0 hn19
  have hRHS : 8 * (Cl * (2 * (r : ℝ) + k + 1) ^ 19) ≤
      Cl * (2 * (r : ℝ) + k + 1) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
    have hfl : (32 : ℝ) * (1 / 2) ≤ (f : ℝ) ^ 5 * L := mul_le_mul hf5 hL (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hA
    linarith
  apply max_le
  · have hcP : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) ≤
        |c| * (2 * (2 * (r : ℝ) + k + 1) ^ 19) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c) hP0).trans
        (mul_le_mul_of_nonneg_left hP (abs_nonneg c))
    have hcl : |c| * (2 * (r : ℝ) + k + 1) ^ 19 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 :=
      mul_le_mul_of_nonneg_right (by linarith) hn19
    have e : c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) =
        c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) := by ring
    rw [e]
    linarith
  · linarith

def XPins : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl → 1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → PlaceTie T.X e →
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (hB : WuBessel Ch) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)),
      HypTT D u u' ∧ 0 < Tr D u ∧ 0 < Tr D u' ∧
      (∀ j, GoodW D (e (plE D j)) u u' θ (locW Ch u u' (e (plE D j)))) ∧
      (∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j)))) ∧
      (∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1) ∧
      (∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) ∧ (∀ j, cOf hB u (e (plE D j)) ≠ 0)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocalDoubleCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Move {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (γ γ' : Formalism.MainNotions.S.MatKR k r) : Prop :=
  ∃ n ∈ Formalism.QuantumDeterminants.Nset k r, ∃ s ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ s' ∈ Formalism.QuantumDeterminants.UWset k r z', ∃ n' ∈ Formalism.QuantumDeterminants.Nset k r,
    γ' = (s * n) * γ * (n' * s')

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

def JMove : Prop :=
  ∀ (τ : D.what₂.Tau) (γ γ' : Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (ν ν' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Move (locW C u u' τ).z (locW C u u' τ).z' γ γ' → (∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z' γ p) →
    RMeas D (locW C u u' τ) γ 1 ν → RMeas D (locW C u u' τ) γ' 1 ν' →
    hsNormSq ((locS hB u u' τ).J ν' γ') = hsNormSq ((locS hB u u' τ).J ν γ)

def DecR : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    Move (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) (Formalism.L2.SG.LoopTerm.gamR hI C t τ) ∧
    ∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) p

def RMeasExT : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    ∃ ν, RMeas D (locW C u u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) 1 ν

end Formalism.L2.SG.Pf.LocalDoubleCoset
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.AmpWinRX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (u u' : D.what₂.Word)

theorem goodW_all (τ : D.what₂.Tau) : GoodW D τ u u' θ (locW C u u' τ) :=
  goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ) (Formalism.L2.SG.Pf.zTr C u τ)
    (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)

end Formalism.L2.SG.Pf.AmpWinRX
end
end

section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix InnerProductSpace

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def XLeavesP : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
    u ≠ u' → 0 < cb → 0 < cTf → Formalism.BasicNotions.Ties D → 29 ≤ C' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl →
    1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → ∀ hPl : PlaceTie T.X e,
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j))
      (cc : Fin (nfE D) → ℂ),
      XLeafAt T.X Ch u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1
        (T.Y.FN u) (T.Y.FN u') νq (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN a b ξ ξ' cc

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] in

theorem carrierXSideP_of_leaves (Cb : ℝ) (hLift : LiftAt3 Cb) (hX : XLeavesP) : CarrierSideBoundPositive Cb := by
  intro C₆ Cc hC6
  refine ⟨max (max (max Cc Cd) Ce) 1, ?_⟩
  intro CA hCA h1CA C0 CG CDel cT Cb' a2 a3 a4 a5 a6 a7
  set Cq : ℝ := 8400 * (|Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst|) + 48120 with hCq
  obtain ⟨k1, hk1⟩ := lenI_big CDel Cb' Cq a4 a6
  refine ⟨max k1 1801, fun Cg cb Cw cTf CT C0f hcb hcT => ⟨29, max (max 1000 (25000 + 21 * (|Cc| + |Cd| + |Ce|))) (1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose|), ?_⟩⟩
  intro C' Cl hC' hCl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hTies hne hk hH0 hPl hSz hi hPt hNu
  have hClp : 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl := le_trans (le_max_right _ _) hCl
  have hk18' : 1801 ≤ D.R.k := by
    have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk
    exact this
  obtain ⟨θ, Ch, a, b, ξ, ξ', cc, hleaf⟩ :=
    hX CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th vR Q hne hcb hcT hTies hC' hClp hk18' hH0 hPl hSz
      hi hPt hNu
  have h5 := Formalism.MainNotions.BridgeLemma.last_shifted_parameter_eq hH0.2.1
  obtain ⟨hG, hw, hw', hl1, hl2, hne', -⟩ := hSz
  have hOk : ∀ w, ((gOf D e).place w).Ok := hG.hplace

  have hcard : 0 < Fintype.card (InfinitePlace D.host.E) := by
    have h1 : (gOf D e).m ≤ (gOf D e).f := hG.hmf
    have h2 : (gOf D e).f = Fintype.card (InfinitePlace D.host.E) := rfl
    have h3 : (gOf D e).m = 2 * (gOf D e).r + 2 := rfl
    omega
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hcard
  have hDel1 : (1 : ℝ) ≤ (D.s.Del : ℝ) := (hOk w).hDel
  have hDel0 : (D.s.Del : ℝ) ≠ 0 := by linarith
  have hde := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u
  have hde' := Formalism.L2.SG.Pf.SzHypOf.deOf_eq D h5 hDel0 τ u'

  have hkk : k1 ≤ (gOf D e).k := le_trans (le_max_left _ _) hk
  have hlenI := hk1 (gOf D e) L.sc.b hkk hG
  have hlenI' : Cq * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := hlenI
  obtain ⟨p1, p2, p3⟩ := polys D.R.k D.R.rS
  have hQ0 : 0 ≤ (D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4 := by positivity
  have hCqc : ∀ c : ℝ, |c| ≤ |Cc| + |Cd| + |C₆| + |Ce| + |fourierDecayLevelZeroConst| →
      8400 * |c| * ((D.R.k : ℝ) * ((D.R.rS : ℝ) + 1) ^ 3 + ((D.R.rS : ℝ) + 1) ^ 4) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
    intro c hc
    refine le_trans ?_ hlenI'
    apply mul_le_mul_of_nonneg_right _ hQ0
    rw [hCq]; linarith
  have ac := abs_nonneg Cc
  have ad := abs_nonneg Cd
  have a6' := abs_nonneg C₆
  have ae := abs_nonneg Ce
  have a6e := abs_nonneg fourierDecayLevelZeroConst
  have hLc := scale_le (by positivity) p1 (hCqc Cc (by linarith))
  have hLd := scale_le (by positivity) p1 (hCqc Cd (by linarith))
  have hC6' := scale_le (by positivity) p2 (hCqc C₆ (by linarith))
  have hLe := scale_le (by positivity) p1 (hCqc Ce (by linarith))
  have hC6e := scale_le (by positivity) p2 (hCqc fourierDecayLevelZeroConst (by linarith))
  have hlen : 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ^ 3 + 6 * ((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
    refine le_trans p3 (le_trans ?_ hlenI')
    apply mul_le_mul_of_nonneg_right _ hQ0
    rw [hCq]; linarith

  have hCA' : Cc ≤ CA := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCA
  have hCAd : Cd ≤ CA := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hCA
  have hCAe : Ce ≤ CA := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCA

  have hS0 := hH0.1
  have hCl1000 : (1000 : ℝ) ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) :=
    fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 (e (plE D j))
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hc
    push Not at hc
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    exact_mod_cast this
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
    norm_num at this; linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by
    have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk
    have e1 : (gOf D e).k = D.R.k := rfl
    omega
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1)
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity

  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by have := Formalism.MainNotions.BridgeLemma.five_le_k D; omega) hn1801) ?_
    have : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
    rw [this]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAh : decayThreshold (|Cc| + |Cd| + |Ce|) D.R.k D.R.rS ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / 2 := by
    unfold decayThreshold
    have habs : |(|Cc| + |Cd| + |Ce|)| = |Cc| + |Cd| + |Ce| := abs_of_nonneg (by positivity)
    rw [habs]
    have hn' : (2 * (D.R.rS : ℝ) + D.R.k + 1) = (D.R.r : ℝ) := by rw [hr]; push_cast; ring
    rw [hn']
    have hCl2 : 25000 + 21 * (|Cc| + |Cd| + |Ce|) ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
    have h7 : (D.R.r : ℝ) ^ 7 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    have hn7 : 0 ≤ (D.R.r : ℝ) ^ 7 := by positivity
    have hn19' : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
    have e1 : (25000 + 21 * (|Cc| + |Cd| + |Ce|)) * (D.R.r : ℝ) ^ 7 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
      mul_le_mul hCl2 h7 hn7 (by linarith)
    have hc0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith) hn19'
    linarith
  exact carrierDataBuilt_of_hyp T.X Ch Cb hLift capacity_from_hermitian_char hH0.1 hCl1000
    (by have : 1801 ≤ (gOf D e).k := le_trans (le_max_right _ _) hk; exact this) Cc C₆ u u' e hPl CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' cc hleaf h5 hde hde' hOk hw hw'
    hl1 hl2 hne' hlen hLc hLd hC6' hCA' hCAd hLe hC6e hCAe _ hgap hok hAh hi hPt one_pos hNu
    (fun Θ TP A₀ hBuilt => energy_compact_test_bound T Ch u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
      (lOf D (deOf D τ u) (deOf D τ u')) a b ξ ξ' cc i0' Θ TP A₀ X0 sd C Th vR Q i0 i0' νq (hleaf.2.2 Θ TP A₀) hBuilt)

def XPinsP : Prop :=
  ∀ (CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl : ℝ)
    (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (τ : D.what₂.Tau) (Cp Th' : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → 0 < cb → 0 < cTf → Formalism.BasicNotions.Ties D → 29 ≤ C' → 1000 + |Formalism.FourierDecayAlt.P.orbital_integral_converges.choose| ≤ Cl → 1801 ≤ D.R.k →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → PlaceTie T.X e →
    J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
      (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
    (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
    ∃ (θ : ℝ) (Ch : Choice T.X θ) (hB : WuBessel Ch) (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j))
      (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j)) (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)),
      HypTT D u u' ∧ 0 < Tr D u ∧ 0 < Tr D u' ∧
      (∀ j, GoodW D (e (plE D j)) u u' θ (locW Ch u u' (e (plE D j)))) ∧
      (∀ j, GoodS D (lamD D (e (plE D j))) (locS hB u u' (e (plE D j)))) ∧
      (∀ j, CoefPin hB u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) 1) ∧
      (∀ j, sclOf hB u u' (e (plE D j)) ≠ 0) ∧ (∀ j, cOf hB u (e (plE D j)) ≠ 0)

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
theorem xLeavesP_of_pinsP (hJ : PI.BesselMapUniq.BesselMapUniq) (hP : XPinsP) : XLeavesP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq X0 sd C Th F0 what₂ vR Q hne hcb hcT hTies hC' hClp
    hk18 hH0 hPl hSz hi hPt hNu
  obtain ⟨θ, Ch, hB, a, b, ξ, ξ', hTT, hT, hT', hW, hA, hpin1, hscl, hcO⟩ :=
    hP CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18 hH0 hPl hSz
      hi hPt hNu
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hS0 := hH0.1

  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Formalism.MainNotions.BridgeLemma.five_le_k D
  have hL : (1 / 2 : ℝ) ≤ L.sc.L := by
    by_contra hcn
    push Not at hcn
    have h1 : Real.exp (2 * L.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hfR : (2 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hfR 5
    norm_num at this; linarith
  have hrr : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hr]
  have hn1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by rw [hr]; push_cast; have : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _; linarith
  have hn19 : 0 ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hh16 : 16 * Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    have e1 : Cl * (D.R.r : ℝ) ^ 19 * 32 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    linarith
  have hn1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by omega
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) := by
    refine gapOK_mono (Formalism.L2.SG.Pf.WuDec.gapOK_of_big D.R.k D.R.rS (by omega) hn1801) ?_
    rw [hrr]
    have h1 : 1 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_right (by linarith) hn19
    linarith
  have hAch := le_of_le_of_eq (ac_le (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose) Cl L.sc.L D.R.rS D.R.k D.R.f hClp hf hL) (by rw [hrr])
  refine ⟨θ, Ch, a, b, ξ, ξ', fun j => Formalism.L2.SG.Pf.Carrier.CarPinTor.ccOne Ch hB hJ L hCl hH0 u u' (e (plE D j)) hTT (hW j)
    (hA j) hT hT' (a j) (b j) (ξ j) (ξ' j) (hpin1 j) (hscl j), ?_⟩
  exact xLeafAt_of_pins T.X Ch hB hJ L hCl hH0 u u' e hPl (host_v D) CA (deOf D τ u) (deOf D τ u')
    (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' 1 (T.Y.FN u) (T.Y.FN u') νq _ a b ξ ξ' hTT hW hA hT hT' hpin1 hscl hcO
    (fun _ => Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) (fun j => Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D _)
    (fun j => Formalism.MainNotions.BridgeLemma.szh_gap hS0 _) (fun _ => hok) _ (le_max_left _ _) (le_max_right _ _) (fun _ => hAch) _ rfl

def KFinNZ : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau),
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    ∃ a : X.B.H (vOf X τ), PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) a ∧ bOf hB u τ a ≠ 0

theorem inner_normalize_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {x : V} (hx : x ≠ 0) :
    ⟪x, (((‖x‖ ^ 2 : ℝ) : ℂ))⁻¹ • x⟫_ℂ = 1 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  have h : (‖x‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  push_cast
  exact inv_mul_cancel₀ h

theorem inner_normalize_left {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {y : V} (hy : y ≠ 0) :
    ⟪(((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ • y, y⟫_ℂ = 1 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  have h : (‖y‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hc : (starRingEnd ℂ) (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ = (((‖y‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rw [hc]
  push_cast
  exact inv_mul_cancel₀ h

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in

theorem xPinsP_of (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) : XPinsP := by
  intro CA C0 CG CDel cT Cb' Cg cb Cw cTf CT C0f C' Cl D L T u u' e τ Cp Th' i0 i0' νq hne hcb hcT hTies hC' hClp hk18
    hH0 hPl hSz hi hPt hNu
  haveI : Nonempty D.what₂.Word := ⟨u⟩
  have hCl : (1000 : ℝ) ≤ Cl := by have := abs_nonneg (Formalism.FourierDecayAlt.P.orbital_integral_converges.choose); linarith
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH0.1 (by linarith) hC'
  obtain ⟨Ch⟩ := Formalism.L2.SG.Pf.choiceExists T.X 1 one_pos
  have hB : WuBessel Ch := Formalism.L2.SG.Pf.LoopLoc.wuBessel_of hG hJ Ch
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG Ch
  have hc : ∀ (w : D.what₂.Word) (t : D.what₂.Tau), 0 < cOf hB w t := fun w t =>
    Formalism.L2.SG.Pf.AmpWin.cOf_pos hB (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).1 (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB w t).2
  have hscl : ∀ t, sclOf hB u u' t ≠ 0 := by
    intro t
    have h1 := Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty Ch hLF hB u' t
    have hl : 0 < (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := ENNReal.toReal_pos h1.1 h1.2.ne
    have hd : 0 < Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t))) with h | h
      · exfalso
        have : Subsingleton (T.X.Vloc u' (vOf T.X t)) := Module.finrank_zero_iff.1 h
        apply h1.1
        unfold l2SG
        simp [Subsingleton.elim (phiOf hB u' t _) 0]
      · exact h
    unfold sclOf
    have hpos : 0 < cOf hB u t * (Module.finrank ℂ (T.X.Vloc u' (vOf T.X t)) : ℝ) /
        (l2SG (Ch.nuS u' t) (phiOf hB u' t)).toReal := div_pos (mul_pos (hc u t) (by exact_mod_cast hd)) hl
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have ha : ∀ j : Fin (nfE D), ∃ a : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) a ∧
      bOf hB u (e (plE D j)) a ≠ 0 := fun j => hNZ D T.X 1 Ch hB u (e (plE D j)) hG
  have hb : ∀ j : Fin (nfE D), ∃ b : T.X.B.H (vOf T.X (e (plE D j))),
      PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) (sigB T.X (Ch.Q (e (plE D j))) (Ch.Qi (e (plE D j))) (e (plE D j))) b ∧
      bOf hB u' (e (plE D j)) b ≠ 0 := fun j => hNZ D T.X 1 Ch hB u' (e (plE D j)) hG
  choose a ha using ha
  choose b hb using hb
  refine ⟨1, Ch, hB, a, b, fun j => (((‖bOf hB u (e (plE D j)) (a j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u (e (plE D j)) (a j),
    fun j => (((‖bOf hB u' (e (plE D j)) (b j)‖ ^ 2 : ℝ) : ℂ))⁻¹ • bOf hB u' (e (plE D j)) (b j),
    Formalism.MainNotions.SchurRelationsDiscreteSeries.hypTT_all u u', Nat.cast_pos.2 (D.mem u).A.T_prime.pos, Nat.cast_pos.2 (D.mem u').A.T_prime.pos,
    fun j => Formalism.L2.SG.Pf.AmpWinRX.goodW_all Ch u u' (e (plE D j)),
    fun j => goodS_of hB u u' (e (plE D j)) (Formalism.L2.SG.Pf.goodSRest_all hG hTies.dsig_tie hB u u' (e (plE D j))),
    fun j => ⟨(ha j).1, (hb j).1, ?_, one_ne_zero⟩, fun j => hscl _, fun j => (hc u _).ne'⟩
  rw [inner_normalize_right (ha j).2, inner_normalize_left (hb j).2, one_mul]

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem carrierP_of_kFinite (hT : CSTarget) (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := hT
  obtain ⟨Cb, hL⟩ := liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_repaired_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem carrierP_of_kfin4 (hT : CSTarget4) (hJ : PI.BesselMapUniq.BesselMapUniq) (hNZ : KFinNZ) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP := by
  obtain ⟨hPA, hMP, hBB⟩ := hT
  obtain ⟨Cb, hL⟩ := liftAt3_exists
  exact Formalism.L2.SG.SpectralTiesReal.carrierP_of_compact_model hPA Formalism.FourierDecayAlt.P.lemma_model hMP hBB Cb
    (carrierXSideP_of_leaves Cb hL (xLeavesP_of_pinsP hJ (xPinsP_of hJ hNZ)))

def KFinDense : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ δ : ℝ, 0 < δ → ∃ a : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a ∧
      (Ws.map fun w => ‖dsigW σ w (v - a)‖).sum < δ

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem kFinNZ_of (hD : KFinDense) : KFinNZ := by
  intro D X θ C hB u τ hG
  have hLF := Formalism.L2.SG.Pf.LocF.locFactor_holds hG C
  have hl := (Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ).1
  obtain ⟨-, -, hSH, -, -, -, -, -⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) hSH (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hex : ∃ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), phiOf hB u τ m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hl
    unfold l2SG
    have h0 : (fun x => (‖phiOf hB u τ (Matrix.of x)‖₊ : ENNReal) ^ 2) =ᵐ[C.nuS u τ] 0 := by
      filter_upwards [hae] with x hx
      simp [hcon _ hx]
    rw [lintegral_congr_ae h0]
    simp
  obtain ⟨m, hm, hΦ⟩ := hex
  have hds := Formalism.L2.SG.Pf.dsTr C τ
  have hlam := Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ
  have hv0 : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds (Formalism.L2.SG.Pf.isLowUnitH_base_vector C τ)
  have hv : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hds) hv0 hm
  have hBs := (hB u τ).choose_spec.1
  obtain ⟨hadd, -, -, Cw, Ws, hWs, hbd⟩ := hBs
  have hBv : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) ≠ 0 := hΦ
  have hnB : 0 < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ := norm_pos_iff.mpr hBv
  set δ : ℝ := ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ / (|Cw| + 1) with hδ
  have hδ0 : 0 < δ := div_pos hnB (by positivity)
  obtain ⟨a, ha, hS⟩ := hD D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ (sigB X (C.Q τ) (C.Qi τ) τ) hlam hds _ hv Ws hWs δ hδ0
  refine ⟨a, ha, fun hBa => ?_⟩
  have has : a ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.L2.SG.Pf.k_finite_smooth D.R.k D.R.rS (epsSH D.R) (lamD D τ) _ _ hds a ha
  have hva : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) :=
    Formalism.MainNotions.LowestKTypeMultiplicity.smooth_sub hv has
  have hsplit : bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a) + bOf hB u τ a := by
    have := hadd _ hva a has
    rw [sub_add_cancel] at this
    exact this
  rw [hBa, add_zero] at hsplit
  have hb : ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖ ≤
      Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum := hbd _ hva
  rw [← hsplit] at hb
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
  have h1 : Cw * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum ≤
      |Cw| * δ := by
    calc _ ≤ |Cw| * (Ws.map fun w => ‖dsigW (sigB X (C.Q τ) (C.Qi τ) τ) w
            (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) - a)‖).sum := mul_le_mul_of_nonneg_right (le_abs_self Cw) hS0
      _ ≤ |Cw| * δ := mul_le_mul_of_nonneg_left hS.le (abs_nonneg Cw)
  have h2 : |Cw| * δ < ‖bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ))‖ := by
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg Cw]
  linarith

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem carrierP_of_dense (hT : CSTarget) (hJ : PI.BesselMapUniq.BesselMapUniq) (hD : KFinDense) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP :=
  carrierP_of_kFinite hT hJ (kFinNZ_of hD)

variable [Fact Formalism.L2.SG.Pf.CarrierT.CoefCapAll] [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem carrierP_of_dense4 (hT : CSTarget4) (hJ : PI.BesselMapUniq.BesselMapUniq) (hD : KFinDense) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.CarrierP :=
  carrierP_of_kfin4 hT hJ (kFinNZ_of hD)

end Formalism.L2.SG.Pf.CarrierXAll
end
end
