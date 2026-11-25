module
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalToGlobal.Divisibility.RecBridgeWire
import Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section
noncomputable section
namespace Formalism.SlopeId

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

theorem muZero_free {eps : ℝ} (Fm : FamP eps) : J.MuZero Fm := Formalism.L2.DIV.Wire.za_of Fm

theorem muTu_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨2 * |Fm.CTu|, x0, fun x hx i u => ((h x hx i).2 u).trans ?_⟩
  let s := (Fm.L x i).sc
  let r := (Fm.D x i).R
  calc
    _ ≤ |Fm.CTu| * (2 * (r.n : ℝ)) * s.x := by
      refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (zero_lt_one.trans s.one_lt_alt).le _) (by positivity)
      · exact mul_le_mul (le_abs_self _) (by unfold Ranks.n; exact_mod_cast r.m_le_f) (Nat.cast_nonneg _) (abs_nonneg _)
      · obtain ⟨hl, hu, _⟩ := J.th_bounds (Fm.L x i)
        unfold Scale.L
        exact J.scale_rpow_le_self_of_le_one _ (by linarith only [hl, hu])
    _ = 2 * |Fm.CTu| * (s.x * r.n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [J.xn_le_Xpp s r]) (by positivity)

theorem muDGam_of_size {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.DGamSize Fm) : J.MuDGam Fm := J.muDGam_of_fact Fm h

theorem muFG_of_full {eps : ℝ} (Fm : FamP eps) (h : NuFullF Fm) : J.MuFG Fm :=
  match h with | ⟨x0, hf⟩ => ⟨x0, fun x hx i u => (hf x hx i u).1⟩

theorem linkMu_of_sizes {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hF : J.MuFG Fm)
    (hR : J.MuRank Fm) : LinkMu Fm := J.linkMu Fm (muZero_free Fm) hF hR (muTu_of_size Fm hT) (muDGam_of_size Fm hG)

theorem linkMu_of_full {eps : ℝ} (Fm : FamP eps) (hT : Formalism.MainNotions.TuSize Fm) (hG : Formalism.MainNotions.DGamSize Fm) (hNF : NuFullF Fm)
    (hR : J.MuRank Fm) : LinkMu Fm := linkMu_of_sizes Fm hT hG (muFG_of_full Fm hNF) hR

end Formalism.SlopeId
end
