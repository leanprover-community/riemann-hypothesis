module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd

@[expose] public section
open MeasureTheory Matrix
open scoped InnerProductSpace
noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.DDSmoothness

theorem nonzero_K_finite : Formalism.MainNotions.S.Pv.AmpDD.NzKF := by
  intro hKD hKS k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hσ hw0 l hl hnz
  obtain ⟨x, hxDD, hlx⟩ := hnz
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hl
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DD_smooth hKS hlam hσ hw0 x hxDD
  let e : ℝ := ‖l x‖ / (|C| + 1)
  have he : 0 < e := div_pos (norm_pos_iff.mpr hlx) (by positivity)
  obtain ⟨v, hvK, hv⟩ := hKD k r ε lam H σ hlam hσ x hxs Ws hWs e he
  refine ⟨v, hvK, fun hlv => ?_⟩
  have hvs := hKS k r ε lam H σ hlam hσ v hvK
  have hd : x - v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v]
    exact smooth_add hxs (smooth_smul (-1) hvs)
  suffices h : ‖l x‖ ≤ |C| * e by
    nlinarith only [h, he, show e * (|C| + 1) = ‖l x‖ from div_mul_cancel₀ _ (by positivity)]
  rw [show l x = l (x - v) by simpa [hlv] using hadd (x - v) hd v hvs]
  exact (hbd (x - v) hd).trans (mul_le_mul (le_abs_self C) hv.le
    (List.sum_nonneg fun y hy => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      exact norm_nonneg _) (abs_nonneg C))

end Formalism.MainNotions.S.Pv.AmpDDPf
