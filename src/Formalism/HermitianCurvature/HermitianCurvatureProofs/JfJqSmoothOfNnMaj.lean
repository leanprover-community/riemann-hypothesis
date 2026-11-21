import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by
  intro hD k r Wp Wq _ _ _ _ _ _ D A F hT hC
  obtain ⟨hmeas, hbd⟩ := hD k r Wp Wq D A 0 F hT hC
  have hx : Continuous (fun p : SS k r => xiP D p) := by
    clear hmeas hbd hD hT hC
    unfold xiP psi ell
    refine Continuous.mul ?_ (Continuous.star ?_)
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
  have h0 : (0 : ℕ) + 0 ≤ 0 := le_rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hbb⟩ := hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)
    have hbg := hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)
    have hm := hmeas [] [] (by simp) (by simp) h0 g hg
    refine Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbg] with p hp
    calc ‖xiP D p • rho D p F g‖ = ‖xiP D p‖ * ‖rho D p F g‖ := norm_smul _ _
      _ ≤ 1 * ‖rho D p F g‖ := by gcongr; exact SmoothnessOnGoodSet.norm_xiP D p
      _ = ‖rho D p (dLR (List.map (AdL p) []) (List.map (AdR p) []) F) g‖ := by rw [one_mul]; rfl
      _ ≤ b p := hp
  · intro K hK hKO
    obtain ⟨b, hb, hbb⟩ := hbd K hK hKO
    exact ⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩

end Formalism.FourierDecayAlt.P.JFxDs1
end
end

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

lemma glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Formalism.FourierDecayAlt.Q.Glev k r 0 := by simpa [Formalism.FourierDecayAlt.Q.Glev] using hg



end Formalism.FourierDecayAlt.P.CellSmoothness
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem jf_jDom_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)

theorem jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom (jf_jDom_of_nnMaj h)



end Formalism.FourierDecayAlt.P
end
end
