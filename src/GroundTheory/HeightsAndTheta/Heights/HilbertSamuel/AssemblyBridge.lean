import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtra

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dif_pos hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem ResolutionMixedBridge.proof : ResolutionMixedBridge.Statement := by
  intro D Ω _ _ κ _ d M m₁ hM hm₁
  have hex : ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (coordIdeal ℤ d.x) Ψ :=
    goodProjExists Unit (GlobalTheory κ) (coordIdeal ℤ d.x) D d.arith
  set B : HermLine (GlobalTheory κ) := (HermLine.ofCone m₁).tensor (HermLine.ofCone d.m).inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, HermLine.ofCone]
  have hgl : logRatio d.m m₁ = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, HermLine.ofCone, logRatio, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor (gbamix_smoothHerm_ofCone hm₁)
      (isSmoothHerm_inv (gbamix_smoothHerm_ofCone d.smooth)))
  have hsec : IsSectionOn (coordIdeal ℤ d.x) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose (fun j => HermLine.ofCone (M j)) B.inv 1 d.arith
    hex.choose_spec (fun j => gbamix_smoothHerm_ofCone (hM j)) hBs hsec
  unfold ptsIntegral
  rw [dif_pos hex, hgl]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.proof

theorem BlockResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof BlockResolutionMixedBridge.full BlockResolutionInterpIntegral.full

theorem ResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.proof

theorem ResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof ResolutionMixedBridge.full ResolutionInterpIntegral.full

theorem Closed.Inter.pullbackPushforward_holds : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.proof Closed.Inter.BlockGenFinite Closed.Inter.FibreIsolFinite

theorem Closed.Inter.pullbackDensity_holds : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
