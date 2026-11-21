import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  first | exact @GlobalTheory.LevelCompact.exists_level_compact | exact GlobalTheory.LevelCompact.exists_level_compact | (intros; apply GlobalTheory.LevelCompact.exists_level_compact <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.Unf

theorem mixS_om_compact_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  intro D ψ S T χS χT om hω θ hθ S₀ ρ d v f hf Kp hKp
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact D ψ S T χS χT om hω f hf Kp hKp
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hω.std θ hθ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hKN N
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hω θ hθ N
  obtain ⟨c, hc⟩ := hA f hf
  have hcont : Continuous fun p : GA D S × GA D T =>
      c * (GlobalTheory.Grow.height S p.1 * GlobalTheory.Grow.height T p.2) ^ A :=
    continuous_const.mul ((((GlobalTheory.Grow.continuous_height S).comp continuous_fst).mul
      ((GlobalTheory.Grow.continuous_height T).comp continuous_snd)).pow A)
  obtain ⟨B, hB⟩ := hKp.bddAbove_image hcont.continuousOn
  refine ⟨(C : ℝ) * max B 0, fun p hp x w => ?_⟩
  have h1 := hC (om p f) (hUK p hp) x w
  have h2 : supSob ψ θ N (om p f) ≤ ENNReal.ofReal (max B 0) :=
    (hc p.1 p.2).trans (ENNReal.ofReal_le_ofReal ((hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)))
  have hm := maj_nonneg θ K N x
  have h3 : ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * max B 0 * maj θ K N x) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end GlobalTheory.Unf

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  atlas_forward_decl GlobalTheory.Unf.mixS_om_compact_maj
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.Unf

theorem flatFun_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∀ K : Set (GA D V × GA D W), IsCompact K → ∃ M : UX D ρ → ℝ, Integrable M vU.ν ∧ ∀ p ∈ K, ∀ y w u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (om p Φ) w u‖ ≤ M u := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hW vU x hx Φ hΦ K hK
  have hn : ∀ a, ‖ψ a‖ = 1 := hW.std.1.2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨K', hK', hC⟩ := GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant D ψ V W χV χW om hW θ hθ V₀ ρ dV vS Φ hΦ K hK
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular D θ hθ W.rank ρ vU x hx
  obtain ⟨C, hC⟩ := hC N
  refine ⟨fun u => C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1), (hN K' hK').const_mul C, ?_⟩
  intro p hp y w u
  have hT := vT.covol
  unfold flatFun evalAt
  rw [norm_mul, norm_star]
  have h1 : ‖psiUni ψ u.1‖ = 1 := hn _
  rw [h1, one_mul]
  unfold GlobalTheory.MixModel.HypDec.mixT
  have hb : ∀ ξ ∈ vT.𝓕, ‖heisO ψ V₀ W (dW.incX V₀ ξ) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w)
      (dV.mixS W ψ vS.μ vS.𝓕 (om p Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1)))) 0‖ ≤ C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1) := by
    intro ξ _
    rw [dW.integrandT_eq, norm_mul, hn, one_mul]
    exact hC p hp _ _
  have := norm_setIntegral_le_of_norm_le_const (by rw [hT.2.2]; exact ENNReal.one_lt_top) hb
  rw [measureReal_def, hT.2.2, ENNReal.toReal_one, mul_one] at this
  exact this
end GlobalTheory.Unf
end
end
