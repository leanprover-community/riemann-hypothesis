import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedUniformRotatedOfExpansion
import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.UpdateEqUMinus
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.LimBdFpm
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CoefFacts
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckDualTThrS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveInputsOfHypothesesGlobal
import CompanionTheory.AutomorphicTheory.RankOneTori.FrameBesselBoundOfLargeConstants
import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq CompanionTheory.LimBd.Main

theorem limSteps_of (hI : PI.DSInfCharCap.DSInfCharCap) : LimSteps :=
  ⟨generating_function_polynomial, span_powers, CompanionTheory.CapEig.capelli_coefficient_smooth, CompanionTheory.CapEig.capelli_coefficient_continuity,
    CompanionTheory.CapEig.coefEig_of_infChar hI, phase_zero_alt, beta_at_infinity_zero⟩

end CompanionTheory.WaveGrid
end

section
namespace CompanionTheory.WaveGrid.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity Formalism.QuantumDeterminants MeasureTheory

theorem global_regularity_jacobi : GRegJ :=
  gRegJ_of nilpotent_derivative unitary_capelli_holds group_equations_post_holds smooth_of_coefficients_holds
    (gRegScalar_of group_chart_holds chart_equations_holds classical_to_weak_solution elliptic_regularity_weighted JfS.symbol_nilpotent_holds lie_stabilizer_splitting)

theorem smooth_coefficient_bessel : SmoothKB := by
  intro P Wp Wq _ _ _ _ _ _ p f A hA hCk hCC heig
  have hThr : JF.TransportedAlt P.k P.r A (2 * P.r + P.k + 1) := hA _ (by
    unfold CompanionTheory.JfS.NN
    nlinarith [Nat.zero_le (2 * P.r * (2 * P.r + P.k + 1) * (2 * P.r + P.k + 1))])
  have hF := Gr.jf_mem_FFlM p.T.base A (2 * P.r + P.k + 1) f hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := p.hP
  refine global_regularity_jacobi P.k P.r Wp Wq p.T.base _ _ (B.JF p.T.base f) hTy hTy' hF fun Y => ?_
  obtain ⟨c, hc⟩ := heig Y
  refine ⟨c, fun g hg => ?_⟩
  have hgG : g ∈ B.GV P.k P.r := hg.1
  have hCkn : B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f := B5.ckOn_mono le_top hCk
  rw [casimir_under_jacquet_integral P.k P.r Wp Wq p.T.base A (2 * P.r + P.k + 1) f (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ q ∂p.T.base.μSS,
      JF.xiP p.T.base q • Q.CV P.k P.r (Y : ℂ) (B.rho p.T.base q f) g =
        c • (JF.xiP p.T.base q • B.rho p.T.base q f g) := by
    filter_upwards [B7.ae_inSS p.T.base] with q hq
    rw [capelli_rho_commute P.k P.r _ _ p.T.base (Y : ℂ) f q hq hCkn _ hgG]
    have hs := B7.sgs_mem p.T.base hq hgG
    simp only [B.rho]
    rw [hc _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end CompanionTheory.WaveGrid.Coef
end

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBPEq
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT zuckT_of_zuck zuckDualT_of_zuckDual)

theorem asymptotic_different_types : AsmDiff := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBP.CompactFormNormalFormDomination.thmBpAt_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA _
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA

theorem asymptotic_equal_types : AsmEq := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBPEq.CompactFormNormalFormDomination.thmBpAt_eqR_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf
    hfA _ _
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf hfA

end CompanionTheory.WaveGrid
end

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.BasicNotions CompanionTheory.LimBd.Main

theorem uniqueness_global : WAt.UniqG := by
  intro k r ε lam hl h hg hh H _ _ _ σ hσ H' _ _ _ σ' hσ'
  refine ReciprocityTheory.ChartRestriction.DS.discrete_series_unique_large_gap k r ε lam hl h hg (lt_of_le_of_lt ?_ hh) H σ hσ H' σ' hσ'
  have h1 : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (2 * r + k + 1))) h2 (Nat.cast_nonneg _)
    (by positivity)
  linarith [show ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) *
    ((2 * r + k + 1 : ℕ) : ℝ) by ring]

theorem wave_bessel_period_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct) (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3)
    (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91) (Cb : ℝ) : WEnd.WBp Cb :=
  have hS := limSteps_of CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  have hK := CompanionTheory.D.gk.admitted.k_finite_smooth
  WEnd.wBp_of hCt ht hZ hZd hS (endDiffW_of asymptotic_different_types hS Coef.smooth_coefficient_bessel hK hZ hZd)
    (endEqW_of asymptotic_equal_types GlobalTheory.CompanionTheory.WignerShift.wigExists hS Coef.smooth_coefficient_bessel hK hZ hZd) hK H uniqueness_global Cb

theorem weighted_bound_rotated_uniform_of_cubic_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct Cgf : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  WGlue.weighted_uniform_rotated_of_expansion_alt_alt (wave_bessel_period_threshold hCt ht hZ hZd H)
    (Tied.coefCC1_of hCt ht hZ CompanionTheory.D.gk.admitted.k_finite_smooth CompanionTheory.CapEig.capelli_coefficient_continuity) hOB

open ReciprocityTheory.ChartRestriction.DS in
theorem thrS_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) : G2.thrS ε + 1 < 43 * (n : ℝ) ^ 2 := by
  have hq : S7.q0 ε ≤ n := (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have hq' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg (S7.q0 ε) : (0 : ℝ) ≤ _)]
  have h1 : (n : ℝ) * (S7.q0 ε : ℝ) ≤ n * n := mul_le_mul_of_nonneg_left hq' (by positivity)
  unfold G2.thrS
  rcases max_cases (2 * (n : ℝ)) (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with h2 | h2 <;>
    rw [h2.1] <;> nlinarith

theorem thrS_le (n : ℕ) (ε : Fin n → Bool) (hn : 1 ≤ n) : ReciprocityTheory.ChartRestriction.DS.G2.thrS ε ≤ 43 * (n : ℝ) ^ 3 := by
  have h1 := thrS_lt ε hn
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hn) (by norm_num)
  linarith

theorem uniform_bessel_rank_three_of_inputs {Cgf : ℝ} (H : WEnd.In91) (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) :
    Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  weighted_bound_rotated_uniform_of_cubic_threshold (by norm_num) thrS_le CompanionTheory.Zuck.zuckT_thrS CompanionTheory.Zuck.zuckDualT_thrS H hOB

end CompanionTheory.WaveGrid
end

section
namespace CompanionTheory.WaveGrid

theorem weighted_bound_rotated_uniform_of_hypsG (H : BranchingSupport.HypsG) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  uniform_bessel_rank_three_of_inputs (WEnd.wave_inputs_of_hypotheses_global H) fun D => Formalism.MainStatements.RankOne.one_bessel_torus_bound D (le_refl 100)

end CompanionTheory.WaveGrid
end

section
namespace CompanionTheory.WaveGrid

theorem weighted_bound_rotated_uniform : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  weighted_bound_rotated_uniform_of_hypsG (CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap)

end CompanionTheory.WaveGrid
end
