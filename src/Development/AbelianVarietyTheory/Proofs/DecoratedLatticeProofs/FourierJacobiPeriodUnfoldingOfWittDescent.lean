import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsConvOfInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.BesselIntegrand

theorem handFB_smul_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handFB s vL Y Ξ h₁ := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem unfF_eq_besFun : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  intro D hD ψ σ J B s vL Y G Φ hΦ h h₁ n
  have h1 : IsThetaFunO ψ J.W B.V (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦ
  have h2 : IsThetaFunO ψ J.W B.V (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := s.weil.om_pres _ _ h1
  have e : s.om (1, n.1 * embA B.d B.o h₁ * h) Φ = s.om (1, n.1) (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      one_mul, one_mul]
  have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s _ h1 1 h₁
  rw [map_one] at c
  unfold unfF besFun rTrans
  rw [e, GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B s _ h2 n.1 n.2, c, handFB_smul_om]
  ring

end GlobalTheory.Unf.FB.BesselIntegrand
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  atlas_forward_decl GlobalTheory.Unf.FB.BesselIntegrand.unfF_eq_besFun
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_semidirectProduct_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  first | exact @GlobalTheory.Unf.besSemi | exact GlobalTheory.Unf.besSemi | (intros; apply GlobalTheory.Unf.besSemi <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem unfF_continuous_invariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨hc, hi, he⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
    have h1 := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D J.W₀ J.cpt J.v0 (GA D B.V)
      (fun h₀ h => tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) hc hi).2.1
    have h2 : unfF s vL Y G Φ = fun h => G h *
        ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
      funext h
      rw [unfF, he h]
    rw [h2]
    exact hG.2.1.mul h1
  · intro γ hγ h
    obtain ⟨hq, hb⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨-, hone, -, -, hdec, -⟩ :=
      GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1
    obtain ⟨n, hn, h₁, rfl⟩ := (hdec γ).1 hb
    obtain ⟨hnq, hhq⟩ := ((GlobalTheory.T.besselGroup_semidirectProduct_rational D σ B).2.2.2.2 n hn h₁).1 hq
    have hth : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) :=
      (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
    have hinv := (GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B s vL Y _ hY hth).1 h₁ hhq 1
    rw [mul_one] at hinv
    have e := GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ ⟨n, hn⟩
    refine e.trans ?_
    simp only [besFun, rTrans, unfF]
    rw [hinv, hone _ n hnq, hG.1 _ hq h, star_one, mul_one, mul_comm]

end GlobalTheory.Unf.FB
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedBessel_continuous_leftInvariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  atlas_forward_decl GlobalTheory.Unf.FB.unfF_continuous_invariant
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem quasiFam_bdd_on_compact {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S L : HSp D}
    (v : VolM D L.rank S.rank) {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) {K : Set (GA D S)}
    (hK : IsCompact K) : ∃ M : ℝ, ∀ h ∈ K, ∀ w, ‖Y h w‖ ≤ M := by
  set Kf : Mx D L.rank S.rank → GA D S → ℂ := fun x p => ((‖Y p x‖ : ℝ) : ℂ) with hKf
  have hc : Continuous (Function.uncurry Kf) :=
    Complex.continuous_ofReal.comp (continuous_norm.comp (hY.cont.comp continuous_swap))
  have hper : ∀ γ ∈ ratMx D L.rank S.rank, ∀ x p, Kf (γ + x) p = Kf x p := by
    rintro γ ⟨γ', rfl⟩ x p
    have hq := hY.quasi p γ' x
    have h1 : (incA D).toAddMonoidHom.mapMatrix γ' = ratW L S γ' := rfl
    simp only [hKf, h1, hq, norm_mul, hψ.1.2.1, one_mul]
  obtain ⟨-, -, hloc, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D L.rank S.rank v (GA D S) Kf hc hper
  choose C hC using hloc
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun p => {q | ∀ x, ‖Kf x q‖ ≤ C p}) (fun p _ => hC p)
  refine ⟨∑ p ∈ t, |C p|, fun h hh w => ?_⟩
  obtain ⟨p, hp, hhp⟩ := Set.mem_iUnion₂.1 (hcov hh)
  have := hhp w
  simp only [hKf, Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
  exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _) hp))

theorem unfolded_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  haveI := J.v0.haar
  haveI := s.vW.haar
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  obtain ⟨-, -, hvb, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvb (σ + 1) J.W₀.rank
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS vb s.vU s.vW x₀
    hbase G Φ hG hΦ 𝓑 h𝓑'
  obtain ⟨hΓc, hΓd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W₀ (GQ J.W₀) le_rfl
  refine GlobalTheory.fubini_compact_quotient (GA D J.W₀) J.v0.μ (GQ J.W₀) hΓc hΓd J.cpt J.v0.𝓕 J.v0.fund (GA D B.V)
    (s.vW.μ.restrict 𝓑) (fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ?_ ?_ ?_
  · exact ((hG.2.1.comp continuous_snd).mul hcont).measurable
  · intro γ hγ h x
    simp only [hinv γ hγ h x]
  · intro K hK
    obtain ⟨M, hM⟩ := quasiFam_bdd_on_compact s.weil.std vL hY hK
    obtain ⟨c, hc⟩ := hK.bddAbove_image
      ((continuous_const.mul ((continuous_height J.W).pow A)).comp J.d.continuous_embed).continuousOn
    refine ⟨M.toNNReal * c.toNNReal, fun h₀ hh₀ => ?_⟩
    have hc' : C * height J.W (J.d.emb0 h₀) ^ A ≤ c := hc ⟨h₀, hh₀, rfl⟩
    calc ∫⁻ h, ‖G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)‖ₑ ∂(s.vW.μ.restrict 𝓑)
        ≤ ∫⁻ h in 𝓑, ENNReal.ofReal M * (‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν) ∂s.vW.μ := by
          refine lintegral_mono fun h => ?_
          rw [enorm_mul, mul_left_comm]
          have := (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) (quasi_of_fam hY h₀)
            (s.weil.om_pres _ _ hΦ)).2 M (hM h₀ hh₀)
          rw [hx₀]
          gcongr
      _ = ENNReal.ofReal M * ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν ∂s.vW.μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal c :=
          by gcongr; exact (hCA (J.d.emb0 h₀)).trans (ENNReal.ofReal_le_ofReal hc')
      _ = ((M.toNNReal * c.toNNReal : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul]; rfl

end GlobalTheory.Unf.FB
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  atlas_forward_decl GlobalTheory.Unf.FB.unfolded_integrable
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierBesselThetaIntegrand_isUnfoldingTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B → IsTh ψ J.d B.V x₀ (th J ψ B y) := by
  first | exact @GlobalTheory.th_isTh | exact GlobalTheory.th_isTh | (intros; apply GlobalTheory.th_isTh <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

theorem weilRepresentationOnFunctions_embed_mul {D : D7} {V W : HSp D} (om : Om V W) (e g : GA D V) (h : GA D W) (Φ : WO V W → ℂ) :
    om (g, h) (om (e, 1) Φ) = om (g * e, h) Φ := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem fjN_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑 h₀
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨-, -, hvM, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvM (σ + 1) J.W₀.rank
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hq : Quasi ψ J.W₀ B.L (Y h₀) := quasi_of_fam hY h₀
  have hTh := GlobalTheory.T.fourierBesselThetaIntegrand_isUnfoldingTheta D ψ s.weil.std σ J B (Y h₀) hq x₀ hx₀
  have hΦ' : IsThetaFunO ψ J.W B.V (s.om (J.d.emb0 h₀, 1) Φ) := s.weil.om_pres _ _ hΦ
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have key := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS J.vN vb s.vU s.vW x₀
    (th J ψ B (Y h₀)) hbase hTh G (s.om (J.d.emb0 h₀, 1) Φ) hG hΦ' 𝓑 h𝓑').2
  have hL : (fun n : flagN J.d => fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n) =
      fun n => th J ψ B (Y h₀) n.1 * liftS s.om s.vW.μ s.vW.𝓕 G (s.om (J.d.emb0 h₀, 1) Φ) n.1 := by
    funext n
    simp only [fjSrcKerFun, JacLev.ker, th, Step.lift, liftS_apply, zl, weilRepresentationOnFunctions_embed_mul]
    ring
  have hR' : (fun h => G h * fl ψ J.d B.V s.vS vb s.vU (th J ψ B (Y h₀)) (rat x₀) (s.om (1, h) (s.om (J.d.emb0 h₀, 1) Φ))) =
      fun h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) := by
    funext h
    rw [weilRepresentationOnFunctions_embed_mul, one_mul, hx₀, (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) _ hq (s.weil.om_pres _ _ hΦ)).1]
  rw [hL, ← hR']
  exact key

end GlobalTheory.Unf.FB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_integral_over_N_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  atlas_forward_decl GlobalTheory.Unf.FB.fjN_unfold
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem per_lift_eq_integral_unfF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have := s.vW.haar
  have := J.v0.haar
  have hI := GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hin := GlobalTheory.T.fourierJacobi_integral_over_N_unfold D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hc := (GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ).2.2
  have hU : ∀ h, unfF s vL Y G Φ h = ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
    intro h
    rw [unfF, hc h, integral_const_mul]
  constructor
  · have := hI.integral_prod_right
    refine this.congr ?_
    exact Filter.Eventually.of_forall fun h => (hU h).symm
  · calc J.per ψ B.ζ Y (s.lift G Φ)
        = ∫ h₀ in J.v0.𝓕, ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ ∂J.v0.μ := by
          unfold JacLev.per fjSrcKer
          congr 1
          funext h₀
          exact hin h₀
      _ = ∫ h in 𝓑, ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ ∂s.vW.μ :=
          integral_integral_swap hI
      _ = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
          congr 1
          funext h
          exact (hU h).symm

end GlobalTheory.Unf.FB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  atlas_forward_decl GlobalTheory.Unf.FB.per_lift_eq_integral_unfF
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem GlobalTheory.Unf.unfFB_of_descent : ∀ D : D7, Descent D → UnfFB D := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  haveI := s.vW.haar
  obtain ⟨hcnt, hdisc, hfd⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hcont, hclN, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hcont hclN hnorm huniq hrat B.vA B.vN.ν B.vN.𝓝
    hU.1 hU.2.1 hHR
  obtain ⟨hFc, hFi⟩ := GlobalTheory.T.unfoldedBessel_continuous_leftInvariant D hD ψ σ J B s vL Y G Φ hY hG hΦ
  obtain ⟨hI, hL⟩ := GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have habs := GlobalTheory.Unf.BesInt.absConv_of_invariant D σ B _ hFc hFi
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unfF s vL Y G Φ (g * h) :=
    fun h => (hFc.comp (continuous_mul_right h)).measurable
  have key := GlobalTheory.quot_fubini_mean (GA D B.V) s.vW.μ (besGrp B.d B.o) (GQ B.V ⊓ besGrp B.d B.o) inf_le_right
    (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o) hcnt hdisc B.μR hHR 𝓡 𝓑 h𝓡 h𝓑 (unfF s vL Y G Φ)
    hFc.measurable hFi hI (fun h => ((hint _ (hm h)).1).2 (habs h))
  rw [← hL] at key
  convert key using 2 with h
  have e2 : (∫ r : besGrp B.d B.o in 𝓡, unfF s vL Y G Φ (r * h) ∂B.μR) =
      ∫ h₁ in B.vA.𝓕, ∫ n in B.vN.𝓝, unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) ∂B.vN.ν ∂B.vA.μ :=
    (hint _ (hm h)).2 (habs h)
  rw [e2, BesLev.per, besPer]
  congr 1; funext h₁; congr 1; funext n
  exact (GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ n).symm

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent : ∀ D : D7, Descent D → UnfFB D := by
  atlas_forward_decl GlobalTheory.Unf.unfFB_of_descent
end
