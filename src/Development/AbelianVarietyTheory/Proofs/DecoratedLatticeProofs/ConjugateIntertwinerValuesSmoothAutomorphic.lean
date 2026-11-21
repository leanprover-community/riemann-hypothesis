import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapIntertwinesRealPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowCont

theorem reg_star {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : X.B.I.GA) (φ : L2X X) :
    X.B.R g (star φ) = star (X.B.R g φ) := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  obtain ⟨-, hr, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a := fun a => ⟨measurable_mul_const a, hr a⟩
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)
  have e1 := X.B.R_spec g (star φ)
  have e2 := X.B.R_spec g φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

theorem iotaX_rat_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
    intro I I' e x
    subst e; rfl
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)

theorem exists_conj_multilinear {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.Y 0) S) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (Φ : X.B.Hs →L[ℂ] L2X X) :
    ∃ Ψ : ContinuousMultilinearMap ℂ M.H (L2X X), ∀ y,
      Ψ y = star (Φ (X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm fun τ => c τ (y τ)))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a) := by
    intro y τ a
    rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
    refine congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)
    exact Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'
  have hCc : Continuous C := by
    refine continuous_pi fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (c τ).continuous.comp (continuous_apply τ)
  let Ψ₀ : MultilinearMap ℂ M.H (L2X X) := MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y))))
    (fun y τ a b => by rw [hCu, hCu, hCu, map_add, m.map_update_add, map_add, map_add])
    (fun y τ a b => by
      rw [hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ,
        starRingEnd_self_apply])
  refine ⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩
  show star (Φ (m (C y))) = _
  rw [hm]

set_option maxHeartbeats 1000000 in

theorem conjMap_cont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩

end GlobalTheory.ConjRowCont

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  first | exact @GlobalTheory.ConjRowCont.conjMap_cont | exact GlobalTheory.ConjRowCont.conjMap_cont | (intros; apply GlobalTheory.ConjRowCont.conjMap_cont <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  first | exact @GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | exact GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | (intros; apply GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowAut

theorem conj_lie {n : ℕ} {P H J E : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hs : Pᴴ * H * P = J)
    (hE : Eᴴ * J + J * E = 0) : (P * E * P⁻¹)ᴴ * H + H * (P * E * P⁻¹) = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  calc _ = (P⁻¹)ᴴ * Eᴴ * Pᴴ * H * (P * P⁻¹) + ((P⁻¹)ᴴ * Pᴴ) * H * (P * E * P⁻¹) := by
        rw [hPi, hPiH]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = (P⁻¹)ᴴ * (Eᴴ * J + J * E) * P⁻¹ := by
        rw [← hs]; simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hE]; simp

theorem exp_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (E : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • (P * E * P⁻¹)) * P = NormedSpace.exp (t • E) := by
  have h : t • (P * E * P⁻¹) = P * (t • E) * P⁻¹ := by simp
  rw [h, Matrix.exp_conj _ _ hP]
  exact (GlobalTheory.IotaReal.conj_eq_iff _ _ _ hP).2 rfl

theorem iota_data {D : D7} (θ : InfFam D) (hθ : IsInfFam θ)
    (hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)
    (∀ k ∈ GQ (D.sp.Y 0), ι k ∈ I.GFset) ∧ (∀ k ∈ GfC (D.sp.Y 0), (ι k).1 = 1) ∧
    (∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1) ∧
    (∀ v E, Formalism.REAL.inG (I.ε v) E → ∃ τ, ∃ Y ∈ lieAt (D.sp.Y 0) τ, ∀ t : ℝ,
      (ι (oneP θ (D.sp.Y 0) τ Y t)).2 = 1 ∧ uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 v) = NormedSpace.exp (t • E) ∧
        ∀ w, w ≠ v → uMat ((ι (oneP θ (D.sp.Y 0) τ Y t)).1 w) = 1) ∧
    (1 ≤ I.n → ∀ v, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Real.exp (GlobalTheory.Count.dOp (uMat ((ι g).1 v))) ≤ c * normInf θ (D.sp.Y 0) g) := by
  intro ι
  subst h
  have key : ∀ k, (∀ v, uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k * (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit
  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  have hsnd : ∀ k ∈ GinfC (D.sp.Y 0), (ι k).2 = 1 := by
    intro k hk
    apply Subtype.ext
    apply Units.ext
    refine (key k).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) k).val = 1 := by
      rw [show finHom (D.sp.Y 0) k = 1 from hk]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨fun k hk => (Formalism.IndefR.RationalEmbedding.iota_rat D k).1 hk, fun k hk => ?_, hsnd, fun v E hE => ?_, fun hn v => ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := GlobalTheory.IotaReal.infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · have hY : (Formalism.L2.SG.InstExistsPf.instOf D).P v * E * ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ∈
        lieAt (D.sp.Y 0) ((Formalism.L2.Host.tauPl D).symm v) :=
      conj_lie (hPu v) ((Formalism.L2.SG.InstExistsPf.instOf D).P_spec v) hE
    refine ⟨_, _, hY, fun t => ?_⟩
    have hat := GlobalTheory.IotaReal.isAtTau_atTau θ hθ _ _ (hexp _ _ hY t)
    refine ⟨hsnd _ hat.1, ?_, fun w hw => ?_⟩
    · refine (hinf _ v).trans (Eq.trans ?_ (exp_conj (hPu v) E t))
      exact congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P v) hat.2.1
    · refine (hinf _ w).trans ?_
      refine (congrArg (fun M : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ => ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * M *
        (Formalism.L2.SG.InstExistsPf.instOf D).P w) (hat.2.2 _ fun e => hw ((Formalism.L2.Host.tauPl D).symm.injective e))).trans ?_
      show ((Formalism.L2.SG.InstExistsPf.instOf D).P w)⁻¹ * (1 : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ) * (Formalism.L2.SG.InstExistsPf.instOf D).P w = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd w)]
  · obtain ⟨c, hc0, hc⟩ := GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹
      ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
    refine ⟨c, hc0, fun g => ?_⟩
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero _ hn (ι g) v
    rw [hinf g v] at h0 ⊢
    exact (hc _ h0).trans (mul_le_mul_of_nonneg_left (GlobalTheory.TauNorm.sum_le_normInf θ g _) hc0)

set_option maxHeartbeats 800000 in

theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsAutFunSm θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  have hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous hP D X h θ S M J χ t c hS hθ hgap hid hm hc Φ hΦ hrep
  obtain ⟨hrat, hfst, hsnd, hone, hgr⟩ := iota_data θ hθ
    (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h
  change ∀ k ∈ _, iotaX X h k ∈ _ at hrat
  change ∀ k ∈ _, (iotaX X h k).1 = 1 at hfst
  change ∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd
  choose f hf using hrep
  have hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹))) := fun u y => by
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨A, -, hA⟩ := hΦ
    have hA' : Φ = X.B.Re.comp A := hA.symm
    have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)
    have h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)) := by
      rw [hA']
      exact congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))))
        (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)
    rw [h2] at h1
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y
  have ht : t ∈ GfC (D.sp.Y 0) := hm.1
  have hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a := fun a b ha hb =>
    Prod.ext (by simp [ha]) (by simp [hb])
  have hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := fun u => by
    have : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹))) := funext (hval u)
    rw [this]
    exact ((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_right _))).star
  have haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
    intro u
    refine ⟨fun γ hγ y => ?_, ?_, hcont u⟩
    · rw [hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]
    · obtain ⟨hKo, ⟨K, hK⟩, -⟩ := (GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg
      refine ⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp
        (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩
      · rw [← hK] at hKo
        exact hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2)
          (continuous_snd.comp ((iotaX X h).continuous.comp
            ((continuous_mul_right _).comp (continuous_mul_left _))))
      · have hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g := by rw [← hK]; exact hk
        have h1 : (iotaX X h (t * k * t⁻¹)).1 = 1 :=
          hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))
        have e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹) := by group
        have e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2) := Prod.ext h1 rfl
        rw [hval, hval, e, map_mul, e2, hlev u _ hk']
  intro u
  refine ⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  have key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0),
      ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N := by
    rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
    · refine ⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩
      have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
      rw [this, mul_one, pow_zero, mul_one]
    have hn' : 1 ≤ X.B.I.n := by rw [← rank_eq X h]; exact hn
    have hti : (iotaX X h t⁻¹).1 = 1 := hfst _ ((GfC _).inv_mem ht)
    obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn' hg
    refine ⟨m, fun v x => ?_⟩
    obtain ⟨C, hC⟩ := hm (Set.range f) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩
      obtain ⟨τ, Y, hY, hι⟩ := hone w E.1 E.2
      refine ⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩
      have h1 := (GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star
      simp only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) =
          GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s :=
        GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2
      have e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) =
          y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s) := by
        have h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1 := (hι s).1
        rw [map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right,
          ContinuousMulEquiv.apply_symm_apply]
      show f u _ = f u _
      rw [e2, e1]) _ ⟨v, rfl⟩
    choose b hb0 hb using hgr hn'
    have hp := (GlobalTheory.TauLipschitz.tauLip X.B.I hn').1
    have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb0 w
    refine ⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩
    have hN : 0 ≤ normInf θ (D.sp.Y 0) a := by unfold normInf; positivity
    have e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
      rw [map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]
    have h2 := GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha)
      ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)
    rw [hval, norm_star, e]
    refine (hC _).trans ?_
    have h0 := inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le
    rw [mul_assoc, ← mul_pow, mul_assoc]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun l hl x => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
  rw [hv]
  exact hN v x

end GlobalTheory.ConjRowAut

end
end
