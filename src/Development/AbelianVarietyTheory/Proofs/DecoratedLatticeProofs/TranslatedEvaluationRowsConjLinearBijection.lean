import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  first | exact @GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | exact GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | (intros; apply GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  intro D X h θ S M J χ t v₀ _ hv₀ T hTm hae
  let T' : MMap M := PiTensorProduct.lift.symm T
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hTm
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ T').1 hT'm
  have hval : T' v₀ = T (PiTensorProduct.tprod ℂ v₀) := by
    simp [T', PiTensorProduct.lift_symm]
  have hf := (hT.aut v₀).cont
  have hleft := (hT.aut v₀).left
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => T' v₀ (ι.symm x * t)
  have hφ : ∀ x, φ x = T' v₀ (ι.symm (x * ι t)) := fun x => by
    simp only [φ, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hφc : Continuous φ := by
    have e : φ = fun x => T' v₀ (ι.symm (x * ι t)) := funext hφ
    rw [e]
    exact hf.comp (ι.symm.continuous.comp (continuous_mul_right _))
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    show T' v₀ (ι.symm (γ * y) * t) = T' v₀ (ι.symm y * t)
    rw [map_mul, mul_assoc]
    exact hleft _ (hQ γ hγ) _
  have hae' : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have e : φ = evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
      funext x; simp only [φ, evS, hval]; rfl
    rw [e]; exact hae
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae'
  have hv : T' v₀ = 0 := by
    funext g
    have e := hz (ι (g * t⁻¹))
    simpa [φ] using e
  have hT0 : T' = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ hv
  have : T = PiTensorProduct.lift T' := (PiTensorProduct.lift.apply_symm_apply T).symm
  rw [this, hT0, map_zero]

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), IsInfFam θ → (∀ τ, (v₀ τ : M.H τ) ≠ 0) → ∀ T ∈ MultT θ M J χ, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 → T = 0 := by
  atlas_forward_decl GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  first | exact @GlobalTheory.Core.SeeOnto.see_onto | exact GlobalTheory.Core.SeeOnto.see_onto | (intros; apply GlobalTheory.Core.SeeOnto.see_onto <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem star_comp_const_smul_eq_conj_smul {α : Type*} (a : ℂ) (F : α → ℂ) :
    (fun x => star ((a • F) x)) = (starRingEnd ℂ a) • (fun x => star (F x)) := by
  funext x
  simp [star_mul']

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

set_option maxHeartbeats 2000000 in

theorem evalAll_rows : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  intro hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
  have hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨c, -, hc⟩ := hConj
    have h1 := (X.low (X.pl.symm τ)).1
    rw [← (c τ).norm_map, hc τ]
    exact h1
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hfun := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hCusp D X h θ S M J χ t hθ hMat
  obtain ⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) :=
    ⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩
  have hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X := fun T =>
    GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)
  have hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := fun T => by
    filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2
    rw [h1, Pi.star_apply, h2]
  have e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) +
        (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro T T'
    rw [Submodule.coe_add, LinearMap.add_apply]
    funext x
    exact star_add _ _
  have e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro a T
    rw [Submodule.coe_smul, LinearMap.smul_apply]
    generalize T.1 (PiTensorProduct.tprod ℂ v₀) = F
    exact star_comp_const_smul_eq_conj_smul a (evS X h t F)
  let j : MultT θ M J χ →ₗ⋆[ℂ] HHX X :=
    { toFun := fun T => ⟨star (f T), hmem T⟩
      map_add' := fun T T' => by
        apply Subtype.ext
        show star (f (T + T')) = star (f T) + star (f T')
        apply Lp.ext
        refine (hstar (T + T')).trans ?_
        rw [e1]
        exact ((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun a T => by
        apply Subtype.ext
        rw [Submodule.coe_smul]
        apply Lp.ext
        refine (hstar (a • T)).trans ?_
        rw [e2]
        exact ((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }
  have hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := hstar
  refine ⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩
  · rw [injective_iff_map_eq_zero]
    intro T hT
    have h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0 := by
      rw [hT]; exact Lp.coeFn_zero _ _ _
    have hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 := by
      filter_upwards [hj T, h0] with x h1 h2
      rw [h2] at h1
      have h3 := congrArg star h1
      rw [star_star] at h3
      rw [← h3]
      exact star_zero _
    exact Subtype.ext (GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)
  · intro ψ
    have hψ : star (star (ψ : L2X X)) ∈ HHX X := by rw [star_star]; exact ψ.2
    obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
      (star (ψ : L2X X)) hψ
    refine ⟨⟨T, hT⟩, ?_⟩
    apply Subtype.ext
    apply Lp.ext
    refine (hj ⟨T, hT⟩).trans ?_
    filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3
    rw [h2, Pi.star_apply] at h3
    rw [← h3, star_star]

end GlobalTheory.Core.Mi
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  atlas_forward_decl GlobalTheory.Core.Mi.evalAll_rows
end
