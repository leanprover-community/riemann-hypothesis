import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

open GlobalTheory.ThetaTransform

noncomputable section

namespace GlobalTheory.LineDerivTransfer

theorem hasDerivAt_heisV_of {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) (hΦ'm : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (hΦ'd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0) (w : VA F N) :
    HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ :=
    GlobalTheory.ThetaDeriv.decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (GlobalTheory.SWQ.rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (GlobalTheory.SWQ.rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (GlobalTheory.SWQ.rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (GlobalTheory.ThetaDeriv.hasDerivAt_schr hF ψ hM hΦ'd (GlobalTheory.SWQ.rat ξ + w.1) t).const_mul (ph ξ))
    (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this

theorem thV_smul {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (c : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (c • Φ) = c • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end GlobalTheory.LineDerivTransfer

open GlobalTheory.LineDerivTransfer in

theorem GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  intro D ψ hψ S T JB ξ hB κ _ co hrat Φ hΦ L L' hL hL0 hL' hL0' c hrel x
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  let e := numCoord co σ
  have he : ∀ w w', symplO S T w w' = symV (e w) (e w') := fun w w' => by
    rw [symplO_eq_symp rfl hB, co.form]
    simp only [e, symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  obtain ⟨-, -, hfin, -⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e
  have hc : Continuous e := (GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank _ e).1
  have hΦσ := comp_mem_schA σ hΦ
  have key : ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∃ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin (Fintype.card κ)),
        (∀ x, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) (Φ' (x ∘ σ.symm)) 0) ∧
        (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
          thV ψ Φ' ∘ e := by
    intro L hL hL0
    have hM : IsRealLine (e.toLinearMap.toAddMonoidHom.comp L) := ⟨hc.comp hL, fun t => (hfin _).1 (hL0 t)⟩
    obtain ⟨Φ', hm, hd⟩ := GlobalTheory.ThetaDeriv.exists_deriv_schr hR ψ hψ.1 hM hΦσ
    refine ⟨Φ', hm, fun x => ?_, funext fun w => ?_⟩
    · have h : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) =
          fun t => GlobalTheory.WeilM.schr ψ (e.toLinearMap.toAddMonoidHom.comp L t) (fun y => Φ (y ∘ σ)) (x ∘ σ.symm) := by
        funext t
        simp only [GlobalTheory.WeilM.schr, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, e, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
        congr 2
        funext i
        simp
      rw [h]
      exact hd _
    · rw [thetaTr_eq co σ]
      have h : (fun t : ℝ => heisO ψ S T (L t) (thV ψ (fun y => Φ (y ∘ σ)) ∘ e) w) =
          fun t => heisV ψ (e.toLinearMap.toAddMonoidHom.comp L t) (thV ψ (fun y => Φ (y ∘ σ))) (e w) :=
        funext fun t => congrFun (heisO_comp he (L t) _) w
      rw [show numCoord co σ = e from rfl, h]
      exact (hasDerivAt_heisV_of ψ hR hψ.1 hΦσ hm hM hd (e w)).deriv
  obtain ⟨Φ₁, hm₁, hd₁, hh₁⟩ := key L hL hL0
  obtain ⟨Φ₂, hm₂, hd₂, hh₂⟩ := key L' hL' hL0'
  rw [hh₁, hh₂] at hrel
  have h2 : thV ψ Φ₂ = thV ψ (c • Φ₁) := by
    rw [thV_smul]
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact congrFun hrel w
  have h3 := thV_injOn hR hψ.1 hm₂ (Submodule.smul_mem _ c hm₁) h2
  rw [(hd₂ x).deriv, (hd₁ x).deriv, h3]
  rfl
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  atlas_forward_decl GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  atlas_forward_decl GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

noncomputable section

namespace GlobalTheory.ArchLineCont

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)

theorem continuous_ofMixed' (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd' (F : Type) [Field F] [NumberField F] : Continuous (realAd F) :=
  Continuous.prodMk ((continuous_ofMixed' F).comp (continuous_algebraMap ℝ _)) continuous_const

set_option synthInstance.maxHeartbeats 400000 in

theorem archLine_continuous_finPart : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  intro D S X d e g cS hcS u
  have hform : ∀ t, GlobalTheory.VacTransfer.archLine cS u t =
      (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun t => by
    rw [GlobalTheory.VacTransfer.archLine_apply, hcS]
  refine ⟨?_, fun t => ?_⟩
  · have hsm : Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u : Matrix (Fin S.rank) (Fin d) (AE D)) :=
      (continuous_realAd' D.host.F).smul continuous_const
    have : (GlobalTheory.VacTransfer.archLine cS u : ℝ → WO S X) = fun t =>
        (HMul.hMul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)ᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) :
          Matrix (Fin X.rank) (Fin S.rank) (AE D)) := funext hform
    rw [this]
    exact (hsm.matrix_transpose.matrix_submatrix e id).matrix_mul continuous_const
  · rw [hform]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.mul_apply, map_sum (finPart D)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [(finPart D).map_mul, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.ArchLineSum.finPart_smul,
      show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul, zero_mul, zero_mul]

end GlobalTheory.ArchLineCont
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  atlas_forward_decl GlobalTheory.ArchLineCont.archLine_continuous_finPart
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.VacTransfer

set_option maxHeartbeats 800000 in

theorem exists_darboux_cS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ u, co.e (cS u) = M.co.e u := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hc
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · simp [sgn]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D))
    (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J)
    (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  refine ⟨1, D.host.xi0 • (sgn ε S).gram⁻¹, co, one_smul _ _, fun x => ?_, hco⟩
  obtain ⟨y, z, h⟩ := hM.rat ((x * G⁻¹)ᵀ.submatrix id e.symm)
  refine ⟨y, z, Eq.trans ?_ h⟩
  rw [← hco, hc]
  congr 1
  exact (map_transpose_inv_mul (incA D) e x hdet).symm

theorem vacDatum_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  subst hψ
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  obtain ⟨ξ, JB, co, hJB, hrat, hco⟩ :=
    exists_darboux_cS D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F co Bs.ψ Φ = f := by
    funext w
    obtain ⟨u, rfl⟩ := cS.surjective w
    refine Eq.trans ?_ (hD.2 u)
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco]
  have hvac : ∀ τ z, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f =
      Complex.I • dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f := by
    intro τ z
    funext w
    have h0 := congrFun (hf.2 τ z) w
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (-Complex.I) * h0 +
      dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f w * Complex.I_sq
  refine ⟨fun _ => 1, fun u u' _ _ hrel x => ?_⟩
  have hrel' : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := fun w => by
    simpa using hrel w
  obtain ⟨hc, hc0⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u
  obtain ⟨hc', hc0'⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u'
  have key : (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u' t) f w) 0) =
      Complex.I • (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u t) f w) 0) := by
    refine (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u') hc' hc0').trans
      (Eq.trans ?_ (congrArg (Complex.I • ·) (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u) hc hc0).symm))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact (congrArg (fun z => dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f)
      (GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e Bs Vs Ws hcart cS hcS u u' hrel' τ)).trans (hvac τ _)
  rw [← hΦf] at key
  have h1 := GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv D Bs.ψ hstd (sgn ε S) X JB ξ hJB (Fin S.rank × Fin d) co hrat Φ hD.1 (archLine cS u) (archLine cS u')
    hc hc0 hc' hc0' Complex.I key x
  simpa only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, archLine_apply, hco] using h1

end GlobalTheory.VacTransfer

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuumEquations_transfer_schroedingerDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  atlas_forward_decl GlobalTheory.VacTransfer.vacDatum_transfer
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, Algebra.smul_def]
  congr 1
  simp [evI, realAd]

theorem realAd_mul_snd (t : ℝ) (c : AF F) : (realAd F t * c).2 = 0 := by
  show (realAd F t).2 * c.2 = 0
  simp [realAd]

theorem at_realAd_mul (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 := Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

def gam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (t : ℝ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ _ (y ⬝ᵥ fun i => evI F (w.2 i)) + t ^ 2 * Algebra.trace ℝ _ (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : ℝ) : ℂ)) *
    f (y + t • fun i => evI F (w.1 i))

theorem gam_differentiableAt (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun t => gam w f t y) 0 := by
  unfold gam
  fun_prop

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ) (f : SInf F κ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x = gam w f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  have hK : x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2) =
      realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hev : evI F (realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) =
      t • ((fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (w.2 i)) + t • evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    rw [evI_realAd_mul]
    congr 1
    rw [← evIHom_apply, map_add, evIHom_apply, evIHom_apply, evI_realAd_mul, ← evIHom_apply (x ⬝ᵥ w.2),
      RingHom.map_dotProduct]
    rfl
  unfold schr pureA gam
  rw [hK, hψ.2.2 _ (at_realAd_mul _ _), hev]
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • w).1) i).1) =
      (fun i => evI F (x i)) + t • fun i => evI F (w.1 i) := by
    funext i
    show evIHom (x i + realAd F t * w.1 i) = evI F (x i) + t • evI F (w.1 i)
    rw [map_add, evIHom_apply, evIHom_apply, evI_realAd_mul]
  have hg : (fun i => ((x + (realAd F t • w).1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (realAd F t * w.1 i).2 = (x i).2
    rw [realAd_mul_snd, add_zero]
  rw [hf, hg]
  simp only [map_smul, map_add, smul_eq_mul]
  ring_nf

end GlobalTheory.VacFactor

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dgam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  deriv (fun t => gam w f t y) 0

theorem exists_indep {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ k, g k ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ LinearIndependent ℂ g ∧ Φ = ∑ k, pureA F (f k) (g k) := by
  obtain ⟨m₀, c, p, hp⟩ := Submodule.mem_span_set'.mp hΦ
  choose f₀ g₀ hg₀ hp₀ using fun i => (p i).2
  set f₁ : Fin m₀ → SInf F κ := fun i => c i • f₀ i
  have hΦ' : Φ = ∑ i, pureA F (f₁ i) (g₀ i) := by
    rw [← hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp₀ i]
    funext x
    simp [f₁, pureA, mul_assoc]
  set V := Submodule.span ℂ (Set.range g₀)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g₀)
  let b := Module.finBasis ℂ V
  have hmem : ∀ i, g₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : Fin m₀ → Fin (Module.finrank ℂ V) → ℂ := fun i j => b.repr ⟨g₀ i, hmem i⟩ j
  have hg : ∀ i z, g₀ i z = ∑ j, a i j * (b j : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z := by
    intro i z
    have := congrArg (fun v : V => (v : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z) (b.sum_repr ⟨g₀ i, hmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨Module.finrank ℂ V, fun j => ∑ i, a i j • f₁ i, fun j => (b j : _), fun j => ?_, ?_, ?_⟩
  · exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg₀ i)) (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · rw [hΦ']
    funext x
    simp only [Finset.sum_apply, pureA, hg, Finset.mul_sum, Finset.sum_mul, SchwartzMap.sum_apply,
      SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (t : ℝ) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.heisLine ψ u t (pureA F f g) x = gam (M.co.e u) f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  unfold Model.heisLine Darboux.rho
  rw [map_smul, schr_pureA ψ hψ]

theorem hasDerivAt_heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (pureA F f g) x)
      (dgam (M.co.e u) f (fun i => evI F (x i)) * g (fun i => (x i).2)) 0 := by
  simp only [heisLine_pureA M ψ hψ]
  exact (gam_differentiableAt _ _ _).hasDerivAt.mul_const _

theorem hasDerivAt_heisLine_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (g : Fin m → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x)
      (∑ k, dgam (M.co.e u) (f k) (fun i => evI F (x i)) * g k (fun i => (x i).2)) 0 := by
  have e : (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x) =
      fun t => ∑ k, M.heisLine ψ u t (pureA F (f k) (g k)) x := by
    funext t
    simp only [Model.heisLine, Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_heisLine_pureA M ψ hψ u (f k) (g k) x

end GlobalTheory.VacFactor

open GlobalTheory.VacFactor in

theorem GlobalTheory.VacFactor.mem_span_of_isGaussEq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hψ Φ hΦ hG
  obtain ⟨m, f, g, hg, hgi, rfl⟩ := exists_indep hΦ
  obtain ⟨ε, hε⟩ := hG
  let mk : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) →
      (Fin n × Fin d → AF F) :=
    fun y z i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)
  have hmk1 : ∀ y z, (fun i => evI F (mk y z i)) = y := fun y z => by
    funext i
    simp [mk, evI]
  have hmk2 : ∀ y z, (fun i => (mk y z i).2) = z := fun y z => rfl
  have key : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
      ∀ k y, dgam (M.co.e u') (f k) y = Complex.I * dgam (M.co.e u) (f k) y := by
    intro u u' hu hu' hr k y
    have h0 : ∑ k, (dgam (M.co.e u') (f k) y - Complex.I * dgam (M.co.e u) (f k) y) • g k = 0 := by
      funext z
      have e := hε u u' hu hu' hr (mk y z)
      rw [(hasDerivAt_heisLine_sum M ψ hψ u' f g (mk y z)).deriv,
        (hasDerivAt_heisLine_sum M ψ hψ u f g (mk y z)).deriv, hmk1, hmk2] at e
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [e, Finset.mul_sum]
      simp only [mul_assoc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hgi _ h0 k)
  have hgne : ∀ k, ∃ z, g k z ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hgi.ne_zero k (funext h)
  have gauss : ∀ k, M.IsGauss ψ τ (f k) := by
    intro k
    obtain ⟨z₀, hz₀⟩ := hgne k
    refine ⟨ε, fun u u' hu hu' hr f₁ f₁' h1 h1' => ?_⟩
    have hR : Rest (evI F) (⇑(f k)) (fun x : Fin n × Fin d → AF F => g k (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f k, g k, hg k, rfl⟩⟩
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h0 : evI F (show AF F from ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))) = 0 := by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _
        have := congrArg (fun v : Fin n × Fin d → AF F => (v i).2) (hz _ h0)
        change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at this
        simpa using this
      have hxz : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [hz2, add_zero]
      exact congrArg (g k) hxz
    have hD : ∀ (v : Matrix (Fin n) (Fin d) (AE F E)) (f₂ : SInf F (Fin n × Fin d)),
        ActsD (evI F) (M.heisLine ψ v) (⇑(f k)) (⇑f₂) → ∀ y, f₂ y = dgam (M.co.e v) (f k) y := by
      intro v f₂ h y
      have a := h _ hR (mk y z₀)
      have b := hasDerivAt_heisLine_pureA M ψ hψ v (f k) (g k) (mk y z₀)
      have := a.unique b
      simp only [tens, hmk1, hmk2] at this
      exact mul_right_cancel₀ hz₀ this
    refine DFunLike.ext _ _ fun y => ?_
    rw [hD u' f₁' h1' y, key u u' hu hu' hr k y, ← hD u f₁ h1 y]
    simp
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, g k, ?_, hg k, rfl⟩
  exact Submodule.mem_sInf.mpr fun N hN => hN.1 _ (gauss k)

end
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gaussianVacuaSpan_of_vacuumEquations : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  first | exact @GlobalTheory.VacFactor.mem_span_of_isGaussEq | exact GlobalTheory.VacFactor.mem_span_of_isGaussEq | (intros; apply GlobalTheory.VacFactor.mem_span_of_isGaussEq <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

noncomputable section

namespace GlobalTheory.SquareAgree

theorem pureA_mem_algD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hM f hf g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have h1 : GlobalTheory.WeilM.pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g =
      ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [GlobalTheory.WeilM.pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, φ k, hf, hφSB k, hφvac k, rfl⟩)

end GlobalTheory.SquareAgree

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  atlas_forward_decl GlobalTheory.SquareAgree.pureA_mem_algD
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.VacDatum

theorem vacDatum_exists : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f hf
  obtain ⟨ξ, JB, co, hJB, hrat, hiff⟩ :=
    GlobalTheory.T.exists_rational_darboux_orientedPair_transport D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hψ ▸ hBs.std)
  obtain ⟨-, -, hon⟩ := GlobalTheory.ThetaTransform.thetaTr_bij (S := sgn ε S) (T := X) co hstd rfl hJB hrat
  obtain ⟨Φ, hΦ, hΦf⟩ := (hon f).1 hf.1
  have hD : IsDatum M ψ cS Φ f := (hiff Φ f).2 ⟨hΦ, hΦf⟩
  have hG := GlobalTheory.T.fockVacuumEquations_transfer_schroedingerDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  have hsp := GlobalTheory.T.mem_gaussianVacuaSpan_of_vacuumEquations M Bs.ψ Bs.emb hBs.std Φ hΦ hG
  refine ⟨Φ, Submodule.span_le.2 ?_ hsp, hD⟩
  rintro _ ⟨g, h, hg, hh, rfl⟩
  exact GlobalTheory.T.fockPolynomial_tmul_schwartzBruhat_mem_algebraicData M Bs.ψ Bs.emb hM g hg h hh

end GlobalTheory.VacDatum

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  atlas_forward_decl GlobalTheory.VacDatum.vacDatum_exists
end
