import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleIntegralVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransfer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralsAgreeOfIntegrableKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFiniteDataMatchEachStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTriangleTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageSmallNonzeroBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageNonzeroAtFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelFundamentalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageSmallNonzeroBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageKernelIntegrablePolynomialBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageKernelIntegrablePolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomialStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralKernelLieAlgebraStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleIntegralVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangleStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StageConv
theorem theta_stage_converges : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t P h, MeasureTheory.IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m := by
  intro hP _ _
  have hW := _root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hRec T Lc μ₀ _ G => ?_⟩⟩
  intro W S _ _ i j p q A A' WW X hX t P h
  obtain ⟨hp, hq, hA, hA', hnA, _, _, hXi⟩ := hX
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hrank : WW.rank < 2 * (A.rank - p) := rank_lt (m_le_of_size hRec.size) hp hq hA hA' hXi.rank
  have hf :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hXi.fst t) (GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hXi.isVac)
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) W.ψ_std W.θ_is (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B hf P
  obtain ⟨N, C', hint⟩ := hW D W.ψ W.θ W.θ_is true A WW _ _ (X.ω t) (hXi.weil t) p ⟨τ, hnA τ⟩ hrank X.m X.fd hXi.meas _ hΦ
  exact (hint h).1
end GlobalTheory.StageConv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_stage_convergent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t P h, MeasureTheory.IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m := by
  first | exact @_root_.GlobalTheory.StageConv.theta_stage_converges | exact _root_.GlobalTheory.StageConv.theta_stage_converges | (intros; apply _root_.GlobalTheory.StageConv.theta_stage_converges <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct
theorem GlobalTheory.StageLift.theta_stage_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  intro hP hK hL
  have hM := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hL
  have hWe := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hL
  have hAg := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_tripleConditions (_root_.GlobalTheory.T.theta_finiteData_match_each_stage hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL' G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h3⟩ := h C hC D large₂ a b r T Lc μ hL' G
  obtain ⟨FA, FA', FW, ea, eb, hd⟩ := h1 W i j p q A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, qm, qm', hq, hq', hLM⟩ := hM D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨g, hg⟩ := qm.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have key : ∀ t, ∃ l : ℂ, l ≠ 0 ∧ ∀ P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      X.I W.ψ W.θ t (g (qm' P')) = l • X.I' W.ψ W.θ t P' := by
    intro t
    obtain ⟨hT, hE, hf, hf', hk, hk'⟩ := hd t
    obtain ⟨hex, hall⟩ := hLM _ _ hT hE
    obtain ⟨Pim, rf, rl, pm, pm', hm⟩ := hWe D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT hex (X.ω t) (X.ω' t)
      (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hall _ _ _ _ _ _ _ hm
    obtain ⟨κ, hκ, hrk⟩ := h3 W i j p q A A' WW X hX FA FA' FW t hf hf' Pim rf rl pm pm' hm Pr Pf qm qm' r r' e hq hq' hr hr'
    obtain ⟨c, hc0, hcI⟩ := hAg D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hT X.m X.fd X.m' X.fd' hIs.meas hIs.meas' _ _ _ _ _ _ _ hm
    refine ⟨c * κ, mul_ne_zero hc0 hκ, fun P' hP' => ?_⟩
    have hΦ : GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P')) ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW :=
      Submodule.subset_span ⟨X.f t, g (qm' P'), hf, rfl⟩
    have hΦ0 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      Submodule.subset_span ⟨X.f' t, P', hf', rfl⟩
    have hΦ' := Submodule.smul_mem _ κ hΦ0
    have hsm : ∀ x h, thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') =
        κ * X.ker' W.ψ W.θ t P' h x := by
      intro x h
      rw [← hk' P' x h]
      simp [thetaKO, map_smul]
    have hint : ∀ h, MeasureTheory.IntegrableOn
        (fun x => thetaKO (X.ω' t) x h (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P')) X.fd' X.m' := by
      intro h
      simp_rw [hsm]
      exact (hP' h).const_mul κ
    have hqg : qm (g (qm' P')) = qm' P' := LinearMap.congr_fun hg _
    have hp : pm (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) (g (qm' P'))) =
        pm' (κ • GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
      rw [hr _ hf, map_smul, hr' _ hf', hqg, hrk, TensorProduct.tmul_smul, map_smul]
    have h1 := hcI _ hΦ _ hΦ' hint hp
    funext h
    have h2 := congrFun h1 h
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Tri.I, Tri.I', Pi.smul_apply, smul_eq_mul]
    simp_rw [← hk]
    rw [h2]
    simp_rw [hsm]
    rw [MeasureTheory.integral_const_mul]
    ring
  choose lam hlam using key
  exact ⟨lam, g ∘ₗ qm', fun t => (hlam t).1, fun t P' hP' => (hlam t).2 P' hP'⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_liftable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank), (∀ t, lam t ≠ 0) ∧
        ∀ t P', (∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') → X.I W.ψ W.θ t (s P') = lam t • X.I' W.ψ W.θ t P' := by
  first | exact @_root_.GlobalTheory.StageLift.theta_stage_lift_exists | exact _root_.GlobalTheory.StageLift.theta_stage_lift_exists | (intros; apply _root_.GlobalTheory.StageLift.theta_stage_lift_exists <;> assumption)
end
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology MeasureTheory
open GlobalTheory.WeilM
noncomputable section
namespace GlobalTheory.SoPureThetaCont
theorem continuous_pure_theta_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT hD φ hSB hev hSo h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  let A : (Fin a' × Fin (a + a') → Af F) → ℂ := fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a' × Fin (a + a') → Af F) := GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB hstd
  have heq : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ = pureA F u A := fun _ => rfl
  have hso : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ G.M'.So B.ψ B.τ₁ := fun u =>
    Submodule.subset_span ⟨u, φ, hSB, hev, hSo, rfl⟩
  have hsch : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ schA F _ := fun u =>
    GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F _ := fun x Φ hΦ =>
    hPair.weil.isUSplitting.pres x Φ hΦ
  have hconv : ∀ u : SInf F (Fin a' × Fin (a + a')), IntegrableOn (fun g => theta om' (pure u φ) g h) G.M'.dom G.M'.μ :=
    fun u => (hD.2 _ (hso u)).2.1 h
  have hadd : ∀ (u u' : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (u + u') φ) g h = theta om' (pure u φ) g h + theta om' (pure u' φ) g h := by
    intro u u' g
    have e : pure (u + u') φ = pure u φ + pure u' φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    simp only [theta, e, map_add]
    exact thetaSum_add F (hpres _ _ (hsch u)) (hpres _ _ (hsch u'))
  have hsmul : ∀ (c : ℂ) (u : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (c • u) φ) g h = c * theta om' (pure u φ) g h := by
    intro c u g
    have e : pure (c • u) φ = c • pure u φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    simp only [theta, e, map_smul]
    exact thetaSum_smul F c _
  have hcontg : ∀ g, Continuous fun u : SInf F (Fin a' × Fin (a + a')) => theta om' (pure u φ) g h := fun g =>
    (_root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair).2 A hA g h
  let μd := G.M'.μ.restrict G.M'.dom
  let T : SInf F (Fin a' × Fin (a + a')) → UA σ G.V'.J → ℂ := fun u g => theta om' (pure u φ) g h
  have hfin : ∀ u, (∫⁻ g, ‖T u g‖ₑ ∂μd) ≠ ⊤ := fun u => (hconv u).2.ne
  have hν : ∀ u, ∫ g, ‖T u g‖ ∂μd = (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := fun u =>
    integral_norm_eq_lintegral_enorm (hconv u).1
  let ν : Seminorm ℂ (SInf F (Fin a' × Fin (a + a'))) :=
    Seminorm.of (fun u => ∫ g, ‖T u g‖ ∂μd)
      (fun u u' => by
        calc ∫ g, ‖T (u + u') g‖ ∂μd ≤ ∫ g, (‖T u g‖ + ‖T u' g‖) ∂μd :=
              integral_mono (hconv (u + u')).norm ((hconv u).norm.add (hconv u').norm)
                fun g => by simp only [T]; rw [hadd]; exact norm_add_le _ _
          _ = _ := integral_add (hconv u).norm (hconv u').norm)
      (fun c u => by
        simp only [T, hsmul, norm_mul]
        exact integral_const_mul _ _)
  haveI : BarrelledSpace ℂ (SInf F (Fin a' × Fin (a + a'))) := by
    classical exact GlobalTheory.schwartzMap_barrelledSpace _
  have hN : LowerSemicontinuous fun u => ∫⁻ g, ‖T u g‖ₑ ∂μd := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro u
    calc ∫⁻ g, ‖T u g‖ₑ ∂μd ≤ ∫⁻ g, liminf (fun u' => ‖T u' g‖ₑ) (𝓝 u) ∂μd :=
          lintegral_mono fun g => (((hcontg g).tendsto u).enorm.liminf_eq).ge
      _ ≤ _ := lintegral_liminf_le' fun u' => (hconv u').1.enorm
  have hνc : Continuous ν := by
    refine Seminorm.continuous_of_lowerSemicontinuous ν fun u y hy => ?_
    by_cases hy0 : y < 0
    · exact Filter.Eventually.of_forall fun u' => hy0.trans_le (apply_nonneg ν u')
    · push_neg at hy0
      have hy' : y < (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := by rw [← hν]; exact hy
      have h1 : ENNReal.ofReal y < ∫⁻ g, ‖T u g‖ₑ ∂μd := (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy'
      filter_upwards [hN u _ h1] with u' hu'
      show y < ∫ g, ‖T u' g‖ ∂μd
      rw [hν]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hu'
  let L : SInf F (Fin a' × Fin (a + a')) →+ ℂ :=
    { toFun := fun u => G.M'.I om' (pure u φ) h
      map_zero' := by
        show ∫ g, T 0 g ∂μd = 0
        have : ∀ g, T 0 g = 0 := fun g => by
          simpa using hsmul 0 0 g
        simp [this]
      map_add' := fun u u' => by
        show ∫ g, T (u + u') g ∂μd = ∫ g, T u g ∂μd + ∫ g, T u' g ∂μd
        simp only [T, hadd]
        exact integral_add (hconv u) (hconv u') }
  have hLb : ∀ u, ‖L u‖ ≤ ν u := fun u => norm_integral_le_integral_norm _
  have hL : Continuous L := by
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun u => norm_nonneg _) hLb ?_
    simpa using hνc.tendsto (0 : SInf F (Fin a' × Fin (a + a')))
  exact hL
end GlobalTheory.SoPureThetaCont
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @_root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | exact _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | (intros; apply _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.DefThetaNZ
section Darboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_algebraic_vector_definite_theta_ne (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (hDec : Decay B G om om')
    {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hne : G.M'.I om' Φ' ≠ 0) :
    ∃ ΦD ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, G.M'.I om' ΦD ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  clear hne
  funext h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), om' x Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) :=
    hPair.weil.isUSplitting.pres
  have hdense := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ hPair
  have hsch : ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, Ψ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) := by
    intro Ψ hΨ
    refine (Submodule.span_le.2 ?_) hΨ
    rintro _ ⟨f, φ, hSB, hvac, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
    filter_upwards [hvac, hT.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  show G.M'.I om' Φ' h = 0
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    have hc := _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal hP F E σ B a a' G X om om' hT hDec φ hSB hvac hv₁ h
    have hz : ∀ P ∈ (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))), G.M'.I om' (pure P φ) h = 0 := fun P hP' =>
      congrFun (hall _ (Submodule.subset_span ⟨P, φ, hP', hSB, hvac, rfl⟩)) h
    have hcl : IsClosed {f : SInf F (Fin a' × Fin (a + a')) | G.M'.I om' (pure f φ) h = 0} := isClosed_eq hc continuous_const
    have hsub := hcl.closure_subset_iff.2 hz
    rw [hdense.closure_eq] at hsub
    exact hsub (Set.mem_univ f)
  | zero => exact I_zero _ _ h
  | add x y hx hy ihx ihy =>
    rw [I_add' G.M' om' ((hDec.2 x hx).2.1 h) ((hDec.2 y hy).2.1 h) (fun g => ⟨hpres _ _ (hsch x hx), hpres _ _ (hsch y hy)⟩),
      ihx, ihy, add_zero]
  | smul c x hx ihx => rw [I_smul', ihx, mul_zero]
end Darboux
end GlobalTheory.DefThetaNZ
namespace GlobalTheory.DefThetaNZ
open scoped Matrix
theorem exists_algebraic_function_definite_theta_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  intro hP hK hL D ψ θ _hψ hθ W W₁ X A A₁ B α β hT _hdef ν₁ 𝓕₁ hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨⟨Φ', hΦ'So, hne⟩, -⟩, -⟩ := hK' R Rf hR
  obtain ⟨ΦD, hΦD, hneD⟩ := _root_.GlobalTheory.DefThetaNZ.exists_algebraic_vector_definite_theta_ne hP hTD hDec hΦ'So hne
  obtain ⟨Φ, hΦ, hDat⟩ := hO.algB' ΦD hΦD
  refine ⟨Φ, hΦ, fun h0 => ?_⟩
  obtain ⟨h', hh'⟩ := Function.ne_iff.1 hneD
  obtain ⟨h, rfl⟩ := GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective D X e hO.JX h'
  have := GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) ΦD Φ
    hO.measW₁ hO.domW₁ (hO.theta_eq_B hDat) h
  rw [h0] at this
  exact hh' this.symm
end GlobalTheory.DefThetaNZ
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  first | exact @_root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero | exact _root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero | (intros; apply _root_.GlobalTheory.DefThetaNZ.exists_algebraic_function_definite_theta_ne_zero <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.DefiniteSmallIrred
theorem definite_small_irreducible_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Ψ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
  GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X (fun h => ωB (1, h)) τ Y Ψ Φ' → ∀ h : GA D X,
  HasDerivAt (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) (GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' h) 0 := by
  intro hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨ Φ' hΦ' hder h
  have hw : IsWeilDatumO ψ W₁ X α (α / β) ωB := (GlobalTheory.Grid.isWeil_false ψ W₁ X α (α / β) ωB).1 hm.weilB
  have hthA : ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, IsThetaFunO ψ W₁ X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hth : IsThetaFunO ψ W₁ X Ψ := hthA Ψ hΨ
  have hpos : ∀ τ, (gramAt D W₁ τ).PosDef := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs₁ τ)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ W₁ X α (α / β) ωB hw θ hθ τ Y hY
  have hGΨ : ∀ (g : GA D W₁) (k : GA D X),
      HasDerivAt (fun t : ℝ => thetaKO ωB g (k * oneP θ X τ Y t) Ψ) (thetaKO ωB g k Φ') 0 := by
    have hG : Gn Ψ = Φ' := by
      funext z
      have h1 := (hGn Ψ hth).2.2.2 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at h1
      exact h1.unique (hder z)
    intro g k
    have h1 := (hGn Ψ hth).2.2.2 (g, k) 0
    simp only [Prod.mk_mul_mk, mul_one, hG] at h1
    exact h1
  let L : ℂ →ₗ[ℂ] (WO W₁ X → ℂ) := LinearMap.toSpanSingleton ℂ _ Ψ
  have hL : ∀ x, IsThetaFunO ψ W₁ X (L x) := fun x => GlobalTheory.OrientedHeis.theta_smul x hth
  have hL1 : L 1 = Ψ := by simp [L]
  obtain ⟨-, hD⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ W₁ X α (α / β) ωB hw θ hθ hpos ℂ L hL
    (fun _ => 1) continuous_const (fun _ _ _ => rfl) ν₁ 𝓕₁ hν₁.1 hν₁.2
  obtain ⟨L', -, hk, hlift⟩ := hD τ Y hY
  have hkid : ∀ g k, thetaKO ωB g k (L' 1) = thetaKO ωB g k Φ' := by
    intro g k
    have h1 := hk 1 g k
    rw [hL1] at h1
    exact h1.unique (hGΨ g k)
  have h2 := hlift h
  simp only [GlobalTheory.DefLift.lift, hL1, hkid] at h2
  exact h2
theorem theta_vanish_all_of_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  intro hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
  have hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hTK hLM
  set S := GlobalTheory.SquareComm.algF ψ θ false A₁ B with hSdef
  have hint := GlobalTheory.DefIrred.integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁
  have tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ := by
    intro Φ g h k
    show (ωB (g, h) * ωB (1, k)) Φ 0 = _
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rfl
  have tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ - GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_sub]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.sub_apply]
    rw [e]
    exact integral_sub (hΦ h) (hΨ h)
  have tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ + GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hΦ h) (hΨ h)
  have tsmul : ∀ (c : ℂ) Φ, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ := by
    intro c Φ; funext h
    have e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul c _
  let Kint : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b := by
            funext g; simp [thetaKO, map_add]
          rw [e]; exact (ha.1 h).add (hb.1 h),
        by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]⟩
      smul_mem' := fun c a ha => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a := by
            funext g; simp [thetaKO, map_smul]
          rw [e]; exact (ha.1 h).const_mul c,
        by rw [tsmul, ha.2, smul_zero]⟩ }
  let K : Submodule ℂ (WO W₁ X → ℂ) := S ⊓ Kint
  obtain ⟨c, hc0, hc⟩ := hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁
  have kerp' : GlobalTheory.SquareComm.finRel ωB S ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [map_sub, hm.mapB.invf u hu Ψ hΨ]
  have kill : ∀ Ψ ∈ S, p' Ψ = 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
    intro Ψ hΨ hp0
    obtain ⟨Φ₀, hΦ₀, hd, -, hI⟩ := hc Ψ hΨ
    have hp00 : p' Φ₀ = 0 := by
      have := kerp' hd
      rw [LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero] at this
      exact this
    have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp00])
    have h2 : GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 0 = 0 := by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]
    rw [h2] at h1
    have h3 : GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0 := (smul_eq_zero.1 h1.symm).resolve_left hc0
    have h4 := hrel _ hd
    rw [tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero] at h4
    exact h4
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p' := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    refine ⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩
    · simp only [tr]; exact hΨi (h * g)
    · funext h
      simp only [GlobalTheory.SquareComm.thetaInt, tr]
      exact congrFun hΨ0 (h * g)
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p' := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    obtain ⟨Φ', hΦ'S, hder⟩ := hm.mapB.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Φ', ⟨hΦ'S, hint Φ' hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩
    funext h
    have hd := _root_.GlobalTheory.DefiniteSmallIrred.definite_small_irreducible_lie_derivative hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨS Φ' hΦ'S hder h
    have e0 : (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) = fun _ => (0 : ℂ) := by
      funext t; rw [hΨ0]; rfl
    rw [e0] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  rcases hm.irred.2 (K.map p') stf stl with hbot | htop
  · exfalso
    have : p' Φ₁ ∈ K.map p' := ⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hp₁ this
  · have : p' Φ₂ ∈ K.map p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩ := this
    have h0 := kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])
    rw [tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero] at h0
    exact h0
end GlobalTheory.DefiniteSmallIrred
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_of_definite_small_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  first | exact @_root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | exact _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | (intros; apply _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallNz
theorem smallStage_thetaIntegral_of_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p A A' WW X hX hint => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, hsA', -, hD⟩ := hd W i j p 0 A A' WW X hX
  have hdef : ∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0 := fun τ => by simpa using hsA' τ
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
      (pm : (WO A WW → ℂ) →ₗ[ℂ] Pi) (pm' : (WO A' WW → ℂ) →ₗ[ℂ] Pi),
      GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl pm pm' ∧ Nontrivial Pr ∧
      ∀ P', q' P' ≠ 0 → pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p 0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    refine ⟨Pm, rf, rl, pm, pm', hm, nontrivial_left e, fun P' hP' => ?_⟩
    rw [hr' _ hf']
    exact e.map_ne_zero_iff.2 (tmul_ne_zero hP' hy)
  by_cases hT : Nonempty T
  · obtain ⟨t0⟩ := hT
    haveI : Nontrivial Pr := (key t0).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P0, rfl⟩ := hq' x
    refine ⟨P0, fun t h0 => ?_⟩
    obtain ⟨hTr, -, -, hf', -, hk'⟩ := hD t
    obtain ⟨Pm, rf, rl, pm, pm', hm, -, hne⟩ := key t
    have memF : ∀ P', GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    obtain ⟨Φ, hΦ, hΦ0⟩ := _root_.GlobalTheory.T.definite_theta_lift_ne_zero hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m' X.fd' hIs.meas'
      _ _ _ _ _ _ _ hm
    exact hΦ0 (_root_.GlobalTheory.T.vanishing_of_definite_small_irreducible hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m X.fd X.m' X.fd' hIs.meas hIs.meas'
      _ _ _ _ _ _ _ hm _ (memF P0) (hne P0 hx) (by rw [eI']; exact h0) Φ hΦ)
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
end GlobalTheory.StageSmallNz
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_nonzero_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero | exact _root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero | (intros; apply _root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero <;> assumption)
end
end

section
section
noncomputable section
namespace GlobalTheory.GoodFock
section Ring
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset
variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}
end Ring
section Poly
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
end Poly
section Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
end Theta
section Quot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {M X : HSp D}
end Quot
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem exists_admissible_fock_polynomial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]
end Main
end GlobalTheory.GoodFock
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @_root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | exact _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | (intros; apply _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial <;> assumption)
end
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace GlobalTheory.ThetaIntegralLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
theorem thetaIntegral_line_hasDerivAt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (χY χW : Chr F E) (om : Rep σ Y W)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hw : M.IsWeil ψ χY χW om) (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hcont : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Φ₁ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ h, HasDerivAt (fun t : ℝ => M.I om Φ (h * γ (Multiplicative.ofAdd t))) (M.I om Φ₁ h) 0 := by
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, fun h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · have e : ∀ h', M.I om 0 h' = 0 := fun h' => by simpa using I_smul M om 0 0 h'
      simpa [e] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add Φ Ψ hΦ hΨ ihΦ ihΨ =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ihΦ
    obtain ⟨Ψ₁, m₂, p₂, q₂⟩ := ihΨ
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m₁ m₂, fun x => ?_, fun h => ?_⟩
    · simpa only [map_add, Pi.add_apply] using (p₁ x).fun_add (p₂ x)
    · simpa only [I_add M om hpres hconv hΦ hΨ, I_add M om hpres hconv m₁ m₂] using (q₁ h).fun_add (q₂ h)
  | smul c Φ hΦ ih =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ih
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m₁, fun x => ?_, fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (p₁ x).const_mul c
    · simpa only [I_smul] using (q₁ h).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hφ, rfl⟩ := hΦ
    obtain ⟨c, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) :=
      fun u => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
      refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f⟩
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at z hz i, add_zero]
    have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pureA F f φ) = pureA F (c t) φ := fun t => hacts t _ hR
    refine ⟨pureA F c' φ, hmem c', fun x => ?_, fun h => ?_⟩
    · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
        (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * φ fun i => (x i).2)
          (c' (fun j => evI F (x j)) * φ fun i => (x i).2) 0 := by
        rw [hasDerivAt_iff_tendsto_slope]
        refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [slope_def_module, h0]
        simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
        ring
      simp only [hc]
      exact h2
    · let L : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
        { toFun := fun u => M.I om (pureA F u φ) h
          map_add' := fun u u' => by
            have e : pureA F ⇑(u + u') φ = pureA F u φ + pureA F u' φ := by
              funext x; simp [pureA, add_mul]
            rw [e, I_add M om hpres hconv (hmem u) (hmem u')]
          map_smul' := fun s u => by
            have e : pureA F ⇑(s • u) φ = (s : ℂ) • pureA F u φ := by
              funext x; simp [pureA, mul_assoc, Complex.real_smul]
            rw [e, I_smul, RingHom.id_apply, Complex.real_smul] }
      have hL : Continuous L := hcont φ hφ h
      have hcurve : (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) = fun t => L (c t) := by
        funext t
        rw [← I_om_one, hc]
        rfl
      rw [hcurve, hasDerivAt_iff_tendsto_slope]
      refine ((hL.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, map_smul, map_sub]
end GlobalTheory.ThetaIntegralLine
end
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
noncomputable section
namespace GlobalTheory.ConvThetaNe
open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section Over
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
theorem hasDerivAt_large_parameter_theta_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om')
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hY : Y ∈ lieAt X τ) {Φ Φ' : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (hΦ' : Φ' ∈ algF ψ θ true A B)
    (hd : IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ') (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ωA ν 𝓕 Φ (h * oneP θ X τ Y t)) (thetaInt ωA ν 𝓕 Φ' h) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
  obtain ⟨Φ'D, -, hD'⟩ := hO.algA Φ' hΦ'
  have hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M := by
    refine Submodule.span_mono ?_ hΦD
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, h1, φ, h2, h3, rfl⟩
  obtain ⟨T, m, f, φ, hf, rfl⟩ := GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD
  have e1 := _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ
    hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC
  obtain ⟨Φ₁, -, hp, hI⟩ := _root_.GlobalTheory.ThetaIntegralLine.thetaIntegral_line_hasDerivAt hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC
    (fun g hg x => by
      obtain ⟨L, hL⟩ := hT.weil.isUSplitting.adm (1, x) l hla g hg
      refine L.continuous.congr fun u => ?_
      rw [GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]
      rfl) hγ hD.1
  have hM := hT.geo.hM
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]
      exact (GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩
  have e2 : Φ₁ = Φ'D := by
    funext x
    refine (hp x).unique ?_
    rw [e1]
    simp only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x
  have := hI (kapX X e hO.JX h)
  rw [e2] at this
  simp only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]
  exact this
end Over
theorem convergent_theta_integral_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ algF ψ θ false A₁ B, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' ≠ 0 := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB
  have hC := (hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  set S := algF ψ θ true A B with hS
  have hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := fun Φ hΦ h => integrable_big hO hC hΦ h
  have tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k) := by
    intro Φ h k
    simp only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ := by
    intro Φ hΦ Ψ hΨ; funext h
    have e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hint Φ hΦ h) (hint Ψ hΨ h)
  have tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ := by
    intro s Φ; funext h
    have e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul s _
  let K : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha.2, smul_zero]⟩ }
  have kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0 := fun Ψ hΨ h0 => by
    rw [hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]
    funext h; simp [thetaInt, thetaKO]
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    refine ⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩
    funext h
    rw [tr, hΨ0]
    rfl
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    obtain ⟨Ψ', hΨ'S, hder⟩ := hm.mapA.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩
    have h1 := _root_.GlobalTheory.ConvThetaNe.hasDerivAt_large_parameter_theta_integral hP hθ hO hTD hC hY hΨS hΨ'S hder h
    rw [hΨ0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases hm.irred.2 (K.map p) stf stl with hbot | htop
  · obtain ⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p := hm.mapA.onto ▸ Submodule.mem_top
    have h1 : p Φ ∈ K.map p := ⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, hpΦ] at h1
    exact hp' h1
  · obtain ⟨Φ, hΦ, hne⟩ := exists_big_ne hK hL hO hTD
    obtain ⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p := by rw [htop]; exact Submodule.mem_top
    have h1 := tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS
    rw [sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero] at h1
    exact hne h1
end GlobalTheory.ConvThetaNe
end
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallBig
theorem smallStage_thetaIntegral_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q0 A A' WW X hX _ => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, -, -, hD⟩ := hd W i j p q0 A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨P0, hP0⟩ := _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, (∀ h, IntegrableOn (X.ker' W.ψ W.θ t P0 h) X.fd' X.m') ∧ X.I' W.ψ W.θ t P0 ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, hk'⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p q0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    haveI : Nontrivial Pr := nontrivial_left e
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P1, rfl⟩ := hq' x
    obtain ⟨hint, hker⟩ := hP0 _ _ hTr hInf _ _ _ _ _ _ _ hm _ hf'
    have hint' := hint X.m' X.fd' hIs.meas'
    have hne : pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) ≠ 0 := fun h0 => by
      have h1 := hker h0 P1
      rw [hr' _ hf'] at h1
      exact e.map_ne_zero_iff.2 (tmul_ne_zero hx hy) h1
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 := hint' h
      simp only [hk'] at h1
      exact h1
    · rw [← eI']
      exact _root_.GlobalTheory.ConvThetaNe.convergent_theta_integral_ne_zero hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hTr X.m' X.fd' hIs.meas'
        _ _ _ _ _ _ _ hm _ (Submodule.subset_span ⟨_, P0, hf', rfl⟩) hint' hne
  exact ⟨P0, fun t => (key t).1, fun t => (key t).2⟩
end GlobalTheory.StageSmallBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | exact _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | (intros; apply _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageSmall
theorem theta_stage_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.smallStage_thetaIntegral_nonzero_case hP hK hL) (_root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h2⟩ := h C hC D large₂ a b r T Lc μ hL G
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hi := GlobalTheory.T.integrableOn_thetaKernel_definiteSeesawStage G W i j p A A' WW X hX
    obtain ⟨P', hP'⟩ := h1 W S hW hN i j p A A' WW X hX hi
    exact ⟨P', fun t h => hi t P' h, hP'⟩
  · exact h2 W S hW hN i j p q A A' WW X hX hq
end GlobalTheory.StageSmall
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_small_rank_stage_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmall.theta_stage_of_small_rank | exact _root_.GlobalTheory.StageSmall.theta_stage_of_small_rank | (intros; apply _root_.GlobalTheory.StageSmall.theta_stage_of_small_rank <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageKer
end GlobalTheory.StageKer
theorem GlobalTheory.StageKer.theta_stage_kernel_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_thetaDictionary_exists (_root_.GlobalTheory.T.theta_stage_liftable hP hK hL)) (_root_.GlobalTheory.T.theta_small_rank_stage_holds hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h3⟩, h4⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, hD⟩ := h1 W S hW hN i j p q A A' WW X hX
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  obtain ⟨P0, hc0, hne0⟩ := h4 W S hW hN i j p q A A' WW X hX
  obtain ⟨Pr, qP, hq⟩ := _root_.GlobalTheory.T.thetaIntegral_factors_through_kType hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have hIs := hX.2.2.2.2.2.2.2
  have key : ∀ t P, X.I W.ψ W.θ t P = 0 ↔ qP P = 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, -, hk, -⟩ := hD t
    obtain ⟨Pf, y, J, hJ, hI⟩ := hq _ _ hTr hInf X.m X.fd hIs.meas (X.ω t) (hIs.weil t) (X.f t) hf
    have eI : ∀ P, X.I W.ψ W.θ t P = J (qP P ⊗ₜ y) := fun P => by
      rw [← hI P]; funext h; simp only [GlobalTheory.SquareComm.thetaInt, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, hk]
    have hne : X.I W.ψ W.θ t (s P0) ≠ 0 := by
      rw [hs t P0 (hc0 t)]; exact smul_ne_zero (hlam t) (hne0 t)
    have hy : y ≠ 0 := by
      rintro rfl; apply hne; rw [eI, TensorProduct.tmul_zero, map_zero]
    have hJi : Function.Injective J := hJ.resolve_left (by
      intro hJ0; apply hne; rw [eI, hJ0]; rfl)
    intro P
    rw [eI, map_eq_zero_iff J hJi]
    constructor
    · intro h0; by_contra hq0; exact GlobalTheory.StageKer.tmul_ne_zero_of_ne hq0 hy h0
    · intro h0; rw [h0, TensorProduct.zero_tmul]
  intro t t' P h0
  exact (key t' P).2 ((key t P).1 h0)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_kernel_characterization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  first | exact @_root_.GlobalTheory.StageKer.theta_stage_kernel_eq | exact _root_.GlobalTheory.StageKer.theta_stage_kernel_eq | (intros; apply _root_.GlobalTheory.StageKer.theta_stage_kernel_eq <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageFactor
open MeasureTheory
variable {D : D7} {T : Type} {A A' WW : HSp D}
end GlobalTheory.StageFactor
open GlobalTheory.StageFactor
theorem GlobalTheory.StageFactor.theta_tower_stage_norm_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.theta_integral_stage_convergent hP hK hL) (_root_.GlobalTheory.T.theta_stage_kernel_characterization hP hK hL))
    (GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.theta_stage_liftable hP hK hL) (_root_.GlobalTheory.T.theta_small_rank_stage_holds hP hK hL))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h C hC D large₂ a b r T Lc μ hL G
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  exact ⟨lam, factor_of_parts X W.ψ W.θ (h1 W S hW hN i j p q A A' WW X hX) (h2 W S hW hN i j p q A A' WW X hX) lam s hlam hs
    (h4 W S hW hN i j p q A A' WW X hX)⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_of_isStageC : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  first | exact @_root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization | exact _root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization | (intros; apply _root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization <;> assumption)
end
end
