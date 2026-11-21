import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLiftStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelPStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseChain
theorem lastStep_integrableOn_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv F Q x g
  have hC := hP.bot.hyp.2.2.2.1
  have hω : IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' _ _ (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) :=
    weil_transport ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) (hC.chain.ωX W.P.A3.A.μ0) (j + 1) (idx_top h)
  obtain ⟨c1, hc1⟩ := hC.lev.βY (j + 1) (by omega)
  obtain ⟨c2, hc2⟩ := hC.lev.βX
  have hv' : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' v :=
    (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc1) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc2) hc1.1 hc2.1 hv
  have hf := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hC.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) hv' Q
  have hν := hC.models.νX W.P.A3.A.μ0
  have key := GlobalTheory.Hk3.StepX.integ_X hω hf (F.1 x)
    (multT_apply_continuous _ _ _ _ F.1 F.2 x) (multT_apply_left _ _ _ _ F.1 F.2 x) _ hν.1.1 _ hν.2 g 1
  simpa only [mul_one] using key
end GlobalTheory.BaseChain
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_step_vector_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  atlas_forward_decl _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
theorem stepX_isIo_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hcard : Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H ≠ 0 := by
    have hf' : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    exact Nat.card_pos.ne'
  have hcH : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
    simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality]
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · have h1 := _root_.GlobalTheory.T.top_step_vector_property_alt W hP j h _ ((hf.row W.P.A3.A.μ0).vT j h) F φ v g
    unfold IntegrableOn at h1 ⊢
    change Integrable _ ((_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0).restrict ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0))
    rw [Measure.restrict_smul]
    exact h1.smul_measure hcH
  · obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g W.P.A3.A.μ0 j h F
    obtain ⟨h'', he⟩ := (hf.row W.P.A3.A.μ0).ioT j h F
    have e1 := congrFun (hL _ ((hf.row W.P.A3.A.μ0).vT j h) φ v) g
    have key : ∀ X : ℂ, (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * X) = X := by
      intro X
      have e3 : (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal = ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℝ))⁻¹ := by
        simp [_root_.GlobalTheory.BaseChain.inverseLevelCardinality, ENNReal.toReal_inv]
      have hc : ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard
      rw [e3, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [inv_mul_cancel₀ hc, one_mul]
    change ∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, _ ∂(_root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
      ((f.row W.P.A3.A.μ0).ioT j h F).1 (f.c.ItT j h φ v) g
    rw [setIntegral_smul_measure_complex, he]
    have e2 : (∫ y in (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0, thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row W.P.A3.A.μ0).vT j h) φ) * F.1 v y ∂(_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) =
        (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) * (ioXT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h ⟨F.1, h''⟩).1 (f.c.ItT j h φ v) g := e1
    exact (congrArg (fun z : ℂ => (_root_.GlobalTheory.BaseChain.inverseLevelCardinality W).toReal • z) e2).trans (key _)
end GlobalTheory.BaseChain
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_top_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  atlas_forward_decl _root_.GlobalTheory.BaseChain.stepX_isIo_alt
end
end
