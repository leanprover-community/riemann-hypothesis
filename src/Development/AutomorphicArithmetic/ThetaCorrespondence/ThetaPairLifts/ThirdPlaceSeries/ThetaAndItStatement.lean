import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctionsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorThetaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorTheta

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopConv
variable {D : D7}
end GlobalTheory.TopConv
end
noncomputable section
namespace GlobalTheory.TopConv
set_option maxHeartbeats 1000000 in
theorem top_comb_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv
  have hLev := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hbY⟩ := hLev.βY (j + 1) (by omega)
  obtain ⟨cX', hbX⟩ := hLev.βX
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have hr : (Yc D (j + 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY n) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY n) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 n (_root_.GlobalTheory.Fam.pk_z W).triv) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m)
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (_root_.GlobalTheory.Fam.pk_z W).vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact W.Q.charW.base.chain.vX _
  have hX := key (j + 1) (idx_top h)
  obtain ⟨d₁, hd₁, e₁⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hX
  obtain ⟨d₂, hd₂, e₂⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hv
  have hv0 : v ≠ 0 := (GlobalTheory.Chain.StepVac.stepVec_vac sdY sdX hr hv).2.1
  have hspan := comb_mem_span (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₂) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)
  rw [← e₂] at hspan
  have hvac := GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hv.1 sdY sdX hspan hv0
  obtain ⟨b, hb, hbv⟩ := exists_finComb_of_mem_span _ hvac
  obtain ⟨c, hc, hcc⟩ := isFinComb_comp (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₁) hb
  refine ⟨c, hc, ?_⟩
  rw [hcc, hbv]
  exact e₁.symm
end GlobalTheory.TopConv
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
theorem _root_.GlobalTheory.T.top_step_vector_theta_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  atlas_forward_decl _root_.GlobalTheory.TopConv.top_comb_alt
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
namespace GlobalTheory.BaseChainTop
variable {D : D7}
end GlobalTheory.BaseChainTop
namespace GlobalTheory.BaseChainTop
theorem theta_and_it_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j h
  have hC := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hP.ex
  have hvT := (hR.row W.P.A3.A.μ0).vT j h
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvT.1.2.inf
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' ((f.row W.P.A3.A.μ0).vT j h) :=
    GlobalTheory.VecTheta.isThetaFunO_stepVec hvT
  have key : ∀ n (e : D.R.m - 1 = n),
      IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) ∧
      IsItW (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e)
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e))
        (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact ⟨hC.chain.ωX _, hC.chain.ItX _⟩
  obtain ⟨hW', hI'⟩ := key (j + 1) (idx_top h)
  obtain ⟨b, hb, hbv⟩ := _root_.GlobalTheory.T.top_step_vector_theta_alt W hP j h _ hvT
  exact ⟨fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW'.std hθ _ _ _ _ hth φ, isItW_of_comb hW' hθ hth hb hbv hI'⟩
end GlobalTheory.BaseChainTop
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
theorem _root_.GlobalTheory.T.base_chain_top_theta_functions_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  atlas_forward_decl _root_.GlobalTheory.BaseChainTop.theta_and_it_alt
end
end
