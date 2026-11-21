import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataChainStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataChainStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsMatrixReadingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsMatrixReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionAtLevelPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDual

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MidVacLat
variable {D : D7}
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j hj d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sd0 : IsSelfDualC (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j (by omega))
  have sd1 : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) hj)
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd0).1 (f.g.b j)
  obtain ⟨M', hM', hmv'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd1).1 (f.g.b (j + 1))
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hvth := hd₀.2.1.2.theta
  have hvlat := hd₀.2.1.2.lat
  exact ⟨M, M', hM, hM', hmv _, hmv' _, hWe.om_pres _ _ hvth,
    isLatVac_move hWe sd0 hM sd1 hM' (hmv _) (hmv' _) hvth hvlat⟩
end GlobalTheory.MidVacLat
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
  atlas_forward_decl _root_.GlobalTheory.MidVacLat.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MovedDat
theorem locF_prod_level_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ (j : ℕ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP)), omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) y = ∏ i, GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (GlobalTheory.MovedDat.RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f v n G pl hG j y
  have hlev := hG.lev
  have hRd : ∀ (i i' : Fin n) (h : i' = i) (PP : Formalism.L2.DIV.Pl D.host.E) (z : (G i').S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)),
      RdAt (G i') PP z g → RdAt (G i) PP (cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) h) z) g := by
    intro i i' h; subst h; intro PP z g hz; exact hz
  have hlam : ∀ (i i' : Fin n) (h : i' = i) (z : (G i').S.P.J),
      (G i').S.P.lam z = (G i).S.P.lam (cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) h) z) := by
    intro i i' h; subst h; intro z; rfl
  have hw : ∀ (w w' : (_root_.GlobalTheory.Fam.pk_z W).Pg) (h : w' = w) (k : Fin n) (z : (G k).S.P.J) (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)),
      RdAt (G k) w'.1 z (g w') → RdAt (G k) w.1 z (g w) := by
    intro w w' h; subst h; intro k z g hz; exact hz
  have key := GlobalTheory.LocMod.StepVec.omegaG_eq_prod (t := D.R.t) (j := j) (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1)
    (X := fun w => (G (pl.symm w)).S.P.J) (fun w => RdAt (G (pl.symm w)) w.1) (fun w x => (G (pl.symm w)).S.P.lam x)
    (fun g => by
      rw [(hlev g).1]
      constructor
      · intro h w
        obtain ⟨x, hx⟩ := h (pl.symm w)
        exact ⟨x, hw w (pl (pl.symm w)) (pl.apply_symm_apply w) _ x g hx⟩
      · intro h i
        obtain ⟨x, hx⟩ := h (pl i)
        exact ⟨_, hRd i (pl.symm (pl i)) (pl.symm_apply_apply i) _ x _ hx⟩)
    (fun g x hx => by
      have e := (hlev g.1).2 g.2 (fun i => cast (congrArg (fun k => (↥(G k).S.P.J : Type _)) (pl.symm_apply_apply i)) (x (pl i)))
        (fun i => hRd i (pl.symm (pl i)) (pl.symm_apply_apply i) _ (x (pl i)) _ (hx (pl i)))
      refine e.trans ?_
      rw [← Equiv.prod_comp pl (fun w => (G (pl.symm w)).S.P.lam (x w))]
      exact Finset.prod_congr rfl fun i _ => (hlam i (pl.symm (pl i)) (pl.symm_apply_apply i) (x (pl i))).symm)
    y
  refine key.trans ?_
  rw [← Equiv.prod_comp pl]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hF : ∀ i' : Fin n, i' = i →
      GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (RdAt (G i') (pl i).1) (fun x => (G i').S.P.lam x)
        (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) =
      GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x)
        (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
    intro i' h; subst h; rfl
  exact hF _ (pl.symm_apply_apply i)
end GlobalTheory.MovedDat
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_groups_matrix_reading_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ (j : ℕ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP)), omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) y = ∏ i, GlobalTheory.LocMod.StepVec.locF D.R.t j (r_le_Y j) (GlobalTheory.MovedDat.RdAt (G i) (pl i).1) (fun x => (G i).S.P.lam x) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1) (y (pl i).1) := by
  atlas_forward_decl _root_.GlobalTheory.MovedDat.locF_prod_level_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Fam.chi_compat_pk_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  intro D L hT Gi Gl Kc Yd cX ex W hW k _ _ _ _ q PP hP hI π' hπ hR j hj1 hj2 μ hμ hC
  have hL := hW.bot.hyp.2.2.2.1.lev
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) =
      Formalism.IndefR.Datum.toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, (finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hUnr : UnramEverywhere D (_root_.GlobalTheory.Fam.pk_z W).eta :=
    GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta (Formalism.L2.Host.CharFrame.isEta _).unr
  have hη : (_root_.GlobalTheory.Fam.pk_z W).eta y = 1 := hUnr y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 y = (_root_.GlobalTheory.Fam.pk_z W).mu0 j y := by
    unfold Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hH1 := hL.mu0 ⟨j - 1, by omega⟩
  have hH2 := hL.chi ⟨j - 1, by omega⟩
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_at_level_place_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : Formalism.IndefR.Datum.EAf D →+* k, (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (Formalism.IndefR.Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi j PP) μ := by
  atlas_forward_decl _root_.GlobalTheory.Fam.chi_compat_pk_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.MovedDat
open GlobalTheory.LocMod.StepVec
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end GlobalTheory.MovedDat
namespace GlobalTheory.MovedDat
open GlobalTheory.LocMod.StepVec
theorem phi_down_eq_alt (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (G0 : GLoc v)
    (π' : Formalism.IndefR.Datum.EAf D →+* G0.k) (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) (j a : ℕ) (ha : j + a = G0.s)
    (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank)
    (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin (Yc D (j + 1)).rank)
    (mS : MovedTo (ofSplit G0.q) (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      (((G0.FY j (a + 1) (by omega)).β * ((G0.S.T (Fin D.R.t)).bas j (a + 1) (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega) (ea.symm i)))
    (mT : MovedTo (ofSplit G0.q) (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      (((G0.FY (j + 1) a (by omega)).β * ((G0.S.T (Fin D.R.t)).bas (j + 1) a (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega) (eb.symm i)))
    (x : WO (Yc D j) (Yc D (j + 1))) :
    ((G0.S.T (Fin D.R.t)).Phi j a ha ((ofSplit G0.q).down (G0.FY j (a + 1) (by omega)) (G0.FY (j + 1) a (by omega)) x)) =
      G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j
        (((frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
          (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)).map π').submatrix eb ea) := by
  have hS := map_eq_of_movedTo (ofSplit G0.q) (G0.FY j (a + 1) (by omega)) hπ _ _ mS
  have hT := map_eq_of_movedTo (ofSplit G0.q) (G0.FY (j + 1) a (by omega)) hπ _ _ mT
  have key := coords_down (ofSplit G0.q) _ _ hπ (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega)))
    (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega))) ea eb hS hT
    (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)
  rw [down_moved_actO] at key
  rw [← key]
  rfl
end GlobalTheory.MovedDat
namespace GlobalTheory.MovedDat
theorem moved_datum_eq_prod_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hRow v hv hVT n G pl hGP hGR j hj a ha
  refine ⟨1, one_ne_zero, fun x => ?_⟩
  rw [one_mul, isHalf_actO_iff]
  choose π' hπ hred hint hres using fun i => GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D (G i).k (G i).q (pl i).1 (hGR.idem i).1
  choose ea hea mS using fun i => hGR.frame i j (a i + 1) (by have := ha i; omega)
  choose eb heb mT using fun i => hGR.frame i (j + 1) (a i) (by have := ha i; omega)
  have hC := fun i => _root_.GlobalTheory.MovedDat.phi_down_eq_alt D L hT Gi Gl Kc Yd cX ex W f v (G i) (π' i) (hπ i) j (a i) (ha i) (ea i) (eb i) (mS i) (mT i) x
  by_cases hx : IsHalf (∑ i, (G i).q.e) x
  · rw [if_pos hx]
    have hx' := (isHalf_actO_iff _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ _ x).2 hx
    have hQ : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP),
        omegaQ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi
          (fun _ => 1) Frm.B).r (fun _ => 1) 1 y = 1 := fun y => by
      rw [omegaQ, dif_pos (by simp)]; simp
    by_cases hI : IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))
    · rw [if_pos ⟨hx, hI⟩, hQ, mul_one, _root_.GlobalTheory.T.local_groups_matrix_reading_alt D L hT Gi Gl Kc Yd cX ex W u f v n G pl hGR j]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hC i, GlobalTheory.LocMod.StepVec.redM_eq_map (pl i).1 hI, GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum D f.c v (G i) (pl i).1 (π' i) (hπ i) (hred i) (_root_.GlobalTheory.Fam.pk_z W).chi j
        (fun c hc => _root_.GlobalTheory.T.reduction_at_level_place_alt D L hT Gi Gl Kc Yd cX ex W hP (G i).k (G i).q (pl i).1 (pl i).2 (hGR.idem i).1 (π' i) (hπ i) (hred i)
          (c + 1) (by omega) (by omega) _ ((G i).S.tame _) (hGR.mu i (c + 1) (by omega) (by omega)))
        _ _ (r_le_Y j) (ea i) (eb i) (hea i) (heb i)]
      rfl
    · rw [if_neg (fun h => hI h.2)]
      symm
      by_contra hne
      apply hI
      have hnz := fun i h => hne (Finset.prod_eq_zero (Finset.mem_univ i) h)
      intro r s
      refine GlobalTheory.T.integral_finiteAdele_of_split_place_components D n (fun i => (G i).k) (fun i => (G i).q) (fun i => (pl i).1) (fun i => (hGR.idem i).1)
        (fun i l h => pl.injective (Subtype.ext h)) π' hπ hint _ ?_ fun i => ?_
      · rw [← GlobalTheory.LocMod.StepVec.frMapO_smul]
        congr 1
        exact Matrix.ext fun r' s' => hx' r' s'
      · have h1 := hnz i
        rw [hC i] at h1
        have h2 := GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ _ j).symm ((eb i).symm r)) ((ea i).symm s)
        simpa using h2
  · rw [if_neg (fun h => hx h.1), if_neg hx]
end GlobalTheory.MovedDat
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_exponents_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  atlas_forward_decl _root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDat
end GlobalTheory.MidDat
open GlobalTheory.MidDat in
theorem GlobalTheory.MidDat.moved_datum_prod_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have ha : ∀ i, j + ((G i).s - j) = (G i).s := fun i => by have := (G i).hs; omega
  have hA := _root_.GlobalTheory.T.descent_data_step_exponents_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj (fun i => (G i).s - j) ha
  obtain ⟨κ, hκ, hdat⟩ := hA
  have ho : ∀ i, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ x ∈ o.support, IsHalf ((G i).q.e + cA D (G i).q.e) x) ∧
      ∀ Tm, (ofSplit (G i).q).IsModel f.c.ψ ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit (G i).q).up ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) x ∈ latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) (· = (G i).q.v)} (fun _ => 1) →
        Tm Φ₁ = comb f.c.ψ (Yc D j) (Yc D (j + 1)) o (Tm Φ₀) := fun i => exists_o hstd (G i).q _ _ hM hM'
  choose o ho1 ho2 using ho
  let Lp : Fin n → LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M' := fun i =>
    { k := (G i).k, q := (G i).q, unit := (G i).unit, Y := _, Y' := _,
      FS := (G i).FY j ((G i).s - j + 1) (by have := ha i; omega), FT := (G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega),
      Φ := ⟨((G i).S.T (Fin D.R.t)).Phi j ((G i).s - j) (ha i), (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ (ha i)⟩,
      e := (G i).eg j, e_is := (G i).eg_is j _ (ha i), o := o i, o_at := ho1 i, o_is := ho2 i }
  refine ⟨κ, hκ, Lp, fun i => rfl, fun i => rfl, fun i => ⟨(G i).latY _ _ _, (G i).latY _ _ _⟩, fun d hd => ?_⟩
  obtain ⟨-, e, he, hθ⟩ := hd.2
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((_root_.GlobalTheory.Fam.pk_z W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
  have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hRead.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (sdY j (by omega)) hM (sdY (j + 1) hj) hM'
    _ hb _ hb' hmv hmv' e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) hvth hcth hθ
  subst hee
  have hfun : (fun x => (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧
          IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then
        omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) *
          omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)))
        else 0)) = κ • prodDat Lp := funext fun x => hdat x
  rw [hfun] at hmove
  refine ⟨κ⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)),
    GlobalTheory.OrientedHeis.theta_smul _ (hWe.om_pres _ _ hcth), isThetaAt_smul hκ hmove, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hκ, one_smul]
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_vector_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  atlas_forward_decl _root_.GlobalTheory.MidDat.moved_datum_prod_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.Fam.OffLevel
open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit
variable {D : D7}
end GlobalTheory.Fam.OffLevel
end
open GlobalTheory.Fam.OffLevel in
theorem GlobalTheory.Fam.latV_N_eq_off_level_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ _ v _ hv n G pl _ _ j hj M M' hM hM' p hp
  have hP : ∀ q, (· = p) q → q ∉ v.gP := fun q hq => hq ▸ hp
  exact ⟨latV_eq_of_moves _ _ _ _ _ p (hv.moves j (by omega) _ hP) hM,
    latV_eq_of_moves _ _ _ _ _ p (hv.moves (j + 1) hj _ hP) hM'⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDatum
theorem moved_datum_eq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  obtain ⟨M, M', hM, hM', hmv, hmv', hvac⟩ := _root_.GlobalTheory.T.descent_data_step_lattice_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀
  obtain ⟨κ, hκ, Lp, hq, he, hint, hdat⟩ :=
    _root_.GlobalTheory.T.descent_data_step_vector_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hinj : Function.Injective fun i => (Lp i).q.v := by
    intro a b h
    apply hPin.inj
    simpa only [hq] using h
  have hP : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hPin.places _).2 ⟨i, hq i⟩
  obtain ⟨o', ho', hcomb⟩ := GlobalTheory.T.localCombinations_compose_finitely_many_places D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj (· ∈ v.gP) hP
  have hN : IsSelfDualC (Yc D j) (v.N j) := hv.sd j (by omega)
  have hN' : IsSelfDualC (Yc D (j + 1)) (v.N (j + 1)) := hv.sd (j + 1) hj
  have hoff := _root_.GlobalTheory.T.descent_data_step_self_dual_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj M M' hmv hmv'
  obtain ⟨F₀, hF₀t, hF₀at, -⟩ := hdat d₀ hd₀
  have hV := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F₀ hvac hF₀at hF₀t).2 (v.N j) (v.N (j + 1)) hN hN' hint
    (fun p hp => hoff p (by
      rw [hPin.places]
      rintro ⟨i, rfl⟩
      exact hp i (hq i).symm))
  have hth : IsThetaFunO f.c.ψ _ _ (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
    rw [hcomb]; exact hV.1
  refine ⟨M, M', o', hM, hM', ho', vac_true_mono _ hvac, ?_, ?_, κ, hκ, ?_⟩
  · rw [hcomb]; exact vac_true_mono _ hV
  · intro hne; rw [hcomb]; exact GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ hvac hne
  · intro d hd
    obtain ⟨F, hFt, hFat, hFeq⟩ := hdat d hd
    rw [hFeq]
    congr 1
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj _ F hvac hFat hFt).1, GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect D f.c.ψ hstd _ _ M M' hM hM' n Lp hinj, ← hcomb,
      hPin.eG j hj _ hth]
    simp only [he]
end GlobalTheory.MidDatum
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_chain_step_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  atlas_forward_decl _root_.GlobalTheory.MidDatum.moved_datum_eq_alt
end
end
