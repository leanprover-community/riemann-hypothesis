import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryStepValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeTransportStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAtStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelEqUpInfStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem exists_continuous_section_localHomProduct_twAt (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    ∃ (n : ℕ) (ρ : Fin n → Fin J.r)
      (Ψ : (∀ m : Fin n, GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G (ρ m)).k) →
        GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)),
      Continuous Ψ ∧ (∀ x, Ψ x ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)) ∧
      ∀ g ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J), Ψ (fun m => _root_.GlobalTheory.LevProd.localHomProduct J j hj g (ρ m)) = g := by
  classical
  let v : Fin J.r → GlobalTheory.FinPl.Pl (I.rec7 l Z) := fun i => (J.G i).q.v
  let f : Fin J.r → Fin J.r := fun i => (Finset.univ.filter (fun i' => v i' = v i)).min' ⟨i, by simp⟩
  have hf : ∀ i, v (f i) = v i := fun i =>
    (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter (fun i' => v i' = v i)) ⟨i, by simp⟩)).2
  have hf2 : ∀ i i', v i = v i' → f i = f i' := by
    intro i i' h
    simp only [f, h]
  let R := {i : Fin J.r // f i = i}
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let ρ : Fin (Fintype.card R) → Fin J.r := fun m => (e.symm m).1
  have hinj : Function.Injective fun m => (J.G (ρ m)).q.v := by
    intro m m' h
    have h1 : f (ρ m) = f (ρ m') := hf2 _ _ h
    rw [(e.symm m).2, (e.symm m').2] at h1
    exact e.symm.injective (Subtype.ext h1)
  obtain ⟨Ψ, hc, hin, -, huniq⟩ := GlobalTheory.FixLev.exists_section ((I.rec7 l Z).sp.X j)
    (fun m => (J.G (ρ m)).k) (fun m => (J.G (ρ m)).q) hinj
    (fun _ => XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
    (fun m => (J.G (ρ m)).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J (ρ m) hj; omega))
  have hP : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) fun p => ∃ m, p = (J.G (ρ m)).q.v) =
      GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) := by
    congr 1
    funext p
    apply propext
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨ρ m, rfl⟩
    · rintro ⟨i, rfl⟩
      have hfix : f (f i) = f i := hf2 _ _ (hf i)
      refine ⟨e ⟨f i, hfix⟩, ?_⟩
      show v i = v (e.symm (e ⟨f i, hfix⟩)).1
      rw [e.symm_apply_apply]
      exact (hf i).symm
  refine ⟨Fintype.card R, ρ, Ψ, hc, fun x => hP.le (hin x), fun g hg => huniq g (hP.ge hg) _ fun m => ?_⟩
  exact (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ g _).2 rfl
theorem isCompact_relax' (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hR : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) :
    IsCompact (_root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  classical
  have hU := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j (by omega) (J.ι j α)).1
  haveI hNn : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp
    infer_instance
  obtain ⟨n, ρ, Ψ, hc, hin, huniq⟩ := _root_.GlobalTheory.LevProd.exists_continuous_section_localHomProduct_twAt J j hj
  let Kp : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    Set.pi Set.univ fun i => (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) : Set _)
  have hKpc : IsCompact Kp := isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hKpcl : IsClosed Kp := isClosed_set_pi fun i _ => Subgroup.isClosed_of_isOpen _ SplitFlip.isOpen_KO
  have hphi : Continuous (_root_.GlobalTheory.LevProd.localHomProduct J j hj) := continuous_pi fun i => GlobalTheory.LevIdx.continuous_locHom _ _ _
  let C : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    (fun p : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) =>
      (_root_.GlobalTheory.LevProd.localHomProduct J j hj p.1)⁻¹ * p.2) '' ((J.A.U j (J.ι j α) : Set _) ×ˢ Kp)
  have hCc : IsCompact C := (hU.cpt.prod hKpc).image ((hphi.comp continuous_fst).inv.mul continuous_snd)
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) →
      GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) := fun p => p.1 * Ψ (fun m => p.2 (ρ m))
  have hF : Continuous F :=
    continuous_fst.mul (hc.comp (continuous_pi fun m => (continuous_apply (ρ m)).comp continuous_snd))
  let S := ((J.A.U j (J.ι j α) : Set _) ×ˢ C) ∩ F ⁻¹' (_root_.GlobalTheory.LevProd.localHomProduct J j hj ⁻¹' Kp)
  have hSc : IsCompact S := (hU.cpt.prod hCc).inter_right ((hKpcl.preimage hphi).preimage hF)
  have heq : (_root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) = F '' S := by
    ext g
    constructor
    · intro hg
      have hg1 := Subgroup.mem_inf.1 (hg : g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α)
      have hsup : g ∈ ((J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) : Subgroup _) : Set _) :=
        (Subgroup.mem_inf.1 hg1.1).1
      have hK : _root_.GlobalTheory.LevProd.localHomProduct J j hj g ∈ Kp := Subgroup.mem_comap.1 hg1.2
      rw [Subgroup.mul_normal] at hsup
      obtain ⟨x, hx, y, hy, rfl⟩ := hsup
      have hFy : F (x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y) = x * y := by
        show x * Ψ (fun m => _root_.GlobalTheory.LevProd.localHomProduct J j hj y (ρ m)) = x * y
        rw [huniq y hy]
      refine ⟨(x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y), ⟨⟨hx, ⟨(x, _root_.GlobalTheory.LevProd.localHomProduct J j hj (x * y)), ⟨hx, hK⟩, ?_⟩⟩, ?_⟩, hFy⟩
      · show (_root_.GlobalTheory.LevProd.localHomProduct J j hj x)⁻¹ * _root_.GlobalTheory.LevProd.localHomProduct J j hj (x * y) = _root_.GlobalTheory.LevProd.localHomProduct J j hj y
        rw [map_mul, inv_mul_cancel_left]
      · show _root_.GlobalTheory.LevProd.localHomProduct J j hj (F (x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y)) ∈ Kp
        rw [hFy]
        exact hK
    · rintro ⟨⟨x, z⟩, ⟨⟨hx, -⟩, hK⟩, rfl⟩
      show F (x, z) ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mem_comap.2 hK⟩
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hin _))
      · exact Subgroup.mul_mem _ (hU.le hx) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hin _))
  rw [heq]
  exact hSc.image hF
theorem isCompact_upperLevelSubgroup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), IsCompact (_root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
  split_ifs with h
  · exact _root_.GlobalTheory.LevProd.isCompact_relax' hW _ h.choose_spec.choose_spec.1 j hj _
  · rw [Subgroup.coe_bot]
    exact isCompact_singleton
end GlobalTheory.LevProd
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_compact_upper_level_subgroup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), IsCompact (_root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  atlas_forward_decl _root_.GlobalTheory.LevProd.isCompact_upperLevelSubgroup
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_transport_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  first | exact @_root_.GlobalTheory.LevProd.loc_level_alt | exact _root_.GlobalTheory.LevProd.loc_level_alt | (intros; apply _root_.GlobalTheory.LevProd.loc_level_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem up_phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg i
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup at hg
  split_ifs at hg with h
  · obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
    by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace h.choose_spec.choose (J.G i).q.v
    · obtain ⟨i₀, hi₀⟩ := hv
      exact _root_.GlobalTheory.T.true_geometry_lattice_closed_alt W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 t J hJ i₀ i hi₀ g hgf
        ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
    · have hle : h.choose_spec.choose.A.U j (h.choose_spec.choose.ι j h.choose_spec.choose_spec.2.some) ⊔
          GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace h.choose_spec.choose) ≤
          (KO (J.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (_root_.GlobalTheory.LevProd.localHomProduct J j hj)) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · exact _root_.GlobalTheory.T.true_geometry_lattice_final_alt W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 _ t J hJ i hv x hx
        · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
          change GlobalTheory.LevIdx.locHom (J.G i).q _ _ x ∈ KO (J.G i).k _
          rw [locHom_eq_one_of_grpAt _ _ _ hv hx]
          exact one_mem _
      exact hle hsup
  · rw [Subgroup.mem_bot.1 hg, map_one]
    exact one_mem _
end GlobalTheory.LevProd
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_step_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  atlas_forward_decl _root_.GlobalTheory.LevProd.up_phi_mem_KO_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem pl_eq_of_quadratic_data_same_place (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂)
    (hJ₂ : J₂.Reads) (i : Fin J.r) (i₂ : Fin J₂.r) (h : (J.G i).q.v = (J₂.G i₂).q.v) : J.pl i = J₂.pl i₂ := by
  have h1 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i
  have h2 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t₂ J₂ hJ₂).2 i₂
  exact hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t₂, J₂.mem i₂⟩ (h1.symm.trans (h.trans h2))
theorem locHom_gl_eq_self_of_map_pr_eq (j : ℕ) {PP} (h₁ h₂ : _root_.GlobalTheory.Fam.QAllAlt W PP) (hj₁ : j ≤ (a.Q PP h₁).s + 1) (hj₂ : j ≤ (a.Q PP h₂).s + 1)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (a.Q PP h₂).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, (mt _ (gl y)).map (a.Q PP h₂).q.pr = ((a.Q PP h₂).FX j hj₂).β * y.val * ((a.Q PP h₂).FX j hj₂).γ) (y) :
    GlobalTheory.LevIdx.locHom (a.Q PP h₁).q _ ((a.Q PP h₁).FX j hj₁) (gl y) = y :=
  ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y)).symm
end GlobalTheory.LevOnto
end
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem gl_mem_relax_of_supp_at_and_map_pr (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads)
    (α : J.Ch j) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂) (hJ₂ : J₂.Reads) (i : Fin J₂.r)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr =
      ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).β * y.val * ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).γ)
    (y) (hy : y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) : gl y ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α := by
  have hAt : ∀ P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop, P (J₂.G i).q.v → gl y ∈ GlobalTheory.FinPl.grpAt _ P :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt (· = (J₂.G i).q.v) rfl)⟩, ?_⟩
  · by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v
    · exact Subgroup.mem_sup_right (hAt _ hv)
    · exact Subgroup.mem_sup_left (_root_.GlobalTheory.T.true_geometry_lattice_open_alt W hW u a ha hTr j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy)
  · rw [Subgroup.mem_comap, Subgroup.mem_pi]
    intro i' _
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl y) ∈ KO (J.G i').k _
    by_cases hv : (J.G i').q.v = (J₂.G i).q.v
    · have e := _root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J₂ hJ₂ i' i hv
      have key : ∀ P (hP : P ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (hj₁ : j ≤ (a.Q P ⟨t, hP⟩).s + 1), P = J₂.pl i →
          GlobalTheory.LevIdx.locHom (a.Q P ⟨t, hP⟩).q _ ((a.Q P ⟨t, hP⟩).FX j hj₁) (gl y) ∈ KO (a.Q P ⟨t, hP⟩).k
            (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) := by
        rintro P hP hj₁ rfl
        rw [_root_.GlobalTheory.LevOnto.locHom_gl_eq_self_of_map_pr_eq j _ _ hj₁ _ gl (fun y => (hgl y).2) y]
        exact hy
      exact key _ (J.mem i') _ e
    · rw [locHom_eq_one (J₂.G i).q (J.G i').q _ _ (gl y) (hgl y).1 (Ne.symm hv)]
      exact one_mem _
theorem onto_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, _root_.GlobalTheory.LevProd.localHomProduct J j hj g = x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α x hx
  have hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  have hUp : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj = _root_.GlobalTheory.LevProd.relaxedLevelSubgroup hex.choose_spec.choose j hj hex.choose_spec.choose_spec.2.some := by
    unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
    rw [dif_pos hex]
  have hJ₀ : hex.choose_spec.choose.Reads := hex.choose_spec.choose_spec.1
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl _ hglp _ using hgl
  refine ⟨((List.finRange J.r).map fun i => gl i (x i)).prod, ?_, ?_⟩
  · rw [hUp]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact _root_.GlobalTheory.LevOnto.gl_mem_relax_of_supp_at_and_map_pr hW ha hTr j hj _ hJ₀ _ J hJ i (gl i) (hglp i) (x i) (hx i)
  · rw [map_list_prod, List.map_map]
    have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
      intro i
      funext i'
      show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
      by_cases h : i' = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
      · rw [Pi.mulSingle_eq_of_ne h]
        refine locHom_eq_one (J.G i).q (J.G i').q _ _ _ (hglp i (x i)).1 fun hv => h ?_
        exact hJ.inj (_root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J hJ i' i hv.symm)
    simp only [Function.comp_def, hphi]
    exact list_prod_mulSingle x
end GlobalTheory.LevOnto
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, _root_.GlobalTheory.LevProd.localHomProduct J j hj g = x := by
  atlas_forward_decl _root_.GlobalTheory.LevOnto.onto_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
theorem GlobalTheory.LevProd.level_prod_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ Up : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), Up ≤ GfC _ ∧ IsCompact (Up : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ (H : ∀ i, Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) (φ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)), (∀ i, H i ≤ KO (J.G i).k _ ∧ MeasurableSet (H i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (H i).relIndex (KO (J.G i).k _) ≠ 0 ∧ (J.E i).wt j (α i) = ((((J.E i).m j (H i)).toReal⁻¹ : ℝ) : ℂ)) ∧ (∀ g ∈ Up, ∀ i, φ g i ∈ KO (J.G i).k _) ∧ (∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ Up, φ g = x) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  refine ⟨_root_.GlobalTheory.LevProd.upperLevelSubgroup a (j := j) (by omega), _root_.GlobalTheory.LevProd.upperLevelSubgroup_le_GfC a j (by omega), _root_.GlobalTheory.T.is_compact_upper_level_subgroup W hW u a ha hA j (by omega), fun t J hJ α => ?_⟩
  refine ⟨_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j (by omega) α, _root_.GlobalTheory.LevProd.localHomProduct J j (by omega), fun i => ⟨?_, ?_, ?_, _root_.GlobalTheory.LevProd.wt_eq_inv_measure_levelSubgroupAtPlace J j (by omega) α i⟩,
    _root_.GlobalTheory.T.true_geometry_lattice_step_value_alt W hW u a ha hA j (by omega) t J hJ, _root_.GlobalTheory.T.true_geometry_lattice_level_alt W hW u a ha hA j (by omega) t J hJ α,
    _root_.GlobalTheory.T.true_geometry_lattice_twist_alt W hW u a ha hA j (by omega) t J hJ α⟩
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.1
  · exact (_root_.GlobalTheory.T.true_geometry_lattice_transport_alt W hW u a ha hA j (by omega) t J hJ α i).2.2
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_step_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ Up : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), Up ≤ GfC _ ∧ IsCompact (Up : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ (H : ∀ i, Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) (φ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)), (∀ i, H i ≤ KO (J.G i).k _ ∧ MeasurableSet (H i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (H i).relIndex (KO (J.G i).k _) ≠ 0 ∧ (J.E i).wt j (α i) = ((((J.E i).m j (H i)).toReal⁻¹ : ℝ) : ℂ)) ∧ (∀ g ∈ Up, ∀ i, φ g i ∈ KO (J.G i).k _) ∧ (∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ Up, φ g = x) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i := by
  atlas_forward_decl _root_.GlobalTheory.LevProd.level_prod_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.Fam
namespace VolMid
end VolMid
open VolMid
theorem volLev_mul_wt_mid_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨Up, hUpf, hUpc, hK⟩ := _root_.GlobalTheory.T.true_geometry_step_value_alt W hW u a ha haT j hj
  have step : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j,
      (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = (GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up : ℂ) ∧
        J.wt j α ≠ 0 ∧ GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 := by
    intro t J hJ α
    obtain ⟨H, φ, hH, hφK, hφs, hU⟩ := hK t J hJ α
    have hidx := relIndex_eq_prod_of_pi φ Up (J.A.U j (J.ι j α)) (fun i => KO (J.G i).k _) H hφK hφs hU
    have hreps := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is j (by omega) (J.ι j α)).1
    have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) _ (a.g.x j).vol (J.A.U j (J.ι j α)) Up (fun g hg => ((hU g).1 hg).1) hUpf hUpc
      hreps.opn
    have hwt : J.wt j α = ((J.A.U j (J.ι j α)).relIndex Up : ℂ) := by
      rw [hidx, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
      push_cast
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(hH i).2.2.2]
      exact GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral (J.G i) _ (J.E i) j (H i) (hH i).1 (hH i).2.1 (hH i).2.2.1
    refine ⟨?_, ?_, GlobalTheory.AdForm.PinInhab.volLev_ne_zero hW.tr.ok haT.pinX.inf j _ _ hreps⟩
    · rw [hwt, ← hvol]; push_cast; ring
    · rw [hwt, hidx]; push_cast; exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hH i).2.2.1
  by_cases hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t, J, hJ, ⟨α⟩⟩ := hex
    refine ⟨GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up, ?_, fun t' J' hJ' α' => (step t' J' hJ' α').1⟩
    obtain ⟨h1, h2, h3⟩ := step t J hJ α
    rw [← h1]
    exact mul_ne_zero (by exact_mod_cast h3) h2
  · exact ⟨1, one_ne_zero, fun t J hJ α => absurd ⟨t, J, hJ, ⟨α⟩⟩ hex⟩
end GlobalTheory.Fam
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_chain_step_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  atlas_forward_decl _root_.GlobalTheory.Fam.volLev_mul_wt_mid_alt
end
end
