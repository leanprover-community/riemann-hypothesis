import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColNone
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevelWtConstStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsKernelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryExistsKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyFinalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyFinal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyCharsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QLevOfReadsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZeroColOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsExistsStatement

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.KomExist
theorem exists_compactOpen_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) (kom t j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ haT
  have hL := hW.pk.bot.hyp.2.2.2.1.lev
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists (I.rec7 l Z)
  have key : ∀ (t : W.P.T) j, j < B.R.m → ∃ om : Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
      IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) om := by
    intro t j hj
    have hH := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t ⟨j, hj⟩
    exact hE _ _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ haT.pinX.std hH hH
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX j (le_of_lt hj)))
      (GlobalTheory.HeckeCharacterRestriction.resEta_even hL t ⟨j, hj⟩ (even_rankX (j + 1) hj))
  classical
  refine ⟨fun t j => if h : j < B.R.m then (key t j h).choose else 1, fun t j hj => ?_⟩
  simp only [dif_pos hj]
  exact (key t j hj).choose_spec
end GlobalTheory.Fam.KomExist
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_exists_kernel_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)),
    ∀ t j, j < B.R.m → IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (_root_.GlobalTheory.Fam.chrK_alt W t j) (_root_.GlobalTheory.Fam.chrK_alt W t j) (kom t j) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.KomExist.exists_compactOpen_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam.FinData
theorem main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ t J _ s j α γ hj
  refine ⟨?_, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atG j).2.1, GlobalTheory.Fam.VacTheta.isFinComb_of_combAt (ha.vis.atT j).1⟩
  unfold _root_.GlobalTheory.Fam.QuadraticExtensionData.dQ
  refine isFinComb_smul _ _ (isFinComb_smul _ _ (GlobalTheory.QPl.ThetaPin.isFinComb_aconv _ fun e he => ?_))
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨ε, hε, hsum⟩ := (J.G i).q.above
  have hs := (J.G i).hs
  refine GlobalTheory.QPl.ThetaPin.isFinComb_of_half hε _ fun w hw => hsum ▸ ?_
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  rcases Nat.lt_or_ge j (J.G i).s with h1 | h1
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = (J.G i).s := ⟨(J.G i).s - j - 1, by omega⟩
    exact ((J.E i).dL_mid j d hd (α i) (γ i)).1 w hw
  · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · subst h2
      exact ((J.E i).dL_pen (α i) (γ i)).1 w hw
    · obtain rfl : j = (J.G i).s + 1 := by omega
      exact ((J.E i).dL_top (α i) (γ i)).1 w hw
end GlobalTheory.Fam.FinData
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (s : ∀ j, J.Ch j → ℂ) j α γ, j < B.R.m →
    GlobalTheory.SeeSaw.IsFinComb (J.dQ s j α γ) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dG j) ∧ GlobalTheory.SeeSaw.IsFinComb (a.v.dT j) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.FinData.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam
theorem colOf_readS_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ha hat J hJ k
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  choose S hS using fun t => GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) _ _ (J t).A (J t).ι (hJ t).is (_root_.GlobalTheory.Fam.pk_z W).θ
    hat.pinX.inf a.k a.ι a.o.p a.o.β a.o.Q (fun j => (a.g.x j).L) hat.std a.o.I a.o.q a.o.χ a.o.hχ
  refine ⟨S, fun t => ⟨fun j hj η φ hφ => ((hS t j hj φ hφ).2 η).1, fun row kom dd s cV cK cP => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj ψ hψ α y
    have h := (hS t j hj ψ hψ).1 ((J t).ι j α) y
    change (if hj' : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj' ((J t).ι j α) ψ y else 0) ∈ a.o.Ram j
    have hj2 : j ≤ B.R.m := hj
    rw [dif_pos hj2]
    exact h
  · intro j hj ψ hψ α y
    have hj' : j ≤ B.R.m := by change j + 2 ≤ B.R.m at hj; omega
    change (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) (S t j (k.ε j) ψ) y else 0) =
      a.o.S k.ε j (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) ψ y else 0)
    rw [dif_pos hj', dif_pos hj']
    exact ((hS t j hj' ψ hψ).2 (k.ε j)).2 _ y
  · intro η ψ hψ
    have h0 : (0 : ℕ) ≤ B.R.m := Nat.zero_le _
    refine ⟨((hS t 0 h0 ψ hψ).2 η).1, fun α y => ?_⟩
    change (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) (S t 0 η ψ) y else 0) =
      a.o.S (fun _ => η) 0 (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) ψ y else 0)
    rw [dif_pos h0, dif_pos h0]
    exact ((hS t 0 h0 ψ hψ).2 η).2 _ y
end GlobalTheory.Fam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.colOf_readS_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    Function.Injective (fun i => (J.G i).q.v) ∧ ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
  first | exact @_root_.GlobalTheory.Fam.QJPlaces.places_under_alt | exact _root_.GlobalTheory.Fam.QJPlaces.places_under_alt | (intros; apply _root_.GlobalTheory.Fam.QJPlaces.places_under_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.QPl.EpsSupp
end GlobalTheory.QPl.EpsSupp
open GlobalTheory.QPl.EpsSupp in
theorem GlobalTheory.Fam.famOf_eps_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg
  have h1 := eps_mem_grpAt (_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg
  refine ⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩
  rw [← (ha.tie row col).1.b j]
  exact ha.vis.b j
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  atlas_forward_decl _root_.GlobalTheory.Fam.famOf_eps_mem_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.QColLaws.laws_resc_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _haT row col hr hc t F w₀ s hs hPin hQ
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hsh := ha.shape
  have hIs := _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col) hr
  have hweil := _root_.GlobalTheory.T.weilOK_of_rank_one_gram' W u hW.pk (a.fam row col) a.v hr hc (ha.tie row col).1
    (fun j h => ⟨hsh.pre.line.1, hsh.pre.tau j h⟩) t w₀ hQ
  exact GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling _ (a.fam row col).c a.v ((a.fam row col).t t) (GlobalTheory.QTw.resc w₀ s) hIs.1 (hIs.2 hc t) ha.vis hweil.1
    ⟨w₀, s, hs, ⟨F, hPin⟩, rfl⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_family_final_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  atlas_forward_decl _root_.GlobalTheory.QColLaws.laws_resc_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QVecJoin
open GlobalTheory.QVec GlobalTheory.LocMod.StepVec
end GlobalTheory.QVecJoin
end General
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.QVecJoin
theorem qVec_pinTup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat J hJ row col hCh sc cT t
  have hC3 := hW.pk.bot.hyp.2.2.2.1
  have hL := hC3.lev
  obtain ⟨hinj, hund⟩ := _root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t (J t) (hJ t)
  have hV := (ha.tie row col).1
  have hQS : ∀ p, p ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q ↔ ∃ i, ((J t).G i).q.v = p := by
    intro p
    simp only [QFam.pinTup, _root_.GlobalTheory.Fam.familyOfRowColumnChoices, Finset.mem_image]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
  have hSQ : ∀ p, (∃ i, ((J t).G i).q.v = p) ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, hund i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, rfl⟩ := (hJ t).surj PP hPP
      exact ⟨i, hund i⟩
  have hQiff : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t ↔ ∃ i, (J t).pl i = PP := fun PP =>
    ⟨fun h => (hJ t).surj PP h, by rintro ⟨i, rfl⟩; exact (J t).mem i⟩
  have hrk : ∀ i, (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (((J t).G i).s + 1) := by
    intro i
    have e1 : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m - 1 := rfl
    have e2 := ((J t).G i).hs
    omega
  have gIn : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∃ k, (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    refine ⟨k, ?_⟩
    have hmemK : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ (PP.under (𝓞 (I.rec7 l Z).host.K)).asIdeal := by
      have hk' : PP.under (𝓞 (I.rec7 l Z).host.K) = (_root_.GlobalTheory.Fam.pk_z W).C.P.pb k := hk
      rw [hk']
      exact (_root_.GlobalTheory.Fam.pk_z W).C.P.pb_over k
    have h2 : algebraMap (𝓞 (I.rec7 l Z).host.K) (𝓞 (I.rec7 l Z).host.E) (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hoff : ∀ p, (∃ i, ((J t).G i).q.v = p) → p ∉ a.v.gP := by
    intro p hp hxg
    obtain ⟨PP, hPP, rfl⟩ := (hSQ p).1 hp
    obtain ⟨PP', hPP', e⟩ := (hV.gP _).1 hxg
    obtain ⟨k, hk⟩ := gIn PP' hPP'
    have hg : (((I.rec7 l Z).host.g k : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal :=
      (natCast_mem_under PP _).1 (e ▸ (natCast_mem_under PP' _).2 hk)
    obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hPP
    haveI : PP.asIdeal.IsPrime := PP.isPrime
    haveI : Finite (Formalism.L2.DIV.kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
    haveI : Fintype (Formalism.L2.DIV.kP PP) := Fintype.ofFinite _
    have hq0 : ((q : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
      have h0q : ((q : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (Formalism.L2.DIV.kP PP)
      exact (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).1 (by simpa using h0q)
    exact false_of_coprime_mem PP ((Nat.coprime_primes hq ((I.rec7 l Z).host.g_prime k)).2 (hne k)) hq0 hg
  have hS : (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) = (fun p => ∃ i, ((J t).G i).q.v = p) :=
    funext fun p => propext (hQS p)
  have hmv : ∀ j, j < (I.rec7 l Z).R.m → GlobalTheory.FinPl.Moves _ (a.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (a.v.N j) (fun p => ∃ i, ((J t).G i).q.v = p) :=
    fun j hj => hV.moves j hj _ hoff
  have hb : ∀ j, a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := fun j => (hV.b j) ▸ ha.vis.b j
  have hS' : (fun p => ∃ i, ((J t).G i).q.v = p) = fun p => ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) :=
    funext fun p => propext (hSQ p)
  have sdY : ∀ j, j < (I.rec7 l Z).R.m → IsSelfDualC (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) := fun j hj =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ (hL.βY j hj)
  have sdX : IsSelfDualC (I.rec7 l Z).sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hL.βX
  refine ⟨?_, ?_⟩
  · intro j hj d hd g hg
    have hmid : ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j = aconv (List.ofFn fun i => ((J t).E i).eL j) := if_pos hj
    rw [hmid]
    rw [hS] at hg
    exact step_mid (I.rec7 l Z) (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) a.v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g) (_root_.GlobalTheory.Fam.chrK_alt W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv j (by omega)) (hmv (j + 1) hj) (hb j) (hb (j + 1)) (sdY j (by omega)) (sdY (j + 1) hj) _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _ (hC3.chain.ωY t j hj) g hg
  · intro j hj d hd g hg
    rw [hS] at hg
    have hmT : GlobalTheory.FinPl.Moves _ a.g.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.v.NT (fun p => ∃ i, ((J t).G i).q.v = p) := by
      rw [hV.bT.2]; exact hV.movesT _
    have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
      have h1 := ha.vis.bT
      rwa [hV.bT.1] at h1
    exact step_top (I.rec7 l Z) (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) a.v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g) (_root_.GlobalTheory.Fam.chrK_alt W t) ha.vis (J t).r (J t).pl
      (fun i => (J t).G i) (fun i => (J t).E i) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).Q t) _ hinj hQiff (fun p => Iff.rfl) (hJ t).res hrk j hj
      (hmv (j + 1) (by omega)) hmT (hb (j + 1)) hbT (sdY (j + 1) (by omega)) sdX _ _ _ _ _ d rfl rfl
      (GlobalTheory.SeeSaw.Inh.vac_ne_zero hd.2.1) (by rw [hS']; exact hd.1) hd.2 _ _ _
      (isWeilDatum_cast ((_root_.GlobalTheory.Fam.pk_z W).ωX t) (hC3.chain.ωX t) (j + 1) (idx_top hj)) g hg
end GlobalTheory.QVecJoin
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT) := by
  atlas_forward_decl _root_.GlobalTheory.QVecJoin.qVec_pinTup_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl.PinComb
variable {D : D7} {c : Comm D}
variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}
end GlobalTheory.QPl.PinComb
open GlobalTheory.QPl.PinComb in
theorem GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ J _ row col hCh sc cT t j
  exact pinTup_combAt _ sc cT j
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  atlas_forward_decl _root_.GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.Fam.colSide_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA k row hrow hsame
  classical
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  have hc : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row _root_.GlobalTheory.Fam.trivialColumnChoice) (hRow _)).1
  choose J hJ using _root_.GlobalTheory.T.exists_quadratic_extension_reads_of_true W hW u a ha haT hc
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt W hW u a ha haT hiA
  choose s ζ ρ hD using fun t => hC t (J t) (hJ t)
  obtain ⟨V, VT, hV0, hVT0, hV⟩ := _root_.GlobalTheory.T.true_geometry_exists_volume_data_alt W hW u a ha haT
  obtain ⟨kom, hkom⟩ := _root_.GlobalTheory.T.true_geometry_exists_kernel_alt W hW u a ha haT
  have hdd0 : ∀ t j α γ, ∃ d, j < B.R.m → GlobalTheory.SeeSaw.IsFinComb d ∧ ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d f =
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((J t).dQ (s t) j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f)) := by
    intro t j α γ
    by_cases hj : j < B.R.m
    · obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_twist_local_value_alt W hW u a ha haT t (J t) (hJ t) (s t) j α γ hj
      obtain ⟨d, hd⟩ := GlobalTheory.Fam.finComb3 _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ _ h1 h2 h3
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose dd hdd using hdd0
  obtain ⟨S', hS'⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt W hW u a ha haT J hJ k
  have hone : ∀ t, ∃ β₀ : (J t).Ch B.R.m, ∀ β, β = β₀ := fun t => by
    have hc1 : Fintype.card ((J t).Ch B.R.m) = 1 := by
      rw [Fintype.card_pi]
      refine Finset.prod_eq_one fun i _ => ?_
      have h1 := ((J t).E i).one
      have h2 : ((J t).G i).s + 1 + 1 = B.R.m := ((J t).G i).hs
      rw [h2] at h1
      exact h1
    exact Fintype.card_eq_one_iff.1 hc1
  choose β₀ hβ₀ using hone
  let cQf : W.P.T → ℕ → ℂ := fun t j => ∏ i, ((((J t).E i).idx (j + 1) : ℂ) * (((J t).E i).idx (j + 1 + 1) : ℂ))⁻¹
  let cTf : W.P.T → ℕ → ℂ := fun t j => @TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
  let cK : W.P.T → ℕ → ℂ := fun t j => V j * C j * a.c₀ j * ρ t j
  let cP : W.P.T → ℂ := fun t => VT * ∑ β, s t B.R.m β
  let cV : W.P.T → ℕ → ℂ := fun t j => if h : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then
      k.v.kap j h.choose h.choose_spec * (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
    else (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
  let col := _root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP
  let F := _root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col (fun _ => rfl)
  let w₀ := fun t => (F t).pinTup (k.sc t) (cTf t)
  let w := fun t => GlobalTheory.QTw.resc (w₀ t) (s t)
  have hPinCh : ∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) a.c₀ (J t).A (J t).ι w := fun t => by
    refine ⟨fun j α γ => C j * (J t).wt j α * ζ t j α γ, ?_⟩
    refine
      { is := (hJ t).is
        live := (hJ t).live
        om := fun j hj => by rw [(hJ t).chr j hj]; exact hkom t j hj
        dat := fun j hj α γ => ⟨(hdd t j α γ (by omega)).1, by
          show IsRatDatum _ _ _ _ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (dd t j α γ) (a.g.vac j))
          rw [(hdd t j α γ (by omega)).2]
          exact ((hD t).2.2.2 j hj α γ).1⟩
        cst := fun j hj α γ _ => by
          have h1 := ((hV t (J t) (hJ t)).1 j (by omega) α)
          have h2 := ((hD t).2.2.2 j hj α γ).2
          show V j * C j * a.c₀ j * ρ t j = _
          rw [← h1, ← h2]
          ring
        ram := fun j _ φ => Iff.rfl
        rdq := fun j hj β φ y => dif_pos hj }
  refine ⟨col, w₀, w, F, ⟨a.c₀, haT.pinX, fun t => ⟨⟨(J t).Ch₀, (J t).A, (J t).ι, hPinCh t⟩, ?_⟩⟩, ?_⟩
  · obtain ⟨UT, hUT1, hUT2⟩ := (hV t (J t) (hJ t)).2
    refine ⟨UT, s t B.R.m (β₀ t) * (J t).wt B.R.m (β₀ t),
      { emb := haT.emb
        lev := hUT1
        eT := fun n h β => ?_
        cP := ?_ }⟩
    · subst h
      rw [hβ₀ t β]
      show (s t B.R.m (β₀ t) • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt B.R.m (β₀ t))).mapDomain (· * a.g.bT) = _
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, one_mul, smul_eq_mul]
    · show VT * ∑ β, s t B.R.m β = _
      rw [Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb), ← hUT2 (β₀ t)]
      ring
  have hdQ : ∀ t j α γ, j < B.R.m → (w t).dQ j α γ = (J t).dQ (s t) j α γ := fun t j α γ hj => by
    show _ • (if j < B.R.m then _ else 0) = _
    rw [if_pos hj]
    rfl
  have hpl := fun t => _root_.GlobalTheory.T.true_geometry_twist_local_data_alt W hW u a ha haT t (J t) (hJ t)
  have hQ : ∀ t p, p ∈ (w₀ t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := fun t p => by
    show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, (hpl t).2 i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, hi⟩ := (hJ t).surj PP hPP
      exact ⟨i, Finset.mem_univ _, by rw [(hpl t).2 i, hi]⟩
  have hPins : ∀ t, (F t).Pins (w₀ t) := fun t =>
    { inj := (hpl t).1
      places := fun p => by
        show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
        rw [Finset.mem_image]
        exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
      kom := fun j hj => hkom t j hj
      mid := fun j σ h => ⟨(_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, ((hrow t).sBF j (σ + 1) h).2.2.1, ((hrow t).sBF j (σ + 1) h).2.2.2,
        ((hrow t).sFB j σ h).2.2.1, ((hrow t).sFB j σ h).2.2.2⟩
      lastc := fun j h => ((hrow t).sBF j 0 h).2.2.2
      eQ := fun j hj => if_pos hj
      eQT := fun j h => rfl
      dQ := fun j hj α γ => if_pos hj
      ε := fun j ρ' h α => if_pos (Or.inl ⟨ρ', h⟩)
      εT := fun n h β => rfl
      FY := fun j _ f hf => hf
      cQ := fun j _ => rfl }
  have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
    have h1 := ha.vis.bT
    rw [((ha.tie row col).1.bT).1] at h1
    exact h1
  have hOK : (a.fam row col).ColOK :=
    { kom := fun t j hj => hkom t j hj
      ker := fun t j hj α γ => by
        have hx := haT.pinX.xs j (by omega)
        have hx' := haT.pinX.xs (j + 1) (by omega)
        have hL : ((a.g.x j).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx.2.2 z)
        have hL' : ((a.g.x (j + 1)).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx'.2.2 z)
        have hv : IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ (a.g.x j).s (a.g.x (j + 1)).s ((a.g.x j).L : Set _)
            ((a.g.x (j + 1)).L : Set _) (a.g.vac j) := by
          rw [hx.1, hx'.1, hL, hL']
          exact haT.pinX.vc j hj
        exact ⟨⟨_, _, hkom t j hj⟩, hv, (hdd t j α γ hj).1⟩
      e := fun t j α g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        exact (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α x (Finsupp.support_smul hx)).2
      eT := fun t n h β g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        have : x = 1 := by
          exact Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hx))
        subst this
        simpa using hbT
      stabK := fun t j hj ψ hψ => GlobalTheory.T.chainKernel_preserves_ramifiedForms_liveCharts I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) (J t).Ch₀ (J t).Ch (J t).A (J t).ι
        (hJ t).is (hJ t).live j hj ψ hψ
      stabS := fun t j hj ψ hψ => (hS' t).1 j hj (k.ε j) ψ hψ }
  have hcv : ∀ t, CVEq k.v (w t) := fun t => by
    refine ⟨fun j σ h => ?_, fun j h => ?_⟩
    · have hex : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := ⟨σ, h⟩
      have hk : ∀ σ' (h' : j + 2 * (σ' + 1) + 2 = B.R.m), k.v.kap j σ' h' = k.v.kap j σ h := fun σ' h' => by
        obtain rfl : σ' = σ := by omega
        rfl
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_pos hex, hk]
      rfl
    · have hex : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := fun ⟨σ, h'⟩ => by omega
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_neg hex]
      rfl
  have hroot : ∀ (Sp : ℕ → Prop) (x : ℂ), (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → ∀ y : ℂ, (∃ n : ℕ, 0 < n ∧ y ^ n = 1) → ∀ c : ℂ, c ≠ 0 →
      GlobalTheory.Fam.UnitRatio Sp (c * x) (c * y) := fun Sp x ⟨n1, hn1, hx⟩ y ⟨n2, hn2, hy⟩ c hc => by
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hy
      exact zero_ne_one hy
    refine (GlobalTheory.Fam.unitRatio_laws Sp).2.2.1 _ _ (n1 * n2) (mul_ne_zero hc hy0) (Nat.mul_pos hn1 hn2) ?_
    rw [mul_pow, mul_pow, pow_mul x, hx, pow_mul' y, hy, one_pow, one_pow]
  have hsum : ∀ t, ∑ β, s t B.R.m β = s t B.R.m (β₀ t) := fun t =>
    Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb)
  refine
    { ok := hOK
      pins := hPins
      same := fun t => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      laws := fun t => _root_.GlobalTheory.T.true_geometry_family_final_alt hDS hHC W hW u a ha haT row col (hRow col) hOK t (F t) (w₀ t) (s t) (hD t).1 (hPins t) (hQ t)
      lev := fun t => _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt W hW u a ha haT t (J t) (hJ t) row col (F t) rfl rfl (fun i => HEq.rfl)
      vec := fun t => _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) _ t
      FY := fun t j f => Iff.rfl
      FT := fun t f => Set.mem_univ f
      FX := fun t j _ ψ _ α y => Set.mem_univ _
      atQ := fun t j => by
        obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j
        refine ⟨h1, h2, fun α γ x hx => h3 α γ x (Finsupp.support_smul hx)⟩
      e := fun t j α => ⟨rfl, fun g hg => (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α g (Finsupp.support_smul hg)).1⟩
      eT := fun t n h β => ⟨rfl, fun g hg => by
        have hg' := Finsupp.support_single_subset (Finsupp.support_smul hg)
        rw [Finset.mem_singleton.1 hg']
        exact Subgroup.one_mem _⟩
      dd := fun t j hj α γ f _ => by
        rw [hdQ t j α γ hj]
        exact (hdd t j α γ hj).2 f
      read := fun t => ⟨S' t 0, (hS' t).2 row kom dd s cV cK cP⟩
      sc := fun t => rfl
      cT := fun t j ρ' h => (congrArg (@TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j)) ((hrow t).sBF j ρ' h).2.2.2).symm
      cv := hcv
      cK := fun t j hj => hroot _ _ ((hD t).2.2.1 j) _ ((hD _).2.2.1 j) _
        (mul_ne_zero (mul_ne_zero (hV0 j hj) (hC0 j hj)) (haT.pinX.mv j (by omega)).1)
      cP := fun t => by
        show GlobalTheory.Fam.UnitRatio _ (VT * ∑ β, s t B.R.m β) (VT * ∑ β, s _ B.R.m β)
        rw [hsum, hsum]
        exact hroot _ _ ((hD t).1 _ _) _ ((hD _).1 _ _) _ hVT0
      zero := _root_.GlobalTheory.T.true_geometry_joint_twist_bound_alt W hW u a ha haT J hJ row kom dd _ s cV cK cP (fun t α => (hD t).2.1 α) hPinCh }
end
end
