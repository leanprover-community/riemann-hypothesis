import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyRowData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneCentralPinStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreDataOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConsistentRowChoicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConsistentRowChoices
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvarianceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsLinksOfGeoRowsColsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeEqBaseOffTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceChiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkZeroOfChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownwardStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownward
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEvalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEval
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkOntoOfOntoAllStatement

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.FamInhab
open GlobalTheory.Fam.Inhab
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)
section Read
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {At : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C At Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)
variable {K}
end Read
section Real
open GlobalTheory.MiS
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word)
variable {W}
theorem rec_tie_mult_h_pk_z : Formalism.IndefR.RecTie.TopMultH (_root_.GlobalTheory.Fam.pk_z W) :=
  (GlobalTheory.DefiniteMult.topMult_and_extV_injective D _ _ _ _ _ (_root_.GlobalTheory.Fam.pk_z W) _ W.Q.charW.base).1
end Real
end GlobalTheory.Fam.FamInhab
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
theorem GlobalTheory.Fam.LiftSide.exists_characters_is_and_same_of_pkHyp : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ g : GlobalTheory.Fam.Geo D, ∃ r : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t, (∀ t, (r t).Is) ∧ ∀ t t', (r t).Same (r t') := by
  intro hC D L hT Gi Gl Kc Yd cX ex W u hW g
  have h := hW.bot.hyp.2.2.2.1
  exact ⟨_, fun t => GlobalTheory.Fam.FamInhab.rowOf_is _ hC h.lev h.models h.chain _root_.GlobalTheory.Fam.FamInhab.rec_tie_mult_h_pk_z u g t,
    fun t t' => GlobalTheory.Fam.FamInhab.rowOf_same _ hC h.lev h.models h.chain _ u g t t'⟩
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
theorem _root_.GlobalTheory.T.exists_pairwise_same_choices_at_geo : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ g : GlobalTheory.Fam.Geo D, ∃ r : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t, (∀ t, (r t).Is) ∧ ∀ t t', (r t).Same (r t') := by
  atlas_forward_decl _root_.GlobalTheory.Fam.LiftSide.exists_characters_is_and_same_of_pkHyp
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
theorem _root_.GlobalTheory.T.true_geometry_family_invariance_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  atlas_forward_decl _root_.GlobalTheory.Fam.colSide_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem lattice_eq_base_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ p, p ∉ a.v.tP → GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) (a.g.x 0).L (· = p) = GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft (I.rec7 l Z).host.E (I.rec7 l Z).host.E (finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 (I.rec7 l Z).host.E))) (· = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr row col hc p hp
  obtain ⟨hs⟩ := hW.tr.std
  obtain ⟨k, hk⟩ := (hs u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hx := (hTr.pinX.xs 0 (Nat.zero_le _)).2.2
  have hlb := hk.lb ()
  have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
  have hd : ((B.T u : ℕ) : ℤ) ≠ 0 := fun h => hTp (by rw [h]; simp)
  have h1 : ((1 : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    rw [Int.cast_one]; exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set e := finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) with he
  have hpi : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := by
    refine ⟨⟨B.host.conj (X.piT u : B.host.E), map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2⟩, ?_⟩
    apply RingOfIntegers.ext
    have := X.piT_norm u
    push_cast
    exact this.symm
  refine le_antisymm (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ ((B.T u : ℕ) : ℤ) hd ?_ p hTp)
    (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ 1 one_ne_zero ?_ p h1)
  · intro y hy
    have hyi : ∀ j, IsIntegral ℤ (y j) := (hx y).1 hy
    refine Submodule.mem_map.2 ⟨fun j => (((B.T u : ℕ) : ℤ) • y) (e.symm j), (hlb _).2 fun j => ?_, ?_⟩
    · refine ⟨((B.T u : ℕ) : 𝓞 B.host.E) * ⟨y (e.symm j), hyi _⟩, ?_, fun _ => dvd_mul_of_dvd_left hpi _⟩
      show (((B.T u : ℕ) : ℤ) • y) (e.symm j) = _
      rw [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    · funext i
      show (((B.T u : ℕ) : ℤ) • y) (e.symm (e i)) = _
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hxm, rfl⟩
    rw [one_smul]
    refine (hx _).2 fun j => ?_
    obtain ⟨r, hr, -⟩ := (hlb x).1 hxm (e j)
    show IsIntegral ℤ (x (e j))
    rw [hr]; exact r.2
end GlobalTheory.Fam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamPlaced
section Prim
open GlobalTheory.FinPl
end Prim
theorem placedP_of_allTrue : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hT' row col hc
  refine ⟨a.k, a.fld, a.val, a.top, a.loc, a.ι, a.v, a.o, a.n, a.G, a.pl, hc, ha.vis, (ha.tie row col).1, ha.shape, ha.gpin,
    (ha.tie row col).2, ?_, ?_⟩
  swap
  · intro p hp b hb
    have hx := (hT'.pinX.xs B.R.m le_rfl).2.2
    have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
      intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
    have hpos : 0 < B.R.N B.R.m := B.R.N_pos _
    refine prim_std _ _ hx p _ (fun i => ?_)
      (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)
      (B.host.conj (X.piT u : B.host.E)) (map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2)
      ((B.T u : ℕ) : ℤ) ?_ hTp b hb
    · refine (hT'.z0 i).symm ▸ ?_
      show IsIntegral ℤ (TC.z0 X u _)
      unfold TC.z0
      split_ifs
      · exact (X.piT u).2
      · exact isIntegral_zero
    · have h0 : TC.z0 X u ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩ = (X.piT u : B.host.E) :=
        if_pos (Nat.sub_add_cancel hpos)
      have h1 := (hT'.z0 (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm
        ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)).trans h0
      have h2 : (X.piT u : B.host.E) * B.host.conj (X.piT u : B.host.E) = (((B.T u : ℕ) : ℤ) : B.host.E) := by
        rw [Int.cast_natCast]; exact X.piT_norm u
      exact (congrArg (fun t : B.host.E => t * B.host.conj (X.piT u : B.host.E)) h1).trans h2
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  constructor
  · exact ha.bot.1
  · exact ha.bot.2.2.1
  · refine ⟨1, -(I.rec7 l Z).host.xi0 ^ ((I.rec7 l Z).R.m / 2), by simp, ?_, ?_⟩
    · intro r; rw [one_mul]; exact ha.bot.2.2.2 r
    · exact ha.norm.2
  · exact fun i => (ha.stdG i).2.2
  · exact _root_.GlobalTheory.Fam.lattice_eq_base_off_twist_alt W hA u a ha hT' row col hc
  · intro κ hκ y e
    exact ⟨_root_.GlobalTheory.T.true_geometry_local_data_alt W hA u a ha hT' row col hc κ hκ y e, _root_.GlobalTheory.T.true_geometry_reduction_level_alt W hA u a ha hT' row col hc κ hκ y e⟩
end GlobalTheory.FamPlaced
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_p_of_true_geometry : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  atlas_forward_decl _root_.GlobalTheory.FamPlaced.placedP_of_allTrue
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem linkZero_of_chartZero_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), _root_.GlobalTheory.MiTop.ChartAtZeroCondition f → (∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, d.B.lev = f.c.B 0 D.R.rS h₀) → d.b = (show GA D (D.sp.Y 0) from f.g.b 0) → _root_.GlobalTheory.MiTop.LinkVanishes f d := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hc hl hb n h₀ t φ
  obtain ⟨α₀, h1, h2, h3, -⟩ := hc t
  refine ⟨(h3 φ).1, fun G y v => ?_⟩
  obtain rfl : n = D.R.rS := by
    have : D.R.rS = D.R.m / 2 - 1 := rfl
    omega
  have e : ∀ g : GA D (Yc D 0) → ℂ, trc (Finsupp.single (f.g.b 0) 1) g = rTrans (f.g.b 0) g := fun g => by
    unfold trc
    rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  unfold _root_.GlobalTheory.MiTop.BottomData.per Tup.per Tup.perF
  rw [Finset.sum_eq_single α₀ (fun b _ hb => absurd (h1 b) hb) (by simp)]
  beta_reduce
  rw [h2, (h3 φ).2 y, hb]
  exact besLev_per_congr (hl h₀).symm _ HEq.rfl (heq_of_eq (e _))
end GlobalTheory.MiTop
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkZero_of_chartZero' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), _root_.GlobalTheory.MiTop.ChartAtZeroCondition f → (∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, d.B.lev = f.c.B 0 D.R.rS h₀) → d.b = (show GA D (D.sp.Y 0) from f.g.b 0) → _root_.GlobalTheory.MiTop.LinkVanishes f d := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.linkZero_of_chartZero_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopLevelP
section Package
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Package
theorem vector_of_mem_cxp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  exact mem_CXP_of_good (_root_.GlobalTheory.Fam.pk_z W) hC.grp.red_R hC.models.jX hC.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
    (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ⟨F, rfl⟩ ((hP.hTop t).le ⟨_, rfl⟩)
end GlobalTheory.TopLevelP
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
theorem _root_.GlobalTheory.T.vector_of_mem_extra_projection : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.Fam.leadingLinearMap W t F ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t := by
  atlas_forward_decl _root_.GlobalTheory.TopLevelP.vector_of_mem_cxp
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GoodFix
open Formalism.L2.DIV
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev
end GlobalTheory.GoodFix
open GlobalTheory.GoodFix in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) (v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec), (_root_.GlobalTheory.Fam.pk_z W).e0 ((_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v)) = (_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F v
  have hC := hP.bot.hyp.2.2.2.1
  have hL := hP.lev
  unfold _root_.GlobalTheory.MiS.LevelHypothesis at hL
  obtain ⟨⟨s, hs⟩, -⟩ := hL
  have hgf := good_fix (W.P.A3.A.fam.R t) (W.P.A3.A.fam.lvl W.Q.F.P1 W.Q.F.ψ1) hs.ok2.irr F
  exact goodProjector_fixes_compositeThetaLift_of_fixed GlobalTheory.T.cusp_forms_rapid_decay (_root_.GlobalTheory.Fam.pk_z W) hC.lev hC.models hC.chain hC.grp.red_R t _ hgf v
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
theorem _root_.GlobalTheory.T.e_zero_theta_descent_eval_alt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) (v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec), (_root_.GlobalTheory.Fam.pk_z W).e0 ((_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v)) = (_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v) := by
  atlas_forward_decl _root_.GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis
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
namespace GlobalTheory.RowDescent
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev geometricDatumOfFamily (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H :=
  (_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)
theorem apex_eq_toMap_geometricDatum (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) :
    _root_.GlobalTheory.Fam.leadingLinearMap W t F = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F)) := rfl
theorem dn_fst_eq_dnFrom_fst {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (_root_.GlobalTheory.Fam.pk_z W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (_root_.GlobalTheory.Fam.pk_z W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k ((_root_.GlobalTheory.Fam.pk_z W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2
theorem dnFrom_fst_eq_of_heq (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (_root_.GlobalTheory.Fam.pk_z W).CC t k) (X' : (_root_.GlobalTheory.Fam.pk_z W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) k X).1 = (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]
theorem heq_eq_rec_apply (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (_root_.GlobalTheory.Fam.pk_z W).CC t n) g p) z) (g z) := by
  subst p
  rfl
set_option maxHeartbeats 1000000 in
theorem down_eq_thDn {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((_root_.GlobalTheory.Fam.pk_z W).HX t).H)
    (hG : G.1 = (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e y)) : _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := _root_.GlobalTheory.RowDescent.dn_fst_eq_dnFrom_fst f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)) =
      ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := _root_.GlobalTheory.RowDescent.dnFrom_fst_eq_of_heq W t (idx_top h) (ioXT (_root_.GlobalTheory.Fam.pk_z W) t (2 * n) h ⟨G.1, h'⟩) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)
    (_root_.GlobalTheory.RowDescent.heq_eq_rec_apply W t (idx_top h) ((_root_.GlobalTheory.Fam.pk_z W).ioX t) _)
  have e3 : (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t ⟨G.1, h'⟩)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((_root_.GlobalTheory.Fam.pk_z W).CC t) ((_root_.GlobalTheory.Fam.pk_z W).ioY t) (D.R.m - 1) ((_root_.GlobalTheory.Fam.pk_z W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (_root_.GlobalTheory.Fam.pk_z W).thDn t y := e1.trans (e2.trans e3)
  unfold _root_.GlobalTheory.MiTop.descentToLevelZero
  exact key
theorem piTensorProduct_lift_postOn_eq_of_fixed (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (T : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec, (_root_.GlobalTheory.Fam.pk_z W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((_root_.GlobalTheory.Fam.pk_z W).MY 0) (_root_.GlobalTheory.Fam.pk_z W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]
end GlobalTheory.RowDescent
end
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.linkDown_of_ok : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  refine ⟨⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩, rfl, ?_⟩
  have e1 := _root_.GlobalTheory.RowDescent.down_eq_thDn f t (hR.row t) n h ⟨_root_.GlobalTheory.Fam.leadingLinearMap W t F, _root_.GlobalTheory.T.vector_of_mem_extra_projection W hP t F⟩
    (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F) (_root_.GlobalTheory.RowDescent.apex_eq_toMap_geometricDatum W t F)
  have hC : (_root_.GlobalTheory.Fam.pk_z W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : _root_.GlobalTheory.MiTop.rowFormOfTuple W t F = PiTensorProduct.lift ((_root_.GlobalTheory.Fam.pk_z W).HE.e ((_root_.GlobalTheory.Fam.pk_z W).Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (_root_.GlobalTheory.RowDescent.geometricDatumOfFamily W t F))
  have e4 := _root_.GlobalTheory.RowDescent.piTensorProduct_lift_postOn_eq_of_fixed W _ (_root_.GlobalTheory.T.e_zero_theta_descent_eval_alt_alt W hP t F)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
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
theorem _root_.GlobalTheory.T.linkDown_of_famCh : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → _root_.GlobalTheory.MiTop.LinkDescends f := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.linkDown_of_ok
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MiTop
theorem famAllQ_of_allTrue_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → 1 ≤ B.R.rS → GlobalTheory.ChainOnto.OntoAll (I.rec7 l Z) → _root_.GlobalTheory.MiTop.FamilyAllConditions W := by
  intro hCD hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hA hr ho
  have hpk := hA.pk
  obtain ⟨z, hzC, hzZ, hz⟩ := _root_.GlobalTheory.T.exists_botDat_of_placedP_framed W hpk hr
  refine ⟨z, hzC, hzZ, fun u => ?_⟩
  obtain ⟨a, haI, haT, haO, haF⟩ := _root_.GlobalTheory.T.all_true_family_datum_alt hDS hHC hSA W hA u
  obtain ⟨row, hrI, hrS⟩ := _root_.GlobalTheory.T.exists_pairwise_same_choices_at_geo hCD W u hpk a.g
  have hcol := fun k => _root_.GlobalTheory.T.true_geometry_family_invariance_alt hDS hHC W hA u a haI haT haO k row hrI hrS
  obtain ⟨col, hOK, hLaws, hCZ, hTail, hComm, hRat⟩ :=
    _root_.GlobalTheory.T.true_geometry_family_column_data_alt hDS hHC hSA W hA u a haI haT row hrI hrS hcol
  have hc : (a.fam row col).c.Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hpk (a.fam row col) hOK).1
  have hPl := _root_.GlobalTheory.T.placed_p_of_true_geometry W hA u a haI haT row col hc
  obtain ⟨d, hdB, hdb, hdz⟩ := hz u (a.fam row col) a.d.B hPl haF
  refine ⟨a.fam row col, d, hdz, hLaws, ?_, hTail, _root_.GlobalTheory.T.linkDown_of_famCh W u hpk _ hOK, _root_.GlobalTheory.T.linkOnto_of_ontoAll' W u hpk ho _ hOK, hComm, hRat⟩
  refine _root_.GlobalTheory.T.linkZero_of_chartZero' W u (a.fam row col) d hCZ (fun h₀ => ?_) hdb
  rw [hdB]
  exact haI.bot.1 h₀
end GlobalTheory.MiTop
end
end
