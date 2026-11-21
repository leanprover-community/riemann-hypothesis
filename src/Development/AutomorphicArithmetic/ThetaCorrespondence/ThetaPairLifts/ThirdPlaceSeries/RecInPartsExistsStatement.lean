import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationSideStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParameterOfDiscreteSeriesReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParameterOfDiscreteSeriesReciprocity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParameterOfDiscreteSeriesRay

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.Reads
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
set_option maxHeartbeats 2000000 in
theorem mjRead_of_indefinite_down_join (x : TwIn ex) {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) :
    Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro i v
  have h1 := x.Y.mjRead i (x.Z.jW i v)
  have h2 := x.Z.jW_read i v
  have h3 : x.Y.mj.eW i (x.Z.jW i v) ∈ LinearMap.range (x.Y.mj.eW i) := ⟨_, rfl⟩
  rw [x.Y.mj.eW_range i] at h3
  have h4 := h3.2
  have h5 : Mult.postOn _ (x.R.toRealDat.eWf i (sg0 D x.A3.A)) ((x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v))) =
      (x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v)) := sub_eq_zero.1 h4
  refine h1.trans (congrArg _ ?_)
  rw [← h5, h2]
  rfl
set_option maxHeartbeats 4000000 in
theorem mt_mj_read_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), Holds x.R x.F → Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) ∧ Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y _
  exact ⟨liftGroupForms_eq_extended_rationalForms_companion x, _root_.GlobalTheory.Mem.R3.Reads.mjRead_of_indefinite_down_join x y⟩
end GlobalTheory.Mem.R3.Reads
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.GenRows
set_option maxHeartbeats 4000000 in
theorem goodGeneric_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ a
  have hSer : ∀ k : Fin 2, haveI : Fact ((q.w.st q.Z).toD7.host.g k).Prime := ⟨(q.w.st q.Z).toD7.host.g_prime k⟩
      ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod ((q.w.st q.Z).toD7.host.g k)))
        (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod ((q.w.st q.Z).toD7.host.g k)) C),
        ∀ f, (q.w.st q.Z).toD7.ntypes.eSer k f = Formalism.L2.NT.eSerO O (q.w.st q.Z).toD7.R.r f :=
    fun k => ⟨_, q.core_data_of_point.a.all.types.O k, q.core_data_of_point.a.all.types.eSer_def k⟩
  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  exact (GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation a.x.R a.x.F a.x.pins.char 1 a.intersectionNumber_baseChange.ok hSer).1
end GlobalTheory.Mem.R3.GenRows
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.GenRows.goodGeneric_rows_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 4000000 in
private theorem logLam_of_part_pz : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D →
    ∀ (X : DivX D), LamAre Z X → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    X.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e)) ∧ R.EEp3 c ≠ ⊥ := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost X hX i π c e he hne hle
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost π
  obtain ⟨lab, hl, hv⟩ := hX
  have hov : OverIx Z π (lab π) := hl π ⟨p, fun j => by
    rw [rat j p]
    exact Submodule.map_le_iff_le_comap.1 (hp.1 j)⟩
  have hi := hov i
  rw [rat i (lab π)] at hi
  have hc : c = lab π := GlobalTheory.Mem.R3.ScalarComponentUnique.part_unique R F cG X0 Y hP hH i π c (lab π) hne hle hi
  refine ⟨?_, fun hb => ?_⟩
  · rw [(hv i π e he).1 hne, hc]
    rfl
  · have hW : R.Wp3 i c = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun s hs => ?_)
      have hs' : R.EEc s ≤ R.EEp3 c := le_iSup₂_of_le (f := fun s (_ : R.Carries c s) => R.EEc s) s hs le_rfl
      rw [hb] at hs'
      exact absurd (le_bot_iff.1 hs') hs.1
    apply hne
    refine eq_bot_iff.2 fun x hx => ?_
    have h0 : Y.mj.eW i x ∈ R.Wp3 i c := hle hx
    rw [hW] at h0
    have hx0 : Y.mj.eW i x = 0 := (Submodule.mem_bot ℂ).1 h0
    have hn1 := Y.mj.eW_norm i x
    rw [hx0, norm_zero, zero_pow two_ne_zero] at hn1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hn2 : ‖x‖ ^ 2 = 0 := (mul_eq_zero.1 hn1.symm).resolve_left hn.ne'
    exact (Submodule.mem_bot ℂ).2 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn2))
set_option maxHeartbeats 4000000 in
private theorem logLam_twArgs_pz : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HostHyp (w.st Z).toD7 → ∀ (X : DivX (w.st Z).toD7), LamAre t.r.Z X →
    letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (w.st Z).toD7.R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (w.st Z).toD7.what₂.LL →+* ℂ), e ≠ (w.st Z).toD7.what₂.embLL → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro h1 h2 h3 h4 K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a hHost X hX
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro i π c e he hne hle
  have hW : Y.mj.eW = t.r.Y.mj.eW := by kexactB eq_of_heq heW
  have hle' : (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (t.r.z.R.Wp3 i c).comap (t.r.Y.mj.eW i) := by
    rw [← hW]
    kexactB hle
  have h := logLam_of_part_pz h1 h2 h3 h4 t.r.z.R t.r.z.F t.r.z.cG _ t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange hHost X hX i π c e he hne hle'
  kexactB h.1.trans (congrArg Real.log (lam_eq i _ c (InfinitePlace.mk e) h.2).symm)
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.parameter_of_discrete_series_ray_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), e ≠ (q.w.D q.Z).what₂.embLL → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  exact logLam_twArgs_pz h4 h5 h6 hCRD K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    (hHost (q.w.st q.Z) q.x.isOver).1 q.O.X q.x.ox.lam
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique
set_option maxHeartbeats 4000000 in
theorem scal_rows_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  letI := a.x.grp; letI := a.x.fin; letI := a.x.alg
  intro i π c e hne hle
  by_cases he : e = (q.w.D q.Z).what₂.embLL
  · subst he
    have h := eigenvalue_of_part hCRD a.x.R a.x.F a.x.cG _ a.x.Y a.x.pins a.intersectionNumber_baseChange i π c hne hle
    exact (q.O.X.logLam_base _ π).trans
      (congrArg Real.log (h.trans (congrArg (a.x.R.lam3 i a.x.A3.A.μ0 c) a.x.R.hv0)))
  · exact _root_.GlobalTheory.T.parameter_of_discrete_series_ray_alt hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a i π c e he hne hle
end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.ScalarComponentUnique.scal_rows_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3.RecInAt
set_option maxHeartbeats 4000000 in
theorem recIn_parts_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)), ∃ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow := by
  intro hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM R hR sP sS hP hS a x hax y
  obtain rfl := eq_of_heq hax
  classical
  obtain ⟨hC, -, hxi, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hmt := _root_.GlobalTheory.Mem.R3.Reads.mt_mj_read_alt _ _ _ _ _ _ _ _ q.O.ex a.x R (sS.toRealSpectralMatching R) y a.intersectionNumber_baseChange
  have hFr : Top.Fr.at (q.w.st q.Z) q.f = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z :=
    (congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq.symm).trans rfl
  have hchr := hR.s.chr
  have hC' : a.x.R.C = R.T.n.cf := by
    have h1 := eq_of_heq hC
    rw [h1, hFr]
    exact (congrArg Sigma.fst hchr).symm
  have heig := @GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters hW hDS hHC hCR _ a.x.G a.x.grp a.x.fin _ _ _ a.x.A3 _ _ _ a.x.alg a.x.R a.x.F a.x.cG q.O.ex.p0 a.x.Y a.x.Z q.O.X a.x.pins a.intersectionNumber_baseChange
  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  have hHost : HostHyp (q.w.D q.Z) := (hH (q.w.st q.Z) q.x.isOver).1
  have hgen : ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 :=
    _root_.GlobalTheory.T.geometric_parameter_of_reciprocity_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have hlam : ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ),
      (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) →
      q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) :=
    _root_.GlobalTheory.T.parameter_of_discrete_series_reciprocity_alt hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  obtain ⟨E, labPi, piOf, hparts⟩ := heig hHost hgen hlam
  have key : ∀ (c : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (h : R.T.n.cf = c),
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) h) R.T.n.tp).xi = R.T.n.tp.xi := by
    intro c h; subst h; rfl
  have key2 : ∀ (c1 c2 : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (t1 : Formalism.L2.Host.TupTied (q.w.D q.Z) c1 q.O.ex.nch)
      (t2 : Formalism.L2.Host.TupTied (q.w.D q.Z) c2 q.O.ex.nch), c1 = c2 → HEq t1 t2 → t1.xi = t2.xi := by
    intro c1 c2 t1 t2 h ht; subst h; cases ht; rfl
  obtain ⟨hcf, htp⟩ := Sigma.mk.inj_iff.1 hchr
  have hxiR : R.T.n.tp.xi = q.w.I.xi := (key2 _ _ _ _ hcf htp).trans q.x.n.xi
  have htx : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → a.x.R.toLevCh.xiH (a.x.Y.tupT μ) =
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp).xi μ := by
    intro μ hμ
    rw [key _ hC'.symm, hxiR]
    exact eq_of_heq (hxi μ hμ).2
  refine ⟨⟨E, labPi, piOf, cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp, cast_heq _ _, htx, hmt.1, hmt.2⟩, ?_⟩
  exact hparts
end GlobalTheory.Mem.R3.RecInAt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selected_realization_side_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)), ∃ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow := by
  atlas_forward_decl _root_.GlobalTheory.Mem.R3.RecInAt.recIn_parts_exists_alt
end
end
