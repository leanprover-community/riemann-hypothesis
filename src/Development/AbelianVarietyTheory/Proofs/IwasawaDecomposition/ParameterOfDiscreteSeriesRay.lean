import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LambdaPrimeEqLambdaThree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLiftTwistedModelIffUntwisted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLamAreShift

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.IndefR.RecTie GlobalTheory.LamPrimeTransport
open scoped InnerProductSpace

set_option maxHeartbeats 4000000 in

theorem eigenvalue_of_part : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) π = R.lam3 i A3.A.μ0 c A3.A.v0 := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π p hne hle
  have hC := hP.char
  have hEx := hH.aux.ex
  have hA := hH.prim.thmA
  have hGE := hH.prim.gEquiv
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hC.base.thP hEx
  have hM : R.toRealDat.IsModels := hC.base.models
  have hμ : Used0 D D.what₂.mu0 := Or.inl rfl
  have hT := Y.tied.lift
  have htup : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hread := thetaP_read R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hC.base.lev hC.base.grp hM hE Y.IL hT D.what₂.mu0 hμ i
  rw [← htup]
  refine hT.lamP D.what₂.mu0 hμ i π _ hne fun y hy' => ?_
  have hw0p : Y.mj.eW i y ∈ R.Wp3 i p := hle hy'
  have hw0e : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) = (Y.IL.jMj i y).1 := (Y.mjRead i y).symm
  have hw0W : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) ∈
      (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [hw0e]; exact (Y.IL.jMj i y).2
  have haS := GlobalTheory.LamPrimeTransport.adjoint_mem_base_level R F hCRD hC hEx hGE Y.tupT Y.hm Y.hTop Y.hinj i (Y.mj.eW i y) hw0W
  obtain ⟨a, ha⟩ : ∃ a, LinearMap.adjoint (R.thG i (Y.tupT D.what₂.mu0)) (Y.mj.eW i y) = a := ⟨_, rfl⟩
  rw [ha] at haS
  obtain ⟨x', hx'⟩ : ∃ x', Y.IL.jMt D.what₂.mu0 hμ i x' = ⟨R.toRealDat.extV i (Y.tupT D.what₂.mu0) a, haS⟩ :=
    ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hprex : pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x') = a := by
    apply Y.hinj i (Y.tupT D.what₂.mu0)
    rw [ext_pre, hx']
  have hTx : D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = x' := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : ⟪u, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y⟫_ℂ = ⟪D.what₂.thetaP D.what₂.mu0 ((i : ℕ) + 1) u, y⟫_ℂ :=
      LinearMap.adjoint_inner_right _ _ _
    rw [e1, hT.mj i, hT.mt D.what₂.mu0 hμ i, hread u, ← hw0e]
    erw [ipWc_lift R.toRealDat hM.HW F.lv2 Y.tupT Y.hm Y.hTop Y.hinj i]
    rw [← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i u),
      ← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x'),
      ipA_ext, hprex, ← ha, LinearMap.adjoint_inner_right]
  rw [hTx]
  apply (Y.IL.jMj i).injective
  apply Subtype.ext
  rw [hread x', hprex, ← ha, hA i (Y.tupT D.what₂.mu0) p (Y.mj.eW i y) hw0p, LinearEquiv.map_smul, Submodule.coe_smul, ← hw0e]
  rw [map_smul]
  exact map_smul _ _ _

end GlobalTheory.Mem.R3.ScalarComponentUnique
end

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.L2.Col GlobalTheory.HeckeLifts₂

set_option maxHeartbeats 4000000 in

theorem part_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c p : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) → c = p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π c p hne hc hp
  by_contra hcp
  obtain ⟨hW, hHk⟩ := hH.prim.hecke.2
  have hu := untw_of_hH hP.char hHk
  have hd0 := disjoint_eigSum (hu.comm i) (C := SysC A3 i c) (C' := SysC A3 i p) fun y h h' =>
    h.elim fun x hx => h'.elim fun x' hx' => by
      have e : x = x' := funext fun k => D.what₂.embLL.injective ((congrFun hx.2 k).symm.trans (congrFun hx'.2 k))
      subst e
      exact (A3.liftI i A3.A.fam.μ0).excl3 (hH.sep c.1 c.2 p.1 p.2 (fun h => hcp (Subtype.ext h)) i) x hx.1 hx'.1
  have hd : Disjoint (R.Wp3 i c) (R.Wp3 i p) := hd0.mono (hu.parts i c).le (hu.parts i p).le
  have hinj : ∀ x, Y.mj.eW i x = 0 → x = 0 := fun x hx => by
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero] at h1
    have hn := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 (show RealDat.nP F.lv2 false * ‖x‖ ^ 2 = 0 by rw [← h1]; ring) with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  apply hne
  refine eq_bot_iff.2 fun x hx => ?_
  have h1 : Y.mj.eW i x ∈ R.Wp3 i c := hc hx
  have h2 : Y.mj.eW i x ∈ R.Wp3 i p := hp hx
  exact (Submodule.mem_bot ℂ).2 (hinj x ((Submodule.disjoint_def.1 hd) _ h1 h2))

end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

private theorem logLam_of_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
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

private theorem logLam_twArgs : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HostHyp (w.st Z).toD7 → ∀ (X : DivX (w.st Z).toD7), LamAre t.r.Z X →
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
  have h := logLam_of_part h1 h2 h3 h4 t.r.z.R t.r.z.F t.r.z.cG _ t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange hHost X hX i π c e he hne hle'
  exact (by with_unfolding_all exact (h.1.trans (congrArg Real.log (lam_eq i _ c (InfinitePlace.mk e) h.2).symm) :))

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.parameter_of_discrete_series_ray : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), e ≠ (q.w.D q.Z).what₂.embLL → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  exact logLam_twArgs h4 h5 h6 hCRD K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    (hHost (q.w.st q.Z) q.x.isOver).1 q.O.X q.x.ox.lam
end
