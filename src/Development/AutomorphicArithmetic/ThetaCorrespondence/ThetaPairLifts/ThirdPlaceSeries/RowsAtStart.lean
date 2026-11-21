import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtOfExpRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepcongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NchTOfTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
theorem exists_mtAd_psi_vector_of_yRel {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  refine ⟨{ PV := _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l
            std := (by with_unfolding_all exact (l.mt.ad.std :))
            eW := (by with_unfolding_all exact (l.mt.ad.eW :))
            read := fun μ h i y g => ?_
            rat := (by with_unfolding_all exact (l.mt.ad.rat :))
            wt := (by with_unfolding_all exact (l.mt.ad.wt :))
            id := (by with_unfolding_all exact (l.mt.ad.id :)) }, rfl⟩
  have h1 := l.mt.ad.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))
  have h2 := hY.jMt μ h i y
  kexactB h1.trans (congrFun (eq_of_heq h2) _).symm
end GlobalTheory.HeightCounting.Fin3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
theorem real_pin_setup_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.SeriesTie.RealPin (datL x L).R (datL x L).cG (setupL L l.b.ser.ex.ρ) :=
  have p := l.b.ser.ex.pin
  ⟨(by with_unfolding_all exact (p.psi :)), (by with_unfolding_all exact (p.inf :)), (by with_unfolding_all exact (p.cartT :)), (by with_unfolding_all exact (p.onbS :)), (by with_unfolding_all exact (p.onbT :)), (by with_unfolding_all exact (p.latS :)), (by with_unfolding_all exact (p.latT :)), (by with_unfolding_all exact (p.frS :)), (by with_unfolding_all exact (p.frT :)), (by with_unfolding_all exact (p.vac :)), (by with_unfolding_all exact (p.Pg :)),
    (by with_unfolding_all exact (p.grp :)), (by with_unfolding_all exact (p.mu0 :)), (by with_unfolding_all exact (p.eta :)), (by with_unfolding_all exact (p.delta :)), (by with_unfolding_all exact (p.deltaPl :)), (by with_unfolding_all exact (p.ap :)), (by with_unfolding_all exact (p.am :))⟩
theorem is_univ_char_local (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : GlobalTheory.UnivChar.IsUnivChar (DL x L).nexp := (by with_unfolding_all exact (l.b.ser.ex.univ :))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
open GlobalTheory.SeriesTie in
private theorem gens_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).gens = fun i j b k Q ψ h P => (by exact ρ.gens i j b k Q ψ h P) := by
  funext i j b k Q ψ h P
  delta GlobalTheory.SeriesTie.Setup.gens GlobalTheory.ExportSeries.Base.genSet GlobalTheory.ExportSeries.Base.gen GlobalTheory.ExportSeries.Base.vecFlat
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.gens (kc% i) (kc% j) b k (kc% Q) (kc% ψ) (kc% h) (kc% P)))
open GlobalTheory.SeriesTie in
private theorem sum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).sum = fun i j b k Q ψ => (by exact ρ.sum i j b k Q ψ) := by
  funext i j b k Q ψ
  delta GlobalTheory.SeriesTie.Setup.sum GlobalTheory.ExportSeries.Base.classSum GlobalTheory.ExportSeries.Base.vecFlat
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.sum (kc% i) (kc% j) b k (kc% Q) (kc% ψ)))
open GlobalTheory.SeriesTie in
private theorem xi_eq_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (b : Bool) :
    (setupL L ρ).xi i j b (DL x L).nexp =
      fun Q M h P a => (by with_unfolding_all exact ((ρ.xi ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (Dof x).nexp ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :))) (kc% a)) :)) := by
  funext Q M h P a
  delta GlobalTheory.SeriesTie.Setup.xi GlobalTheory.ExportSeries.Base.xiCoef GlobalTheory.ExportSeries.Base.xi GlobalTheory.ExportSeries.Base.vecFam
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.xi (kc% i) (kc% j) b (Dof x).nexp (kc% Q) M (kc% h) (kc% P) (kc% a)))
open GlobalTheory.SeriesTie in
private theorem isHeckeDatum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsHeckeDatum =
      fun i j b k P α R z => (by exact ρ.IsHeckeDatum i j b k P α R z) := by
  funext i j b k P α R z
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.elt), (d.reps), (d.det)⟩ : ρ.IsHeckeDatum ((i)) ((j)) b k ((P)) ((α)) ((R)) ((z))) : _))
  · exact ⟨(by with_unfolding_all exact (d.elt :)), (by with_unfolding_all exact (d.reps :)), (by with_unfolding_all exact (d.det :))⟩
section Cell
open GlobalTheory.SeriesTie
variable {ρ : Setup (Dof x).ntw} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool}
private def rdL_pz (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) : Rd (setupL L ρ) (DL x L).nexp i j c := (rd)
private theorem rat_iff_pz (hρ : ρ.Good) (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) :
    SeriesTie.Rat (setupL_good L hρ) (@rdL_pz K B f T w P x L ρ i j c rd) ↔ SeriesTie.Rat hρ rd := by
  conv_lhs => delta SeriesTie.Rat RatBase RatTwist RatUniv
  rewrite [isDatum_eq L ρ, theta_eq L ρ, gens_eq_pz L ρ, xi_eq_pz L ρ i j c]
  kexactB (Iff.refl (SeriesTie.Rat hρ rd))
private theorem heckeTie_imp_pz {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (h : HeckeTie rd) :
    HeckeTie (@rdL_pz K B f T w P x L ρ i j c rd) := by
  delta HeckeTie HeckeAt
  rewrite [isHeckeDatum_eq_pz L ρ]
  exact (by with_unfolding_all exact (h :))
private def cellL_pz {hρ : ρ.Good} {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (t : CellTie hρ (Dof x).nexp rd) :
    CellTie (setupL_good L hρ) (DL x L).nexp (i := i) (j := j) (b := c) (@rdL_pz K B f T w P x L ρ i j c rd) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [isDatum_eq L ρ]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [isDatum_eq L ρ, theta_eq L ρ]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [theta_eq L ρ]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [gens_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [xi_eq_pz L ρ i j c]; kexactB t.thU_eq
  thU_off := by rewrite [xi_eq_pz L ρ i j c]; kexactB t.thU_off
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := kc% t.mtLat_iff
  thP_eq := by rewrite [sum_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thP_eq :))
private theorem isNormL_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    IsNorm (datL x L).R (datL x L).geo.v₀ ((setupL L ρ).B i j c) ν ↔
      IsNorm x.m.z.R x.m.z.geo.v₀ (ρ.B ((i)) ((j)) c) ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, e, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
    exact ⟨h0, e, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := (oL x L).Z) x.o.Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩
  · obtain ⟨h0, e, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
    exact ⟨h0, e, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := x.o.Z) (oL x L).Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩
end Cell
section Comparison₂
open GlobalTheory.SeriesTie
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem rat_setupL_iff_rat_realRd {ρ : Setup (Dof x).ntw} (h : ρ.Good) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    SeriesTie.Rat (setupL_good L h) (realRd (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν) ↔
      SeriesTie.Rat h (realRd l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :=
  (by with_unfolding_all exact ((@rat_iff_pz K B f T w P x L ρ i j c h (((realRd l.b.YS x.m.z.geo.v₀ h (kc% i) (kc% j) c ν)))) : _))
theorem is_scalar_local_y_structure_of_is_scalar {ρ : Setup (Dof x).ntw} {h : ρ.Good} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool} {ν : ℂ}
    (s : IsScalar l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :
    IsScalar (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν :=
  ⟨s.ne, fun ⟨ν', h'⟩ => (isNormL_pz L ρ i j c ν).2 (s.norm ⟨ν', (isNormL_pz L ρ i j c ν').1 h'⟩),
    fun ⟨ν', h₁, h₂⟩ => (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν).2 (s.rat ⟨ν', (isNormL_pz L ρ i j c ν').1 h₁, (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν').1 h₂⟩)⟩
def localYStructureExportTie : ExportTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ where
  ρ := setupL L l.b.ser.ex.ρ
  good := setupL_good L l.b.ser.ex.good
  pin := _root_.GlobalTheory.HeightCounting.Fin3.real_pin_setup_local L l
  vec := (by with_unfolding_all exact (l.b.ser.ex.vec :))
  ν := (by with_unfolding_all exact (l.b.ser.ex.ν :))
  scalar := fun i j c => _root_.GlobalTheory.HeightCounting.Fin3.is_scalar_local_y_structure_of_is_scalar L l (h := l.b.ser.ex.good) ((by with_unfolding_all exact ((l.b.ser.ex.scalar ((i)) ((j)) c) : _)))
  tie := fun i j c => (by with_unfolding_all exact ((@cellL_pz K B f T w P x L l.b.ser.ex.ρ i j c l.b.ser.ex.good
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.tie (kc% i) (kc% j) c)))) : _))
  hecke := fun i j c => (by with_unfolding_all exact ((@heckeTie_imp_pz K B f T w P x L l.b.ser.ex.ρ i j c
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.hecke (kc% i) (kc% j) c)))) : _))
  univ := _root_.GlobalTheory.HeightCounting.Fin3.is_univ_char_local L l
private def lamL_pz (Z : GlobalTheory.LamTie.LamDat (Dof x)) : GlobalTheory.LamTie.LamDat (DL x L) :=
  ⟨(by with_unfolding_all exact ((chFr (a := x.o.Z) (oL x L).Z ((Z.C))) : _)), (by with_unfolding_all exact (Z.q0 :)), (by with_unfolding_all exact (Z.w0 :)), (by with_unfolding_all exact (Z.c :)), (by with_unfolding_all exact (Z.chi :))⟩
private theorem lamL_ok_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.Ok) : (lamL_pz L Z).Ok := ⟨(by with_unfolding_all exact (h.places :)), (by with_unfolding_all exact (h.aux :)), (by with_unfolding_all exact (h.big :))⟩
private theorem lamL_tie_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z) :
    GlobalTheory.LamTie.IsLamTieFull (DL x L).ntw (lamL_pz L Z) := (by with_unfolding_all exact (h :))
private theorem lamL_C_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.C = cfOf x) : (lamL_pz L Z).C = cfD x L :=
  (by with_unfolding_all exact ((congrArg (fun c : CharFrame (Dof x) => chFr (a := x.o.Z) (oL x L).Z ((c))) h) : _))
def seriesAtLocal (X : Formalism.L2.NExpTied (withLoc L)) (h : ExpRel L l.b.Bs.exp X) :
    SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) where
  ex := _root_.GlobalTheory.HeightCounting.Fin3.localYStructureExportTie L l
  bad := (by with_unfolding_all exact (l.b.ser.bad :))
  ch := (by with_unfolding_all exact (l.b.ser.ch :))
  join := fun i j b k Q ψ hA ht => (by with_unfolding_all exact ((h.reads (kc% i) (j.1 + 1) b k (kc% Q) (kc% ψ) (Nat.le_add_left _ _) (kc% j.2) (kc% hA)
    (l.b.ser.ex.ρ.ek (kc% i) b k)
    (Formalism.IndefR.Links.PolF (Dof x) (Formalism.IndefR.Links.Wc (Dof x) (kc% j)).rank (Formalism.IndefR.Links.Vc (Dof x) (kc% j)).rank)
    (fun f g => (l.b.ser.ex.tie (kc% i) (kc% j) b).rdV k (kc% Q) (kc% ψ) (kc% f)
      ((Formalism.L2.Theta.finHom _).rangeRestrict ((l.mt.ad.PV (kc% j)).ψ (kc% g))))
    (kc% (l.b.ser.join (kc% i) (kc% j) b k (kc% Q) (kc% ψ) (kc% hA) (kc% ht)))) :))
  sup := kc% l.b.ser.sup
  off := (by with_unfolding_all exact (l.b.ser.off :))
  lam := lamL_pz L l.b.ser.lam
  lam_ok := lamL_ok_pz L l.b.ser.lam_ok
  lam_teich := (by with_unfolding_all exact (l.b.ser.lam_teich :))
  lam_C := lamL_C_pz L l.b.ser.lam_C
  lam_q := (by with_unfolding_all exact (l.b.ser.lam_q :))
  lam_tie := lamL_tie_pz L l.b.ser.lam_tie
end Comparison₂
end GlobalTheory.HeightCounting.Fin3
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.series_at_local_of_exp_relation : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (X : Formalism.L2.NExpTied (withLoc L)), ExpRel L l.b.Bs.exp X → Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l)) :=
  fun L l X h => ⟨_root_.GlobalTheory.HeightCounting.Fin3.seriesAtLocal L l X h⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem hecke_expansion_heightData_of_levelC {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) : NExpHeckeRowX x.m.z.R x.m.z.cG _ l.b.YS (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) fun _ => LinearMap.id :=
  hkRow_of_ad x.m.z.R x.m.z.cG l.rat.kKs l.rat.hk l.b.YS (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l) l.rat.In.Sb l.b.fi l.b.Sb_le l.rat.rat.hecke
theorem hecke_expansion_datL_of_levelC {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) :
    NExpHeckeRowX (datL x L).R (datL x L).cG _ (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l) fun _ => LinearMap.id :=
  ⟨(by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.hecke_expansion_heightData_of_levelC l).tie :))⟩
end GlobalTheory.HeightCounting.Fin3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_expansion_local_of_levelC : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), NExpHeckeRowX (datL x L).R (datL x L).cG _ (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l) fun _ => LinearMap.id := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Fin3.hecke_expansion_datL_of_levelC
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
section Gen
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))
theorem hkDat_of_hkDat_datL (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {i k Q α Rr} (h : HkDat (datL x L).R (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(h.split), (h.offS), (h.odd), (h.le), (h.elt), (h.reps)⟩
theorem eigVec_eW_of_hkDat_good_index (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (eigAd_iff_eigVec x.r.Y l.rat.In.Sb l.rat.In.eig).mp l.rat.rat.eig i σ k Q α Rr hd hσ y hy)
theorem eigAd_smallPlaceSet_of_yRel (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) (_root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l) :=
  (eigAd_iff_eigVec _ _ _).2 fun i σ k Q α Rr hd hσ y hy =>
    (by with_unfolding_all exact ((EigVec.congr (v' := ((Y.mj.eW i y))) (eigVec_loc L (_root_.GlobalTheory.HeightCounting.Fin3.eigVec_eW_of_hkDat_good_index l ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((_root_.GlobalTheory.HeightCounting.Fin3.hkDat_of_hkDat_datL L l hd))) ((hσ)) ((y)) ((hy))))
      (((hY.eW i y)))) : _))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigAd_of_yRel_at_level_c : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → EigAd Y (_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l) (_root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l) := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Fin3.eigAd_smallPlaceSet_of_yRel
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Fin3
theorem emtTheta_L_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0)
    (hY : YRel L Y) : EMtTheta Y (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) := by
  intro v i hv y hy n a f h
  have h2 := HEq.trans (heq_of_eq h) (hY.eW i _)
  exact (by with_unfolding_all exact ((l.c.th ((v)) ((i)) ((hv)) ((y)) ((hy)) n ((a)) ((f)) (((eq_of_heq h2)))) : _))
end GlobalTheory.HeightCounting.Fin3
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.emtTheta_of_yRel : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → EMtTheta Y (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Fin3.emtTheta_L_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.HeightCounting.Fin3
theorem grpTie_of_LC_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'
end GlobalTheory.HeightCounting.Fin3
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpTie_of_levelC : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1 (x.m.z.R.eG.trans x.m.z.cG) := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Fin3.grpTie_of_LC_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.NchAt
set_option maxHeartbeats 4000000 in
theorem tie_of_true_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'} {tp' : TupTied D' cf' C'}
    (b : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') : NChTie D' C' ∧ PsiChoiceCompatible D' cf' C' tp' := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := b
  subst eq
  cases pack
  refine ⟨⟨Sp.twOf_eq, Sp.twSide_eq, fun a => ?_, ?_, ch.nct.embedding_baseField_condition⟩, ch.psi⟩
  · exact (Sp.Q_eq _ _ a (((L.X.nd.locs_mem _ _ a).2 ⟨rfl, rfl⟩))).trans (Sp.Qc_eq _ _)
  · obtain ⟨ψ0, hc, hw, -⟩ := ch.nct.psi_eq
    exact ⟨ψ0, hc, hw, fun a g => Sp.psi_eq a g _ (hw _ g)⟩
end GlobalTheory.HeightCounting.NchAt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem mtInput_of_levelC : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))
def nTrueAtWeight : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := _root_.GlobalTheory.HeightCounting.Fin3.mtInput_of_levelC l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }
variable (L) in
structure AllLevelsData : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → _root_.Formalism.L2.RowLocTiedAlt (withLoc L) a.gal.lp F
variable (al : _root_.GlobalTheory.HeightCounting.Fin3.AllLevelsData l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))
theorem pq_weight_eq (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)
def weightedAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := _root_.GlobalTheory.HeightCounting.Fin3.nTrueAtWeight l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := fun y => (by with_unfolding_all exact (((congrArg (fun e : (Dof x).host.E →+* Qb => e ((y))) ((al.jE) : ((al.a.gal.fr.jE) : (Dof x).host.E →+* Qb) = l.a.jE)).trans (l.a.frame ((y)))) : _))
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth
def localAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (DL x L) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterTupleAgreement L l) := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.weightedAtData l Sp Au ss al hLg) :))
include l in
variable (L) in
theorem grpTie_famR : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).card :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).e0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).lvl0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).psi0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩
variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)
def normalizedRowDatum : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := DL x L) (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l
  hecke := _root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l
  grp := _root_.GlobalTheory.HeightCounting.Fin3.grpTie_famR l L
  rowLoc := (by with_unfolding_all exact ((al.loc ((by with_unfolding_all exact ((frameY Y) :))) ((by with_unfolding_all exact ((eq_of_heq (kc% hY.rep : HEq (repOf Y) (kc% (repOf x.r.Y) : type_of% (repOf Y)))) :)))) :))
  S_eq := (by with_unfolding_all exact ((SL_heq L l.rat) :))
  hL_eq := (by with_unfolding_all exact ((HEq.refl l.rat.In.hL) :))
  rep_eq := (by with_unfolding_all exact (hY.rep.symm :))
theorem nonempty_nMore_of_xdAll {xd : ThData (Dof x)} (hxd : XdAll xd) : Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (_root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y hY) (datL x L).geo (xdD L xd)) := by
  obtain ⟨ad, had⟩ := _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel L l Y hY
  obtain ⟨ser⟩ := _root_.GlobalTheory.T.series_at_local_of_exp_relation L l al.a.exp al.exp
  have e : (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt = _root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l := (by with_unfolding_all exact (al.mt :))
  have H : ∃ ad' : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt, ad'.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
    rw [e]; exact ⟨ad, had⟩
  obtain ⟨ad', had'⟩ := H
  have ser' : SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L al.a.exp) ad'.PV (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) := had'.symm ▸ ser
  exact ⟨{ ad := ad'
           fi := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal_fi_e_heq L l
           hecke := _root_.GlobalTheory.T.hecke_expansion_local_of_levelC L l
           cHk := (by with_unfolding_all exact ((fun i b Q => (⟨l.b.Bs.cHk i b Q, pow_one _⟩ : ∃ u : ((Dof x).ntw.O i)ˣ, (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk i b 1 Q =
             algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) u)) :))
           eig := ⟨_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l, _root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l, (by with_unfolding_all exact (l.b.Sb_le :)), (by with_unfolding_all exact ((HEq.refl l.rat.In.eig) :)), _root_.GlobalTheory.T.eigAd_of_yRel_at_level_c L l Y hY⟩
           ser := (by with_unfolding_all exact (ser' :))
           tau := (by with_unfolding_all exact ((al.exp.tau l.b.tau) :))
           geo := _root_.GlobalTheory.HeightCounting.Fin3.thetaTie_yStructureLocal_nonempty L l
           ok := _root_.GlobalTheory.HeightCounting.Fin3.twist_ok_local L l
           th := _root_.GlobalTheory.T.emtTheta_of_yRel L l Y hY
           xd := xdD_all L hxd
           large := (by with_unfolding_all exact (hLg :))
           labc := (by with_unfolding_all exact (l.a.labc :))
           zeta := (by with_unfolding_all exact (l.a.zeta :))
           pht := (by with_unfolding_all exact ((⟨l.a.fr, l.a.fr_jE, l.a.pht⟩ : ∃ fr : Formalism.L2.OmFrame (Dof x), fr.jE = l.a.jE ∧ PhtOn l.a.A.wd fr fun _ _ _ _ => True) :)) }⟩
def localCharacterChoiceTwist : NchT w (oL x L).Z P.Wt (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) where
  tp := _root_.GlobalTheory.HeightCounting.Fin3.localCharacterTupleAgreement L l
  xi := (by with_unfolding_all exact (l.c.xi_eq :))
  psi := (by with_unfolding_all exact (l.c.psi_eq :))
  tie := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).1
  Q := fun v hv => ⟨(by with_unfolding_all exact (((congrFun l.c.Q_eq v).trans (GlobalTheory.HeightCounting.Up.Model.qOf_on v hv)) :)),
    (by with_unfolding_all exact ((l.c.k_eq v ((GlobalTheory.HeightCounting.Up.Model.twisted_iff x v).2 hv)) :))⟩
  chrPsi := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).2
include hY in
theorem exists_core_and_listPin {xd : ThData (Dof x)} (hxd : XdAll xd) (t : RowsT K w (oL x L).Z P.Wt p0) (hz : HEq t.r.z (datL x L))
    (ht : HEq t.r.Y Y) : ∃ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg),
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w (oL x L).Z P.Wt p0 t (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg) (xdD L xd) c) ∧
      ∀ cDep : ℝ, ListSt cDep x → ListPin (DL x L) t.r.z.R.toRealDat.toLevCh cDep K.s.b := by
  obtain ⟨hX, ⟨z, intersectionNumber_baseChange, Y', Zr, tix⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := t
  have e : z = datL x L := eq_of_heq hz
  subst e
  have e' : Y' = Y := eq_of_heq ht
  subst e'
  obtain ⟨mo⟩ := _root_.GlobalTheory.HeightCounting.Fin3.nonempty_nMore_of_xdAll l Sp Au ss al hLg Y' hY hxd
  exact ⟨⟨_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg, _root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y' hY, (by with_unfolding_all exact (l.sel :))⟩, ⟨(mo, ⟨bkL L⟩)⟩, fun cDep h => GlobalTheory.T.toricCharacterGridList_kept_localizedStage x L cDep h⟩
omit l in
theorem exists_read_heq_of_eq {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} (e : z = z') {p : BaseLevelRowSide (w.D Z)}
    (Y₀ : Read z.R.toRealDat z.F.lv2 p) : ∃ Y₁ : Read z'.R.toRealDat z'.F.lv2 p, HEq Y₁ Y₀ := by
  subst e
  exact ⟨Y₀, HEq.rfl⟩
omit l in
theorem start_at_all_pre2 : StepW Start fun K _ _ _ w => ∀ P : Pre2 K w, RowsAt P :=
  Step.trans GlobalTheory.Mem.R3.Rw.St.exists_rowsT (Step.of_all fun _ _ _ _ _ _ _ H w hs P => H w ⟨hs.1, ⟨P⟩⟩ P)
end GlobalTheory.HeightCounting.Fin3
end
end
end
