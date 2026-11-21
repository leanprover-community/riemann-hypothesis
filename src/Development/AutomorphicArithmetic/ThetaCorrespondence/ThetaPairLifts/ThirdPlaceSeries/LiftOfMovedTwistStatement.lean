import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeqStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.MvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
section Gen
variable {D : D7} (N : TwNew D)
def sideA_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE :=
  { bare := A.bare
    wdT := A.wdT
    lab := A.lab
    chr := { A.chr with }
    row := N.row A.row
    pl := { A.pl with }
    iota := A.iota
    wd := { A.wd with }
    grp := { A.grp with }
    par := { A.par with }
    au := { A.au with }
    chiT := A.chiT }
end Gen
end GlobalTheory.HeightCounting.Up.LiTw
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr GlobalTheory.LayerMove
noncomputable section
namespace UpperTheory.One.M
set_option maxHeartbeats 4000000
def stageAOfSwitch (s : _root_.UpperTheory.One.M.TrivialCondition) {D : D7} (N : TwNew D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := _root_.GlobalTheory.HeightCounting.Up.LiTw.sideA_alt N a.A
  cg := _root_.UpperTheory.One.M.New.cgMk s a.cg.e (_root_.UpperTheory.One.M.New.cgGood s a.cg) (_root_.UpperTheory.One.M.New.cgSurj a.cg) a.cg.zero a.cg.loc a.cg.tw a.cg.inf a.cg.csd
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax
end UpperTheory.One.M
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
section Gen
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}
def liftOfMovedTwist {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp) where
  a := (by with_unfolding_all exact (((_root_.UpperTheory.One.M.stageAOfSwitch trivial) N l.a ((by with_unfolding_all exact ((repOf r.Y) :))) ((by with_unfolding_all exact (e :)))) :))
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := (by with_unfolding_all exact ((cusp N l.cusp) :))
theorem li_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G1 : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB (N := N) ((by with_unfolding_all exact (r.Y :))) μ h i y := fun μ h i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H1 ((μ)) ((h)) ((i)) ((y)))) : _)))
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  refine Exists.intro (_root_.GlobalTheory.HeightCounting.Up.LiTw.liftOfMovedTwist l _ hc hh r hp e ((by with_unfolding_all exact ((inMt (N := N) ((r.Y)) ((G1)) l.mt) : _))) ((by with_unfolding_all exact ((inRat (N := N) ((r.Y)) ((G2)) l.rat) : _)))) ?_
  exact (by with_unfolding_all exact ((And.intro (HEq.refl (N.row l.a.A.row)) (And.intro (HEq.refl l.Pq) (And.intro (HEq.refl (N.rat l.rat.S))
    (And.intro (HEq.refl l.rat.In.Sb) (And.intro (HEq.refl l.rat.In.hL) (And.intro (HEq.refl l.rat.In.eig) (HEq.refl l.rat.In.θ))))))) :))
end GlobalTheory.HeightCounting.Up.LiTw
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_package_twist_heq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt
end
end
