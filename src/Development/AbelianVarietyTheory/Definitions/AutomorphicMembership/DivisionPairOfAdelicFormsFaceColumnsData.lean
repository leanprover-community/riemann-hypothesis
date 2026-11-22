module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
public import Lean

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure TwIn (ex : Extra D L hT Gi Gl K Yd cX) : Type 1 where
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  pins : Pins R F cG
  err : ErrEq R F
  Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0
  Z : ReadL R F ex.p0 Y
  C : ReadC R F ex.p0 Y
  sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH
  div : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) ex.p0 (colOf R F sEE) C.NuC (idsOf cG Z C)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup
  amb0 : AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 JA
  JM : MjHIds D A3.A Yd (A3.indefDown (s0Of R F))
  mjH : MjHTie D A3.A Yd (A3.indefDown (s0Of R F)) Z.jW JM

attribute [instance] TwIn.grp TwIn.fin TwIn.alg

variable {ex : Extra D L hT Gi Gl K Yd cX}

set_option maxHeartbeats 2000000 in
@[reducible] def divisionPairOfAdelicFormsFaceColumnsData (x : TwIn ex) : RowSideFamily ex where
  Gp := x.G
  Pl0 := x.Pl0
  I0 := x.I0
  T := x.T
  A3 := x.A3
  P0 := x.F.P0
  ψ0 := x.F.ψ0
  Ps := x.F.P1
  ψs := x.F.ψ1
  Zs := zsOf x.R x.F
  S0 := s0Of x.R x.F
  S1 := s1Of x.R x.F
  Dc := x.F.Dc (zsOf x.R x.F)
  Sp := x.F.Sp (zsOf x.R x.F)
  C := colOf x.R x.F x.sEE
  NuC := x.C.NuC
  I := idsOf x.cG x.Z x.C
  JA := x.JA
  JM := x.JM
  tied := ⟨x.div, x.amb0, x.mjH, x.Y.cen0 x.cG x.pins.keep⟩

def TwIn.wd (x : TwIn ex) : (x.F.Dc (zsOf x.R x.F)).Mem → D.what₂.Word := (Equiv.ofBijective _ x.C.bij).symm

theorem TwIn.wd_wU (x : TwIn ex) (u : D.what₂.Word) : x.wd (x.C.wU u) = u := (Equiv.ofBijective _ x.C.bij).symm_apply_apply u

theorem TwIn.wU_wd (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) : x.C.wU (x.wd m) = m :=
  (Equiv.ofBijective _ x.C.bij).apply_symm_apply m

def TwIn.bR (x : TwIn ex) (m : (x.F.Dc (zsOf x.R x.F)).Mem) (i : Fin ((x.F.Dc (zsOf x.R x.F)).a m)) : (D.mem (x.wd m)).A.Mram :=
  D.eMu (x.wd m) (D.jN (x.wd m) (x.C.eNu (x.wd m)
    (Pi.single (Fin.cast (congrArg (x.F.Dc (zsOf x.R x.F)).a (x.wU_wd m)).symm i) 1)))

variable {x : TwIn ex} {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}

theorem phEff_one (x : TwIn ex) : phEff x.R = fun _ => 1 := by
  funext i
  unfold phEff
  rw [x.pins.phs i]
  simp

end GlobalTheory.Mem.R3

end
