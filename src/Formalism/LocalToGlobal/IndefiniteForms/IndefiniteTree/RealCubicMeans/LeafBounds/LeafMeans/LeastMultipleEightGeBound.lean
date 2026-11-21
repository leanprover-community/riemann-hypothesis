import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.MeansTie
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.PackedMeans.IndexMeans.MeansBridge

noncomputable section

open Finset NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.IndefR.Obj

namespace IxMeans.MeansTie2

open IxMeans IxMeans.MeansTie

def nX (f r jp : ℕ) : ℕ := f * jp * (r - jp)

def zeroConstantLowerBound (f r jp : ℕ) : ℕ := max (r + (nX f r jp + 1).choose 2 + 2) (8 * f * r + 4)

def leastMultipleEightBound (f r jp : ℕ) : ℕ := 8 * ((zeroConstantLowerBound f r jp + 7) / 8)




structure PgNums where

  Nr : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  jp : ℕ

  DY : ℝ

  T : ℝ

  b : ℝ

  x : ℝ

  rd : ℝ

  Lc : ℝ

  eta : ℝ

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def pgOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) : PgNums where
  Nr := (faceLiftPage R F I J hd).Nr
  f := (faceLiftPage R F I J hd).f
  m := (faceLiftPage R F I J hd).m
  k := (faceLiftPage R F I J hd).k
  jp := (faceLiftFactor R F I J hd j).q'
  DY := (faceLiftFactor R F I J hd j).DY
  T := (faceLiftFactor R F I J hd j).T
  b := (faceLiftPage R F I J hd).b
  x := (faceLiftPage R F I J hd).x
  rd := (faceLiftPage R F I J hd).rd
  Lc := (faceLiftPage R F I J hd).Lc
  eta := (faceLiftPage R F I J hd).η



variable {Tau ι : Type} [Fintype Tau] [Fintype ι]

structure PackPage (r4 : ℝ) (P : MeansPack Tau ι) (pg : PgNums) : Prop where
  hN : (P.N : ℝ) = pg.Nr
  hf : (P.f : ℝ) = pg.f
  hm : (P.m : ℝ) = pg.m
  hjp : P.jp = pg.jp
  hD : (P.D : ℝ) = pg.DY
  hT : (P.T : ℝ) = pg.T
  hb : P.b = pg.b
  hx : P.x = pg.x
  hrd : P.rd = pg.rd
  hLp : P.Lp = pg.Lc

  hh0 : P.h0 = pg.eta / pg.m

  hc0 : P.c0 = (leastMultipleEightBound P.f P.N P.jp : ℝ)

  hnc8 : 8 ∣ P.nc
  hnc1 : 8 * P.f * P.N + 4 ≤ P.nc
  hnc2 : P.nc ≤ 16 * P.f * P.N ^ 2 + 8

  fourth_root_eq : P.fourthRootConstant = r4

structure LeafTie (P : MeansPack Tau ι) (Lv : Leaves Tau) (pg : PgNums) : Prop where

  hbigp : ∀ τ, Lv.bigp τ = P.N - P.jp

  hA : (Lv.A : ℝ) + 2 = pg.k

  heloc : ∀ q, q.Prime → (Lv.eloc q).Nonempty

  heloc0 : ∀ q, ¬ q.Prime → Lv.eloc q = ∅

  hlevel : 1 ≤ Lv.level





structure RecTie6 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) (P : MeansPack Tau (J.ι j)) : Prop where
  hX : J.X j = P.X
  hsl : J.sl j = P.sl
  hU : (faceLiftFactor R F I J hd j).U = P.U
  hE : J.E0 j = P.E0
  hcc : J.cc j = P.cc
  hQ : J.Qcc j = P.Qcc


structure FullTie (r4 : ℝ) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (j : Fin D.R.m) (P : MeansPack Tau (J.ι j)) (Lv : Leaves Tau) : Prop where
  recs : RecTie6 R F I J hd j P
  page : PackPage r4 P (pgOf R F I J hd j)
  defs : DefTie P Lv
  leaves : LeafTie P Lv (pgOf R F I J hd j)


def basePg : PgNums where
  Nr := 2
  f := 1
  m := 1
  k := 2
  jp := 0
  DY := 0
  T := 0
  b := Real.exp 4
  x := Real.exp (Real.exp 1)
  rd := 1
  Lc := 0
  eta := 128

def basePack2 : MeansPack (Fin 1) (Fin 1) where
  N := 2
  f := 1
  T := 0
  D := 0
  jp := 0
  m := 1
  nc := 24
  u := 0
  u1 := 0
  up := 0
  c0 := 24
  b := Real.exp 4
  rd := 1
  x := Real.exp (Real.exp 1)
  Lp := 0
  h0 := 128
  fourthRootConstant := 0
  sl := 0
  e := 0
  SB := ∅
  cpp := 0
  vdd := 0
  Pinf := 0
  PPe := 0
  XW := 0

def baseLeaves2 : Leaves (Fin 1) where
  dE := 1
  level := 1
  q1 := 1
  d := 1
  g1 := 1
  g2 := 1
  rr := 1
  rr' := 1
  r0 := 1
  P0 := 0
  logmu := 0
  cubicPeriodConstant := 0
  c1 := 0
  Nc := 1
  bigp := fun _ => 2
  A := 0
  eloc := fun q => if q.Prime then {0} else ∅

def baseE : ℕ →₀ ℝ := Finsupp.single 2 2

def tiedPack : MeansPack (Fin 1) (Fin 1) := packOf basePack2 baseLeaves2 baseE









end IxMeans.MeansTie2
