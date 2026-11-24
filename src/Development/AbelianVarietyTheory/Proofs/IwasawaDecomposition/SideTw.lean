module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def sgTw (x : St P) (N : TwNew (Dof x)) : SameGrp (B := B) (C := w.C) x.o.Z (oTw x N).Z where
  e _ := Equiv.refl _
  pl _ _ := rfl
  e0 _ := rfl

def datTw (x : St P) (N : TwNew (Dof x)) : Dat (w.st (oTw x N).Z) w.I P.hX T P.Wt :=
  DatCopy.copy (a := x.o.Z) (oTw x N).Z (sgTw x N) x.m.z

def sideTw (x : St P) (N : TwNew (Dof x)) : Side0 (oTw x N) where
  cen := x.s.cen
  tie := x.s.tie
  is := x.s.is
  RR := x.s.RR
  frames := x.s.frames
  jEE := x.s.jEE
  basis := x.s.basis
  norm := x.s.norm

theorem fitsTw (x : St P) (N : TwNew (Dof x)) : (oTw x N).Fits := ⟨x.fits.div, x.fits.grp, ⟨(by with_unfolding_all exact (x.fits.grpAt.pl :)), (by with_unfolding_all exact (x.fits.grpAt.idem :)), (by with_unfolding_all exact (x.fits.grpAt.cen :))⟩,
  fun eR h => ⟨(by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).amb : _)), (by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).mt : _))⟩⟩

def stTw (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) : St P :=
  ⟨oTw x N, fitsTw x N, x.G_eq, x.etaF, x.bk, m, hc, hh, sideTw x N, r, hp⟩

end GlobalTheory.HeightCounting.Up

end
