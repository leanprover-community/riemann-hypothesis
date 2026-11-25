module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr


variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
def ysTh_alt (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpRealS (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).cG ((thTw (Dof x) th).rat l.rat.S) where
  fi := (by with_unfolding_all exact (l.b.YS.fi :))
  geq := (by with_unfolding_all exact (l.b.YS.geq :))
  rho := (by with_unfolding_all exact (l.b.YS.rho :))
  chi := (by with_unfolding_all exact (l.b.YS.chi :))
  eF := (by with_unfolding_all exact (l.b.YS.eF :))
  bsup := (by with_unfolding_all exact (l.b.YS.bsup :))
  act := by with_unfolding_all exact (l.b.YS.act :)
def exponentOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpTied (w.st (oTw x (thTw (Dof x) th)).Z).toD7 :=
  (dof_oTw x (thTw (Dof x) th)) ▸ (bsTw l.b.Bs th).exp
def rowPsiOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    ∀ i : Fin (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.m,
      Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (oTw x (thTw (Dof x) th)).Z).toD7 i)
        (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
end GlobalTheory.HeightCounting.Up
end
end
