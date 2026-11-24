module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
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
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
def pointOfRealisation (pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T P) {Del h0 : ℕ} (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)) {c : ℝ}
    (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf (zscOf P Del h0 c) S) (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) : PtAt ex c where
  P := rowSideOfCompatibleThetaPair P
  Del := Del
  h0 := h0
  hDel := hDel
  hh0 := hh0
  Dcf := Dcf
  Spf := Spf
  gamDvd := pin.gamDvd
  T := B.T
  alg := B.alg
  R := B.Q.Rl
  charW := B.Q.charW
  zs := B.Q.zs
  s0 := B.Q.s0
  s1 := B.Q.s1
  dc := B.Q.dc
  stdChar := B.Q.stdChar
  signs := B.Q.signs
  cG := B.Q.cG
  Sx := B.Q.Sx
  nexp := B.Q.nexp
  stdV := B.Q.stdV
  stdX := B.Q.stdX
  host := B.Q.host
  err_eq := B.Q.err_eq
  vpos := B.Q.vpos
  κ := B.κ
  v₀ := B.v₀
  fw := B.fw
  bar := B.bar
  O := B.O
  pins := B.pins
  rhoGeo := B.rhoGeo
  equivAll := B.equivAll
  cTie := B.cTie
  phase := B.phase
  qGuard := Qp.qGuard
  hF := Qp.hF
  phsOne := Qp.phsOne
  prXunit := Qp.prXunit
  grpRecPin := Qp.grpRecPin
  fdiag := Qp.fdiag
  eGtie := Qp.eGtie
  betaStd := Qp.betaStd
  tupT := Qr.tupT
  hm := Qr.hm
  Tp := Qr.Tp
  tupXi := Qr.recR.tupXi
  tupAt := Qr.recR.tupAt
  tupTie := Qr.tupTie
  tupT_tup := Qr.tupT_tup
  muEq := Qr.muEq
def PointSummands.pt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : PtAt O.ex c :=
  _root_.GlobalTheory.Fc.Ind.pointOfRealisation b.pin b.DH.2.1 b.DH.2.2 b.B b.pins b.Rr
def conditionOnPoint (G : PtP) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O c b => G D O c b.pt
def RowPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => b.pt.PointConditions'
end GlobalTheory.Fc.Ind
end
end
