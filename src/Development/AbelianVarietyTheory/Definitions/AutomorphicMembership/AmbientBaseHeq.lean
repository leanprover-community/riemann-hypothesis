module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure ColLay (D : D7) (lev : LevelData D) (eX : ErrX D) : Prop where
  piG_lev : PiGLevel D lev eX
  piT_lev : PiTLevel D lev eX
  seen : SeenDef D eX
  tauOf : TauOfDef D eX
  one : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamChoice_at D
  atT : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
    (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
    ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x)

def GatNum (s : Scale) (D : D7) : Prop :=
  ∀ u w hg, (D.gat u w hg).P.r = (if (D.what₂.places.resChar w : ℝ) < s.p0 D.R.k then G.rG s else 1) ∧
    (D.gat u w hg).e = ⌈(1 : ℝ) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) s.a⌉₊

structure GyLay (K : Ctx) (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (Gy : G.LatInst D) : Prop where
  vram : cmp.VramDef Gy
  fills : FillsAll Gt Gy
  led : ∀ L : SizeData₂ D, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst D L, CanonInst X → G.EpDef X K.C.cX.Ce →
    G.KapIDef X K.C.GK → (∀ w, G.ParametersFill X K.C.GK w) → G.LatTied Gt X Gy

def ExportAt (D : D7) (nch : NChoice D) (xd : ThData D) : Prop :=
  ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)),
    (∀ i, D.ntw.NonzeroIndexPlace i → GlobalTheory.TwAll.goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.pin (BlochKatoReduction.bk0 D)) (twEOf xd) N0 i) ∧
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (nch.twI w) ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w)

section Lemmas

variable {D : D7}


end Lemmas

structure Core (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) : Type 1 where
  isOver : K.Over X.B.toPre
  xi : X.C.Tup → HChar X.B.host.E
  mu : MuIs X f T xi
  forced : ∀ p : ℕ, p.Prime → ((∃ i, p = X.B.host.g i) ∨ p = X.B.host.d ∨ (p : ℝ) ≤ K.s.X'' X.B.R.n) → p ∈ T.pl
  O : Obj2 X.toD7
  col : ColLay X.toD7 O.lev O.errX
  gatNum : GatNum K.s X.toD7
  gy : GyLay K X.toD7 O.gatT O.cmp O.Gy
  r : RowT X.toD7 (Fr.at X f) xi
  p0_eq : O.p0 = r.p0
  X_eq : O.X = r.X
  amb_eq : O.amb = r.amb
  ambientBase_heq : HEq O.amb0 r.amb0
  mtStable : DQ.MtStableAt X.toD7
  th_io : O.th.TieIo
  gauge_def : letI := X.toD7.host.cmStar; O.gauge.IsGauge
  real : Formalism.L2.Theta.RealTied X.toD7
  dsig_eq : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)
  del : X.S.s.Del = (Delv K.s K.cD : ℚ)
  etaF : X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  chiT : ∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
    ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))
  nch_tie : NChTie X.toD7 O.nch
  nch_Q : ∀ w, X.B.places.resChar w ∈ T.pl → O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w

end GlobalTheory.Mem.Top

end
