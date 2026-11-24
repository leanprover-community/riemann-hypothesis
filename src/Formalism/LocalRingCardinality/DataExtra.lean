module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.SharpRestriction.GrowthBounds.DefsInst
public import Formalism.LocalRingCardinality.DataAmbForm
public import Formalism.LocalRingCardinality.DataKerP
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.BasicNotions

open Formalism.MainNotions

def EpTie {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : Prop :=
  ∀ u w hg, (D.gat u w hg).e = X.ep (D.what₂.places.resChar w)

def NuUnserved {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) : Prop :=
  ∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) = ∅ →
    DV.LocEq (D.plEq w) (L.NuLat u) (DV.MramL D u)

def FillsAll {D : D7} (hT : GatTies D) (Y : G.LatInst D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)), ∀ j ∈ SizeData₂.lifts D,
    ((Y.Fl u w hg).w v j s : ℝ) = wj D j (hT.gat_pos u w hg ⟨v, s⟩) - G.kaJ D j

structure ExtraC where
  Ce : ℝ
  err : ErrC

structure Extra (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (X : DivX D) (cX : ExtraC) where

  lev : LevelData D

  th : ThetaX D

  th_io : th.TieIo

  cmp : LatCmp D

  lat : LatDefs D L Gi Gl K cmp

  tw : TwForms D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D hT cmp tw u w h (Gl.Ch u w h)

  ep_def : G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : G.KapIDef Gi K
  fills_all : FillsAll hT Gl
  nu_unserved : NuUnserved Gi K

  idx : IdxDefs D X
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D

  kapR_def : DV.KapRBase X

  errX : ErrX D
  err : ErrDefs D L errX lev K cX.err

  nch : NChoice D

  nch_tie : NChTie D nch

  xd : ThData D

  p0 : BaseLevelRowSide D

  rationalRoots_def : p0.s.RRDef

  amb : AmbForm D (RowSide.sharp D)
  amb0 : AmbForm D p0.s

  fdef : L.FDef

  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u

  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig
  gauge_def : letI := D.host.cmStar; gauge.IsGauge

end Formalism.BasicNotions
