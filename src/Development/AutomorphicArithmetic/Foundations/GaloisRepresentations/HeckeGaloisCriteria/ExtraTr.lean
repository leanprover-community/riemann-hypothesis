module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.BuDefQEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.KapSharpTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.NchTieTr
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (c : CutD D)

def raw : Gen.Raw D :=
  ⟨(layCut D c).eta, (layCut D c).eta_nonneg, (layCut D c).reEta _ (layCut D c).eta_nonneg, (layerCut_admissible D c).reEta _ _,
    (layCut D c).etaOk_reEta⟩

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (cut D c) := Gen.ledTr (raw c) L

theorem tiesTr (h : Ties D) : Ties (raw c).rec' := Gen.tiesTr (raw c) h h.tw_cover



def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (raw c).rec' (Gen.ledTr (raw c) L) (Gen.gatTr (raw c) gatT) (Gen.instTr (raw c) Gx) (Gen.latTr (raw c) Gy) K
      (Gen.divTr (raw c) X) cX :=
  Gen.extraTr (raw c) ex (nchTr c ex.nch) (nchTie_tr c ex.nch_tie) (xdTr c ex.xd)
    (show BaseLevelRowSide (cut D c) from ⟨sideTr c ex.p0.s⟩) (rrDef_tr c _ ex.rationalRoots_def) (ambTr c ex.amb) (ambTr c ex.amb0) (kapSharp_tr c)

end UpperTheory.GalC
