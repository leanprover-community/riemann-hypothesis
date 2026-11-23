module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InstBack
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.WitTr



theorem kerT_entC_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' := by
  intro B f T w Z t Y Gy ker k N h hE
  exact ⟨DivTr.ktTr w Z N h k, DivTr.entC_tr w Z N h k hE⟩

end GlobalTheory.Mem.Top.Bl.WitTr
