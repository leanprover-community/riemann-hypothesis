module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
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

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩

section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)

end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  by
    constructor
    · intro h W V S N
      exact ⟨(h W V S N).1, (h W V S N).2.2⟩
    · intro h W V S N
      obtain ⟨a, ⟨t⟩⟩ := h W V S N
      exact ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩

end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
