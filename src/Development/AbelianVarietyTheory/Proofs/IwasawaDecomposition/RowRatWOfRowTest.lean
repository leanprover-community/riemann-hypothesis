module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
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

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  by
    intro H
    have h := (StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H
    apply h.trans
    apply StepW.of_all
    intro K B f T w hK hF G Z hX Wt z a b _ c d _ _ _ _
    exact G Z hX Wt z a b c d

end GlobalTheory.Mem.LiteralAutomorphy
