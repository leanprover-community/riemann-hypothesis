module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowBlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS),
    Countable (cLat X u (Sum.inl (Sum.inr b))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inr b)))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
