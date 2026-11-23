module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelRowsEqDimensionStatement
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



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem pRows_of_parts_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b →
    _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions →
    _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := _root_.GlobalTheory.T.ind_piece_degree_zero D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }
end GlobalTheory.Fc.Ind
end
