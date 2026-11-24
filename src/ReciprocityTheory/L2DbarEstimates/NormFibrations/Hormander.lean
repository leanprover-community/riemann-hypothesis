module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem
public import ReciprocityTheory.L2DbarEstimates.LeviForms.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.LeviForms.IntegrableWd
public import ReciprocityTheory.L2DbarEstimates.LeviForms.MacofFderivApplyContDiffOn
import ReciprocityTheory.L2DbarEstimates.Localization.Extend
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))

theorem ma (n : ℕ) : MAStatement n :=
  I.ma n (I.maCof n)

end ReciprocityTheory.L2DbarEstimates
