module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
public import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.AllLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.PolNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.StepLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.WeakRes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CuspRapidDecayGL.CuspRapidDecaySiegelGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MultiplicityOneRigidity.GelfandKazhdanDualOfRigidity
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open GlobalTheory.GalCut GlobalTheory.Cong UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.NearKilling

theorem stepLift_holds : StepLift :=
  stepLift UpperTheory.ConvolutionTheory.cbcc noSelfTwist_holds
    (polBC PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.S2.CuspBdd.cuspFormsBoundedGL)) weakRes

theorem allLift_holds : AllLift := allLift stepLift_holds satSplit_holds

end UpperTheory.Gal.NearKilling
