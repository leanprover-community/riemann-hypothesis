module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.StUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchUnit
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.NeZeroOfFinprod
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
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

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem runTh_of_pi (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : PositivityTheory.Rg.BcB.Desc.GrowthPiJ) : RunTh :=
  runTh_of UpperTheory.ConvolutionTheory.G2.uSide UpperTheory.ConvolutionTheory.G2.g2s muEx UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit Th.stUnit
    (endoBlockG cuspReadI) (stableBlockG cuspReadI h1 h2 h3 h4 h5)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
