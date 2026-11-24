module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.Strong
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Thin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.AbsInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.PartNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.BaseChangeNB
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne
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

@[expose] public section

open UpperTheory.V.Z.Tf PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.Gal.Desc

theorem speh : GlobalTheory.BcSpeh.BcSpeh := UpperTheory.BaseChangeIdentities.speh UpperTheory.BaseChangeIdentities.baseChangeNB

theorem weakAll : WeakAll := weakAll_of SR.splitRigid (GaloisFromTraceFormula.partNorm GaloisFromTraceFormula.absInf) GOne.unitOf GaloisFromTraceFormula.runTh

theorem desc : GlobalTheory.Cong.Desc :=
  desc_of speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin GOne.unitOf weakAll

theorem descOffT : GlobalTheory.Cong.DescOffT := GlobalTheory.Cong.descOffT_of_desc desc

end UpperTheory.Gal.Desc
