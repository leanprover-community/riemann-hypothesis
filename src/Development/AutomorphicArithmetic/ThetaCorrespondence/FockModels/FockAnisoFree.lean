module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoOfRanges
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SiegelFormulaSchwartz.SiegelFormulaThetaOfSchwartz
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CoefND
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.WeilSiegelFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace UpperTheory.Lit.Sw47

theorem convergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent := GlobalTheory.StdUnn.sw_doubled_of_std PositivityTheory.SiegelWeilCoefficients.field

theorem weilUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary :=
  PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two UpperTheory.Lit.weilThetaConvergence PositivityTheory.Rg.Wsf.weilSiegelFormula

theorem fa : FA := fa_of convergent weilUnitary

theorem fockAniso_free (_ : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D

end UpperTheory.Lit.Sw47
