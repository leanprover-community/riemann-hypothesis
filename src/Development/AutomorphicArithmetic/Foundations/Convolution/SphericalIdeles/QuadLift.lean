module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamSphOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CoreId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.LocGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TorusCharComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTrace
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

theorem UpperTheory.ConvolutionTheory.Sph.ramSph : UpperTheory.ConvolutionTheory.Sph.RamSph :=
  UpperTheory.ConvolutionTheory.Sph.ramSphOf UpperTheory.Gal.Join.locGal (UpperTheory.Gal.Join.liftGood
    (UpperTheory.Gal.Join.coreId UpperTheory.Gal.InertialTypesAlt.G.varEx UpperTheory.Gal.InertialTypesAlt.G.varTrace UpperTheory.Gal.InertialTypesAlt.L.elemPairJ_holds))

theorem UpperTheory.ConvolutionTheory.Sph.quadLift : GlobalTheory.GalCut.QuadLift := UpperTheory.ConvolutionTheory.Sph.quadLiftOf UpperTheory.ConvolutionTheory.Sph.ramSph
