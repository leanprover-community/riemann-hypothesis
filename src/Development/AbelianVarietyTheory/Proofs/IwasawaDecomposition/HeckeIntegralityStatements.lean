module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadTie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTransformOfPointLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
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

@[expose] public section

namespace GlobalTheory.HeckeMember

theorem heckeInt_transform_readTie :
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform ∧ GlobalTheory.HeckeSupSt.HeckeReadTie :=
  ⟨GlobalTheory.HkIntegral.heckeInt,
   GlobalTheory.HeckeEx.heckeTransform_of_pointLaws
     (GlobalTheory.HeckePointLaw.heckePointLaws_of_transport GlobalTheory.ThetaTransport.thetaTransportLaw),
   GlobalTheory.HeckeReadProof.heckeReadTie GlobalTheory.SplitLinear.splitLinearModel GlobalTheory.VacStabFixed.vacFixed⟩

end GlobalTheory.HeckeMember
