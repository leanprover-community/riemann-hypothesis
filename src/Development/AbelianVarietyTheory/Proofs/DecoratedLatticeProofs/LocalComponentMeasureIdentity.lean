module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLinesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLatticeStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentity

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFramesStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFramesStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLinesStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLatticeStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeSplittingSumStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLatticeStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLatticeStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentity =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentity", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape\npublic import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFramesStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

namespace GlobalTheory.Fam.LatShape

theorem coreFrame_beta_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    {F F' : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F) (h' : p.IsCoreFrame B s FA F') : F.β = F'.β := by
  ext r (a | u)
  · rw [h.1, h'.1]
  · cases u
    rw [h.2, h'.2]

end GlobalTheory.Fam.LatShape

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentity =====
