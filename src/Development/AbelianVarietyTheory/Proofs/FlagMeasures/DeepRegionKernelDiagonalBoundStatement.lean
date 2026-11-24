module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepRegion_kernelDiagonal_bound : GlobalTheory.FlagMeas.AbsoluteVolume → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  first | exact @GlobalTheory.DeepRegion.deepBound | exact GlobalTheory.DeepRegion.deepBound | (intros; apply GlobalTheory.DeepRegion.deepBound <;> assumption)
