module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
