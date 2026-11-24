module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalLevelRelIndexAtLevelPrimeSelfDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeLevel
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

namespace GlobalTheory.LevelIndex

theorem selfDualLatticeIndex_stabiliserLevelIndexFormula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel.indexKU_iff.mp
    (GlobalTheory.LevelIndex.indexKU_of_selfDualOverBase
      (GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice))

end GlobalTheory.LevelIndex
