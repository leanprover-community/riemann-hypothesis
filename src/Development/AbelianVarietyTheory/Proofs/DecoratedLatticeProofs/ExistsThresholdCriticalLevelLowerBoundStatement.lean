module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.exists_threshold_criticalLevel_lower_bound : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.CritLevelSize.tcritLow_sizes | exact GlobalTheory.CritLevelSize.tcritLow_sizes | (intros; apply GlobalTheory.CritLevelSize.tcritLow_sizes <;> assumption)
