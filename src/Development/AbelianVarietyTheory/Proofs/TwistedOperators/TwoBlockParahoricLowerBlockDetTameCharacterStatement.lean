module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  first | exact @GlobalTheory.ParahoricLowerBlock.lower_block_tame | exact GlobalTheory.ParahoricLowerBlock.lower_block_tame | (intros; apply GlobalTheory.ParahoricLowerBlock.lower_block_tame <;> assumption)
