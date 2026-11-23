module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.cuspidal_L2_norm_one_isometry : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a))) [ν.IsHaarMeasure], ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧ ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) ℂ, Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.transfer | exact GlobalTheory.CompanionTheory.CuspTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.transfer <;> assumption)
