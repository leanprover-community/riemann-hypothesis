module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) := Measure.haar
    have : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
    have htransfer := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := htransfer
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep (K := E) (n := a) ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
