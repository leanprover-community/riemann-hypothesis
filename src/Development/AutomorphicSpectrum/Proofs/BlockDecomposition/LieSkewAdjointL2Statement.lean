module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  first | exact @GlobalTheory.CompanionTheory.LieSkew.lie_skew | exact GlobalTheory.CompanionTheory.LieSkew.lie_skew | (intros; apply GlobalTheory.CompanionTheory.LieSkew.lie_skew <;> assumption)
