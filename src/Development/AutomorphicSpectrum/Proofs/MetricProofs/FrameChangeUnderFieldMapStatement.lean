module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.frame_change_under_field_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₂ : Type) [Field Ω₂] (x₂ : (Σ k, ι₂ k) → Ω₂) (φ : M.Ω →+* Ω₂) (zb : (Σ k, ι₂ k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal x₂) → M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → (∀ (m : ι k) (I : Finset (Fin N)), RegAt x₂ (mCoordIdeal zb) (φ (F₁.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u ⟨k, m⟩ I)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₁.u' I ⟨k, m⟩)) ∧ RegAt x₂ (mCoordIdeal zb) (φ (F₂.u' I ⟨k, m⟩))) → (∀ a b, RegAt x₂ (mCoordIdeal zb) ((((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) a b) ∧ RegAt x₂ (mCoordIdeal zb) ((((F₂.T p.1).map φ)⁻¹ * (F₁.T p.1).map φ) a b)) → ∃ c : ℂ, c ≠ 0 ∧ ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, ∑ I, valAt x₂ (φ (F₁.u ⟨k, m⟩ I)) zb * minorIJ (CovMap.LocImg.valMat x₂ zb (((F₁.T p.1).map φ)⁻¹ * (F₂.T p.1).map φ) * h) I (stepCols N j p.2) = c * ∑ I, valAt x₂ (φ (F₂.u ⟨k, m⟩ I)) zb * minorIJ h I (stepCols N j p.2) := by
  exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.main
