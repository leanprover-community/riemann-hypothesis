module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option linter.dupNamespace false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace Formalism.L2.SG.PoincareSeriesSquareIntegrable

open Formalism.L2.SG.FoldBound

def IsFoldDatum {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (S : Subgroup G)
    (Ω : Set G) (a : ℝ≥0) (Ph : G → ℂ) : Prop :=
  Measurable Ph ∧ (∀ s ∈ S, ∀ y : G, Ph (s * y) = Ph y) ∧
    ∀ y : G, ‖Ph y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ ω in Ω, ‖Ph (y * ω)‖ₑ ∂μ

def multiplicityLIntegral {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G)
    (Ω : Set G) (F : Set G) (Ph : G → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in F, mult Γ Ω y * ‖Ph y‖ₑ ∂μ

def poinc {G : Type*} [Group G] (D : Set G) (Ph : G → ℂ) (x : G) : ℂ :=
  ∑' δ : D, Ph ((δ : G) * x)

def stab {G : Type*} [Group G] (S S' : Subgroup G) (γ : G) : Subgroup G :=
  S ⊓ S'.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_stab {G : Type*} [Group G] (S S' : Subgroup G) (γ g : G) :
    g ∈ stab S S' γ ↔ g ∈ S ∧ γ⁻¹ * g * γ ∈ S' := by
  simp [stab]

def IsDoubleTransversal {G : Type*} [Group G] (Γ S S' : Subgroup G) (R : Set G) : Prop :=
  R ⊆ (Γ : Set G) ∧
    ∀ γ ∈ Γ, ∃! r : R, ∃ s ∈ S, ∃ s' ∈ S', s * (r : G) * s' = γ

def PoincareSeriesFinite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), IsFoldDatum μ S Ω a Ph →
  ∀ (F : Set G), IsFundamentalDomain S F μ → multiplicityLIntegral μ Γ Ω F Ph < ⊤ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ x : G, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) < ⊤

def PoincareSeriesMemLp (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), IsFoldDatum μ S Ω a Ph →
  ∀ (F : Set G), IsFundamentalDomain S F μ → multiplicityLIntegral μ Γ Ω F Ph < ⊤ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
    MemLp (poinc D Ph) 2 (μ.restrict FΓ) ∧
    (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ) ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph ∧
    (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2

def PoincareSeriesInner (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S S' : Subgroup G), DiscreteTopology Γ → S ≤ Γ → S' ≤ Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
  ∀ (a a' : ℝ≥0) (Ph Ph' : G → ℂ), IsFoldDatum μ S Ω a Ph → IsFoldDatum μ S' Ω a' Ph' →
  ∀ (F F' : Set G), IsFundamentalDomain S F μ → IsFundamentalDomain S' F' μ →
    multiplicityLIntegral μ Γ Ω F Ph < ⊤ → multiplicityLIntegral μ Γ Ω F' Ph' < ⊤ →
  ∀ (D D' : Set G), IsRightTransversal Γ S D → IsRightTransversal Γ S' D' →
  ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
    (∫⁻ x in F', ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ∂μ)
        ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' ∧
    (∑' r : R, ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ) < ⊤ ∧
    (∀ r ∈ R, IntegrableOn (fun x => Ph x * conj (Ph' (r⁻¹ * x))) (Fs r) μ) ∧
    IntegrableOn (fun x => poinc D Ph x * conj (poinc D' Ph' x)) FΓ μ ∧
    (∫ x in FΓ, poinc D Ph x * conj (poinc D' Ph' x) ∂μ)
      = ∑' r : R, ∫ x in Fs r, Ph x * conj (Ph' ((r : G)⁻¹ * x)) ∂μ

end Formalism.L2.SG.PoincareSeriesSquareIntegrable
