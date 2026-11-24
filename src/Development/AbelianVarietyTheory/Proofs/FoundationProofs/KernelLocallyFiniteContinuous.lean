module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology

namespace GlobalTheory.AutomorphicL2KernelContinuous

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ}

theorem finite_contributing (hc : HasCompactSupport f) {C C' : Set G} (hC : IsCompact C) (hC' : IsCompact C') :
    {γ : Γ | ∃ x ∈ C, ∃ y ∈ C', f (x⁻¹ * γ * y) ≠ 0}.Finite := by
  have hK := (hC.prod (hc.isCompact.prod hC')).image (f := fun p : G × G × G => p.1 * p.2.1 * p.2.2⁻¹) (by fun_prop)
  refine (finite_mem_compact (Γ := Γ) hK).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  exact ⟨(x, x⁻¹ * γ * y, y), ⟨hx, subset_tsupport f h, hy⟩, by simp [mul_assoc]⟩

theorem locallyFinite_support [LocallyCompactSpace G] (hc : HasCompactSupport f) :
    LocallyFinite fun γ : Γ => Function.support fun p : G × G => f (p.1⁻¹ * γ * p.2) := by
  rintro ⟨x, y⟩
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C', hC', hy⟩ := exists_compact_mem_nhds y
  refine ⟨C ×ˢ C', prod_mem_nhds hx hy, (finite_contributing hc hC hC').subset ?_⟩
  rintro γ ⟨p, h, h1, h2⟩
  exact ⟨p.1, h1, p.2, h2, h⟩

theorem continuous_kernel [LocallyCompactSpace G] (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous fun p : G × G => kernel Γ f p.1 p.2 := by
  have h : Continuous fun p : G × G => ∑ᶠ γ : Γ, f (p.1⁻¹ * γ * p.2) :=
    continuous_finsum (fun γ => by fun_prop) (locallyFinite_support hc)
  refine h.congr fun p => ?_
  exact (tsum_eq_finsum (finite_support_kernel hc p.1 p.2)).symm

end GlobalTheory.AutomorphicL2KernelContinuous
