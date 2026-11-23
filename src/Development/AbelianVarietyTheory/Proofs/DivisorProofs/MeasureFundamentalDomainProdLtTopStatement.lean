module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.measure_fundamentalDomain_prod_lt_top | exact GlobalTheory.measure_fundamentalDomain_prod_lt_top | (intros; apply GlobalTheory.measure_fundamentalDomain_prod_lt_top <;> assumption)
