module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.classSum_regroup_finerLevel_cosets : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  first | exact @GlobalTheory.ClassRefineBridge.sum_isReps_refine | exact GlobalTheory.ClassRefineBridge.sum_isReps_refine | (intros; apply GlobalTheory.ClassRefineBridge.sum_isReps_refine <;> assumption)
