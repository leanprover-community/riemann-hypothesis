module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ Γ' G₁ G₂ _ _ _ _ e ι₁ ι₂ θ K₁ K₂ γ δ f φ
  have hprod : (ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom) = (ι₁.prod ι₂).comp e.toMonoidHom := by
    ext x <;> rfl
  have hR : ((ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom)).range = (ι₁.prod ι₂).range := by
    rw [hprod, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  have hS : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
    intro x
    have h : stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁ ι₂ K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [h]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun a => by simp [Subgroup.mem_comap]))
  unfold pointSum
  simp only [hS]
  rw [hR]

end GlobalTheory
