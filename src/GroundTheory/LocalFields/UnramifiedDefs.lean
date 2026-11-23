module

public import GroundTheory.LocalFields.Integers
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  change ramificationIndex K L = 1 ↔ _
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = 1 * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

end Tower

end GroundTheory.LocalField
