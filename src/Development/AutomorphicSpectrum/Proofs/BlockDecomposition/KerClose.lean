module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelClose

theorem kerClose : KerClose := by
  intro X Ω x y hΩ
  have hC : IsCompact ((fun o : X.G => x * o * y⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro φ hφ γ hγ
    have hmem : x⁻¹ * (γ : X.G) * y ∈ Ω := hφ hγ
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨_, hmem, by group⟩
  have hker : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      ker X.Γ φ x y = ∑ γ ∈ hfin.toFinset, φ (x⁻¹ * (γ : X.G) * y) := fun φ hφ =>
    finsum_eq_sum_of_support_subset _ (hsupp φ hφ)
  refine ⟨(hfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro φ φ' ε hφ hφ' hε
  rw [hker φ hφ, hker φ' hφ', ← Finset.sum_sub_distrib]
  calc ‖∑ γ ∈ hfin.toFinset, (φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y))‖
      ≤ ∑ γ ∈ hfin.toFinset, ‖φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y)‖ :=
        norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε := Finset.sum_le_card_nsmul _ _ _ fun γ _ => hε _
    _ = (hfin.toFinset.card : ℝ) * ε := nsmul_eq_mul _ _

end GlobalTheory.CompanionTheory.KernelClose
