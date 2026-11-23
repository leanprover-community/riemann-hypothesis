module

public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace GlobalTheory.CompanionTheory.TopGroup

theorem finite_image_of_right_invariant_near_one :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by
  intro Γ X _ _ _ K hK Gf hS
  have hU : ∀ k ∈ K, {y : Γ | k⁻¹ * y ∈ {s : Γ | ∀ x, Gf (x * s) = Gf x}} ∈ nhds k := by
    intro k _
    have hc : Continuous fun y : Γ => k⁻¹ * y := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds ?_
    show _ ∈ nhds (k⁻¹ * k)
    rw [inv_mul_cancel]
    exact hS
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image Gf).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hcover hy)
  refine ⟨k, hk, ?_⟩
  have h := hyk k
  rw [mul_inv_cancel_left] at h
  exact h.symm

end GlobalTheory.CompanionTheory.TopGroup
