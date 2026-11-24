module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.closeLift :
    ∀ (Ph A B : Type) [Group Ph] [Group A] [Group B] (π : Ph →* A) (π' : Ph →* B) (V : Subgroup Ph) [V.Normal], π.ker ⊔ V = π'.ker ⊔ V → (∀ a b g, Close π π' V a b → π' g = b → ∃ g', π g' = a ∧ g⁻¹ * g' ∈ V) ∧ ∀ k, π' k = 1 → ∃ k', π k' = 1 ∧ k⁻¹ * k' ∈ V := by
  intro Ph A B _ _ _ π π' V _ hsup
  have hdec : ∀ x, π' x = 1 → ∃ k, π k = 1 ∧ ∃ v ∈ V, k * v = x := by
    intro x hx
    have hx' : x ∈ π.ker ⊔ V := by
      rw [hsup]
      exact Subgroup.mem_sup_left (MonoidHom.mem_ker.2 hx)
    obtain ⟨k, hk, v, hv, hkv⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
    exact ⟨k, MonoidHom.mem_ker.1 hk, v, hv, hkv⟩
  refine ⟨fun a b g ⟨g0, g0', ha, hb, hV⟩ hg => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, v, hv, hkv⟩ := hdec (g0'⁻¹ * g) (by rw [map_mul, map_inv, hb, hg, inv_mul_cancel])
    refine ⟨g0 * k, by rw [map_mul, ha, hk, mul_one], ?_⟩
    have hg' : g = g0' * (k * v) := by rw [hkv, mul_inv_cancel_left]
    rw [hg']
    have hw : g0'⁻¹ * g0 ∈ V := by
      have := V.inv_mem hV
      rwa [_root_.mul_inv_rev, inv_inv] at this
    have hconj : k⁻¹ * (g0'⁻¹ * g0) * k ∈ V := by
      have := (inferInstance : V.Normal).conj_mem _ hw k⁻¹
      rwa [inv_inv] at this
    have heq : (g0' * (k * v))⁻¹ * (g0 * k) = v⁻¹ * (k⁻¹ * (g0'⁻¹ * g0) * k) := by group
    rw [heq]
    exact V.mul_mem (V.inv_mem hv) hconj
  · obtain ⟨k', hk', v, hv, rfl⟩ := hdec k hk
    refine ⟨k', hk', ?_⟩
    have heq : (k' * v)⁻¹ * k' = v⁻¹ := by group
    rw [heq]
    exact V.inv_mem hv
