module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Jacobson.Ideal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Nakayama

@[expose] public section

open TensorProduct

namespace GlobalTheory.BSP

open TensorProduct in
theorem _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient :
    ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  intro A _ 𝔞 h𝔞 P _ _ _ P' _ _ _ _ w hw
  have surj : Function.Surjective w := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top h𝔞 ?_
    intro y _
    obtain ⟨z, hz⟩ := hw.2 ((1 : A ⧸ 𝔞) ⊗ₜ[A] y)
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul P 𝔞 z)
    rw [← (quotTensorEquivQuotSMul P 𝔞).symm_apply_apply z, ← hx,
      quotTensorEquivQuotSMul_symm_mk, LinearMap.baseChange_tmul] at hz
    have hmem : w x - y ∈ 𝔞 • (⊤ : Submodule A P') := by
      rw [← Submodule.Quotient.mk_eq_zero, ← quotTensorEquivQuotSMul_mk_one_tmul 𝔞 (w x - y),
        (quotTensorEquivQuotSMul P' 𝔞).map_eq_zero_iff, TensorProduct.tmul_sub, hz, sub_self]
    have : y = w x - (w x - y) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right hmem)
  refine ⟨?_, surj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property w LinearMap.id surj
  set π : P →ₗ[A] P := LinearMap.id - s ∘ₗ w with hπ
  have hwπ : ∀ p, w (π p) = 0 := fun p => by
    have := LinearMap.congr_fun hs (w p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [hπ, this]
  have hπw : ∀ p, w p = 0 → π p = p := fun p hp => by simp [hπ, hp]
  have hbot : LinearMap.range π = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 _ ?_ ?_ h𝔞
    · rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    · rintro _ ⟨p, rfl⟩
      have h0 : (1 : A ⧸ 𝔞) ⊗ₜ[A] π p = 0 := by
        apply hw.1
        rw [LinearMap.baseChange_tmul, hwπ, TensorProduct.tmul_zero, map_zero]
      rw [← (quotTensorEquivQuotSMul P 𝔞).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
        Submodule.Quotient.mk_eq_zero] at h0
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'', ← hπw _ (hwπ p)]
      exact Submodule.mem_map_of_mem h0
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have : π p ∈ LinearMap.range π := ⟨p, rfl⟩
  rw [hbot, Submodule.mem_bot, hπw p hp] at this
  exact this

end GlobalTheory.BSP
