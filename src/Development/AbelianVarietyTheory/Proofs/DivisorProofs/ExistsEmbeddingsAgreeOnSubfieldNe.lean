module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem exists_embeddings_agree_on_subfield_ne (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω]
    [CharZero L] (a : Ω) (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F),
      i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω
  have he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0 := by
    intro h
    have h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a := sub_eq_zero.mp h
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by
      by_contra! hc
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)
    have h2 := congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2
    apply ha
    refine ⟨(φ 1)⁻¹ * φ a, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  have hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) :=
    fun h => he h.eq_zero
  rw [nilpotent_iff_mem_prime] at hn
  push_neg at hn
  obtain ⟨J, hJ, heJ⟩ := hn
  haveI := hJ
  let g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J) :=
    (algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)
  refine ⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance,
    g.comp (Algebra.TensorProduct.includeLeftRingHom),
    g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩
  · ext l
    simp only [RingHom.comp_apply]
    congr 1
    show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro h
    apply heJ
    have h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a) := h
    have h4 := IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3
    exact Ideal.Quotient.eq.mp h4

end GlobalTheory
