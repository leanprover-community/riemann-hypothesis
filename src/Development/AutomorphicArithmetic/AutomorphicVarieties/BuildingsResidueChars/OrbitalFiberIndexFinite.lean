module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

namespace UpperTheory

private lemma relIndex_normal_sup {Γ : Type} [Group Γ] (N A C : Subgroup Γ) [N.Normal] (hN : N ≤ A)
    (h : A.relIndex C ≠ 0) : A.relIndex (N ⊔ C) ≠ 0 := by
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]
  have key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N)) := by
    intro K
    rw [← Subgroup.relIndex_comap, hA]
  have hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  rw [key, hm, ← key]
  exact h

theorem orbitalFiber_index_finite : V.Z.Sym.Glob.Fib.IndexFin := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0
  obtain ⟨T, hT⟩ := hT
  have hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0 := by
    intro h
    apply h0
    have := Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this
  have h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0 :=
    relIndex_normal_sup Γ₁ _ _ le_sup_left hAC
  have pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U',
      ι (b : Γ) = ι h * t * u := by
    intro b
    have hb : ι (b : Γ) ∈ S ⊔ U' := b.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
    obtain ⟨s, hs, u, hu, e⟩ := hb
    obtain ⟨h, hh, t, ht, u₂, hu₂, rfl⟩ := hT s hs
    exact ⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩
  choose f hfT hf using pick
  have h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    have inj : Function.Injective
        (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) =>
          (⟨f q.out, hfT _⟩ : T)) := by
      intro q q' hq
      have hq' : f q.out = f q'.out := congrArg Subtype.val hq
      rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      generalize q.out = a at hq'
      generalize q'.out = b at hq'
      obtain ⟨h, hh, u, hu, ha⟩ := hf a
      obtain ⟨h', hh', u', hu', hb⟩ := hf b
      rw [← hq'] at hb
      have hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁ := by
        simpa using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹
      have hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι := by
        have : ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u' := by
          simp only [map_mul, map_inv, ha, hb]
          group
        rw [Subgroup.mem_comap, this]
        exact U'.mul_mem (U'.inv_mem hu) hu'
      have e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ)
          = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b) := by
        push_cast
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    haveI := Finite.of_injective _ inj
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans h1 h2

end UpperTheory
