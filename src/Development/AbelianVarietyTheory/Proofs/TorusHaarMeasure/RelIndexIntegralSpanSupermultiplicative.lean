module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSupMulRelIndexInfSame
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SpanImageInfSpanImageOfLinearIndependent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_mul_le_of_le {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by
  rw [← GlobalTheory.relIndex_sup_mul_relIndex_inf A M₁ _ M₂ _ h₁ h₂, mul_comm, ← inf_inf_distrib_left]
  refine Nat.mul_le_mul_left _ (AddSubgroup.relIndex_le_of_le_right ?_ hne)
  exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)


omit [IsCMField E] in
theorem span_le_inf_span {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
  refine le_inf ?_ ?_
  · have : Submodule.span (𝓞 E) (Set.range w) ≤ Λ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
    exact fun x hx => this hx
  · exact fun x hx => Submodule.span_le_restrictScalars (𝓞 E) E _ hx

theorem relIndex_span_mul_le : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  intro r X α β γ _ _ _ _ _ _ w hw hΛ
  have hw' : LinearIndependent (𝓞 E) w := hw.restrict_scalars' (𝓞 E)
  obtain ⟨i₁, s₁⟩ := GlobalTheory.span_inf_sup_overlapping_parts (𝓞 E) _ α β γ w hw'
  obtain ⟨i₂, s₂⟩ := GlobalTheory.span_inf_sup_overlapping_parts E _ α β γ w hw
  have hne := relIndex_span_ne_zero r X _ w hw hΛ
  rw [← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup] at hne
  have key := relIndex_mul_le_of_le _ _ _ _ _
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)) fun a => hΛ _)
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) fun a => hΛ _) hne
  rw [← i₁, ← i₂, ← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  exact key

end GlobalTheory.SpanIndex
