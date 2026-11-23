module

import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

open Module Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def pure_type_projection {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := tyPart ty σ
  map_add' a b := by
    funext k
    simp only [tyPart, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    funext k
    simp only [tyPart, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem typeProjection_apply {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (w : Fin g → ℂ) (k : Fin g) :
    pure_type_projection ty σ w k = if ty k = σ then w k else 0 := by
  simp [pure_type_projection, tyPart]

def typeSupportedVectors {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : Submodule ℂ (Fin g → ℂ) where
  carrier := {w | ∀ k, ty k ≠ σ → w k = 0}
  add_mem' {a b} ha hb k hk := by simp [ha k hk, hb k hk]
  zero_mem' k _ := rfl
  smul_mem' c a ha k hk := by simp [ha k hk]

theorem mem_typeSupportedVectors_iff {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (w : Fin g → ℂ) :
    w ∈ typeSupportedVectors ty σ ↔ tyPart ty σ w = w := by
  constructor
  · intro h
    funext k
    simp only [tyPart]
    split_ifs with hk
    · rfl
    · exact (h k hk).symm
  · intro h k hk
    rw [← h]
    simp [tyPart, hk]

def typeSupportedEquiv {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) :
    typeSupportedVectors ty σ ≃ₗ[ℂ] ({k // ty k = σ} → ℂ) where
  toFun v k := v.1 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun k => if h : ty k = σ then f ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv v := by
    apply Subtype.ext
    funext k
    by_cases h : ty k = σ
    · simp [h]
    · simp only [h, dite_false]
      exact (v.2 k h).symm
  right_inv f := by
    funext k
    simp [k.2]

theorem finrank_typeSupportedVectors {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) :
    finrank ℂ (typeSupportedVectors ty σ) = Nat.card {k // ty k = σ} := by
  rw [(typeSupportedEquiv ty σ).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem type_part_linear_independent (H : Host E) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ty P) {k k' : ℕ} (y : Fin k → D.La) (z : Fin k' → D.La) (σ : E →+* ℂ)
    (hz : ∀ b, tyPart ty σ (P (z b)) = 0) (hcount : Nat.card {i // ty i = σ} = k)
    (hrk : k + k' = finrank (𝓞 E) D.La) (hli : LinearIndependent (𝓞 E) (Sum.elim y z)) :
    LinearIndependent ℂ (fun a => tyPart ty σ (P (y a))) ∧
      ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty σ (P (y a))) ↔ tyPart ty σ w = w := by
  haveI := D.fin
  set T := pure_type_projection ty σ
  set S := Submodule.span ℂ (Set.range fun a => tyPart ty σ (P (y a)))
  have hT : ∀ w, T w = tyPart ty σ w := fun _ => rfl

  have hsmul : ∀ (s : 𝓞 E) (v : D.La), T (P (s • v)) = σ (s : E) • T (P v) := by
    intro s v
    funext i
    rw [typeProjection_apply, Pi.smul_apply, typeProjection_apply, smul_eq_mul]
    split_ifs with h
    · rw [hP.1, h]
    · simp

  have hmult : ∀ v : D.La, ∃ a : 𝓞 E, a ≠ 0 ∧ a • v ∈ Submodule.span (𝓞 E) (Set.range (Sum.elim y z)) := by
    intro v
    by_contra hne
    push_neg at hne
    have hli2 : LinearIndependent (𝓞 E) (fun o : Option (Fin k ⊕ Fin k') => o.elim v (Sum.elim y z)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [Fintype.sum_option] at hc
      simp only [Option.elim] at hc
      have hcn : c none = 0 := by
        by_contra h0
        apply hne (c none) h0
        have : c none • v = -∑ i, c (some i) • Sum.elim y z i := eq_neg_of_add_eq_zero_left hc
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      rw [hcn, zero_smul, zero_add] at hc
      have := Fintype.linearIndependent_iff.mp hli (fun i => c (some i)) hc
      intro o
      cases o with
      | none => exact hcn
      | some i => exact this i
    have hc := hli2.fintype_card_le_finrank
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at hc
    omega

  have hspan : ∀ v ∈ Submodule.span (𝓞 E) (Set.range (Sum.elim y z)), T (P v) ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      cases i with
      | inl a => exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        simp only [Sum.elim_inr]
        rw [hT, hz b]
        exact S.zero_mem
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact S.add_mem hx hy
    | smul s x _ hx => rw [hsmul]; exact S.smul_mem _ hx
  have hall : ∀ v : D.La, T (P v) ∈ S := by
    intro v
    obtain ⟨a, ha, hav⟩ := hmult v
    have h1 := hspan _ hav
    rw [hsmul] at h1
    have hσ : σ (a : E) ≠ 0 := by
      rw [map_ne_zero]
      exact_mod_cast ha
    have := S.smul_mem (σ (a : E))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hσ, one_smul] at this

  have hallC : ∀ w : Fin g → ℂ, T w ∈ S := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact hall v
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
    | smul r x _ hx =>
      have : T (r • x) = (r : ℂ) • T x := by
        rw [← map_smul]
        congr 1
      rw [this]
      exact S.smul_mem _ hx
  have hSV : S = typeSupportedVectors ty σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, mem_typeSupportedVectors_iff]
      funext i
      simp only [tyPart]
      split_ifs <;> rfl
    · intro w hw
      rw [mem_typeSupportedVectors_iff] at hw
      rw [← hw]
      exact hallC w
  refine ⟨?_, fun w => by rw [hSV, mem_typeSupportedVectors_iff]⟩
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  change k = finrank ℂ S
  rw [hSV, finrank_typeSupportedVectors, hcount]

theorem Host_rt0_conj_eq_neg (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero <;> assumption

theorem Host_rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  apply hd
  have h2 : -(H.d : ℂ) = 0 := by rw [← h1]; ring
  simpa using h2

theorem pure_type_projection_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsTypeFn H p q ty → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → IsPure hP x → LinearIndependent (𝓞 E) x → (LinearIndependent ℂ (fun a => tyPart ty τ (P (x (.inl a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty τ (P (x (.inl a)))) ↔ tyPart ty τ w = w) ∧ LinearIndependent ℂ (fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ↔ tyPart ty (ComplexEmbedding.conjugate τ) w = w := by
  intro E _ _ _ H D g ty P hP p q x τ hty hpq hτ hpure hli
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    apply Host_rt0_ne_zero H
    have : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
    simpa using this
  have hcτ : (ComplexEmbedding.conjugate τ) (H.rt : E) = -H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ, Host_rt0_conj_eq_neg]
  have hrk : p + q = finrank (𝓞 E) D.La := by rw [hpq, D.rank]
  constructor
  · refine type_part_linear_independent H D ty P hP (fun a => x (.inl a)) (fun b => x (.inr b)) τ ?_ ((hty τ).1 hτ) hrk ?_
    · intro b
      funext i
      simp only [tyPart, Pi.zero_apply]
      split_ifs with h
      · apply hpure.2 b i
        rw [h, hτ]
        simp only [sgnRt, Bool.false_eq_true, if_false]
        exact hne
      · rfl
    · convert hli using 1
      funext o
      cases o <;> rfl
  · have hq : Nat.card {i // ty i = ComplexEmbedding.conjugate τ} = q := by
      apply ((hty _).2)
      rw [hcτ]
      exact hne.symm
    refine type_part_linear_independent H D ty P hP (fun b => x (.inr b)) (fun a => x (.inl a)) _ ?_ hq (by rw [← hrk, add_comm]) ?_
    · intro a
      funext i
      simp only [tyPart, Pi.zero_apply]
      split_ifs with h
      · apply hpure.1 a i
        rw [h, hcτ]
        simp only [sgnRt, if_true]
        exact hne.symm
      · rfl
    · have := hli.comp (Equiv.sumComm (Fin q) (Fin p)) (Equiv.injective _)
      convert this using 1
      funext o
      cases o <;> rfl

end PositivityTheory.Xgf

end
