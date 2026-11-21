import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.EigenlineBaseChange

theorem isIntegral_coe_iff {M : IntermediateField ℚ ℂ} (x : M) : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective

theorem span_eq_top {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M) (τ : D.what₂.Tau) (s : M)
    (hs : TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}) :
    Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} = ⊤ := by
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hsm : s ∈ TaylorLogMetric.ellT D M τ := hs ▸ Submodule.mem_span_singleton_self s
  rw [GlobalTheory.Glob.mem_ellT_iff hM] at hsm
  let g : ∀ y ∈ D.host.AA0, 𝓞 M := fun y hy =>
    ⟨s * ⟨_, hM τ (D.host.conj y)⟩, (isIntegral_coe_iff _).1 (hsm y hy)⟩
  set I : Ideal (𝓞 M) := Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
    ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} with hI
  have hg : ∀ y hy, g y hy ∈ I := fun y hy => Ideal.subset_span ⟨y, hy, rfl⟩
  by_contra hI1
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := hg 1 (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D)
    rw [h, Ideal.mem_bot] at h1
    have h2 : (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj 1) = 0 :=
      congrArg (fun a : 𝓞 M => ((a : M) : ℂ)) h1
    rw [map_one, map_one, mul_one] at h2
    exact hs0 (Subtype.ext h2)
  obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := M) hI0 hI1
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)] at hx
  have hxs : x * s ∈ TaylorLogMetric.ellT D M τ := by
    rw [GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
      (hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hg y hy)))
    have h1 : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
    have h2 : ((c : M) : ℂ) = (x : ℂ) * ((s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)) :=
      congrArg (fun a : M => (a : ℂ)) hc
    rw [h2, ← mul_assoc] at h1
    exact h1
  rw [hs, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  refine hx1 ((FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩)
  exact mul_right_cancel₀ hs0 hc

theorem ellT_eq_span_of_le : ∀ (D : D7) (M M' : IntermediateField ℚ ℂ) [NumberField M] [NumberField M'] (hle : M ≤ M'), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s} → TaylorLogMetric.ellT D M' τ = Submodule.span (𝓞 M') {(⟨(s : ℂ), hle s.2⟩ : M')} := by
  intro D M M' _ _ hle hM τ s hs
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M' := fun τ x => hle (hM τ x)
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hs0' : (s : ℂ) ≠ 0 := fun h => hs0 (Subtype.ext h)
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM'] at hx
    have key : ∀ a ∈ Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
        ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)},
        IsIntegral ℤ ((x : ℂ) * (s : ℂ)⁻¹ * ((a : M) : ℂ)) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, hy, e⟩ := ha
        rw [e, mul_assoc, inv_mul_cancel_left₀ hs0']
        exact hx y hy
      | zero => simpa using isIntegral_zero
      | add a b _ _ ha hb =>
        have e : (((a + b : 𝓞 M) : M) : ℂ) = ((a : M) : ℂ) + ((b : M) : ℂ) := rfl
        rw [e, mul_add]
        exact ha.add hb
      | smul c a _ ha =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
        have e : (((c • a : 𝓞 M) : M) : ℂ) = ((c : M) : ℂ) * ((a : M) : ℂ) := rfl
        rw [e, mul_left_comm]
        exact hc.mul ha
    have h1 := key 1 (by rw [span_eq_top hM τ s hs]; trivial)
    have e : (((1 : 𝓞 M) : M) : ℂ) = 1 := rfl
    rw [e, mul_one] at h1
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨(s : ℂ), hle s.2⟩ : M')⁻¹, (isIntegral_coe_iff _).1 h1⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hs0' (congrArg (fun a : M' => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM']
    exact (GlobalTheory.Glob.mem_ellT_iff hM τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)

end GlobalTheory.EigenlineBaseChange
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MeanPeriodGenerator

theorem ellT_eq_span (D : D7) (cD : D.what₂.Tau → ℂ) (h : IsDgen D cD)
    (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M)
    (τ : D.what₂.Tau) (hc : cD τ ∈ M) :
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {(⟨cD τ, hc⟩ : M)} := by
  obtain ⟨M₀, _, hM₀, hs⟩ := h
  obtain ⟨s, hsc, hs⟩ := hs τ
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm
  have hc0 : cD τ ≠ 0 := fun h => hs0 (Subtype.ext (hsc.trans h))
  haveI : NumberField (M ⊔ M₀ : IntermediateField ℚ ℂ) := NumberField.mk
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ (M ⊔ M₀ : IntermediateField ℚ ℂ) :=
    fun τ x => (le_sup_left : M ≤ M ⊔ M₀) (hM τ x)
  have h' := GlobalTheory.EigenlineBaseChange.ellT_eq_span_of_le D M₀ (M ⊔ M₀) le_sup_right hM₀ τ s hs
  apply le_antisymm
  · intro x hx
    have hx' : (⟨(x : ℂ), (le_sup_left : M ≤ M ⊔ M₀) x.2⟩ : (M ⊔ M₀ : IntermediateField ℚ ℂ)) ∈
        TaylorLogMetric.ellT D (M ⊔ M₀) τ := by
      rw [GlobalTheory.Glob.mem_ellT_iff hM']
      exact (GlobalTheory.Glob.mem_ellT_iff hM τ x).1 hx
    rw [h', Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hcx⟩ := hx'
    have e : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) * (s : ℂ) = (x : ℂ) :=
      congrArg (fun a : (M ⊔ M₀ : IntermediateField ℚ ℂ) => (a : ℂ)) hcx
    have hi : IsIntegral ℤ ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) :=
      (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).2 c.isIntegral_coe
    have e2 : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) = (x : ℂ) * (cD τ)⁻¹ := by
      rw [← e, hsc, mul_inv_cancel_right₀ hc0]
    rw [e2] at hi
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨cD τ, hc⟩ : M)⁻¹, (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).1 hi⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hc0 (congrArg (fun a : M => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM]
    have := (GlobalTheory.Glob.mem_ellT_iff hM₀ τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)
    rw [hsc] at this
    exact this

theorem mean_logMet_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  intro D cc dl cD hc hmean hgen
  have hne : ∀ τ, cD τ ≠ 0 := by
    intro τ h
    obtain ⟨M₀, _, hM₀, hs⟩ := hgen
    obtain ⟨s, hsc, hs⟩ := hs τ
    exact GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm (Subtype.ext (hsc.trans h))
  refine ⟨hne, fun M _ hD hcM τ => ?_⟩
  haveI : NumberField M := NumberField.mk
  have hell := ellT_eq_span D cD hgen M hD.1 τ (hcM τ)
  have hl : TaylorLogMetric.liftM M (cD τ) = ⟨cD τ, hcM τ⟩ := dif_pos (hcM τ)
  rw [hl, ← hmean M hD τ, Finset.sum_neg_distrib]
  exact (GlobalTheory.Glob.meanLogOm_eq_of_gen hD.1 (GlobalTheory.Glob.area_lamConj_pos hc hD) hell.symm).symm

end GlobalTheory.MeanPeriodGenerator
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  atlas_forward_decl GlobalTheory.MeanPeriodGenerator.mean_logMet_eq
end
