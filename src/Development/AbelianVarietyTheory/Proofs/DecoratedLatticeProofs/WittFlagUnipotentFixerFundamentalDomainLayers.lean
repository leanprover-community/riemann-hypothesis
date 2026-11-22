module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Layers

section Abstract

open scoped Pointwise

variable {A B U X G : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B] [MeasurableSpace B]
  [MeasurableSpace U] [MeasurableSpace X] [Group G] [MulAction G X]
  {mA : Measure A} {mB : Measure B} {ν : Measure U} [SFinite mA] [SFinite mB] [SFinite ν]

theorem null_middle {N : Set B} (hN : mB N = 0) : (mA.prod (mB.prod ν)) {p | p.2.1 ∈ N} = 0 := by
  have h : {p : A × (B × U) | p.2.1 ∈ N} = Set.univ ×ˢ (N ×ˢ Set.univ) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, hN]
  simp

theorem null_shear [mA.IsAddLeftInvariant] {φ : B → A} (hφ : Measurable φ) {N : Set A} (hN : mA N = 0) :
    (mA.prod (mB.prod ν)) {p | p.1 + φ p.2.1 ∈ N} = 0 := by
  have hM : MeasurableSet (toMeasurable mA N) := measurableSet_toMeasurable _ _
  have hM0 : mA (toMeasurable mA N) = 0 := by rw [measure_toMeasurable, hN]
  have hs : MeasurableSet {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N} :=
    (measurable_fst.add (hφ.comp (measurable_fst.comp measurable_snd))) hM
  refine measure_mono_null (t := {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N}) (fun p hp => subset_toMeasurable mA N hp) ?_
  rw [Measure.prod_apply_symm hs]
  have h0 : ∀ y : B × U, mA ((fun x => (x, y)) ⁻¹' {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N}) = 0 := fun y => by
    have h1 : (fun x : A => (x, y)) ⁻¹' {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N} =
        (fun x => φ y.1 + x) ⁻¹' toMeasurable mA N := by
      ext x; simp [add_comm]
    rw [h1, measure_preimage_add, hM0]
  exact (lintegral_congr h0).trans lintegral_zero

theorem isFundamentalDomain_layers [mA.IsAddLeftInvariant] (ΓA : AddSubgroup A) (ΓB : AddSubgroup B) [Countable ΓB]
    (κ : B → B → A) (hκ : ∀ b', Measurable (κ b')) (e : A × (B × U) ≃ᵐ X)
    (hfree : ∀ (g g' : G) (x : X), g • x = g' • x → g = g')
    (hG : ∀ g : G, ∃ (c' : ΓA) (b' : ΓB), ∀ p, g • e p = e (c'.1 + p.1 + κ b'.1 p.2.1, b'.1 + p.2.1, p.2.2))
    (hG' : ∀ (c' : ΓA) (b' : ΓB), ∃ g : G, ∀ p, g • e p = e (c'.1 + p.1 + κ b'.1 p.2.1, b'.1 + p.2.1, p.2.2))
    {𝓒 : Set A} {𝓕 : Set B} (hC : IsAddFundamentalDomain ΓA 𝓒 mA) (hF : IsAddFundamentalDomain ΓB 𝓕 mB) :
    IsFundamentalDomain G (e '' (𝓒 ×ˢ (𝓕 ×ˢ Set.univ))) ((mA.prod (mB.prod ν)).map e) := by
  have hmem : ∀ q, e q ∈ e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))) ↔ q ∈ 𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U)) :=
    fun q => e.injective.mem_set_image
  have hmp := (e.measurable.measurePreserving (mA.prod (mB.prod ν))).symm e
  refine ⟨?_, ?_, ?_⟩
  · have hS : NullMeasurableSet (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))) (mA.prod (mB.prod ν)) :=
      hC.nullMeasurableSet.prod (hF.nullMeasurableSet.prod nullMeasurableSet_univ)
    rw [e.image_eq_preimage_symm]
    exact hS.preimage hmp.quasiMeasurePreserving
  · rw [e.measurableEmbedding.ae_map_iff]
    have h1 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∃ g : ΓB, g +ᵥ p.2.1 ∈ 𝓕 := by
      have := null_middle (mA := mA) (ν := ν) (ae_iff.1 hF.ae_covers)
      exact ae_iff.2 this
    have h2 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ b' : ΓB, ∃ g : ΓA, g +ᵥ (p.1 + κ b'.1 p.2.1) ∈ 𝓒 := by
      rw [ae_all_iff]
      intro b'
      exact ae_iff.2 (null_shear (hκ b'.1) (ae_iff.1 hC.ae_covers))
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨b', hb⟩ := hp1
    obtain ⟨c', hc⟩ := hp2 b'
    obtain ⟨g, hg⟩ := hG' c' b'
    refine ⟨g, ?_⟩
    rw [hg p, hmem]
    refine ⟨?_, hb, Set.mem_univ _⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add] at hc
    simpa only [add_assoc] using hc
  · intro g₁ g₂ hne
    obtain ⟨c₁, b₁, h₁⟩ := hG g₁⁻¹
    obtain ⟨c₂, b₂, h₂⟩ := hG g₂⁻¹
    change (mA.prod (mB.prod ν)).map e (g₁ • (e '' _) ∩ g₂ • (e '' _)) = 0
    rw [e.map_apply]
    have hin : ∀ p, p ∈ e ⁻¹' (g₁ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U)))) ∩ g₂ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))))) →
        (c₁.1 + p.1 + κ b₁.1 p.2.1 ∈ 𝓒 ∧ b₁.1 + p.2.1 ∈ 𝓕) ∧ (c₂.1 + p.1 + κ b₂.1 p.2.1 ∈ 𝓒 ∧ b₂.1 + p.2.1 ∈ 𝓕) := by
      rintro p ⟨hp1, hp2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₁, hmem] at hp1
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₂, hmem] at hp2
      exact ⟨⟨hp1.1, hp1.2.1⟩, ⟨hp2.1, hp2.2.1⟩⟩
    by_cases hb : b₁ = b₂
    · subst hb
      by_cases hc : c₁ = c₂
      · subst hc
        refine measure_mono_null (t := ∅) (fun p hp => ?_) (measure_empty)
        have : g₁⁻¹ • e p = g₂⁻¹ • e p := by rw [h₁, h₂]
        exact absurd (inv_injective (hfree _ _ _ this)) hne
      · have hd := hC.aedisjoint (i := -c₁) (j := -c₂) (fun h => hc (neg_injective h))
        have hd' : mA ((-c₁ +ᵥ 𝓒) ∩ (-c₂ +ᵥ 𝓒)) = 0 := hd
        refine measure_mono_null (fun p hp => ?_) (null_shear (hκ b₁.1) hd')
        obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hin p hp
        refine ⟨?_, ?_⟩
        · rw [Set.mem_neg_vadd_set_iff]
          simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h1
        · rw [Set.mem_neg_vadd_set_iff]
          simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h2
    · have hd := hF.aedisjoint (i := -b₁) (j := -b₂) (fun h => hb (neg_injective h))
      have hd' : mB ((-b₁ +ᵥ 𝓕) ∩ (-b₂ +ᵥ 𝓕)) = 0 := hd
      refine measure_mono_null (fun p hp => ?_) (null_middle (mA := mA) (ν := ν) hd')
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hin p hp
      exact ⟨Set.mem_neg_vadd_set_iff.2 h1, Set.mem_neg_vadd_set_iff.2 h2⟩

end Abstract

section Concrete

variable {D : D7}

theorem act_coords {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c' c : skewA D ρ) (b' b : Mx D ρ S₀.rank)
    (u : GL (Fin ρ) (AE D)) :
    d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u)) =
      d.nC (c' + c + cComm S₀ b' b) * (d.nB (b' + b) * d.levi u) := by
  have h1 : d.nB b' * d.nC c = d.nC c * d.nB b' := (d.nC_mul_nB b' c).symm
  have h2 : d.nB (b' + b) * d.nC (cComm S₀ b' b) = d.nC (cComm S₀ b' b) * d.nB (b' + b) :=
    (d.nC_mul_nB _ _).symm
  calc d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u))
      = d.nC c' * (d.nB b' * d.nC c) * d.nB b * d.levi u := by simp only [mul_assoc]
    _ = d.nC c' * d.nC c * (d.nB b' * d.nB b) * d.levi u := by rw [h1]; simp only [mul_assoc]
    _ = d.nC c' * d.nC c * d.nC (cComm S₀ b' b) * d.nB (b' + b) * d.levi u := by
        rw [d.nB_mul_nB, h2]; simp only [mul_assoc]
    _ = d.nC (c' + c + cComm S₀ b' b) * (d.nB (b' + b) * d.levi u) := by
        rw [d.nC_add, d.nC_add]; simp only [mul_assoc]

end Concrete

end GlobalTheory.Layers

end
