import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import BuildAid.ForwardExisting

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
end
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  atlas_forward_decl GlobalTheory.WpFam.TrAdd.main
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.WpFam.TrIs

theorem main : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  obtain ⟨_, _, _, hL0, ⟨𝔞, h𝔞, hL1⟩, _, _, _⟩ := hT
  obtain ⟨hsub, _, hleft, hright⟩ := GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hmem𝔞 : ∀ a' : K, a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a'
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ ι '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ ι '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : ∀ a : K, ι a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : ∀ a' : K, ι a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    intro a'
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← ι.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  have hTr : ∀ x x' : K, Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x x' => (hA _).symm
  refine ⟨hsub, ?_, ?_, hleft, hright, ?_, ?_⟩
  · intro x x' h
    have hd := (hTr x x').1 h
    rw [h0, h1, hone, hmem𝔞]
    constructor
    · intro hx
      have := add_mem hd hx
      rwa [sub_add_cancel] at this
    · intro hx
      have := sub_mem hx hd
      rwa [sub_sub_cancel] at this
  · intro x x' hx hx'
    rw [hTr]
    exact sub_mem ((hmem𝔞 x').1 ((h1 x').1 hx')) ((hone x).1 ((h0 x).1 hx))
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL0' z).1 hz
    exact ⟨k, e⟩
  · intro z hz
    obtain ⟨k, -, e⟩ := (hL1' z).1 hz
    exact ⟨k, e⟩

end GlobalTheory.WpFam.TrIs
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  atlas_forward_decl GlobalTheory.WpFam.TrIs.main
end
