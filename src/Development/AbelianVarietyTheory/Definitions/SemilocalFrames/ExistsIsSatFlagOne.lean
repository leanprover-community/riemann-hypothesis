import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E) (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h
    · rw [mul_smul]; exact Λ.smul_mem _ h'
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have : (b * d) • (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) • x = a • d • x := by
      rw [← algebraMap_smul E (b * d), ← algebraMap_smul E a, ← algebraMap_smul E d, smul_smul, smul_smul]
      congr 1
      rw [map_mul]; field_simp
    rw [this]; exact Λ.smul_mem _ h

theorem span_inf {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (W : Submodule E (Fin n → E)) :
    Submodule.span E ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = W := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun y hy => hy.2
  · intro y hy
    obtain ⟨d, hd, h⟩ := exists_smul_mem Λ y (hΛ ▸ Submodule.mem_top)
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd
    have h1 : d • y ∈ Submodule.span E
        ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.subset_span ⟨h, (W.restrictScalars (𝓞 E)).smul_mem d hy⟩
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ h1
    rwa [← algebraMap_smul E d, smul_smul, inv_mul_cancel₀ hd1, one_smul] at h2




theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))


theorem finrank_span_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) =
      Module.finrank E (Submodule.span E s) := by
  letI : Algebra E ℂ := φ.toAlgebra
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent E s
  haveI : Finite t := hli.finite
  haveI : Fintype t := Fintype.ofFinite t
  have hli' : LinearIndependent ℂ fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E)) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hli'
  rw [Subtype.range_coe, hsp] at h1
  rw [h1, ← h2]
  suffices hs : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) =
      Submodule.span ℂ (Set.range fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E))) by rw [hs]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span E t := hsp ▸ Submodule.subset_span hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    | zero =>
      have : (fun l : Fin n => φ ((0 : Fin n → E) l)) = 0 := by ext; simp
      simp only [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun l : Fin n => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      simp only [this]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : (fun l : Fin n => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      simp only [this]; exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i, hts i.2, rfl⟩



end GlobalTheory.FlagMeas.SatModel
