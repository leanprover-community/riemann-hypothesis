import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_eq_zero_of_lTensor_subtype_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type)
      [AddCommGroup N] [Module R N] (K : Type) [AddCommGroup K] [Module R K] (I : Submodule R K),
      (∀ (a : R) (x : K), a ≠ 0 → a • x ∈ I → ∀ k, r k • x ∈ I) →
      ∀ w : N ⊗[R] I, I.subtype.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ _ _ r N _ _ K _ _ I hI w hw k
  let I' : Submodule R K :=
    { carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ I}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        rw [smul_add]
        refine I.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact I.smul_mem _ hax
        · rw [mul_smul]; exact I.smul_mem _ hby
      smul_mem' := by
        rintro c x ⟨a, ha, hax⟩
        refine ⟨a, ha, ?_⟩
        rw [smul_comm]; exact I.smul_mem _ hax }
  have hle : I ≤ I' := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  have hflat : Module.Flat R (K ⧸ I') := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := I'.mkQ_surjective y
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hy
    have hax : (a : R) • x ∈ I' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using ha
    obtain ⟨b, hb, hbx⟩ := hax
    have hx : x ∈ I' := ⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero a.2), by
      rw [mul_smul]; exact hbx⟩
    simpa using (Submodule.Quotient.mk_eq_zero I').2 hx
  have hinj : Function.Injective (I'.subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat I'.mkQ I'.mkQ_surjective I'.subtype
      I'.injective_subtype (LinearMap.exact_subtype_mkQ I') N
  let ι : I →ₗ[R] I' := Submodule.inclusion hle
  let φ : I' →ₗ[R] I := LinearMap.codRestrict I (r k • I'.subtype) (fun x => by
    obtain ⟨a, ha, hax⟩ := x.2
    exact hI a x ha hax k)
  have h1 : ι.lTensor N w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact hw
  have hcomp : φ ∘ₗ ι = r k • LinearMap.id := by
    ext x
    rfl
  have h2 : φ.lTensor N (ι.lTensor N w) = r k • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_smul,
      LinearMap.lTensor_id]
    rfl
  rw [← h2, h1, map_zero]

end GlobalTheory.CompanionTheory.Dblock
end

section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_mem_range_lTensor_of_lTensor_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R)
      (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀]
      (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂]
      (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
      (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) →
      (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) →
      (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) →
      (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) →
      ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := by
  intro p _ R _ _ _ r N _ _ K₀ _ _ K₁ _ _ K₂ _ _ K₃ _ _ d₀ d₁ d₂ hr hdd h1 h2 h3 w hw k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : ∀ k, r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    intro k
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel hp]
    exact (hr k).symm
  have hsat : ∀ (a : R) (x : K₂), a ≠ 0 → a • x ∈ LinearMap.range d₁ →
      ∀ k, r k • x ∈ LinearMap.range d₁ := by
    rintro a x ha ⟨y, hy⟩ k
    have hax : a • d₂ x = 0 := by
      rw [← map_smul, ← hy, hdd]
    have h0 : d₂ (r (k + 1) • x) = 0 := by
      rw [map_smul]
      exact h3 a _ ha hax (k + 1)
    have h4 := h2 _ h0 (k + 1)
    rw [hrk k, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ h4
  have hsub : (LinearMap.range d₁).subtype ∘ₗ d₁.rangeRestrict = d₁ := by
    ext x
    rfl
  have hw' : (LinearMap.range d₁).subtype.lTensor N (d₁.rangeRestrict.lTensor N w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]
    exact hw
  have h5 := smul_eq_zero_of_lTensor_subtype_eq_zero R r N K₂ (LinearMap.range d₁) hsat _ hw' (k + 1)
  have h6 : d₁.rangeRestrict.lTensor N (r (k + 1) • w) = 0 := by
    rw [map_smul]
    exact h5
  have hex : Function.Exact (LinearMap.ker d₁).subtype d₁.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : d₁ x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext z.2
  obtain ⟨u, hu⟩ := (lTensor_exact N hex d₁.surjective_rangeRestrict _).1 h6
  have h7 : ∀ u : N ⊗[R] LinearMap.ker d₁,
      r (k + 1) • (LinearMap.ker d₁).subtype.lTensor N u ∈ LinearMap.range (d₀.lTensor N) := by
    intro u
    induction u with
    | zero => simp
    | tmul n z =>
      obtain ⟨y, hy⟩ := h1 z z.2 (k + 1)
      exact ⟨n ⊗ₜ y, by simp [hy, TensorProduct.tmul_smul]⟩
    | add a b ha hb =>
      rw [map_add, smul_add]
      exact Submodule.add_mem _ ha hb
  rw [hrk k, mul_smul, mul_smul, ← hu]
  exact Submodule.smul_mem _ _ (h7 u)

end GlobalTheory.CompanionTheory.Dblock
end
