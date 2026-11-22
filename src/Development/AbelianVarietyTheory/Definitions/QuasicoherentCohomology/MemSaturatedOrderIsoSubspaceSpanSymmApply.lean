module

public import Mathlib

@[expose] public section

open scoped nonZeroDivisors Pointwise

namespace GlobalTheory

section Basic

variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

def saturation (N : Submodule R M) : Submodule R M :=
  (Submodule.torsion R (M ⧸ N)).comap N.mkQ

def IsSaturatedSubmodule (N : Submodule R M) : Prop :=
  saturation N = N

theorem mem_saturation_iff' {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a ∈ R⁰, a • x ∈ N := by
  change N.mkQ x ∈ Submodule.torsion R (M ⧸ N) ↔ _
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact h
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul] at h
    exact h

theorem mem_saturation_iff [IsDomain R] {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  rw [mem_saturation_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]

theorem le_saturation (N : Submodule R M) : N ≤ saturation N := fun x hx => mem_saturation_iff'.2 ⟨1, one_mem _, by rwa [one_smul]⟩

@[gcongr]
theorem saturation_mono {N N' : Submodule R M} (h : N ≤ N') : saturation N ≤ saturation N' := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  exact mem_saturation_iff'.2 ⟨a, ha, h hax⟩

@[simp]
theorem saturation_saturation (N : Submodule R M) : saturation (saturation N) = saturation N := by
  refine le_antisymm (fun x hx => ?_) (le_saturation _)
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hax
  refine mem_saturation_iff'.2 ⟨b * a, mul_mem hb ha, ?_⟩
  rwa [mul_smul]

theorem IsSaturatedSubmodule.saturation_eq {N : Submodule R M} (h : IsSaturatedSubmodule N) :
    saturation N = N := h

theorem isSaturatedSubmodule_iff_le {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ saturation N ≤ N := ⟨fun h => h.saturation_eq.le, fun h => le_antisymm h (le_saturation N)⟩

theorem isSaturatedSubmodule_iff' {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a ∈ R⁰, ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff_le]
  constructor
  · intro h a ha x hx
    exact h (mem_saturation_iff'.2 ⟨a, ha, hx⟩)
  · intro h x hx
    obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
    exact h a ha x hax

theorem isSaturatedSubmodule_iff [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a : R, a ≠ 0 → ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]

theorem isSaturatedSubmodule_iff_torsion_eq_bot {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Submodule.torsion R (M ⧸ N) = ⊥ := by
  rw [isSaturatedSubmodule_iff_le, Submodule.eq_bot_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact (Submodule.Quotient.mk_eq_zero N).2 (h (show x ∈ saturation N from hy))
  · intro h x hx
    exact (Submodule.Quotient.mk_eq_zero N).1 (h (N.mkQ x) hx)

theorem isSaturatedSubmodule_iff_isTorsionFree [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Module.IsTorsionFree R (M ⧸ N) := by
  rw [isSaturatedSubmodule_iff_torsion_eq_bot, Submodule.isTorsionFree_iff_torsion_eq_bot]

theorem IsSaturatedSubmodule.isTorsionFree_quotient [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : Module.IsTorsionFree R (M ⧸ N) := isSaturatedSubmodule_iff_isTorsionFree.1 h

theorem isSaturatedSubmodule_saturation (N : Submodule R M) :
    IsSaturatedSubmodule (saturation N) := by
  rw [isSaturatedSubmodule_iff_le, saturation_saturation]

instance isTorsionFree_quotient_saturation [IsDomain R] (N : Submodule R M) :
    Module.IsTorsionFree R (M ⧸ saturation N) :=
  (isSaturatedSubmodule_saturation N).isTorsionFree_quotient

theorem saturation_inf (N P : Submodule R M) :
    saturation (N ⊓ P) = saturation N ⊓ saturation P := by
  refine le_antisymm (le_inf (saturation_mono inf_le_left) (saturation_mono inf_le_right)) ?_
  intro x hx
  obtain ⟨hN, hP⟩ := Submodule.mem_inf.1 hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hN
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hP
  refine mem_saturation_iff'.2 ⟨a * b, mul_mem ha hb, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]
    exact N.smul_mem b hax
  · rw [mul_smul]
    exact P.smul_mem a hbx

theorem IsSaturatedSubmodule.inf {N P : Submodule R M} (hN : IsSaturatedSubmodule N)
    (hP : IsSaturatedSubmodule P) : IsSaturatedSubmodule (N ⊓ P) := by
  unfold IsSaturatedSubmodule
  rw [saturation_inf, hN.saturation_eq, hP.saturation_eq]

theorem saturation_comap (f : M →ₗ[R] M') (N : Submodule R M') :
    saturation (N.comap f) = (saturation N).comap f := by
  ext x
  simp only [Submodule.mem_comap, mem_saturation_iff', map_smul]

theorem IsSaturatedSubmodule.comap {N : Submodule R M'} (h : IsSaturatedSubmodule N)
    (f : M →ₗ[R] M') : IsSaturatedSubmodule (N.comap f) := by
  unfold IsSaturatedSubmodule
  rw [saturation_comap, h.saturation_eq]

end Basic

section Rank

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

end Rank

section Relative

variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']

end Relative

section Localisation

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]

end Localisation

section AmbientLocalisation

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]

include p

theorem mem_span_localization_iff (N : Submodule R V) (x : V) :
    x ∈ Submodule.span S (N : Set V) ↔ ∃ a ∈ p, a • x ∈ N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact N.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_mem ha hb, ?_⟩
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact N.smul_mem b hay
      · rw [mul_smul]
        exact N.smul_mem a hbz
    | smul s y _ hy =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p s
      refine ⟨(t : R) * a, mul_mem t.2 ha, ?_⟩
      have e : ((t : R) * a) • (IsLocalization.mk' S r t • y) = r • (a • y) := by
        rw [mul_smul, smul_comm a (IsLocalization.mk' S r t) y, ← algebraMap_smul S (t : R),
          smul_smul (algebraMap R S t), IsLocalization.mk'_spec', algebraMap_smul]
      rw [e]
      exact N.smul_mem r hay
  · rintro ⟨a, ha, hax⟩
    have hu : IsUnit (algebraMap R S a) := IsLocalization.map_units S (⟨a, ha⟩ : p)
    rw [← Submodule.smul_mem_iff_of_isUnit _ hu, algebraMap_smul]
    exact Submodule.subset_span hax

end AmbientLocalisation

section GenericFibre

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]

end GenericFibre

section Lattice

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

end Lattice

section Examples

end Examples

end GlobalTheory
