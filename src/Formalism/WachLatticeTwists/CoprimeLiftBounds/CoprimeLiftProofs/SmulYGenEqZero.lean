import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne

section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.ColumnGeneratorDecomposition Formalism.NG.ColKerChi

theorem rel : StatRel := by
  intro A T' G _ _ _ _ M _ _ r χ E e₁ δ ι _ D j Kc k0 φ l
  have hR : ∀ z ∈ colRelJ r χ E e₁ δ D j Kc k0, φ (Submodule.Quotient.mk z) = 0 := fun z hz => by
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hsing : ∀ (x : A) (v : A × (Fin (j l) → A) × A),
      x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l v = Pi.single l (x • v) := by
    intro x v
    funext k
    by_cases h : k = l
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hsing2 : ∀ (x : A) (a : Fin (j l)) (t : A),
      x • (Pi.single a t : Fin (j l) → A) = Pi.single a (x * t) := by
    intro x a t
    funext k
    by_cases h : k = a
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hgen : ∀ (x c : A) (s : Fin (j l) → A) (c₀ : A),
      x • (colGenJ (0 : Ymod r χ E) l c s c₀ : ColFreeJ A r χ E ι j) =
        colGenJ 0 l (x * c) (x • s) (x * c₀) := by
    intro x c s c₀
    show (x • (0 : Ymod r χ E), x • Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (c, s, c₀)) =
      ((0 : Ymod r χ E), Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (x * c, x • s, x * c₀))
    rw [smul_zero, hsing]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_smul]
    show φ (E • Submodule.Quotient.mk ((colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j))) = 0
    rw [← Submodule.Quotient.mk_smul, hgen, mul_one, smul_zero, mul_zero]
    exact hR _ (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))
  · intro a
    have hz := hR (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    have e : (colGenJ (0 : Ymod r χ E) l 0 (Pi.single a (1 - e₁)) 0 : ColFreeJ A r χ E ι j) =
        (1 - e₁) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 := by
      rw [hgen, mul_zero, hsing2, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, one_smul, sub_eq_zero] at hz
    exact hz.symm
  · have hz := hR (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    have e : (colGenJ (0 : Ymod r χ E) l 0 0 (algebraMap T' A δ - E) : ColFreeJ A r χ E ι j) =
        (algebraMap T' A δ - E) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j) := by
      rw [hgen, mul_zero, smul_zero, mul_one]
    rw [e, Submodule.Quotient.mk_smul, map_smul, sub_smul, sub_eq_zero] at hz
    exact hz
  · intro g hg
    have hz := hR (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)))
      (Submodule.subset_span (Or.inr ⟨l, g, hg, rfl⟩))
    have key : (colGenJ (⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E) l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) (fun a => -(algebraMap T' A δ * Kc l a g))
        (-(algebraMap T' A δ * k0 l g)) : ColFreeJ A r χ E ι j) =
        ((⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ : Ymod r χ E), 0) +
          (((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) • (colGenJ (0 : Ymod r χ E) l 1 0 0 : ColFreeJ A r χ E ι j) +
          (∑ a, (-(algebraMap T' A δ * Kc l a g)) • colGenJ (0 : Ymod r χ E) l 0 (Pi.single a 1) 0 +
          (-(algebraMap T' A δ * k0 l g)) • (colGenJ (0 : Ymod r χ E) l 0 0 1 : ColFreeJ A r χ E ι j))) := by
      simp only [hgen, hsing2, mul_one, mul_zero, smul_zero]
      refine Prod.ext ?_ ?_
      · simp [colGenJ, Prod.fst_sum]
      · funext k
        by_cases hk : k = l
        · subst hk
          simp [colGenJ, Prod.snd_sum, Finset.sum_apply, funext_iff, Pi.single_apply]
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · simp [Prod.fst_sum]
          · funext a
            simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
          · simp [Prod.snd_sum]
        · simp [colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne hk]
    rw [key] at hz
    simp only [← Submodule.mkQ_apply, map_add, map_smul, map_sum] at hz
    have hz' : φ (yGen r χ E e₁ δ D j Kc k0 g) + ((uElt r χ g - 1) • φ (nuGen r χ E e₁ δ D j Kc k0 l) +
        (∑ a, (-(algebraMap T' A δ * Kc l a g)) • φ (sigGen r χ E e₁ δ D j Kc k0 l a) +
        (-(algebraMap T' A δ * k0 l g)) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l))) = 0 := hz
    simp only [sub_smul, one_smul, neg_smul, mul_smul, Finset.sum_neg_distrib,
      ← Finset.smul_sum] at hz'
    rw [smul_add, ← sub_eq_zero, ← hz']
    abel

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section SlopeTestRemainingChoices
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

def cobZ (ρ : Representation O G M) (v : M) : coZ1s ρ :=
  ⟨coD0 ρ v, fun g h => by
    show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
    rw [map_mul, map_sub, Module.End.mul_apply]; abel⟩

lemma mkQ_cobZ (ρ : Representation O G M) (v : M) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) (cobZ ρ v) : H1z ρ) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self (coD0 ρ) v

lemma mkQ_eq_zero_of (ρ : Representation O G M) (z : coZ1s ρ) (v : M)
    (h : ∀ g, (z : G → M) g = ρ g v - v) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) z : H1z ρ) = 0 := by
  have hz : z = cobZ ρ v := Subtype.ext (funext h)
  rw [hz]
  exact mkQ_cobZ ρ v

end SlopeTestRemainingChoices

section Y
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

lemma ycoc_eq (r : G →* A) (χ : G →* T'ˣ) (E : A) (g : G) :
    ycoc r χ E g =
      (((χ g)⁻¹ : T'ˣ) : T') • ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) := by
  show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = _
  rw [sub_mul, sub_mul, smul_sub, one_mul, smul_mul_assoc,
    Algebra.smul_def (((χ g)⁻¹ : T'ˣ) : T') (algebraMap T' A ((χ g : T'ˣ) : T') * E), ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]

lemma smul_yGen_eq_zero (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (a : A) (g : G)
    (h : a * ycoc r χ E g = 0) : a • yGen r χ E e₁ δ D j Kc k0 g = 0 := by
  unfold yGen
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  convert Submodule.zero_mem _ using 1
  exact Prod.ext (Subtype.ext h) (smul_zero _)

end Y

theorem qAlg : StatQAlg := by
  intro A T' G _ _ _ _ r χ E γ ζ h hζ
  rw [ycoc_eq, mul_smul_comm, hζ, ← mul_assoc, h, zero_mul, smul_zero]

theorem colChiC : StatColChiC := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 he hE hk φ l
  obtain ⟨_, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) (D l)
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) (D l)))
  rw [Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) :
      coZ1s (resRep (uRep O (M := M) r χ) (D l))) : D l → M) ∈
    LinearMap.range (coD0 (resRep (uRep O (M := M) r χ) (D l)))
  rw [LinearMap.mem_range]
  refine ⟨-φ (nuGen r χ E e₁ δ D j Kc k0 l), ?_⟩
  funext g
  show uElt r χ (g : G) • -φ (nuGen r χ E e₁ δ D j Kc k0 l) - -φ (nuGen r χ E e₁ δ D j Kc k0 l) =
    φ (yGen r χ E e₁ δ D j Kc k0 (g : G))
  obtain ⟨a0, ha0⟩ := hk l g
  have h := hy g g.2
  simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, ha0, mul_smul, hE] at h
  rw [eq_neg_of_add_eq_zero_left h, smul_neg]
  abel

theorem colChiOne : StatColChiOne := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' u hu he hE hδ hk φ l
  obtain ⟨hnu, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  have h2 : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) =
      (δO * δO * (ℓ : O) ^ e' l * u l g) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l) := by
    intro g hg
    have h := hy g hg
    simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, hu, sub_self, add_zero, hk l g hg,
      hδ] at h
    rw [h, smul_smul]
    congr 1
    ring
  refine ⟨by rw [← hE]; exact hnu, h2, fun I hI => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ))) =
    (0 : H1z (resRep (resRep (uRep O (M := M) r χ) (D l)) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : D l) : G)) = 0
    rw [h2 _ (g : D l).2, hI g g.2, mul_zero, zero_smul]
  rw [hz]
  exact Submodule.zero_mem _

theorem unrOutside : StatUnrOutside := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI
  have hy : ∀ g ∈ I, ycoc r χ E g = 0 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hI g hg
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = 0
    rw [h1, h2, inv_one, Units.val_one, one_smul, sub_self, zero_mul]
  refine ⟨hy, fun φ => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (1 : A) (g : G)
      (by rw [one_mul]; exact hy g g.2)
    rw [one_smul] at h0
    rw [h0, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

theorem unrS : StatUnrS := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI φ
  have hy0 : ∀ g ∈ I, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := by
    intro g hg
    obtain ⟨a, ha, hinj⟩ := hI g hg
    apply hinj
    rw [← map_smul, smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 a g
      (by rw [ycoc_eq, mul_smul_comm, ha, smul_zero]), map_zero]
  refine ⟨hy0, ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    exact hy0 g g.2
  rw [hz]
  exact Submodule.zero_mem _

end Formalism.RepresentationBoundsCohomology.BR
end
end
