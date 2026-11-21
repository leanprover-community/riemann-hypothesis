import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundleStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotient
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage

section
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory
theorem ses_precomp_iso_postcomp_coker_zero : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  intro X A E₁ E₂ E₃ F a b h hS f e _ hf ι hF
  have hι : ι = 0 := hF.eq_of_src _ _
  subst hι
  have hz : f ≫ b ≫ cokernel.π (0 : F ⟶ E₃) = 0 := by
    rw [hf, Category.assoc, reassoc_of% h, zero_comp, comp_zero]
  refine ⟨hz, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hS
  refine ShortComplex.isoMk (asIso e).symm (Iso.refl _) (asIso (cokernel.π (0 : F ⟶ E₃))) ?_ ?_
  · simp [hf]
  · simp
end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_cokernel_compose : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  atlas_forward_decl GlobalTheory.ses_precomp_iso_postcomp_coker_zero
end

section
section
open CategoryTheory Limits AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullbackSub

theorem shortExact_pullback_mono {C : Type*} [Category C] [Abelian C] {A E₂ E₃ F : C}
    (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e] (hf : f = e ≫ pullback.fst b ι) :
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  subst hf
  have hz : (e ≫ pullback.fst b ι) ≫ b ≫ cokernel.π ι = 0 := by
    rw [Category.assoc, ← Category.assoc (pullback.fst b ι), pullback.condition, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  refine ⟨hz, ?_⟩
  have hmf : Mono (e ≫ pullback.fst b ι) := inferInstance
  have hk := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel ι)
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) hmf
    (inferInstanceAs (Epi (b ≫ cokernel.π ι)))
  let ei : A ≅ pullback b ι := asIso e
  have hei : ei.hom = e := rfl
  have key : ∀ {T : C} (x : T ⟶ pullback b ι), (x ≫ ei.inv) ≫ e ≫ pullback.fst b ι = x ≫ pullback.fst b ι := by
    intro T x; rw [← hei, Category.assoc, Iso.inv_hom_id_assoc]
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} g hg => pullback.lift g (KernelFork.IsLimit.lift' hk (g ≫ b)
        (by simpa [Category.assoc] using hg)).1
        (KernelFork.IsLimit.lift' hk (g ≫ b) (by simpa [Category.assoc] using hg)).2.symm ≫ ei.inv)
    (fun {T} g hg => ?_) (fun {T} g hg m hm => ?_)
  · exact (key _).trans (pullback.lift_fst _ _ _)
  · rw [← cancel_mono (e ≫ pullback.fst b ι)]
    exact hm.trans ((key _).trans (pullback.lift_fst _ _ _)).symm

theorem shortExact_preimage_of_epi_mono : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact :=
  fun X _ _ _ _ b ι _ _ f e _ hf => shortExact_pullback_mono b ι f e hf

end GlobalTheory.PullbackSub
end
end

open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_of_pullback_cokernel : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  atlas_forward_decl GlobalTheory.PullbackSub.shortExact_preimage_of_epi_mono
end

section
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem shortExact_pullback_cokernel_of_shortExact {C : Type*} [Category C] [Abelian C]
    {A E₂ E₃ F F' : C} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F') (hs : s ≫ ι' = ιF) (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0) (hS : (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact)
    (t : A ⟶ pullback b ι') (τ : A ⟶ F) (ht1 : t ≫ pullback.fst b ι' = f)
    (ht2 : t ≫ pullback.snd b ι' = τ ≫ s) :
    ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  have hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0 := by
    rw [← Category.assoc, ht2, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨hz', ?_⟩
  have hmf : Mono f := hS.mono_f
  have hmt : Mono t := by
    subst ht1
    exact mono_of_mono t (pullback.fst b ι')
  have hsnd : Epi (pullback.snd b ι') := Abelian.epi_pullback_of_epi_f b ι'
  refine ShortComplex.ShortExact.mk' ?_ hmt (epi_comp _ _)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  simp only at x hx
  have hc := (ShortComplex.exact_cokernel s)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hc
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := hc (x ≫ pullback.snd b ι') (by simpa using hx)
  simp only at hy
  have hex := hS.exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hex
  have hb : (π₁ ≫ x ≫ pullback.fst b ι') ≫ b ≫ cokernel.π ιF = 0 := by
    have : π₁ ≫ x ≫ pullback.fst b ι' ≫ b = y ≫ ιF := by
      rw [pullback.condition, ← Category.assoc, ← Category.assoc, ← hs,
        Category.assoc π₁, hy, Category.assoc]
    have h2 := this =≫ cokernel.π ιF
    simp only [Category.assoc] at h2 ⊢
    rw [h2, cokernel.condition, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz2⟩ := hex (π₁ ≫ x ≫ pullback.fst b ι') hb
  simp only at hz2
  refine ⟨T₂, π₂ ≫ π₁, epi_comp _ _, z, ?_⟩
  simp only
  apply (cancel_mono (pullback.fst b ι')).1
  simp only [Category.assoc, ht1]
  simpa [Category.assoc] using hz2

end GlobalTheory

open GlobalTheory in
theorem GlobalTheory.shortExact_pullback_cokernel_modules : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  intro X A E₂ E₃ F F' b _ ιF ι' _ s hs f hz hS t τ ht1 ht2
  exact shortExact_pullback_cokernel_of_shortExact b ιF ι' s hs f hz hS t τ ht1 ht2
end

open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_pullback_compatible_sub : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  atlas_forward_decl GlobalTheory.shortExact_pullback_cokernel_modules
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Flag.Concat

variable {X : Scheme.{0}} {E₁ E₂ E₃ : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (hab : a ≫ b = 0)
  {r₁ r₃ : ℕ} (fl₁ : Flag E₁ r₁) (fl₃ : Flag E₃ r₃)

def obj (k : Fin (r₁ + r₃ + 1)) : X.Modules :=
  if h : (k : ℕ) ≤ r₁ then fl₁.F ⟨k, by omega⟩ else pullback b (fl₃.ι ⟨k - r₁, by have := k.2; omega⟩)

theorem obj_of_le {k : Fin (r₁ + r₃ + 1)} {i : Fin (r₁ + 1)} (h : (k : ℕ) = i) :
    obj b fl₁ fl₃ k = fl₁.F i := by
  obtain ⟨i, hi⟩ := i
  simp only at h
  subst h
  exact dif_pos (by omega)

theorem obj_of_gt {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j)
    (hj : 0 < (j : ℕ)) : obj b fl₁ fl₃ k = pullback b (fl₃.ι j) := by
  obtain ⟨j, hj'⟩ := j
  simp only at h hj
  obtain rfl : j = k - r₁ := by omega
  exact dif_neg (by omega)

def incl (k : Fin (r₁ + r₃ + 1)) : obj b fl₁ fl₃ k ⟶ E₂ :=
  if h : (k : ℕ) ≤ r₁ then
    eqToHom (obj_of_le b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl) ≫ fl₁.ι ⟨k, by omega⟩ ≫ a
  else
    eqToHom (obj_of_gt b fl₁ fl₃ (j := ⟨k - r₁, by have := k.2; omega⟩) (by simp only; omega)
      (by simp only; omega)) ≫ pullback.fst b (fl₃.ι _)

theorem incl_of_le {k : Fin (r₁ + r₃ + 1)} {i : Fin (r₁ + 1)} (h : (k : ℕ) = i) :
    incl a b fl₁ fl₃ k = eqToHom (obj_of_le b fl₁ fl₃ h) ≫ fl₁.ι i ≫ a := by
  obtain ⟨i, hi⟩ := i
  simp only at h
  subst h
  exact dif_pos (by omega)

theorem incl_of_gt {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j)
    (hj : 0 < (j : ℕ)) :
    incl a b fl₁ fl₃ k = eqToHom (obj_of_gt b fl₁ fl₃ h hj) ≫ pullback.fst b (fl₃.ι j) := by
  obtain ⟨j, hj'⟩ := j
  simp only at h hj
  obtain rfl : j = k - r₁ := by omega
  exact dif_neg (by omega)

def proj (k : Fin (r₁ + r₃ + 1)) : obj b fl₁ fl₃ k ⟶ fl₃.F ⟨k - r₁, by have := k.2; omega⟩ :=
  if h : (k : ℕ) ≤ r₁ then 0 else
    eqToHom (obj_of_gt b fl₁ fl₃ (j := ⟨k - r₁, by have := k.2; omega⟩) (by simp only; omega)
      (by simp only; omega)) ≫ pullback.snd b (fl₃.ι _)

include hab in

theorem incl_comp (k : Fin (r₁ + r₃ + 1)) :
    incl a b fl₁ fl₃ k ≫ b = proj b fl₁ fl₃ k ≫ fl₃.ι ⟨k - r₁, by have := k.2; omega⟩ := by
  unfold incl proj
  split_ifs with h
  · simp [hab]
  · simp [pullback.condition]

def step (i : Fin (r₁ + r₃)) : obj b fl₁ fl₃ i.castSucc ⟶ obj b fl₁ fl₃ i.succ :=
  if h : (i : ℕ) + 1 ≤ r₁ then
    eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl) ≫
      fl₁.step ⟨i, by omega⟩ ≫
      eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl).symm
  else
    pullback.lift (incl a b fl₁ fl₃ i.castSucc)
        (proj b fl₁ fl₃ i.castSucc ≫ fl₃.step ⟨i - r₁, by omega⟩)
        (by rw [incl_comp a b hab, Category.assoc, Flag.step_ι]; rfl) ≫
      eqToHom (obj_of_gt b fl₁ fl₃ (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
        (by simp only [Fin.val_succ]; omega) (by simp)).symm

theorem step_of_le (i : Fin (r₁ + r₃)) (h : (i : ℕ) + 1 ≤ r₁) :
    step a b hab fl₁ fl₃ i =
      eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl) ≫
        fl₁.step ⟨i, by omega⟩ ≫
        eqToHom (obj_of_le b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl).symm :=
  dif_pos h

theorem step_of_ge (i : Fin (r₁ + r₃)) (h : r₁ ≤ (i : ℕ)) :
    step a b hab fl₁ fl₃ i =
      pullback.lift (incl a b fl₁ fl₃ i.castSucc)
        (proj b fl₁ fl₃ i.castSucc ≫ fl₃.step ⟨i - r₁, by omega⟩)
        (by rw [incl_comp a b hab, Category.assoc, Flag.step_ι]; rfl) ≫
      eqToHom (obj_of_gt b fl₁ fl₃ (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
        (by simp only [Fin.val_succ]; omega) (by simp)).symm :=
  dif_neg (by omega)

theorem step_ι (i : Fin (r₁ + r₃)) :
    step a b hab fl₁ fl₃ i ≫ incl a b fl₁ fl₃ i.succ = incl a b fl₁ fl₃ i.castSucc := by
  unfold step
  split_ifs with h
  · rw [incl_of_le a b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).succ) rfl,
      incl_of_le a b fl₁ fl₃ (i := (⟨i, by omega⟩ : Fin r₁).castSucc) rfl]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Flag.step_ι_assoc]
  · rw [incl_of_gt a b fl₁ fl₃ (k := i.succ) (j := (⟨i - r₁, by omega⟩ : Fin r₃).succ)
      (by simp only [Fin.val_succ]; omega) (by simp)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact pullback.lift_fst _ _ _

end GlobalTheory.Vert.Flag.Concat

namespace GlobalTheory.Vert.Flag.Concat

open GlobalTheory.VB

theorem short_exact_zero_concat : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := GlobalTheory.T.short_exact_cokernel_compose

theorem short_exact_pullback_fst_concat : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := GlobalTheory.T.shortExact_of_pullback_cokernel

theorem short_exact_lift_concat : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := GlobalTheory.T.shortExact_pullback_compatible_sub

theorem isVB_cokernel_comp {X : Scheme.{0}} {E₁ E₂ E₃ G : X.Modules} {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃}
    {h : a ≫ b = 0} (hS : (ShortComplex.mk a b h).ShortExact) (g : G ⟶ E₁) {m n : ℕ}
    (hg : IsVB (cokernel g) m) (h₃ : IsVB E₃ n) : IsVB (cokernel (g ≫ a)) (m + n) := by
  have := hS.mono_f
  exact VBExt.isVB_X₂_of_shortExact X _ m n (shortExact_cokernel_comp g a) hg
    (h₃.of_iso (hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)))

theorem isSubbundle_iso_comp {X : Scheme.{0}} {A B E : X.Modules} (e : A ⟶ B) [IsIso e] {f : B ⟶ E}
    (hf : IsSubbundle f) : IsSubbundle (e ≫ f) := by
  obtain ⟨_, s, hs⟩ := hf
  exact ⟨inferInstance, s, hs.of_iso (cokernelEpiComp e f).symm⟩

variable {X : Scheme.{0}} {E₁ E₂ E₃ : X.Modules} {a : E₁ ⟶ E₂} {b : E₂ ⟶ E₃} {hab : a ≫ b = 0}
  (hS : (ShortComplex.mk a b hab).ShortExact) {r₁ r₃ : ℕ} (fl₁ : Flag E₁ r₁) (fl₃ : Flag E₃ r₃)

include hS in

theorem shortExact_incl {k : Fin (r₁ + r₃ + 1)} {j : Fin (r₃ + 1)} (h : (k : ℕ) = r₁ + j) :
    ∃ hz : incl a b fl₁ fl₃ k ≫ b ≫ cokernel.π (fl₃.ι j) = 0,
      (ShortComplex.mk (incl a b fl₁ fl₃ k) (b ≫ cokernel.π (fl₃.ι j)) hz).ShortExact := by
  have := hS.epi_g
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · have hk : (k : ℕ) = (Fin.last r₁ : ℕ) := by simp; omega
    have hz : IsZero (fl₃.F j) := by
      have h0 := fl₃.isVB j
      rw [hj] at h0
      exact VB.isVB_zero_iff.1 h0
    exact short_exact_zero_concat X a b hab hS _ (eqToHom (obj_of_le b fl₁ fl₃ hk) ≫ fl₁.ι (Fin.last r₁))
      (by rw [incl_of_le a b fl₁ fl₃ hk, Category.assoc]) _ hz
  · exact short_exact_pullback_fst_concat X b (fl₃.ι j) _ (eqToHom (obj_of_gt b fl₁ fl₃ h hj)) (incl_of_gt a b fl₁ fl₃ h hj)

include hS fl₁ fl₃ in

theorem isVB_E₂ : IsVB E₂ (r₁ + r₃) :=
  VBExt.isVB_X₂_of_shortExact X _ r₁ r₃ hS fl₁.isVB_self fl₃.isVB_self

include hS in
theorem isVB_obj (k : Fin (r₁ + r₃ + 1)) : IsVB (obj b fl₁ fl₃ k) k := by
  by_cases hk : (k : ℕ) ≤ r₁
  · exact (fl₁.isVB ⟨k, by omega⟩).of_iso (eqToIso (obj_of_le b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl)).symm
  · have hkj : (k : ℕ) = r₁ + ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ) := by simp; omega
    obtain ⟨_, hS'⟩ := shortExact_incl hS fl₁ fl₃ hkj
    have h₂ := isVB_E₂ hS fl₁ fl₃
    rw [show r₁ + r₃ = k + (r₃ - ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ)) by simp; omega] at h₂
    exact VB.isVB_X₁_of_shortExact X _ _ _ hS' h₂ (fl₃.isVB_cokernel _)

include hS in
theorem isSubbundle_incl (k : Fin (r₁ + r₃ + 1)) : IsSubbundle (incl a b fl₁ fl₃ k) := by
  by_cases hk : (k : ℕ) < r₁
  · have := hS.mono_f
    rw [incl_of_le a b fl₁ fl₃ (i := ⟨k, by omega⟩) rfl]
    refine isSubbundle_iso_comp _ ⟨inferInstance, _, isVB_cokernel_comp hS _ (fl₁.isVB_cokernel _)
      fl₃.isVB_self⟩
  · have hkj : (k : ℕ) = r₁ + ((⟨k - r₁, by have := k.2; omega⟩ : Fin (r₃ + 1)) : ℕ) := by simp; omega
    obtain ⟨_, hS'⟩ := shortExact_incl hS fl₁ fl₃ hkj
    exact isSubbundle_of_shortExact hS' (fl₃.isVB_cokernel _)

include hS in
theorem isIso_incl_last : IsIso (incl a b fl₁ fl₃ (Fin.last (r₁ + r₃))) := by
  rcases Nat.eq_zero_or_pos r₃ with h3 | h3
  · have hk : ((Fin.last (r₁ + r₃) : Fin _) : ℕ) = (Fin.last r₁ : ℕ) := by simp [h3]
    rw [incl_of_le a b fl₁ fl₃ hk]
    have h0 := fl₃.isVB_self
    rw [h3] at h0
    have : IsIso a := hS.isIso_f_iff.2 (VB.isVB_zero_iff.1 h0)
    infer_instance
  · rw [incl_of_gt a b fl₁ fl₃ (j := Fin.last r₃) (by simp) (by simpa using h3)]
    infer_instance

def concat : Flag E₂ (r₁ + r₃) where
  F := obj b fl₁ fl₃
  ι := incl a b fl₁ fl₃
  isSubbundle := isSubbundle_incl hS fl₁ fl₃
  isVB := isVB_obj hS fl₁ fl₃
  step := step a b hab fl₁ fl₃
  step_ι := step_ι a b hab fl₁ fl₃
  isIso_last := isIso_incl_last hS fl₁ fl₃

end GlobalTheory.Vert.Flag.Concat

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

theorem GlobalTheory.Vert.Flag.concat_spec : ∀ (X : Scheme.{0}) (E₁ E₂ E₃ : X.Modules) (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃)
    (h : a ≫ b = 0), (ShortComplex.mk a b h).ShortExact → ∀ (r₁ r₃ : ℕ)
    (fl₁ : GlobalTheory.Vert.Flag E₁ r₁) (fl₃ : GlobalTheory.Vert.Flag E₃ r₃), ∃ fl₂ : GlobalTheory.Vert.Flag E₂ (r₁ + r₃),
    (∀ (k : Fin (r₁ + r₃ + 1)) (i : Fin (r₁ + 1)), (k : ℕ) = i →
      ∃ e : fl₂.F k ≅ fl₁.F i, fl₂.ι k = e.hom ≫ fl₁.ι i ≫ a) ∧
    (∀ (k : Fin (r₁ + r₃ + 1)) (j : Fin (r₃ + 1)), (k : ℕ) = r₁ + j →
      ∃ hz : fl₂.ι k ≫ b ≫ cokernel.π (fl₃.ι j) = 0,
        (ShortComplex.mk (fl₂.ι k) (b ≫ cokernel.π (fl₃.ι j)) hz).ShortExact) ∧
    (∀ (k : Fin (r₁ + r₃)) (i : Fin r₁), (k : ℕ) = i →
      ∃ (e : fl₂.F k.succ ≅ fl₁.F i.succ) (u : fl₂.gr k ≅ fl₁.gr i),
        fl₂.ι k.succ = e.hom ≫ fl₁.ι i.succ ≫ a ∧ fl₂.π k ≫ u.hom = e.hom ≫ fl₁.π i) ∧
    (∀ (k : Fin (r₁ + r₃)) (j : Fin r₃), (k : ℕ) = r₁ + j →
      ∃ (m : fl₂.F k.succ ⟶ fl₃.F j.succ) (u : fl₂.gr k ≅ fl₃.gr j),
        m ≫ fl₃.ι j.succ = fl₂.ι k.succ ≫ b ∧ fl₂.π k ≫ u.hom = m ≫ fl₃.π j) := by
  intro X E₁ E₂ E₃ a b h hS r₁ r₃ fl₁ fl₃
  open GlobalTheory.Vert.Flag.Concat in
  refine ⟨concat hS fl₁ fl₃, fun k i hki => ⟨eqToIso (obj_of_le b fl₁ fl₃ hki), incl_of_le a b fl₁ fl₃ hki⟩,
    fun k j hkj => shortExact_incl hS fl₁ fl₃ hkj, fun k i hki => ?_, fun k j hkj => ?_⟩
  · obtain ⟨i, hi⟩ := i
    simp only at hki
    subst hki
    dsimp only [concat, Flag.gr, Flag.π]
    have hs := Concat.step_of_le a b h fl₁ fl₃ k (by omega)
    refine ⟨eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp)),
      cokernel.mapIso _ _ (eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.castSucc)
        (i := (⟨k, hi⟩ : Fin r₁).castSucc) rfl))
        (eqToIso (Concat.obj_of_le b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp))) ?_,
      Concat.incl_of_le a b fl₁ fl₃ (k := k.succ) (i := (⟨k, hi⟩ : Fin r₁).succ) (by simp), ?_⟩
    · rw [hs]
      simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    · exact cokernel.π_desc _ _ _
  · obtain ⟨j, hj⟩ := j
    simp only at hkj
    obtain rfl : j = k - r₁ := by omega
    dsimp only [concat, Flag.gr, Flag.π]
    have hs := Concat.step_of_ge a b h fl₁ fl₃ k (by omega)
    have := hS.epi_g
    obtain ⟨hz, hS₁⟩ := Concat.shortExact_incl hS fl₁ fl₃ (k := k.castSucc)
      (j := (⟨k - r₁, hj⟩ : Fin r₃).castSucc) (by simp; omega)
    obtain ⟨hz', hS₂⟩ := Concat.short_exact_lift_concat X b (fl₃.ι (⟨k - r₁, hj⟩ : Fin r₃).castSucc)
      (fl₃.ι (⟨k - r₁, hj⟩ : Fin r₃).succ) (fl₃.step ⟨k - r₁, hj⟩) (fl₃.step_ι _) _ hz hS₁
      (pullback.lift (Concat.incl a b fl₁ fl₃ k.castSucc)
        (Concat.proj b fl₁ fl₃ k.castSucc ≫ fl₃.step ⟨k - r₁, hj⟩)
        (by rw [Concat.incl_comp a b h, Category.assoc, Flag.step_ι]; rfl))
      (Concat.proj b fl₁ fl₃ k.castSucc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    have E := Concat.obj_of_gt b fl₁ fl₃ (k := k.succ) (j := (⟨k - r₁, hj⟩ : Fin r₃).succ)
      (by simp; omega) (by simp)
    refine ⟨eqToHom E ≫ pullback.snd b _, cokernelIsoOfEq hs ≪≫ cokernelCompIsIso _ _ ≪≫
      (cokernelIsCokernel _).coconePointUniqueUpToIso hS₂.gIsCokernel, ?_, ?_⟩
    · rw [Concat.incl_of_gt a b fl₁ fl₃ (k := k.succ) (j := (⟨k - r₁, hj⟩ : Fin r₃).succ)
        (by simp; omega) (by simp)]
      simp [pullback.condition]
    · simp
      erw [(cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hS₂.gIsCokernel WalkingParallelPair.one]
      simp
end
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CovTest

namespace GlobalTheory.FlagTwoSteps

theorem nonempty_flag_pullback {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] {r : ℕ}
    {W U : X.Opens} {e : Fin r → Γ(F, W)} (he : IsFrame e) (hU : U ≤ W) :
    Nonempty (Vert.Flag ((Scheme.Modules.pullback U.ι).obj F) r) := by
  have h1 := (he.res hU).pullback U.ι
  have h2 : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun y _ => by simp
  exact Vert.Flag.nonempty_of_isFrame_top r _ _ (h1.res h2)

theorem shortExact_pullback {X : Scheme.{0}} (U : X.Opens) {A B : X.Modules} {s : A ⟶ B}
    {r : ℕ} (hA : IsVB A r) (hs : IsSubbundle s) :
    ∃ h : (Scheme.Modules.pullback U.ι).map s ≫ cokernel.π ((Scheme.Modules.pullback U.ι).map s) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have := (GlobalTheory.SubPull.isSubbundle_pullback X U.toScheme U.ι A B s r hA hs).mono
  exact ⟨cokernel.condition _, { exact := ShortComplex.exact_cokernel _ }⟩

theorem exists_flag_two_steps : ∀ (X : Scheme.{0}) (E S P : X.Modules) (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ n) (s : S ⟶ P) (j : P ⟶ E), IsVB E n → IsVB S m₁ → IsVB P m₂ → IsSubbundle s →
    IsSubbundle j → ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (fl : GlobalTheory.Vert.Flag ((Scheme.Modules.pullback U.ι).obj E) n)
      (eS : (Scheme.Modules.pullback U.ι).obj S ≅ fl.F ⟨m₁, by omega⟩)
      (eP : (Scheme.Modules.pullback U.ι).obj P ≅ fl.F ⟨m₂, by omega⟩),
      eS.hom ≫ fl.ι ⟨m₁, by omega⟩ = (Scheme.Modules.pullback U.ι).map (s ≫ j) ∧
        eP.hom ≫ fl.ι ⟨m₂, by omega⟩ = (Scheme.Modules.pullback U.ι).map j := by
  intro X E S P n m₁ m₂ h₁₂ h₂ s j hE hS hP hs hj x
  have : Nonempty X := ⟨x⟩
  have := hs.mono
  have := hj.mono
  obtain ⟨a, ha⟩ := hs.isVB_cokernel
  obtain ⟨b, hb⟩ := hj.isVB_cokernel
  have hSE₁ : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_cokernel s }
  have hSE₂ : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  obtain rfl : m₂ = m₁ + a := hP.rank_unique (VBExt.isVB_X₂_of_shortExact X _ m₁ a hSE₁ hS ha)
  obtain rfl : n = m₁ + a + b := hE.rank_unique (VBExt.isVB_X₂_of_shortExact X _ _ b hSE₂ hP hb)
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hS x
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := ha x
  obtain ⟨U₃, e₃, hx₃, he₃⟩ := hb x
  let U : X.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hx₃⟩
  have := hS.isQuasicoherent
  have := ha.isQuasicoherent
  have := hb.isQuasicoherent
  obtain ⟨flS⟩ := nonempty_flag_pullback (U := U) he₁ (inf_le_left.trans inf_le_left)
  obtain ⟨flA⟩ := nonempty_flag_pullback (U := U) he₂ (inf_le_left.trans inf_le_right)
  obtain ⟨flB⟩ := nonempty_flag_pullback (U := U) he₃ inf_le_right
  set Φ := Scheme.Modules.pullback U.ι
  obtain ⟨z₁, hz₁⟩ := shortExact_pullback U hS hs
  obtain ⟨z₂, hz₂⟩ := shortExact_pullback U hP hj
  obtain ⟨flP, hP₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₁ hz₁ m₁ a flS
    (flA.ofIso (PreservesCokernel.iso Φ s))
  obtain ⟨flE, hE₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₂ hz₂ (m₁ + a) b flP
    (flB.ofIso (PreservesCokernel.iso Φ j))
  obtain ⟨c₁, hc₁⟩ := hP₁ ⟨m₁, by omega⟩ (Fin.last m₁) rfl
  obtain ⟨c₂, hc₂⟩ := hE₁ ⟨m₁, by omega⟩ ⟨m₁, by omega⟩ rfl
  obtain ⟨c₃, hc₃⟩ := hE₁ ⟨m₁ + a, by omega⟩ (Fin.last (m₁ + a)) rfl
  refine ⟨U, hxU, flE, (asIso (flS.ι (Fin.last m₁))).symm ≪≫ c₁.symm ≪≫ c₂.symm,
    (asIso (flP.ι (Fin.last (m₁ + a)))).symm ≪≫ c₃.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₂, Iso.inv_hom_id_assoc,
      hc₁, IsIso.inv_hom_id_assoc, Functor.map_comp]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₃, Iso.inv_hom_id_assoc,
      IsIso.inv_hom_id_assoc]

end GlobalTheory.FlagTwoSteps
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.LineQuot
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.PluckerMap

attribute [local instance] Abelian.hasFiniteBiproducts

theorem sum_prod_mul_det {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] {d : ℕ}
    (b : Module.Basis (Fin d) R N) (v : ι → N) (c : Fin d → ι → R) (h : ∀ a, b a = ∑ m, c a m • v m) :
    ∑ I : Fin d → ι, (∏ a, c a (I a)) * b.det (fun a => v (I a)) = 1 := by
  classical
  rw [← b.det_self, show (⇑b : Fin d → N) = fun a => ∑ m, c a m • v m from funext h]
  refine Eq.trans ?_ (b.det.toMultilinearMap.map_sum fun a m => c a m • v m).symm
  exact Finset.sum_congr rfl fun I _ => (b.det.toMultilinearMap.map_smul_univ _ _).symm

theorem det_update_eq_repr {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {d : ℕ}
    (b : Module.Basis (Fin d) R N) (a : Fin d) (w : N) : b.det (Function.update b a w) = b.repr w a := by
  conv_lhs => rw [← b.sum_repr w]
  rw [AlternatingMap.map_update_sum, Finset.sum_eq_single a]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self, b.det_self, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [AlternatingMap.map_update_smul, b.det.map_update_self _ hj.symm, smul_zero]
  · simp

variable {T : Scheme.{0}} {L Q F : T.Modules} {d : ℕ}

theorem eq_repr_smul {U V : T.Opens} {e : Fin 1 → Γ(L, U)} (he : IsFrame e) (h : V ≤ U) (s : Γ(L, V)) :
    s = (he.basis h).repr s 0 • resM L h (e 0) := by
  conv_lhs => rw [← (he.basis h).sum_repr s]
  rw [Fin.sum_univ_one, IsFrame.basis_apply]

theorem isFrame_basicOpen {U V : T.Opens} {e : Fin d → Γ(F, U)} (he : IsFrame e) (h : V ≤ U)
    (s : Fin d → Γ(F, V)) :
    IsFrame fun a => resM F (T.basicOpen_le ((he.basis h).det s)) (s a) :=
  isFrame_iff.2 fun W hW => by
    have hu := ExMap.isUnit_resG_basicOpen _ hW
    rw [he.resG_det, ← Module.Basis.is_basis_iff_det] at hu
    simp only [resM_resM]
    exact ⟨hu.1, hu.2.ge⟩

theorem exists_frame {M : ℕ} {u : Fin (M + 1) → (L ⟶ Q)} (hL : IsVB L 1) (hQ : IsVB Q d) (hu : JointEpi u) (x : T) :
    ∃ (I : Fin d → Fin (M + 1)) (W : T.Opens) (t : Γ(L, W)), x ∈ W ∧ (IsFrame fun _ : Fin 1 => t) ∧
      IsFrame fun a => (u (I a)).app W t := by
  have hp : Epi (biproduct.desc u) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hu Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (M + 1) => L) j ≫ ·) ha
  obtain ⟨U₁, e', hx₁, he'⟩ := hL x
  obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
  choose O hO hxO t ht using fun a => exists_app_eq_of_epi (biproduct.desc u) (e a) hx₂
  let W : T.Opens := U₂ ⊓ Finset.univ.inf O
  have hxW : x ∈ W := ⟨hx₂, by rw [Opens.coe_finset_inf]; simpa using hxO⟩
  have hW (a : Fin d) : W ≤ O a := inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))
  have hW' : W ≤ U₁ := inf_le_left.trans h₂
  let B := he.basis (inf_le_left : W ≤ U₂)
  have h1 := sum_prod_mul_det B (fun m => (u m).app W (resM L hW' (e' 0)))
    (fun a m => (he'.basis hW').repr ((biproduct.π (fun _ : Fin (M + 1) => L) m).app W (resM _ (hW a) (t a))) 0)
    fun a => by
      rw [IsFrame.basis_apply, ← resM_resM (hO a) (hW a), ← ht, ← app_resM, desc_app]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Scheme.Modules.Hom.app_smul, ← eq_repr_smul he']
  obtain ⟨I, -, hI⟩ := IsLocalRing.exists_of_isUnit_sum (s := Finset.univ)
    (f := fun I : Fin d → Fin (M + 1) => T.presheaf.germ W x hxW (_ * B.det fun a => (u (I a)).app W (resM L hW' (e' 0))))
    (by rw [← map_sum, h1, map_one]; exact isUnit_one)
  rw [map_mul] at hI
  have hf := isFrame_basicOpen he (inf_le_left : W ≤ U₂) fun a => (u (I a)).app W (resM L hW' (e' 0))
  refine ⟨I, _, resM L ((T.basicOpen_le _).trans hW') (e' 0),
    (T.mem_basicOpen _ x hxW).2 (isUnit_of_mul_isUnit_right hI), ?_, ?_⟩
  · have := he'.res ((T.basicOpen_le (B.det fun a => (u (I a)).app W (resM L hW' (e' 0)))).trans hW')
    rwa [show (fun i => resM L _ (e' i)) = fun _ => resM L _ (e' 0) from funext fun i => by rw [Subsingleton.elim i 0]] at this
  · convert hf using 2
    rw [← app_resM, resM_resM]

def frameLocus (v : Fin d → Γ(F, ⊤)) : T.Opens :=
  ⨆ W : {W : T.Opens // IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)}, W.1

theorem le_frameLocus {v : Fin d → Γ(F, ⊤)} {W : T.Opens} (h : IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)) :
    W ≤ frameLocus v := le_iSup (fun W : {W : T.Opens // IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)} => W.1) ⟨W, h⟩

theorem isFrame_frameLocus (v : Fin d → Γ(F, ⊤)) : IsFrame fun a => resM F (le_top : frameLocus v ≤ ⊤) (v a) :=
  isFrame_of_forall_exists fun V h x hx => by
    obtain ⟨W, hW⟩ := Opens.mem_iSup.1 (h hx)
    refine ⟨V ⊓ W.1, inf_le_left, ⟨hx, hW⟩, ?_⟩
    simpa only [resM_resM] using W.2 _ inf_le_right

theorem isCoordFamily {N : ℕ} (v : Fin (N + 1) → Fin d → Γ(F, ⊤))
    (hv : ∀ x : T, ∃ (i : Fin (N + 1)) (W : T.Opens), x ∈ W ∧ IsFrame fun a => resM F (le_top : W ≤ ⊤) (v i a)) :
    ProjSpace.IsCoordFamily (fun i => frameLocus (v i))
      fun i j => ((isFrame_frameLocus (v i)).basis le_rfl).det fun a => resM F le_top (v j a) where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, W, hx, hW⟩ := hv x
    exact Opens.mem_iSup.2 ⟨i, le_frameLocus hW hx⟩
  self i := by
    have := ((isFrame_frameLocus (v i)).basis le_rfl).det_self
    rwa [IsFrame.coe_basis, funext fun a => resM_resM _ _ (v i a)] at this
  mul i j k := by
    simp only [IsFrame.resG_det, resM_resM]
    rw [(isFrame_frameLocus (v i)).det_eq_detUnit_mul (isFrame_frameLocus (v j)) inf_le_left inf_le_right
      (fun a => resM F le_top (v k a)), IsFrame.val_detUnit]
    simp only [resM_resM]
  basicOpen_le i j := le_frameLocus (by
    simpa only [resM_resM] using isFrame_basicOpen (isFrame_frameLocus (v i)) le_rfl fun a => resM F le_top (v j a))

section Rel

variable {k : Type} [CommRing k] {N M : ℕ}

def PRel (φ : T ⟶ PSpace k N) (σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))) (u : Fin (M + 1) → (L ⟶ Q)) : Prop :=
  ∀ (i : Fin (N + 1)) (x : T), x ∈ φ ⁻¹ᵁ ProjSpace.chart k N i →
    ∃ (W : T.Opens) (h : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i) (t : Γ(L, W)), x ∈ W ∧ (IsFrame fun _ : Fin 1 => t) ∧
      (IsFrame fun a => (u (σ i a)).app W t) ∧ ∀ m, (u m).app W t =
        ∑ a, ProjSpace.pullRatio φ W i h (σ.symm (Function.update (σ i) a m)) • (u (σ i a)).app W t

theorem exists_prel (f : T ⟶ Sp k) (σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))) {u : Fin (M + 1) → (L ⟶ Q)}
    (hL : IsVB L 1) (hQ : IsVB Q d) (hu : JointEpi u) :
    ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ PRel φ σ u := by
  let v (m : Fin (M + 1)) : Γ(homMod L Q, ⊤) := (homGlobalEquiv L Q).symm (u m)
  let ε {W : T.Opens} {t : Γ(L, W)} (ht : IsFrame fun _ : Fin 1 => t) (V : T.Opens) (h : V ≤ W) :
      Γ(homMod L Q, V) ≃ₗ[Γ(T, V)] Γ(Q, V) := PtNorm.homPi ht h ≪≫ₗ LinearEquiv.funUnique (Fin 1) _ _
  have hε {W : T.Opens} {t : Γ(L, W)} (ht : IsFrame fun _ : Fin 1 => t) (V : T.Opens) (h : V ≤ W) (m : Fin (M + 1)) :
      ε ht V h (resM _ le_top (v m)) = resM Q h ((u m).app W t) := app_resM (u m) h t
  let H := isCoordFamily (fun i a => v (σ i a)) fun x => by
    obtain ⟨I, W, t, hx, ht, hf⟩ := exists_frame hL hQ hu x
    refine ⟨σ.symm I, W, hx, hf.map_of_linearEquiv (fun V h => (ε ht V h).symm) fun V h a => ?_⟩
    rw [LinearEquiv.symm_apply_eq, resM_resM, hε, Equiv.apply_symm_apply]
  refine ⟨H.toHom f, H.toHom_str f, fun i x hx => ?_⟩
  rw [H.toHom_preimage] at hx
  obtain ⟨W, e, -, hxW, hW, he⟩ := hL.exists_affine hx
  obtain ⟨t, rfl⟩ : ∃ t, e = fun _ => t := ⟨e 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hv := isFrame_frameLocus fun a => v (σ i a)
  refine ⟨W, hW.trans (H.le_toHom_preimage f i), t, hxW, he,
    (hv.res hW).map_of_linearEquiv (ε he) fun V h a => by rw [resM_resM, resM_resM, hε], fun m => ?_⟩
  have h1 := congrArg (ε he W le_rfl) ((hv.basis hW).sum_repr (resM _ le_top (v m)))
  rw [hε, resM_self, map_sum] at h1
  refine h1.symm.trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [map_smul, IsFrame.basis_apply, resM_resM, hε, resM_self,
    ← ProjSpace.resG_pullRatio (hi := H.le_toHom_preimage f i) hW, H.pullRatio_toHom f, IsFrame.resG_det,
    ← det_update_eq_repr]
  congr 2
  funext b
  simp only [resM_resM, Equiv.apply_symm_apply, IsFrame.coe_basis]
  exact (Function.apply_update (fun _ m => resM (homMod L Q) (le_top : W ≤ ⊤) (v m)) (σ i) a m b).symm

variable {φ : T ⟶ PSpace k N} {σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))} {u : Fin (M + 1) → (L ⟶ Q)}

theorem PRel.pullback [L.IsQuasicoherent] [Q.IsQuasicoherent] (h : PRel φ σ u) {S : Scheme.{0}} (g : S ⟶ T) :
    PRel (g ≫ φ) σ fun m => (Scheme.Modules.pullback g).map (u m) := by
  intro i y hy
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i (g y) hy
  refine ⟨g ⁻¹ᵁ W, g.preimage_mono hW, QCoh.pullbackSections g L le_rfl t, hx, ht.pullback g, ?_, fun m => ?_⟩
  · simpa only [QCoh.pullback_map_app_pullbackSections] using hf.pullback g
  · simp only [QCoh.pullback_map_app_pullbackSections]
    rw [hr m, map_sum]
    simp only [QCoh.pullbackSections_smul]
    exact Finset.sum_congr rfl fun a _ => by rw [← ProjSpace.appLE_pullRatio]

theorem PRel.pre (h : PRel φ σ u) {L' : T.Modules} (α : L ≅ L') : PRel φ σ fun m => α.inv ≫ u m := by
  intro i x hx
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i x hx
  have e (m) : (α.inv ≫ u m).app W (α.hom.app W t) = (u m).app W t := by
    rw [QCoh.app_app, α.hom_inv_id_assoc]
  exact ⟨W, hW, α.hom.app W t, hx, ht.map_iso α.hom, by simpa only [e] using hf, by simpa only [e] using hr⟩

theorem PRel.exists_desc_app (h : PRel φ σ u) (i : Fin (N + 1)) (x : T) (hx : x ∈ φ ⁻¹ᵁ ProjSpace.chart k N i) :
    ∃ (W : T.Opens) (hW : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i), x ∈ W ∧ ∀ (V : T.Opens) (hV : V ≤ W),
      (∀ s : Fin d → Γ(L, V), ∑ a, (u (σ i a)).app V (s a) = 0 → ∀ a, s a = 0) ∧
      ∀ s : Fin (M + 1) → Γ(L, V), ∑ m, (u m).app V (s m) = ∑ a, (u (σ i a)).app V
        (∑ m, ProjSpace.pullRatio φ V i (hV.trans hW) (σ.symm (Function.update (σ i) a m)) • s m) := by
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i x hx
  refine ⟨W, hW, hx, fun V hV => ⟨fun s hs a => ?_, fun s => ?_⟩⟩
  · have := (hf V hV).1 (a₁ := fun a => (ht.basis hV).repr (s a) 0) (a₂ := 0) (by
      rw [map_zero, ← hs, Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← app_resM, ← Scheme.Modules.Hom.app_smul, ← eq_repr_smul ht])
    rw [eq_repr_smul ht hV (s a), congrFun this a, Pi.zero_apply, zero_smul]
  · simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eq_repr_smul ht hV (s m), Scheme.Modules.Hom.app_smul, app_resM, hr m, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_resM, resM_smul, ProjSpace.resG_pullRatio,
      smul_comm]

theorem PRel.exists_factor {Q' : T.Modules} {u' : Fin (M + 1) → (L ⟶ Q')} (h : PRel φ σ u) (h' : PRel φ σ u')
    (hu : JointEpi u) : ∃ e : Q ⟶ Q', ∀ m, u m ≫ e = u' m := by
  have hepi : Epi (biproduct.desc u) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hu Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (M + 1) => L) j ≫ ·) ha
  choose i hi using fun x : T => ProjSpace.exists_mem_chart k N (φ x)
  choose W hW hx H using fun x => h.exists_desc_app (i x) x (hi x)
  choose W' hW' hx' H' using fun x => h'.exists_desc_app (i x) x (hi x)
  have loc : ∀ (V : T.Opens) (t : Γ(⨁ fun _ : Fin (M + 1) => L, V)),
      (biproduct.desc u).app V t = 0 → (biproduct.desc u').app V t = 0 := by
    intro V t h0
    refine sec_ext_of_cover (fun x => V ⊓ W x ⊓ W' x) (fun _ => inf_le_left.trans inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨y, ⟨⟨hy, hx y⟩, hx' y⟩⟩) fun x => ?_
    have h1 := congrArg (resM Q (inf_le_left.trans inf_le_left : V ⊓ W x ⊓ W' x ≤ V)) h0
    rw [← app_resM, map_zero, desc_app, (H x _ (inf_le_left.trans inf_le_right)).2] at h1
    rw [← app_resM, map_zero, desc_app, (H' x _ inf_le_right).2]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [(H x _ (inf_le_left.trans inf_le_right)).1 _ h1 a, map_zero]
  have hk : kernel.ι (biproduct.desc u) ≫ biproduct.desc u' = 0 := by
    ext V x
    have h := congrArg (fun f => f.app V x) (kernel.condition (biproduct.desc u))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h ⊢
    exact loc V _ h
  refine ⟨Abelian.epiDesc _ _ hk, fun j => ?_⟩
  rw [← biproduct.ι_desc u j, Category.assoc, Abelian.comp_epiDesc, biproduct.ι_desc]

end Rel

theorem hom_ext_map_biproduct {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (Φ : C ⥤ D)
    [Φ.Additive] {ι : Type} [Fintype ι] (f : ι → C) [HasBiproduct f] {Z : D} {a b : Φ.obj (⨁ f) ⟶ Z}
    (h : ∀ j, Φ.map (biproduct.ι f j) ≫ a = Φ.map (biproduct.ι f j) ≫ b) : a = b := by
  have e (c : Φ.obj (⨁ f) ⟶ Z) : c = ∑ j, Φ.map (biproduct.π f j) ≫ Φ.map (biproduct.ι f j) ≫ c := by
    simp only [← Functor.map_comp_assoc, ← Preadditive.sum_comp, ← Functor.map_sum, biproduct.total, Φ.map_id,
      Category.id_comp]
  rw [e a, e b]
  simp only [h]

theorem exists_epi_biproduct {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {E : B.Modules} {r : ℕ} (hE : IsVB E r) :
    ∃ (M : ℕ) (L : B.Modules) (a : (⨁ fun _ : Fin (M + 1) => L) ⟶ E), IsVB L 1 ∧ Epi a := by
  have := hE.isFiniteQC
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hq
  obtain ⟨n, N, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize LB.toMod (lbZPow A (-n)) = L at φ hφ hL
  refine ⟨N, L, biproduct.desc (Fin.cons 0 fun j => Sigma.ι (fun _ => L) j ≫ φ), hL,
    (Preadditive.epi_iff_cancel_zero _).2 fun Z b hb => ?_⟩
  rw [← cancel_epi φ]
  refine Sigma.hom_ext _ _ fun j => ?_
  simpa using biproduct.ι _ j.succ ≫= hb

theorem exists_toPSpace_of_isSubbundle : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q → ∀ (E : B.Modules) (n m : ℕ), IsVB E n → m ≤ n → ∀ (G : Scheme.{0}) (γ : G ⟶ B) (P : G.Modules) (j : P ⟶ (Scheme.Modules.pullback γ).obj E), IsVB P m → IsSubbundle j → ∃ (N : ℕ) (φ : G ⟶ PSpace k N), φ ≫ PSpace.str k N = γ ≫ q ∧ ∀ (T : Scheme.{0}) (g₁ g₂ : T ⟶ G) (g : T ⟶ B) (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g), g₁ ≫ φ = g₂ ≫ φ → ∃ e : (Scheme.Modules.pullback g₁).obj P ≅ (Scheme.Modules.pullback g₂).obj P, e.hom ≫ (Scheme.Modules.pullback g₂).map j ≫ (Scheme.Modules.pullbackComp g₂ γ).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E = (Scheme.Modules.pullback g₁).map j ≫ (Scheme.Modules.pullbackComp g₁ γ).hom.app E ≫ (Scheme.Modules.pullbackCongr w₁).hom.app E := by
  intro k _ B q hq E n m hE _ G γ P j hP hj
  obtain ⟨M, L, a, hL, ha⟩ := exists_epi_biproduct hq hE
  obtain ⟨d, hQ⟩ := hj.isVB_cokernel
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := Fin d → Fin (M + 1)))
  let σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1)) := (Fintype.equivFinOfCardEq hN).symm
  let b (i : Fin (M + 1)) : L ⟶ E := biproduct.ι (fun _ : Fin (M + 1) => L) i ≫ a
  have hext {T : Scheme.{0}} (g : T ⟶ B) {Z : T.Modules} {x y : (Scheme.Modules.pullback g).obj E ⟶ Z}
      (h : ∀ i, (Scheme.Modules.pullback g).map (b i) ≫ x = (Scheme.Modules.pullback g).map (b i) ≫ y) : x = y := by
    rw [← cancel_epi ((Scheme.Modules.pullback g).map a)]
    exact hom_ext_map_biproduct _ _ fun i => by simpa [b] using h i
  let u (i : Fin (M + 1)) := (Scheme.Modules.pullback γ).map (b i) ≫ cokernel.π j
  obtain ⟨φ, hφ, hr⟩ := exists_prel (γ ≫ q) σ (u := u) (hL.pullback γ) hQ fun Z c hc => by
    rw [← cancel_epi (cokernel.π j)]
    exact hext γ fun i => by simpa [u] using hc i
  have := (hL.pullback γ).isQuasicoherent
  have := hQ.isQuasicoherent
  have := hj.mono
  have key (T : Scheme.{0}) (g₁ g₂ : T ⟶ G) (g : T ⟶ B) (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g) (h : g₁ ≫ φ = g₂ ≫ φ) :
      ∃ e : (Scheme.Modules.pullback g₁).obj P ⟶ (Scheme.Modules.pullback g₂).obj P,
        e ≫ (Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E =
          (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E := by
    have hu (g' : T ⟶ G) (w : g' ≫ γ = g) (i : Fin (M + 1)) :
        ((cmp g' γ w).app L).inv ≫ (Scheme.Modules.pullback g').map (u i) = (Scheme.Modules.pullback g).map (b i) ≫
          (cmp g' γ w).inv.app E ≫ (Scheme.Modules.pullback g').map (cokernel.π j) := by
      rw [Iso.inv_comp_eq, Iso.app_hom, ← cmp_naturality_assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
    have h₁ := (hr.pullback g₁).pre ((cmp g₁ γ w₁).app L)
    have h₂ := (hr.pullback g₂).pre ((cmp g₂ γ w₂).app L)
    rw [h] at h₁
    simp only [hu] at h₁ h₂
    obtain ⟨e, he⟩ := h₁.exists_factor h₂ fun Z c hc => by
      rw [← cancel_epi ((Scheme.Modules.pullback g₁).map (cokernel.π j)), ← cancel_epi ((cmp g₁ γ w₁).inv.app E)]
      exact hext g fun i => by simpa using hc i
    have he' : (cmp g₁ γ w₁).inv.app E ≫ (Scheme.Modules.pullback g₁).map (cokernel.π j) ≫ e =
        (cmp g₂ γ w₂).inv.app E ≫ (Scheme.Modules.pullback g₂).map (cokernel.π j) :=
      hext g fun i => by simpa using he i
    have hex := (ShortComplex.exact_cokernel j).map_of_epi_of_preservesCokernel (Scheme.Modules.pullback g₂)
      (inferInstanceAs (Epi (cokernel.π j))) inferInstance
    have : Mono ((ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).map (Scheme.Modules.pullback g₂)).f :=
      (SubPull.isSubbundle_pullback _ _ g₂ _ _ _ m hP hj).mono
    obtain ⟨c, hc⟩ : ∃ c, c ≫ (Scheme.Modules.pullback g₂).map j =
        (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E ≫ (cmp g₂ γ w₂).inv.app E := hex.lift' _ (by
      change _ ≫ (Scheme.Modules.pullback g₂).map (cokernel.π j) = 0
      rw [Category.assoc, Category.assoc, ← he', Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
        cokernel.condition]
      simp)
    exact ⟨c, by rw [reassoc_of% hc]; simp⟩
  refine ⟨N, φ, hφ, fun T g₁ g₂ g w₁ w₂ h => ?_⟩
  obtain ⟨e, he⟩ := key T g₁ g₂ g w₁ w₂ h
  obtain ⟨e', he'⟩ := key T g₂ g₁ g w₂ w₁ h.symm
  have := (SubPull.isSubbundle_pullback _ _ g₁ _ _ _ m hP hj).mono
  have := (SubPull.isSubbundle_pullback _ _ g₂ _ _ _ m hP hj).mono
  exact ⟨⟨e, e', by
      rw [← cancel_mono ((Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E), Category.assoc, he', he,
        Category.id_comp], by
      rw [← cancel_mono ((Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E), Category.assoc, he, he',
        Category.id_comp]⟩, he⟩

end GlobalTheory.PluckerMap

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB

namespace GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.LineQuot

section Sub

variable {X : Scheme.{0}} {A B E : X.Modules} {a b r : ℕ}

private theorem rank_cokernel {u : A ⟶ E} (hu : IsSubbundle u) (hA : IsVB A a) (hE : IsVB E r) :
    IsVB (cokernel u) (r - a) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hu
  obtain rfl : r = a + s := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } hA hs).1
  rw [Nat.add_sub_cancel_left]
  exact hs x

private theorem sub_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

private theorem sub_of_comp {u : A ⟶ B} {g : B ⟶ E} {f : A ⟶ E} (w : u ≫ g = f) (hf : IsSubbundle f)
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B b) (hE : IsVB E r) (h₁ : a ≤ b) (h₂ : b ≤ r) :
    IsSubbundle u := by
  subst w
  have := hg.mono
  have := hf.mono
  refine ⟨mono_of_mono u g, b - a, VB.isVB_X₁_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) ?_
    (rank_cokernel hg hB hE)⟩
  have h := rank_cokernel hf hA hE
  rwa [show r - a = b - a + (r - b) by omega] at h

private theorem sub_comp_iso {u : A ⟶ B} (hu : IsSubbundle u) (e : B ⟶ E) [IsIso e] : IsSubbundle (u ≫ e) :=
  have ⟨_, s, hs⟩ := hu
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso u e).symm⟩

private theorem exists_le (fl : Vert.Flag E r) (i : Fin (r + 1)) :
    ∀ l : Fin (r + 1), i ≤ l → ∃ t : fl.F i ⟶ fl.F l, t ≫ fl.ι l = fl.ι i := by
  intro l
  induction l using Fin.induction with
  | zero =>
    intro h
    obtain rfl : i = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ l ih =>
    intro h
    rcases h.eq_or_lt with rfl | h
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 h)
      exact ⟨t ≫ fl.step l, by rw [Category.assoc, fl.step_ι, ht]⟩

end Sub

variable {B G T Y : Scheme.{0}} {γ : G ⟶ B} {E : B.Modules} {n m₁ m₂ : ℕ} {S P : G.Modules} {s : S ⟶ P}
  {j : P ⟶ (Scheme.Modules.pullback γ).obj E}

private theorem pair_ext (hS : IsVB S m₁) (hP : IsVB P m₂) (hs : IsSubbundle s) (hj : IsSubbundle j)
    (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (g₁ g₂ : T ⟶ G) {g : T ⟶ B} (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g)
    (h₁ : ∃ e : (Scheme.Modules.pullback g₁).obj S ≅ (Scheme.Modules.pullback g₂).obj S,
      e.hom ≫ (Scheme.Modules.pullback g₂).map (s ≫ j) ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map (s ≫ j) ≫ (cmp g₁ γ w₁).hom.app E)
    (h₂ : ∃ e : (Scheme.Modules.pullback g₁).obj P ≅ (Scheme.Modules.pullback g₂).obj P,
      e.hom ≫ (Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E) : g₁ = g₂ := by
  obtain ⟨eS, heS⟩ := h₁
  obtain ⟨eP, heP⟩ := h₂
  have hj' := sub_comp_iso (SubPull.isSubbundle_pullback _ _ g₂ _ _ j m₂ hP hj) ((cmp g₂ γ w₂).hom.app E)
  have := hj'.mono
  refine (hG T g _ _ ((Scheme.Modules.pullback g₂).map s) _ (SubPull.isSubbundle_pullback _ _ g₂ _ _ s m₁ hS hs) hj'
    (hS.pullback g₂) (hP.pullback g₂)).unique ⟨w₁, eS, eP, heP, ?_⟩
    ⟨w₂, Iso.refl _, Iso.refl _, Category.id_comp _, by simp⟩
  rw [← cancel_mono ((Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E), Category.assoc, Category.assoc,
    heP]
  simpa only [Functor.map_comp, Category.assoc] using heS

private theorem exists_iso_comp {π : Y ⟶ B} (ρ : Y ⟶ G) (wρ : ρ ≫ γ = π) (σ : T ⟶ Y) (υ : T ⟶ G) {g : T ⟶ B}
    (wσ : σ ≫ π = g) (wυ : υ ≫ γ = g) (w : (σ ≫ ρ) ≫ γ = g) {A : G.Modules}
    (u : A ⟶ (Scheme.Modules.pullback γ).obj E) {F : Y.Modules} (ι : F ⟶ (Scheme.Modules.pullback π).obj E)
    {F' : T.Modules} (ι' : F' ⟶ (Scheme.Modules.pullback υ).obj ((Scheme.Modules.pullback γ).obj E))
    (a : (Scheme.Modules.pullback ρ).obj A ≅ F)
    (ha : a.hom ≫ ι = (Scheme.Modules.pullback ρ).map u ≫ (cmp ρ γ wρ).hom.app E)
    (b : (Scheme.Modules.pullback σ).obj F ≅ F')
    (hb : b.hom ≫ ι' ≫ (cmp υ γ wυ).hom.app E = (Scheme.Modules.pullback σ).map ι ≫ (cmp σ π wσ).hom.app E)
    (c : (Scheme.Modules.pullback υ).obj A ≅ F') (hc : c.hom ≫ ι' = (Scheme.Modules.pullback υ).map u) :
    ∃ e : (Scheme.Modules.pullback (σ ≫ ρ)).obj A ≅ (Scheme.Modules.pullback υ).obj A,
      e.hom ≫ (Scheme.Modules.pullback υ).map u ≫ (cmp υ γ wυ).hom.app E =
        (Scheme.Modules.pullback (σ ≫ ρ)).map u ≫ (cmp (σ ≫ ρ) γ w).hom.app E := by
  refine ⟨((cmp σ ρ rfl).app A).symm ≪≫ (Scheme.Modules.pullback σ).mapIso a ≪≫ b ≪≫ c.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← hc, Category.assoc, Iso.inv_hom_id_assoc, hb, ← Functor.map_comp_assoc, ha, Functor.map_comp_assoc,
    cmp_assoc σ ρ γ wρ wσ rfl w, Iso.inv_comp_eq, Iso.app_hom, cmp_naturality_assoc]

private theorem exists_sections (hE : IsVB E n) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (hS : IsVB S m₁) (hP : IsVB P m₂)
    (hs : IsSubbundle s) (hj : IsSubbundle j) (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (π : Y ⟶ B)
    (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hY : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) fl) :
    ∃ ρ : Y ⟶ G, ρ ≫ γ = π ∧ ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι := by
  let i₁ : Fin (n + 1) := ⟨m₁, by omega⟩
  let i₂ : Fin (n + 1) := ⟨m₂, by omega⟩
  obtain ⟨t, ht⟩ := exists_le (fl ()) i₁ i₂ h₁₂
  obtain ⟨ρ, ⟨wρ, aS, aP, haP, haS⟩, -⟩ := hG Y π _ _ t ((fl ()).ι i₂)
    (sub_of_comp ht ((fl ()).isSubbundle _) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
      (hE.pullback π) h₁₂ h₂) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
  rw [← cmp_hom_app] at haP
  have haS' : aS.hom ≫ (fl ()).ι i₁ = (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (cmp ρ γ wρ).hom.app E := by
    rw [← ht, reassoc_of% haS, haP, Functor.map_comp_assoc]
  refine ⟨ρ, wρ, fun x => ?_⟩
  obtain ⟨U, hx, flU, cS, cP, hcS, hcP⟩ :=
    FlagTwoSteps.exists_flag_two_steps G _ S P n m₁ m₂ h₁₂ h₂ s j (hE.pullback γ) hS hP hs hj x
  obtain ⟨σ, ⟨wσ, hσ⟩, -⟩ := hY U.toScheme (U.ι ≫ γ) fun _ => flU.ofIso ((cmp U.ι γ rfl).app E)
  obtain ⟨b₁, hb₁⟩ := hσ () i₁
  obtain ⟨b₂, hb₂⟩ := hσ () i₂
  have w : (σ ≫ ρ) ≫ γ = U.ι ≫ γ := by rw [Category.assoc, wρ, wσ]
  exact ⟨U, σ, hx, pair_ext hS hP hs hj hG _ _ w rfl
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₁) aS haS' b₁ hb₁ cS hcS)
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₂) aP haP b₂ hb₂ cP hcP)⟩

private theorem closed_of_sections {Z : Scheme.{0}} (ρ : Y ⟶ G) (f : G ⟶ Z) [IsProper (ρ ≫ f)]
    (h : ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι) :
    UniversallyClosed f ∧ LocallyOfFiniteType f := by
  choose U σ hx hσ using h
  have : Surjective ρ := ⟨fun x => ⟨σ x ⟨x, hx x⟩,
    (Scheme.Hom.comp_apply (σ x) ρ _).symm.trans (by rw [hσ]; rfl)⟩⟩
  refine ⟨UniversallyClosed.of_comp_surjective ρ f, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩)).2 fun x => ?_
  have : LocallyOfFiniteType (σ x ≫ ρ) := by rw [hσ]; infer_instance
  have := locallyOfFiniteType_of_comp (σ x) ρ
  rw [← hσ, Category.assoc]
  infer_instance

end GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.PairProj in
theorem _root_.GlobalTheory.T.pair_bundle_flag_compat : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q →
    ∀ (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
    ∀ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
      GlobalTheory.VB.IsVB S m₁ → GlobalTheory.VB.IsVB P m₂ → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j →
      GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j → IsProjOver (γ ≫ q) := by
  intro k _ _ B q hq E n m₁ m₂ hE h₁₂ h₂ G γ S P s j hS hP hs hj hG
  obtain ⟨Y, π, fl, hY, hYp⟩ := GlobalTheory.T.exists_flag_bundle_proj_vector_bundle k B q E n hq hE
  obtain ⟨ρ, wρ, hρ⟩ := exists_sections hE h₁₂ h₂ hS hP hs hj hG π fl hY
  have : IsProper (ρ ≫ γ ≫ q) := by
    rw [← Category.assoc, wρ]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver hYp).1
  obtain ⟨_, _⟩ := closed_of_sections ρ (γ ≫ q) hρ
  obtain ⟨N₁, φ₁, hφ₁, H₁⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₁ hE (h₁₂.trans h₂) G γ S (s ≫ j)
    hS (sub_comp hs hj)
  obtain ⟨N₂, φ₂, hφ₂, H₂⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₂ hE h₂ G γ P j hP hj
  have hPN (N : ℕ) : IsProjOver (PSpace.str k N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hZ := ProjSpace.isProjOver_pullback (ProjSpace.isProjOver_pullback hq (hPN N₁)) (hPN N₂)
  let ψ₁ : G ⟶ pullback q (PSpace.str k N₁) := pullback.lift γ φ₁ hφ₁.symm
  let ψ : G ⟶ pullback (pullback.fst q (PSpace.str k N₁) ≫ q) (PSpace.str k N₂) :=
    pullback.lift ψ₁ φ₂ (by rw [hφ₂, pullback.lift_fst_assoc])
  have hψ : ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q = γ ≫ q := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have : Mono ψ := ⟨fun {T} g₁ g₂ h => by
    have e₀ : g₁ ≫ ψ₁ = g₂ ≫ ψ₁ := by
      simpa only [ψ, Category.assoc, pullback.lift_fst] using h =≫ pullback.fst _ _
    have e₂ : g₁ ≫ φ₂ = g₂ ≫ φ₂ := by
      simpa only [ψ, Category.assoc, pullback.lift_snd] using h =≫ pullback.snd _ _
    have e₁ : g₁ ≫ φ₁ = g₂ ≫ φ₁ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_snd] using e₀ =≫ pullback.snd _ _
    have w : g₁ ≫ γ = g₂ ≫ γ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_fst] using e₀ =≫ pullback.fst _ _
    exact pair_ext hS hP hs hj hG g₁ g₂ w rfl (H₁ T g₁ g₂ _ w rfl e₁) (H₂ T g₁ g₂ _ w rfl e₂)⟩
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hZ).1
  have : IsSeparated (γ ≫ q) := by rw [← hψ]; infer_instance
  have : IsProper (ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q) := by rw [hψ]; exact {}
  have : IsClosedImmersion ψ := (IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨IsProper.of_comp ψ
    (pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q), inferInstance⟩
  rw [← hψ]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ψ hZ
end
