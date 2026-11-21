import Mathlib

section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Et.TrivTors

abbrev triv (n : ℕ) (V : Scheme.{0}) : Scheme.{0} := ∐ fun _ : ZMod n => V

abbrev proj (n : ℕ) (V : Scheme.{0}) : triv n V ⟶ V := Sigma.desc fun _ => 𝟙 V

def shift (n : ℕ) (V : Scheme.{0}) (k : ZMod n) : triv n V ⟶ triv n V :=
  Sigma.desc fun h => Sigma.ι (fun _ : ZMod n => V) (h + k)

def idx (n : ℕ) (V : Scheme.{0}) : C(↥(triv n V), ZMod n) :=
  ⟨fun x => ((sigmaMk (fun _ : ZMod n => V)).symm x).1,
    (continuous_sigma fun _ => continuous_const).comp (sigmaMk (fun _ : ZMod n => V)).symm.continuous⟩

variable {n : ℕ} {V : Scheme.{0}}

@[reassoc (attr := simp)]
theorem ι_shift (k h : ZMod n) :
    Sigma.ι (fun _ : ZMod n => V) h ≫ shift n V k = Sigma.ι (fun _ : ZMod n => V) (h + k) := by
  simp [shift]

@[reassoc (attr := simp)]
theorem shift_proj (k : ZMod n) : shift n V k ≫ proj n V = proj n V := by
  ext h
  simp [shift]

@[simp]
theorem idx_ι (h : ZMod n) (x : V) : idx n V ((Sigma.ι (fun _ : ZMod n => V) h).base x) = h := by
  have e := sigmaMk_mk (fun _ : ZMod n => V) h x
  change ((sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x)).1 = h
  have e' : (sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x) = ⟨h, x⟩ :=
    (sigmaMk (fun _ : ZMod n => V)).symm_apply_eq.mpr e.symm
  rw [e']

end GlobalTheory.Et.TrivTors

end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.Et.TrivTors

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_zero, Sigma.ι_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_desc_assoc, Fin.cases_succ, Sigma.ι_desc, Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨i, _, _⟩ := (sigmaOpenCover fun _ : Fin 0 => V).exists_eq x
      exact i.elim0
    infer_instance
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

theorem proj_finite_etale_surjective :
    ∀ (n : ℕ), n ≠ 0 → ∀ (V : Scheme.{0}), IsFinite (proj n V) ∧ Etale (proj n V) ∧ Surjective (proj n V) := by
  intro n hn V
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨isFinite_sigmaDesc_fin V (m + 1), ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
  · refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun v => ?_)
    exact Set.mem_iUnion.2 ⟨0, v, rfl⟩

end GlobalTheory.Et.TrivTors
end
end
