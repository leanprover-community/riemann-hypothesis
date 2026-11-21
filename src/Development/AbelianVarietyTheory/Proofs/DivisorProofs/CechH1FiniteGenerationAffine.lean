import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover

section
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue

set_option autoImplicit false

namespace GlobalTheory.AffGlue

theorem eq_zero_of_cover_zero : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  intro T D V hV ι W hW hWV hcov x hx
  let J : Ideal Γ(T, V) := LinearMap.ker (LinearMap.toSpanSingleton Γ(T, V) (D.M V hV) x)
  have hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • x = 0 := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  let s : Set Γ(T, V) := {f | ∃ n : ℕ, f ^ n • x = 0}
  have hs : V ≤ ⨆ f : s, T.basicOpen f.1 := by
    intro y hy
    have hy' : y ∈ ⨆ i, W i := hcov hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy'
    obtain ⟨i, hi⟩ := hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (V := W i) ⟨y, hi⟩ hy
    have hD : IsAffineOpen (T.basicOpen f) := hV.basicOpen f
    have h0 : D.ρ hV hD (T.basicOpen_le f) x = 0 := by
      have := D.ρ_ρ hV (hW i) hD (hWV i) hfle x
      rw [hx i, map_zero] at this
      exact this.symm
    obtain ⟨n, hn⟩ := D.loc_inj hV f hD x h0
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨f, n, hn⟩, hyf⟩
  have hspan : Ideal.span s = ⊤ := (hV.self_le_iSup_basicOpen_iff).mp hs
  have hrad : J.radical = ⊤ := by
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro f ⟨n, hn⟩
    exact ⟨n, (hJ _).mpr hn⟩
  have h1 : (1 : Γ(T, V)) ∈ J := by
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]; trivial
  simpa using (hJ 1).mp h1

end GlobalTheory.AffGlue
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_glue_separated : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  atlas_forward_decl GlobalTheory.AffGlue.eq_zero_of_cover_zero
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue

namespace GlobalTheory.AffGlue.Cech

variable {T : Scheme.{0}}

theorem span_small_eq_top {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hc : V ≤ ⨆ i, W i) :
    Ideal.span {f : Γ(T, V) | ∃ i, T.basicOpen f ≤ W i} = ⊤ := by
  rw [← hV.self_le_iSup_basicOpen_iff]
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
  obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le (V := W i) ⟨x, hi⟩ hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩

theorem eq_zero_of_small (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ (i : ι) (O : T.Opens) (hO : IsAffineOpen O) (h : O ≤ V), O ≤ W i →
      D.ρ hV hO h x = 0) : x = 0 := by
  have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule Γ(T, V) (D.M V hV)) _
    (span_small_eq_top hV W hc) x (by
      rintro ⟨f, i, hf⟩
      obtain ⟨n, hn⟩ := D.loc_inj hV f (hV.basicOpen f) x (hx i _ _ _ hf)
      exact ⟨n, by simpa using hn⟩)
  simpa using this

theorem exists_glue_finset (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i)
    (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) (s : Finset ι) :
    ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = m k := by
  let I : Ideal Γ(T, V) :=
    { carrier := {a | ∃ x : D.M V hV, ∀ k ∈ s, D.ρ hV (hW k) (hWV k) x = resG T (hWV k) a • m k}
      add_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, fun k hk => by rw [map_add, map_add, add_smul, hx k hk, hy k hk]⟩
      zero_mem' := ⟨0, fun k _ => by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro c a ⟨x, hx⟩
        exact ⟨c • x, fun k hk => by
          rw [D.ρ_smul, hx k hk, smul_eq_mul, map_mul, mul_smul]⟩ }
  have h1 : (1 : Γ(T, V)) ∈ I := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ (span_small_eq_top hV W hc) 1 ?_
    rintro ⟨f, i, hf⟩
    obtain ⟨N, x₀, hx₀⟩ := D.loc_surj hV f (hV.basicOpen f)
      (D.ρ (hW i) (hV.basicOpen f) hf (m i))
    have key : ∀ k, ∃ e : ℕ, resG T (hWV k) f ^ e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      intro k
      refine D.loc_inj (hW k) (resG T (hWV k) f) ((hW k).basicOpen _) _ ?_
      have hle : T.basicOpen (resG T (hWV k) f) ≤ T.basicOpen f := by
        have := T.basicOpen_res f (homOfLE (hWV k)).op
        exact (le_of_eq this).trans inf_le_right
      have h2 := congrArg (D.ρ (hV.basicOpen f) ((hW k).basicOpen (resG T (hWV k) f)) hle) hx₀
      rw [D.ρ_ρ, D.ρ_smul, D.ρ_ρ, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f))] at h2
      rw [map_sub, D.ρ_ρ, D.ρ_smul, map_pow, resG_resG' _ _ (hle.trans (T.basicOpen_le f)),
        ← h2, hm i k _ _ _ (T.basicOpen_le _), sub_self]
    choose e he using key
    refine ⟨s.sup e + N, f ^ s.sup e • x₀, fun k hk => ?_⟩
    have hk' : e k ≤ s.sup e := Finset.le_sup hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hk'
    have h3 : resG T (hWV k) f ^ s.sup e •
        (D.ρ hV (hW k) (hWV k) x₀ - resG T (hWV k) f ^ N • m k) = 0 := by
      rw [hd, pow_add, mul_smul, he, smul_zero]
    rw [smul_sub, sub_eq_zero] at h3
    rw [D.ρ_smul, map_pow, h3, smul_eq_mul, mul_one, map_pow, pow_add, mul_smul]
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, fun k hk => by rw [hx k hk, map_one, one_smul]⟩

theorem exists_glue {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V)
    {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V)
    (hc : V ≤ ⨆ i, W i) (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) :
    ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i := by
  obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover (fun i => (W i : Set T))
    (fun i => (W i).isOpen) (fun x hx => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hx)
      exact Set.mem_iUnion.2 ⟨i, hi⟩)
  obtain ⟨x, hx⟩ := exists_glue_finset D hV W hW hWV hc m hm s
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_small D (hW i) (fun k : s => W k) (fun y hy => ?_) _ ?_
  · obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hs (hWV i hy))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hyk⟩
  · rintro ⟨k, hk⟩ O hO h hOk
    rw [map_sub, D.ρ_ρ, hm i k O hO h hOk, ← hx k hk, D.ρ_ρ, sub_self]

end GlobalTheory.AffGlue.Cech
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_sections_glue : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ m : ∀ i, D.M (W i) (hW i), (∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j), D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) → ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i := by
  atlas_forward_decl GlobalTheory.AffGlue.Cech.exists_glue
end

section
open GlobalTheory.DeRham TensorProduct

namespace GlobalTheory

theorem DeRham.localisation_of_liftSemi_bijective :
    ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R']
      {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
      (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) →
      (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧
        ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  intro R R' _ _ _ f _ M M' _ _ _ _ ρ hρ
  have hloc : IsLocalizedModule (Submonoid.powers f) (TensorProduct.mk R R' M 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R' _).2
      (TensorProduct.isBaseChange R M R')
  refine ⟨fun m' ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hρ.2 m'
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (TensorProduct.mk R R' M 1) z
    refine ⟨n, x, ?_⟩
    have h' : (algebraMap R R' f ^ n) • z = (1 : R') ⊗ₜ[R] x := by
      rw [← map_pow, algebraMap_smul]
      exact h
    rw [← map_smul, h', liftSemi_tmul, one_smul]
  · have h0 : TensorProduct.mk R R' M 1 x = TensorProduct.mk R R' M 1 0 := by
      apply hρ.1
      simp [hx]
    obtain ⟨⟨_, n, rfl⟩, h⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h0
    exact ⟨n, by simpa [Submonoid.smul_def] using h⟩

end GlobalTheory
end

section
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_lift_bijective_localization : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) → (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧ ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  first | exact @GlobalTheory.DeRham.localisation_of_liftSemi_bijective | exact GlobalTheory.DeRham.localisation_of_liftSemi_bijective | (intros; apply GlobalTheory.DeRham.localisation_of_liftSemi_bijective <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) :
    (onAff A hV').left ⟶ (onAff A hV).left :=
  pullback.lift (pullback.fst A.hom hV'.fromSpec)
    (pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op))
    (by rw [pullback.condition, Category.assoc, hV.map_fromSpec hV' (homOfLE h).op])

@[reassoc (attr := simp)] theorem bcProj_fst {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem bcProj_snd {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : bcProj A hV hV' h ≫ pullback.snd A.hom hV.fromSpec =
      pullback.snd A.hom hV'.fromSpec ≫ Spec.map (T.presheaf.map (homOfLE h).op) :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (h : V' ≤ V) : letI := resAlg h
    IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) (bcProj A hV hV' h) := by
  letI := resAlg h
  letI : GrpObj ((Over.pullback hV.fromSpec).obj A) := inferInstanceAs (GrpObj (onAff A hV))
  letI : GrpObj ((Over.pullback hV'.fromSpec).obj A) := inferInstanceAs (GrpObj (onAff A hV'))
  have n := isGrpPullback_pullback A hV'.fromSpec
  refine (isGrpPullback_pullback A hV.fromSpec).cancel ?_ ?_
  · refine IsGrpPullback.congr n ?_ ?_
    · exact (hV.map_fromSpec hV' (homOfLE h).op).symm
    · exact (bcProj_fst A hV hV' h).symm
  · exact bcProj_snd A hV hV' h

theorem eq_bcProj {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (φ : (onAff A hV').left ⟶ (onAff A hV).left)
    (hφ : φ ≫ (onAff A hV).hom = (onAff A hV').hom ≫ Spec.map (T.presheaf.map (homOfLE h).op))
    (hf : φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec) :
    φ = bcProj A hV hV' h := by
  apply pullback.hom_ext
  · rw [hf, bcProj_fst]
  · exact hφ.trans (bcProj_snd A hV hV' h).symm

theorem bcProj_self {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) : bcProj A hV hV h = 𝟙 _ := by
  symm
  apply eq_bcProj
  · rw [Category.id_comp, show (homOfLE h).op = 𝟙 (Opposite.op V) from rfl, T.presheaf.map_id,
      Spec.map_id]
    exact (Category.comp_id _).symm
  · exact Category.id_comp _

theorem bcProj_comp {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') :
    bcProj A hV' hV'' h' ≫ bcProj A hV hV' h = bcProj A hV hV'' (h'.trans h) := by
  apply eq_bcProj
  · change (bcProj A hV' hV'' h' ≫ bcProj A hV hV' h) ≫ pullback.snd A.hom hV.fromSpec = _
    rw [Category.assoc, bcProj_snd, bcProj_snd_assoc, ← Spec.map_comp, ← T.presheaf.map_comp]
    rfl
  · rw [Category.assoc, bcProj_fst, bcProj_fst]

theorem pull_eq_self {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {σ : R →+* R}
    {b : Sp R ⟶ Sp R} {φ : A.left ⟶ A.left}
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A σ b φ) (hσ : σ = RingHom.id R) (hφ : φ = 𝟙 _)
    (c : primDR A) : m.pull c = c := by
  subst hσ hφ
  exact Subtype.ext (IsMor.pullCohomologyOne_id m.isMor c.1)

theorem loc_of_bijective_liftSemi {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M') (hρ : Function.Bijective (liftSemi ρ)) :
    (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧
      ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 :=
  GlobalTheory.T.semilinear_lift_bijective_localization f ρ hρ

section Data

variable {A} (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
  (hg : SmoothOfRelativeDimension g A.hom)

include hA in
theorem isAbelianScheme_onAff {V : T.Opens} (hV : IsAffineOpen V) : IsAbelianScheme (onAff A hV) :=
  isAbelianScheme_pullback_obj hV.fromSpec A hA

include hg in
theorem smooth_onAff {V : T.Opens} (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension g (onAff A hV).hom :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback A.hom hV.fromSpec) hg

include H hA hg in
theorem small_primDR {V : T.Opens} (hV : IsAffineOpen V) : Small.{0} (primDR (onAff A hV)) := by
  obtain ⟨hf, -, -⟩ := H.1.prim (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Γ(T, V) (primDR (onAff A hV))
  exact small_of_surjective hf

def modV {V : T.Opens} (hV : IsAffineOpen V) : Type :=
  @Shrink.{0} (primDR (onAff A hV)) (small_primDR H hA hg hV)

instance {V : T.Opens} (hV : IsAffineOpen V) : AddCommGroup (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

instance {V : T.Opens} (hV : IsAffineOpen V) : Module Γ(T, V) (modV H hA hg hV) := by
  letI := small_primDR H hA hg hV
  unfold modV
  infer_instance

def shEquiv {V : T.Opens} (hV : IsAffineOpen V) : modV H hA hg hV ≃ₗ[Γ(T, V)] primDR (onAff A hV) := by
  letI := small_primDR H hA hg hV
  exact Shrink.linearEquiv Γ(T, V) (primDR (onAff A hV))

def rho {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) :
    modV H hA hg hV →+ modV H hA hg hV' :=
  letI := resAlg h
  { toFun := fun x => (shEquiv H hA hg hV').symm
      ((GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hV' h)).pull (shEquiv H hA hg hV x))
    map_zero' := by simp
    map_add' := fun x y => by simp }

theorem shEquiv_rho {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (x : modV H hA hg hV) : letI := resAlg h
    shEquiv H hA hg hV' (rho H hA hg hV hV' h x) =
      (GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hV' h)).pull (shEquiv H hA hg hV x) :=
  LinearEquiv.apply_symm_apply _ _

def data : Data T where
  M V hV := modV H hA hg hV
  grp V hV := inferInstance
  mod V hV := inferInstance
  ρ hV hV' h := rho H hA hg hV hV' h
  ρ_smul := by
    intro V V' hV hV' h a x
    letI := resAlg h
    apply (shEquiv H hA hg hV').injective
    rw [shEquiv_rho, map_smul, LinearMap.map_smulₛₗ, map_smul, shEquiv_rho]
    rfl
  ρ_self := by
    intro V hV h x
    apply (shEquiv H hA hg hV).injective
    rw [shEquiv_rho]
    refine pull_eq_self _ ?_ (bcProj_self A hV h) _
    ext a
    change (T.presheaf.map (homOfLE h).op).hom a = a
    rw [show (homOfLE h).op = 𝟙 (Opposite.op V) from rfl, T.presheaf.map_id]
    rfl
  ρ_ρ := by
    intro V V' V'' hV hV' hV'' h h' x
    apply (shEquiv H hA hg hV'').injective
    rw [shEquiv_rho, shEquiv_rho, shEquiv_rho]
    exact GrpMor.pull_pull _ _ _ (fun r => resG_resG' h h' (h'.trans h) r) (bcProj_comp A hV hV' hV'' h h') _
  loc_surj := by
    intro V hV f hD m
    letI := resAlg (T.basicOpen_le f)
    haveI : IsLocalization.Away f Γ(T, T.basicOpen f) := hV.isLocalization_basicOpen f
    have hbc := (H.2.2.1 _ (onAff A hV) g (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV) _
      (onAff A hD) (bcProj A hV hD _) (isGrpPullback_bcProj A hV hD _)).1
    obtain ⟨n, x, hx⟩ := (loc_of_bijective_liftSemi f _ hbc).1 (shEquiv H hA hg hD m)
    refine ⟨n, (shEquiv H hA hg hV).symm x, (shEquiv H hA hg hD).injective ?_⟩
    rw [shEquiv_rho, LinearEquiv.apply_symm_apply, ← hx, map_smul]
    rfl
  loc_inj := by
    intro V hV f hD x hx
    letI := resAlg (T.basicOpen_le f)
    haveI : IsLocalization.Away f Γ(T, T.basicOpen f) := hV.isLocalization_basicOpen f
    have hbc := (H.2.2.1 _ (onAff A hV) g (isAbelianScheme_onAff hA hV) (smooth_onAff hg hV) _
      (onAff A hD) (bcProj A hV hD _) (isGrpPullback_bcProj A hV hD _)).1
    have hx' : rho H hA hg hV hD (T.basicOpen_le f) x = 0 := hx
    have h0 : (GlobalTheory.Published.AbelianDeRham.bcMor (isGrpPullback_bcProj A hV hD (T.basicOpen_le f))).pull
        (shEquiv H hA hg hV x) = 0 := by
      rw [← shEquiv_rho, hx', map_zero]
    obtain ⟨n, hn⟩ := (loc_of_bijective_liftSemi f _ hbc).2 (shEquiv H hA hg hV x) h0
    refine ⟨n, ?_⟩
    change (f ^ n • x : modV H hA hg hV) = 0
    apply (shEquiv H hA hg hV).injective
    rw [LinearEquiv.map_smul, hn, LinearEquiv.map_zero]

end Data

end GlobalTheory.DeRhamSheaf

namespace GlobalTheory.AffGlue

variable {T : Scheme.{0}}

theorem sep (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ i, D.ρ hV (hW i) (hWV i) x = 0) : x = 0 :=
  GlobalTheory.T.affine_glue_separated D hV W hW hWV hc x hx

theorem glue (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V) (hc : V ≤ ⨆ i, W i)
    (m : ∀ i, D.M (W i) (hW i))
    (hm : ∀ (i j : ι) (O : T.Opens) (hO : IsAffineOpen O) (hi : O ≤ W i) (hj : O ≤ W j),
      D.ρ (hW i) hO hi (m i) = D.ρ (hW j) hO hj (m j)) :
    ∃ x : D.M V hV, ∀ i, D.ρ hV (hW i) (hWV i) x = m i :=
  GlobalTheory.T.affine_cover_sections_glue D hV W hW hWV hc m hm

theorem isSheaf_famPresheaf (D : Data T) : (famPresheaf D).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hsf
  let s : ∀ k, fam D (U k) := sf
  have key : ∀ (k l : κ) (O : T.Opens) (hO : IsAffineOpen O) (hk : O ≤ U k) (hl : O ≤ U l),
      (s k).1 ⟨O, hO, hk⟩ = (s l).1 ⟨O, hO, hl⟩ := fun k l O hO hk hl =>
    congrFun (congrArg Subtype.val (hsf k l)) ⟨O, hO, le_inf hk hl⟩
  have cov : ∀ W : T.Opens, W ≤ iSup U → W ≤ ⨆ p : Σ k, AffIn (W ⊓ U k), p.2.1 := by
    intro W hW x hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hW hx)
    obtain ⟨O, hO, hxO, hOW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens)
      (show x ∈ W ⊓ U k from ⟨hx, hk⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, O, hO, hOW⟩, hxO⟩
  have hle : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), p.2.1 ≤ W :=
    fun W p => p.2.2.2.trans inf_le_left
  have hleU : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), p.2.1 ≤ U p.1 :=
    fun W p => p.2.2.2.trans inf_le_right
  let val : ∀ (W : T.Opens) (p : Σ k, AffIn (W ⊓ U k)), D.M p.2.1 p.2.2.1 :=
    fun W p => (s p.1).1 ⟨p.2.1, p.2.2.1, hleU W p⟩
  have compat : ∀ (W : T.Opens) (p q : Σ k, AffIn (W ⊓ U k)) (O : T.Opens) (hO : IsAffineOpen O)
      (hp : O ≤ p.2.1) (hq : O ≤ q.2.1),
      D.ρ p.2.2.1 hO hp (val W p) = D.ρ q.2.2.1 hO hq (val W q) := by
    intro W p q O hO hp hq
    rw [fam_rel D (s p.1) ⟨p.2.1, p.2.2.1, hleU W p⟩ ⟨O, hO, hp.trans (hleU W p)⟩ hp,
      fam_rel D (s q.1) ⟨q.2.1, q.2.2.1, hleU W q⟩ ⟨O, hO, hq.trans (hleU W q)⟩ hq]
    exact key p.1 q.1 O hO (hp.trans (hleU W p)) (hq.trans (hleU W q))
  have ex : ∀ (W : T.Opens) (hW : IsAffineOpen W) (_ : W ≤ iSup U), ∃ x : D.M W hW,
      ∀ p : Σ k, AffIn (W ⊓ U k), D.ρ hW p.2.2.1 (hle W p) x = val W p := by
    intro W hW hWU
    exact glue D hW (fun p : Σ k, AffIn (W ⊓ U k) => p.2.1) (fun p => p.2.2.1) (hle W) (cov W hWU)
      (val W) (compat W)
  choose x hx using ex
  have uniq : ∀ (W : T.Opens) (hW : IsAffineOpen W) (_ : W ≤ iSup U) (y z : D.M W hW),
      (∀ p : Σ k, AffIn (W ⊓ U k), D.ρ hW p.2.2.1 (hle W p) y = D.ρ hW p.2.2.1 (hle W p) z) →
        y = z := by
    intro W hW hWU y z h
    rw [← sub_eq_zero]
    exact sep D hW (fun p : Σ k, AffIn (W ⊓ U k) => p.2.1) (fun p => p.2.2.1) (hle W) (cov W hWU) _
      (fun p => by rw [map_sub, h, sub_self])
  let t : fam D (iSup U) := ⟨fun W => x W.1 W.2.1 W.2.2, fun W W' h => by
    apply uniq W'.1 W'.2.1 W'.2.2
    intro p
    rw [D.ρ_ρ, hx]
    exact hx W.1 W.2.1 W.2.2 ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.trans (inf_le_inf_right _ h)⟩⟩
  refine ⟨t, fun k => ?_, fun y hy => ?_⟩
  · apply Subtype.ext
    funext O
    have := hx O.1 O.2.1 (O.2.2.trans (le_iSup U k)) ⟨k, O.1, O.2.1, le_inf le_rfl O.2.2⟩
    rw [D.ρ_self] at this
    exact this
  · have hy' : ∀ k (O : AffIn (U k)), (show fam D (iSup U) from y).1 ⟨O.1, O.2.1, O.2.2.trans (le_iSup U k)⟩ =
        (s k).1 O := fun k O => congrFun (congrArg Subtype.val (hy k)) O
    apply Subtype.ext
    funext W
    apply uniq W.1 W.2.1 W.2.2
    intro p
    rw [fam_rel D (show fam D (iSup U) from y) W ⟨p.2.1, p.2.2.1, (hle W.1 p).trans W.2.2⟩ (hle W.1 p), hx]
    exact hy' p.1 ⟨p.2.1, p.2.2.1, hleU W.1 p⟩

end GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

theorem exists_isDeRhamSheaf : GlobalTheory.Published.AbelianDeRham → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ H : T.Modules, IsDeRhamSheaf A H := by
  intro H T A _ g hA hg
  have hS := isSheaf_famPresheaf (data H hA hg)
  refine ⟨toModules (data H hA hg) hS, fun V hV => (secEquiv hS hV).trans (shEquiv H hA hg hV), ?_⟩
  intro V V' hV hV' h φ hφ hf s
  have e := eq_bcProj A hV hV' h φ (by exact hφ.1.w) hf
  subst e
  change shEquiv H hA hg hV' (secEquiv hS hV' (GlobalTheory.Twist.resM _ h s)) = _
  rw [secEquiv_resM]
  exact shEquiv_rho H hA hg hV hV' h _

end GlobalTheory.DeRhamSheaf
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFinGen

theorem finite_piece (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (f : R) (hf : IsIdempotentElem f) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - f}))))) :
    Module.Finite (R ⧸ Ideal.span {1 - f}) ((R ⧸ Ideal.span {1 - f}) ⊗[R] HO1 A.hom) := by
  haveI : IsLocalization.Away f (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hf
  haveI : Module.Flat R (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.flat (R ⧸ Ideal.span {1 - f}) (Submonoid.powers f)
  let B : Over (Sp (R ⧸ Ideal.span {1 - f})) :=
    (Over.pullback (spMap (algebraMap R (R ⧸ Ideal.span {1 - f})))).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj _ A hA
  have hBg : SmoothOfRelativeDimension g B.hom := hg
  obtain ⟨hfp, -, -, -⟩ := hO _ B g hB hBg
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (R ⧸ Ideal.span {1 - f}) A.left B.left A.hom B.hom
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) inferInstance inferInstance
  haveI := hfp.1
  exact Module.Finite.equiv e.symm

theorem finite_HO1 (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) : Module.Finite R (HO1 A.hom) := by
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R A hA
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff, ← he.complete]
    exact Ideal.sum_mem _ (fun k _ ↦ Ideal.subset_span ⟨k, rfl⟩)
  have hidem : ∀ g : Set.range e, IsIdempotentElem g.val := by
    rintro ⟨_, k, rfl⟩; exact he.idem k
  haveI : ∀ g : Set.range e, IsLocalization.Away g.val (R ⧸ Ideal.span {1 - g.val}) := fun g ↦
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem g)
  haveI : ∀ g : Set.range e, IsLocalizedModule.Away g.val
      (TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) := fun g ↦
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.val) (R ⧸ Ideal.span {1 - g.val}) _).2
      (TensorProduct.isBaseChange R (HO1 A.hom) (R ⧸ Ideal.span {1 - g.val}))
  refine Module.Finite.of_localizationSpan' (Set.range e) hspan
    (Rₚ := fun g ↦ R ⧸ Ideal.span {1 - g.val})
    (Mₚ := fun g ↦ (R ⧸ Ideal.span {1 - g.val}) ⊗[R] HO1 A.hom)
    (fun g ↦ TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) (fun g ↦ ?_)
  obtain ⟨_, k, rfl⟩ := g
  obtain ⟨d, hd⟩ := hsm k
  exact finite_piece hO A hA (e k) (he.idem k) d hd

end GlobalTheory.CechFinGen

theorem GlobalTheory.CechFinGen.finite_HO1_onAff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens,
    Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  intro E _ _ _ H X t hp U
  letI : GrpObj (GlobalTheory.DeRhamSheaf.onAff t.G U.2) := Functor.grpObjObj
  have hA : IsAbelianScheme t.G := GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hp
  exact GlobalTheory.CechFinGen.finite_HO1 GlobalTheory.AbCoh.oStr (GlobalTheory.DeRhamSheaf.onAff t.G U.2) (GlobalTheory.DeRhamSheaf.isAbelianScheme_onAff hA U.2)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_finite_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  atlas_forward_decl GlobalTheory.CechFinGen.finite_HO1_onAff
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

variable {Z : Scheme.{0}}

theorem sf_resG_resG {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem sf_resG_id {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : resG Z h x = x :=
  congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))

theorem sf_resG_inj {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) {x y : Γ(Z, U)}
    (e : resG Z h x = resG Z h y) : x = y := by
  have := congrArg (resG Z h') e
  rwa [sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id] at this

variable {J : Type} (W : J → Z.Opens) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))

def sfCr (U : Z.Opens) (i i' : J) (h : U ≤ W i ⊓ W i') : Γ(Z, U) := resG Z h (c i i')

theorem sfCr_res {U V : Z.Opens} (i i' : J) (h : U ≤ W i ⊓ W i') (h' : V ≤ U) :
    resG Z h' (sfCr W c U i i' h) = sfCr W c V i i' (h'.trans h) :=
  sf_resG_resG _ _ _

theorem sfCr_add (hc : IsCoc W c) (U : Z.Opens) (i i' i'' : J) (h : U ≤ W i ⊓ W i' ⊓ W i'') :
    sfCr W c U i i' (h.trans inf_le_left) +
      sfCr W c U i' i'' (h.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) =
      sfCr W c U i i'' (h.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := by
  have e := congrArg (resG Z h) (hc i i' i'')
  rw [map_add, sf_resG_resG, sf_resG_resG, sf_resG_resG] at e
  exact e

theorem sfCr_self (hc : IsCoc W c) (U : Z.Opens) (i : J) (h : U ≤ W i ⊓ W i) :
    sfCr W c U i i h = 0 := by
  have e := sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))
  have e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h := e
  linear_combination e2


theorem sfCr_congr2 (U : Z.Opens) {i i' j' : J} (e : i' = j') (h : U ≤ W i ⊓ W i') (h' : U ≤ W i ⊓ W j') :
    sfCr W c U i i' h = sfCr W c U i j' h' := by subst e; rfl

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

theorem cechAffineCochainValue_congr_source (f : C1 (OAff s)) {A A' B : Z.affineOpens} (e : A = A') (h : B.1 ≤ A.1) (h' : B.1 ≤ A'.1) :
    fv s f h = fv s f h' := by subst e; rfl

end GlobalTheory.CechFin

open GlobalTheory.CechPoset in

theorem GlobalTheory.CechFin.cocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  intro R _ Z s J W hW hW2 hI S hS c hc
  let κ := {j // j ∈ S}
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let D : κ → Z.Opens := fun k => W k.1
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k) := by
    classical
    intro I hIn
    have := hI (I.image Subtype.val) (hIn.image _)
    rwa [Finset.iInf_finset_image] at this
  have hcov : ⨆ k, D k = ⊤ := by
    rw [← hS, iSup_subtype']
  have hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1 :=
    fun a b => Finset.iInf_union
  have hsup : ⨆ a, (cov D hD a).1 = ⊤ := by
    refine eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))
    refine le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1)
      (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))
    simp [cov]
  have hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1 :=
    fun a k hk => biInf_le (fun k => D k) hk
  let Fv : C1 (covF s D hD) := fun a b φ =>
    sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1
      (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))
  have hF : Fv ∈ Z1 (covF s D hD) := by
    intro a b d φ ψ
    have e := sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1
      (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b))))
        (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))
    show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ =
      resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) +
        sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _
    rw [sfCr_res]
    rw [add_comm]
    exact e.symm
  obtain ⟨y, hy⟩ := (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2
    (H1.mk _ ⟨Fv, hF⟩)
  obtain ⟨f0, rfl⟩ := H1.mk_surjective _ y
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hy
  obtain ⟨g, hg⟩ := hy

  let hfun : ∀ i, Γ(Z, W i) := fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi =>
      -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm :
        W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1)
        (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)
  refine ⟨-f0, hfun, fun i hi i' hi' => ?_⟩
  let k : κ := ⟨i, hi⟩
  let k' : κ := ⟨i', hi'⟩
  let a := ne {k} (Finset.singleton_nonempty k)
  let a' := ne {k'} (Finset.singleton_nonempty k')
  let b := ne {k, k'} (Finset.insert_nonempty k {k'})
  have ca : (cov D hD a.unop).1 = W i := Finset.iInf_singleton k D
  have ca' : (cov D hD a'.unop).1 = W i' := Finset.iInf_singleton k' D
  have cb : (cov D hD b.unop).1 = W i ⊓ W i' := by
    show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  let φ : a ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))
  let φ' : a' ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))
  have hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1 := cov_mono D hD (leOfHom φ.unop)
  have ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1 := cov_mono D hD (leOfHom φ'.unop)
  have hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i' := cb.le
  have hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1 := cb.ge
  have mna : mn a = k := Finset.min'_singleton k
  have mna' : mn a' = k' := Finset.min'_singleton k'
  have hxB : (cov D hD b.unop).1 ≤ W (mn b).1 := hmem b _ (mn_mem b)
  have h4 := congrFun (congrFun (congrFun hg a) b) φ
  have h5 := congrFun (congrFun (congrFun hg a') b) φ'
  have h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A := cov D hD a.unop) (B := cov D hD b.unop) hab -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]
    exact h4
  have h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A := cov D hD a'.unop) (B := cov D hD b.unop) ha'b -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]
    exact h5
  have c1 := sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i'
    (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))
  have c2 := sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1
    (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)
  rw [sfCr_self W c hc] at c2
  have r1 := res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_left hBP
  have r2 := res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_right hBP
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab] at r1
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b] at r2
  have erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') =
      -resG Z hBP (fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) +
        resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by
    show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
      -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) = _
    rw [map_sub, map_neg, map_neg]; ring
  have e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP := rfl
  have t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a) := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi]
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  have t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a') := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi']
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  rw [r1, r2] at erho
  apply sf_resG_inj hBP hPB
  rw [map_add, map_sub, t1, t2]
  linear_combination e0 - erho - h4' + h5' - c1 + c2
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  atlas_forward_decl GlobalTheory.CechFin.cocycle_of_finite_affine_subcover
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover : ∀ (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J), (∀ i, W i ≤ ⨆ a ∈ S, W a) → ∀ d : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W d → ∀ h₀ : ∀ i, Γ(Z, W i), (∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) → ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechFin.isCob_of_isCob_subcover | exact GlobalTheory.CechFin.isCob_of_isCob_subcover | (intros; apply GlobalTheory.CechFin.isCob_of_isCob_subcover <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

namespace GlobalTheory

theorem pullback_fromSpec_compact_affineCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  intro E _ _ _ H X t hP U J W hW hcov
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion (pullback.fst t.G.hom hU.fromSpec) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd t.G.hom hU.fromSpec)
  · intro I hI
    have := GlobalTheory.isAffineHom_diagonal_of_isSeparated (pullback.snd t.G.hom hU.fromSpec)
    refine GlobalTheory.isAffineOpen_finset_biInf (fun i => ?_) I hI
    have hle : W i ≤ (pullback.fst t.G.hom hU.fromSpec).opensRange := by
      intro x hx
      have hx' : x ∈ t.G.hom ⁻¹ᵁ U.1 := hcov ▸ (le_iSup W i) hx
      have hy : t.G.hom x ∈ Set.range hU.fromSpec := by
        rw [hU.range_fromSpec]; exact hx'
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨z, hz⟩
    rw [← (pullback.fst t.G.hom hU.fromSpec).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
    exact hW i
  · rw [← Scheme.Hom.preimage_iSup, hcov, ← Scheme.Hom.comp_preimage, pullback.condition,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  atlas_forward_decl GlobalTheory.pullback_fromSpec_compact_affineCover
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_transfer {Z Z' : Scheme.{0}} {J : Type} (W : J → Z.Opens) (W' : J → Z'.Opens)
    (R : Type) [CommRing R]
    (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) (act' : ∀ i i' : J, R →+* Γ(Z', W' i ⊓ W' i'))
    (φ1 : ∀ i, Γ(Z, W i) →+* Γ(Z', W' i))
    (φ2 : ∀ i i', Γ(Z, W i ⊓ W i') →+* Γ(Z', W' i ⊓ W' i'))
    (φ3 : ∀ i i' i'', Γ(Z, W i ⊓ W i' ⊓ W i'') →+* Γ(Z', W' i ⊓ W' i' ⊓ W' i''))
    (h1 : ∀ i, Function.Surjective (φ1 i))
    (h2 : ∀ i i', Function.Bijective (φ2 i i'))
    (h3 : ∀ i i' i'', Function.Injective (φ3 i i' i''))
    (hl : ∀ i i' x, φ2 i i' (resG Z inf_le_left x) = resG Z' inf_le_left (φ1 i x))
    (hr : ∀ i i' x, φ2 i i' (resG Z inf_le_right x) = resG Z' inf_le_right (φ1 i' x))
    (ha : ∀ i i' i'' x, φ3 i i' i'' (resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') x) =
      resG Z' (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (φ2 i i' x))
    (hb : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'') (φ2 i' i'' x))
    (hc : ∀ i i' i'' x, φ3 i i' i'' (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') x) =
      resG Z' (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'') (φ2 i i'' x))
    (hact : ∀ i i' r, φ2 i i' (act i i' r) = act' i i' r) :
    CechFG W' R act' → CechFG W R act := by
  rintro ⟨N, e', he', hc'⟩
  choose g hg using fun (k : Fin N) (i i' : J) => (h2 i i').2 (e' k i i')
  refine ⟨N, g, ?_, ?_⟩
  · intro k i i' i''
    apply h3 i i' i''
    have := he' k i i' i''
    rw [map_add, ha, hb, hc, hg, hg, hg]
    exact this
  · intro c hcoc
    obtain ⟨r, h', hh⟩ := hc' (fun i i' => φ2 i i' (c i i')) (by
      intro i i' i''
      have := congrArg (φ3 i i' i'') (hcoc i i' i'')
      rw [map_add, ha, hb, hc] at this
      exact this)
    choose h hh1 using fun i => h1 i (h' i)
    refine ⟨r, h, fun i i' => (h2 i i').1 ?_⟩
    have e1 := hh i i'
    rw [map_add, map_sub, map_sum, hl, hr, hh1, hh1]
    simp only [map_mul, hact, hg]
    exact e1

theorem appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {O₁ O₂ : Y.Opens} {V₁ V₂ : X.Opens} (hO : O₂ ≤ O₁)
    (hV : V₂ ≤ V₁) (e₁ : V₁ ≤ f ⁻¹ᵁ O₁) (e₂ : V₂ ≤ f ⁻¹ᵁ O₂) (x : Γ(Y, O₁)) :
    (f.appLE O₂ V₂ e₂).hom (resG Y hO x) = resG X hV ((f.appLE O₁ V₁ e₁).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] {O : Y.Opens}
    (hO : O ≤ f.opensRange) {V : X.Opens} (hV : V = f ⁻¹ᵁ O) (e : V ≤ f ⁻¹ᵁ O) :
    Function.Bijective (f.appLE O V e).hom := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  haveI := f.isIso_app O hO
  exact (asIso (f.app O)).commRingCatIsoToRingEquiv.bijective

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem preimage_inf' {X Y : Scheme.{0}} (f : X ⟶ Y) (A B : Y.Opens) :
    f ⁻¹ᵁ (A ⊓ B) = f ⁻¹ᵁ A ⊓ f ⁻¹ᵁ B := by
  ext x; simp

theorem appLE_act {G X : Scheme.{0}} (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (O : G.Opens)
    (V : (pullback p hU.fromSpec).Opens) (hO : O ≤ p ⁻¹ᵁ U)
    (e : V ≤ pullback.fst p hU.fromSpec ⁻¹ᵁ O) (r : Γ(X, U)) :
    ((pullback.fst p hU.fromSpec).appLE O V e).hom ((p.appLE U O hO).hom r) =
      (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) V).hom r := by
  have e' : V ≤ (pullback.snd p hU.fromSpec ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← pullback.condition]; exact e.trans (Scheme.Hom.preimage_mono _ hO)
  have key : (pullback.snd p hU.fromSpec ≫ hU.fromSpec).appLE U V e' =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (pullback.snd p hU.fromSpec).appLE ⊤ V le_top := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    exact congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·) (Scheme.Hom.map_appLE _ _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq pullback.condition _ _ _ e', key]
  rfl

end GlobalTheory.CechTr

namespace GlobalTheory.CechTr

open GlobalTheory.CechFin

theorem cechFG_of_baseChange_affineOpen (G X : Scheme.{0}) (p : G ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) :
    CechFG (fun i => pullback.fst p hU.fromSpec ⁻¹ᵁ W i) Γ(X, U)
        (fun i i' => (secMap (R := Γ(X, U)) (pullback.snd p hU.fromSpec) _).hom) →
      CechFG W Γ(X, U) (fun i i' => (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  have hR : ∀ O : G.Opens, O ≤ p ⁻¹ᵁ U → O ≤ (pullback.fst p hU.fromSpec).opensRange := by
    intro O hO
    rw [Scheme.Hom.opensRange_pullbackFst, IsAffineOpen.opensRange_fromSpec]
    exact hO
  have h2e : ∀ A B : G.Opens, pullback.fst p hU.fromSpec ⁻¹ᵁ A ⊓ pullback.fst p hU.fromSpec ⁻¹ᵁ B =
      pullback.fst p hU.fromSpec ⁻¹ᵁ (A ⊓ B) := fun A B => (preimage_inf' _ A B).symm
  refine cechFG_of_transfer W _ _ _ _
    (fun i => ((pullback.fst p hU.fromSpec).appLE (W i) _ le_rfl).hom)
    (fun i i' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i') _ (h2e _ _).le).hom)
    (fun i i' i'' => ((pullback.fst p hU.fromSpec).appLE (W i ⊓ W i' ⊓ W i'') _
      (by rw [h2e, h2e])).hom)
    (fun i => (appLE_bijective _ (hR _ (hWU i)) rfl _).2)
    (fun i i' => appLE_bijective _ (hR _ (inf_le_left.trans (hWU i))) (h2e _ _) _)
    (fun i i' i'' => (appLE_bijective _ (hR _ (inf_le_left.trans (inf_le_left.trans (hWU i))))
      (by rw [h2e, h2e]) _).1)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' i'' x => appLE_resG _ _ _ _ _ x)
    (fun i i' r => appLE_act p U hU _ _ _ _ r)

theorem cechFG_of_baseChange_affine (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type)
    (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1) :
    CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1)
        (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) →
      CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) :=
  cechFG_of_baseChange_affineOpen G X p U.1 U.2 J W hWU

end GlobalTheory.CechTr
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  atlas_forward_decl GlobalTheory.CechTr.cechFG_of_baseChange_affine
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := GlobalTheory.T.cechCocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by
    rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add, map_add]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover E H X t hP U J W hWaff hcov
  have hfin := GlobalTheory.T.structure_h1_finite_affine_open E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_finite_generation_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  atlas_forward_decl GlobalTheory.CechFin.cech_h1_finite
end
