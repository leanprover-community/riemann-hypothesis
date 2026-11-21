import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforward
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_top_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))], Statement I (⊤ : X.IdealSheafData) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Unit.statement_top
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Dich

open TopologicalSpace Scheme.IdealSheafData

theorem isReduced_subscheme_of_radical_eq {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : J.radical = J) : IsReduced J.subscheme := by
  have : ∀ U, IsReduced (J.subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ J.ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    have e : (J.ideal U).radical = J.ideal U := congr($(h).ideal U)
    exact Ideal.radical_eq_iff.mp e
  exact IsReduced.of_openCover _ J.subschemeCover.openCover

theorem irreducibleSpace_subscheme {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : IsIrreducible (J.support : Set X)) : IrreducibleSpace J.subscheme := by
  have hr : Set.range J.subschemeι = (J.support : Set X) := J.range_subschemeι
  have hirr : IsIrreducible (Set.range J.subschemeι) := hr ▸ h
  have : IrreducibleSpace (Set.range J.subschemeι) :=
    { toPreirreducibleSpace := Subtype.preirreducibleSpace hirr.2
      toNonempty := hirr.1.to_subtype }
  exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this

theorem exists_radical_pow_le {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData) :
    ∃ k : ℕ, J.radical ^ k ≤ J := by
  have hU : ∀ U : X.affineOpens, ∃ k : ℕ, (J.ideal U).radical ^ k ≤ J.ideal U := fun U => by
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose k hk using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.sup k, le_of_iSup_eq_top (fun i : t => i.1) ?_ fun i => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change (J.ideal i.1).radical ^ t.sup k ≤ J.ideal i.1
    exact (Ideal.pow_le_pow_right (Finset.le_sup i.2)).trans (hk i.1)

theorem exists_of_radical_ne {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData)
    (hJ : J ≠ ⊤) (hr : J.radical ≠ J) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  classical
  have hex := exists_radical_pow_le J
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, J.radical ^ (m + 1) ≤ J ∧ ¬ J.radical ^ m ≤ J := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · have hs := Nat.find_spec hex
      rw [hk, pow_zero] at hs
      exact absurd (top_le_iff.mp hs) hJ
    · refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
      rw [Nat.sub_add_cancel hk]
      exact Nat.find_spec hex
  refine ⟨J.radical, J ⊔ J.radical ^ m, lt_of_le_of_ne J.le_radical hr.symm,
    left_lt_sup.mpr hm₂, fun U a b ha hb => ?_⟩
  have hle : J.radical.ideal U * (J ⊔ J.radical ^ m).ideal U ≤ J.ideal U := by
    change J.radical.ideal U * (J.ideal U ⊔ (J.radical.ideal U) ^ m) ≤ J.ideal U
    rw [Ideal.mul_sup]
    refine sup_le Ideal.mul_le_right ?_
    rw [← pow_succ']
    exact hm₁ U
  exact hle (Ideal.mul_mem_mul ha hb)

theorem exists_of_not_preirreducible {X : Scheme.{0}} (J : X.IdealSheafData)
    (hr : J.radical = J) (hirr : ¬ IsPreirreducible (J.support : Set X)) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  push_neg at hirr
  obtain ⟨Z₁, Z₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hirr
  let C₁ : Closeds X := J.support ⊓ ⟨Z₁, h₁⟩
  let C₂ : Closeds X := J.support ⊓ ⟨Z₂, h₂⟩
  have hsup : C₁ ⊔ C₂ = J.support := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hlt : ∀ (C : Closeds X) (Z : Set X), C ≤ J.support → (C : Set X) ⊆ Z →
      ¬ (J.support : Set X) ⊆ Z → J < vanishingIdeal C := by
    intro C Z hC hCZ hn
    refine lt_of_le_not_ge (le_support_iff_le_vanishingIdeal.mp hC) fun hle => hn ?_
    intro x hx
    have hx' : x ∈ ((vanishingIdeal C).support : Set X) := support_antitone hle hx
    rw [coe_support_vanishingIdeal] at hx'
    exact hCZ hx'
  refine ⟨vanishingIdeal C₁, vanishingIdeal C₂, hlt C₁ Z₁ inf_le_left (fun x hx => hx.2) hn₁,
    hlt C₂ Z₂ inf_le_left (fun x hx => hx.2) hn₂, fun U a b ha hb => ?_⟩
  have e : vanishingIdeal C₁ ⊓ vanishingIdeal C₂ = J := by
    rw [← vanishingIdeal_sup, hsup, vanishingIdeal_support, hr]
  have hm : a * b ∈ (vanishingIdeal C₁ ⊓ vanishingIdeal C₂).ideal U :=
    ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩
  rwa [e] at hm

theorem isIntegral_or_exists_mul_mem : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData),
    J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧
      ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U →
        a * b ∈ J.ideal U := by
  intro X _ J hJ
  by_cases hr : J.radical = J
  · by_cases hirr : IsPreirreducible (J.support : Set X)
    · left
      have hne : (J.support : Set X).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        exact hJ (J.support_eq_bot_iff.mp (SetLike.coe_injective h))
      haveI := isReduced_subscheme_of_radical_eq J hr
      haveI := irreducibleSpace_subscheme J ⟨hne, hirr⟩
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    · exact Or.inr (exists_of_not_preirreducible J hr hirr)
  · exact Or.inr (exists_of_radical_ne J hJ hr)

end GlobalTheory.CompanionTheory.GE.Dich
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_ideal_integral_or_split : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData), J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem idealSheafData_wellFoundedGT :
    ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  intro X _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, hUt, hxU⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  have hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1)) := fun i => by
    haveI : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) :=
      IsLocallyNoetherian.component_noetherian i.1
    infer_instance
  let φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) :=
    fun I i => I.ideal i.1
  have hφ : StrictMono φ := by
    refine Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_
    intro I J h
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov
      (fun i => congrFun h i)
  have h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) := ⟨h1.wf⟩
  exact hφ.wellFoundedGT

end GlobalTheory.CompanionTheory.GE
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_sheaf_well_founded_gt : ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.NonPrime

variable {X : Scheme.{0}}

lemma secs_mk {E F : X.Modules} (f : F ⟶ E) [Mono f] (V : X.Opens) :
    secs (Subobject.mk f) V = Set.range (f.app V) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.underlyingIso_arrow]

lemma smul_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} (a : Γ(X, V)) {x : Γ(E, V)}
    (hx : x ∈ secs S V) : a • x ∈ secs S V := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨a • t, Scheme.Modules.Hom.app_smul S.arrow a t⟩

lemma add_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} {x y : Γ(E, V)}
    (hx : x ∈ secs S V) (hy : y ∈ secs S V) : x + y ∈ secs S V := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, map_add _ s t⟩

def idealSub (J : X.IdealSheafData) (E : X.Modules) : Subobject E :=
  Subobject.mk (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))

lemma secs_idealSub (J : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (U : X.affineOpens) :
    secs (idealSub J E) U = ((J.ideal U • ⊤ : Submodule Γ(X, U) Γ(E, U)) : Set Γ(E, U)) := by
  rw [idealSub, secs_mk, ← (GlobalTheory.surjective_and_ker_unit_subschemeι J E U).2,
    ← GlobalTheory.QCoh.range_kernel_ι_app]
  rfl

lemma isQuasicoherent_idealSub (J : X.IdealSheafData) {E : X.Modules} (hE : IsCoherent E) :
    ((idealSub J E : Subobject E) : X.Modules).IsQuasicoherent := by
  have := hE.1
  have := (isCoherent_pullback J.subschemeι hE).1
  have h₀ : ((𝟭 X.Modules).obj E).IsQuasicoherent := hE.1
  have h₁ : ((Scheme.Modules.pullback J.subschemeι ⋙ Scheme.Modules.pushforward J.subschemeι).obj
      E).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom J.subschemeι
    ((Scheme.Modules.pullback J.subschemeι).obj E)
  have hk : (kernel ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app
      E)).IsQuasicoherent := GlobalTheory.QCoh.isQuasicoherent_kernel _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))).symm hk

lemma propSupp_mono {A : Type} [CommRing A] [X.Over (Spec (.of A))] {E : X.Modules}
    {S S' : Subobject E} (h : S ≤ S') (hS : PropSupp A S) : PropSupp A S' := by
  obtain ⟨T, hT, hsupp⟩ := hS
  refine ⟨T, hT, ?_⟩
  have w : S.arrow ≫ cokernel.π S'.arrow = 0 := by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) :=
    epi_of_epi_fac (cokernel.π_desc S.arrow (cokernel.π S'.arrow) w)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) hsupp

theorem statement_of_mul_mem : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J J₁ J₂ : X.IdealSheafData),
    (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) →
    Statement I J₁ → Statement I J₂ → Statement I J := by
  intro A _ _ I X _ _ _ _ J J₁ J₂ hm h₁ h₂ E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hEq : E.IsQuasicoherent := hE.1
  set K : Subobject E := idealSub J₁ E with hKdef
  have hKq : (K : X.Modules).IsQuasicoherent := isQuasicoherent_idealSub J₁ hE
  have hS1 : ClosedSys I E (fun e => S e ⊔ K) :=
    { qcoh := fun e => (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh e) hKq).1
      pow_le := fun e => (hS.pow_le e).trans le_sup_left
      succ := fun e => by
        conv_lhs => rw [hS.succ e]
        exact sup_right_comm _ _ _ }
  have hK1 : ∀ e, Killed J₁ (S e ⊔ K) := by
    intro e U a ha x
    have hax : a • x ∈ secs K U := by
      rw [hKdef, secs_idealSub]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact (GlobalTheory.T.subobject_le_iff_affine_sections K (S e ⊔ K)).1 le_sup_right U hax
  obtain ⟨B, hBq, hBP, hB⟩ := h₁ E hE _ hS1 hK1 (propSupp_mono le_sup_left hP)
  have hDq : ((B ⊔ K : Subobject E) : X.Modules).IsQuasicoherent :=
    (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ hBq hKq).1
  have hDP : PropSupp A (B ⊔ K) := propSupp_mono le_sup_left hBP
  have hc : ∀ e, S (e + 0) ≤ (B ⊔ K) ⊔ powSub I E (e + 1) := fun e =>
    (le_sup_left : S e ≤ S e ⊔ K).trans ((hB e).symm.le.trans (sup_le_sup_right le_sup_left _))
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP (B ⊔ K) hDq 0 hc
  have hkill : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J₂.ideal U →
      ∀ x ∈ secs (B ⊔ K) U, a • x ∈ secs (S n) U := by
    intro n U a ha x hx
    have hle : B ⊔ K ≤ S n ⊔ K :=
      sup_le ((le_sup_left : B ≤ B ⊔ powSub I E (n + 1)).trans (hB n).le) le_sup_right
    have hx' := (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 hle U hx
    rw [(GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh n) hKq).2 U U.2] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    rw [smul_add]
    refine add_mem_secs _ (smul_mem_secs _ a hs) ?_
    rw [hKdef, secs_idealSub] at hk
    refine Submodule.smul_induction_on (p := fun k => a • k ∈ secs (S n) U) hk
      (fun b hb y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul, mul_comm]
      exact hK n U _ (hm U b a hb ha) y
    · rw [smul_add]
      exact add_mem_secs _ hy hz
  exact halg (h₂ _ (GlobalTheory.T.coherent_subobject_coherent hE _ hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J₂ _ S c' hkill) hP') hDP

end GlobalTheory.CompanionTheory.GE.NonPrime
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_product_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J J₁ J₂ : X.IdealSheafData), (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) → Statement I J₁ → Statement I J₂ → Statement I J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem
end

section
section
set_option autoImplicit false
set_option maxSynthPendingDepth 1

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  TopologicalSpace

namespace GlobalTheory.CompanionTheory.GE.ChowOpen

lemma isClosedImmersion_restrict_iSup {T Z : Scheme.{0}} (f : T ⟶ Z) {ι : Type} (V : ι → Z.Opens)
    (h : ∀ i, IsClosedImmersion (f ∣_ V i)) : IsClosedImmersion (f ∣_ (⨆ i, V i)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => (⨆ i, V i).ι ⁻¹ᵁ V i) ?_ ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    have hV : (⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i) = V i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup V i)
    have e := morphismRestrictRestrict f (⨆ i, V i) ((⨆ i, V i).ι ⁻¹ᵁ V i)
    have h' : IsClosedImmersion (f ∣_ ((⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i))) := by
      rw [hV]; exact h i
    exact (MorphismProperty.arrow_mk_iso_iff (@IsClosedImmersion) e).2 h'

theorem exists_image_open {T Z : Scheme.{0}} (f : T ⟶ Z) [QuasiCompact f] (S : Z.Opens)
    [IsClosedImmersion (f ∣_ S)] (hS : f ⁻¹ᵁ S = ⊤) :
    ∃ (O : f.image.Opens) (φ : O.toScheme ⟶ T), IsIso φ ∧ φ ≫ f = O.ι ≫ f.imageι := by
  have hι : IsIso (f ⁻¹ᵁ S).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨by rw [← Set.range_eq_univ, Scheme.Opens.range_ι, hS]; rfl⟩⟩
  refine ⟨f.imageι ⁻¹ᵁ S, SchemeImage.imageRestrictLift f S ≫ (f ⁻¹ᵁ S).ι, inferInstance, ?_⟩
  rw [Category.assoc, ← morphismRestrict_ι, SchemeImage.imageRestrictLift_fac_assoc,
    morphismRestrict_ι]

theorem exists_chow_open_projective {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (s : X ⟶ Spec (.of A)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IrreducibleSpace X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ s ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian X := ⟨⟩
  have hex : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := htne.card_pos; omega⟩
  let e : Fin (k + 1) ≃ t := (Fintype.equivFinOfCardEq (by simpa using hk)).symm
  let U : Fin (k + 1) → X.Opens := fun j => V (e j)
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hVaff _
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨e.symm ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hc := fun j => ProjSpace.exists_closedImmersion_stdOpen (A := A) s (hUaff j)
  choose n c hccl hcc using hc
  have : ∀ j, IsClosedImmersion (c j) := hccl
  have hη : genericPoint X ∈ ChowGraph.W U := by
    rw [ChowGraph.W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ((genericPoint_spec X).mem_open_set_iff (U j).2).2
      ⟨e j, Set.mem_univ _, hxV _⟩
  have : NoetherianSpace (ChowGraph.W U).toScheme :=
    NoetherianSpace.set ((ChowGraph.W U : X.Opens) : Set X)
  have : QuasiCompact (ChowGraph.g s n U c hcc) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hqc : QuasiCompact (ChowGraph.q s n U c hcc) := by
    unfold ChowGraph.q; infer_instance
  have hcl : IsClosedImmersion
      (ChowGraph.q s n U c hcc ∣_ (⨆ i, ChowGraph.V (A := A) n i)) :=
    isClosedImmersion_restrict_iSup _ _ fun i =>
      ChowGraph.isClosedImmersion_q_restrict s n U c hcc i
  have hS : ChowGraph.q s n U c hcc ⁻¹ᵁ (⨆ i, ChowGraph.V (A := A) n i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : ChowGraph.π s n U c hcc y ∈ (⊤ : X.Opens) := trivial
    rw [← hU] at hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, ChowGraph.q_mem_V s n U c hcc i y hi⟩
  obtain ⟨O, φ, hφ, hφq⟩ := exists_image_open (ChowGraph.q s n U c hcc) _ hS
  have hπ : IsProper (ChowGraph.π s n U c hcc) := by
    unfold ChowGraph.π; infer_instance
  refine ⟨ProjSpace.multiProjDim k n, (ChowGraph.q s n U c hcc).image,
    (ChowGraph.q s n U c hcc).imageι ≫ ProjSpace.multiProjEmb A k n, O,
    φ ≫ ChowGraph.π s n U c hcc, ChowGraph.W U, inferInstance, inferInstance, ?_, ⟨_, hη⟩, ?_⟩
  · rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, ← Category.assoc, ← hφq]
    simp only [ChowGraph.q, ChowGraph.π, Category.assoc, pullback.condition]
  · rw [morphismRestrict_comp]
    have := ChowGraph.isIso_π_restrict s n U c hcc
    have h1 : IsIso (φ ∣_ (ChowGraph.π s n U c hcc ⁻¹ᵁ ChowGraph.W U)) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hφ _
    exact IsIso.comp_isIso' h1 this

theorem exists_chow_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧
      IsIso (ψ ∣_ W) :=
  exists_chow_open_projective (X ↘ Spec (.of A))

end GlobalTheory.CompanionTheory.GE.ChowOpen
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chow_cover_integral : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X], ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens) (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧ O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GlobalTheory.QCoh

namespace GlobalTheory.CompanionTheory.GE.Close

variable {X : Scheme.{0}}

abbrev fn (V : X.Opens) : Γ(𝟙_ X.Modules, V) ≃ₗ[Γ(X, V)] Γ(X, V) := structureModuleSectionsEquiv V

def subOf (J : X.IdealSheafData) : Subobject (𝟙_ X.Modules) := Subobject.mk (idealModuleι J)

theorem mem_secs_subOf (J : X.IdealSheafData) (V : X.affineOpens) (x : Γ(𝟙_ X.Modules, V.1)) :
    x ∈ secs (subOf J) V.1 ↔ fn V.1 x ∈ J.ideal V := by
  unfold secs subOf
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, range_app_iso_comp,
    ← exists_idealModuleι_app_eq_iff_mem]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (fn V.1).injective ht⟩

theorem subOf_qcoh (J : X.IdealSheafData) : ((subOf J : Subobject _) : X.Modules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealModuleι J)).symm inferInstance

theorem subOf_le_iff {J K : X.IdealSheafData} : subOf J ≤ subOf K ↔ J ≤ K := by
  rw [le_iff_secs_subset]
  constructor
  · intro h U a ha
    have := h U ((mem_secs_subOf J U ((fn U.1).symm a)).2 (by simpa using ha))
    simpa using (mem_secs_subOf K U _).1 this
  · intro h U x hx
    exact (mem_secs_subOf K U x).2 (h U ((mem_secs_subOf J U x).1 hx))

theorem subOf_sup (J K : X.IdealSheafData) : subOf (J ⊔ K) = subOf J ⊔ subOf K := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  obtain ⟨hq, hs⟩ := GlobalTheory.CompanionTheory.GE.supsecs hE (subOf J) (subOf K) (subOf_qcoh J) (subOf_qcoh K)
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    rw [hs U.1 U.2]
    have h1 := (mem_secs_subOf _ U x).1 hx
    rw [Scheme.IdealSheafData.ideal_sup] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨(fn U.1).symm a, (mem_secs_subOf J U _).2 (by simpa using ha),
      (fn U.1).symm b, (mem_secs_subOf K U _).2 (by simpa using hb), ?_⟩
    apply (fn U.1).injective
    simpa using hab.symm
  · exact sup_le (subOf_le_iff.2 le_sup_left) (subOf_le_iff.2 le_sup_right)

theorem eq_subOf_of_qcoh (B : Subobject (𝟙_ X.Modules)) (hB : (B : X.Modules).IsQuasicoherent) :
    ∃ J : X.IdealSheafData, subOf J = B := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have : IsFiniteQC (𝟙_ X.Modules) := isFiniteQC_structureModule
  have hq : (cokernel B.arrow).IsQuasicoherent := inferInstance
  have : IsFiniteQC (cokernel B.arrow) := .of_epi (cokernel.π B.arrow)
  refine ⟨annihilatorSheaf (cokernel B.arrow), ?_⟩
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    have hA := (mem_secs_subOf _ U x).1 hx
    rw [annihilatorSheaf_ideal, Module.mem_annihilator] at hA
    have h0 := hA ((cokernel.π B.arrow).app U.1 ((fn U.1).symm 1))
    rw [← Scheme.Modules.Hom.app_smul] at h0
    have hx' : fn U.1 x • (fn U.1).symm 1 = x := by
      apply (fn U.1).injective
      simp
    rw [hx'] at h0
    exact (exact_cokernel_π_app B.arrow U.2 x).1 h0
  · rw [le_iff_secs_subset]
    rintro U x ⟨y, rfl⟩
    refine (mem_secs_subOf _ U _).2 ?_
    rw [annihilatorSheaf_ideal, Module.mem_annihilator]
    intro m
    obtain ⟨z, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app B.arrow U.2 m
    rw [← Scheme.Modules.Hom.app_smul]
    have hc : fn U.1 (B.arrow.app U.1 y) • z = fn U.1 z • B.arrow.app U.1 y := by
      apply (fn U.1).injective
      simp [mul_comm]
    rw [hc, Scheme.Modules.Hom.app_smul, (exact_cokernel_π_app B.arrow U.2).apply_apply_eq_zero y,
      smul_zero]

theorem mono_cokernel_desc_of_exact {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h : S.Exact) : Mono (cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 h

theorem supportedIn_cokernel_idealModuleι (J : X.IdealSheafData) :
    Scheme.Modules.SupportedIn (cokernel (idealModuleι J)) (J.support : Set X) := by
  have hpush : Scheme.Modules.SupportedIn
      ((Scheme.Modules.pushforward J.subschemeι).obj (structureModule J.subscheme))
      (J.support : Set X) := by
    refine ((Scheme.Modules.SupportedIn.univ _).pushforward J.subschemeι).mono ?_
    rintro _ ⟨z, -, rfl⟩
    exact J.range_subschemeι.le ⟨z, rfl⟩
  let S : ShortComplex X.Modules := ShortComplex.mk (idealModuleι J) (toSubscheme J) (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := mono_cokernel_desc_of_exact S hex
  exact Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) hpush

theorem supportedIn_subOf (J : X.IdealSheafData) :
    Scheme.Modules.SupportedIn (cokernel (subOf J).arrow) (J.support : Set X) := by
  have e : (Subobject.underlyingIso (idealModuleι J)).hom ≫ idealModuleι J = (subOf J).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk _
  let i : cokernel (subOf J).arrow ≅ cokernel (idealModuleι J) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (Subobject.underlyingIso (idealModuleι J)).hom _)
  exact (supportedIn_cokernel_idealModuleι J).of_iso i.symm

theorem support_subset_of_supportedIn (J : X.IdealSheafData) {T : Set X} (hT : IsClosed T)
    (h : Scheme.Modules.SupportedIn (cokernel (subOf J).arrow) T) : (J.support : Set X) ⊆ T := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have hq := subOf_qcoh J
  intro x hx
  by_contra hxT
  obtain ⟨U, ⟨V, hV, rfl⟩, hxV, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxT hT.isOpen_compl
  let W : X.affineOpens := ⟨V, hV⟩
  have h0 := h V (Set.disjoint_left.2 fun y hy hyT => hle hy hyT)
    ((cokernel.π (subOf J).arrow).app V ((fn V).symm 1))
  have h1 := (exact_cokernel_π_app (subOf J).arrow hV _).1 h0
  have h2 : (1 : Γ(X, V)) ∈ J.ideal W := by
    have := (mem_secs_subOf J W _).1 h1
    simpa [W] using this
  obtain ⟨t, ht⟩ := (exists_idealModuleι_app_eq_iff_mem J W 1).2 h2
  refine notMem_support_of_mem_basicOpen J t (x := x) ?_ hx
  rw [ht, Scheme.basicOpen_of_isUnit _ isUnit_one]
  exact hxV

theorem isProper_of_support_subset {S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (J T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ f)) (h : (J.support : Set X) ⊆ T.support) :
    IsProper (J.subschemeι ≫ f) := by
  let K : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal J.support
  have hJK : J ≤ K := (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).1 le_rfl
  have hTK : T ≤ K := (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).1 h
  have hKs : (K.support : Set X) = J.support := by
    simp [K]
  let p : K.subscheme ⟶ J.subscheme := IsClosedImmersion.lift J.subschemeι K.subschemeι
    (by simpa using hJK)
  let q : K.subscheme ⟶ T.subscheme := IsClosedImmersion.lift T.subschemeι K.subschemeι
    (by simpa using hTK)
  have hp : p ≫ J.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hq : q ≫ T.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hqc : IsClosedImmersion q := by
    have : IsClosedImmersion (q ≫ T.subschemeι) := by rw [hq]; infer_instance
    exact IsClosedImmersion.of_comp q T.subschemeι
  have hsurj : Surjective p := by
    refine ⟨fun z => ?_⟩
    have h1 : J.subschemeι z ∈ (K.support : Set X) := by
      rw [hKs]; exact J.range_subschemeι.le ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := K.range_subschemeι.ge h1
    refine ⟨w, J.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← hp]
    rfl
  have huc : UniversallyClosed (p ≫ J.subschemeι ≫ f) := by
    rw [← Category.assoc, hp, ← hq, Category.assoc]
    infer_instance
  have : UniversallyClosed (J.subschemeι ≫ f) := .of_comp_surjective p _
  exact ⟨⟩

section Core

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [X.Over (Spec (.of R))]

theorem subOf_eq_powSub (Q : X.IdealSheafData) (n : ℕ)
    (hQ : ∀ U : X.affineOpens, Q.ideal U = Ideal.map (toFunctions (A := R) U.1) (I ^ n)) :
    subOf Q = powSub I (𝟙_ X.Modules) n := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have key : ∀ (U : X.affineOpens) (x : Γ(𝟙_ X.Modules, U.1)),
      x ∈ secs (powSub I (𝟙_ X.Modules) n) U.1 ↔ fn U.1 x ∈ Q.ideal U := by
    intro U x
    rw [secs_powSub I _ hE n U.1 U.2, hQ U, SetLike.mem_coe]
    have e : Submodule.map (fn U.1).toLinearMap (Ideal.map (toFunctions (A := R) U.1) (I ^ n) • ⊤ :
        Submodule Γ(X, U.1) Γ(𝟙_ X.Modules, U.1)) = Ideal.map (toFunctions (A := R) U.1) (I ^ n) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
      simp
    constructor
    · intro h
      rw [← e]
      exact ⟨x, h, rfl⟩
    · intro h
      rw [← e] at h
      obtain ⟨y, hy, hyx⟩ := h
      have hxy : y = x := (fn U.1).injective hyx
      exact hxy ▸ hy
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    exact (key U x).2 ((mem_secs_subOf Q U x).1 hx)
  · rw [le_iff_secs_subset]
    intro U x hx
    exact (mem_secs_subOf Q U x).2 ((key U x).1 hx)

theorem exists_ideal_of_statement [IsSeparated (X ↘ Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    (hS : Statement I (⊥ : X.IdealSheafData)) (J Q : ℕ → X.IdealSheafData)
    (hQ : ∀ e, subOf (Q e) = powSub I (𝟙_ X.Modules) (e + 1)) (hJQ : ∀ e, Q e ≤ J e)
    (hsucc : ∀ e, J e = J (e + 1) ⊔ Q e)
    (hprop : IsProper ((J 0).subschemeι ≫ (X ↘ Spec (.of R)))) :
    ∃ JB : X.IdealSheafData, IsProper (JB.subschemeι ≫ (X ↘ Spec (.of R))) ∧
      ∀ e, JB ⊔ Q e = J e := by
  have hcs : ClosedSys I (𝟙_ X.Modules) (fun e => subOf (J e)) :=
    { qcoh := fun e => subOf_qcoh (J e)
      pow_le := fun e => by
        rw [← hQ]
        exact subOf_le_iff.2 (hJQ e)
      succ := fun e => by
        rw [← hQ, ← subOf_sup, ← hsucc] }
  have hk : ∀ e, Killed (⊥ : X.IdealSheafData) (subOf (J e)) := by
    intro e U a ha x
    have ha0 : a = 0 := by simpa using ha
    rw [ha0, zero_smul]
    exact ⟨0, map_zero _⟩
  obtain ⟨B, hBq, ⟨T, hT, hsup⟩, hB⟩ := hS (𝟙_ X.Modules) (isCoherent_unit X) _ hcs hk
    ⟨J 0, hprop, supportedIn_subOf (J 0)⟩
  obtain ⟨JB, rfl⟩ := eq_subOf_of_qcoh B hBq
  refine ⟨JB, isProper_of_support_subset _ JB T hT
    (support_subset_of_supportedIn JB T.support.isClosed hsup), fun e => ?_⟩
  have h1 : subOf (JB ⊔ Q e) = subOf (J e) := by
    rw [subOf_sup, hQ]
    exact hB e
  exact le_antisymm (subOf_le_iff.1 h1.le) (subOf_le_iff.1 h1.ge)

end Core

section Thick

variable {R : Type} [CommRing R] (I : Ideal R) [X.Over (Spec (.of R))]

theorem fromSpec_appTop {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
  have h := hV.fromSpec_app_of_le ⊤ le_top
  have e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]
    simp
  refine h.trans ?_
  erw [e, Category.comp_id]
  rfl

theorem toFunctions_hom {V : X.Opens} :
    (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop ≫ X.presheaf.map (homOfLE le_top).op =
      CommRingCat.ofHom (toFunctions (A := R) V) := by
  ext r
  rfl

theorem fromSpec_comp_over {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom (toFunctions (A := R) V)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop,
    ← cancel_epi (Scheme.ΓSpecIso (.of R)).inv, ← Scheme.ΓSpecIso_inv_naturality,
    ← toFunctions_hom]
  simp only [Category.assoc]
  rfl

theorem toFunctions_mem_ker (e : ℕ) (U : X.affineOpens) (r : R) (hr : r ∈ I ^ (e + 1)) :
    (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).app U.1 (toFunctions (A := R) U.1 r) = 0 := by
  set f := X ↘ Spec (.of R)
  set pr := pullback.fst f (thick R I e)
  have h1 : (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ pr.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (.of (R ⧸ I ^ (e + 1)))).inv ≫ (pullback.snd f (thick R I e)).appTop := by
    rw [← Scheme.Hom.comp_appTop, show pr ≫ f = _ from pullback.condition, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h2 : pr.appTop (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) = 0 := by
    have h4 := ConcreteCategory.congr_hom h1 r
    simp only [ConcreteCategory.comp_apply] at h4
    refine h4.trans ?_
    have h5 : (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hr
    rw [h5, map_zero, map_zero]
  have nat := pr.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op
  have h3 := ConcreteCategory.congr_hom nat (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
  simp only [ConcreteCategory.comp_apply] at h3
  change pr.app U.1 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
    (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) = 0
  refine h3.trans ?_
  erw [h2, map_zero]

theorem appLE_fromSpec {A : CommRingCat.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (q : CommRingCat.of Γ(X, V) ⟶ A) (h : ⊤ ≤ (Spec.map q ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map q ≫ hV.fromSpec).appLE V ⊤ h = q ≫ (Scheme.ΓSpecIso A).inv := by
  rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc]
  erw [Scheme.Hom.map_appLE]
  rw [Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_app_eq_zero (e : ℕ) (U : X.affineOpens) (a : Γ(X, U.1))
    (ha : (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).app U.1 a = 0) :
    a ∈ Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) := by
  have hU : IsAffineOpen U.1 := U.2
  set 𝔞 := Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) with h𝔞
  let v : R ⧸ I ^ (e + 1) →+* Γ(X, U.1) ⧸ 𝔞 :=
    Ideal.quotientMap 𝔞 (toFunctions (A := R) U.1) Ideal.le_comap_map
  let q : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of (Γ(X, U.1) ⧸ 𝔞) :=
    CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)
  let t : Spec (.of (Γ(X, U.1) ⧸ 𝔞)) ⟶ X := Spec.map q ≫ hU.fromSpec
  have hw : t ≫ (X ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom v) ≫ thick R I e := by
    simp only [t, Category.assoc, fromSpec_comp_over hU, ← Spec.map_comp]
    rfl
  let l := pullback.lift t (Spec.map (CommRingCat.ofHom v)) hw
  have hl : l ≫ pullback.fst (X ↘ Spec (.of R)) (thick R I e) = t := pullback.lift_fst _ _ _
  have hh : ⊤ ≤ t ⁻¹ᵁ U.1 := by
    intro z _
    change (Spec.map q ≫ hU.fromSpec) z ∈ U.1
    rw [Scheme.Hom.comp_apply]
    exact hU.range_fromSpec.le ⟨_, rfl⟩
  have e1 : ∀ (g : Spec (.of (Γ(X, U.1) ⧸ 𝔞)) ⟶ X) (hg : l ≫ pullback.fst (X ↘ Spec (.of R)) (thick R I e) = g)
      (h : ⊤ ≤ g ⁻¹ᵁ U.1), g.appLE U.1 ⊤ h a = 0 := by
    rintro _ rfl h
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  have e2 := e1 t hl hh
  rw [show t.appLE U.1 ⊤ hh = _ from appLE_fromSpec hU q hh, CommRingCat.comp_apply] at e2
  have e3 : q a = 0 := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso _).inv)
    rw [e2, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 e3

theorem ideal_ker_thick (e : ℕ) (U : X.affineOpens) :
    (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).ker.ideal U =
      Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Scheme.Hom.ker_apply]
  apply le_antisymm
  · intro a ha
    exact mem_of_app_eq_zero I e U a ha
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact toFunctions_mem_ker I e U r hr

end Thick

section Main

theorem isClosedImmersion_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem thickMap_fst {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (P : Over (Spec (CommRingCat.of R))) :
    thickMap R I e P ≫ pullback.fst P.hom (thick R I (e + 1)) = pullback.fst P.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem geClosed_of_statement :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (X : Scheme.{0}) [X.Over (Spec (.of R))] [IsSeparated (X ↘ Spec (.of R))]
        [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))],
        Statement I (⊥ : X.IdealSheafData)) → GEClosed := by
  intro H R _ _ I hI P hsep hlft hqc C i β hi hβ hprop
  letI : P.left.Over (Spec (.of R)) := ⟨P.hom⟩
  have hf : (P.left ↘ Spec (.of R)) = P.hom := rfl
  haveI : IsSeparated (P.left ↘ Spec (.of R)) := hsep
  haveI : LocallyOfFiniteType (P.left ↘ Spec (.of R)) := hlft
  haveI : QuasiCompact (P.left ↘ Spec (.of R)) := hqc
  have hthick : ∀ e, IsClosedImmersion (thick R I e) := isClosedImmersion_thick I
  let pr : ∀ e, (thickObj R I e P).left ⟶ P.left := fun e => pullback.fst P.hom (thick R I e)
  haveI hpr : ∀ e, IsClosedImmersion (pr e) := fun e => by
    have := hthick e
    change IsClosedImmersion (pullback.fst P.hom (thick R I e))
    infer_instance
  have hmapfst : ∀ e, thickMap R I e P ≫ pr (e + 1) = pr e := fun e => thickMap_fst I e P
  haveI hmap : ∀ e, IsClosedImmersion (thickMap R I e P) := fun e => by
    have : IsClosedImmersion (thickMap R I e P ≫ pr (e + 1)) := by
      rw [hmapfst]; exact hpr e
    exact IsClosedImmersion.of_comp_isClosedImmersion _ (pr (e + 1))
  haveI := hi
  let c : ∀ e, C e ⟶ P.left := fun e => i e ≫ pr e
  haveI hc : ∀ e, IsClosedImmersion (c e) := fun e => inferInstance
  let J : ℕ → P.left.IdealSheafData := fun e => (c e).ker
  let Q : ℕ → P.left.IdealSheafData := fun e => (pr e).ker
  have hQ : ∀ e, subOf (Q e) = powSub I (𝟙_ P.left.Modules) (e + 1) := fun e =>
    subOf_eq_powSub I (Q e) (e + 1) (fun U => ideal_ker_thick I e U)
  have hJQ : ∀ e, Q e ≤ J e := fun e => Scheme.Hom.le_ker_comp _ _
  have hsucc : ∀ e, J e = J (e + 1) ⊔ Q e := by
    intro e
    have h := ker_inter_eq_sup (pr (e + 1)) (i (e + 1)) (thickMap R I e P) (β e) (i e) (hβ e)
    rw [hmapfst] at h
    have h2 : (β e ≫ i (e + 1)) ≫ pr (e + 1) = c e := by
      rw [(hβ e).w, Category.assoc, hmapfst]
    rw [h2] at h
    exact h
  have hprop0 : IsProper ((J 0).subschemeι ≫ (P.left ↘ Spec (.of R))) := by
    let u : (J 0).subscheme ⟶ C 0 := IsClosedImmersion.lift (c 0) (J 0).subschemeι
      (by simp [J])
    let w : C 0 ⟶ (J 0).subscheme := IsClosedImmersion.lift (J 0).subschemeι (c 0)
      (by simp [J])
    have hu : u ≫ c 0 = (J 0).subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hw : w ≫ (J 0).subschemeι = c 0 := IsClosedImmersion.lift_fac _ _ _
    haveI : IsIso u := ⟨w, by rw [← cancel_mono (J 0).subschemeι, Category.assoc, hw, hu, Category.id_comp],
      by rw [← cancel_mono (c 0), Category.assoc, hu, hw, Category.id_comp]⟩
    have hthick0 := hthick 0
    have hc0 : c 0 ≫ P.hom = (i 0 ≫ (thickObj R I 0 P).hom) ≫ thick R I 0 := by
      simp only [c, pr, Category.assoc]
      rw [pullback.condition]
      rfl
    rw [hf, ← hu, Category.assoc, hc0]
    infer_instance
  obtain ⟨JB, hJB, hsup⟩ := exists_ideal_of_statement I (H R I hI P.left) J Q hQ hJQ hsucc hprop0
  let j := JB.subschemeι
  have hker : ∀ e, j.ker ≤ (c e).ker := fun e => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    change JB ≤ J e
    rw [← hsup e]
    exact le_sup_left
  let b : ∀ e, C e ⟶ JB.subscheme := fun e => IsClosedImmersion.lift j (c e) (hker e)
  have hb : ∀ e, b e ≫ j = c e := fun e => IsClosedImmersion.lift_fac _ _ _
  refine ⟨JB.subscheme, j, b, inferInstance, hJB, fun e => ?_, fun e => ?_⟩
  · haveI : IsClosedImmersion (b e ≫ j) := by rw [hb]; exact hc e
    refine GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup j (pr e) (b e) (i e) (hb e) ?_
    rw [hb, Scheme.IdealSheafData.ker_subschemeι]
    exact (hsup e).symm
  · rw [← cancel_mono j, Category.assoc, hb, hb]
    change β e ≫ i (e + 1) ≫ pr (e + 1) = i e ≫ pr e
    rw [← Category.assoc, (hβ e).w, Category.assoc, hmapfst]

end Main

end GlobalTheory.CompanionTheory.GE.Close
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geClosed_of_statement_bot : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Scheme.{0}) [X.Over (Spec (.of R))] [IsSeparated (X ↘ Spec (.of R))] [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))], Statement I (⊥ : X.IdealSheafData)) → PositivityTheory.FormalThickening.GEClosed := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.Close.geClosed_of_statement
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GroundTheory.Arith.SchemeCoh
namespace GlobalTheory.CompanionTheory.GE

theorem step_integral {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (IH : ∀ J' : X.IdealSheafData, J < J' → Statement I J') : Statement I J := by
  intro E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  letI : J.subscheme.Over (Spec (.of A)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of A))⟩
  have h1 : IsSeparated (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : IsSeparated (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h2 : LocallyOfFiniteType (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : LocallyOfFiniteType (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h3 : QuasiCompact (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : QuasiCompact (J.subschemeι ≫ (X ↘ Spec (.of A))))
  obtain ⟨N, Y, i, O, ψ, W, hi, hψ, hcomm, hW, hiso⟩ := GlobalTheory.T.exists_chow_cover_integral (A := A) (X := J.subscheme)
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩
  have hZ : Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := GlobalTheory.T.formal_existence_projective_open I hI i hi O
  have hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = ((O : Scheme.{0}) ↘ Spec (.of A)) := by
    change (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = O.ι ≫ i ≫ ProjSpace.toSpecBase A N
    rw [hcomm, Category.assoc]
    rfl
  obtain ⟨D, c, J', hDq, hDP, hc, hJ, hkill⟩ := GlobalTheory.T.formal_existence_proper_pushforward I hI J hZ ψ hψ hover W hW hiso hE hS hK hP
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP D hDq c hc
  exact halg (IH J' hJ _ (GlobalTheory.T.coherent_subobject_coherent hE D hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J' D S c' hkill) hP') hDP

theorem statement_bot {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    (X : Scheme.{0}) [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] :
    Statement I (⊥ : X.IdealSheafData) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hwf : WellFoundedGT X.IdealSheafData := GlobalTheory.T.ideal_sheaf_well_founded_gt
  refine WellFoundedGT.induction (motive := fun J : X.IdealSheafData => Statement I J) ⊥ ?_
  intro J IH
  by_cases hJ : J = ⊤
  · subst hJ
    exact GlobalTheory.T.formal_existence_top_ideal I
  rcases GlobalTheory.T.noetherian_ideal_integral_or_split J hJ with h | ⟨J₁, J₂, h₁, h₂, hm⟩
  · exact step_integral I hI J IH
  · exact GlobalTheory.T.formal_existence_product_ideal I J J₁ J₂ hm (IH _ h₁) (IH _ h₂)

theorem geClosed : GEClosed :=
  GlobalTheory.T.geClosed_of_statement_bot fun _ _ _ I hI X _ _ _ _ => statement_bot I hI X

end GlobalTheory.CompanionTheory.GE
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed : GEClosed := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.geClosed
end
