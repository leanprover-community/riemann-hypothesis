import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecomposition
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerDecompositionFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChange

section
set_option autoImplicit false

namespace GlobalTheory.FGFieldEmb

open Cardinal

theorem nonempty_ringHom_complex_of_mk_le (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem nonempty_ringHom_complex_of_fg :
    ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  intro K _ _ k hk
  obtain ⟨t, rfl⟩ := hk
  refine nonempty_ringHom_complex_of_mk_le _ ?_
  refine le_trans ?_ Cardinal.aleph0_le_continuum
  refine (IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_
  refine max_le (max_le ?_ ?_) le_rfl
  · simp [Cardinal.mkRat]
  · exact (Cardinal.lt_aleph0_of_finite _).le

end GlobalTheory.FGFieldEmb
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ringHom_complex_of_fg' : ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  atlas_forward_decl GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.AbFGSpread

theorem sym_transfer {X Y : Scheme.{0}} {L : LB X} {N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (jX : X ⟶ X)
    (jj : Y ⟶ Y) (φ : Y ⟶ X) (e : jj ≫ φ = φ ≫ jX) (hw : LBIso N (L.pull φ)) (hs : LBIso (N.pull jj) N) :
    LBIso ((L.pull jX).pull φ) (L.pull φ) := by
  have h1 : LBIso ((L.pull jX).pull φ) (L.pull (jj ≫ φ)) := by
    rw [e]; exact (FibreNef.lbIso_pull_comp hL jX φ).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull φ).pull jj) := FibreNef.lbIso_pull_comp hL φ jj
  have h3 : LBIso ((L.pull φ).pull jj) (N.pull jj) := RigidBundleGlue.LBIso.pull hw.symm jj
  have p := fun (f : Y ⟶ X) => pull_isLB hL f
  refine LBIso.trans (pull_isLB (pull_isLB hL jX) φ) (p _) (p φ) h1 ?_
  refine LBIso.trans (p _) (pull_isLB (p φ) _) (p φ) h2 ?_
  refine LBIso.trans (pull_isLB (p φ) _) (pull_isLB hN _) (p φ) h3 ?_
  exact LBIso.trans (pull_isLB hN _) hN (p φ) hs hw

theorem sym_of_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (jX : X ⟶ X) (jj : Y ⟶ Y) (φ : Y ⟶ X)
    (e : jj ≫ φ = φ ≫ jX) (hs : LBIso ((L.pull jX).pull φ) (L.pull φ)) :
    LBIso ((L.pull φ).pull jj) (L.pull φ) := by
  have p := fun {Z : Scheme.{0}} (f : Z ⟶ X) => pull_isLB hL f
  have h1 : LBIso ((L.pull φ).pull jj) (L.pull (jj ≫ φ)) := (FibreNef.lbIso_pull_comp hL φ jj).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull jX).pull φ) := by
    rw [e]; exact FibreNef.lbIso_pull_comp hL jX φ
  refine LBIso.trans (pull_isLB (p φ) _) (p _) (p φ) h1 ?_
  exact LBIso.trans (p _) (pull_isLB (p jX) _) (p φ) h2 hs

theorem spread_to_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  intro K _ _ A _ hA L M hL hM hLa hMa hLs hMs
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ A.left A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple hLa)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ L hL sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ M hM sq
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have sub : ∀ t : Finset K, t ⊆ s → (t : Set K) ⊆ K₁ := fun t ht =>
    PolCountableDescent.subset_closure_of_subset ht
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : A.left ⟶ A₁.left := sq₁.lift φ (A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, PolCountableDescent.spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (sub s₁ (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hLL⟩ := H₂ K₁ h (sub s₂ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨M₁, hM₁, hMM⟩ := H₃ K₁ h (sub s₃ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨hab₁, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ A ψ hG hA
  have : IsProper A₁.hom := hab₁.proper
  have e₁ := PolDescent.inv_left_comp hG
  have symL := sym_transfer hL₁ hL _ _ ψ e₁ hLL hLs
  have symM := sym_transfer hM₁ hM _ _ ψ e₁ hMM hMs
  obtain ⟨s₄, H₄⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ L₁ hG.1
    inferInstance inferInstance (pull_isLB hL₁ _) hL₁ symL
  obtain ⟨s₅, H₅⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ M₁ hG.1
    inferInstance inferInstance (pull_isLB hM₁ _) hM₁ symM
  let t : Finset K := s ∪ s₄ ∪ s₅
  let k₀ : IntermediateField ℚ K := IntermediateField.adjoin ℚ (t : Set K)
  let K₂ : Subfield K := k₀.toSubfield
  have mem₂ : ∀ y ∈ t, y ∈ K₂ := fun y hy => IntermediateField.subset_adjoin ℚ (t : Set K) hy
  have h₁₂ : K₁ ≤ K₂ := Subfield.closure_le.2 (fun y hy => mem₂ y (by simp [t, Finset.mem_coe.1 hy]))
  have rng : ∀ u : Finset K, u ⊆ t → (u : Set K) ⊆ Set.range K₂.subtype := fun u hu y hy =>
    ⟨⟨y, mem₂ y (hu hy)⟩, rfl⟩
  let inc₂ := spMap (Subfield.inclusion h₁₂)
  let A₂ : Over (Sp K₂) := (Over.pullback inc₂).obj A₁
  have hP : IsGrpPullback A₂ A₁ inc₂ (pullback.fst A₁.hom inc₂) := isGrpPullback_pullback A₁ inc₂
  let χ : A₂.left ⟶ A₁.left := pullback.fst A₁.hom inc₂
  let π : A.left ⟶ A₂.left := pullback.lift ψ (A.hom ≫ spMap K₂.subtype)
    (by rw [hψ₂, Category.assoc, PolCountableDescent.spMap_subtype_comp h₁₂])
  have hπ₁ : π ≫ χ = ψ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ A₂.hom = A.hom ≫ spMap K₂.subtype := pullback.lift_snd _ _ _
  have hG₂ : IsGrpPullback A A₂ (spMap K₂.subtype) π :=
    IsGrpPullback.cancel hP (by rw [PolCountableDescent.spMap_subtype_comp h₁₂, hπ₁]; exact hG) hπ₂
  obtain ⟨hab₂, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₂ K K₂.subtype A₂ A π hG₂ hA
  have e₂ := PolDescent.inv_left_comp hP
  have symL₂ := H₄ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₄ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have symM₂ := H₅ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₅ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have isoL : LBIso L ((L₁.pull χ).pull π) := by
    refine LBIso.trans hL (pull_isLB hL₁ _) (pull_isLB (pull_isLB hL₁ _) _) hLL ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hL₁ χ π
  have isoM : LBIso M ((M₁.pull χ).pull π) := by
    refine LBIso.trans hM (pull_isLB hM₁ _) (pull_isLB (pull_isLB hM₁ _) _) hMM ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hM₁ χ π
  refine ⟨k₀, A₂, inferInstance, π, L₁.pull χ, M₁.pull χ, ⟨t, rfl⟩, hab₂, hG₂, pull_isLB hL₁ _,
    pull_isLB hM₁ _, ?_, ?_, sym_of_pull hL₁ _ _ χ e₂ symL₂, sym_of_pull hM₁ _ _ χ e₂ symM₂, isoL, isoM⟩
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ L hab₂ hG₂ (pull_isLB hL₁ _) hL isoL hLa
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ M hab₂ hG₂ (pull_isLB hM₁ _) hM isoM hMa

end GlobalTheory.AbFGSpread
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_ampleBundles_descend_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  atlas_forward_decl GlobalTheory.AbFGSpread.spread_to_fg_subfield
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.FieldBaseChange

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

theorem abelian_ample_symm_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  intro k Ω _ _ σ A₀ _ hA L hL hamp hsym
  have h := isGrpPullback_pullback A₀ (spMap σ)
  refine ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h, ?_, ?_⟩
  · have := hA.proper
    exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp h.1
  · have hinv := inv_left_comp h
    have i₁ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (pullback.fst A₀.hom (spMap σ))
      (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left _ rfl
    have i₂ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (GrpObj.inv : A₀ ⟶ A₀).left
      (pullback.fst A₀.hom (spMap σ)) _ hinv.symm
    have i₃ := GlobalTheory.RigidBundleGlue.LBIso.pull hsym (pullback.fst A₀.hom (spMap σ))
    exact (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      i₁.symm i₂).trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) i₃

end GlobalTheory.FieldBaseChange
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  atlas_forward_decl GlobalTheory.FieldBaseChange.abelian_ample_symm_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [Field k] (A₀ : Over (Sp k))

theorem lbIso_lbPow_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {L : LB A₀.left} (hL : L.IsLB) (N : ℕ) :
    LBIso (lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) N)
      ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) N).pull (bcMap A₀.hom ρ)) := by
  have h₁ : LBIso (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hL _ (bcMap_fst A₀.hom ρ).symm
  have hR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow (pull_isLB hR _) N)
    (pull_isLB (isLB_lbPow hR N) _) (lbIso_lbPow h₁ N) (lbIso_lbPow_pull hR _ N)

theorem lbIso_linComb_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {M : LB A₀.left} (hM : M.IsLB) {K : Type} [Fintype K]
    (φS : K → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))))
    (φR : K → (pullback A₀.hom (spMap (algebraMap k R)) ⟶ pullback A₀.hom (spMap (algebraMap k R))))
    (ε : K → ℤ) (hφ : ∀ o, φS o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ φR o) :
    LBIso (LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) φS ε)
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) φR ε).pull (bcMap A₀.hom ρ)) := by
  have hR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have h₁ : LBIso (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hM _ (bcMap_fst A₀.hom ρ).symm
  exact LBIso.trans (LB.isLB_linComb (pull_isLB hM _) _ _) (LB.isLB_linComb (pull_isLB hR _) _ _)
    (pull_isLB (LB.isLB_linComb hR _ _) _) (PelPrim.lbIso_linComb h₁ φS ε)
    (SymExtend.lbIso_linComb_pull hR (bcMap A₀.hom ρ) φS φR ε (bcMap A₀.hom ρ) hφ)

theorem comm_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    (f : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)
    (g : (Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀)
    (h : bcMap A₀.hom ρ ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ g.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, Category.assoc, h]
  · have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
    have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
    rw [Category.assoc, bcMap_snd, ← Category.assoc, hf, Category.assoc, hg, bcMap_snd]

def fam {S : Type} [CommRing S] [Algebra k S] {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)) :
    Option (Fin r) → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))) :=
  fun o => o.elim (𝟙 _) fun i => (β i).left

theorem fam_comm {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀))
    (gam : Fin r → ((Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀))
    (h : ∀ i, bcMap A₀.hom ρ ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _) (o : Option (Fin r)) :
    fam A₀ β o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ fam A₀ gam o := by
  cases o with
  | none => simp [fam]
  | some i => exact comm_bc A₀ ρ (β i) (gam i) (h i)

end GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent GlobalTheory.SqDecSpread in

theorem GlobalTheory.SqDecSpread.sqDec_fg : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀],
    IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω))))
      (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) →
    ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀)
      (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  intro k Ω _ _ _ A₀ _ hA L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have := hA.proper
  have := hA.smooth
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  choose Ri g hRi hg hgeq using fun i => haveI := hβ i; exists_fg_isMonHom (A := A₀) (A' := A₀) (β i)
  let R₁ : Subalgebra k Ω := ⨆ i, Ri i
  have hR₁ : R₁.FG := fg_iSup hRi
  choose gam hgam hgameq using fun i => haveI := hg i; exists_specialise (g i) (Subalgebra.inclusion (le_iSup Ri i))
  have key₁ : ∀ i, bcMap A₀.hom R₁.val ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _ := by
    intro i
    rw [hgameq i, ← Category.assoc, bcMap_comp_of_eq A₀.hom (Subalgebra.inclusion (le_iSup Ri i)) R₁.val (Ri i).val
      (fun _ => rfl), hgeq i]
  have hL₁ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hM₁ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hLΩ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have hMΩ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have H₁ : LBIso ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) N).pull (baseChangeMap A₀.hom R₁.val))
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) (fam A₀ gam) ε).pull
        (baseChangeMap A₀.hom R₁.val)) :=
    LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (isLB_lbPow hLΩ N) (pull_isLB (LB.isLB_linComb hM₁ _ _) _)
      (lbIso_lbPow_bc A₀ R₁.val hL N).symm
      (LBIso.trans (isLB_lbPow hLΩ N) (LB.isLB_linComb hMΩ _ _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) H
        (lbIso_linComb_bc A₀ R₁.val hM (fam A₀ β) (fam A₀ gam) ε (fam_comm A₀ R₁.val β gam key₁)))
  obtain ⟨R, hR, hRfg, H₂⟩ := exists_fg_lbIso A₀.hom hR₁ _ _ (isLB_lbPow hL₁ N) (LB.isLB_linComb hM₁ _ _) H₁
  choose δ hδ hδeq using fun i => haveI := hgam i; exists_specialise (gam i) (Subalgebra.inclusion hR)
  have hLR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have hMR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  refine ⟨R, hRfg, N, a₀, r, a, δ, hN, ha₀, hδ, ?_⟩
  exact LBIso.trans (isLB_lbPow hLR N) (pull_isLB (isLB_lbPow hL₁ N) _) (LB.isLB_linComb hMR _ _)
    (lbIso_lbPow_bc A₀ (Subalgebra.inclusion hR) hL N)
    (LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) (LB.isLB_linComb hMR _ _) H₂
      (lbIso_linComb_bc A₀ (Subalgebra.inclusion hR) hM (fam A₀ δ) (fam A₀ gam) ε
        (fam_comm A₀ (Subalgebra.inclusion hR) δ gam fun i => (hδeq i).symm)).symm)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) → ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  atlas_forward_decl GlobalTheory.SqDecSpread.sqDec_fg
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecBC

theorem sqDec_baseChange : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  intro k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc
  have hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀,
      IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left := by
    intro i
    haveI := hβ i
    obtain ⟨g, hg, e⟩ := GlobalTheory.HomDescent.exists_specialise (β i) ρ
    refine ⟨g, hg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]
    · have w₁ := Over.w g
      have w₂ := Over.w (β i)
      simp only [Over.pullback_obj_hom] at w₁ w₂
      rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]
  choose g hgm hgc using hg'
  refine ⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩
  set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR
  set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS
  have efS : fS = bc ≫ fR := (GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm
  have pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f) :=
    fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
  have i1 := lbIso_lbPow_pull hL fS N
  have i2 := GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS
  have i3 := pullIso (lbIso_lbPow_pull hL fR N).symm bc
  have i4 := pullIso H bc
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left) := by
    intro o
    cases o with
    | none => simp
    | some i => exact hgc i
  have i5 := (GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm
  have i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)))
      (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by
    obtain ⟨w, hw⟩ := (GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm
    exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩
  have j1 := i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _)
    (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2
  have j2 := j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _)
    (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3
  have j3 := j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4
  have j4 := j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _)
    (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5
  exact j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _)
    (LB.isLB_linComb (pull_isLB hM _) _ _) i6

end GlobalTheory.SqDecBC
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_baseChange_algebraMap : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  atlas_forward_decl GlobalTheory.SqDecBC.sqDec_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem exists_algHom_finite (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG) :
    ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), Nonempty (R →ₐ[k] k₁) := by
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, inferInstance, ⟨Ideal.Quotient.mkₐ k m⟩⟩

theorem main : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  intro k Ω _ _ σ A₀ _ hA L M hL hM h
  letI := σ.toAlgebra
  obtain ⟨R, hR, hRd⟩ := GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated k Ω A₀ hA L M hL hM h
  obtain ⟨k₁, _, _, _, ⟨ρ⟩⟩ := exists_algHom_finite k Ω R hR
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, GlobalTheory.T.squareDecomposition_baseChange_algebraMap k R k₁ ρ A₀ L M hL hM hRd⟩

end GlobalTheory.SqDecFinite
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_descends_to_finiteExtension : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  atlas_forward_decl GlobalTheory.SqDecFinite.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_ext_compat_of_finite :
    ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  intro k K k₁ _ _ _ _ _ _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] k₁)
  letI : Field ((K ⊗[k] k₁) ⧸ m) := Ideal.Quotient.field m
  have hfin : FiniteDimensional K ((K ⊗[k] k₁) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  refine ⟨(K ⊗[k] k₁) ⧸ m, inferInstance, inferInstance, hfin,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : k₁ →ₐ[k] K ⊗[k] k₁).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [IsScalarTower.algebraMap_apply K (K ⊗[k] k₁) ((K ⊗[k] k₁) ⧸ m),
    Algebra.TensorProduct.algebraMap_apply]
  congr 1
  rw [← Algebra.TensorProduct.algebraMap_apply', ← Algebra.TensorProduct.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply k K (K ⊗[k] k₁) a

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_compatible_embedding : ∀ (k K k₁ : Type) [Field k] [Field K] [Field k₁] [Algebra k K] [Algebra k k₁] [FiniteDimensional k k₁], ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (e : k₁ →+* K'), e.comp (algebraMap k k₁) = (algebraMap K K').comp (algebraMap k K) := by
  atlas_forward_decl GlobalTheory.exists_finite_ext_compat_of_finite
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_power_decomposition_field_extension : ∀ (k K k₁ K' : Type) [Field k] [Field K] [Field k₁] [Field K'] (a : k →+* K) (b : k →+* k₁) (c : K →+* K') (d : k₁ →+* K'), c.comp a = d.comp b → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp K)) [GrpObj A] (π : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap a) π → ∀ (L₀ M₀ : LB A₀.left) (L M : LB A.left), L₀.IsLB → M₀.IsLB → L.IsLB → M.IsLB → LBIso L (L₀.pull π) → LBIso M (M₀.pull π) → SqDec ((Over.pullback (spMap b)).obj A₀) (L₀.pull (pullback.fst A₀.hom (spMap b))) (M₀.pull (pullback.fst A₀.hom (spMap b))) → SqDec ((Over.pullback (spMap c)).obj A) (L.pull (pullback.fst A.hom (spMap c))) (M.pull (pullback.fst A.hom (spMap c))) := by
  first | exact @GlobalTheory.SqDecTransport.transport | exact GlobalTheory.SqDecTransport.transport | (intros; apply GlobalTheory.SqDecTransport.transport <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem sqDec_of_finite_extension : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K _ _ A _ hA L M hL hM aL aM sL sM
  obtain ⟨k₀, A₀, _, π, L₀, M₀, hfg, hA₀, hπ, hL₀, hM₀, aL₀, aM₀, sL₀, sM₀, eL, eM⟩ :=
    GlobalTheory.T.abelianVariety_ampleBundles_descend_fg_subfield K A hA L M hL hM aL aM sL sM
  obtain ⟨σ⟩ := GlobalTheory.T.nonempty_ringHom_complex_of_fg' K k₀ hfg
  obtain ⟨hC, aLC, sLC⟩ := GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange k₀ ℂ σ A₀ hA₀ L₀ hL₀ aL₀ sL₀
  obtain ⟨-, aMC, sMC⟩ := GlobalTheory.T.abelian_ample_symm_preserved_field_baseChange k₀ ℂ σ A₀ hA₀ M₀ hM₀ aM₀ sM₀
  have hsq := GlobalTheory.T.complex_symmetricAmple_square_decomposition ((Over.pullback (spMap σ)).obj A₀) hC _ _ (pull_isLB hL₀ _) (pull_isLB hM₀ _) aLC aMC sLC sMC
  obtain ⟨k₁, _, _, _, hsq₁⟩ := GlobalTheory.T.squareDecomposition_descends_to_finiteExtension k₀ ℂ σ A₀ hA₀ L₀ M₀ hL₀ hM₀ hsq
  obtain ⟨K', _, _, _, e, he⟩ := GlobalTheory.T.exists_finite_extension_compatible_embedding k₀ K k₁
  exact ⟨K', inferInstance, inferInstance, inferInstance,
    GlobalTheory.T.transport_power_decomposition_field_extension k₀ K k₁ K' (algebraMap k₀ K) (algebraMap k₀ k₁) (algebraMap K K') e he.symm A₀ A π hπ L₀ M₀ L M hL₀ hM₀ hL hM eL eM hsq₁⟩

end GlobalTheory.SqDecFinite
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), SqDec ((Over.pullback (spMap (algebraMap K K'))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap K K')))) (M.pull (pullback.fst A.hom (spMap (algebraMap K K')))) := by
  atlas_forward_decl GlobalTheory.SqDecFinite.sqDec_of_finite_extension
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.LocExt

theorem exists_finite_normal_cover_of_finiteDimensional : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  intro R _ _ _ _ hcomp K' _ _ _
  have hnorm : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hCN : IsCN R := ⟨inferInstance, hnorm, hcomp, inferInstance⟩
  let K := FractionRing R
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K K' := inferInstance
  let C := integralClosure R K'
  haveI hCf : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRC : Function.Injective (algebraMap R C) := fun x y h => hRK' (congrArg Subtype.val h)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρ, hρf, -, hσρ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) hCN hRC
      (RingHom.finite_algebraMap.2 hCf)
  obtain ⟨hnoeth', hnorm', -, -⟩ := hCN'
  letI : Algebra C R' := σ.toAlgebra
  letI : Algebra R R' := ρ.toAlgebra
  haveI : IsScalarTower R C R' := IsScalarTower.of_algebraMap_eq (fun r => (RingHom.congr_fun hσρ r).symm)
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R)
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro h
        apply hρ
        rw [map_zero, ← h]
        exact (RingHom.congr_fun hσρ r).symm
      · rintro rfl; simp
    have : c ∈ RingHom.ker σ := hc
    rw [hker] at this
    exact this
  have hσ' : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσ
  let τ : K' →+* FractionRing R' := IsFractionRing.lift (A := C) hσ'
  refine ⟨R', inferInstance, inferInstance, hnoeth', hnorm', inferInstance, ρ, τ, hρ, hρf, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  have h1 : algebraMap K K' (algebraMap R K r) = algebraMap C K' (algebraMap R C r) := rfl
  rw [h1]
  simp only [τ, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  rw [← RingHom.comp_apply σ, hσρ]

end GlobalTheory.LocExt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normal_noetherian_cover_fractionFieldExt : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  atlas_forward_decl GlobalTheory.LocExt.exists_finite_normal_cover_of_finiteDimensional
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.GenFibreBaseChange

theorem genFibre_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  intro R R' _ _ _ _ ρ a ha G _
  have hsq : jK R' ≫ spMap ρ = spMap a ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]
  have hw : (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
      Category.assoc]
  let π₀ : pullback (pullback.snd G.hom (spMap ρ)) (jK R') ⟶ pullback G.hom (jK R) := pullback.lift _ _ hw
  have e₁ : π₀ ≫ pullback.fst G.hom (jK R) =
      pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have e₂ : π₀ ≫ pullback.snd G.hom (jK R) = pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a :=
    pullback.lift_snd _ _ _
  refine ⟨π₀, ?_, fun L hL => ?_⟩
  · have n := (isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))
    rw [hsq] at n
    have n' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G (spMap a ≫ jK R)
        (π₀ ≫ pullback.fst G.hom (jK R)) := by
      rw [e₁]; exact n
    exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n' e₂
  · have h₁ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (spMap ρ))
      (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R')) rfl
    have h₂ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R)) π₀ e₁.symm
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      (LBIso.symm h₁) h₂

end GlobalTheory.GenFibreBaseChange
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_baseChange_grpPullback_domains : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  atlas_forward_decl GlobalTheory.GenFibreBaseChange.genFibre_pull
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecIdBC

theorem sqDec_of_baseChange_id : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  intro F _ A _ L M hL hM hD
  have hid : spMap (RingHom.id F) = 𝟙 (Sp F) := by
    simp [spMap]
  have hw : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id F) := by rw [hid]; simp
  let π' : A.left ⟶ pullback A.hom (spMap (RingHom.id F)) := pullback.lift (𝟙 _) A.hom hw
  have e₁ : π' ≫ pullback.fst A.hom (spMap (RingHom.id F)) = 𝟙 _ := pullback.lift_fst _ _ _
  have e₂ : π' ≫ ((Over.pullback (spMap (RingHom.id F))).obj A).hom = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact pullback.lift_snd _ _ _
  have hP : IsGrpPullback A ((Over.pullback (spMap (RingHom.id F))).obj A) (𝟙 _) π' := by
    have n : IsGrpPullback A A (𝟙 _ ≫ spMap (RingHom.id F)) (π' ≫ pullback.fst A.hom (spMap (RingHom.id F))) := by
      rw [e₁, Category.id_comp, hid]; exact GlobalTheory.SiegLower.isGrpPullback_id A
    exact IsGrpPullback.cancel (isGrpPullback_pullback A _) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ g : A ⟶ A, IsMonHom g ∧ g.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso L ((L.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hL (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (GlobalTheory.SiegLower.lbIso_pull_id hL)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hL) _ _ _ π' (fun _ => by rw [e₁]; simp))
  have iM : LBIso M ((M.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hM (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (GlobalTheory.SiegLower.lbIso_pull_id hM)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hM) _ _ _ π' (fun _ => by rw [e₁]; simp))
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow L N) ((lbPow (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb M (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow hL N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecIdBC
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_of_baseChange_along_identity : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  atlas_forward_decl GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R'))) (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  first | exact @GlobalTheory.GenericDec.sqDec_of_generic | exact GlobalTheory.GenericDec.sqDec_of_generic | (intros; apply GlobalTheory.GenericDec.sqDec_of_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_baseChange : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  first | exact @GlobalTheory.SymBaseChange.symm_pull | exact GlobalTheory.SymBaseChange.symm_pull | (intros; apply GlobalTheory.SymBaseChange.symm_pull <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.CoverDec

theorem exists_cover_sqDec : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  intro R _ _ _ _ hc G _ hG hAb L M hL hM hAL hAM hSL hSM
  have sL := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) L hL hSL
  have sM := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) M hM hSM
  obtain ⟨K', _, _, _, hD⟩ := GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle (FractionRing R) ((Over.pullback (jK R)).obj G) hAb _ _
    (pull_isLB hL _) (pull_isLB hM _) hAL hAM sL sM
  obtain ⟨R', _, _, _, _, _, ρ, τ, hinj, hfin, hcomp⟩ := GlobalTheory.T.exists_finite_normal_noetherian_cover_fractionFieldExt R hc K'
  obtain ⟨π₀, hP, hLL⟩ := GlobalTheory.T.genericFibre_baseChange_grpPullback_domains R R' ρ (τ.comp (algebraMap (FractionRing R) K')) hcomp G
  have hD' := GlobalTheory.SqDecTransport.transport (FractionRing R) (FractionRing R') K' (FractionRing R')
    (τ.comp (algebraMap (FractionRing R) K')) (algebraMap (FractionRing R) K') (RingHom.id _) τ rfl
    ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) π₀ hP _ _ _ _
    (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (hLL L hL) (hLL M hM) hD
  have h1 := GlobalTheory.T.squareDecomposition_of_baseChange_along_identity _ _ _ _ (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) hD'
  have h2 := GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian R' ((Over.pullback (spMap ρ)).obj G) (IsSemiAbelian.pullback (spMap ρ) G hG) _ _
    (pull_isLB hL _) (pull_isLB hM _) h1
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    (Over.pullback (spMap ρ)).obj G, inferInstance, pullback.fst G.hom (spMap ρ), hinj, hfin,
    isGrpPullback_pullback G (spMap ρ), h2⟩

end GlobalTheory.CoverDec
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteNormalCover_symmBundle_power_decomposition : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  atlas_forward_decl GlobalTheory.CoverDec.exists_cover_sqDec
end
