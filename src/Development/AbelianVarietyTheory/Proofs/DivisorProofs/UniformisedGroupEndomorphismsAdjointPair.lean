import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDat
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X), (∀ b b', FormalEnd U.toUnifPre a h' b → FormalEnd U.toUnifPre a h' b' → b = b') ∧ ∀ b b' : G ⟶ G, (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → b = b' := by
  first | exact @GlobalTheory.MumUniq.main | exact GlobalTheory.MumUniq.main | (intros; apply GlobalTheory.MumUniq.main <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SelfDualSpread

section General

variable {S S' : Scheme.{0}}

theorem pull_evc_gen {A B : Over S} {A' B' : Over S'} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ f) (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ g)
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hQ' : (Q.pull m').IsLB)
    (a b : A ⊗ A ⟶ A) (a' b' : A' ⊗ A' ⟶ A') (y : A ⟶ B) (y' : A' ⟶ B')
    (ha : m ≫ a.left = a'.left ≫ f) (hb : m ≫ b.left = b'.left ≫ f) (ey : f ≫ y.left = y'.left ≫ g) :
    CechPic.pull m (evc hQ a (b ≫ y)) = evc hQ' a' (b' ≫ y') := by
  rw [evc, evc, CechPic.cls_pull hQ, ← CechPic.pull_comp, ← CechPic.pull_comp]
  congr 2
  apply left_ext
  · rw [Category.assoc, Category.assoc, lift_left_fst, m₁, lift_left_fst_assoc, ha]
  · rw [Category.assoc, Category.assoc, lift_left_snd, m₂, lift_left_snd_assoc, Over.comp_left, Over.comp_left,
      ← Category.assoc, hb, Category.assoc, Category.assoc, ey]

end General

theorem exists_generic_iso (hD : GlobalTheory.Published.DualAbelianScheme) {K : Type} [Field K] (Q : Out.PolAV (Sp K))
    (hΛ : (abelian₂ Q.A Q.L).IsLB) {D : Over (Sp K)} [GrpObj D] {R : LB (Q.A ⊗ D).left} (hR : IsDual Q.A D R)
    (hR' : IsAdditive (swap R)) :
    ∃ x : Q.A ⟶ D, IsMonHom x ∧ IsIso x ∧ CechPic.cls (abelian₂ Q.A Q.L) hΛ = evc hR.isLB (fst Q.A Q.A) (snd Q.A Q.A ≫ x) := by
  have := Q.isAb.comm
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := PerfectDual.isDual_of_isPerfect hD Q.A Q.A Q.isAb Q.isAb Q.smoothDim
    Q.smoothDim (isPerfect_lam Q.isLB Q.ktriv)
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 fun Y a b b' ↦ by
    rw [e, e, e, CechPic.lam_comm, CechPic.lam_comm _ a b, CechPic.lam_comm _ a b', ← e, ← e, ← e]
    exact (isAdditive_iff hΛ).1 hd.additive _ _ _ _
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hR hR' hΛ hd.additive a₂
  exact ⟨x, hx, hd.isIso_of_cls hR ex, ex⟩

section Generic

variable {S : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {K : Type} [Field K] {η : Sp K ⟶ S}
  {A B : Over S} [GrpObj A] [GrpObj B] {A' B' : Over (Sp K)} [GrpObj A'] [GrpObj B'] {φ : A'.left ⟶ A.left}
  {ψ : B'.left ⟶ B.left}

omit [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] in

theorem exists_res (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) (y : A ⟶ B) :
    ∃ y' : A' ⟶ B', φ ≫ y.left = y'.left ≫ ψ :=
  ⟨Over.homMk (hψ.1.lift (φ ≫ y.left) A'.hom (by rw [Category.assoc, Over.w y, hφ.1.w])) (hψ.1.lift_snd _ _ _),
    (hψ.1.lift_fst _ _ _).symm⟩

theorem lbIso_of_generic (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hη : IsGenericPointHom η)
    (hφ : IsGrpPullback A' A η φ) (hψ : IsGrpPullback B' B η ψ) {R : LB (A ⊗ B).left} (hR : IsDual A B R)
    {m' : (A' ⊗ B').left ⟶ (A ⊗ B).left} (m₁ : m' ≫ (fst A B).left = (fst A' B').left ≫ φ)
    (m₂ : m' ≫ (snd A B).left = (snd A' B').left ≫ ψ) (hR' : IsDual A' B' (R.pull m'))
    {m : (A' ⊗ A').left ⟶ (A ⊗ A).left} (l₁ : m ≫ (fst A A).left = (fst A' A').left ≫ φ)
    (l₂ : m ≫ (snd A A).left = (snd A' A').left ≫ φ) {M₁ M₂ : LB (A ⊗ A).left} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (a₁ : IsAdditive M₁) (a₂ : IsAdditive M₂)
    (e : CechPic.pull m (CechPic.cls M₁ h₁) = CechPic.pull m (CechPic.cls M₂ h₂)) : LBIso M₁ M₂ := by
  obtain ⟨y₁, hy₁, -⟩ := hR.univ A M₁ h₁ a₁
  obtain ⟨y₂, hy₂, -⟩ := hR.univ A M₂ h₂ a₂
  have c₁ : CechPic.cls M₁ h₁ = evc hR.isLB (fst A A) (snd A A ≫ y₁) :=
    (CechPic.cls_eq_iff h₁ (pull_isLB hR.isLB _)).2 hy₁
  have c₂ : CechPic.cls M₂ h₂ = evc hR.isLB (fst A A) (snd A A ≫ y₂) :=
    (CechPic.cls_eq_iff h₂ (pull_isLB hR.isLB _)).2 hy₂
  obtain ⟨y₁', e₁⟩ := exists_res hφ hψ y₁
  obtain ⟨y₂', e₂⟩ := exists_res hφ hψ y₂
  have k := fun (y : A ⟶ B) (y' : A' ⟶ B') (ey : φ ≫ y.left = y'.left ≫ ψ) ↦
    pull_evc_gen m₁ m₂ hR.isLB hR'.isLB (fst A A) (snd A A) (fst A' A') (snd A' A') y y' l₁ l₂ ey
  have e' : y₁' = y₂' := BirigidLift.dual_ext hR' (by rw [← k _ _ e₁, ← k _ _ e₂, ← c₁, ← c₂, e])
  obtain ⟨_, _⟩ := hη.quasiCompact_and_dominant
  have := hA.smooth
  have := hB.proper
  have ey : y₁ = y₂ := ExtUnique.over_hom_ext_of_isPullback hφ.1 (by rw [e₁, e₂, e'])
  subst ey
  exact (CechPic.cls_eq_iff h₁ h₂).1 (c₁.trans c₂.symm)

end Generic

theorem exists_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.SemiAbelianHomExtension → ∀ (O : Type) [CommRing O] (c : O →+* O)
    (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (K : Type) [Field K] (η : Sp K ⟶ S), GlobalTheory.IsGenericPointHom η →
    ∀ (A : Over S) [GrpObj A] (i : OAct O A), IsAbelianScheme A →
    ∀ (Q : Out.PolAV (Sp K)) (j : OAct O Q.A) (φ : Q.A.left ⟶ A.left), GlobalTheory.CurveRootGeometry.IsActPull j i η φ →
      GlobalTheory.CurveRootGeometry.IsRosati c Q j →
    ∃ P : LB (A ⊗ A).left, IsSelfDual c i P ∧ ∀ m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left,
      m ≫ (fst A A).left = (fst Q.A Q.A).left ≫ φ → m ≫ (snd A A).left = (snd Q.A Q.A).left ≫ φ →
      LBIso (P.pull m) (abelian₂ Q.A Q.L) := by
  intro hD hE O _ c S _ _ hS K _ η hη A _ i hA Q j φ hact hros
  obtain ⟨hφ, hj⟩ := hact
  have := Q.isAb.comm
  obtain ⟨B, _, R, hB, -, hR, hRs⟩ := hD S A hA
  have hψ := isGrpPullback_pullback B η
  obtain ⟨m', m₁, m₂⟩ := exists_prod_pullback hφ hψ
  have hR' : (R.pull m').IsLB := pull_isLB hR.isLB m'
  have dR' := hR.baseChange hφ hψ m₁ m₂ hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
  have aR' := (BirigidLift.additive_pull hφ hψ m₁ m₂ hR.isLB hR' ((CechPic.cls_eq_iff hR' hR').1 rfl)
    hR.additive hRs.additive).2
  have hΛ : (abelian₂ Q.A Q.L).IsLB := (isPerfect_lam Q.isLB Q.ktriv).isLB
  obtain ⟨x, hx, ix, ex⟩ := exists_generic_iso hD Q hΛ dR' aR'
  have : IsMonHom (asIso x).hom := hx
  obtain ⟨E, ⟨hE₁, hE₂⟩, -⟩ := hE.generic_existsUnique_iso_of_isGrpPullback hS hη
    (isSemiAbelian_of_isAbelianScheme A hA) (isSemiAbelian_of_isAbelianScheme B hB) hφ hψ (asIso x)
  replace hE₂ : φ ≫ E.hom.left = x.left ≫ pullback.fst B.hom η := hE₂.symm
  have hP : (ev R (fst A A) (snd A A ≫ E.hom)).IsLB := pull_isLB hR.isLB _
  obtain ⟨a₁, a₂⟩ := BirigidLift.additive_ev hR.isLB hR.additive hRs.additive E.hom
  have eΛ : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = CechPic.lam (CechPic.cls Q.L Q.isLB) a b :=
    fun Y a b ↦ by
      rw [evc, show CechPic.cls _ hΛ = CechPic.lam (CechPic.cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
        CechPic.cls_cube_two Q.isLB _ _ hΛ, CechPic.pull_lam, lift_fst, lift_snd]

  have key : ∀ (m : (Q.A ⊗ Q.A).left ⟶ (A ⊗ A).left) (a b : A ⊗ A ⟶ A) (a' b' : Q.A ⊗ Q.A ⟶ Q.A),
      m ≫ a.left = a'.left ≫ φ → m ≫ b.left = b'.left ≫ φ →
      CechPic.pull m (evc hP a b) = CechPic.lam (CechPic.cls Q.L Q.isLB) a' b' := fun m a b a' b' ha hb ↦ by
    rw [BirigidLift.evc_of_cls hR.isLB hP rfl, pull_evc_gen m₁ m₂ hR.isLB hR' a b a' b' E.hom x ha hb hE₂, ← eΛ,
      BirigidLift.evc_of_cls hR' hΛ ex]
  have c₀ : CechPic.cls _ hP = evc hP (fst A A) (snd A A) := by
    rw [evc, lift_fst_snd, Over.id_left, CechPic.pull_id]
  obtain ⟨m, l₁, l₂⟩ := exists_prod_pullback hφ hφ
  refine ⟨ev R (fst A A) (snd A A ≫ E.hom), ⟨isDual_of_iso S A A B _ R hR hP E.hom inferInstance hE₁
    ((CechPic.cls_eq_iff hP hP).1 rfl), ?_, fun a ↦ ?_⟩, fun n n₁ n₂ ↦ ?_⟩
  · refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ (pull_isLB hP _) hP a₂ a₁ ?_
    rw [c₀, cls_ev hP, key m _ _ _ _ l₂ l₁, key m _ _ _ _ l₁ l₂, CechPic.lam_comm]
  · have := i.hom a
    have hM₁ := pull_isLB hP (lift (fst A A ≫ i.act a) (snd A A)).left
    have hM₂ := pull_isLB hP (lift (fst A A) (snd A A ≫ i.act (c a))).left
    refine lbIso_of_generic hA hB hη hφ hψ hR m₁ m₂ dR' l₁ l₂ hM₁ hM₂
      ((isAdditive_iff hM₁).2 fun Y u u' t ↦ ?_) ((isAdditive_iff hM₂).2 fun Y u u' t ↦ ?_) ?_
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [evc_ev hP, evc_ev hP, evc_ev hP]
      simp only [lift_snd_assoc, lift_fst]
      exact (isAdditive_iff hP).1 a₁ _ _ _ _
    · rw [cls_ev hP, cls_ev hP, key m _ _ (fst Q.A Q.A ≫ j.act a) _ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₁, Category.assoc, Category.assoc, hj]) l₂,
        key m _ _ _ (snd Q.A Q.A ≫ j.act (c a)) l₁ (by
          rw [Over.comp_left, Over.comp_left, ← Category.assoc, l₂, Category.assoc, Category.assoc, hj])]
      exact EndOnTorsion.lam_rosati Q (hros a) _ _
  · refine (CechPic.cls_eq_iff (pull_isLB hP n) hΛ).1 ?_
    rw [CechPic.cls_pull hP, c₀, key n _ _ _ _ n₁ n₂]
    exact (CechPic.cls_cube_two Q.isLB _ _ hΛ).symm

end GlobalTheory.SelfDualSpread
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GroupAdjoint

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem exists_adjoint {K : Type} [CommRing K] (Q : PolAV (Sp K)) (f : Q.A ⟶ Q.A) [IsMonHom f] :
    ∃ x : Q.A ⟶ Q.A, IsMonHom x ∧ ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A),
      lam (cls Q.L Q.isLB) (a ≫ f) b = lam (cls Q.L Q.isLB) a (b ≫ x) := by
  have := Q.isAb.comm
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := CompanionTheory.PfDual.kTrivDual K Q.A Q.g Q.isAb Q.smoothDim Q.L Q.isLB Q.ktriv
  have hΛ : (abelian₂ Q.A Q.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = lam (cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show cls _ hΛ = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      cls_cube_two Q.isLB _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp K)) (a a' b : Y ⟶ Q.A), evc hΛ (a * a') b = evc hΛ a b + evc hΛ a' b :=
    (isAdditive_iff hΛ).1 hd.additive
  have l₂ : ∀ (Y : Over (Sp K)) (a b b' : Y ⟶ Q.A), evc hΛ a (b * b') = evc hΛ a b + evc hΛ a b' := fun Y a b b' ↦ by
    rw [e, e, e, lam_comm, lam_comm _ a b, lam_comm _ a b', ← e, ← e, ← e]
    exact l₁ _ _ _ _
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 l₂
  have hM := pull_isLB hΛ (lift (fst Q.A Q.A ≫ f) (snd Q.A Q.A)).left
  have m : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hM a b = evc hΛ (a ≫ f) b := fun Y a b ↦ by
    rw [evc_ev hΛ]
    simp only [lift_fst_assoc, lift_snd]
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hd a₂ hM
    ((isAdditive_iff hM).2 fun Y u u' t ↦ by rw [m, m, m, MonObj.mul_comp, l₁])
    ((BirigidLift.isAdditive_swap_iff hM).2 fun Y u t t' ↦ by rw [m, m, m, l₂])
  refine ⟨x, hx, fun Y a b ↦ ?_⟩
  rw [← e, ← e, ← m]
  exact BirigidLift.evc_of_cls hd.isLB hM ex a b

theorem exists_adjoint_on_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U g hg
  have hN : IsNoetherianRing R := hR.1.1
  have hI : IsIntegrallyClosed R := hR.1.2.2.1
  have := U.gen_hom
  have hL := U.LG.isLB
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨x, hx, ex⟩ := exists_adjoint A (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (jK R) := .fractionField R (FractionRing R)
  obtain ⟨g', ⟨hg', eg'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) hj hG hG (U.gen.hom ≫ x ≫ U.gen.inv)
  refine ⟨g', hg', ?_⟩
  have := hG.smooth
  have := hG.geomConnected
  have := GlobalTheory.smooth_tensorObj_hom G G
  have := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  have h₁ : (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  refine GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G ⊗ G) (1 : 𝟙_ _ ⟶ G ⊗ G).left (Over.w _) _ _ h₁ h₂ ?_
  refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_

  have ec : pull U.gen.hom.left (cls A.L A.isLB) = pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) := by
    rw [← cls_pull A.isLB _ (pull_isLB A.isLB _), ← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 U.ext
  have key : ∀ a b : G ⊗ G ⟶ G, pull (pullback.fst (G ⊗ G).hom (jK R)) (lam (cls U.LG.L hL) a b) =
      lam (cls A.L A.isLB) ((Over.pullback (jK R)).map a ≫ U.gen.hom) ((Over.pullback (jK R)).map b ≫ U.gen.hom) := by
    intro a b
    rw [← lam_pull, ec, lam_pull_of_isGrpPullback hp]
    refine GlobalTheory.CompanionTheory.DualScheme.pull_lam_of_left (T' := Over.mk (_ ≫ jK R)) _ _ ?_ ?_
    · exact (ExtUnique.pullback_map_left_fst (jK R) a).symm
    · exact (ExtUnique.pullback_map_left_fst (jK R) b).symm
  rw [cls_pull h₁, cls_pull h₂, cls_cube_two hL, cls_cube_two hL, key, key, Functor.map_comp, Functor.map_comp, eg']
  have := ex _ ((Over.pullback (jK R)).map (fst G G) ≫ U.gen.hom) ((Over.pullback (jK R)).map (snd G G) ≫ U.gen.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using this

end GlobalTheory.Mum.GroupAdjoint
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  atlas_forward_decl GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq

open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in

theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdjoint_unique_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  atlas_forward_decl GlobalTheory.Mum.rosatiAdj_unique
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  atlas_forward_decl GlobalTheory.Mum.KeepsIota.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := GlobalTheory.T.rosatiAdjoint_unique_degenerationData

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  atlas_forward_decl GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem linEnd_adjoint_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE g g' hg hg'
  obtain ⟨g₁, hg₁, hiso⟩ := GlobalTheory.T.exists_adjoint_endomorphism_uniformised_group R hR D A G hG U g hg.1
  have h₁ : LinEnd U.toUnifPre a' h g₁ := GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint R hR D A G hG U a a' h h' hE g g₁ hg hg₁ hiso
  have hu := GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData R hR.1 D A G hG U a' h
  have heq : g₁ = g' := hu.2 g₁ g' fun e => congrFun (hu.1 _ _ h₁.2 hg'.2) e
  subst heq
  exact hiso

end GlobalTheory.Mum
end
