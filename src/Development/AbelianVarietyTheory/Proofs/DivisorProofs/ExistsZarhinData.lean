import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.DualHomSurj

theorem surjective_of_ker_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hd0 hk
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have hLQF : LocallyQuasiFinite la.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := GlobalTheory.HomExt.finite_torsion_points hSA t hd0
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hk _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  haveI : IsMonHom la := hla
  refine GlobalTheory.AbLaw.MulN.surjective_of_geomFibres la fun K _ _ s => ?_
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (Q.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (Q.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := GlobalTheory.DualTower.dim_eq_of_isDual Ak Bk (Q.pull h) hd'
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (GlobalTheory.IsogenyQuasiInverse.flat_surjective_of_field _ _ gA hA' hB' hgA (hdim ▸ hgB) _).2

end GlobalTheory.DualHomSurj
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualHomFlat

theorem geomFibre_flat (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (la : A ⟶ B) [IsMonHom la] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hd : IsDual A B P)
    [LocallyQuasiFinite la.left] (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) :
    Flat ((Over.pullback s).map la).left := by
  letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'
  subst hdim
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1

end GlobalTheory.DualHomFlat

namespace GlobalTheory.DualHomFlat

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left)
    (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q →
    IsDual B A (swap Q) → IsMonHom la → 0 < d →
    (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hdpos hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite la.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hdpos
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  have h1 : IsProper (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper la.left := IsProper.of_comp _ B.hom
  have hf : IsFinite la.left := .of_isProper_of_locallyQuasiFinite _
  exact flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance
    inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t

end GlobalTheory.DualHomFlat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  first | (exact @GlobalTheory.DualHomFlat.main) | (exact GlobalTheory.DualHomFlat.main) | (intros; apply GlobalTheory.DualHomFlat.main  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualFactor

theorem factor_of_flat {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) [IsMonHom la] [Flat la.left] [Surjective la.left]
    [QuasiCompact la.left] (d : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) :
    ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by
    intro W a b h
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
    have h1 : (a / b) ≫ la = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hk W _ h1
    rwa [div_pow, div_eq_one] at h2)
  have := FlatQuotient.epi_of_flat_surjective la
  have := FlatQuotient.epi_tensorHom la la
  refine ⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩
  · have e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]
  · rw [← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu,
      comp_pow, Category.comp_id]
    have hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id,
      Category.comp_id, mul_pow]
  · rw [← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  intro S A B _ _ Q la d hA hB hAB hBA hla hd hk
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have : Surjective la.left := GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : Flat la.left := GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : QuasiCompact la.left := by
    have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp la.left B.hom
  exact factor_of_flat A B la d hk

end GlobalTheory.DualFactor
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinExist

section Dual

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Q : LB (A ⊗ B).left}

theorem evc_mul_right (hQ' : IsDual B A (swap Q)) (hQ : Q.IsLB) {Y : Over S} (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
  have e := (isAdditive_iff hQ'.isLB).1 hQ'.additive Y b b' a
  rwa [evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB] at e

theorem eq_of_evc (hQ : IsDual A B Q) {T : Over S} (x y : T ⟶ B)
    (h : evc hQ.isLB (fst A T) (snd A T ≫ x) = evc hQ.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev Q (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hQ.isLB _
  have hadd : IsAdditive (ev Q (fst A T) (snd A T ≫ x)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t => ?_
    rw [evc_ev hQ.isLB, evc_ev hQ.isLB, evc_ev hQ.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hQ.isLB).1 hQ.additive Y a a' (t ≫ x)
  refine (hQ.univ T _ hM hadd).unique ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hQ.isLB _)).1 ?_)
  rw [cls_ev hQ.isLB, cls_ev hQ.isLB]
  exact h

end Dual

section Siegel

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)

theorem evc_mul_left (hA : Out.RelAmple c.A c.diag) {Y : Over S} (a a' b : Y ⟶ c.A) :
    evc c.isLB (a * a') b = evc c.isLB a b + evc c.isLB a' b :=
  GlobalTheory.PrincipalIntegral.pair_mul c GlobalTheory.SemiRigid.globalFns hA Y a a' b

theorem evc_comm {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc c.isLB b a :=
  GlobalTheory.PrincipalIntegral.pair_comm c Y a b

theorem isAdditive_P (hA : Out.RelAmple c.A c.diag) : IsAdditive c.P :=
  (isAdditive_iff c.isLB).2 fun _ a a' b => evc_mul_left c hA a a' b

variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem evc_la (hQ : Q.IsLB) {la : c.A ⟶ B} (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la)))
    {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc hQ a (b ≫ la) := by
  have e := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff c.isLB (pull_isLB hQ _)).2 hla)
  rw [cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc] at e
  exact e

end Siegel

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

section Main

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem isMonHom_la (hA : Out.RelAmple c.A c.diag) (hQ : IsDual c.A B Q) (hQ' : IsDual B c.A (swap Q)) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) : IsMonHom la := by
  refine isMonHom_of_mul la fun T x y => eq_of_evc hQ _ _ ?_
  rw [← Category.assoc, ← evc_la c hQ.isLB hla, comp_mul, comp_mul, evc_mul_right hQ' hQ.isLB, ← Category.assoc,
    ← Category.assoc, ← evc_la c hQ.isLB hla, ← evc_la c hQ.isLB hla,
    evc_comm c (fst c.A T) ((snd c.A T ≫ x) * (snd c.A T ≫ y)), evc_mul_left c hA, evc_comm c _ (fst c.A T),
    evc_comm c _ (fst c.A T)]

theorem pow_eq_one_of_la {d : ℕ} (hK : SiegKerBy c d) (hQ : IsDual c.A B Q) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) {T : Over S} (x : T ⟶ c.A) (hx : x ≫ la = 1) :
    x ^ d = 1 := by
  refine hK.2 T x ((cls_eq_zero_iff (pull_isLB c.isLB _)).1 ?_)
  change evc c.isLB (snd c.A T ≫ x) (fst c.A T) = 0
  rw [evc_comm c, evc_la c hQ.isLB hla, Category.assoc, hx, MonObj.comp_one, evc_one_right hQ.isLB hQ.zero]

end Main

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

open GlobalTheory.ZarhinFam

theorem exists_zData : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  intro h M d S t c _ _ _ hd _ _ hK
  obtain ⟨B, iB, Q, hB, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme S c.A c.ab
  obtain ⟨la, hla, -⟩ := hQ.univ c.A c.P c.isLB (isAdditive_P c hK.1)
  have hmon := isMonHom_la c hK.1 hQ hQ' hla
  obtain ⟨mu, hmu, h1, h2⟩ := GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker S c.A B Q la d c.ab hB hQ hQ' hmon hd
    fun T x hx => pow_eq_one_of_la c hK hQ hla x hx
  exact ⟨B, iB, hB.comm, Q, la, mu, hB, hQ, hQ', hmon, hmu, h1, h2, hla⟩

end GlobalTheory.ZarhinExist
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_data : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  first | (exact @GlobalTheory.ZarhinExist.exists_zData) | (exact GlobalTheory.ZarhinExist.exists_zData) | (intros; apply GlobalTheory.ZarhinExist.exists_zData <;> assumption)
end
