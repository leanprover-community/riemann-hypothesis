import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section SlopeTestRemainingChoices

variable {S T : Scheme.{0}} (f : T ⟶ S)

theorem pullback_prod_hom_ext {X Y : Over S} {W : Over T}
    {u v : W ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : u ≫ (Over.pullback f).map (fst X Y) = v ≫ (Over.pullback f).map (fst X Y))
    (h₂ : u ≫ (Over.pullback f).map (snd X Y) = v ≫ (Over.pullback f).map (snd X Y)) : u = v :=
  BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv (Over.pullback f) _ _)
    (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y))) h₁ h₂

theorem pullback_map_one {X G : Over S} [MonObj G] :
    (Over.pullback f).map (1 : X ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, Functor.map_comp]
  change _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))]
  exact toUnit_unique _ _

end SlopeTestRemainingChoices

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section Torus

variable {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

theorem torusHomOf_iff_appTop' (h : X₂ → X₁) (t : splitTorus S X₁ ⟶ splitTorus S X₂) : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X₂ χ).val = (charUnit S X₁ (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) : Γ((splitTorus S X₁).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X₂ χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {h : X₂ → X₁} {t t' : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht,
    (torusHomOf_iff_appTop' _ _).1 ht']

theorem eq_one_of_torusHomOf_zero {t : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf (fun _ => (0 : X₁)) t) : t = 1 := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective ?_
  rw [map_one]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have k : ∀ χ : X₂, (GlobalTheory.splitTorusPointsEquiv S X₂ _ t (Multiplicative.ofAdd χ)).val =
      (charUnit S X₁ 0).val := fun χ => by
    rw [GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht]
  rw [k χ, ← k 0, ofAdd_zero, map_one]
  rfl

theorem torusHomOf_torusMap (q : X₂ →+ X₁) : TorusHomOf q (GlobalTheory.SplitTorusPow.torusMap S q) :=
  (torusHomOf_iff_appTop' _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q χ

end Torus

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem IsProdUnif.linHom_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → LinHom U₁ U i₁ q₁ (lift (𝟙 G₁) 1) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ hi₁ hi₂
  have h1 : IsMonHom (1 : G₁ ⟶ G₂) := inferInstanceAs (IsMonHom (toUnit G₁ ≫ η[G₂]))
  have hi₂' : i₁ ≫ p₂ = 1 := hi₂.trans Hom.one_def.symm
  have hlim := hD.lim
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have := (U₂.gt e).q_hom
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    refine pullback_prod_hom_ext _ ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂', pullback_map_one,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]
  ·
    have := (U₂.gt e).i_hom
    let E := Equiv.ofBijective _ hD.xsum
    let j₁ : D₁.toPre.X → D.toPre.X := fun y => E.symm (y, 0)
    let j₂ : D₂.toPre.X → D.toPre.X := fun y => E.symm (0, y)
    have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
      have := E.apply_symm_apply (y, 0)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
      have := E.apply_symm_apply (0, y)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    obtain ⟨t₁, ht₁, hf⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, hs⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    let t := GlobalTheory.SplitTorusPow.torusMap (Sp (R ⧸ I ^ (e + 1))) q₁
    have ht : TorusHomOf q₁ t := torusHomOf_torusMap q₁
    have e₁ : t ≫ t₁ = 𝟙 _ := by
      have k := ht.comp ht₁
      simp only [fun y => (hj₁ y).1] at k
      exact torusHomOf_unique k (TorusHomOf.id _)
    have e₂ : t ≫ t₂ = 1 := by
      have k := ht.comp ht₂
      simp only [fun y => (hj₂ y).1] at k
      exact eq_one_of_torusHomOf_zero k
    refine ⟨t, ht, pullback_prod_hom_ext _ ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id, hf,
        ← Category.assoc, e₁, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_snd, hs, ← Category.assoc, e₂,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.MumProd
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdTorusExt

section Torus

variable {S : Scheme.{0}} {X X' X'' : Type} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']

theorem torusMap_comp' (a : X →+ X') (b : X'' →+ X) :
    GlobalTheory.SplitTorusPow.torusMap S a ≫ GlobalTheory.SplitTorusPow.torusMap S b = GlobalTheory.SplitTorusPow.torusMap S (a.comp b) := by
  apply (GlobalTheory.splitTorusPointsEquiv S X'' _).injective
  conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]
  rw [Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap,
    GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_id' : GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  apply (GlobalTheory.splitTorusPointsEquiv S X _).injective
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]
  rw [GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem isIso_lift_torusMap {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (E : X ≃+ X₁ × X₂) :
    IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂)))) := by
  haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂
  have e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) =
      GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫
        lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
          (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    rw [comp_lift, torusMap_comp', torusMap_comp']
  haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) :=
    ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by
      rw [torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp,
        torusMap_id'], by
      rw [torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by
        ext <;> simp, torusMap_id']⟩
  rw [e]
  infer_instance

end Torus

end GlobalTheory.ProdTorusExt

namespace GlobalTheory.ProdTorusExt

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  intro R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD
  let F := Over.pullback (thick R I e)
  let S₀ := Sp (R ⧸ I ^ (e + 1))
  haveI := hD.hom₁
  haveI := hD.hom₂
  haveI := g₁.q_hom
  haveI := g₂.q_hom
  haveI := g₁.i_hom
  haveI := g₂.i_hom
  let E : D.X ≃+ D₁.X × D₂.X := AddEquiv.ofBijective (q₁.prod q₂) hD.xsum
  let j₁ : D₁.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)
  let j₂ : D₂.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)
  let τ₁ := GlobalTheory.SplitTorusPow.torusMap S₀ j₁
  let τ₂ := GlobalTheory.SplitTorusPow.torusMap S₀ j₂
  haveI : IsMonHom τ₁ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _
  haveI : IsMonHom τ₂ := GlobalTheory.SplitTorusPow.isMonHom_torusMap _
  haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E

  haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) :=
    isIso_prodComparison_of_preservesLimit_pair F G₁ G₂
  haveI := hD.lim
  have eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A :=
    (Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm
  haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance
  haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)
  haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)
  let q := lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))
  let i := lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P g₁.q.left → P g₂.q.left → P q.left := by
    intro P _ _ h₁ h₂
    haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))
    haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))
    rw [Over.comp_left, Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))
  have hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]
  have hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]

  have key := GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel
  have hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) := by
    refine IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm
      (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _)
      (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_
    · simp only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · exact toUnit_unique _ _
    · simp only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, IsMonHom.one_hom]

  have hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (y, 0))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  have hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (0, y))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  refine ⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj,
    hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩
  · refine ⟨τ₁, ?_, hi₁⟩
    rw [hE₁ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₁
  · refine ⟨τ₂, ?_, hi₂⟩
    rw [hE₂ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₂

end GlobalTheory.ProdTorusExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_product_over_thickening_of_sumData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  atlas_forward_decl GlobalTheory.ProdTorusExt.main
end
