import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierEqOfPrimitiveAdjointBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w
    rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finset_sum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_eightfold_product_eq_eighthPower : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  atlas_forward_decl GlobalTheory.Poinc.Eq8.Chars8.main
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  first | exact @GlobalTheory.Poinc.Eq8.endChar_endU | exact GlobalTheory.Poinc.Eq8.endChar_endU | (intros; apply GlobalTheory.Poinc.Eq8.endChar_endU <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  atlas_forward_decl GlobalTheory.Mum.PowData.over₀_prod_zpow
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem torusHomOf_iff_charUnit {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem charUnit_eq_pointsEquiv {S : Scheme.{0}} {X : Type} [AddCommGroup X] (χ : X) :
    charUnit S X χ = GlobalTheory.splitTorusPointsEquiv S X _ (𝟙 _) (Multiplicative.ofAdd χ) :=
  Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) χ).trans (GlobalTheory.SplitTorusHom.appTop_id _)).symm

theorem torusHomOf_prod_zpow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {K : Type}
    [Fintype K] (n : K → ℤ) (h : K → X' → X) (t : K → (splitTorus S X ⟶ splitTorus S X'))
    (ht : ∀ i, TorusHomOf (h i) (t i)) : TorusHomOf (fun χ => ∑ i, n i • h i χ) (∏ i, t i ^ n i) := by
  simp only [torusHomOf_iff_charUnit] at ht
  rw [torusHomOf_iff_charUnit]
  intro χ
  have e₁ : ∀ i, GlobalTheory.splitTorusPointsEquiv S X' _ (t i) (Multiplicative.ofAdd χ) = charUnit S X (h i χ) := fun i =>
    Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X' _ (t i) χ).trans (ht i χ))
  rw [← GlobalTheory.splitTorusPointsEquiv_val, map_prod]
  simp only [map_zpow, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply, e₁]
  rw [charUnit_eq_pointsEquiv, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, ← charUnit_eq_pointsEquiv]

end GlobalTheory.Mum.PowData

theorem GlobalTheory.Mum.PowData.onTorus_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a h H e
  choose t ht et using fun i => H i e
  refine ⟨∏ i, t i ^ n i, torusHomOf_prod_zpow n h t ht, ?_⟩
  have := (U₀.gt e).i_hom
  have hm : (Over.pullback (thick R I e)).map (∏ i, a i ^ n i) = ∏ i, (Over.pullback (thick R I e)).map (a i) ^ n i :=
    (map_prod ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _).trans
      (Finset.prod_congr rfl fun i _ => map_zpow ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _)
  rw [hm, comp_prod_zpow, prod_zpow_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [et i]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  atlas_forward_decl GlobalTheory.Mum.PowData.onTorus_prod_zpow
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTorChar

theorem eq_torusMap_of_torusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (t : splitTorus S X ⟶ splitTorus S X') (ht : GlobalTheory.Mum.Two.TorusHomOf h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem torMatch_of_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, GlobalTheory.Mum.Two.OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  intro R _ _ _ hR D' D A' A G' G _ _ _ _ hG' hG U' U p hpm ρ hon
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hρ : GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p =
      GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp := by
    obtain ⟨t, ht, hi⟩ := hon 0
    have htm := eq_torusMap_of_torusHomOf ρ t ht
    have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp
    have k' := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp'
    have e' : ((Over.pullback (spMap (residue R))).map p).left ≫ GlobalTheory.TorusPart.thickLift hr hp =
        GlobalTheory.TorusPart.thickLift hr hp' ≫ ((Over.pullback (thick R (maximalIdeal R) 0)).map p).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, e, Category.assoc]
        simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
        rw [pullback.lift_fst, pullback.lift_fst_assoc]
      · have w := Over.w ((Over.pullback (spMap (residue R))).map p)
        simp only [GlobalTheory.TorusPart.thickLift]
        rw [Category.assoc, pullback.lift_snd, Category.assoc, ← Category.assoc _ _ (GlobalTheory.TorusPart.thickPt 0 hr), w]
        simp only [Over.pullback_map_left]
        rw [pullback.lift_snd, pullback.lift_snd]
    have hc := GlobalTheory.TorusPart.pullTorus_comp k' k _ _ e' (U'.gt 0).i
    unfold GlobalTheory.TorusPart.gtTorus
    rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← GlobalTheory.Poinc.HomTor.pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTorChar

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionMatch_of_characterMap_on_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  atlas_forward_decl GlobalTheory.Poinc.HomTorChar.torMatch_of_onTorus
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

set_option maxHeartbeats 1000000 in

theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  atlas_forward_decl GlobalTheory.Mum.PowData.adjCls_abelianPart
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
noncomputable section

namespace GlobalTheory.Mum.PowData

open GlobalTheory.Mum.FactorPol

set_option maxHeartbeats 1000000 in

theorem periodRel_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q inc j hinc hj iq adj qB h k L T
  have hA := hR.1
  have := hR.2
  have := U.gen_hom
  have := U₀.gen_hom
  haveI := hinc
  haveI := hj
  haveI : IsMonHom q := L.1
  obtain ⟨k', tk'⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  have un₀ := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have kh : ∀ χ, k' (h χ) = χ := congrFun ((un₀ _).2 _ _ (iq ▸ onTorus_comp tk' L.2.2.2) onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q qB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A₀.A, IsMonHom c ∧ Gen₀ U.toUnifPre U₀.toUnifPre q c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map q ≫ U₀.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨c', hc', gc'⟩ : ∃ c' : A₀.A ⟶ A.A, IsMonHom c' ∧ Gen₀ U₀.toUnifPre U.toUnifPre j c' :=
    ⟨U₀.gen.inv ≫ (Over.pullback (jK R)).map j ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  haveI := hc
  haveI := hc'
  obtain ⟨E, eG, eA⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (q ≫ j) (c ≫ c') inferInstance inferInstance
    (by
      unfold Gen₀ at gc gc'
      rw [Functor.map_comp, Category.assoc, gc', ← Category.assoc, gc, Category.assoc])
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB

  have lamE : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) (x ≫ q ≫ j) y = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [lam_comm, ← Category.assoc, adj, lam_comm]
  have lamE' : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) x (y ≫ q ≫ j) = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [← Category.assoc, adj]
  have adjE : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL _ _ _).trans (Eq.trans (by rw [eG, lamE, lamE']) (cls_cube_two hL _ _ _).symm))
  have H₂ : LBIso (cubeLB G₀ ![fst G G ≫ q, snd G G ≫ q] U₀.LG.L)
      (cubeLB G ![fst G G ≫ E.aG, snd G G ≫ 𝟙 G] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL₀ _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL₀ _ _ _).trans (Eq.trans (by rw [eG, Category.comp_id, lamE]) (cls_cube_two hL _ _ _).symm))
  have H₃ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q q E.aG (𝟙 _) c c E.aA (𝟙 _)
    gc gc E.ext (by simp [Gen₀]) H₂
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C E E adjE H₃
    Ω K

  have eh : (⇑E.h : D.toPre.X → D.toPre.X) = ⇑h ∘ ⇑k :=
    (un _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (onTorus_comp L.2.2.2 T)
  have hφk : ∀ y, φ y = k y := fun y => hinj ((hhφ y).trans (congrFun eh y))
  have hB := D.tau_bimult
  refine ⟨fun y => ?_, fun χ => ?_⟩
  · obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    rw [← hφk]
    refine GlobalTheory.Mum.Two.Fac.pt_ext R D₀.toPre Ω _ _ ?_
    simpa only [Category.assoc] using h1
  · obtain ⟨u, hu, -⟩ := C χ
    refine ⟨u, hu, fun y z J hJ => ?_⟩
    obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have e := GlobalTheory.Mum.Two.act_val_frac R D₀.toPre D.toPre qB h Ω y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha χ u hu
      z J hJ
    rwa [hφk] at e

end GlobalTheory.Mum.PowData
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  atlas_forward_decl GlobalTheory.Mum.PowData.periodRel_of_adj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData.CmpTwoProof

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem pull_cls_of_isPart {X X₁ : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}
    (h : IsPart N M e π) (hN : N.IsLB) (hM : M.IsLB) : CechPic.pull e (cls N hN) = cls M hM := by
  have h1 := LB.isLB_linComb hN (fun _ : PUnit.{1} => 𝟙 X₁ ≫ e) (fun _ => 1)
  have h2 := LB.isLB_linComb hM (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)
  have a := cls_linComb hN _ _ h1
  have b := cls_linComb hM _ _ h2
  have c := (cls_eq_iff h1 h2).2 (iso_of_chart h2 (h.up (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)))
  have := (a.symm.trans c).trans b
  simpa only [Fintype.sum_unique, one_smul, Category.id_comp, pull_id] using this

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

end GlobalTheory.Mum.PowData.CmpTwoProof

open GlobalTheory.Mum.PowData.CmpTwoProof in
theorem GlobalTheory.Mum.PowData.cmpTwo_of_adjCls : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  intro R _ _ D D₀ q j hq hj hadj
  haveI := hq
  haveI := hj
  have hN : (JN D D₀).IsLB := jn_isLB D D₀
  have hG := GlobalTheory.globalFns_holds
  have pl := pull_cls_of_isPart (isPart_inl D.P.L D₀.P.L) hN D.P.isLB
  have pr := pull_cls_of_isPart (isPart_inr D.P.L D₀.P.L) hN D₀.P.isLB
  let φΓ : Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) :=
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let εΓ : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim Oε Oinvε
  have hL1 := LB.isLB_linComb hN φΓ εΓ

  have h0 : cls _ hL1 = 0 := by
    rw [cls_linComb hN _ _ hL1, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, pull_comp, pl, pr]
    refine Eq.trans ?_ (sub_eq_zero.2 (hadj _ (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A)))
    simp only [lam, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨Γ₀, hΓ₀⟩ := (cls_eq_zero_iff hL1).1 h0

  let o : (D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A ⊗ D₀.P.A).left :=
    (toUnit (D.P.A ⊗ D₀.P.A) ≫ lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)).left
  have hz : ∀ k, o ≫ φΓ k = Sum.elim (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D.P.A).left ≫ coprod.inl)
      (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D₀.P.A).left ≫ coprod.inr) k := by
    rintro (k | k) <;> simp only [φΓ, Sum.elim_inl, Sum.elim_inr, ← Category.assoc] <;> congr 1 <;>
      fin_cases k <;>
      simp only [lamPts, o, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, ← Over.comp_left, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, comp_one_pt, one_comp_hom, _root_.mul_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have fe0 : FormEq (Sum.elim φΓ (fun k => o ≫ φΓ k)) (Sum.elim εΓ (fun k => - εΓ k)) φΓ εΓ := by
    intro U _ h
    have hQ : ∏ k, h (o ≫ φΓ k) ^ (- εΓ k) = 1 := by
      simp only [hz]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
      simp only [Sum.elim_inl, Sum.elim_inr, εΓ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      simp only [neg_neg, one_smul, neg_smul]
      abel
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hQ, _root_.mul_one]
  obtain ⟨Γ, hΓ, hΓv⟩ := exists_gen hN fe0 (LB.mulGen _ _ _ _ _ Γ₀ (LB.invGen _ _ _ (LB.pullGen _ _ _ Γ₀ o)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hΓ₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hΓ₀ o)))
  have hone : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D₀.P.A).left) (z : Z) (J), Good (JN D D₀) z J → r ≫ o = r →
      val Γ r z J = 1 := by
    intro Z r z J hJ hr
    rw [hΓv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hr, mul_inv_cancel]
  have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  let ι₀ : D₀.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)).left
  have fe1 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => ι₀ ≫ φΓ k) εΓ := by
    intro U _ h
    rw [Fintype.prod_empty, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ι₀, ← Category.assoc,
      ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, comp_one_pt, one_comp_hom, Category.id_comp,
      _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have e0 : (η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)) ≫ toUnit _ ≫
      lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) =
      η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A) := by
    rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, comp_lift, comp_one_pt,
      Category.comp_id, o₀]
  have key1 := gen_unique' hN (u := LB.pullGen _ _ _ Γ ι₀) (u' := LB.oneGen (JN D D₀) (Y := D₀.P.A.left)) fe1
    D₀.P.A.hom (eSec D₀.P.A) (Over.w η[D₀.P.A]) (hG _ _ D₀.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hΓ ι₀)
    (oneGen_isGen _) (fun y J hJ => by
      rw [val_pull hJ, val_one]
      refine hone _ _ y J hJ ?_
      have := congrArg (fun f => f.left) e0
      simpa only [eSec, ι₀, o, Over.comp_left] using this)
  have hΓ1 : ∀ (T : Over (Sp R)) (w : T ⟶ D₀.P.A) (y : T.left) (J), Good (JN D D₀) y J →
      val Γ (lift (1 : T ⟶ D.P.A) w).left y J = 1 := by
    intro T w y J hJ
    have := key1 T.left w.left y J hJ
    rw [val_pull hJ, val_one] at this
    rwa [show w.left ≫ ι₀ = (lift (1 : T ⟶ D.P.A) w).left by
      rw [← Over.comp_left, comp_lift, comp_one_pt, Category.comp_id]] at this
  refine ⟨Γ, hΓ, ?_⟩
  intro χ' χ hc u hu T x z J hJ
  let m : D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (𝟙 D.P.A) (toUnit D.P.A ≫ D₀.c χ)).left
  have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
  have fe2 : FormEq (fun k => m ≫ φΓ k) εΓ
      (Sum.elim (fun k => D.Oφ (𝟙 _) χ' k ≫ coprod.inl) (fun k => D₀.Oφ q χ k ≫ coprod.inr)) (Sum.elim Oε Oinvε) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four,
      Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, m, pm, ← Hom.one_def, hc,
      ← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, Category.comp_id, comp_one_pt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have ev2 : ∀ y I, Good (JN D D₀) y I → val u (eSec D.P.A) y I = val (LB.pullGen _ _ _ Γ m) (eSec D.P.A) y I := by
    intro y I hI
    rw [val_pull hI]
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    have e2 : eSec D.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D.P.A] ≫ toUnit _) (toUnit _), o']
    rw [c, e2, hΓ1 _ _ y I hI]
  have key := gen_unique' hN (u := u) (u' := LB.pullGen _ _ _ Γ m) fe2 D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 hu.1 (DVR.pullGen_isGen _ _ _ _ hΓ m) ev2 T.left x.left z J hJ
  rw [key, val_pull hJ]
  congr 1
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  atlas_forward_decl GlobalTheory.Mum.PowData.cmpTwo_of_adjCls
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

section ProdPow

variable {X Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]

def prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := I × K) (fun p => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : I × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s fun k => j (i, k)) ^ n i

variable {L}

theorem val_prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (prodZGen L φ ε n t) r z J = ∏ i, val (t i) r z J ^ n i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans ?_)
  exact congrArg (· ^ n i) (gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem prodZGen_isGen (hL : L.IsLB) {φ : I → K → (Y ⟶ X)} {ε : I → K → ℤ} (n : I → ℤ)
    {t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))} (ht : ∀ i, (t i).IsGen) : (prodZGen L φ ε n t).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have m : ∀ (j : I × K → L.ι) (i : I), y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (φ i) (fun k => j (i, k)) :=
    fun _ i hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y _ ((prodZGen L φ ε n t).s j) = ∏ i, gm (𝟙 Y) y _ ((t i).s fun k => j (i, k)) ^ n i := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans
      (congrArg (· ^ n i) (gm_res _ y _ hj _)))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, v j hy.1, v j' hy.2]
  erw [gm_linComb L (fun p : I × K => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2) (𝟙 Y) y j j' hy.1 hy.2]
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  erw [gen_trans (ht i) (𝟙 Y) y (m j i hy.1) (m j' i hy.2)]
  rw [mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

end ProdPow

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

section JoinIso

variable {X X₁ X₂ Z : Scheme.{0}}

theorem part_gm_g_eq_one {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) (hM : M.IsLB)
    {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {i j : N.ι} (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) :
    gm f z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  subst hf
  rw [h.g _ ψ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

theorem part_gm_g_sec {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) {σ : M.ι → N.ι}
    (hσ : ∀ i, π (σ i) = i) {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {a b : M.ι} (ha : ψ z ∈ M.U a)
    (hb : ψ z ∈ M.U b) : gm f z (N.U (σ a) ⊓ N.U (σ b)) (N.g (σ a) (σ b)) = gm ψ z (M.U a ⊓ M.U b) (M.g a b) := by
  subst hf
  rw [h.g _ ψ z _ _ (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)]
  have : ∀ a b a' b', a = a' → b = b' → gm ψ z (M.U a ⊓ M.U b) (M.g a b) = gm ψ z (M.U a' ⊓ M.U b') (M.g a' b') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact this _ _ _ _ (hσ a) (hσ b)

variable {M₁ : LB X₁} {M₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_iso_of_joinGen (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {φ : K → (X₁ ⟶ X₂)}
    {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
      (Sum.elim ε (fun _ => -1)))) (ht : t.IsGen) :
    ∃ w : LB.Iso M₁ (LB.LinComb M₂ φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ X₁) (z : Z) (J),
      Good (join M₁ M₂) z J → gm p z _ (w.s (fun k => rr J (p ≫ φ k), rl J p)) = val t p z J := by
  have hp₁ := isPart_inl M₁ M₂
  have hp₂ := isPart_inr M₁ M₂
  choose σ₂ hσ₂ using snd_surjective (M₂ := M₂) h₁
  choose σ₁ hσ₁ using fst_surjective (M₁ := M₁) h₂
  let ix : (K → M₂.ι) × M₁.ι → K ⊕ PUnit → (join M₁ M₂).ι := fun a =>
    Sum.elim (fun k => σ₂ (a.1 k)) (fun _ => σ₁ a.2)
  have le : ∀ a, (LB.div (LB.LinComb M₂ φ ε) M₁).U a ≤
      LB.wchart (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) (ix a) :=
    fun a y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | u
      · exact (hp₂.mem _ _).2 ((hσ₂ _).symm ▸ Set.mem_iInter.1 hy.1 k)
      · exact (hp₁.mem _ _).2 ((hσ₁ _).symm ▸ hy.2)
  let c : ChartPull (LB.div (LB.LinComb M₂ φ ε) M₁)
      (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
        (Sum.elim ε (fun _ => -1))) (𝟙 X₁) :=
    { idx := ix
      le := le
      g := fun y a b ha hb => by
        erw [gm_div M₁ (LB.LinComb M₂ φ ε) (𝟙 X₁) y a b ⟨ha, hb⟩, gm_linComb M₂ φ ε (𝟙 X₁) y a.1 b.1 ha.1 hb.1,
          gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y (ix a) (ix b) (le a ha) (le b hb)]
        rw [Fintype.prod_sum_type]
        simp only [Finset.univ_unique, Finset.prod_singleton]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_
        · exact congrArg (· ^ ε k) (part_gm_g_sec hp₂ hσ₂ (ψ := 𝟙 X₁ ≫ φ k) (f := 𝟙 X₁ ≫ φ k ≫ coprod.inr)
            (Category.assoc _ _ _).symm (a := a.1 k) (b := b.1 k) (Set.mem_iInter.1 ha.1 k)
            (Set.mem_iInter.1 hb.1 k)).symm
        · refine (congrArg (·⁻¹) ?_).trans (zpow_neg_one _).symm
          refine Eq.trans ?_ (part_gm_g_sec hp₁ hσ₁ (ψ := 𝟙 X₁) (f := 𝟙 X₁ ≫ 𝟙 X₁ ≫ coprod.inl)
            (by rw [Category.id_comp]) (a := a.2) (b := b.2) ha.2 hb.2).symm
          rfl }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m : p z ∈ (LB.div (LB.LinComb M₂ φ ε) M₁).U (fun k => rr J (p ≫ φ k), rl J p) :=
    ⟨(hp₂.good hJ).mem φ p, hp₁.good hJ p⟩
  have n := hJ.mem (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  refine (congrArg (· * val t p z J) ?_).trans (one_mul _)
  rw [trF, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  refine (congrArg₂ (· * ·) (Finset.prod_eq_one fun k _ => ?_) ?_).trans (one_mul 1)
  · refine (congrArg (· ^ ε k) (part_gm_g_eq_one hp₂ h₂ (ψ := p ≫ φ k) (f := p ≫ φ k ≫ coprod.inr)
      (Category.assoc _ _ _).symm (i := σ₂ (rr J (p ≫ φ k))) (j := J (p ≫ φ k ≫ coprod.inr))
      ((hσ₂ _).trans (show (J ((p ≫ φ k) ≫ coprod.inr)).2 = _ by rw [Category.assoc])) ?_)).trans (one_zpow _)
    rw [hσ₂]; exact (hp₂.good hJ) (p ≫ φ k)
  · refine (congrArg (· ^ (-1 : ℤ)) (part_gm_g_eq_one hp₁ h₁ (ψ := p) (f := p ≫ 𝟙 X₁ ≫ coprod.inl)
      (by rw [Category.id_comp]) (i := σ₁ (rl J p)) (j := J (p ≫ 𝟙 X₁ ≫ coprod.inl))
      ((hσ₁ _).trans (show (J (p ≫ coprod.inl)).1 = _ by rw [Category.id_comp])) ?_)).trans (one_zpow _)
    rw [hσ₁]; exact hp₁.good hJ p

end JoinIso

end GlobalTheory.Mum.PowData
end
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

theorem tens_iso_psi : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  intro R _ _ D D₀ r W pr j h k h1 h2 h3 h4 h5 h6
  obtain ⟨u, hu, hu'⟩ := h6
  obtain ⟨κ, hκ, hκ'⟩ := h5
  choose Γ hΓ hΓ' using h4
  have hp₁ := isPart_inl D.P.L D₀.P.L
  let g : Fin r → (D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left) := fun b => (lift (𝟙 D.P.A) (pr b)).left
  let Φ : Fin r → Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ D.P.A.left ⨿ D₀.P.A.left) := fun a =>
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let P := prodZGen (JN D D₀) (fun ab : Fin r × Fin r => fun m => g ab.2 ≫ Φ ab.1 m) (fun _ => Sum.elim Oε Oinvε)
    (fun ab => -W ab.1 ab.2) (fun ab => LB.pullGen (JN D D₀) _ _ (Γ ab.1) (g ab.2))
  have hP : P.IsGen := prodZGen_isGen (jn_isLB D D₀) _ fun ab =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (hΓ ab.1) _
  let rig0 := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (toUnit D.P.A).left
  have hrig0 : rig0.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  let T0 := LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (LB.mulGen (JN D D₀) _ _ _ _ (hp₁.gen u)
    (LB.invGen (JN D D₀) _ _ (hp₁.gen κ))) P) (LB.invGen (JN D D₀) _ _ (hp₁.gen rig0))
  have hT0 : T0.IsGen := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hp₁.gen_isGen hu) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _
        (hp₁.gen_isGen hκ))) hP) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hp₁.gen_isGen hrig0))
  obtain ⟨t, ht, htv⟩ := exists_gen (jn_isLB D D₀)
    (φ' := Sum.elim (fun k => tensφ pr k ≫ coprod.inr) (fun _ : PUnit => 𝟙 D.P.A.left ≫ coprod.inl))
    (ε' := Sum.elim (tensε W) (fun _ => -1)) (by
      intro U _ hh
      clear hu' hκ' hΓ' h3 h1 h2 hT0 hP hrig0
      have cl : ∀ {T T' : Over (Sp R)} {B : Over (Sp R)} [GrpObj B] (s : T' ⟶ T) (x y : T ⟶ B) (i : Fin 4),
          s.left ≫ lamPts x y i = lamPts (s ≫ x) (s ≫ y) i := by
        intro T T' B _ s x y i
        fin_cases i
        · exact congrArg (fun q => q.left) (MonObj.comp_mul s x y)
        · rfl
        · rfl
        · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one s)
      have hD1 : ∀ a b i, g b ≫ Φ a (Sum.inl i) = lamPts (𝟙 D.P.A) (pr b ≫ j a) i ≫ coprod.inl := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j a) i ≫ coprod.inl = _
        rw [← Category.assoc, cl, lift_fst, lift_snd_assoc]
      have hD2 : ∀ a b i, g b ≫ Φ a (Sum.inr i) = tensφ pr ((a, b), i) ≫ coprod.inr := by
        intro a b i
        show (lift (𝟙 D.P.A) (pr b)).left ≫ lamPts (fst D.P.A D₀.P.A ≫ pr a) (snd D.P.A D₀.P.A) i ≫ coprod.inr = _
        rw [← Category.assoc, cl, lift_fst_assoc, lift_snd, Category.id_comp]
        rfl
      have hOi : ∀ i, Oinvε i = - Oε i := by intro i; fin_cases i <;> rfl
      have hCD : (∏ p : (Fin r × Fin r) × Fin 4,
            hh (lamPts (𝟙 D.P.A) (pr p.1.2 ≫ j p.1.1) p.2 ≫ coprod.inl) ^ (- -(W p.1.1 p.1.2 * Oε p.2))) *
          (∏ p : (Fin r × Fin r) × (Fin 4 ⊕ Fin 4), hh (g p.1.2 ≫ Φ p.1.1 p.2) ^ (-W p.1.1 p.1.2 * Sum.elim Oε Oinvε p.2)) =
          ∏ p : (Fin r × Fin r) × Fin 4, hh (tensφ pr p ≫ coprod.inr) ^ (tensε W p) := by
        rw [Fintype.prod_prod_type (α₁ := Fin r × Fin r), Fintype.prod_prod_type (α₁ := Fin r × Fin r),
          Fintype.prod_prod_type (α₁ := Fin r × Fin r), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ab _ => ?_
        rw [Fintype.prod_sum_type, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hD1, hD2, Sum.elim_inl, Sum.elim_inr, hOi]
        simp only [tensε, neg_neg, neg_mul, mul_neg, zpow_neg, mul_inv_cancel, _root_.one_mul, Prod.mk.eta]
      have hAB : (∏ i : Fin 4, hh (![(padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2)).left,
            𝟙 D.P.A.left, (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2).left, (toUnit D.P.A ≫ η[D.P.A]).left] i ≫
              coprod.inl) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) i)) *
          (∏ i : Fin 4, hh (lamPts (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) i ≫ coprod.inl) ^
            (-Oε i)) =
          (hh (𝟙 D.P.A.left ≫ coprod.inl))⁻¹ * hh ((toUnit D.P.A ≫ η[D.P.A]).left ≫ coprod.inl) := by
        simp only [Fin.prod_univ_four, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        have e0 : (𝟙 D.P.A * ∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) =
            padd D.P.A (𝟙 D.P.A) (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) := rfl
        have e1 : (1 : D.P.A ⟶ D.P.A) = toUnit D.P.A ≫ η[D.P.A] := rfl
        have e2 : (𝟙 D.P.A : D.P.A ⟶ D.P.A).left = 𝟙 D.P.A.left := rfl
        rw [e0, e1, e2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      have key : ∀ A B C D E Q I O : U, A * B = I⁻¹ * O → C * D = Q → E = O ^ (-1 : ℤ) →
          A * (B * C) * D * E = Q * I ^ (-1 : ℤ) := by
        intro A B C D E Q I O h₁ h₂ h₃
        rw [← _root_.mul_assoc A B C, h₁, _root_.mul_assoc _ C D, h₂, h₃]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
      exact key _ _ _ _ _ _ _ _ hAB hCD rfl) T0 hT0
  obtain ⟨w, hw, hwv⟩ := exists_iso_of_joinGen D.P.isLB D₀.P.isLB t ht
  refine ⟨w, hw, fun y z J J' hJ hJ' => ?_⟩
  obtain ⟨Jn, hJn, e1, e2⟩ := exists_good_join D.P.isLB D₀.P.isLB hJ' hJ
  subst e1 e2
  rw [hwv _ (D.xK y) z Jn hJn, htv _ _ z Jn hJn]
  have hp₂ := isPart_inr D.P.L D₀.P.L
  have hJ1 : Good D.P.L z (rl Jn) := hp₁.good hJn
  have vT : val T0 (D.xK y) z Jn = val u (D.xK y) z (rl Jn) * (val κ (D.xK y) z (rl Jn))⁻¹ *
      (∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2)) *
      (val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn))⁻¹ := by
    simp only [T0, P, rig0, val_mul hJn, val_inv, hp₁.val_gen _ _ _ hJn, val_prodZGen _ _ _ _ _ hJn, val_pull hJn,
      val_pull hJ1]
  have c1 := val_corr hJ1 (hu' y) (𝟙 _)
  rw [val_mul hJ1, val_mul hJ1, val_pull hJ1, Category.id_comp] at c1
  have cE := hκ' (toUnit (TK R) ≫ D.c y) y (fun ab => h ab.1 (k ab.2 y)) (Category.comp_id _)
    (fun ab => by simp only [h1, h2, Category.assoc]) z (rl Jn) hJ1
  have hrig : D.xK y ≫ (toUnit D.P.A).left = 𝟙 _ ≫ (toUnit (TK R)).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c y).left ≫ (toUnit D.P.A).left = _
    rw [← Over.comp_left, Category.assoc, comp_toUnit, comp_toUnit]
  have vrig : val D.rig (D.xK y ≫ (toUnit D.P.A).left) z (rl Jn) = val D.rigK (𝟙 _) z (rl Jn) := by
    rw [hrig]; exact (val_pull hJ1 _ _ _).symm
  have hper : ∀ a b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z (rr Jn) =
      val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) * val (Γ a) (D.xK y ≫ g b) z Jn := by
    intro a b
    obtain ⟨u', hu'n, hu'v⟩ := h3 a (k b y)
    rw [hu'v y z Jn hJn]
    refine congrArg (_ * ·) ((hΓ' a (h a (k b y)) (k b y) (h1 a (k b y)) u' hu'n (TK R) (toUnit _ ≫ D.c y) z Jn hJn).trans
      (congrArg (fun q => val (Γ a) q z Jn) ?_))
    show (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D₀.c (k b y))).left =
      (toUnit (TK R) ≫ D.c y).left ≫ (lift (𝟙 D.P.A) (pr b)).left
    rw [h2, ← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
  have hG : ∏ ab : Fin r × Fin r, val (Γ ab.1) (D.xK y ≫ g ab.2) z Jn ^ (-W ab.1 ab.2) =
      (∏ a, ∏ b, val (Γ a) (D.xK y ≫ g b) z Jn ^ W a b)⁻¹ := by
    rw [Fintype.prod_prod_type]; simp only [zpow_neg, Finset.prod_inv_distrib]
  have key2 : ∀ {V : Type} [CommGroup V] (ψ ρ Tm Uu Kk Tp Gp : V), Tm * Uu = ψ * ρ → Tm * Kk = Tp →
      ψ = Uu * Kk⁻¹ * Gp⁻¹ * ρ⁻¹ * (Tp * Gp) := by
    intro V _ ψ ρ Tm Uu Kk Tp Gp e₁ e₂
    rw [eq_inv_mul_of_mul_eq e₁, eq_inv_mul_of_mul_eq e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [vT, vrig, hG]
  simp only [hper, mul_zpow, Finset.prod_mul_distrib]
  have cE' : val (D.tau y (∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y))) (𝟙 _) z (rl Jn) *
      val κ (D.xK y) z (rl Jn) = ∏ a, ∏ b, val (D.tau y (h a (k b y))) (𝟙 _) z (rl Jn) ^ W a b := by
    refine Eq.trans cE ?_
    rw [Fintype.prod_prod_type]
  exact key2 _ _ _ _ _ _ _ c1 cE'

end GlobalTheory.Mum.PowData
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerData_tensorBundleIso_with_psi_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D.P.A ⟶ D₀.P.A)) (j : Fin r → (D₀.P.A ⟶ D.P.A)) (h : Fin r → D₀.X → D.X) (k : Fin r → D.X → D₀.X), (∀ a χ, D.c (h a χ) = D₀.c χ ≫ j a) → (∀ a y, D₀.c (k a y) = D.c y ≫ pr a) → (∀ a, PeriodRel D D₀ (pr a) (h a) (k a)) → (∀ a, CmpTwo D D₀ (pr a) (j a)) → Expand D (fun ab : Fin r × Fin r => W ab.1 ab.2) (𝟙 D.P.A) (fun ab => pr ab.2 ≫ j ab.1) → PrimVal D (∏ ab : Fin r × Fin r, (pr ab.2 ≫ j ab.1) ^ W ab.1 ab.2) (fun y => ∑ ab : Fin r × Fin r, W ab.1 ab.2 • h ab.1 (k ab.2 y)) → ∃ w : LB.Iso D.P.L (LB.LinComb D₀.P.L (tensφ pr) (tensε W)), w.IsGen ∧ ∀ y z J J', Good D₀.P.L z J → Good D.P.L z J' → val (D.psi y) (𝟙 _) z J' = gm (D.xK y) z _ (w.s (fun k => J (D.xK y ≫ tensφ pr k), J' (D.xK y))) * ∏ a, ∏ b, val (D₀.tau (k a y) (k b y)) (𝟙 _) z J ^ W a b := by
  atlas_forward_decl GlobalTheory.Mum.PowData.tens_iso_psi
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.SharpBundle

open GlobalTheory.ZH.EndoExtend GlobalTheory.SquareOfGeneric

theorem prod_left_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (f g : Z ⟶ (X ⊗ Y).left)
    (h₁ : f ≫ (fst X Y).left = g ≫ (fst X Y).left) (h₂ : f ≫ (snd X Y).left = g ≫ (snd X Y).left) : f = g := by
  apply pullback.hom_ext
  · simpa using h₁
  · simpa using h₂

theorem cls_eq_sum_lam : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  intro g n o _ ζ F W R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG U U₀ y α α₂ hα hαs hαL c φc φ₂ hφ hφs hφL pr hP q hq hqg
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := U₀.gen_hom
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB
  have hA := A.isLB
  have hA₀ := A₀.isLB
  have hcP := c.isLB
  have hUP := F.univ.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance

  have key : ∀ a b, CechPic.pull U.gen.hom.left (CechPic.pull (lift (pr a) (pr b)).left (cls c.P hcP)) =
      CechPic.pull (pullback.fst G.hom (jK R)) (lam (cls U₀.LG.L hL₀) (q a) (q b)) := by
    intro a b
    have eP : cls c.P hcP = CechPic.pull φ₂ (cls F.univ.P hUP) := (cls_eq_iff hcP (pull_isLB hUP _)).2 hφL
    have eΛ : CechPic.pull α₂ (cls F.univ.P hUP) = lam (cls A₀.L hA₀) (fst A₀.A A₀.A) (snd A₀.A A₀.A) :=
      ((cls_eq_iff (LB.isLB_linComb hA₀ _ _) (pull_isLB hUP _)).2 hαL).symm.trans (cls_cube_two hA₀ _ _ _)
    have eK : (U.gen.hom ≫ lift (pr a) (pr b)).left ≫ φ₂ =
        (lift ((Over.pullback (jK R)).map (q a) ≫ U₀.gen.hom) ((Over.pullback (jK R)).map (q b) ≫ U₀.gen.hom)).left ≫ α₂ := by
      apply GlobalTheory.SharpBundle.prod_left_ext
      · rw [Category.assoc, hφs.1, Category.assoc, hαs.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_fst, lift_fst]
        exact (hqg a).symm
      · rw [Category.assoc, hφs.2, Category.assoc, hαs.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_snd, lift_snd]
        exact (hqg b).symm
    have hext₀ : CechPic.pull U₀.gen.hom.left (cls A₀.L hA₀) =
        CechPic.pull (pullback.fst G₀.hom (jK R)) (cls U₀.LG.L hL₀) := by
      obtain ⟨w, hw⟩ := U₀.ext
      rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), ← cls_pull hA₀ _ (pull_isLB hA₀ _)]
      exact (cls_eq_iff _ _).2 ⟨w, hw⟩
    rw [← pull_comp, ← Over.comp_left, eP, ← pull_comp, eK, pull_comp, eΛ, pull_lam, lift_fst, lift_snd, ← lam_pull,
      hext₀, lam_pull_fst]
    let hh : Over.mk (((Over.pullback (jK R)).obj G).hom ≫ jK R) ⟶ G :=
      Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
    show _ = CechPic.pull hh.left _
    rw [pull_lam]
    congr 1 <;> ext1 <;> exact pullback.lift_fst _ _ _
  refine pic_ext (jK R) hn G (eSec G) (Over.w η[G]) ?_ ?_
  · have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩
    rw [h0, map_sum]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hq a
    have := hq b
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G₀) = η[G₀] := by rw [Hom.one_def]; simp
    rw [map_zsmul]
    show _ • CechPic.pull η[G].left _ = 0
    rw [pull_lam, IsMonHom.one_hom, IsMonHom.one_hom, ← e₁, lam_one_left, smul_zero]
  · have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    rw [hc', (cls_eq_iff hA (LB.isLB_linComb hcP _ _)).2 hP, cls_linComb hcP, map_sum, map_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, map_zsmul, key]

end GlobalTheory.SharpBundle
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  atlas_forward_decl GlobalTheory.SharpBundle.cls_eq_sum_lam
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

section Power

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] {r : ℕ}

theorem isMonHom_prod_zpow {K : Type} [Fintype K] (a : K → (G ⟶ G₀)) (ha : ∀ i, IsMonHom (a i)) (n : K → ℤ) :
    IsMonHom (∏ i, a i ^ n i) :=
  isMonHom_of_mul _ fun T x z => by
    rw [comp_prod_zpow, comp_prod_zpow, comp_prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := ha i
    rw [MonObj.mul_comp, mul_zpow]

theorem comp_zpow' {T T' : Over S} (p : T' ⟶ T) (y : T ⟶ G) (n : ℤ) : p ≫ y ^ n = (p ≫ y) ^ n := by
  simpa using comp_prod_zpow (K := Unit) p (fun _ => y) (fun _ => n)

theorem prod_zpow_same {M K : Type} [CommGroup M] [Fintype K] (a : M) (f : K → ℤ) : ∏ i, a ^ f i = a ^ ∑ i, f i := by
  have h := map_prod (zpowersHom M a) (fun i => Multiplicative.ofAdd (f i)) Finset.univ
  rw [← ofAdd_sum] at h
  exact h.symm

theorem exists_vec (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u) (v : Fin r → ℤ) :
    ∃ i : G₀ ⟶ G, IsMonHom i ∧ ∀ b, i ≫ q b = 𝟙 G₀ ^ v b := by
  obtain ⟨i, hi, -⟩ := huniv G₀ fun b => 𝟙 G₀ ^ v b
  refine ⟨i, isMonHom_of_mul _ fun T x z => (huniv T fun b => (x * z) ^ v b).unique (fun b => ?_) (fun b => ?_), hi⟩
  · rw [Category.assoc, hi, comp_zpow', Category.comp_id]
  · have := hq b
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, comp_zpow', comp_zpow', Category.comp_id, Category.comp_id,
      mul_zpow]

theorem lam_of_tens {L₀ : LB G₀.left} (hL : L₀.IsLB) (hΘ : ∃ t : LB.Gen (Theta G₀ L₀), t.IsGen) (q : Fin r → (G ⟶ G₀))
    (hq : ∀ u, IsMonHom (q u)) (W : Matrix (Fin r) (Fin r) ℤ) {c : Pic G.left}
    (hc : c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (q a) (q b)) {T : Over S} (x y : T ⟶ G) :
    lam c x y = ∑ a, ∑ b, (W + W.transpose) a b • lam (cls L₀ hL) (x ≫ q a) (y ≫ q b) := by
  have hp : ∀ h : T ⟶ G, pull h.left c = ∑ a, ∑ b, W a b • lam (cls L₀ hL) (h ≫ q a) (h ≫ q b) := fun h => by
    rw [hc]
    simp only [map_sum, map_zsmul, pull_lam]
  have hm : ∀ i, (x * y) ≫ q i = x ≫ q i * y ≫ q i := fun i => by
    have := hq i
    exact MonObj.mul_comp _ _ _
  have ho : ∀ i, (1 : T ⟶ G) ≫ q i = 1 := fun i => by
    have := hq i
    exact MonObj.one_comp _
  have e : ∑ i, ∑ j, W i j • lam (cls L₀ hL) (y ≫ q i) (x ≫ q j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls L₀ hL) (x ≫ q i) (y ≫ q j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (y ≫ _)]
  conv_lhs => rw [lam]
  simp only [hp, hm, ho, lam_one_left, lam_mul_left hL hΘ, RosatiTens.lam_mul_right hL hΘ, smul_add,
    Finset.sum_add_distrib, Matrix.add_apply, add_smul, smul_zero, Finset.sum_const_zero]
  rw [e]
  abel

end Power

theorem exists_tens (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D D₀ : DegData R (maximalIdeal R))
    (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀]
    (hG : IsSemiAbelian G) (hG₀ : IsSemiAbelian G₀) (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀)
    {r : ℕ} (W N : Matrix (Fin r) (Fin r) ℤ) (hN : (W + W.transpose) * N = 1) (q : Fin r → (G ⟶ G₀)) (hq : ∀ u, IsMonHom (q u))
    (huniv : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ G₀)), ∃! x : T ⟶ G, ∀ u, x ≫ q u = y u)
    (hc : cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b))
    (h : Fin r → (D₀.toPre.X →+ D.toPre.X)) (hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (h u))
    (xe : D.toPre.X ≃+ (Fin r → D₀.toPre.X))
    (hxe : ∀ mu, xe.symm mu = ∑ u, h u (∑ v, (W + W.transpose) u v • mu v)) :
    ∃ T : Tens D₀.toPre D.toPre W, T.xe = xe := by
  have hA := hR.1
  set Sm := W + W.transpose with hSm
  have hSs : ∀ a b, Sm a b = Sm b a := fun a b => by simp [hSm, add_comm]
  have hN' : N * Sm = 1 := mul_eq_one_comm.1 hN
  have SN : ∀ a c, ∑ b, Sm a b * N b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN, Matrix.one_apply]
  have NS : ∀ a c, ∑ b, N a b * Sm b c = if a = c then 1 else 0 := fun a c => by
    rw [← Matrix.mul_apply, hN', Matrix.one_apply]
  have hΘ₀ : ∃ t : LB.Gen (Theta G₀ U₀.LG.L), t.IsGen := ⟨U₀.cubG.t, U₀.cubG.isGen⟩
  have hΘ : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have P := fun {T : Over (Sp R)} (x y : T ⟶ G) => lam_of_tens U₀.LG.isLB hΘ₀ q hq W hc x y
  rw [← hSm] at P
  have zr : ∀ {T : Over (Sp R)} (x z : T ⟶ G₀) (n : ℤ), lam (cls U₀.LG.L U₀.LG.isLB) x (z ^ n) =
      n • lam (cls U₀.LG.L U₀.LG.isLB) x z := fun x z n => by
    simpa using RosatiTens.lam_prod_right (κ := Unit) U₀.LG.isLB hΘ₀ x (fun _ => z) (fun _ => n)
  choose j hj jq using fun a => exists_vec q hq huniv fun b => N b a
  choose inc hinc iq using fun a => exists_vec q hq huniv fun b => if a = b then 1 else 0
  let rr' : Fin r → (G ⟶ G₀) := fun a => ∏ b, q b ^ Sm a b
  have hrr : ∀ a, IsMonHom (rr' a) := fun a => isMonHom_prod_zpow q hq _
  have iq₁ : ∀ a, inc a ≫ q a = 𝟙 _ := fun a => by rw [iq, if_pos rfl, zpow_one]
  have jr : ∀ a, j a ≫ rr' a = 𝟙 _ := fun a => by
    simp only [rr', comp_prod_zpow, jq, ← zpow_mul, prod_zpow_same, mul_comm (N _ _), SN]
    simp
  have adjq : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (q a) (j a) := fun a T x z => by
    simp only [P, Category.assoc, jq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, SN]
    simp
  have adjr : ∀ a, AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) (rr' a) (inc a) := fun a T x z => by
    simp only [P, Category.assoc, iq, comp_zpow', Category.comp_id, zr, smul_smul, ← Finset.sum_smul, rr', comp_prod_zpow,
      RosatiTens.lam_prod_left U₀.LG.isLB hΘ₀]
    simp [hSs a]
  have hNs : ∀ a b, N a b = N b a := fun a b => by
    have e₁ : Sm.transpose = Sm := Matrix.ext fun a b => hSs b a
    have e₂ : N.transpose * Sm = 1 := by rw [← e₁, ← Matrix.transpose_mul, hN, Matrix.transpose_one]
    have e₃ : N.transpose = N := by rw [← Matrix.mul_one N.transpose, ← hN, ← Matrix.mul_assoc, e₂, Matrix.one_mul]
    exact congrFun (congrFun e₃ b) a
  let f : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.2 ≫ j ab.1) ^ W ab.1 ab.2
  let f' : G ⟶ G := ∏ ab : Fin r × Fin r, (q ab.1 ≫ j ab.2) ^ W ab.1 ab.2
  have hf : IsMonHom f := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have hf' : IsMonHom f' := isMonHom_prod_zpow _ (fun ab => inferInstance) _
  have ff : f * f' = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [f, f', MonObj.mul_comp, prod_zpow_comp, Category.assoc, jq, comp_zpow', Category.comp_id, ← zpow_mul]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm, ← Finset.prod_mul_distrib]
    simp only [prod_zpow_same, ← zpow_add, ← Finset.sum_add_distrib, ← mul_add]
    have : ∀ b, ∑ a, N c a * (W a b + W b a) = if c = b then 1 else 0 := fun b => NS c b
    simp [this]) (fun c => Category.id_comp _)
  have adjf : AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' := fun T x z => by
    simp only [f, f', comp_prod_zpow, RosatiTens.lam_prod_left U.LG.isLB hΘ, RosatiTens.lam_prod_right U.LG.isLB hΘ]
    refine Finset.sum_congr rfl fun ab _ => congrArg _ ?_
    rw [← Category.assoc, ← Category.assoc, adjq, lam_comm _ _ z, adjq, lam_comm]
  have primf : cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f := by
    simp only [f, RosatiTens.lam_prod_right U.LG.isLB hΘ, adjq _ _, Category.id_comp, Fintype.sum_prod_type]
    exact hc
  have idq : ∏ a, (q a ≫ inc a) ^ (1 : ℤ) = 𝟙 G := (huniv G q).unique (fun c => by
    simp only [prod_zpow_comp, Category.assoc, iq, comp_zpow', Category.comp_id]
    simp) (fun c => Category.id_comp _)
  choose qB hqB oq using fun a => exists_abelian_hom R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre (q a) (hq a)
  choose jB hjB oj using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  choose iB hiB oi using fun a => exists_abelian_hom R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (inc a) (hinc a)
  choose k tk using fun a => unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre (j a) (hj a)
  have un := over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have un₀ := over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have oz : ∀ m : ℤ, Over₀ U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (𝟙 _ ^ m) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.over_id
  have tz : ∀ m : ℤ, OnTorus U₀.toUnifPre U₀.toUnifPre (𝟙 G₀ ^ m) (fun χ => m • χ) := fun m => by
    simpa using GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre Unit (fun _ => m) _ _ fun _ => FactorPol.onTorus_id
  have iqB : ∀ a b, iB a ≫ qB b = 𝟙 _ ^ (if a = b then 1 else 0 : ℤ) := fun a b =>
    (un₀ _).1 _ _ (iq a b ▸ FactorPol.over_comp (oi a) (oq b)) (oz _)
  have jqB : ∀ a b, jB a ≫ qB b = 𝟙 _ ^ N b a := fun a b =>
    (un₀ _).1 _ _ (jq a b ▸ FactorPol.over_comp (oj a) (oq b)) (oz _)
  have idB : ∏ a, (qB a ≫ iB a) ^ (1 : ℤ) = 𝟙 _ := (un _).1 _ _
    (idq ▸ GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ (fun _ => 1) _ _ fun a => FactorPol.over_comp (oq a) (oi a))
    FactorPol.over_id
  have kh : ∀ a b χ, k a (h b χ) = N b a • χ := fun a b =>
    congrFun ((un₀ _).2 _ _ (jq a b ▸ FactorPol.onTorus_comp (tk a) (hh b)) (tz _))
  have xk : ∀ y a, xe y a = k a y := fun y a => by
    obtain ⟨mu, rfl⟩ := xe.symm.surjective y
    rw [AddEquiv.apply_symm_apply, hxe]
    simp only [map_sum, kh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hNs _ a, NS]
    simp
  have extB : ∀ {T : Over (Sp R)} (x x' : T ⟶ D.toPre.P.A), (∀ a, x ≫ qB a = x' ≫ qB a) → x = x' := fun x x' e => by
    rw [← Category.comp_id x, ← Category.comp_id x', ← idB, comp_prod_zpow, comp_prod_zpow]
    simp only [← Category.assoc, e]
  have per := fun a => GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (inc a) (j a) (hinc a) (hj a) (iq₁ a) (adjq a) (qB a) (h a)
    (k a) ⟨hq a, hqB a, oq a, hh a⟩ (tk a)
  have adjB := fun a => GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract R hR D D₀ A A₀ G G₀ hG hG₀ U U₀ (q a) (rr' a) (inc a) (j a) (hq a) (hrr a) (hinc a) (hj a) (iq₁ a)
    (jr a) (adjq a) (adjr a) (qB a) (jB a) (hqB a) (hjB a) (oq a) (oj a)
  have cz : ∀ (m : ℤ) χ, D₀.toPre.c (m • χ) = D₀.toPre.c χ ^ m := fun m χ => by
    let φ : Multiplicative D₀.toPre.X →* (𝟙_ (Over (Sp R)) ⟶ D₀.toPre.P.A) :=
      MonoidHom.mk' (fun y => D₀.toPre.c y.toAdd) fun a b => D₀.toPre.c_add _ _
    exact map_zpow φ (Multiplicative.ofAdd χ) m
  have ch : ∀ a χ, D.toPre.c (h a χ) = D₀.toPre.c χ ≫ jB a := fun a χ => extB _ _ fun b => by
    rw [← (per b).1, kh, cz, Category.assoc, jqB, comp_zpow', Category.comp_id, hNs]
  obtain ⟨w, hw, hψ⟩ := GlobalTheory.T.powerData_tensorBundleIso_with_psi_values R D.toPre D₀.toPre r W qB jB (fun a => h a) (fun a => k a) ch (fun a => (per a).1)
    (fun a => (per a).2) (fun a => GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint R _ _ _ _ (hqB a) (hjB a) (adjB a)) (GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult R _ D.tau_bimult _ _ _ _ _)
    (GlobalTheory.T.thetaMultiplier_eq_of_primitive_adjoint_bundle R hR D A G hG U f f' hf hf' ff adjf primf _ _
      (GlobalTheory.T.uniformisedGroup_prod_zpow_over_abelianParts R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.over_comp (oq ab.2) (oj ab.1))
      (GlobalTheory.T.uniformisedGroup_prod_zpow_characterMap R _ D D A A G G U.toUnifPre U.toUnifPre _ _ _ _ fun ab => FactorPol.onTorus_comp (hh ab.1) (tk ab.2)))
  have lf : ∀ {T : Over (Sp R)} (y : Fin r → (T ⟶ D₀.toPre.P.A)) b, (∏ a, (y a ≫ iB a) ^ (1 : ℤ)) ≫ qB b = y b := fun y b => by
    simp only [prod_zpow_comp, Category.assoc, iqB, comp_zpow', Category.comp_id]
    simp
  exact ⟨{ pr := qB, pr_hom := hqB, xe := xe, w := w, w_gen := hw
           lim := Fan.IsLimit.mk _ (fun s => (∏ a, (s.proj a ≫ iB a) ^ (1 : ℤ) : s.pt ⟶ D.toPre.P.A)) (fun s b => lf _ b)
             (fun s m hm => extB _ _ fun b => (hm b).trans (lf _ b).symm)
           c_pr := fun z a => by rw [xk, (per a).1]
           psi := fun y z J J' hJ hJ' => (hψ y z J J' hJ hJ').trans (congrArg _ (Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => by rw [xk, xk])) }, rfl⟩

end GlobalTheory.Mum.PowData

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
  ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Eq8 in

theorem GlobalTheory.Mum.PowData.sharpRef_of_characters : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN _ _ D₀ e₀ hRef G₀ _ _ A₀ U₀ y α α₂ hG₀ hα hsq hlb P c φc φ₂ hφ hφsq hφlb _ pr _ _
    hPL G _ _ hG D U q hq huniv hcomp ch hch e he
  have hR : Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  have hc := GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum g n o ζ F W V₁ hR D D₀ P A₀ G G₀ hG U U₀ y α α₂ hα hsq hlb c φc φ₂ hφ hφsq hφlb pr hPL q hq hcomp
  have hh : ∀ u, OnTorus U.toUnifPre U₀.toUnifPre (q u) (ch u) := fun u => by
    obtain ⟨h, th⟩ := unifPre_hom_character_const V₁ _ hR.1 D D₀ P A₀ G G₀ U.toUnifPre U₀.toUnifPre (q u) (hq u)
    rwa [torMatch_unique V₁ hR G₀ hG₀ D₀ A₀ U₀ V₁ hR G hG D P U _ _ Function.injective_id _ _ (hch u)
      (GlobalTheory.T.toricTorsionMatch_of_characterMap_on_torus V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ (q u) (hq u) h th)]
  obtain ⟨T, hT⟩ := GlobalTheory.Mum.PowData.exists_tens V₁ hR D D₀ P A₀ G G₀ hG hG₀ U U₀ W (W + W.transpose)⁻¹
    (Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)) q hq huniv hc ch hh
    (e.symm.trans (AddEquiv.piCongrRight fun _ => e₀.symm)) (fun mu => by
      show e (fun a => e₀ (mu a)) = _
      simp [he])
  refine GlobalTheory.T.sharpRef_of_refines_tensor W V Q V₁ ρ D₀.toPre D.toPre e₀ hRef T e fun mu a => ?_
  simp [hT]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_eighthPower_via_characterMaps : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  atlas_forward_decl GlobalTheory.Mum.PowData.sharpRef_of_characters
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G _ _ hG D U q hq hqu hqc
  obtain ⟨ch, hch, hbij⟩ := GlobalTheory.T.characters_eightfold_product_eq_eighthPower V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq hqu
  let act : Matrix (Fin 8) (Fin 8) ℤ → (Fin 8 → Q.X) → (Fin 8 → Q.X) := fun N mu u => ∑ v, N u v • mu v
  have hact : ∀ N N' mu, act N (act N' mu) = act (N * N') mu := by
    intro N N' mu
    funext u
    simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have hone : ∀ mu, act 1 mu = mu := by
    intro mu
    funext u
    simp [act, Matrix.one_apply]
  have hdet : IsUnit (W + W.transpose).det := by rw [hW.2]; exact isUnit_one
  have hM1 : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hM2 : (W + W.transpose)⁻¹ * (W + W.transpose) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hactadd : ∀ N mu mu', act N (mu + mu') = act N mu + act N mu' := by
    intro N mu mu'
    funext u
    simp [act, smul_add, Finset.sum_add_distrib]
  let f : (Fin 8 → Q.X) →+ D.toPre.X :=
    { toFun := fun mu => ∑ u, ch u (e₀.symm (act (W + W.transpose) mu u))
      map_zero' := by
        have : act (W + W.transpose) 0 = 0 := by funext u; simp [act]
        simp [this]
      map_add' := by
        intro mu mu'
        simp only [hactadd, Pi.add_apply, map_add, Finset.sum_add_distrib] }
  have hfb : Function.Bijective f := by
    have hA : Function.Bijective (act (W + W.transpose)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨act (W + W.transpose)⁻¹ x, by rw [hact, hM1, hone]⟩⟩
      have := congrArg (act (W + W.transpose)⁻¹) hxy
      rwa [hact, hact, hM2, hone, hone] at this
    have hE : Function.Bijective (fun x : Fin 8 → Q.X => fun u => e₀.symm (x u)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨fun u => e₀ (x u), by funext u; simp⟩⟩
      funext u
      exact e₀.symm.injective (congrFun hxy u)
    exact hbij.comp (hE.comp hA)
  let e : (Fin 8 → Q.X) ≃+ D.toPre.X := AddEquiv.ofBijective f hfb
  refine ⟨e, GlobalTheory.T.degenerationData_eighthPower_via_characterMaps g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G hG D U q hq hqu hqc ch hch e (fun mu => rfl), ?_⟩
  intro a a' hM E hE mu
  have hEc := GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap V₁ hCN D P G hG U E
  have key := GlobalTheory.T.characterMap_of_integral_matrix_action V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq ch hch a E.aG E.h E.homG hEc hE
  show E.h (f mu) = f (act a' mu)
  simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [← map_zsmul, ← map_sum]
  congr 2
  have h3 : act (W + W.transpose) (act a' mu) = act a.transpose (act (W + W.transpose) mu) := by
    rw [hact, hact, hM]
  rw [h3]
  simp [act, Matrix.transpose_apply]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerDegData_latticeIso_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow
end
