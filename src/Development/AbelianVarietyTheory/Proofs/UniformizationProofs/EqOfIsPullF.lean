import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQk
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkToAkU_of_integral_torsion_point : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (k : ℕ), 1 ≤ k → ∀ (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt D.toPre F k) (xF : TFK (R := R) F ⟶ A.A), p.y = 0 → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g → xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) F) ≫ x).left → QkToAkU U.toUnifPre F k p xF := by
  first | exact @GlobalTheory.qkToAkU_of_integral_torsion | exact GlobalTheory.qkToAkU_of_integral_torsion | (intros; apply GlobalTheory.qkToAkU_of_integral_torsion <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.qkToAk_descends_along_baseChange : GlobalFnsSt → SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) → QkToAkU U'.toUnifPre F k p' x' → QkToAkU U.toUnifPre F k p x := by
  first | exact @GlobalTheory.qkToAk_of_baseChange | exact GlobalTheory.qkToAk_of_baseChange | (intros; apply GlobalTheory.qkToAk_of_baseChange <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteTorsionExt

theorem eq_of_isPullF {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T}
    {g₁ g₂ : GtPtF D F} (h₁ : GtPt.IsPullF F x g g₁) (h₂ : GtPt.IsPullF F x g g₂) : g₁ = g₂ := by
  obtain ⟨b₁, s₁, i₁, z₁, m₁⟩ := g₁
  obtain ⟨b₂, s₂, i₂, z₂, m₂⟩ := g₂
  obtain rfl : b₁ = b₂ := Over.OverMorphism.ext (h₁.1.trans h₂.1.symm)
  obtain rfl : s₁ = s₂ := funext fun χ => GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (i₁ χ) (i₂ χ)
    (DVR.corr_trans D.P.isLB (h₁.2 χ) (DVR.corr_symm (h₂.2 χ)))
  rfl

theorem main : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → I' ≠ ⊤ → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (x₁ : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ G') (gp : GtPt D'.toPre (𝟙_ (Over (Spec (CommRingCat.of R'))))), x₁ ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R' I' e) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G'), xe ≫ fstG I' e G' = toUnit _ ≫ x₁ ∧ xe ≫ (U'.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (LB.pullGen D'.toPre.P.L _ _ ((U'.gt e).t χ) xe.left) (LB.pullGen D'.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R' I' e))).left)) → ∀ (p : QkPt D.toPre F k) (g' : GtPtF D'.toPre F) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → IsPullGtF φ hD F p.g g' → GtPt.IsPullF F (toUnit (TF (R := R') F)).left gp g' → x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R') F) ≫ x₁).left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) → QkToAkU U.toUnifPre F k p x := by
  intro hL R R' _ _ _ _ _ I I' hR hR' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hI' F _ _ _ hF k hk x₁ gp hx₁ hxe
    p g' x hp hg hg' hx
  obtain ⟨p', hp', hpg'⟩ := (GlobalTheory.T.torsionPoint_qk_alt hL.globalFns R' I' hR' hI' D' A' G' U'.toUnifPre k x₁ gp hx₁ hxe).2 F
  have e : p'.g = g' := eq_of_isPullF hpg' hg'
  let y : TFK (R := R') F ⟶ (Over.pullback (jK R')).obj G' :=
    Over.homMk (pullback.lift (toUnit (TF (R := R') F) ≫ x₁).left (jFK (R := R') F)
      (Over.w (toUnit (TF (R := R') F) ≫ x₁))) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U'.gen.hom).left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') =
      (toUnit (TF (R := R') F) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine GlobalTheory.T.qkToAk_descends_along_baseChange hL.globalFns hL.secBaseChange R R' I I' hR hR' φ D A G U G' bc hbc A' D' hD U' hU F hF k hk
    p x p' (y ≫ U'.gen.hom) (by rw [hp, hp', map_zero]) (e ▸ hg) ?_
    (GlobalTheory.T.qkToAkU_of_integral_torsion_point hL R' I' hR' hI' D' A' G' U' k hk x₁ gp hx₁ hxe F p' _ hp' hpg' hy)
  rw [hx, ← hy]
  simp only [Category.assoc]

end GlobalTheory.FiniteTorsionExt
end
