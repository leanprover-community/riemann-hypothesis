import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommuteStatement

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT.OLinTors

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (k : ℕ), 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∀ a p p', QkAct ιD a p p' → f p' = f p ≫ ιA.act a := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hI D A G _ _ hG U F _ _ _ O _ _ _ ιD ιA ιG hlin hcube k hk f hf a p p' hp
  obtain ⟨E, eG, eA, -, -, eact⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  obtain ⟨q, hy, hg, hq⟩ := hp
  have hb := (GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL h₁ h₂ h₃ h₄ R I hI D A G hG U F E E' (by rw [eG, eG']; exact hcube a)).2 k hk p q (f p)
    (by rw [eh', star_star]; exact hy) ((eact F _ _).2 hg) ((hf.1 p _).2 rfl)
  have e := (hf.1 q _).1 hb
  rw [eA] at e
  rw [e]
  first | exact (hf.2.2.1 _ _).2 hq | exact ((hf.2.2.1 _ _).2 hq).symm
end GlobalTheory.UT.OLinTors
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_uniformisation_torsion_map_isLinear : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (k : ℕ), 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∀ a p p', QkAct ιD a p p' → f p' = f p ≫ ιA.act a := by
  first | exact @GlobalTheory.UT.OLinTors.main | exact GlobalTheory.UT.OLinTors.main | (intros; apply GlobalTheory.UT.OLinTors.main <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem torsionIso_of_pelUnif : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  intro hL h1 h2 h3 h4 E _ _ _ H R _ _ _ I hI t P F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f, hf⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hI P.D P.A t.G t.semi P.U F k hk
  have hadj : ∀ a : NumberField.RingOfIntegers E,
      LBIso (cubeLB t.G ![fst t.G t.G ≫ t.act.toRingAct.act a, snd t.G t.G] P.U.LG.L)
        (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.toRingAct.act (star a)] P.U.LG.L) := by
    intro a
    rw [P.bundle]
    exact t.adj a
  have hlin := GlobalTheory.T.linear_uniformisation_torsion_map_isLinear hL h1 h2 h3 h4 R I hI P.D P.A t.G t.semi P.U F
    (NumberField.RingOfIntegers E) P.oD P.oA t.act.toRingAct P.lin hadj k hk f hf
  exact ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hlin, hf.2.2.2.2⟩
end GlobalTheory.UT
end
