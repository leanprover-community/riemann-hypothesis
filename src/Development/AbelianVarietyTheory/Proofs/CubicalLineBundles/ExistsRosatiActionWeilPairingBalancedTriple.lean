import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  first | exact @GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | exact GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | (intros; apply GlobalTheory.PairingScheme.weilIs_iff_of_lamEq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_oAct_rosatiConj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  intro hL E _ _ _ _ H hs K _ _ T
  have : IsCommMonObj T.pol.A := T.pol.isAb.comm
  obtain ⟨ra, hra⟩ := (ringAct_iff_oAct (𝓞 E) (Sp (𝓞 K)) T.pol.A).2 T.t.act
  have hlam : ∀ a : 𝓞 E, LamEq T.pol.L (ra.act a) (𝟙 T.pol.A) T.pol.L (𝟙 T.pol.A) (ra.act (star a)) := by
    intro a
    rw [hra, hs]
    have h := T.t.adj a
    simpa [LamEq] using h
  refine ⟨⟨ra, fun a => (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ T.pol _ _ (ra.hom a) (ra.hom _)).2 (hlam a)⟩,
    hra, ?_⟩
  intro a Tb k x z c hk hx hz
  have hp := points_sums_eq_products.1 (Sp (𝓞 K)) T.pol.A Tb
  rw [hp.2.2.1, hp.1] at hx hz
  have := GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso hL (𝓞 K) T.pol T.pol T.pol T.pol (ra.act a) (𝟙 _) (𝟙 _) (ra.act (star a)) (ra.hom a)
    inferInstance inferInstance (ra.hom _) (hlam a) Tb k x z c hk hx hz
  simpa using this

end GlobalTheory.LamF
end
