import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_dvr_extensions_iso_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp K ⟶ Xo.X) (G G₂ : SAB H (Sp T)) (t t₂ : SAB H (Sp K)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T K))) (n₁ : SABMap t₂ Xo.univ.t x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T K))), ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.sab_extensions_iso | exact GlobalTheory.sab_extensions_iso | (intros; apply GlobalTheory.sab_extensions_iso <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frames_differ_by_unit' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  first | exact @GlobalTheory.IntLie.integral_frames_differ_by_unit | exact GlobalTheory.IntLie.integral_frames_differ_by_unit | (intros; apply GlobalTheory.IntLie.integral_frames_differ_by_unit <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valV_eq_one_integral_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  first | exact @GlobalTheory.IntegralGenerator.valV_eq_one | exact GlobalTheory.IntegralGenerator.valV_eq_one | (intros; apply GlobalTheory.IntegralGenerator.valV_eq_one <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_sabMap_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} (T : CDVR) {x x' : Sp T.Fr ⟶ Xo.X} (hx : x' = x) (G G₂ : SAB H (Sp T.V))
    (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t₂ Xo.univ.t x') (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) :
    ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  subst hx
  exact GlobalTheory.T.semiAbelian_dvr_extensions_iso_compatible E H Dw l Xo T.V T.Fr x' G G₂ t t₂ m₁ m₂ n₁ n₂

theorem intLatU_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  intro E _ _ _ H Dw l Xo c T io y y'
  let := io.toAlgebra
  intro hx
  obtain ⟨G, t, m₁, m₂, ⟨ub, hub⟩, θ, hθ⟩ := y.2.2
  obtain ⟨G₂, t₂, n₁, n₂, ⟨ub₂, hub₂⟩, θ₂, hθ₂⟩ := y'.2.2
  obtain ⟨k, n, hk, hn⟩ := exists_sabMap_of_eq T hx G G₂ t t₂ m₁ m₂ n₁ n₂
  refine ⟨GlobalTheory.T.integral_frames_differ_by_unit' E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ hub hub₂, ?_⟩
  intro a pm h1 h2 h3
  refine GlobalTheory.T.valV_eq_one_integral_generators E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ hθ hθ₂ a
    ⟨pm, h1, ?_, h3⟩
  have hid : spMap (RingHom.id T.Fr) = 𝟙 (Sp T.Fr) := Spec.map_id _
  rw [h2, hid]
  exact (Category.comp_id _).symm

end GlobalTheory.Frames
end
