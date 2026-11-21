import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndSectionValueTranslateProdFirstOrderLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  first | exact @GlobalTheory.KSLin.snd_valR_translate_prod | exact GlobalTheory.KSLin.snd_valR_translate_prod | (intros; apply GlobalTheory.KSLin.snd_valR_translate_prod <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M] (f : P ⟶ Q) :
    (Q ⟶ M) →* (P ⟶ M) where
  toFun := fun g => f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g₁ g₂ => MonObj.comp_mul f g₁ g₂

theorem comp_list_prod {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M]
    (f : P ⟶ Q) {m : ℕ} (u : Fin m → (Q ⟶ M)) :
    f ≫ (List.ofFn u).prod = (List.ofFn fun c => f ≫ u c).prod := by
  have h := map_list_prod (precompHom (M := M) f) (List.ofFn u)
  rw [List.map_ofFn] at h
  exact h

theorem translate_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  intro E _ _ _ H X t U m v' cf va S _ φ g₀ hg g' y hTan hComb hg' hy
  have hr0 : (epsMul (0 : S)).comp (dualMap φ) =
      ((algebraMap S (DualNumber S)).comp φ).comp (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hra : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨fun c => ?_, fun w hw => ?_⟩
  · let gA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ Over.mk (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap ((algebraMap S (DualNumber S)).comp φ)) (by
        show spMap _ ≫ GlobalTheory.LogKS.chart U = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, spMap_comp, Category.assoc])
    have h1 : gA ≫ (1 : Over.mk (GlobalTheory.LogKS.chart U) ⟶ t.G) = 1 := MonObj.comp_one gA
    apply Over.OverMorphism.ext
    rw [← h1, smT_left, Over.comp_left, hy c, ← (hTan c).2]
    simp only [gA, Over.homMk_left]
    rw [← Category.assoc, spMap_comp', hr0, spMap_comp, Category.assoc]
  · obtain ⟨g'', V, h1, h2, h3⟩ := hw
    obtain ⟨u, hu, hprod⟩ := hComb
    have hg'' : g'' = g' := Over.OverMorphism.ext (h1.trans hg'.symm)
    let bA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ tEpsG (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap (dualMap φ)) (by
        show spMap (dualMap φ) ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U =
          spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, ← Category.assoc, spMap_comp', hra, spMap_comp, Category.assoc])
    have hV : V = bA ≫ (List.ofFn u).prod := by
      apply Over.OverMorphism.ext
      rw [h2, Over.comp_left, hprod]
      rfl
    have hbAu : ∀ c, bA ≫ u c = smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c) := by
      intro c
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu c, smT_left, hy c]
      simp only [bA, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
    rw [← h3, hg'', hV, comp_list_prod]
    simp only [hbAu]

end GlobalTheory.LogKSDiv
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_tangent_combination_eq_prod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  atlas_forward_decl GlobalTheory.LogKSDiv.translate_comb
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.KSFrameChange

theorem sum_four_comm {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ b, ∑ y, ∑ x, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ x, F a b x y := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, ∑ b, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ a, ∑ b, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_comm' {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ b, ∑ a, F a b x y :=
  (sum_four_comm F).trans Finset.sum_comm

theorem isKS_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  intro E _ _ _ H X t V U n n' v v' B D Θ hv hv' hB hKS
  obtain ⟨J, W, j, d, hcov, hWL, hF, hD, hc⟩ := hKS
  refine ⟨J, W, j, d, hcov, hWL, hF, hD, ?_⟩
  intro i i' O hO f S _ φ g₀ w' hg hgO htr'
  choose w hw using fun a => (GlobalTheory.LogKS.existsUnique_isTranslate t φ hg (hv a)).exists
  rw [hc i i' O hO f S φ g₀ w hg hgO hw]
  let g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  choose gc yc hgc hyc hwc using htr'
  have hgc' : ∀ c, gc c = g' := fun c => Over.OverMorphism.ext (hgc c)
  have key : ∀ a (O' : t.G.left.Opens) (f' : Γ(t.G.left, O')), ⊤ ≤ g₀ ⁻¹ᵁ O' →
      (valR (w a) O' f').snd = ∑ c, φ (B a c) * (valR (w' c) O' f').snd := by
    intro a O' f' hO'
    obtain ⟨h0, hw'⟩ := GlobalTheory.T.translate_tangent_combination_eq_prod t U v' (B a) (v a) φ g₀ hg g' yc hv' (hB a) rfl hyc
    rw [hw' (w a) (hw a), GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear (g₀ ≫ t.G.hom) t.G g₀ g' rfl yc (fun c => φ (B a c)) h0 O' f' hO']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hwc c, hgc' c]
  simp_rw [key _ O f hgO]
  have hO2 : ⊤ ≤ g₀ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) :=
    hgO.trans (fun x hx => (hO.trans (inf_le_inf (hWL i) (hWL i'))) hx)
  simp_rw [key _ _ _ hO2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KSFrameChange
end
end
