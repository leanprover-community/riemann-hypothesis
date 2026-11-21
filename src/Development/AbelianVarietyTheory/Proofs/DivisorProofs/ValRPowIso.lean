import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPrj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseChRig

theorem valR_map {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom s) = valR x U s := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => h (hV hq)
  unfold valR
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE x hV (homOfLE h).op]
  rfl

theorem valR_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : Γ(X, U)) :
    valR x (g ⁻¹ᵁ U) ((g.app U).hom s) = valR (x ≫ g) U s := by
  have hU' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := hU
  unfold valR
  rw [dif_pos hU, dif_pos hU', Scheme.Hom.comp_appLE]
  rfl

theorem valR_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valR (spMap f ≫ x) U s = f (valR x U s) := by
  have hU' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun q _ => hU (Set.mem_univ _)
  unfold valR
  rw [dif_pos hU, dif_pos hU']
  have e : (spMap f ≫ x).appLE U ⊤ hU' = x.appLE U ⊤ hU ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e]
  exact congrArg (fun φ => φ.hom ((x.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s t : Γ(X, U)) : valR x U (s * t) = valR x U s * valR x U t := by
  unfold valR
  simp only [dif_pos hU, map_mul]

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) : valR x U (s ^ n) = valR x U s ^ n := by
  unfold valR
  simp only [dif_pos hU, map_pow]

theorem valR_gen {A : Type} [CommRing A] {X : Scheme.{0}} (L : LB X) (e : Sp A ⟶ X) (r : (L.pull e).Gen)
    (hr : r.IsGen) (j i : L.ι) (hj : ⊤ ≤ e ⁻¹ᵁ L.U j) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) :
    valR (𝟙 _) _ (r.s fun _ => j).val = valR e _ (L.g j i).val * valR (𝟙 _) _ (r.s fun _ => i).val := by
  have hB : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ ((L.pull e).U (fun _ => j) ⊓ (L.pull e).U (fun _ => i)) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hj hq, Set.mem_iInter.2 fun _ => hi hq⟩
  have h := congrArg (fun v => valR (𝟙 (Sp A)) _ (Units.val v)) (hr (fun _ => j) (fun _ => i))
  replace h := h.trans (valR_mul' _ hB _ _)
  refine (valR_map _ _ hB _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (valR_map _ _ hB _)))
  show valR _ _ (Units.val (∏ _k : PUnit, (res _ (pullU e _ (L.g j i))) ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (valR_map _ _ hB _).trans ((valR_app (𝟙 _) e (U := L.U j ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _).trans ?_)
  rw [Category.id_comp]



end GlobalTheory.MBLow.BaseChRig
