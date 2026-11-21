import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormula
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransform
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitsMulRelationRearrangeCommRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestriction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiff

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace PositivityTheory.HtPt.Qam.CoreP

section Gen
variable {X Y Y' : Scheme.{0}}

def trU (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) : Γ(Y, V)ˣ :=
  Units.map (a.appLE _ V hA).hom.toMonoidHom (L.g j j') *
    (Units.map (b.appLE _ V hB).hom.toMonoidHom (L.g j j'))⁻¹

theorem trU_pull (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (h : Y' ⟶ Y) (V' : Y'.Opens) (hV : V' ≤ h ⁻¹ᵁ V)
    (hA' : V' ≤ (h ≫ a) ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB' : V' ≤ (h ≫ b) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    Units.map (h.appLE V V' hV).hom.toMonoidHom (trU L a b j j' V hA hB) =
      trU L (h ≫ a) (h ≫ b) j j' V' hA' hB' := by
  have e : ∀ (c : Y ⟶ X) (hC : V ≤ c ⁻¹ᵁ (L.U j ⊓ L.U j')) (hC' : V' ≤ (h ≫ c) ⁻¹ᵁ (L.U j ⊓ L.U j')),
      Units.map (h.appLE V V' hV).hom.toMonoidHom (Units.map (c.appLE _ V hC).hom.toMonoidHom (L.g j j')) =
        Units.map ((h ≫ c).appLE _ V' hC').hom.toMonoidHom (L.g j j') := by
    intro c hC hC'
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    have := Scheme.Hom.appLE_comp_appLE h c _ V V' hC hV
    exact congrArg (fun q => q.hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) this
  rw [trU, trU, map_mul, map_inv, e a hA hA', e b hB hB']

theorem trU_pull' (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (h : Y' ⟶ Y) (V' : Y'.Opens) (hV : V' ≤ h ⁻¹ᵁ V) (a' b' : Y' ⟶ X) (ea : h ≫ a = a') (eb : h ≫ b = b')
    (hA' : V' ≤ a' ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB' : V' ≤ b' ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    Units.map (h.appLE V V' hV).hom.toMonoidHom (trU L a b j j' V hA hB) = trU L a' b' j j' V' hA' hB' := by
  subst ea eb
  exact trU_pull L a b j j' V hA hB h V' hV hA' hB'

theorem res_value_compose {U U₁ U₂ V : Y.Opens} (h₁ : U₁ ≤ U) (h₂ : V ≤ U₁) (h₃ : U₂ ≤ U) (h₄ : V ≤ U₂) (s : Γ(Y, U)ˣ) :
    (res h₂ (res h₁ s)).val =
      (Y.presheaf.map (homOfLE h₄).op).hom ((Y.presheaf.map (homOfLE h₃).op).hom s.val) := by
  have e : Y.presheaf.map (homOfLE h₁).op ≫ Y.presheaf.map (homOfLE h₂).op =
      Y.presheaf.map (homOfLE h₃).op ≫ Y.presheaf.map (homOfLE h₄).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun q => q.hom s.val) e

theorem trU_congr (L : LB X) (a : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA hB : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) : trU L a a j j' V hA hB = 1 :=
  mul_inv_cancel _

theorem res_res_pull (c : Y ⟶ X) (O : X.Opens) (W V : Y.Opens) (h₂ : W ≤ c ⁻¹ᵁ O) (h₃ : V ≤ W)
    (hC : V ≤ c ⁻¹ᵁ O) (u : Γ(X, O)ˣ) :
    res h₃ (res h₂ (pullU c O u)) = Units.map (c.appLE O V hC).hom.toMonoidHom u := by
  have e : c.app O ≫ Y.presheaf.map (homOfLE h₂).op ≫ Y.presheaf.map (homOfLE h₃).op =
      c.appLE O V hC := by
    rw [← Functor.map_comp]
    rfl
  ext
  exact congrArg (fun q => q.hom (u : Γ(X, O))) e

theorem linComb_g (L : LB X) (a b : Y ⟶ X) (m : ℤ) (j j' : L.ι) (V : Y.Opens)
    (hV : V ≤ (LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).U (fun _ => j'))
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    res hV ((LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).g (fun _ => j) (fun _ => j')) =
      trU L a b j j' V hA hB ^ m := by
  show res hV (∏ k : Fin 2, (res _ (pullU (![a, b] k) _ (L.g j j'))) ^ (![m, -m] k)) = _
  rw [Fin.prod_univ_two, map_mul, map_zpow, map_zpow]
  have ea := res_res_pull a _ _ V (le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] (fun _ => j) 0))
      (inf_le_right.trans (LB.wchart_le L ![a, b] (fun _ => j') 0)) :
        LB.wchart L ![a, b] (fun _ => j) ⊓ LB.wchart L ![a, b] (fun _ => j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) hV hA (L.g j j')
  have eb := res_res_pull b _ _ V (le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] (fun _ => j) 1))
      (inf_le_right.trans (LB.wchart_le L ![a, b] (fun _ => j') 1)) :
        LB.wchart L ![a, b] (fun _ => j) ⊓ LB.wchart L ![a, b] (fun _ => j') ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) hV hB (L.g j j')
  erw [ea, eb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [trU, mul_zpow, inv_zpow, zpow_neg]

end Gen

section Thick
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem dltOn_res (m : ℕ) {V V' : (Ym G x m).Opens} (h : V' ≤ V) :
    ((Ym G x m).presheaf.map (homOfLE h).op).hom (dltOn G x m V) = dltOn G x m V' := by
  rw [dltOn, dltOn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sum_res (m : ℕ) {W W' : (pullback G.hom x).Opens} (h : W' ≤ W) (h' : prZ G x m ⁻¹ᵁ W' ≤ prZ G x m ⁻¹ᵁ W)
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    ((Ym G x m).presheaf.map (homOfLE h').op).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) =
      ∑ i, ((prZ G x m).app W').hom (((pullback G.hom x).presheaf.map (homOfLE h).op).hom (c i)) *
        dltOn G x m _ ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, dltOn_res]
  congr 1
  have := (prZ G x m).naturality (homOfLE h).op
  exact (congrArg (fun q => q.hom (c i)) this).symm

theorem sum_pull (m : ℕ) {Y' : Scheme.{0}} (g : Y' ⟶ Ym G x m) (π' : Y' ⟶ pullback G.hom x)
    (e : g ≫ prZ G x m = π') (δ' : Γ(Y', ⊤)) (eδ : (g.appTop).hom (dlt G x m) = δ')
    (W : (pullback G.hom x).Opens) (V' : Y'.Opens) (hV : V' ≤ g ⁻¹ᵁ (prZ G x m ⁻¹ᵁ W)) (hV' : V' ≤ π' ⁻¹ᵁ W)
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) =
      ∑ i, (π'.appLE W V' hV').hom (c i) * ((Y'.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom δ') ^ (i : ℕ) := by
  subst e
  subst eδ
  have e1 : ∀ i, (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (((prZ G x m).app W).hom (c i)) =
      ((g ≫ prZ G x m).appLE W V' hV').hom (c i) := by
    intro i
    have := Scheme.Hom.appLE_comp_appLE g (prZ G x m) W _ V' (le_refl _) hV
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact congrArg (fun q => q.hom (c i)) this
  have e2 : (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (dltOn G x m _) =
      (Y'.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom ((g.appTop).hom (dlt G x m)) := by
    have h1 := Scheme.Hom.map_appLE g hV (homOfLE (le_top : prZ G x m ⁻¹ᵁ W ≤ ⊤)).op
    exact congrArg (fun q => q.hom (dlt G x m)) h1
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, e1, e2]

theorem id_appLE' {Z : Scheme.{0}} (W : Z.Opens) (h : W ≤ (𝟙 Z : Z ⟶ Z) ⁻¹ᵁ W) :
    (𝟙 Z : Z ⟶ Z).appLE W W h = 𝟙 _ := by
  exact (Category.id_comp _).trans ((congrArg Z.presheaf.map (Subsingleton.elim _ _)).trans (Z.presheaf.map_id _))

theorem sec_sum (m : ℕ) (W : (pullback G.hom x).Opens) (h : W ≤ secZ G x m ⁻¹ᵁ (prZ G x m ⁻¹ᵁ W))
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    ((secZ G x m).appLE _ W h).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) = c 0 := by
  rw [sum_pull G x m (secZ G x m) (𝟙 _) (secZ_prZ G x m) 0 (secZ_dlt G x m) W W h le_rfl c]
  rw [Fin.sum_univ_succ]
  simp only [map_zero, ne_eq, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, _root_.mul_one]
  exact congrArg (fun q => q.hom (c 0)) (id_appLE' W _)

theorem sum_trunc {R : Type*} [CommRing R] (d : R) (hd : d ^ 2 = 0) (p : ℕ) (hp : 1 ≤ p) (c : Fin (p + 1) → R) :
    ∑ i, c i * d ^ (i : ℕ) = c 0 + c ⟨1, by omega⟩ * d := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have : ∀ i : Fin q, c i.succ.succ * d ^ ((i.succ.succ : Fin (q + 1 + 1)) : ℕ) = 0 := by
    intro i
    simp only [Fin.val_succ]
    rw [show (i : ℕ) + 1 + 1 = i + 2 from rfl, pow_add, hd, mul_zero, mul_zero]
  simp only [this, Finset.sum_const_zero, add_zero]
  simp

theorem dltOn_pow (m : ℕ) (V : (Ym G x m).Opens) : dltOn G x m V ^ (m + 1) = 0 := by
  rw [dltOn, ← map_pow, dlt_pow, map_zero]

theorem tr_sum (p : ℕ) (hp : 1 ≤ p) (W : (pullback G.hom x).Opens)
    (h : prZ G x 1 ⁻¹ᵁ W ≤ trY G x p hp ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (c : Fin (p + 1) → Γ(pullback G.hom x, W)) :
    ((trY G x p hp).appLE _ _ h).hom (∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ)) =
      ((prZ G x 1).app W).hom (c 0) + ((prZ G x 1).app W).hom (c ⟨1, by omega⟩) * dltOn G x 1 _ := by
  rw [sum_pull G x p (trY G x p hp) (prZ G x 1) (trY_prZ G x p hp) (dlt G x 1) (trY_dlt G x p hp) W _ h le_rfl c]
  have := sum_trunc (dltOn G x 1 (prZ G x 1 ⁻¹ᵁ W)) (dltOn_pow G x 1 _) p hp
    (fun i => ((prZ G x 1).app W).hom (c i))
  simp only [Scheme.Hom.app_eq_appLE] at this ⊢
  exact this

theorem cast_p (m : ℕ) (V : (Ym G x m).Opens) (p : ℕ) [CharP k p] : ((p : ℕ) : Γ(Ym G x m, V)) = 0 := by
  let ψ : k →+* Γ(Ym G x m, V) := ((Ym G x m).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
    (((fst (Tm x m) G).left.appTop).hom.comp ((toΓ (Jet k Unit m)).comp (algebraMap k (Jet k Unit m))))
  have := map_natCast ψ p
  rw [CharP.cast_eq_zero k p, map_zero] at this
  exact this.symm

theorem base_eq (p : ℕ) (a : Ym G x p ⟶ G.left) (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (y : Ym G x p) : a y = (prZ G x p ≫ pullback.fst G.hom x) y := by
  obtain ⟨z, rfl⟩ := GlobalTheory.T.zero_section_surjective X0 G k x p y
  have e : secZ G x p ≫ prZ G x p ≫ pullback.fst G.hom x = pullback.fst G.hom x := by
    rw [← Category.assoc, secZ_prZ, Category.id_comp]
  have h1 := congrArg (fun q : pullback G.hom x ⟶ G.left => q z) (ha.trans e.symm)
  simpa using h1

end Thick

section Main
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (p : ℕ)
  (L : LB G.left) (a : Ym G x p ⟶ G.left)

theorem le_pre (ha : secZ G x p ≫ a = pullback.fst G.hom x) (O : G.left.Opens) :
    prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ O) ≤ a ⁻¹ᵁ O := by
  intro y hy
  show a y ∈ O
  rw [base_eq G x p a ha]
  exact hy

theorem le_chart (ha : secZ G x p ≫ a = pullback.fst G.hom x) (m : ℤ) (j : L.ι) :
    prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j) ≤
      (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![m, -m]).U (fun _ => j) := by
  intro y hy
  refine Set.mem_iInter.2 fun q => ?_
  fin_cases q
  · exact le_pre G x p a ha (L.U j) hy
  · exact hy

theorem le_sec (W : (pullback G.hom x).Opens) : W ≤ secZ G x p ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W) := by
  intro z hz
  show (secZ G x p ≫ prZ G x p) z ∈ W
  rw [secZ_prZ]
  exact hz

theorem chart_coef (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![(p : ℤ), -(p : ℤ)]))
    (hn : ∀ (j : L.ι) (h : pullback.fst G.hom x ⁻¹ᵁ L.U j ≤ secZ G x p ⁻¹ᵁ
        LB.wchart L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] (fun _ => j)),
      ((secZ G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) (j : L.ι) :
    ∃ c : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j),
      ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val =
        ∑ i, ((prZ G x p).app _).hom (c i) * dltOn G x p _ ^ (i : ℕ) ∧ c 0 = 1 := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _
    (((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val)
  refine ⟨c, hc, ?_⟩
  have hs := le_sec G x p (pullback.fst G.hom x ⁻¹ᵁ L.U j)
  rw [← sec_sum G x p _ hs c, ← hc]
  have h2 := Scheme.Hom.map_appLE (secZ G x p) hs (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op
  exact (congrArg (fun q => q.hom (C.s fun _ => j).val) h2).trans (hn j _)

theorem tr_coef (ha : secZ G x p ≫ a = pullback.fst G.hom x) (j j' : L.ι)
    (hA : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    ∃ u : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'),
      (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val =
        ∑ i, ((prZ G x p).app _).hom (u i) * dltOn G x p _ ^ (i : ℕ) ∧ u 0 = 1 := by
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _ (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val
  refine ⟨u, hu, ?_⟩
  have hs := le_sec G x p (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')
  rw [← sec_sum G x p _ hs u, ← hu]
  have e : secZ G x p ≫ prZ G x p ≫ pullback.fst G.hom x = pullback.fst G.hom x := by
    rw [← Category.assoc, secZ_prZ, Category.id_comp]
  have h1 := trU_pull' L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB (secZ G x p) _ hs
    (pullback.fst G.hom x) (pullback.fst G.hom x) ha e le_rfl le_rfl
  exact congrArg Units.val (h1.trans (trU_congr _ _ _ _ _ _ _))

theorem overlap [Fact p.Prime] [CharP k p] (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![(p : ℤ), -(p : ℤ)]))
    (hC : C.IsGen) (j j' : L.ι)
    (c₁ : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j))
    (c₂ : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (h₁ : ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val =
        ∑ i, ((prZ G x p).app _).hom (c₁ i) * dltOn G x p _ ^ (i : ℕ))
    (h₂ : ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j')).op).hom (C.s fun _ => j').val =
        ∑ i, ((prZ G x p).app _).hom (c₂ i) * dltOn G x p _ ^ (i : ℕ))
    (e₁ : c₁ 0 = 1) (e₂ : c₂ 0 = 1)
    (hA : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (u : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (hu : (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val =
        ∑ i, ((prZ G x p).app _).hom (u i) * dltOn G x p _ ^ (i : ℕ)) (u₀ : u 0 = 1) :
    ((pullback G.hom x).presheaf.map (homOfLE inf_le_left).op).hom (c₁ (Fin.last p)) =
      ((pullback G.hom x).presheaf.map (homOfLE inf_le_right).op).hom (c₂ (Fin.last p)) +
        u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  have i₁ : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j) := fun _ hy => hy.1
  have i₂ : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j') := fun _ hy => hy.2
  have hV := le_inf (i₁.trans (le_chart G x p L a ha (p : ℤ) j)) (i₂.trans (le_chart G x p L a ha (p : ℤ) j'))
  have hg := congrArg (res hV) (hC (fun _ => j) (fun _ => j'))
  rw [map_mul, linComb_g L a _ (p : ℤ) j j' _ hV hA hB, zpow_natCast] at hg
  have hg' := congrArg Units.val hg
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    res_value_compose _ _ (le_chart G x p L a ha (p : ℤ) j) i₁, res_value_compose _ _ (le_chart G x p L a ha (p : ℤ) j') i₂, h₁, h₂, hu,
    sum_res G x p inf_le_left i₁, sum_res G x p inf_le_right i₂] at hg'
  refine GlobalTheory.T.truncated_expansion_pth_power_coeff _ _ ((prZ G x p).app _).hom (dltOn G x p _) p (cast_p G x _ _ p) (dltOn_pow G x p _)
    ?_ u _ _ u₀ ?_ ?_ hg'
  · intro c c' e
    exact (GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _ _).unique rfl e
  · rw [e₁, map_one]
  · rw [e₂, map_one]

def tU (W : (pullback G.hom x).Opens) (s : Γ(pullback G.hom x, W)) : Γ(Ym G x 1, prZ G x 1 ⁻¹ᵁ W)ˣ where
  val := 1 + dltOn G x 1 _ * ((prZ G x 1).app W).hom s
  inv := 1 - dltOn G x 1 _ * ((prZ G x 1).app W).hom s
  val_inv := by
    linear_combination (-(((prZ G x 1).app W).hom s) ^ 2) * dltOn_pow G x 1 (prZ G x 1 ⁻¹ᵁ W)
  inv_val := by
    linear_combination (-(((prZ G x 1).app W).hom s) ^ 2) * dltOn_pow G x 1 (prZ G x 1 ⁻¹ᵁ W)

theorem tU_res {W W' : (pullback G.hom x).Opens} (h : W' ≤ W) (h' : prZ G x 1 ⁻¹ᵁ W' ≤ prZ G x 1 ⁻¹ᵁ W)
    (s : Γ(pullback G.hom x, W)) :
    (res h' (tU G x W s)).val = 1 + dltOn G x 1 _ *
      ((prZ G x 1).app W').hom (((pullback G.hom x).presheaf.map (homOfLE h).op).hom s) := by
  show ((Ym G x 1).presheaf.map (homOfLE h').op).hom (1 + dltOn G x 1 _ * ((prZ G x 1).app W).hom s) = _
  rw [map_add, map_one, map_mul, dltOn_res]
  congr 2
  have := (prZ G x 1).naturality (homOfLE h).op
  exact (congrArg (fun q => q.hom s) this).symm

theorem pullU_eq {X Y : Scheme.{0}} (b : Y ⟶ X) (O : X.Opens) (u : Γ(X, O)ˣ) (h : b ⁻¹ᵁ O ≤ b ⁻¹ᵁ O) :
    pullU b O u = Units.map (b.appLE O _ h).hom.toMonoidHom u := by
  ext
  show (b.app O).hom u.val = (b.appLE O _ h).hom u.val
  rw [Scheme.Hom.app_eq_appLE]

theorem ring_step {R : Type*} [CommRing R] (d S S' : R) (h : d ^ (1 + 1) = 0) :
    1 + d * S = (1 + (S - S') * d) * (1 + d * S') := by
  linear_combination (-(S - S') * S') * h

theorem second (hp : 1 ≤ p) (hL : L.IsLB) (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (s : ∀ j, Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j))
    (cu : ∀ j j', Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (hA : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hcu : ∀ j j', (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ (hA j j') (hB j j')).val =
        ∑ i, ((prZ G x p).app _).hom (cu j j' i) * dltOn G x p _ ^ (i : ℕ))
    (h0 : ∀ j j', cu j j' 0 = 1)
    (h1 : ∀ j j', cu j j' ⟨1, by omega⟩ =
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (s j) -
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (s j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![trY G x p hp ≫ a, trY G x p hp ≫ prZ G x p ≫ pullback.fst G.hom x] ![1, -1]),
      c.IsGen := by
  have e : trY G x p hp ≫ prZ G x p ≫ pullback.fst G.hom x = prZ G x 1 ≫ pullback.fst G.hom x := by
    rw [← Category.assoc, trY_prZ]
  rw [e]
  refine GlobalTheory.T.line_bundle_cocycle_pullback_transform _ _ L hL _ _ ?_ (fun j => tU G x _ (s j)) ?_
  · intro y
    have h := base_eq G x p a ha (trY G x p hp y)
    have h' := congrArg (fun q : Ym G x 1 ⟶ G.left => q y) e
    simp only [Scheme.Hom.comp_apply] at h h' ⊢
    rw [h, h']
  · intro j j' h
    have hs : prZ G x 1 ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
        trY G x p hp ⁻¹ᵁ (prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')) := by
      intro y hy
      show (trY G x p hp ≫ prZ G x p) y ∈ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')
      rw [trY_prZ]
      exact hy
    have hU := trU_pull' L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ (hA j j') (hB j j') (trY G x p hp) _ hs
      (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) rfl e h le_rfl
    have hv := congrArg Units.val hU
    have hv' : (trU L (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) j j'
        (prZ G x 1 ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')) h le_rfl).val =
        ((prZ G x 1).app _).hom (cu j j' 0) + ((prZ G x 1).app _).hom (cu j j' ⟨1, by omega⟩) * dltOn G x 1 _ := by
      rw [← hv, ← tr_sum G x p hp _ hs, ← hcu]
      rfl
    rw [h0, h1, map_one, map_sub] at hv'
    have hT : Units.map ((trY G x p hp ≫ a).appLE _ _ h).hom.toMonoidHom (L.g j j') *
        (pullU (prZ G x 1 ≫ pullback.fst G.hom x) _ (L.g j j'))⁻¹ =
        trU L (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) j j' _ h le_rfl := by
      rw [pullU_eq _ _ _ le_rfl]
      rfl
    rw [hT]
    have t₁ := tU_res G x (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _) (fun _ hy => hy.1) (s j)
    have t₂ := tU_res G x (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _) (fun _ hy => hy.2) (s j')
    ext
    refine t₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) hv'.symm t₂.symm))
    exact ring_step _ _ _ (dltOn_pow G x 1 _)

end Main
end PositivityTheory.HtPt.Qam.CoreP

namespace PositivityTheory.HtPt.Qam

open CoreP in

theorem core_firstOrder : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) [IsIntegral (pullback G.hom x)] [CharP (pullback G.hom x).functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback G.hom x) → ∀ (L : LB G.left), L.IsLB → ∀ (a b : Ym G x p ⟶ G.left), b = prZ G x p ≫ pullback.fst G.hom x → secZ G x p ≫ a = pullback.fst G.hom x → ∀ (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![(p : ℤ), -(p : ℤ)])), C.IsGen → (∀ (j : L.ι) (h : pullback.fst G.hom x ⁻¹ᵁ L.U j ≤ secZ G x p ⁻¹ᵁ LB.wchart L (K := Fin 2) ![a, b] (fun _ => j)), ((secZ G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) → ∀ (j₀ : L.ι) [Nonempty (pullback.fst G.hom x ⁻¹ᵁ L.U j₀)], (∀ (c : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j₀)) (h : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j₀) ≤ LB.wchart L (K := Fin 2) ![a, b] (fun _ => j₀)), ((Ym G x p).presheaf.map (homOfLE h).op).hom (C.s fun _ => j₀).val = ∑ i, ((prZ G x p).app _).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∃ r : (pullback G.hom x).functionField, r ^ p = ((pullback G.hom x).germToFunctionField _).hom (c (Fin.last p))) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![trY G x p hp ≫ a, trY G x p hp ≫ b] ![1, -1]), c.IsGen := by
  intro X0 G k _ x p _ _ hp _ _ hZ L hL a b hb ha C hC hn j₀ _ hr
  subst hb
  choose cf hcf hcf0 using chart_coef G x p L a ha C hn
  have hA : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      a ⁻¹ᵁ (L.U j ⊓ L.U j') := fun j j' => le_pre G x p a ha (L.U j ⊓ L.U j')
  have hB : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j') := fun _ _ _ hy => hy
  choose cu hcu hcu0 using fun j j' => tr_coef G x p L a ha j j' (hA j j') (hB j j')
  have hnp : ∀ j j', cu j j' ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p =
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (cf j (Fin.last p)) -
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (cf j' (Fin.last p)) := by
    intro j j'
    rw [overlap G x p L a ha C hC j j' (cf j) (cf j') (hcf j) (hcf j') (hcf0 j) (hcf0 j') (hA j j') (hB j j')
      (cu j j') (hcu j j') (hcu0 j j')]
    ring
  obtain ⟨r, hr'⟩ := hr (cf j₀) (le_chart G x p L a ha (p : ℤ) j₀) (hcf j₀)
  obtain ⟨s, hs⟩ := GlobalTheory.T.artin_schreier_cocycle_root (pullback G.hom x) p hZ L.ι (fun j => pullback.fst G.hom x ⁻¹ᵁ L.U j)
    (fun j j' => cu j j' ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩) (fun j => cf j (Fin.last p)) j₀ hnp ⟨r, hr'⟩
  exact second G x p L a hp hL ha s cu hA hB hcu hcu0 hs

end PositivityTheory.HtPt.Qam
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cocp

theorem cocycle_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), alpha g.B p (fun i => w i ^ p) = 0 → ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G))), c.IsGen := by
  intro E _ _ _ H _ hstar X0 t k _ _ p _ _ hp x d g w hα
  obtain ⟨hy0, hy1, -⟩ := PositivityTheory.HtPt.Ce.pt_of_vec E H hstar X0 t k p hp x d g w
  have hwv : (hw g.B p).mulVec (fun i => w i ^ p) = 0 := by
    have := congrArg Prod.fst hα
    rwa [alpha_apply] at this
  have hyp := hy1 hwv
  obtain ⟨gs, hax, hpow, -⟩ := GlobalTheory.T.pow_one_series_p_formula k p d (𝓞 E) g.B
  have hkill := GlobalTheory.T.alpha_kernel_derivative_vanishes k p d (𝓞 E) g.B (fun i => w i ^ p) gs hα hpow
  have hf : ∀ q, MvPowerSeries.pderiv k q (dSer gs fun i => w i ^ p) = 0 := by
    rintro ⟨i, j⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hkill j
  obtain ⟨hI, hN, hCh, hT⟩ := GlobalTheory.T.formal_germ_jet_lift E H hstar X0 t k p x d g (fun m => xkZ t.G x (g.x m))
    (fun m => xkZ_fst t.G x _) (fun m => xkZ_snd t.G x _)
  obtain ⟨C, hC, hnorm, hB⟩ := GlobalTheory.CompanionTheory.Ar.Coc.Pf.pfold E H hstar X0 t k p x d g w gs hax hpow _ rfl hy0 hyp
  have hL := t.PP.isLB
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨s⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ := by
    have hc := hL.cover
    have : (1 : overAt x k ⟶ t.G).left s ∈ (⊤ : t.G.left.Opens) := trivial
    rw [← hc] at this
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    refine ⟨j, fun s' _ => ?_⟩
    have e : s' = s := Subsingleton.elim (α := Sp k) _ _
    rw [e]
    exact hj
  have hU : ∀ m, ⊤ ≤ xkZ t.G x (g.x m) ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) := by
    intro m q _
    have e : (homAt x (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ g.x m).left = (1 : overAt x k ⟶ t.G).left :=
      congrArg (fun q => q.left) (g.chart.zero m)
    have e₁ : pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) = (g.x m).left q := by
      rw [← Scheme.Hom.comp_apply, xkZ_fst]
    have e₂ : (g.x m).left q = (1 : overAt x k ⟶ t.G).left s := by
      rw [← jet_pt m q s, ← e]
      rfl
    change pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) ∈ t.PP.L.U j₀
    rw [e₁, e₂]
    exact hj₀ trivial
  haveI : Nonempty (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) :=
    ⟨⟨_, hU 0 (show (spMap ((jetAug : Jet k (Fin 1 × Fin d) 0 →ₐ[k] k) : Jet k (Fin 1 × Fin d) 0 →+* k) s) ∈ ⊤ from trivial)⟩⟩
  have main := PositivityTheory.HtPt.Qam.core_firstOrder X0 t.G k x p hp hN t.PP.L hL _ _ (prZ_fst t.G x p).symm (secZ_pa t.G x _ hy0) C hC hnorm j₀
    (fun c h hc => by
      obtain ⟨F, hF1, -, hF3⟩ := hT _ hU (c (Fin.last p))
      refine hF3 (GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff k p d F _ hf fun m => ?_)
      obtain ⟨v, hv⟩ := hB j₀ hj₀ m
      refine ⟨v, ?_⟩
      have hr : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ (prZ t.G x p ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)) := by
        intro q _
        have e : prZ t.G x p (rQ t.G x p (g.x m) q) = xkZ t.G x (g.x m)
            (spMap ((inR (k := k) (Jet k (Fin 1 × Fin d) m) p : Jet k (Fin 1 × Fin d) m →ₐ[k] Jet (Jet k (Fin 1 × Fin d) m) Unit p) : Jet k (Fin 1 × Fin d) m →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) q) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, rQ_prZ]
        change prZ t.G x p (rQ t.G x p (g.x m) q) ∈ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)
        rw [e]
        exact hU m trivial
      have hr' : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![_, _] (fun _ => j₀) :=
        hr.trans fun q hq => h hq
      have h2 := GlobalTheory.T.delta_expansion_restriction X0 t.G k x p hp _ (g.x m) _ (hU m) c _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) hc hr (by
        rw [← hv hr']
        exact congrArg (fun q => q.hom (C.s fun _ => j₀).val) (Scheme.Hom.map_appLE (rQ t.G x p (g.x m)) hr (homOfLE h).op))
      exact toΓ_inj _ ((hF1 m).symm.trans h2))
  rw [trY_pa, trY_pb] at main
  exact main

theorem tanpf_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p :=
  PositivityTheory.HtPt.Ce.tanpf_inj_of cocycle_p

end PositivityTheory.HtPt.Cocp
end
