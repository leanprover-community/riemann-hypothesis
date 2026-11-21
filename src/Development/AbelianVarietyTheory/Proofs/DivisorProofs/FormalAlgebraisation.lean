import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingCom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleCompatibleSectionsThickeningTower

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.CancelPow

variable {X Y : Scheme.{0}}

theorem pw_tw (M H : LB X) (t a : ℤ) : AbLaw.pw (tw M H t) a = tw (AbLaw.pw M a) H (t * a) := by
  have : (AbLaw.pw (tw M H t) a).g = (tw (AbLaw.pw M a) H (t * a)).g := by
    funext p q
    change (res _ (M.g p.1 q.1) * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹) ^ a =
      res _ (M.g p.1 q.1 ^ a) * (res _ (H.g p.2 q.2 ^ (-(t * a))))⁻¹
    simp only [map_zpow, map_inv, zpow_neg, inv_inv, zpow_mul]
    exact mul_zpow _ _ _
  exact congrArg (fun g => (⟨(tw M H t).ι, (tw M H t).U, g⟩ : LB X)) this

theorem lbIso_tw_congr_right {A H H' : LB X} (hA : A.IsLB) (t : ℤ) (h : LBIso H H') :
    LBIso (tw A H t) (tw A H' t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ A.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ H'.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (A.ι × H'.ι) × (A.ι × H.ι)), x ∈ (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1 p.2.1) * gm (𝟙 X) x (H'.U p.1.2 ⊓ H.U p.2.2) (w.s (p.1.2, p.2.2)) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (GlobalTheory.LBAlg.gm_tw A H' t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (GlobalTheory.LBAlg.gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [GlobalTheory.LBAlg.germs_of_isGen hw x (p.1.2, p.2.2) (q.1.2, q.2.2) h₁.2 h₂.2 h₃.2 h₄.2,
    ← gm_cocycle hA (𝟙 X) x h₁.1 h₂.1 h₃.1, ← gm_cocycle hA (𝟙 X) x h₂.1 h₃.1 h₄.1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem cancel_pw : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  refine ⟨fun X Y b H M N a hH hM hN e₁ e₂ => ?_, fun X H M a hH hM e => ?_⟩
  · have hP : (M.pull b).IsLB := pull_isLB hM b
    have hQ : (H.pull b).IsLB := pull_isLB hH b
    have k₁ : LBIso N (tw (tw N (H.pull b) 1) (H.pull b) (-1)) := GlobalTheory.LBAlg.lbIso_tw_tw hN hQ 1
    have k₂ : LBIso (tw N (H.pull b) 1) (tw N (AbLaw.pw N a) 1) := lbIso_tw_congr_right hN 1 e₁.symm
    have k₃ : tw N (AbLaw.pw N a) 1 = tw N N a := by
      simp only [tw, GlobalTheory.Algebraise.pw_pw]
      congr 2
      ring
    have k₄ : LBIso (tw N N a) (M.pull b) :=
      LBIso.trans (isLB_tw hN hN a) (isLB_pw hN (a + 1)) hP (GlobalTheory.Algebraise.lbIso_tw hN a).symm e₂
    have k₅ : LBIso (tw N (H.pull b) 1) (M.pull b) :=
      LBIso.trans (isLB_tw hN hQ 1) (isLB_tw hN (isLB_pw hN a) 1) hP k₂ (k₃ ▸ k₄)
    have k₆ : LBIso (tw (tw N (H.pull b) 1) (H.pull b) (-1)) (tw (M.pull b) (H.pull b) (-1)) :=
      GlobalTheory.LBAlg.lbIso_tw_congr hQ (-1) k₅
    have k₇ : LBIso (tw (M.pull b) (H.pull b) (-1)) ((tw M H (-1)).pull b) :=
      LBIso.chartPull (GlobalTheory.LBAlg.chartPullTw (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M b b rfl)
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull H b b rfl) (-1))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (tw M H (-1)) b b rfl) (GlobalTheory.LBAlg.lbIso_self (isLB_tw hM hH (-1)))
    exact LBIso.trans hN (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₁
      (LBIso.trans (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (isLB_tw hP hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₆ k₇)
  · have h₁ : LBIso (tw H H a) (AbLaw.pw M a) :=
      LBIso.trans (isLB_tw hH hH a) (isLB_pw hH (a + 1)) (isLB_pw hM a) (GlobalTheory.Algebraise.lbIso_tw hH a).symm e
    have h₂ : LBIso (tw (tw H H a) H (-a)) (tw (AbLaw.pw M a) H (-a)) := GlobalTheory.LBAlg.lbIso_tw_congr hH (-a) h₁
    have h₃ : AbLaw.pw (tw M H (-1)) a = tw (AbLaw.pw M a) H (-a) := by
      rw [pw_tw]
      congr 1
      ring
    rw [h₃]
    exact LBIso.trans hH (isLB_tw (isLB_tw hH hH a) hH (-a)) (isLB_tw (isLB_pw hM a) hH (-a))
      (GlobalTheory.LBAlg.lbIso_tw_tw hH hH a) h₂

end GlobalTheory.CancelPow
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cancel_powers_of_cech_line_bundles : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  atlas_forward_decl GlobalTheory.CancelPow.cancel_pw
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lb_of_generated_system_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.formalAlgebraisation_morphisms' R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_lb_of_generated_system_proper
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.CrossIso

variable {X Y Z : Scheme.{0}}

theorem gm_pw_g (L : LB X) (t : ℤ) (f : Y ⟶ X) (y : Y) (i j : L.ι) :
    gm f y ((GlobalTheory.AbLaw.pw L t).U i ⊓ (GlobalTheory.AbLaw.pw L t).U j) ((GlobalTheory.AbLaw.pw L t).g i j) =
      gm f y (L.U i ⊓ L.U j) (L.g i j) ^ t :=
  map_zpow (gm f y (L.U i ⊓ L.U j)) (L.g i j) t

theorem gm_pull_g (L : LB X) (F : Y ⟶ X) (f : Z ⟶ Y) (z : Z) (J J' : PUnit → L.ι)
    (hj : F (f z) ∈ L.U (J PUnit.unit)) (hj' : F (f z) ∈ L.U (J' PUnit.unit)) :
    gm f z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f z ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f z _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f z _ hp _).trans
    (gm_pull f F z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem gw_chart {b : Y ⟶ X} {A : LB X} {N : LB Y} {p : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) (k k' : A.ι) (l l' : N.ι) (hk : b (r z) ∈ A.U k) (hk' : b (r z) ∈ A.U k')
    (hl : r z ∈ N.U l) (hl' : r z ∈ N.U l') :
    gw w r z k l = gm (r ≫ b) z _ (A.g k k') * (gm r z _ (N.g l l') ^ p)⁻¹ * gw w r z k' l' := by
  have := (isGen_iff w).1 hw Z r z k k' l l' hk hk' hl hl'
  rw [gm_pw_g] at this
  exact this

theorem cross_alg {G : Type} [CommGroup G] (p q : ℤ) (a a' n u u' : G) :
    (a' * (n ^ q)⁻¹ * u') ^ p * ((a * (n ^ p)⁻¹ * u) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ * (u' ^ p * (u ^ q)⁻¹) := by
  simp only [mul_zpow, inv_zpow, ← zpow_mul, mul_comm q p, mul_inv, inv_inv]
  generalize n ^ (p * q) = m
  generalize a' ^ p = A'
  generalize a ^ q = A
  generalize u' ^ p = U'
  generalize u ^ q = U
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cross_chart {b : Y ⟶ X} {A A' : LB X} {N : LB Y} {p q : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)) (hw : w.IsGen) (hw' : w'.IsGen) (r : Z ⟶ Y) (z : Z)
    (k₁ k₂ : A.ι) (j₁ j₂ : A'.ι) (l₁ l₂ : N.ι) (hk₁ : b (r z) ∈ A.U k₁) (hk₂ : b (r z) ∈ A.U k₂)
    (hj₁ : b (r z) ∈ A'.U j₁) (hj₂ : b (r z) ∈ A'.U j₂) (hl₁ : r z ∈ N.U l₁) (hl₂ : r z ∈ N.U l₂) :
    gw w' r z j₁ l₁ ^ p * (gw w r z k₁ l₁ ^ q)⁻¹ =
      gm (r ≫ b) z _ (A'.g j₁ j₂) ^ p * (gm (r ≫ b) z _ (A.g k₁ k₂) ^ q)⁻¹ *
        (gw w' r z j₂ l₂ ^ p * (gw w r z k₂ l₂ ^ q)⁻¹) := by
  rw [gw_chart w hw r z k₁ k₂ l₁ l₂ hk₁ hk₂ hl₁ hl₂, gw_chart w' hw' r z j₁ j₂ l₁ l₂ hj₁ hj₂ hl₁ hl₂]
  exact cross_alg _ _ _ _ _ _ _

end GlobalTheory.FormalAlg.CrossIso

namespace GlobalTheory.FormalAlg
open CrossIso

theorem exists_crossIso : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  intro X Y b A A' N p q w w' hA hA' hN hw hw'
  have glue : ∀ (j : A'.ι) (k : A.ι), ∃ s : Γ(Y, ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
      ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U j → r z ∈ N.U l →
        gm r z _ s = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ l x, x ∈ W l ↔ b x ∈ A.U k ∧ b x ∈ A'.U j ∧ x ∈ N.U l :=
      ⟨fun l => b ⁻¹ᵁ A.U k ⊓ (b ⁻¹ᵁ A'.U j ⊓ N.U l), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ l, W l ≤ ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
        ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k) := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, mem_pull.2 ((hW l x).1 hx).1⟩
    have l₁ : ∀ l, W l ≤ (A'.pull b).U (fun _ => j) ⊓ (GlobalTheory.AbLaw.pw N q).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, ((hW l x).1 hx).2.2⟩
    have l₂ : ∀ l, W l ≤ (A.pull b).U (fun _ => k) ⊓ (GlobalTheory.AbLaw.pw N p).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).1, ((hW l x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), r z ∈ W l →
        gm r z (W l) (u l) = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ :=
      ⟨fun l => res (l₁ l) (w'.s (fun _ => j, l)) ^ p * (res (l₂ l) (w.s (fun _ => k, l)) ^ q)⁻¹,
        fun Z r z l hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((map_zpow _ _ _).trans (congrArg (· ^ p) (gm_res r z (l₁ l) hy _)))
          ((map_inv _ _).trans (congrArg (·⁻¹)
            ((map_zpow _ _ _).trans (congrArg (· ^ q) (gm_res r z (l₂ l) hy _))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨l, hl⟩ := exists_chart hN x
        exact Opens.mem_iSup.2 ⟨l, (hW l x).2 ⟨mem_pull.1 hx.2, mem_pull.1 hx.1, hl⟩⟩) u (fun l l' x hx => by
        have h₁ := (hW l x).1 hx.1
        have h₂ := (hW l' x).1 hx.2
        have e := cross_chart w w' hw hw' (𝟙 Y) x k k j j l l' h₁.1 h₁.1 h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hA (𝟙 Y ≫ b) x h₁.1, gm_self hA' (𝟙 Y ≫ b) x h₁.2.1, one_zpow, one_zpow, inv_one, one_mul,
          one_mul] at e
        exact (hu _ (𝟙 Y) x l hx.1).trans (e.trans (hu _ (𝟙 Y) x l' hx.2).symm))
    refine ⟨s, fun Z r z l hk hj hl => ?_⟩
    have hy := (hW l (r z)).2 ⟨hk, hj, hl⟩
    exact (gm_res r z (l₀ l) hy s).symm.trans ((congrArg (gm r z (W l)) (hs l)).trans (hu Z r z l hy))
  choose s hs using glue
  let c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b) :=
    ⟨fun P => s (P.1 PUnit.unit) (P.2 PUnit.unit)⟩
  have hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (K : PUnit → A.ι) (j : A'.ι) (l : N.ι),
      b (r z) ∈ A.U (K PUnit.unit) → b (r z) ∈ A'.U j → r z ∈ N.U l →
      gw c r z j K = gw w' r z j l ^ p * (gw w r z (K PUnit.unit) l ^ q)⁻¹ :=
    fun Z r z K j l hk hj hl => hs j (K PUnit.unit) Z r z l hk hj hl
  refine ⟨c, (isGen_iff c).2 ?_, fun Z r z k j l hk hj hl => hc Z r z (fun _ => k) j l hk hj hl⟩
  intro Z r z j j' K K' hj hj' hK hK'
  obtain ⟨l, hl⟩ := exists_chart hN (r z)
  have hk := mem_pull.1 hK
  have hk' := mem_pull.1 hK'
  have e := cross_chart w w' hw hw' r z (K PUnit.unit) (K' PUnit.unit) j j' l l hk hk' hj hj' hl hl
  refine (hc Z r z K j l hk hj hl).trans (e.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw_g A' p _ z j j').symm (congrArg (·⁻¹) ?_))
    (hc Z r z K' j' l hk' hj' hl).symm
  exact ((gm_pull_g (GlobalTheory.AbLaw.pw A q) b r z K K' hk hk').trans (gm_pw_g A q _ z _ _)).symm

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_crossIso
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenAffine

open GeneratorFunctor

set_option backward.isDefEq.respectTransparency false

theorem exists_torus_one (S : Scheme.{0}) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : Γ(T, ⊤)ˣ), IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        g.appTop.hom t.val = v.val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        g.appTop.hom t.val = g'.appTop.hom t.val → g = g' := by
  refine ⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance,
    inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : ℤ →+ Additive Γ(Z, ⊤)ˣ := zmultiplesHom _ (Additive.ofMul v)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S ℤ (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S ℤ).hom)
    let a : Z' ⟶ splitTorus S ℤ := Over.homMk g h
    let a' : Z' ⟶ splitTorus S ℤ := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S ℤ Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine AddMonoidHom.ext_int ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

theorem pb_inv_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (f.appLE U W h).hom (x⁻¹).val = ((pb f U W h x)⁻¹).val := by
  rw [← map_inv, pb_val]

end GenAffine

set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor GenAffine Opposite in

theorem generatorScheme_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  intro B N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation
  let x : Pt (fun _ : Unit => N) G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  have hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g' :=
    fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)
  have hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y :=
    fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩
  have hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i) := by
    intro i
    obtain ⟨T, p, t, hpa, hpl, hex, hun⟩ := exists_torus_one (N.U i).toScheme
    have hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k) :=
      fun k z _ => (p z).2
    let yT : Pt (fun _ : Unit => N) T :=
      Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)
    obtain ⟨ψ, hψ⟩ := hsurj yT
    have hψb : ψ ≫ x.b = p ≫ (N.U i).ι := congrArg Pt.b hψ
    let ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme := IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change x.b (ψ z) ∈ N.U i
      rw [← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]
      exact (p z).2)
    have hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ := IsOpenImmersion.lift_fac _ _ _
    have hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => z.2
    obtain ⟨φ, hφp, hφt⟩ := hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))
    have h2 : ψ₀ ≫ φ = 𝟙 T := by
      refine hun T _ _ ?_ ?_
      · rw [Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]
      · have htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun f z _ => trivial
        have hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i) :=
          Units.ext ((pb_top _ _ _).trans hφt)
        have hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) =
            pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) := pb_congr hψ₀ _ _ _ _
        have e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) =
            pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) := (pb_id_comp ψ _ _ _ le_rfl hψ' _).symm
        have hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p z).2
        have e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i) :=
          Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT
        have e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val :=
          Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _
        refine (pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_
        rw [← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]
        exact (congrArg Units.val (e1.trans (e2.trans e3))).trans e4
    have h1 : φ ≫ ψ₀ = 𝟙 _ := by
      rw [← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]
      refine hinj _ _ ?_
      have hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b := by
        rw [Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]
      have hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p (φ z)).2
      have hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => z.2
      have hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) =
          pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) =
          pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) =
          pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) := (pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm
      have f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i) :=
        Pt.congr hψ () i φ ⊤ hx' hy'
      have f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val :=
        Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'
      refine Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)
      cases k
      refine f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm
      exact f5.trans hφt
    have : IsIso φ := ⟨⟨ψ₀, h1, h2⟩⟩
    rw [← hφp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover
    fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2,
    fun i i' => ?_, fun Z b s hs => ?_⟩
  · have hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') =
        pullU x.b _ (N.g i i') *
          res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i) := by
      rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
      exact x.compat () i i' _ inf_le_left inf_le_right
    dsimp only
    rw [map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]
  · have hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'),
        pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ =
          pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹ := by
      intro i i' W h h'
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')
      rw [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this
      rw [map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]
    let y : Pt (fun _ : Unit => N) Z := ⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i)
        (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y := by
      intro g
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        cases k
        have h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i :=
          Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        exact (inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun i => ?_⟩
        have := Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        have h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹ := pb_id _ _
        have h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) =
            (s i)⁻¹ := h3.symm.trans (this.trans h4)
        rw [pb_inv_val, h5, inv_inv]
    obtain ⟨g0, hg0⟩ := hsurj y
    exact ⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatorScheme_lineBundle_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  atlas_forward_decl GlobalTheory.generatorScheme_affine_finiteType
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem res_compat_of_gm {Z B : Scheme.{0}} {N : LB B} (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z i i', b z ∈ N.U i → b z ∈ N.U i' → gm (𝟙 _) z _ (s i) = gm b z _ (N.g i i') * gm (𝟙 _) z _ (s i'))
    (i i' : N.ι) :
    res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) =
      pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i') := by
  apply unit_ext
  intro z hz
  have hz' : b z ∈ N.U i ⊓ N.U i' := hz
  rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 _) b z _ hz', Category.id_comp]
  exact h z i i' hz'.1 hz'.2

theorem appLE_eq_of_gm {Y Y' B : Scheme.{0}} {N : LB B} (β : Y ⟶ Y') (b : Y ⟶ B) (b' : Y' ⟶ B) (hβ : β ≫ b' = b)
    (i : N.ι) (s : Γ(Y, b ⁻¹ᵁ N.U i)ˣ) (s' : Γ(Y', b' ⁻¹ᵁ N.U i)ˣ)
    (h : ∀ z, b z ∈ N.U i → gm β z _ s' = gm (𝟙 _) z _ s) :
    (β.appLE (b' ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hβ]; exact le_rfl)).hom s'.val = s.val := by
  apply TopCat.Presheaf.section_ext Y.sheaf
  intro z hz
  have := congrArg Units.val (h z hz)
  have hz2 : β z ∈ b' ⁻¹ᵁ N.U i := by rw [← hβ] at hz; exact hz
  rw [gm_val β z _ hz2, gm_val (𝟙 Y) z _ hz] at this
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  exact this

theorem exists_isGen_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ I hI X hX Y β b hb hβ N hN s hs hsβ
  obtain ⟨G, q, u, hqa, hql, hu, hU⟩ := GlobalTheory.T.generatorScheme_lineBundle_affine_finiteType X.left N hN
  have hex := fun e => hU (Y e).left (b e) (s e) (res_compat_of_gm (b e) (s e) (fun z i i' => hs e z i i'))
  choose f hfq hfu using fun e => (hex e).exists
  have hfβ : ∀ e, β e ≫ f (e + 1) = f e := fun e =>
    (hex e).unique ⟨by rw [Category.assoc, hfq, hβ], fun i => by
        rw [← Scheme.Hom.appLE_comp_appLE (β e) (f (e + 1)) (q ⁻¹ᵁ N.U i) (b (e + 1) ⁻¹ᵁ N.U i) (b e ⁻¹ᵁ N.U i)
          (by rw [← hfq (e + 1)]; exact le_rfl) (by rw [← hβ e]; exact le_rfl),
          CommRingCat.comp_apply, hfu (e + 1) i]
        exact appLE_eq_of_gm (β e) (b e) (b (e + 1)) (hβ e) i (s e i) (s (e + 1) i) (hsβ e · i)⟩
      ⟨hfq e, hfu e⟩
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ X.hom)
  have H := GlobalTheory.T.formalAlgebraisation_morphisms'
  obtain ⟨g, hg, -⟩ := H R I hI X Z hX (inferInstanceAs (IsSeparated (q ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (q ≫ X.hom))) (inferInstanceAs (QuasiCompact (q ≫ X.hom)))
    Y β b hb hβ f (fun e => by
      show f e ≫ q ≫ X.hom = _
      rw [← Category.assoc, hfq, (hb e).w]) hfβ
  have hgq : g.left ≫ q = 𝟙 X.left := by
    have hH := H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b (fun e => (hb e).w) hβ
    have h1 := hH.unique (y₁ := Over.homMk (g.left ≫ q) (by rw [Category.assoc]; exact Over.w g))
      (y₂ := 𝟙 X) (fun e => by
        show b e ≫ (g.left ≫ q) = b e
        rw [← Category.assoc, hg e, hfq e])
      (fun e => by rw [Over.id_left, Category.comp_id])
    exact congrArg CommaMorphism.left h1
  have hpt : ∀ x, q (g.left x) = x := fun x => by rw [← Scheme.Hom.comp_apply, hgq]; rfl
  have hle : ∀ i, N.U i ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ N.U i) := fun i x hx => by
    show q (g.left x) ∈ N.U i
    rw [hpt]; exact hx
  refine ⟨⟨fun i => res (hle i) (pullU g.left _ (u i))⟩, fun i j => ?_⟩
  apply unit_ext
  intro x hx
  have hx' : q (g.left x) ∈ N.U i ⊓ N.U j := by rw [hpt]; exact hx
  have key := congrArg (gm g.left x (q ⁻¹ᵁ (N.U i ⊓ N.U j))) (hu i j)
  rw [map_mul, gm_res _ x _ hx', gm_res _ x _ hx', gm_pull g.left q x _ hx', hgq] at key
  show gm (𝟙 _) x _ (res _ (res (hle i) (pullU g.left _ (u i)))) =
    gm (𝟙 _) x _ (N.g i j * res _ (res (hle j) (pullU g.left _ (u j))))
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx.1, gm_res _ x _ hx, gm_res _ x _ hx.2,
    gm_pull (𝟙 _) g.left x _ (hle i hx.1), gm_pull (𝟙 _) g.left x _ (hle j hx.2),
    Category.id_comp]
  exact key

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_algebraisation_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  atlas_forward_decl GlobalTheory.FormalAlg.exists_isGen_of_reductions
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lbIso_of_compatible_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  intro R _ _ I hI X hX Y β b hpb hβ A A' hA hA' c hc hcomp
  have hle : ∀ e (p : (LB.div A' A).ι), b e ⁻¹ᵁ (LB.div A' A).U p ≤
      (LB.div (A'.pull (b e)) (A.pull (b e))).U (fun _ => p.1, fun _ => p.2) :=
    fun e p x hx => ⟨Set.mem_iInter.2 fun _ => hx.1, Set.mem_iInter.2 fun _ => hx.2⟩
  let s : ∀ e (i : (LB.div A' A).ι), Γ((Y e).left, b e ⁻¹ᵁ (LB.div A' A).U i)ˣ :=
    fun e p => res (hle e p) ((c e).s (fun _ => p.1, fun _ => p.2))
  have hs : ∀ e (z : (Y e).left) (p : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      gm (𝟙 _) z _ (s e p) = gw (c e) (𝟙 _) z p.1 (fun _ => p.2) :=
    fun e z p h => gm_res (𝟙 (Y e).left) z (hle e p) (by simpa using h) _
  have hg : ∀ e (z : (Y e).left) (p p' : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      b e z ∈ (LB.div A' A).U p' →
      gm (b e) z _ ((LB.div A' A).g p p') =
        gm (b e) z _ (A'.g p.1 p'.1) * (gm (b e) z _ (A.g p.2 p'.2))⁻¹ := by
    intro e z p p' h h'
    have hm : b e z ∈ (LB.div A' A).U p ⊓ (LB.div A' A).U p' := ⟨h, h'⟩
    show gm (b e) z _ (res _ (A'.g p.1 p'.1) * (res _ (A.g p.2 p'.2))⁻¹) = _
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ _ _ hm _)
      ((map_inv _ _).trans (congrArg _ (gm_res _ _ _ hm _))))
  have hpg : ∀ e (z : (Y e).left) (k k' : A.ι), b e z ∈ A.U k → b e z ∈ A.U k' →
      gm (𝟙 (Y e).left) z _ ((A.pull (b e)).g (fun _ => k) (fun _ => k')) =
        gm (b e) z _ (A.g k k') := by
    intro e z k k' hk hk'
    have hp : (𝟙 (Y e).left) z ∈ (A.pull (b e)).U (fun _ => k) ⊓ (A.pull (b e)).U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (b e) _ (A.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hp _).trans ((gm_pull (𝟙 _) (b e) z (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))
  refine (GlobalTheory.T.exists_generator_algebraisation_reductions R I hI X hX Y β b hpb hβ (LB.div A' A) (LB.isLB_div hA' hA) s ?_ ?_ :
    ∃ t : LB.Gen (LB.div A' A), t.IsGen)
  · intro e z p p' h h'
    rw [hs e z p h, hs e z p' h', hg e z p p' h h']
    have := (isGen_iff (c e)).1 (hc e) _ (𝟙 _) z p.1 p'.1 (fun _ => p.2) (fun _ => p'.2) h.1 h'.1
      (mem_pull.2 h.2) (mem_pull.2 h'.2)
    rw [this, hpg e z p.2 p'.2 h.2 h'.2, Category.id_comp]
  · intro e z p h
    have h1 : b (e + 1) (β e z) = b e z := by rw [← hβ e]; rfl
    have hz : β e z ∈ b (e + 1) ⁻¹ᵁ (LB.div A' A).U p := show b (e + 1) (β e z) ∈ _ from h1 ▸ h
    rw [show gm (β e) z _ (s (e + 1) p) = gw (c (e + 1)) (β e) z p.1 (fun _ => p.2) from
      gm_res _ z (hle (e + 1) p) hz _, hcomp e z p.2 p.1 h.2 h.1, hs e z p h]

end GlobalTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  atlas_forward_decl GlobalTheory.FormalAlg.lbIso_of_compatible_reductions
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem cross_cancel {G : Type} [CommGroup G] (a a' g : G) (p q : ℤ) :
    (a' * g ^ q) ^ p * ((a * g ^ p) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm q p]
  group

theorem lbIso_pw_cross : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  intro R _ _ I hI X hX Y β b hb hβ N v hN p q A A' hA hA' w w' hg hv hv'
  choose c hc hcg using fun e =>
    GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers X.left (Y e).left (b e) A A' (N e) p q (w e) (w' e) hA hA' (hN e) (hg e).1 (hg e).2
  refine GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions R I hI X hX Y β b hb hβ (pw A q) (pw A' p) (isLB_pw hA q) (isLB_pw hA' p) c hc ?_
  intro e z k k' hk hk'
  obtain ⟨l, hl⟩ := exists_chart (hN e) z
  obtain ⟨l', hl'⟩ := exists_chart (hN (e + 1)) (β e z)
  have hz : b (e + 1) (β e z) = b e z := by
    rw [← Scheme.Hom.comp_apply, hβ e]
  have h1 := hcg (e + 1) (Y e).left (β e) z k k' l' (hz ▸ hk) (hz ▸ hk') hl'
  have h0 := hcg e (Y e).left (𝟙 _) z k k' l hk hk' hl
  rw [h1, h0, hv e z k l' l hk hl' hl, hv' e z k' l' l hk' hl' hl]
  exact (cross_cancel _ _ _ p q).symm

end GlobalTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_algebraised_powers_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  atlas_forward_decl GlobalTheory.FormalAlg.lbIso_pw_cross
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

open ReciprocityTheory.ChartRestriction.G.Semi

theorem commGroup_mul_inv_zpow {G : Type} [CommGroup G] (x y : G) (a : ℤ) : (x * y⁻¹) ^ a = x ^ a * (y ^ a)⁻¹ := by
  rw [mul_zpow, inv_zpow]

theorem div_pull_pw_g {X Y : Scheme.{0}} (A : LB X) (H : LB Y) (φ : Y ⟶ X) (a : ℤ) (p q : (PUnit → A.ι) × H.ι) :
    (LB.div ((GlobalTheory.AbLaw.pw A a).pull φ) (GlobalTheory.AbLaw.pw H a)).g p q =
      (((LB.div (A.pull φ) H).g p q) ^ a : Γ(Y, (LB.div (A.pull φ) H).U p ⊓ (LB.div (A.pull φ) H).U q)ˣ) := by
  show res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _ ^ a)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2 ^ a))⁻¹ =
    (res _ (∏ _k : PUnit, res _ (pullU φ _ (A.g _ _)) ^ (1 : ℤ)) * (res _ (H.g p.2 q.2))⁻¹) ^ a
  simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact (commGroup_mul_inv_zpow _ _ a).symm

theorem lbIso_pw_pull_gw : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  intro X Y φ A H w hw a
  refine ⟨⟨fun p => w.s p ^ a⟩, ?_, ?_⟩
  · intro p q
    have e := congrArg (· ^ a) (hw p q)
    simp only [mul_zpow, ← map_zpow] at e
    exact e.trans (congrArg (· * res _ (w.s q ^ a)) (div_pull_pw_g A H φ a p q).symm)
  · intro Z r z k k' _ _
    exact map_zpow _ _ a

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_zpow_local_units_pow : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  atlas_forward_decl GlobalTheory.FormalAlg.lbIso_pw_pull_gw
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem gs_comp_stalkMap {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U)
    (a : Γ(X, U)) :
    gs (r ≫ F) z U a = (Scheme.Hom.stalkMap r z).hom (gs F (r z) U a) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem gm_val_stalkMap {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (u : Γ(Y, V)ˣ) :
    ((gm r z V u : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) =
      (Scheme.Hom.stalkMap r z).hom ((gm (𝟙 Y) (r z) V u : (Y.presheaf.stalk (r z))ˣ) : Y.presheaf.stalk (r z)) := by
  rw [← gs_unit r z V h, ← gs_unit (𝟙 Y) (r z) V h, gs_stalkMap r z V h]

theorem gw_comp_of_rel : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  intro X Y' Y b' β b hb A H' H w' v w ι s s' s'' h₁ h₂ h₃ hc z k k' k'' hk hk' hk''
  subst hb

  have hz : z ∈ ⨆ j, nonzeroLocus (s'' j) := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k₀, hk₀, hu₀⟩ := (mem_nonzeroLocus (s'' j) z).1 hj
  have hu : IsUnit (gs (𝟙 Y) z (H.U k'') ((s'' j).f k'')) := by
    rw [gs_compat (s'' j) (𝟙 Y) z hk'' hk₀]
    exact (Units.isUnit _).mul hu₀
  have hkb : b' (β z) ∈ A.U k := hk
  have e₁ := h₁ j (β z) k k' hkb hk'
  have e₂ := h₂ j z k' k'' hk' hk''
  have e₃ := h₃ j z k k'' hk hk''
  have hV : β z ∈ (A.pull b').U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hkb, hk'⟩
  have e₁' := congrArg (Scheme.Hom.stalkMap β z).hom e₁
  rw [map_mul, ← gs_comp_stalkMap β b' z _ hkb, ← gs_stalkMap β z _ hk'] at e₁'
  have hw' : ((Geo.Tor.gw w' β z k k' : (Y.presheaf.stalk z)ˣ) : Y.presheaf.stalk z) =
      (Scheme.Hom.stalkMap β z).hom ((Geo.Tor.gw w' (𝟙 _) (β z) k k' : (Y'.presheaf.stalk (β z))ˣ) :
        Y'.presheaf.stalk (β z)) :=
    gm_val_stalkMap β z _ hV _
  rw [← hw', e₂] at e₁'
  rw [e₃, ← _root_.mul_assoc, ← Units.val_mul] at e₁'
  exact Units.ext (hu.mul_left_inj.1 e₁')

end GlobalTheory.FormalAlg
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  atlas_forward_decl GlobalTheory.FormalAlg.gw_comp_of_rel
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_lift_id {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : 𝟙 X ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R))) :
    IsClosedImmersion (pullback.lift (𝟙 X) f h) := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]
    infer_instance
  have e : pullback.lift (𝟙 X) f h = inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id R)))) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  rw [e]
  infer_instance

theorem veryAmpleBy_of_lbIso {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H H'' : LB X} (hH : H.IsLB) (hH'' : H''.IsLB) (hI : LBIso H H'') {n : ℕ} {s : Fin (n + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ s'' : Fin (n + 1) → LB.Sec H'', VeryAmpleBy f H'' s'' := by
  obtain ⟨w, hw⟩ := LBIso.trans hH'' hH (pull_isLB hH _) (LBIso.symm hI) (LBIso.symm (GlobalTheory.lbIso_pull_id hH))
  choose s'' hs'' using fun j => (GlobalTheory.SecPullIso.section_pull X X (𝟙 X) H H'' w hH hH'' hw (s j)).1
  exact ⟨s'', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R (RingHom.id R) X f (𝟙 X)
    (by rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]; simp)
    (isClosedImmersion_lift_id f _) H'' w s'' hH'' hw fun j => (hs'' j).1⟩

end GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem formalAlgebraisation_schemes : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro R _ _ I hI Y β hβ hY N hN hNN hA
  choose v hv using hNN
  obtain ⟨a, ha1, hlift⟩ := GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower R I Y β hβ N hN hA
  have hpw : ∀ (c : ℤ) (e : ℕ), ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
      wa.IsGen ∧ ∀ (z : (Y e).left) (k : (N (e + 1)).ι) (k' : (N e).ι), β e z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        Geo.Tor.gw wa (𝟙 _) z k k' = Geo.Tor.gw (v e) (𝟙 _) z k k' ^ c := fun c e => by
    obtain ⟨wa, h1, h2⟩ := GlobalTheory.T.exists_bundleIso_zpow_local_units_pow (Y (e + 1)).left (Y e).left (β e) (N (e + 1)) (N e) (v e) (hv e) c
    exact ⟨wa, h1, fun z k k' hk hk' => h2 (Y e).left (𝟙 _) z k k' hk hk'⟩
  choose va hva hvaw using hpw (a : ℤ)
  choose vb hvb hvbw using hpw ((a + 1 : ℕ) : ℤ)
  obtain ⟨n, s, hsRel, hsVA⟩ := hlift a (Or.inl rfl) va hva
  obtain ⟨n₂, s₂, hs₂Rel, hs₂VA⟩ := hlift (a + 1) (Or.inr rfl) vb hvb
  obtain ⟨B, H', s', b, w, hH', hVA', hpb, hcomp, hw, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hI Y β hβ
    (fun e => GlobalTheory.AbLaw.pw (N e) a) va (fun e => ⟨isLB_pw (hN e) _, hva e⟩) n s hsRel (hsVA 0)
  have hBp : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R B.left B.hom ⟨H', hH', n, s', hVA'⟩
  obtain ⟨M₂, s₂', w', hM₂, hw'⟩ := GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem R I hI B hBp Y β b hpb hcomp
    (fun e => GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) vb (fun e => ⟨isLB_pw (hN e) _, hvb e⟩) n₂ s₂ hs₂Rel
    (fun e => (hs₂VA e).1)
  have c1 : ∀ e z k l' l, b e z ∈ H'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ (a : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvaw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) H'
      (GlobalTheory.AbLaw.pw (N (e + 1)) a) (GlobalTheory.AbLaw.pw (N e) a) (w (e + 1)) (va e) (w e) (Fin (n + 1)) s' (s (e + 1)) (s e)
      (fun j => (hw (e + 1)).2 j) (fun j => hsRel e j) (fun j => (hw e).2 j) (hsVA e).1 z k l' l h1 h2 h3
  have c2 : ∀ e z k l' l, b e z ∈ M₂.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w' e) (𝟙 _) z k l =
        Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ ((a + 1 : ℕ) : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvbw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) M₂
      (GlobalTheory.AbLaw.pw (N (e + 1)) ((a + 1 : ℕ) : ℤ)) (GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) (w' (e + 1)) (vb e) (w' e)
      (Fin (n₂ + 1)) s₂' (s₂ (e + 1)) (s₂ e)
      (fun j => (hw' (e + 1)).2 j) (fun j => hs₂Rel e j) (fun j => (hw' e).2 j) (hs₂VA e).1 z k l' l h1 h2 h3
  have hiso := GlobalTheory.T.lineBundleIso_algebraised_powers_compatible R I hI B hBp Y β b hpb hcomp N v hN (a : ℤ) ((a + 1 : ℕ) : ℤ) H' M₂ hH' hM₂ w w'
    (fun e => ⟨(hw e).1, (hw' e).1⟩) c1 c2
  have hcast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; rfl
  rw [hcast] at hiso
  have hM : (GlobalTheory.AbLaw.tw M₂ H' (-1)).IsLB := isLB_tw hM₂ hH' _
  have hH'M : LBIso H' (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M₂ H' (-1)) a) := GlobalTheory.T.cancel_powers_of_cech_line_bundles.2 B.left H' M₂ a hH' hM₂ hiso
  have hNM : ∀ e, LBIso (N e) ((GlobalTheory.AbLaw.tw M₂ H' (-1)).pull (b e)) := fun e =>
    GlobalTheory.T.cancel_powers_of_cech_line_bundles.1 B.left (Y e).left (b e) H' M₂ (N e) a hH' hM₂ (hN e) ⟨w e, (hw e).1⟩
      (hcast ▸ ⟨w' e, (hw' e).1⟩)
  obtain ⟨s'', hs''⟩ := veryAmpleBy_of_lbIso B.hom hH' (isLB_pw hM _) hH'M hVA'
  exact ⟨B, GlobalTheory.AbLaw.tw M₂ H' (-1), b, hBp, hM,
    (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B _ hM).2 ⟨a, ha1, n, s'', hs''⟩, hpb, hcomp, hNM⟩

end GlobalTheory.FormalAlg
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  atlas_forward_decl GlobalTheory.FormalAlg.formalAlgebraisation_schemes
end

section
namespace GlobalTheory

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation :=
  ⟨GlobalTheory.T.formalAlgebraisation_morphisms', GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle⟩

end GlobalTheory
end
