import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalScale
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.mixed_cross_identity_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  first | exact @GlobalTheory.GenericCross.main | exact GlobalTheory.GenericCross.main | (intros; apply GlobalTheory.GenericCross.main <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericUnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K → (Y' ⟶ X)} {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hj : ∀ q : K ⊕ K', Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) q =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) q) := by
    intro q
    cases q with
    | inl q => rfl
    | inr q => exact congrArg J (Category.assoc _ _ _)
  have key := H (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k))
    (fun q₁ q₂ hq => by rw [hj, hj, hq])
  have m₂ := hJ.mem φ₂ (r ≫ h)
  have m : r z ∈ L.wchart φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      L.wchart (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    refine ⟨hJ.mem φ₁ r, ?_⟩
    have e₃ : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ (fun k => h ≫ φ₂ k) k)) :=
      funext fun k => congrArg J (Category.assoc _ _ _)
    rw [e₃]
    exact hJ.mem (fun k => h ≫ φ₂ k) r
  have e := congrArg (gs r z _) key
  rw [gs_mul r z _ m] at e
  unfold resTop at e
  rw [gs_res r z _ m, gs_res r z _ m] at e
  have p := gs_pull r h z _ m₂ (s₂.f fun k => J ((r ≫ h) ≫ φ₂ k))
  exact p.symm.trans (e.trans (congrArg (gs r z ⊤ c * ·) (gs_res r z _ m _)))

theorem isUnit_cst_generic {V : Type} [CommRing V] [IsDomain V] (y : Spec (CommRingCat.of (FractionRing V)))
    {c : V} (hc : c ≠ 0) : IsUnit (cst (jK V) y c) := by
  have hK : IsUnit (algebraMap V (FractionRing V) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  obtain ⟨w, hw⟩ := hK
  rw [show cst (jK V) y c = cst (𝟙 _) y (algebraMap V (FractionRing V) c) from H1.gs_spec _ y c, ← hw]
  exact ⟨⟨cst (𝟙 _) y (w : FractionRing V), cst (𝟙 _) y (↑w⁻¹ : FractionRing V),
    by rw [← H1.cst_mul, Units.mul_inv, H1.cst_one], by rw [← H1.cst_mul, Units.inv_mul, H1.cst_one]⟩, rfl⟩

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

lemma unitK_fst : (unitK (G := G)) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
  simp only [unitK, pullback.lift_fst]

lemma gs_unitK_scal (y : Spec (CommRingCat.of (FractionRing V))) (c : V) :
    gs (unitK (G := G)) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) c) = cst (jK V) y c := by
  have hsec : (unitK (G := G)) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    simp only [unitK, pullback.lift_snd]
  unfold scal cst
  refine (gs_pull (unitK (G := G)) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans ?_
  rw [← Category.assoc, hsec, Category.id_comp]

end

theorem value_at_generic_unit : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0
  intro k s F u F' hs hu hpull y J hJ
  let _ := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB P.D P.D.toPre.P.isLB P.oD H.w0 uΨ huΨ a N hN hN0 1
  obtain ⟨c, σ'', τ, hc, hsτ, huσ, hth⟩ :=
    GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc k s F u F' hs hu hpull
  have hv := GlobalTheory.UnitValue.value_at_unit_section V E H t P a N hN hN0 X hX hXc k σ'' τ hth _ (jK V) y J hJ
  have e₁ := sval_of_secScal huσ unitK y hJ
  have e₂ := sval_of_secScal hsτ unitK y hJ
  rw [unitK_fst, gs_unitK_scal] at e₁ e₂
  rw [e₁, e₂] at hv
  apply (isUnit_cst_generic y hc).mul_left_cancel
  rw [hv]
  ring

end GlobalTheory.GenericUnitValue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.value_at_unitSection_genericFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  atlas_forward_decl GlobalTheory.GenericUnitValue.value_at_generic_unit
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_mul_of_id {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → sval a (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval b (𝟙 Y) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval a r z J = gs r z ⊤ c * sval b r z J := by
  have key : ∀ j : K → L.ι, a.f j =
      (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j) := fun j =>
    fn_ext (V := LB.wchart L φ j) fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hI' : Good L y I := hI
      refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c)
        (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm
      refine (sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_
      exact (congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)
  have hm := hJ.mem φ r
  exact (congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem unitK_snd : unitK (G := G) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _

theorem unitK_endK (f : G ⟶ G) [IsMonHom f] : unitK (G := G) ≫ endK f = unitK := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply pullback.hom_ext
  · simp only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (jK V ≫ ·) he
  · simp only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

end

theorem expands_pull_of_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k hk s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN0
  choose Fx hFx hFu using (P.U.expand k hk1).1
  choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k =>
    exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
      (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  choose sp hsp _ using (P.U.expand (k * N) hkN).2
  obtain rfl : F = Fx s := hFu s F hs
  refine ⟨Fp (Fx s), ?_, hFp _⟩
  obtain ⟨u, hu, hn, hrel⟩ := hs'
  haveI : IsMonHom (t.act.act a) := t.act.hom a
  have hF : FormEq (fun _ : Fin 1 => gK (G := t.G)) (fun _ => ((k * N : ℕ) : ℤ))
      (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK])
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _
    (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀)
    (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ _ y J hJ)
    (fun i i' y J hJ => by
      have e := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _)
        (hFp _) 1 1 rfl y J hJ
      simpa only [pow_one] using e)
  obtain ⟨c₀, rfl⟩ := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G
    P.U.toUnifPre).1 c
  have hF' := fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm
  have hc₀ : c₀ = 1 := fn_ext (V := ⊤) fun y _ => by
    choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)
    have hJ' : Good P.U.LG.L y J := hJ
    obtain ⟨s₀, hs₀⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _
      unitK y J hJ'
    obtain ⟨b, hb⟩ := exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)
    have e₁ := sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by
      rw [hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]
      exact hc s₀ y J hJ) unitK y J hJ'
    rw [hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK] at e₁
    have e₂ := GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'
    have e₃ : val u unitK y J = val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by
      have e := val_corr hJ' hn (𝟙 _)
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow] at e
      exact e
    have e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀ :=
      (gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])
    rw [e₂, e₃, e₄] at e₁
    rw [gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]
    refine (hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_
    rw [← e₁, _root_.one_mul, mul_comm]
  have hss : s' = sp (Fp (Fx s)) := SecOps.sec_ext (sec_ext_val hL fun y J hJ => by
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one,
      gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])
  rw [hss]
  exact hsp _

end GlobalTheory.PullExpansion
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  first | exact @GlobalTheory.PullExpansion.expands_pull_of_four_le | exact GlobalTheory.PullExpansion.expands_pull_of_four_le | (intros; apply GlobalTheory.PullExpansion.expands_pull_of_four_le <;> assumption)
end
