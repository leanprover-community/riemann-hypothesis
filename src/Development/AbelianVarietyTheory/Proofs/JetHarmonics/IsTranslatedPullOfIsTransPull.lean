import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.EndomorphismPullbackRigid
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT IsNormEnd)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PtTie GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid

namespace GlobalTheory.TransPullCompare

variable {X : Scheme.{0}} {A : Over X}

abbrev TwoGen (L : LB A.left) {T : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, f.left] ![a, -b])

def Rel {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ} (α : TwoGen L m a b)
    (w : LB.Iso (PullPow L f b) (PowOver L a T)) : Prop :=
  m = f ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (j : Fin 2 → L.ι),
    r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
    gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j) =
      gm r z ((LB.div (PowOver L a T) (PullPow L f b)).U (fun _ => j 0, fun _ => j 1)) (w.s (fun _ => j 0, fun _ => j 1))

section Basic
variable {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ}

theorem mem_div_iff (j : Fin 2 → L.ι) (y : (T ⊗ A).left) :
    y ∈ (LB.div (PowOver L a T) (PullPow L f b)).U (fun _ => j 0, fun _ => j 1) ↔
      y ∈ LB.wchart L ![(snd T A).left, f.left] j :=
  ⟨fun h => Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [Set.mem_iInter.1 h.1 0, Set.mem_iInter.1 h.2 0],
    fun h => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h 1⟩⟩



theorem gm_div_two {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (j j' : Fin 2 → L.ι)
    (hj : r z ∈ LB.wchart L ![(snd T A).left, f.left] j) (hj' : r z ∈ LB.wchart L ![(snd T A).left, f.left] j') :
    gm r z _ ((LB.div (PowOver L a T) (PullPow L f b)).g (fun _ => j 0, fun _ => j 1) (fun _ => j' 0, fun _ => j' 1)) =
      trF ![(snd T A).left, f.left] ![a, -b] r z j j' := by
  have h := (mem_div_iff (a := a) (b := b) j _).2 hj
  have h' := (mem_div_iff (a := a) (b := b) j' _).2 hj'
  refine (gm_div (PullPow L f b) (PowOver L a T) r z (fun _ => j 0, fun _ => j 1) (fun _ => j' 0, fun _ => j' 1)
    ⟨h, h'⟩).trans ?_
  refine (congrArg₂ (· * ·) (gm_linComb L _ _ r z _ _ h.1 h'.1)
    (congrArg (·⁻¹) (gm_linComb L _ _ r z _ _ h.2 h'.2))).trans ?_
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]

theorem Rel.isGen_iff {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)} (h : Rel α w) :
    α.IsGen ↔ w.IsGen := by
  obtain ⟨rfl, H⟩ := h
  constructor
  · rintro hα ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    obtain ⟨j, rfl, rfl⟩ : ∃ j : Fin 2 → L.ι, p₁ = (fun _ => j 0) ∧ p₂ = fun _ => j 1 :=
      ⟨![p₁ 0, p₂ 0], funext fun k => congrArg p₁ (Subsingleton.elim _ _),
        funext fun k => congrArg p₂ (Subsingleton.elim _ _)⟩
    obtain ⟨j', rfl, rfl⟩ : ∃ j : Fin 2 → L.ι, q₁ = (fun _ => j 0) ∧ q₂ = fun _ => j 1 :=
      ⟨![q₁ 0, q₂ 0], funext fun k => congrArg q₁ (Subsingleton.elim _ _),
        funext fun k => congrArg q₂ (Subsingleton.elim _ _)⟩
    refine unit_ext fun y hy => ?_
    have hj := (mem_div_iff j y).1 hy.1
    have hj' := (mem_div_iff j' y).1 hy.2
    refine ((gm_res _ y _ hy _).trans (H _ _ y j hj).symm).trans ((gen_trans hα _ y hj hj').trans ?_)
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div_two _ y j j' hj hj')
      ((gm_res _ y _ hy _).trans (H _ _ y j' hj').symm))).symm
  · intro hw
    refine isGen_of_gm _ fun y j j' hj hj' => ?_
    have hy : (𝟙 (T ⊗ A).left : _ ⟶ _) y ∈ (LB.div (PowOver L a T) (PullPow L m b)).U (fun _ => j 0, fun _ => j 1) ⊓
        (LB.div (PowOver L a T) (PullPow L m b)).U (fun _ => j' 0, fun _ => j' 1) :=
      ⟨(mem_div_iff j y).2 hj, (mem_div_iff j' y).2 hj'⟩
    refine (H _ _ y j hj).trans ((gm_res _ y _ hy _).symm.trans ((congrArg (gm _ y _) (hw _ _)).trans ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div_two _ y j j' hj hj')
      ((gm_res _ y _ hy _).trans (H _ _ y j' hj').symm))

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (c : Γ(Y, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom c) = gs r z U c :=
  (gs_res (𝟙 Z) z h trivial ((r.app U).hom c)).trans ((gs_pull (𝟙 Z) r z U (h trivial) c).trans
    (by rw [Category.id_comp]))

theorem gm_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (c : Γ(Y, U)ˣ) :
    gm (𝟙 Z) z ⊤ (Units.map (r.appLE U ⊤ h).hom.toMonoidHom c) = gm r z U c :=
  Units.ext ((gs_unit (𝟙 Z) z ⊤ trivial _).symm.trans ((gs_appLE r U h z c.val).trans (gs_unit r z U (h trivial) c)))

theorem gs_stalk {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ Y') (z : Z) (U : Y'.Opens) (h : q (r z) ∈ U)
    (c : Γ(Y', U)) : (r.stalkMap z).hom (gs q (r z) U c) = gs (r ≫ q) z U c := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

abbrev stU {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (r z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (r.stalkMap z).hom.toMonoidHom

theorem gm_stalk {Y Y' Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ Y') (z : Z) (U : Y'.Opens) (h : q (r z) ∈ U)
    (c : Γ(Y', U)ˣ) : stU r z (gm q (r z) U c) = gm (r ≫ q) z U c :=
  Units.ext ((congrArg (r.stalkMap z).hom (gs_unit q (r z) U h c).symm).trans ((gs_stalk r q z U h c.val).trans
    (gs_unit (r ≫ q) z U h c)))

theorem exists_loc {W : Over X} (z : W.left) {J : (W.left ⟶ A.left) → L.ι} (hJ : Good L z J) {K : Type} [Fintype K]
    (x : K → (W ⟶ A)) : ∃ (W' : Over X) (p : W' ⟶ W) (z' : W'.left), p.left z' = z ∧
      Function.Injective (p.left.stalkMap z').hom ∧ ∀ k, Lands L (p ≫ x k) (J (x k).left) := by
  let V : W.left.Opens := LB.wchart L (fun k => (x k).left) (fun k => J (x k).left)
  have hz : z ∈ V := Set.mem_iInter.2 fun k => hJ _
  refine ⟨overRes V, overResι V, ⟨z, hz⟩, rfl, ?_, fun k y _ => Set.mem_iInter.1 y.2 k⟩
  have hi : ∀ y : V.toScheme, IsIso (V.ι.stalkMap y) := fun y => inferInstance
  have := hi ⟨z, hz⟩
  exact (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap ⟨z, hz⟩)).1

def tr (L : LB A.left) {W : Over X} (v : W ⟶ A) (z : W.left) (i : L.ι) (J : (W.left ⟶ A.left) → L.ι) :
    (W.left.presheaf.stalk z)ˣ := gm v.left z (L.U i ⊓ L.U (J v.left)) (L.g i (J v.left))

variable {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)}

theorem lift_left_snd {W : Over X} (t : W ⟶ T) (v : W ⟶ A) : (lift t v).left ≫ (snd T A).left = v.left := by
  rw [← Over.comp_left, lift_snd]

theorem Rel.germ_isoVal (h : Rel α w) (hα : α.IsGen) {W : Over X} (t : W ⟶ T) (v u : W ⟶ A) (hu : lift t v ≫ f = u)
    (i j : L.ι) (hi : Lands L v i) (hj : Lands L u j) (z : W.left) {J} (hJ : Good L z J) :
    gm (𝟙 _) z ⊤ (isoVal w t v u hu i j hi hj) = tr L v z i J ^ a * tr L u z j J ^ (-b) * val α (lift t v).left z J := by
  obtain ⟨rfl, H⟩ := h
  have hm : (lift t v).left z ∈ LB.wchart L ![(snd T A).left, m.left] ![i, j] := (mem_div_iff (a := a) (b := b) _ _).1
    ⟨Lands.le_wchart (lift_snd t v) hi trivial, Lands.le_wchart hu hj trivial⟩
  refine ((gm_appLE _ _ _ z _).trans (H _ _ z ![i, j] hm).symm).trans
    ((gen_trans hα _ z hm (hJ.mem _ _)).trans (congrArg (· * _) ?_))
  subst hu
  exact (Fin.prod_univ_two _).trans (congrArg₂ (· * ·)
    (congrArg (fun q => gm q z (L.U i ⊓ L.U (J q)) (L.g i (J q)) ^ a) (lift_left_snd t v)) rfl)

theorem Rel.stalk_val (h : Rel α w) {W W' : Over X} (p : W' ⟶ W) (z : W'.left) {J} (hJ : Good L (p.left z) J)
    (t : W ⟶ T) (v u : W ⟶ A) (hu : lift t v ≫ f = u) {t' : W' ⟶ T} {v' u' : W' ⟶ A} (ht : p ≫ t = t') (hv : p ≫ v = v')
    (hu' : lift t' v' ≫ f = u') (hi : Lands L v' (J v.left)) (hj : Lands L u' (J u.left)) :
    stU p.left z (val α (lift t v).left (p.left z) J) = gm (𝟙 _) z ⊤ (isoVal w t' v' u' hu' _ _ hi hj) := by
  obtain ⟨rfl, H⟩ := h
  subst ht hv hu
  have hm : (lift (p ≫ t) (p ≫ v)).left z ∈ LB.wchart L ![(snd T A).left, m.left] ![J v.left, J (lift t v ≫ m).left] :=
    (mem_div_iff (a := a) (b := b) _ _).1
      ⟨Lands.le_wchart (lift_snd _ _) hi trivial, Lands.le_wchart hu' hj trivial⟩
  refine Eq.trans ?_ ((gm_appLE _ _ _ z _).trans (H _ _ z _ hm).symm).symm
  rw [val_of α _ _ J ![J v.left, J (lift t v ≫ m).left] (fun k => by
    fin_cases k
    exacts [congrArg J (lift_left_snd t v), rfl])]
  rw [← comp_lift] at hm ⊢
  exact gm_stalk p.left _ z _ hm _

theorem germ_secVal {k : ℤ} (s : LB.Sec (PowOver L k T)) {W : Over X} (t : W ⟶ T) (v : W ⟶ A) (i : L.ι)
    (hi : Lands L v i) (z : W.left) {J} (hJ : Good L z J) :
    gs (𝟙 _) z ⊤ (secVal s t v i hi) = (tr L v z i J ^ k).val * sval s (lift t v).left z J := by
  refine (gs_appLE _ _ _ z _).trans ((sec_trans s _ z (Lands.le_wchart (lift_snd t v) hi trivial)
    (hJ.mem _ _)).trans (congrArg (fun u : (W.left.presheaf.stalk z)ˣ => u.val * _) ?_))
  simp only [trF, tr, Fin.prod_univ_one]
  rw [lift_left_snd]

theorem stalk_sval {k : ℤ} (s : LB.Sec (PowOver L k T)) {W W' : Over X} (p : W' ⟶ W) (z : W'.left)
    {J : (W.left ⟶ A.left) → L.ι}
    (t : W ⟶ T) (v : W ⟶ A) {t' : W' ⟶ T} {v' : W' ⟶ A} (ht : p ≫ t = t') (hv : p ≫ v = v')
    (hi : Lands L v' (J v.left)) :
    (p.left.stalkMap z).hom (sval s (lift t v).left (p.left z) J) = gs (𝟙 _) z ⊤ (secVal s t' v' _ hi) := by
  subst ht hv
  have hm := Lands.le_wchart (lift_snd (p ≫ t) (p ≫ v)) hi (show z ∈ (⊤ : W'.left.Opens) from trivial)
  refine Eq.trans ?_ (gs_appLE _ _ _ z _).symm
  rw [sval_of s _ _ J (fun _ => J v.left) (fun k => congrArg J (lift_left_snd t v))]
  rw [← comp_lift] at hm ⊢
  exact gs_stalk p.left _ z _ hm _

end Basic

section Compare
variable {L : LB A.left} {T : Over X} {m f : T ⊗ A ⟶ A} {a b : ℤ}
  {α : TwoGen L m a b} {w : LB.Iso (PullPow L f b) (PowOver L a T)}

theorem id_left_eq (T A : Over X) : 𝟙 (T ⊗ A).left = (lift (fst T A) (snd T A)).left := by
  rw [lift_fst_snd, Over.id_left]

theorem some_good (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose J hJ using fun χ : Z ⟶ A.left => exists_chart hL (χ z)
  exact ⟨J, hJ⟩

theorem stU_inj {Y Z : Scheme.{0}} {r : Z ⟶ Y} {z : Z} (h : Function.Injective (r.stalkMap z).hom) :
    Function.Injective (stU r z) := Units.map_injective h

theorem Rel.twist_iff [GrpObj A] (hL : L.IsLB) (h : Rel α w) (hα : α.IsGen) (s : LB.Sec (LPow A L b T))
    (s' : LB.Sec (LPow A L a T)) :
    IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s s' ↔ Carries w s s' := by
  obtain rfl := h.1
  have e : ∀ {W : Over X} (t : W ⟶ T) (v : W ⟶ A),
      (lift t v).left ≫ (lift (fst T A) m).left = (lift t (lift t v ≫ m)).left := fun t v => by
    rw [← Over.comp_left, comp_lift, lift_fst]
  constructor
  · intro H W t v i j hi hj
    refine fn_ext fun z _ => ?_
    obtain ⟨J, hJ⟩ := some_good hL z
    have k := twist_val H (lift t v).left z hJ
    rw [e] at k
    refine (germ_secVal s' t v i hi z hJ).trans (Eq.trans ?_ ((gs_mul _ z ⊤ trivial _ _).trans (congrArg₂ (· * ·)
      ((gs_unit _ z ⊤ trivial _).trans (congrArg Units.val (h.germ_isoVal hα t v _ rfl i j hi hj z hJ)))
      (germ_secVal s t _ j hj z hJ))).symm)
    refine (congrArg _ k).trans ?_
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _ (tr L _ z j J ^ b),
      inv_mul_cancel_right]
  · intro H
    refine VVRank.isTwistPull_of_sv A hL hα fun y J hJ => ?_
    obtain ⟨W, p, z, rfl, inj, hl⟩ := exists_loc (W := T ⊗ A) y hJ ![snd T A, lift (fst T A) (snd T A) ≫ m]
    have e' : lift (p ≫ fst T A) (p ≫ snd T A) ≫ m = p ≫ lift (fst T A) (snd T A) ≫ m := by
      rw [← comp_lift, Category.assoc]
    have hj : Lands L (lift (p ≫ fst T A) (p ≫ snd T A) ≫ m) (J (lift (fst T A) (snd T A) ≫ m).left) := e' ▸ hl 1
    have k := congrArg (gs (𝟙 _) z ⊤) (H W (p ≫ fst T A) (p ≫ snd T A) _ _ (hl 0) hj)
    rw [id_left_eq, e]
    apply inj
    refine (stalk_sval s' p z _ _ rfl rfl (hl 0)).trans (k.trans ((gs_mul _ z ⊤ trivial _ _).trans
      (Eq.trans ?_ (map_mul _ _ _).symm)))
    exact congrArg₂ (· * ·) ((gs_unit _ z ⊤ trivial _).trans
      (congrArg Units.val (h.stalk_val p z hJ _ _ _ rfl rfl rfl rfl (hl 0) hj)).symm)
      (stalk_sval s p z _ _ rfl e'.symm hj).symm

end Compare

section Grp
variable [GrpObj A] [IsCommMonObj A]


theorem lift_translT {T W : Over X} (b : T ⟶ A) (t : W ⟶ T) (v : W ⟶ A) :
    (lift t v).left ≫ (translT A b).left = (lift t (v * (t ≫ b))).left := by
  rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.lift_transl, _root_.mul_comm]

theorem lift_negT {T W : Over X} (t : W ⟶ T) (v : W ⟶ A) :
    (lift t v).left ≫ (negT A T).left = (lift t v⁻¹).left := by
  rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc, Hom.inv_def]

variable {L : LB A.left} {T : Over X} {k : ℤ}

theorem pow_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) {U : Lift L k θ.pt} (h : Rel (m := translPt A θ.pt) θ.φ U)
    {N : ℕ} (hN : 0 < N) (hb : θ.pt ^ N = 1) :
    LB.Gen.Corr L _ _ _ _ (powGen A L k θ N) (LB.oneGen L) ↔ PowEqOne U N := by
  have e : ∀ {W : Over X} (t : W ⟶ T) (v : W ⟶ A) (z : W.left) {J}, Good L z J →
      val (powGen A L k θ N) (lift t v).left z J = ∏ i ∈ Finset.range N,
        val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (lift t (v * (t ≫ θ.pt) ^ i)).left z J := fun t v z J hJ => by
    rw [ThetaPullback.val_powGen θ N _ hJ, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [lift_translT, MonObj.comp_pow]
  constructor
  · intro H W t v c hc hc0
    refine unit_ext fun z _ => ?_
    obtain ⟨J, hJ⟩ := some_good hL z
    have k₀ := (e t v z hJ).symm.trans ((val_corr hJ H _).trans (val_one _))
    rw [map_prod, map_one]
    refine (Finset.prod_congr rfl fun i _ => h.germ_isoVal θ.isGen t _ _ _ _ _ _ _ z hJ).trans ?_
    rw [Finset.prod_mul_distrib, k₀, _root_.mul_one]
    have tel := Finset.prod_range_div' (fun i => tr L (v * (t ≫ θ.pt) ^ i) z (c i) J ^ k) N
    simp only [zpow_neg, ← div_eq_mul_inv]
    rw [tel, hc0, ← MonObj.comp_pow θ.pt N t, hb, MonObj.comp_one, pow_zero, div_self']
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    rw [val_one, id_left_eq, e _ _ _ hJ]
    obtain ⟨W, p, z, rfl, inj, hl⟩ := exists_loc (W := T ⊗ A) y hJ
      (fun i : Fin N => snd T A * (fst T A ≫ θ.pt) ^ (i : ℕ))
    have hb' : (fst T A ≫ θ.pt) ^ N = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
    have e' : ∀ i : ℕ, p ≫ (snd T A * (fst T A ≫ θ.pt) ^ i) = (p ≫ snd T A) * ((p ≫ fst T A) ≫ θ.pt) ^ i := fun i => by
      rw [MonObj.comp_mul, MonObj.comp_pow, Category.assoc]
    have hc : ∀ i : ℕ, Lands L ((p ≫ snd T A) * ((p ≫ fst T A) ≫ θ.pt) ^ i)
        (J (snd T A * (fst T A ≫ θ.pt) ^ i).left) := fun i => by
      rw [← e', pow_eq_pow_mod i hb']
      exact hl ⟨i % N, Nat.mod_lt _ hN⟩
    have k₀ := congrArg (gm (𝟙 _) z ⊤) (H W (p ≫ fst T A) (p ≫ snd T A) _ hc (by rw [hb', pow_zero]))
    apply stU_inj inj
    rw [map_prod, map_one] at k₀ ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) k₀
    exact h.stalk_val p z hJ _ _ _ (by rw [IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.lift_transl, pow_succ, _root_.mul_assoc]) rfl (e' i) _ _ _

def SymVal (θ : ThetaGrp A L k T) (ν : TwoGen L (snd T A ≫ ι[A]) k k) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (z : W.left) (J), Good L z J →
    val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t v).left z J *
      val ν (lift t (v * (t ≫ θ.pt))).left z J *
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (lift t (v * (t ≫ θ.pt))⁻¹).left z J = val ν (lift t v).left z J



end Grp

section Norm
variable [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def rho (W : Over X) (z : W.left) (J : (W.left ⟶ A.left) → L.L.ι) : (W.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (toUnit W).left z J

theorem germ_rigVal (W : Over X) (i : L.L.ι) (hi : Lands L.L (1 : W ⟶ A) i) (z : W.left) {J} (hJ : Good L.L z J) :
    gm (𝟙 _) z ⊤ (rigVal L W i hi) = tr L.L (1 : W ⟶ A) z i J * rho L W z J := by
  refine (gm_appLE _ _ _ z _).trans ((gen_trans (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rigGen
    (toUnit W).left z (Set.mem_iInter.2 fun _ => hi trivial) (hJ.mem _ _)).trans (congrArg (· * _) ?_))
  rw [trF, Fintype.prod_unique, zpow_one]
  rfl

theorem stalk_rho {W W' : Over X} (p : W' ⟶ W) (z : W'.left) {J} (hJ : Good L.L (p.left z) J)
    (hi : Lands L.L (1 : W' ⟶ A) (J (1 : W ⟶ A).left)) :
    stU p.left z (rho L W (p.left z) J) = gm (𝟙 _) z ⊤ (rigVal L W' _ hi) := by
  refine Eq.trans ?_ (gm_appLE _ _ _ z _).symm
  rw [toUnit_unique (toUnit W') (p ≫ toUnit W)]
  exact gm_stalk p.left _ z _ (hJ.mem (fun _ : PUnit => eSec A) (toUnit W).left) _

def NormVal {T : Over X} {m : T ⊗ A ⟶ A} {a b : ℤ} (α : TwoGen L.L m a b) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (z : W.left) (J), Good L.L z J →
    val α (lift t (1 : W ⟶ A)).left z J = rho L W z J ^ a * rho L W z J ^ (-b)

variable {L}

theorem Rel.norm_iff {φ : A ⟶ A} [IsMonHom φ] {T : Over X} {a b : ℤ} {α : TwoGen L.L (snd T A ≫ φ) a b}
    {w : LB.Iso (PullPow L.L (snd T A ≫ φ) b) (PowOver L.L a T)} (h : Rel α w) (hα : α.IsGen) :
    NormVal L α ↔ IsNormalisedIso L φ a b T w := by
  have hL := L.isLB
  constructor
  · refine fun H => ⟨h.isGen_iff.1 hα, fun W t i j hi hj => unit_ext fun z _ => ?_⟩
    obtain ⟨J, hJ⟩ := some_good hL z
    rw [map_mul, map_zpow, map_zpow, h.germ_isoVal hα t _ _ _ _ _ _ _ z hJ, germ_rigVal L W i hi z hJ,
      germ_rigVal L W j hj z hJ, H W t z J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module
  · rintro ⟨-, H⟩ W t y J hJ
    obtain ⟨W', p, z, rfl, inj, hl⟩ := exists_loc y hJ (fun _ : Unit => (1 : W ⟶ A))
    have hi : Lands L.L (1 : W' ⟶ A) (J (1 : W ⟶ A).left) := MonObj.comp_one (M := A) p ▸ hl ()
    have k₀ := congrArg (gm (𝟙 _) z ⊤) (H W' (p ≫ t) _ _ hi hi)
    apply stU_inj inj
    rw [map_mul, map_zpow, map_zpow] at k₀ ⊢
    rw [h.stalk_val p z hJ t 1 1 (origin_comp t φ) rfl (MonObj.comp_one p) (origin_comp _ φ) hi hi, stalk_rho L p z hJ hi,
      k₀, zpow_neg, mul_inv_cancel_right]


theorem exists_pull_gen {M : LB A.left} (hM : M.IsLB) {φ : A ⟶ A} {a b : ℤ}
    (α₀ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα₀ : α₀.IsGen) (T : Over X) :
    ∃ α : TwoGen M (snd T A ≫ φ) a b, α.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good M z J →
      val α r z J = val α₀ (r ≫ (snd T A).left) z J := by
  obtain ⟨α, hα, hv⟩ := exists_gen hM (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen M ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left) (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_norm_gen (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen) :
    ∃ α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]), α₀.IsGen ∧ IsNormEnd A L φ a b α₀ := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  refine ⟨α₀, hα₀, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]


end Norm

section Main
variable [GrpObj A] [IsCommMonObj A] (L : RigLB A)



def ComesFrom {M : LB A.left} {φ : A ⟶ A} {a b : ℤ} {T : Over X}
    (w₀ : LB.Iso (PullPow M (snd (𝟙_ (Over X)) A ≫ φ) b) (PowOver M a (𝟙_ (Over X))))
    (w : LB.Iso (PullPow M (snd T A ≫ φ) b) (PowOver M a T)) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (i j : M.ι) (hi : Lands M v i) (hj : Lands M (v ≫ φ) j),
    isoVal w t v _ (lift_snd_assoc _ _ _) i j hi hj = isoVal w₀ (toUnit W) v _ (lift_snd_assoc _ _ _) i j hi hj








end Main


end GlobalTheory.TransPullCompare
