import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInIffScalarMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.PsiScalUnit

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ w * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

variable {V : Type} [CommRing V] [IsDomain V]

def ev (z : (TK V).left) : FractionRing V →+* (TK V).left.presheaf.stalk z :=
  ((TK V).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem ev_eq (z : (TK V).left) (k : FractionRing V) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (TK V) : TK V ⟶ TK V).left k) = ev z k := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem ev_unit (z : (TK V).left) (w : Γ(Spec (CommRingCat.of V), ⊤)ˣ) :
    ∃ u : Vˣ, (gm (jK V) z ⊤ w).val = ev z (algebraMap V (FractionRing V) u.val) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom w, ?_⟩
  rw [← gs_unit _ z ⊤ trivial, gs_eq _ z ⊤ trivial]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at e
  exact congrArg ((TK V).left.presheaf.germ ⊤ z trivial).hom e.symm

theorem c_left (D : DegPre V) (χ : D.X) : (D.c χ).left = (DVR.cP D (𝟙_ _) χ).left := by
  rw [DVR.cP, toUnit_unit, Category.id_comp]

theorem exists_setup (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) :
    ∃ (z : (TK V).left) (J : _), Good D.P.L z J ∧ ∀ χ, val (D.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (a χ) * val (ga χ) (toUnit (TK V)).left z J := by
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose J hJ using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, J, hJ, fun χ => Units.ext ?_⟩
  exact ((h χ).2 (TK V) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl)

theorem ev_inj (z : (TK V).left) : Function.Injective (ev z) := (ev z).injective

theorem cub_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hB : D.TauBimult) (x y w : D.X) :
    ∃ u : Vˣ, (a (x + y + w) * a x * a y * a w).val =
      algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + w) * a (y + w)).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK V)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 x y w)) (𝟙 _) z J =
      cubV D.cub z J (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w) := by
    refine (val_cub D.cub (𝟙 (TK V)) hJ (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w)).trans ?_
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB x y w) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [vc, vτ, vτ, vτ, vρ] at e
  simp only [hψ] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have p₁ := prod_cub (DVR.cP D (𝟙_ _) x) (DVR.cP D _ y) (DVR.cP D _ w) f
      have q : eSec D.P.A = (1 : 𝟙_ _ ⟶ D.P.A).left := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
      refine Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ rfl p₁).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c_left, DVR.cPoint_add, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y)).1 (h (x + w)).1) (h (y + w)).1)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y + w)).1 (h x).1) (h y).1) (h w).1)
      D.rig_gen) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε _ D.cub.isGen
        (lift (DVR.cP D (𝟙_ _) x) (lift (DVR.cP D (𝟙_ _) y) (DVR.cP D (𝟙_ _) w))).left))
  have e₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)).symm.trans
    ((hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) rfl)) rfl))
      (val_cub D.cub (toUnit (TK V)) hJ _ _ _)))))
  rw [DVR.comp_cP, DVR.comp_cP, DVR.comp_cP] at e₂
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (x + y + w) * a x * a y * a w) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a (x + y) * a (x + w) * a (y + w)) := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem even_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hE : D.PsiEven) (x : D.X) :
    ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE x) (𝟙 _))
  rw [hψ, hψ, Category.id_comp] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have q : (D.c x).left ≫ (ι[D.P.A]).left = (D.c (-x)).left := by
        have h0 : DVR.cP D (𝟙_ _) 0 = 1 := by simpa using DVR.cPoint_nsmul D (𝟙_ _) 0 x
        have h1 := DVR.cPoint_add D (𝟙_ _) (-x) x
        rw [neg_add_cancel, h0] at h1
        rw [c_left, c_left, eq_inv_of_mul_eq_one_left h1.symm, ← Over.comp_left]
        rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (h x).1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (-x)).1 (DVR.pullGen_isGen D.P.L _ _ _ D.sym_gen (D.c x).left))
  have e₂ := (hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (-x)) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a x) := by
    have e' : Units.map (ev z).toMonoidHom (a (-x)) * val (ga (-x)) (toUnit (TK V)).left z J *
        val D.sym ((toUnit (TK V)).left ≫ (D.c x).left) z J =
        Units.map (ev z).toMonoidHom (a x) * val (ga x) (toUnit (TK V)).left z J := e
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e'
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) :=
  fun _ _ _ _ D ga a h => ⟨cub_part D ga a h, even_part D ga a h⟩

end GlobalTheory.PsiScalUnit
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psiScalars_relations_up_to_baseUnits : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubeRel_even_nsmul {X : Type} [AddCommGroup X] (φ : X → ℤ)
    (h : ∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c))
    (he : ∀ a, φ (-a) = φ a) (a : X) (n : ℕ) : φ (n • a) = (n : ℤ) ^ 2 * φ a := by
  have h0 : φ 0 = 0 := by
    have := h 0 0 0
    simp only [add_zero] at this
    linarith
  have key : ∀ n : ℕ, φ (n • a) = (n : ℤ) ^ 2 * φ a ∧
      φ ((n + 1) • a) = ((n + 1 : ℕ) : ℤ) ^ 2 * φ a := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := h ((n + 1) • a) a (-a)
      have e1 : (n + 1) • a + a + -a = (n + 1) • a := by abel
      have e2 : (n + 1) • a + a = (n + 1 + 1) • a := (succ_nsmul a (n + 1)).symm
      have e3 : (n + 1) • a + -a = n • a := by rw [succ_nsmul]; abel
      rw [e1, e2, e3, add_neg_cancel, he, h0, ih.1, ih.2] at h1
      push_cast at h1 ⊢
      linear_combination -h1
  exact (key n).1

theorem even_quadratic_pos_of_finite_nonpos : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by
  intro X _ _ φ h he hfin a ha
  by_contra hle
  rw [not_lt] at hle
  have hinj : Function.Injective (fun n : ℕ => n • a) := by
    intro m n hmn
    have h1 : ((m : ℤ) - (n : ℤ)) • a = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul]
      exact sub_eq_zero.mpr hmn
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast sub_eq_zero.mp h2
    · exact absurd h2 ha
  refine Set.infinite_of_injective_forall_mem hinj ?_ hfin
  intro n
  show φ (n • a) ≤ 0
  rw [cubeRel_even_nsmul φ h he a n]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dvr_fraction_order (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr

theorem cubeRel_scalars_mem_maximalIdeal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiIn_maximalIdeal_of_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → D.PsiEven → {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ 1)}.Finite → ∀ χ : D.X, χ ≠ 0 → D.PsiIn χ (IsLocalRing.maximalIdeal V) := by
  intro V _ _ _ hV D hT hE hfin χ hχ
  have : IsDiscreteValuationRing V := hV.1
  obtain ⟨ga, a, ha⟩ := exists_psiScal V D
  have hc := GlobalTheory.T.psiScalars_relations_up_to_baseUnits V D ga a ha
  have hm : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hiff := fun x => psiIn_iff_scalar_mem V D ga a ha x _ hm
  rw [hiff]
  refine cubeRel_scalars_mem_maximalIdeal V D.X a (hc.1 hT) (hc.2 hE) ?_ χ hχ
  refine hfin.subset ?_
  intro x hx
  show ¬ _
  rw [pow_one, hiff]
  exact hx

end GlobalTheory
end
