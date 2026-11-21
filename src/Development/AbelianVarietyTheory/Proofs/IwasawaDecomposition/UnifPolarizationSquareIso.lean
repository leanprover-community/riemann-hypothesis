import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiDoubleCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

section
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_cub (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b) ξ J =
      Units.map (cst ξ).toMonoidHom w := by
  have hp : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp]
  refine val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t _ fun k => ?_
  show (_ ≫ (psum _ _ _).left) ≫ _ = _
  rw [Category.assoc, Over.w, Over.w]; rfl

theorem val_sym (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (y : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L _ _ D.sym (D.xK y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  rw [val_pull hJ]
  have hx : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
  rw [hx]
  refine val_int ξ hJc D.sym _ fun k => ?_
  obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
    fin_cases k
    · exact ⟨_, rfl⟩
    · exact ⟨𝟙 _, rfl⟩
  rw [hq, Category.assoc, Over.w q, Over.w]; rfl

theorem val_rig (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) :
    ∃ w : Rˣ, val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  unfold DegPre.rigK
  rw [val_pull hJ]
  have : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [this]
  exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

end

theorem alg {G : Type} [CommGroup G] (A0 Ay Am A2 Vr C0 C1 S : G)
    (h1 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C0 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * (Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h2 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 = A2 * Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * Am⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h3 : Am * S = Ay) :
    A2 = C0 * C0 * C1 * Vr * Vr * Vr * S⁻¹ * Ay ^ 4 := by
  have hC0 := mul_left_cancel h1
  have hAm : Am = Ay * S⁻¹ := eq_mul_inv_of_mul_eq h3
  subst hC0 hAm
  have e : A2 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 * (Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * (Ay * S⁻¹)⁻¹ * Ay⁻¹ * Vr⁻¹))⁻¹ := by
    rw [h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem val_cubP {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
      (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := val_cub D ξ hJc a a' b
  exact ⟨w, (val_pull hJ _ _ _).trans hw⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I)
    (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  intro R _ _ _ I D y r s hr hs
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.toPre.P.isLB D.toPre.P.A.hom
  have b1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult 0 0 y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have b2 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult y (-y) y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even y) (𝟙 _))
  have vt : ∀ a b : D.toPre.X, val (D.toPre.tau a b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = val (D.toPre.psi (a + b)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J *
      (val (D.toPre.psi a) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val (D.toPre.psi b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val D.toPre.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ :=
    fun a b => GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b
  obtain ⟨w0, hw0⟩ := val_cubP D.toPre ξ hJ hJc 0 0 y
  obtain ⟨w1, hw1⟩ := val_cubP D.toPre ξ hJ hJc y (-y) y
  obtain ⟨w5, hw5⟩ := val_rig D.toPre ξ hJ hJc
  obtain ⟨w6, hw6⟩ := val_sym D.toPre ξ hJ hJc y
  rw [hw6] at ev
  rw [hw0, vt, vt, hw5] at b1
  rw [hw1, vt, vt, vt, hw5] at b2
  rw [add_zero, zero_add] at b1
  rw [add_neg_cancel, zero_add, neg_add_cancel, ← two_nsmul] at b2
  have key := alg _ _ _ _ _ _ _ _ b1 b2 ev
  obtain ⟨u1, g1⟩ : ∃ u : Rˣ, (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * r) := val_psi D.toPre ξ hJ hJc y r hr
  obtain ⟨u2, g2⟩ : ∃ u : Rˣ, (val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * s) := val_psi D.toPre ξ hJ hJc (2 • y) s hs
  obtain ⟨W, key2⟩ : ∃ W : Rˣ, val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J =
      Units.map (cst ξ).toMonoidHom W * (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J) ^ 4 :=
    ⟨w0 * w0 * w1 * w5 * w5 * w5 * w6⁻¹, by rw [key]; simp only [map_mul, map_inv]⟩
  have e : cst ξ (u2 * s) = cst ξ (W * (u1 * r) ^ 4) := by
    rw [← g2, key2, map_mul, map_pow, ← g1, Units.val_mul, Units.val_pow_eq_pow_val]; rfl
  have e2 := cst_injective ξ e
  refine ⟨u2 * (W * u1 ^ 4)⁻¹, ?_⟩
  have h3 : ((W * u1 ^ 4 : Rˣ) : R) * r ^ 4 = u2 * s := by push_cast; rw [e2]; ring
  rw [Units.val_mul, ← _root_.mul_assoc, _root_.mul_comm s, ← h3, _root_.mul_comm, ← _root_.mul_assoc, Units.inv_mul,
    _root_.one_mul]

end GlobalTheory.PsiDoubleCoord
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  first | exact @GlobalTheory.PsiDoubleCoord.main | exact GlobalTheory.PsiDoubleCoord.main | (intros; apply GlobalTheory.PsiDoubleCoord.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  first | exact @GlobalTheory.SqLB.exists_sq_gen | exact GlobalTheory.SqLB.exists_sq_gen | (intros; apply GlobalTheory.SqLB.exists_sq_gen <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SqCompare

open GlobalTheory.CoordCompare GlobalTheory.PrimNorm GlobalTheory.MulPull in

theorem sq_law {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta A M), t.IsGen) {Y : Over S} (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (v : LB.Gen (LB.LinComb M (diffφ y a b) ![2, -2, 2, -2])) (hv : v.IsGen) :
    ∃ v' : LB.Gen (LB.LinComb M (diffφ y (a * a) (b * b)) ![1, -1, 1, -1]), v'.IsGen := by
  have hc := fun p q s : Y ⟶ A => diff₃_ptCls (T := Y) hM hT p q s
  have h := (hasGen_iff hM _ _).1 ⟨v, hv⟩
  rw [Fin.prod_univ_four] at h
  refine (hasGen_iff hM _ _).2 ?_
  rw [Fin.prod_univ_four]
  set m := ptCls M Y with hm
  set α := toUnit Y ≫ a
  set β := toUnit Y ≫ b
  have cα : toUnit Y ≫ (a * a) = α * α := MonObj.comp_mul _ _ _
  have cβ : toUnit Y ≫ (b * b) = β * β := MonObj.comp_mul _ _ _
  change m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ) = 1 at h
  change m (y * (toUnit Y ≫ (b * b))) ^ (1 : ℤ) * m (y * (toUnit Y ≫ (a * a))) ^ (-1 : ℤ) *
    m (toUnit Y ≫ (a * a)) ^ (1 : ℤ) * m (toUnit Y ≫ (b * b)) ^ (-1 : ℤ) = 1
  rw [cα, cβ]
  have kα := diff₂_mul_right hc y α α
  have kβ := diff₂_mul_right hc y β β
  calc _ = (diff₂ m y (β * β) * (diff₂ m y β * diff₂ m y β)⁻¹) *
        (diff₂ m y (α * α) * (diff₂ m y α * diff₂ m y α)⁻¹)⁻¹ *
        (m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ)) := by
        apply Additive.ofMul.injective
        simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
    _ = 1 := by rw [← kα, ← kβ, h, mul_inv_cancel, mul_inv_cancel, inv_one, _root_.mul_one, _root_.mul_one]

open GlobalTheory.CoordCompare TorusCoord in

theorem sq_desc {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G)
    (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] [Mono Φ.left] (hp : g'.pG ≫ Φ = g.pG)
    (w : LB.Iso (LB.LinComb D'.P.L (K := Fin 1) (fun _ => 𝟙 D'.P.A.left) (fun _ => 2))
      ((LB.LinComb D.P.L (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => 2)).pull Φ.left)) (hw : w.IsGen)
    (χ : D.X) (χ' : D'.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![2, -2, 2, -2]), v.IsGen := by
  obtain ⟨t, ht, W, hW⟩ := GlobalTheory.T.exists_square_generator_through_squareIso D.P.isLB D'.P.isLB w hw (D'.Oφ g'.pG χ') Oinvε (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![2, -2, 2, -2])
    (fun U _ h => by
      have e2 := prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h
      have e3 : ∏ k, h (g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^ (![2, -2, 2, -2] : Fin 4 → ℤ) k =
          (∏ k, h (((Over.map (thick R I e)).map g.q).left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^
            (![1, -1, 1, -1] : Fin 4 → ℤ) k) ^ (2 : ℤ) := by
        simp only [Fin.prod_univ_four, mul_zpow, ← zpow_mul]
        rfl
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (e3.trans (congrArg (· ^ (2 : ℤ)) e2)).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp, Fintype.prod_sum_type]
      simp only [Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (2 * (-1 : ℤ)) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (2 * (1 : ℤ)) *
          h g.pG.left ^ (2 * (1 : ℤ)) * h (1 : T ⟶ D.P.A).left ^ (2 * (-1 : ℤ)) *
        ((h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) *
         (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ))) =
        (h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹) ^ (2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t χ)) (LB.invGen D.P.L _ _ (g.t χ))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))
      (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))))
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    have hWeq : (fun k => r ≫ D'.Oφ g'.pG χ' k) = (fun k => r' ≫ D'.Oφ g'.pG χ' k) :=
      funext (Oφ_congr χ' g'.pG r r' h₁)
    rw [hu' Z r z J hJ, hu' Z r' z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
      hW Z r z J J' hJ hJ', hW Z r' z J J' hJ hJ', hWeq]
    calc _ = W Z z (fun k => r' ≫ D'.Oφ g'.pG χ' k) J J' *
          (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) ^ 2 := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel
      _ = _ := by
          rw [h₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel)
  exact ⟨v, hv⟩

end GlobalTheory.SqCompare

open GlobalTheory.CoordCompare in

theorem GlobalTheory.SqCompare.c_two_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' hL Φ w hw hΦ hpG xe hval x
  obtain ⟨hN, -, hC, -⟩ := hR
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hpG e)
  have hmono : Mono Φ.hom.left := inferInstance
  set a := D'.toPre.c x ≫ Φ.hom
  set b := D.toPre.c (xe x)
  have desc : ∀ n, ∃ v : LB.Gen (LB.LinComb D.toPre.P.L
      (diffφ (D.toPre.prBe (maximalIdeal R) n) (a * a) (b * b)) ![1, -1, 1, -1]), v.IsGen := fun n => by
    obtain ⟨v, hv⟩ := GlobalTheory.SqCompare.sq_desc (U.gt n) (U'.gt n) Φ.hom (hp' n) w hw (xe x) x
      (fun Z r z J J' hJ hJ' h h' => hval n Z r z J J' hJ hJ' h h' x)
    exact GlobalTheory.SqCompare.sq_law D.toPre.P.isLB ⟨D.toPre.cub.t, D.toPre.cub.isGen⟩ _ _ _ v hv
  have hab : a * a = b * b := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ (a * a)) (toUnit _ ≫ (b * b)) fun n => by
        obtain ⟨v, hv⟩ := desc n
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  have e1 : D'.toPre.c (2 • x) ≫ Φ.hom = a * a := by
    rw [two_nsmul, D'.toPre.c_add, padd, ← Hom.mul_def, MonObj.mul_comp]
  have e2 : D.toPre.c (xe (2 • x)) = b * b := by
    rw [map_nsmul, two_nsmul, D.toPre.c_add, padd, ← Hom.mul_def]
  rw [e1, e2, hab]
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationCharMap_eq_on_even_characters : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  atlas_forward_decl GlobalTheory.SqCompare.c_two_comp
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SquareSectionWeightZero

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  intro R _ _ _ _ G _ _ _ D A U
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨E, hE⟩ := GlobalTheory.FamFree.exists_fam_support (F := FractionRing R) h1.globalFns h2.secTwist
    D.tau_bimult (k := 2) (by norm_num) (0 : D.toPre.X)
  have hE0 : ¬ ∀ j, (E.s 0).f j = 0 := (hE 0).2 ⟨0, by simp⟩
  obtain ⟨s, hs, -⟩ := (U.expand 2 (by norm_num)).2 E
  obtain ⟨r, hr, σ, f, -, hf, hexp⟩ := hs
  refine ⟨σ, f, hexp, fun h0 => hE0 ?_⟩
  have key := (GlobalTheory.ConstFam.secScal_iff_resF D.toPre (FractionRing R) (E.s 0) (f 0) r).1 (hf 0)
  have hf0 : (f 0 : GlobalTheory.ConstFam.SecBMod D.toPre 2 0) = 0 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext h0
  rw [hf0] at key
  erw [map_zero] at key
  have hr' : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r ≠ 0 := by
    intro h
    apply hr
    have hinj : Function.Injective (GlobalTheory.ConstFam.toF (R := R) (FractionRing R)) :=
      (algebraMap (FractionRing R) (FractionRing R)).injective.comp (IsFractionRing.injective R _)
    exact hinj (h.trans (map_zero _).symm)
  let t : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 := E.s 0
  have k2 : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r • t = 0 := key.symm
  have e0 : t = 0 := by rw [← inv_smul_smul₀ hr' t, k2, smul_zero]
  intro j
  exact congrArg (fun q : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 => LB.Sec.f q j) e0

end GlobalTheory.SquareSectionWeightZero
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleSquare_section_weightZero_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  first | exact @GlobalTheory.SquareSectionWeightZero.main | exact GlobalTheory.SquareSectionWeightZero.main | (intros; apply GlobalTheory.SquareSectionWeightZero.main <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem feq_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e : ℕ, U.ExpandsAt e k σ f) → ∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + k • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) k mu α) κ.left z J).val := by
  intro R _ _ _ hCN G _ _ hSA D A U k hk σ f hE mu α T κ y z J hJ
  have hR : AdmBase R (maximalIdeal R) := admissibleBase_of_completeNormalLocalCharZero hCN
  have := hR.1
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((k : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ (pullback.fst G.hom (jK R)))
  have hU := U.expand k hk
  obtain ⟨E, hsE, -⟩ := hU.1 s
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k σ s
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D A G U.toUnifPre k 2 ![1, -1] ![σ, σ] ![f, g]
    (fun i => by fin_cases i; exacts [hE, hg])).1 (fun j => by
      simp [Fin.sum_univ_two, Out.scal])
  obtain rfl : f = g := funext fun α => SecOps.sec_ext fun j => by
    have := H α j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  let ρ : T ⟶ DegPre.BF D.toPre (FractionRing R) := lift κ y
  have ρ₁ : ρ ≫ fst _ _ = κ := lift_fst _ _
  have ρ₂ : ρ ≫ DegPre.prB D.toPre (FractionRing R) = y := lift_snd _ _
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α
  have vu := hv u hu hc _ ρ z J hJ
  have hrel := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (E.fe mu α u hu hc) _ ρ.left z J hJ
  rw [← SectionScalarValuation.secScal_sval (hgE _) _ z hJ, ← SectionScalarValuation.secScal_sval (hgE _) _ z hJ] at hrel
  have htr : (ρ ≫ DegPre.trF D.toPre (FractionRing R) mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      y * cP D.toPre T mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ρ₂, comp_cP, comp_cP]
  rw [vu] at hrel
  rw [← htr, ← congrArg (fun q => sval (f (α + k • mu)) q.left z J) ρ₂]
  rw [ρ₁] at hrel
  simp only [Over.comp_left]
  exact hrel

end GlobalTheory.PsiCompare
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationExpansion_functionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e : ℕ, U.ExpandsAt e k σ f) → ∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + k • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) k mu α) κ.left z J).val := by
  atlas_forward_decl GlobalTheory.PsiCompare.feq_of_expandsAt
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalStructure_square_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  first | exact @GlobalTheory.cube_sq_transport | exact GlobalTheory.cube_sq_transport | (intros; apply GlobalTheory.cube_sq_transport <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famB_wtTwo {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (y : T ⟶ D.P.A) (α : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (y.left ≫ D.famφB α i) ^ DegPre.famε 2 i =
      h y.left * h (y * cP D T α).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have a₀ : y.left ≫ D.famφB α 0 = y.left := Category.comp_id _
  have a₁ : y.left ≫ D.famφB α 1 = (y * cP D T α).left := congrArg (fun z => z.left)
    ((MonObj.comp_mul y (𝟙 _) (cP D _ α)).trans (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : y.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun z => z.left) (comp_cP D y α)
  have a₃ : y.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) y)
  rw [Fin.prod_univ_four, a₀, a₁, a₂, a₃]
  show _ ^ (((2 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  norm_num

theorem sq_unit_cancel {A : Type} [CommRing A] [IsDomain A] {s s' F₁ F₁' : A}
    {θ θ' V V' ωx ωam ωm2 ω1 ωa ωm : Aˣ} (hs : s ≠ 0)
    (h₁ : F₁ = s * (θ * V).val) (h₂ : F₁' = s' * (θ' * V').val)
    (h₃ : F₁ ^ 2 = (ωx * ωam * ωm2⁻¹ * ω1).val * F₁' ^ 2)
    (h₄ : s ^ 2 = (ωa * ωa * ω1⁻¹ * ω1).val * s' ^ 2)
    (h₅ : θ ^ 2 = ωam * ωm2⁻¹ * ωa⁻¹ * ωa⁻¹ * ωm * ωm * ωx * ω1⁻¹ * θ' ^ 2) :
    V' ^ 2 = (ωm * ω1⁻¹) ^ 2 * V ^ 2 := by
  have hs' : s' ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, MulZeroClass.mul_zero] at h₄
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 h₄)
  have E : ωa * ωa * ω1⁻¹ * ω1 * (θ * V) ^ 2 = ωx * ωam * ωm2⁻¹ * ω1 * (θ' * V') ^ 2 :=
    Units.ext (mul_left_cancel₀ (pow_ne_zero 2 hs') (by
      rw [h₁, h₂] at h₃
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h₃ h₄ ⊢
      linear_combination h₃ - ((θ : A) * V) ^ 2 * h₄))
  apply Additive.ofMul.injective
  have E' := congrArg Additive.ofMul E
  have h₅' := congrArg Additive.ofMul h₅
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at E' h₅' ⊢
  linear_combination (norm := abel) h₅' - E'

end GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare in

theorem GlobalTheory.PsiCompare.famMult_sq_corr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  intro R _ _ _ D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y z J J' hJ hJ' hdom h0
  haveI := hΦ
  haveI := hdom
  set κ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R) := fst (TF (R := R) (FractionRing R)) D.toPre.P.A with hκ
  set pB : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A := DegPre.prB D.toPre (FractionRing R) with hpB
  set m' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y) with hm'
  set a : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := pB ≫ Φ.inv with ha
  set x' : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A := a * m'⁻¹ with hx'
  let T := DegPre.BF D.toPre (FractionRing R)
  have hxm : x' * m' = a := inv_mul_cancel_right _ _
  have hmΦ : m' ≫ Φ.hom = cP D.toPre T (xe (2 • y)) := cP_comp Φ.hom (hc y) T
  have haΦ : a ≫ Φ.hom = pB := by rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx'Φ : (x' ≫ Φ.hom) * cP D.toPre T (xe (2 • y)) = pB := by
    rw [← hmΦ, ← MonObj.mul_comp, hxm, haΦ]

  have e₁ := hf (xe (2 • y)) 0 T κ (x' ≫ Φ.hom) z J hJ
  have u₁ : uVal D.toPre (FractionRing R) 2 0 (cP D.toPre _ (xe (2 • y))) (lift κ (x' ≫ Φ.hom)) z J =
      cubV D.toPre.cub z J (cP D.toPre T (xe (2 • y))) (cP D.toPre T (xe (2 • y))) (x' ≫ Φ.hom) := by
    have C := isCub_cubV D.toPre.cub hJ
    have ρ₂ : lift κ (x' ≫ Φ.hom) ≫ DegPre.prB D.toPre (FractionRing R) = x' ≫ Φ.hom := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₁, hx'Φ, zero_add] at e₁

  have e₂ := hf' (2 • y) 0 T κ x' z J' hJ'
  have u₂ : uVal D'.toPre (FractionRing R) 2 0 (cP D'.toPre _ (2 • y)) (lift κ x') z J' =
      cubV D'.toPre.cub z J' m' m' x' := by
    have C := isCub_cubV D'.toPre.cub hJ'
    have ρ₂ : lift κ x' ≫ DegPre.prB D'.toPre (FractionRing R) = x' := lift_snd _ _
    rw [uVal, cPoint_zero, cubN, ρ₂, comp_cP, comp_cP]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul,
      _root_.mul_one, C.face, inv_one]
    rfl
  rw [u₂, hxm, zero_add] at e₂

  have e₃ := hcorr (2 • y) T.left x'.left z J J' hJ hJ'
  have p₄ : x' * m' ^ 2 = a * m' := by rw [pow_two, ← _root_.mul_assoc, hxm]
  rw [prod_famB_wtTwo, cPoint_nsmul, ← hm', p₄, map_nsmul] at e₃

  have e₄ := hcorr 0 T.left a.left z J J' hJ hJ'
  rw [prod_famB_wtTwo, smul_zero, map_zero, cPoint_zero, _root_.mul_one,
    show a.left ≫ Φ.hom.left = pB.left from congrArg (fun q => q.left) haΦ] at e₄

  have e₅ := hcub T z J J' hJ hJ' _ rfl m' m' x'
  have p₁ : m' * m' * x' = a * m' := by rw [mul_comm (m' * m') x', ← _root_.mul_assoc, hxm]
  have p₃ : m' * x' = a := by rw [mul_comm, hxm]
  rw [hmΦ, p₁, p₃, ← sq] at e₅
  exact sq_unit_cancel h0 e₁ e₂ e₃ e₄ e₅
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightTwoFactor_sq_values_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  atlas_forward_decl GlobalTheory.PsiCompare.famMult_sq_corr
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (q ⁻¹ᵁ ⊤) z trivial).hom.comp ((q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem cst_eq_cstHom {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) :
    cst q z a = cstHom q z a :=
  gs_eq q z ⊤ trivial _

theorem cst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {a b : R}
    (h : cst (p ≫ jK R) z a = cst (p ≫ jK R) z b) : a = b := by
  by_contra hne
  have hu := IntegralExpansionLocal.isUnit_cst_of_ne_zero p z (sub_ne_zero.2 hne)
  rw [cst_eq_cstHom, map_sub, ← cst_eq_cstHom, ← cst_eq_cstHom, h, sub_self] at hu
  exact not_isUnit_zero hu

theorem gm_top {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : ⊤ ≤ V) (g : Γ(Spec (CommRingCat.of R), V)ˣ) : ∃ u : Rˣ, (gm q z V g).val = cst q z (u : R) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom (res hV g), ?_⟩
  rw [← gm_res q z hV trivial g, ← gs_unit q z ⊤ trivial]
  simp only [cst, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom _
  rw [Iso.hom_inv_id]
  rfl

theorem gm_of_top {Z X : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (x : Spec (CommRingCat.of R) ⟶ X)
    {f : Z ⟶ X} (hf : f = q ≫ x) {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) (g : Γ(X, V)ˣ) :
    ∃ u : Rˣ, (gm f z V g).val = cst q z (u : R) := by
  subst hf
  rw [← gm_pull q x z V (hV trivial) g]
  exact gm_top q z hV _

end GlobalTheory.PsiFourthCoord

namespace GlobalTheory.PsiFourthCoord

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem val_psi_of_coord (D : DegPre R) (χ : D.X) {r : R} {j : PUnit → D.P.L.ι}
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
    {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : J (p ≫ D.xK χ) = j PUnit.unit) : (val (D.psi χ) p z J).val = cst (p ≫ jK R) z r := by
  have m₁ : p z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := h trivial
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  rw [val_of (D.psi χ) p z J j (fun _ => hJ)]
  refine (gs_unit p z _ m₁ _).symm.trans ((gs_res p z h trivial _).symm.trans ?_)
  refine (congrArg (gs p z _) e.symm).trans ((gs_pull p (jK R) z ⊤ trivial _).trans ?_)
  rw [hto]; rfl

theorem val_famMult_two {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 2 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul]

theorem val_rigK_of_top (D : DegPre R) {Z : Scheme.{0}} (p : Z ⟶ (TK R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J)
    (h : ⊤ ≤ (eSec D.P.A) ⁻¹ᵁ D.P.L.U (J ((p ≫ jK R) ≫ eSec D.P.A))) :
    ∃ u : Rˣ, (val D.rigK p z J).val = cst (p ≫ jK R) z u := by
  have e1 : p ≫ (toUnit (TK R)).left = p ≫ jK R := by
    congr 1
  rw [DegPre.rigK, val_pull hJ, e1]
  rw [val_of D.rig (p ≫ jK R) z J (fun _ => J ((p ≫ jK R) ≫ eSec D.P.A)) (fun _ => rfl)]
  exact gm_top _ z (fun y _ => Set.mem_iInter.2 fun _ => h trivial) _

theorem exists_good_pts (P : PolAV (Spec (CommRingCat.of R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {Z : Scheme.{0}} (t : Z ⟶ Spec (CommRingCat.of R)) (a : Spec (CommRingCat.of F) ⟶ Z) (ha : a ≫ t = DegPre.jFR F)
    (z : Z) (pk : (Spec (CommRingCat.of R) ⟶ P.A.left) → P.L.ι)
    (hpk : ∀ q, q ≫ P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ P.L.U (pk q)) :
    ∃ J, Good P.L z J ∧ ∀ q, q ≫ P.A.hom = 𝟙 _ → J (t ≫ q) = pk q := by
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB z (K := {q : Spec (CommRingCat.of R) ⟶ P.A.left // q ≫ P.A.hom = 𝟙 _})
    (fun q => t ≫ q.1) (fun q => pk q.1) (fun a' b' h => by
      have : a'.1 = b'.1 := GC.vpt_ext F P a'.2 b'.2 (by rw [← ha, Category.assoc, Category.assoc, h])
      rw [this]) (fun q => hpk q.1 q.2 trivial)
  exact ⟨J, hJ, fun q hq => e ⟨q, hq⟩⟩

end GlobalTheory.PsiFourthCoord

open GlobalTheory.PsiFourthCoord ReciprocityTheory.ChartRestriction.G.DVR in

theorem GlobalTheory.psi_coord_fourth_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ D D' Φ w _ nu mu z H r r' hr hr'
  classical
  set π := (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) with hπdef
  have hπ : π ≫ jK R = (DegPre.BF D.toPre (FractionRing R)).hom :=
    (Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A))
  have za : (DegPre.zF D.toPre (FractionRing R)).left ≫ (π ≫ jK R) = DegPre.jFR (FractionRing R) := by
    rw [hπ]; exact Over.w (DegPre.zF D.toPre (FractionRing R))
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨j', hj', h', e'⟩ := hr'
  choose pk hpk using fun q : Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left => GC.exists_chart_top D.toPre.P.L D.toPre.P.isLB q
  choose pk' hpk' using fun q : Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left =>
    GC.exists_chart_top D'.toPre.P.L D'.toPre.P.isLB q
  let pkD : (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun q =>
    if q = (D.toPre.c nu).left then j PUnit.unit else pk q
  let pkD' : (Spec (CommRingCat.of R) ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun q =>
    if q = (D'.toPre.c mu).left then j' PUnit.unit else pk' q
  have hpkD : ∀ q, q ≫ D.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D.toPre.P.L.U (pkD q) := fun q _ => by
    by_cases hq : q = (D.toPre.c nu).left
    · subst hq; simp only [pkD, if_pos rfl]; exact hj
    · simp only [pkD, if_neg hq]; exact (hpk q).ge
  have hpkD' : ∀ q, q ≫ D'.toPre.P.A.hom = 𝟙 _ → ⊤ ≤ q ⁻¹ᵁ D'.toPre.P.L.U (pkD' q) := fun q _ => by
    by_cases hq : q = (D'.toPre.c mu).left
    · subst hq; simp only [pkD', if_pos rfl]; exact hj'
    · simp only [pkD', if_neg hq]; exact (hpk' q).ge
  obtain ⟨J, hJ, eJ⟩ := exists_good_pts D.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD hpkD
  obtain ⟨J', hJ', eJ'⟩ := exists_good_pts D'.toPre.P (FractionRing R) (π ≫ jK R) _ za z pkD' hpkD'
  have HH := H J J' hJ hJ'
  have pc : ∀ {X : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X),
      x.left ≫ X.hom = 𝟙 _ := fun x => Over.w x
  have hc : (D.toPre.c nu).left ≫ D.toPre.P.A.hom = 𝟙 _ := pc _
  have hc' : (D'.toPre.c mu).left ≫ D'.toPre.P.A.hom = 𝟙 _ := pc _
  have he : eSec D.toPre.P.A ≫ D.toPre.P.A.hom = 𝟙 _ := pc η[D.toPre.P.A]
  have he' : eSec D'.toPre.P.A ≫ D'.toPre.P.A.hom = 𝟙 _ := pc η[D'.toPre.P.A]
  have hcΦ : ((D'.toPre.c mu).left ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact hc'
  have heΦ : (eSec D'.toPre.P.A ≫ Φ.hom.left) ≫ D.toPre.P.A.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w Φ.hom]; exact he'
  have V1 := val_psi_of_coord D.toPre nu h e π z J (by
    rw [show π ≫ D.toPre.xK nu = (π ≫ jK R) ≫ (D.toPre.c nu).left from (Category.assoc _ _ _).symm, eJ _ hc]
    simp only [pkD, if_pos rfl])
  have V1' := val_psi_of_coord D'.toPre mu h' e' π z J' (by
    rw [show π ≫ D'.toPre.xK mu = (π ≫ jK R) ≫ (D'.toPre.c mu).left from (Category.assoc _ _ _).symm, eJ' _ hc']
    simp only [pkD', if_pos rfl])
  obtain ⟨a, V2⟩ := val_rigK_of_top D.toPre π z J hJ (by rw [eJ _ he]; exact hpkD _ he)
  obtain ⟨a', V2'⟩ := val_rigK_of_top D'.toPre π z J' hJ' (by rw [eJ' _ he']; exact hpkD' _ he')
  have hψ : (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
      (π ≫ jK R) ≫ (D'.toPre.c mu).left := by
    rw [hπ, cP, Over.comp_left]; rfl
  have hψ1 : (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = (π ≫ jK R) ≫ eSec D'.toPre.P.A := by
    rw [hπ]; rfl
  have O1 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left ≫ Φ.hom.left) =
        pkD ((D'.toPre.c mu).left ≫ Φ.hom.left) := by rw [hψ, Category.assoc]; exact eJ _ hcΦ
    have k2 : J' (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left =
        pkD' (D'.toPre.c mu).left := by rw [hψ]; exact eJ' _ hc'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (D'.toPre.c mu).left hψ (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ hcΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ hc' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  have O2 : ∃ b : Rˣ, (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
      (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left).val = cst (π ≫ jK R) z b := by
    have k1 : J ((1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left ≫ Φ.hom.left) =
        pkD (eSec D'.toPre.P.A ≫ Φ.hom.left) := by rw [hψ1, Category.assoc]; exact eJ _ heΦ
    have k2 : J' (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left = pkD' (eSec D'.toPre.P.A) := by
      rw [hψ1]; exact eJ' _ he'
    unfold ExpTrans.om Geo.Tor.gw
    refine gm_of_top (π ≫ jK R) z (eSec D'.toPre.P.A) hψ1 (fun y _ => ?_) _
    refine ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have m := hpkD _ heΦ (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k1] at m
      exact m
    · have m := hpkD' _ he' (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
      rw [← k2] at m
      exact m
  obtain ⟨b, O1⟩ := O1
  obtain ⟨b', O2⟩ := O2
  rw [val_famMult_two D'.tau_bimult _ hJ', val_famMult_two D.tau_bimult _ hJ] at HH
  set Ωc := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) mu).left
  set Ω1 := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
    (1 : DegPre.BF D.toPre (FractionRing R) ⟶ D'.toPre.P.A).left
  have HH2 : (val (D'.toPre.psi mu) π z J' ^ 2 * val D'.toPre.rigK π z J' ^ 2) ^ 2 * Ω1 ^ 2 =
      Ωc ^ 2 * (val (D.toPre.psi nu) π z J ^ 2 * val D.toPre.rigK π z J ^ 2) ^ 2 := by
    rw [HH, mul_pow, inv_pow, mul_right_comm, inv_mul_cancel_right]
  have V := congrArg Units.val HH2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at V
  rw [V1, V1', V2, V2', O1, O2] at V
  have V' : cst (π ≫ jK R) z (r' ^ 4 * ((a' : R) ^ 4 * (b' : R) ^ 2)) =
      cst (π ≫ jK R) z ((b : R) ^ 2 * (a : R) ^ 4 * r ^ 4) := by
    simp only [cst_eq_cstHom, map_mul, map_pow] at V ⊢
    linear_combination V
  have hR := cst_inj π z V'
  refine ⟨(b ^ 2 * a ^ 4) * (a' ^ 4 * b' ^ 2)⁻¹, ?_⟩
  have k : r ^ 4 * ((b ^ 2 * a ^ 4 : Rˣ) : R) = r' ^ 4 * ((a' ^ 4 * b' ^ 2 : Rˣ) : R) := by
    push_cast
    linear_combination -hR
  rw [Units.val_mul, ← _root_.mul_assoc, k, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_coordinates_fourthPower_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  atlas_forward_decl GlobalTheory.psi_coord_fourth_associated
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiFourth

theorem key : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR D D' Φ w hw hΦ xe hc f f' hf hf' hcorr hcub hne y r r' hr hr'
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  haveI : IsIntegral (DegPre.BF D.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D.toPre.P.A.hom).flip
  have ne : ∀ J, Geo.Tor.Good D.toPre.P.L (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J →
      sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J ≠ 0 := by
    intro J hJ h0
    apply hne
    have hL := D.toPre.P.isLB
    have inj := PullIntegral.prB_app_injective D.toPre (FractionRing R)
    have e₀ := ThetaScalar.eq_zero_of_germ (H1.SectionArithmetic.pullSec (f 0) (DegPre.prB D.toPre (FractionRing R)).left) _ hJ
      (by rw [H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, Category.id_comp, h0])
    exact fun j => PullIntegral.sec_ext_of_inj hL _ inj (s' := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero) (fun y J hJ => by
      have := ThetaScalar.sval_eq_zero _ e₀ (𝟙 _) y hJ
      rw [H1.SectionArithmetic.sval_pullSec _ _ _ y hJ] at this
      rw [this]
      exact (ThetaScalar.sval_eq_zero ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero (fun _ => rfl) _ y hJ).symm) j
  exact GlobalTheory.T.psi_coordinates_fourthPower_associated R D D' Φ w hw (xe (2 • y)) (2 • y) _
    (fun J J' hJ hJ' => GlobalTheory.T.weightTwoFactor_sq_values_correspond R D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y _ J J' hJ hJ'
      inferInstance (ne J hJ)) r r' hr hr'

end GlobalTheory.PsiFourth
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  atlas_forward_decl GlobalTheory.PsiFourth.key
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourth

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' _ Φ w wL hw hwL hΦ hlev xe ht hc
  obtain ⟨σ, f, hE, hne⟩ := GlobalTheory.T.exists_bundleSquare_section_weightZero_nonzero R hR G hG D A U
  obtain ⟨σ', f', hE', hcorr⟩ := GlobalTheory.T.psi_square_even_terms_correspond_transport R hR G hG D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  exact GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation R hR D D' Φ w hw hΦ xe hc f f' (GlobalTheory.T.uniformisationExpansion_functionalEquation R hR G hG D A U 2 (by norm_num) σ f hE)
    (GlobalTheory.T.uniformisationExpansion_functionalEquation R hR G hG D' A' U' 2 (by norm_num) σ' f' hE') hcorr (GlobalTheory.T.cubicalStructure_square_transport R hR D D' Φ w hw hΦ) hne

end GlobalTheory.PsiFourth
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.PsiFourth.main | exact GlobalTheory.PsiFourth.main | (intros; apply GlobalTheory.PsiFourth.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqUnifCoord

theorem associated_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b : R} {n : ℕ}
    (hn : 0 < n) (h : Associated (a ^ n) (b ^ n)) : Associated a b := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn.ne'] at h
    rw [(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at h
    exact ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))
  obtain ⟨u, hu⟩ := h
  set K := FractionRing R
  have inj := IsFractionRing.injective R K
  have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (inj (h0.trans (map_zero _).symm))
  have hb' : algebraMap R K b ≠ 0 := fun h0 => hb (inj (h0.trans (map_zero _).symm))
  have hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]
  have hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))
  have hcd : c * d = 1 := inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b),
    div_self (mul_ne_zero ha' hb')])
  refine ⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩
  show algebraMap R K (a * c) = algebraMap R K b
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' hL
  have hA := admissibleBase_of_completeNormalLocalCharZero hR
  haveI : CharZero R := hR.2.2.2
  haveI : IsIntegrallyClosed R := hR.2.1
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre
  obtain ⟨Φ, w, wL, hw, hwL, hm, hp⟩ := GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL
  have hc := GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe
  refine ⟨xe, fun y r r' hr hr' => ?_⟩
  obtain ⟨⟨s, hs, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))
  obtain ⟨⟨s', hs', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)
  have a1 : Associated s (r ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)
  have a2 : Associated s' (r' ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'
  have a3 : Associated (s ^ 4) (s' ^ 4) :=
    GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'
  refine associated_of_pow (n := 8) (by norm_num) ?_
  have e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4 := by ring
  have e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4 := by ring
  rw [e1, e2]
  exact ((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))

end GlobalTheory.SqUnifCoord
end
end
