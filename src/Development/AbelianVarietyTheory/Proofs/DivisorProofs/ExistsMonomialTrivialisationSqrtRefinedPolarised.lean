import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.PsiEvenCoordUnit

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem alg' {G : Type} [CommGroup G] (a b c x y : G) (h : b * y * c = a * x) : y = a * b⁻¹ * c⁻¹ * x := by
  rw [mul_right_comm (a * b⁻¹), mul_right_comm a, ← h, mul_right_comm (b * y), mul_right_comm b, mul_inv_cancel,
    _root_.one_mul, mul_inv_cancel_right]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  intro R _ _ _ D hE y x x' hx hx'
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, val D.sym (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact xK_eq D y
    rw [this]
    refine val_int ξ hJc D.sym (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A,
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨j, h, i1, rfl⟩ := hx
  obtain ⟨j', h', i1', rfl⟩ := hx'
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc y j i1 (h trivial)
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc (-y) j' i1' (h' trivial)
  have e1 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.psi y).s j) = kU (genVal (D.psi y) j h) :=
    Units.ext (gm_genVal ξ (D.psi y) j h)
  have e2 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j') ((D.psi (-y)).s j') = kU (genVal (D.psi (-y)) j' h') :=
    Units.ext (gm_genVal ξ (D.psi (-y)) j' h')
  have f : cU c2 * kU (genVal (D.psi (-y)) j' h') * cU w = cU c1 * kU (genVal (D.psi y) j h) :=
    (congrArg₂ (· * ·) (g2.trans (congrArg (cU c2 * ·) e2)) hw).symm.trans
      (e.trans (g1.trans (congrArg (cU c1 * ·) e1)))
  refine ⟨c1 * c2⁻¹ * w⁻¹, ?_⟩
  have k3 : genVal (D.psi (-y)) j' h' = Units.map (algebraMap R (FractionRing R)).toMonoidHom (c1 * c2⁻¹ * w⁻¹) *
      genVal (D.psi y) j h := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [map_mul]
    change kU _ = cU (c1 * c2⁻¹ * w⁻¹) * kU _
    rw [map_mul, map_mul, map_inv, map_inv]
    exact alg' _ _ _ _ _ f
  exact congrArg Units.val k3

end GlobalTheory.PsiEvenCoordUnit
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  first | exact @GlobalTheory.PsiEvenCoordUnit.main | exact GlobalTheory.PsiEvenCoordUnit.main | (intros; apply GlobalTheory.PsiEvenCoordUnit.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  first | exact @GlobalTheory.TauCoordQuot.main | exact GlobalTheory.TauCoordQuot.main | (intros; apply GlobalTheory.TauCoordQuot.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refining_degenerationData_tauCoordinate_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  first | exact @GlobalTheory.RefTauCoord.main | exact GlobalTheory.RefTauCoord.main | (intros; apply GlobalTheory.RefTauCoord.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoTriv

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem psiCoord_zero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult)
    (x : (FractionRing R)ˣ) (hx : IsPsiCoord D 0 x) :
    ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) u := by
  obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D 0
  have h := PsiCoordLocal.generic_le D 0 j hj
  have hU := PsiCoordLocal.psiUnitOn_zero D hB
  obtain ⟨s, -, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj h
  obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
  have hr : PsiCoord D 0 r := ⟨j, hj, h, e⟩
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.1
    (PsiCoordLocal.not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial hU hr)
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D 0 r).1 hr
  obtain ⟨v, hv⟩ := IsPsiCoord.unique hx hx₀
  refine ⟨v * hu.unit, ?_⟩
  rw [hv, Units.val_mul, e₀, Units.val_mul, IsUnit.unit_spec, map_mul]
  rfl

theorem exists_unit_of_sq {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (g : FractionRing R) (w : Rˣ)
    (h : g ^ 2 = algebraMap R (FractionRing R) w) : ∃ a : Rˣ, g = algebraMap R (FractionRing R) a := by
  have hw : algebraMap R (FractionRing R) (w : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w.ne_zero
  have hg : g ≠ 0 := by rintro rfl; exact hw (by rw [← h]; ring)
  have int : ∀ (g : FractionRing R) (w : Rˣ), g ^ 2 = algebraMap R (FractionRing R) w →
      ∃ a : R, algebraMap R (FractionRing R) a = g := fun g w h => by
    refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Polynomial.X ^ 2 - Polynomial.C (w : R),
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [h]
  obtain ⟨a, ha⟩ := int g w h
  obtain ⟨b, hb⟩ := int g⁻¹ w⁻¹ (by
    rw [inv_pow, h]
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one]))
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, ha, hb, mul_inv_cancel₀ hg, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha.symm⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) [IsLocalRing R'] (m : ℕ) (t : Fin m → R) (r : Fin m → R') (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R' → Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.PsiEven → D.TauBimult → Q.IsMonomialTau t δ → (∀ i y, 0 ≤ δ i y y) → (∀ i, t i ≠ 0) → (∀ i, r i ^ 2 = ρ (t i)) → IsMonomial D r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ R' _ _ Q ρ D e _ m t r δ hCN hρ hH hE hB hQ hδ ht hr y
  haveI : IsIntegrallyClosed R' := hCN.2.1
  set n : Fin m → ℕ := fun i => (δ i (e y) (e y)).toNat with hn_def
  have hn : ∀ i, δ i (e y) (e y) = n i := fun i => (Int.toNat_of_nonneg (hδ i (e y))).symm
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R' D y (-y)
  obtain ⟨k, hk, hkc⟩ := hQ (e y) (e (-y))
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.T.refining_degenerationData_tauCoordinate_unit R R' Q ρ D e hρ hH.refines y (-y) k hkc x hx
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient R' D y (-y) x _ _ _ hx h0 (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit R' D hE y _ _ (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := psiCoord_zero D hB _ (psiCoord_spec D 0)
  set X : FractionRing R' := (psiCoord D y : FractionRing R') with hX
  have hX0 : X ≠ 0 := (psiCoord D y).ne_zero
  have hσ : ∀ s, IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) s) =
      algebraMap R' (FractionRing R') (ρ s) := fun s => IsFractionRing.lift_algebraMap _ s
  have hneg : ∀ i, δ i (e y) (e (-y)) = -(n i : ℤ) := fun i => by
    rw [map_neg, map_neg, hn]
  have hr0 : ∀ i, algebraMap R' (FractionRing R') (r i) ≠ 0 := fun i h => by
    have : algebraMap R' (FractionRing R') (ρ (t i)) = 0 := by rw [← hr i, map_pow, h, zero_pow two_ne_zero]
    exact ht i (hρ ((IsFractionRing.injective R' (FractionRing R')) (by rw [this, map_zero, map_zero])))
  set P : FractionRing R' := ∏ i, algebraMap R' (FractionRing R') (r i) ^ n i with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hr0 i)
  have hk' : IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) = (P ^ 2)⁻¹ := by
    rw [hk, map_prod, hP, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, hσ, hneg, ← hr i, map_pow, zpow_neg, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  rw [hk'] at hu₁
  rw [hu₄, hu₃] at hu₂
  have hsq : (X / P) ^ 2 = algebraMap R' (FractionRing R') (u₂ * u₄ * u₃⁻¹ * u₁⁻¹ : R'ˣ) := by
    have h1 := hu₁.symm.trans hu₂
    have hu : ∀ u : R'ˣ, algebraMap R' (FractionRing R') (u : R') ≠ 0 := fun u =>
      (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).2 u.ne_zero
    simp only [Units.val_mul, map_mul, map_units_inv]
    have := hu u₁; have := hu u₂; have := hu u₃; have := hu u₄
    have h1' : algebraMap R' (FractionRing R') (u₁ : R') = algebraMap R' (FractionRing R') (u₂ : R') *
        algebraMap R' (FractionRing R') (u₄ : R') * X⁻¹ * (algebraMap R' (FractionRing R') (u₃ : R') * X)⁻¹ * P ^ 2 := by
      rw [← h1, inv_mul_cancel_right₀ (pow_ne_zero 2 hP0)]
    rw [h1']
    field_simp
  obtain ⟨a, ha⟩ := exists_unit_of_sq (X / P) _ hsq
  have hcoord : PsiCoord D y (a * ∏ i, r i ^ n i) := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y _).2
    ⟨psiCoord D y, psiCoord_spec D y, by
      rw [map_mul, map_prod, ← ha]; simp only [map_pow]; rw [← hP, div_mul_cancel₀ _ hP0]⟩
  refine ⟨a, n, fun i => ?_, hcoord⟩
  simp [pull, hn]

end GlobalTheory.MonoTriv
end
