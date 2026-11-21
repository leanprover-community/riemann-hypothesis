import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionOfHomomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.QuotientTiedToDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleTrivialization

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuotLift

theorem exists_section_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R]
    [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π →
    ∀ (U : Over (Sp R₁)), Smooth U.hom → ∀ x₀ : Sp R ⟶ U.left, x₀ ≫ U.hom = spMap π →
    ∃ x : Sp R₁ ⟶ U.left, x ≫ U.hom = 𝟙 _ ∧ spMap π ≫ x = x₀ := by
  intro R₁ R _ _ _ _ _ hc π hπ U hU x₀ hx
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint R) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R₁) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of R) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  haveI : Algebra.FormallySmooth R₁ (U.left.presheaf.stalk y) := hs
  have hle : RingHom.ker π ≤ maximalIdeal R₁ := by
    apply le_maximalIdeal
    intro h
    have h1 : (1 : R₁) ∈ RingHom.ker π := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : IsAdicComplete (RingHom.ker π) R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ _ _ hle hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let E := RingHom.quotientKerEquivOfSurjective hπ
  let f : U.left.presheaf.stalk y →ₐ[R₁] R₁ ⧸ RingHom.ker π :=
    { (E.symm : R →+* R₁ ⧸ RingHom.ker π).comp χ₀.hom with
      commutes' := fun r => by
        apply E.injective
        have h2 : χ₀.hom (α.hom r) = π r := congrArg (fun g => g.hom r) e₁
        change E (E.symm (χ₀.hom (α.hom r))) = E (Ideal.Quotient.mk _ r)
        rw [RingEquiv.apply_symm_apply, h2]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := RingHom.ker π) f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom π = χ₀ := by
    ext a
    have h3 := congr($hg a)
    change π (g a) = χ₀.hom a
    have h4 : E (Ideal.Quotient.mk _ (g a)) = E (f a) := congrArg E h3
    rw [show f a = E.symm (χ₀.hom a) from rfl, RingEquiv.apply_symm_apply] at h4
    exact h4
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    refine (congrArg Spec.map ?_).trans (Spec.map_id _)
    ext r
    exact g.commutes r
  · rw [spMap, ← Spec.map_comp_assoc, hg', hχ₀]

end GlobalTheory.QuotLift
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_smooth_section_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ (U : Over (Sp R₁)), Smooth U.hom → ∀ x₀ : Sp R ⟶ U.left, x₀ ≫ U.hom = spMap π → ∃ x : Sp R₁ ⟶ U.left, x ≫ U.hom = 𝟙 _ ∧ spMap π ≫ x = x₀ := by
  atlas_forward_decl GlobalTheory.QuotLift.exists_section_lift
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_function_of_homomorphism : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A), (∀ a b, h (a + b) = h a * h b) → ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  first | exact @GlobalTheory.hom_eq_evenness_defect_of_cube | exact GlobalTheory.hom_eq_evenness_defect_of_cube | (intros; apply GlobalTheory.hom_eq_evenness_defect_of_cube <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescale_psi_even_tau_bimult_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ), (D.PsiEven → ((GlobalTheory.PolDeg.rescale D g).PsiEven ↔ ∀ a : D.X, g (-a) = g a)) ∧ (D.TauBimult → ((GlobalTheory.PolDeg.rescale D g).TauBimult ↔ (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)))) := by
  first | exact @GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff | exact GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff | (intros; apply GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff <;> assumption)
end

section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB




theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) :
    Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  Wit.refines_ofDeg D hB


open GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.InhTate in

theorem isMonomialTau_arcData (k : Type) [Field k] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y) (hp : ∀ y, y ≠ 0 → 0 < be y y)
    (he : ∀ y, (2 : ℤ) ∣ be y y) :
    (ofDeg (arcData k be hs hp he).toPre (arcData k be hs hp he).tau_bimult).IsMonomialTau
      ![PowerSeries.X] ![be] := fun (a b : X) => by
  refine ⟨arcVar k ^ (be a b), ?_, cg _ _ 1, cg_isGen _ _ _, fun z J hJ => ?_⟩
  · rw [Fin.prod_univ_one]
    exact Units.val_zpow_eq_zpow_val _ _
  have e1 := (Wit.exists_tau (arcData k be hs hp he).toPre a b).choose_spec.2 _ (𝟙 _) z J hJ
  refine e1.trans ?_
  have e2 : val ((arcData k be hs hp he).toPre.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (unitOn (arcVar k ^ (be a b))) := by
    exact (congrArg (gm _ z _) (arcData_tau_isConst k be hs hp he a b _)).trans (gm_res _ z _ (hJ.mem _ _) _)
  rw [e2]
  refine Eq.trans ?_ (congrArg (_ * ·) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).symm
  exact (_root_.mul_one _).symm

end GlobalTheory.PolDeg
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem evenDefect_one_iff (D : DegPre R) : EvenDefect D (fun _ => 1) ↔ D.PsiEven := by
  have e : unitOn (1 : (FractionRing R)ˣ) = 1 := map_one _
  constructor
  · intro h χ
    refine corr_of_val D.P.isLB fun y J hJ => ?_
    have := h χ y J hJ
    rw [e, map_one, _root_.one_mul] at this
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    exact this
  · intro h χ z J hJ
    have := val_corr hJ (h χ) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at this
    rw [e, map_one, _root_.one_mul]
    exact this

theorem evenDefect_rescale (D : DegPre R) (h g : D.X → (FractionRing R)ˣ) (H : EvenDefect D h) :
    EvenDefect (rescale D g) (fun χ : D.X => h χ * g (-χ) * (g χ)⁻¹) := by
  intro χ z J hJ
  have := H χ z J hJ
  have a : ∀ χ : D.X, val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 (TK R).left) z J := fun χ =>
    GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ
  let u : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
    (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)
  have key : ∀ (χ : D.X) (p m s : ((TK R).left.presheaf.stalk z)ˣ), m * s = u (h χ) * p →
      u (g (-χ)) * m * s = u (h χ * g (-χ) * (g χ)⁻¹) * (u (g χ) * p) := fun χ p m s e => by
    rw [_root_.mul_assoc, e, map_mul, map_mul, map_inv]
    generalize u (h χ) = A, u (g (-χ)) = B, u (g χ) = C
    rw [_root_.mul_assoc (A * B), inv_mul_cancel_left, mul_left_comm, _root_.mul_assoc]
  exact (congrArg (fun q => q * val D.sym (D.xK χ) z J) (a (-(show D.X from χ)))).trans
    ((key χ _ _ _ this).trans (congrArg (fun q => u (h χ * g (-(show D.X from χ)) * (g χ)⁻¹) * q) (a χ).symm))





end GlobalTheory.PolDeg
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.RescaleBimult

variable {R : Type} [CommRing R] [IsDomain R]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add]; exact MonObj.comp_mul _ _ _

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_cub3 (D : DegPre R) (a a' b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) := by
  refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem exists_defect (D : DegPre R) (a a' b : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J * val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J *
      val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) *
        (val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J * val (D.psi (a' + b)) (𝟙 _) z J) := by
  let t := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a' + b)) (D.psi a)) (D.psi a')) (D.psi b)) D.rigK)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _)) (D.psi_gen _))
    (D.psi_gen _)) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  let t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.psi (a + a')) (D.psi (a + b))) (D.psi (a' + b))
  have ht' : t'.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (D.psi_gen _))
    (D.psi_gen _)
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht t' ht' (fun U _ h => by
    refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
      (prod_cub (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) h))).trans ?_
    rw [← pt_add, ← pt_add, ← pt_add, ← pt_add]
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, zpow_neg, zpow_one]
    have e : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
    erw [e]
    simp only [ptK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel)
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (a + a' + b)) (𝟙 _) z J * val (D.psi a) (𝟙 _) z J *
      val (D.psi a') (𝟙 _) z J * val (D.psi b) (𝟙 _) z J * val D.rigK (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b) :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (val_mul hJ _ _ _) rfl)) rfl)) rfl)) (val_cub3 D a a' b hJ))
  have e₂ : val t' (𝟙 _) z J = val (D.psi (a + a')) (𝟙 _) z J * val (D.psi (a + b)) (𝟙 _) z J *
      val (D.psi (a' + b)) (𝟙 _) z J :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)
  rw [← e₁, ← e₂]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem exists_rescale_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  intro R _ _ D
  choose F hF using exists_defect D
  let z₀ : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  have C := isCub_cubV D.cub hJ₀
  have um : ∀ u v : (FractionRing R)ˣ, unitOn (u * v) = unitOn u * unitOn v :=
    fun u v => map_mul _ _ _
  have ui : ∀ u : (FractionRing R)ˣ, unitOn u⁻¹ = (unitOn u)⁻¹ := fun u => map_inv _ _
  have E := fun {z : (TK R).left} {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference D.X (FractionRing R)ˣ F
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF b a c z₀ J₀ hJ₀)
      rw [add_comm b a, C.s01] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun a b c => gm_unitOn_inj z₀ (by
      have h₁ := E (hF a b c z₀ J₀ hJ₀)
      have h₂ := E (hF a c b z₀ J₀ hJ₀)
      rw [add_comm c b, add_right_comm a c b, C.s12] at h₂
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂
      linear_combination (norm := abel) h₂ - h₁))
    (fun x x' x'' y => gm_unitOn_inj z₀ (by
      have h₁ := E (hF (x + x') x'' y z₀ J₀ hJ₀)
      have h₂ := E (hF x x' y z₀ J₀ hJ₀)
      have h₃ := E (hF x (x' + x'') y z₀ J₀ hJ₀)
      have h₄ := E (hF x' x'' y z₀ J₀ hJ₀)
      have h₅ := E (C.coc (toUnit (TK R) ≫ D.c x) (toUnit (TK R) ≫ D.c x') (toUnit (TK R) ≫ D.c x'')
        (toUnit (TK R) ≫ D.c y))
      rw [← pt_add, ← pt_add] at h₅
      rw [← add_assoc x x' x''] at h₃
      rw [um, um, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at h₁ h₂ h₃ h₄ h₅ ⊢
      linear_combination (norm := abel) h₃ + h₄ - h₁ - h₂ + h₅))
  refine ⟨fun x => (g x)⁻¹, fun (a a' b : D.X) => corr_of_val D.P.isLB fun z J hJ => ?_⟩
  have hp : ∀ x : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).psi x) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J := fun x =>
    (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (by rw [ui, map_inv]; rfl)
  have ht : ∀ x y : D.X, val ((GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹).tau x y) (𝟙 _) z J =
      (gm (𝟙 (TK R).left) z ⊤ (unitOn (g (x + y))))⁻¹ * val (D.psi (x + y)) (𝟙 _) z J *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g x)))⁻¹ * val (D.psi x) (𝟙 _) z J)⁻¹ *
      ((gm (𝟙 (TK R).left) z ⊤ (unitOn (g y)))⁻¹ * val (D.psi y) (𝟙 _) z J)⁻¹ *
      (val D.rigK (𝟙 _) z J)⁻¹ := fun x y =>
    (val_tau (GlobalTheory.PolDeg.rescale D fun x => (g x)⁻¹) x y hJ).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (hp (x + y)) (congrArg (·⁻¹) (hp x))) (congrArg (·⁻¹) (hp y))) rfl)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht (a + a') b) (val_cub3 D a a' b hJ))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (ht a b) (ht a' b))).symm)
  have h₁ := E (hF a a' b z J hJ)
  have h₂ := congrArg (fun u => gm (𝟙 (TK R).left) z ⊤ (unitOn u)) (hg a a' b)
  simp only [um, map_mul] at h₂
  have h₃ := E h₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at h₁ h₃ ⊢
  linear_combination (norm := abel) h₁ + h₃

end GlobalTheory.RescaleBimult
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_rescale_tau_bimult_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  atlas_forward_decl GlobalTheory.RescaleBimult.exists_rescale_tauBimult
end

section
section
namespace GlobalTheory

theorem exists_even_cube_correction : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (U V : Type) [CommGroup U] [CommGroup V] (e : U →* V), Function.Injective e → ∀ a : X → V, (∀ x y w : X, ∃ u : U, a (x + y + w) * a x * a y * a w = e u * (a (x + y) * a (x + w) * a (y + w))) → (∀ x : X, ∃ u : U, a (-x) = e u * a x) → ∃ c : X → V, (∀ x y w : X, c (x + y + w) * c x * c y * c w = c (x + y) * c (x + w) * c (y + w)) ∧ (∀ x : X, c (-x) = c x) ∧ ∀ x : X, ∃ u : U, c x * a x = e u := by
  intro X _ _ _ U V _ _ e he a h3 hneg
  choose f hf using h3
  choose n hn using hneg
  have tA : ∀ {p q : V}, Additive.ofMul p = Additive.ofMul q → p = q := fun h => h
  have hfA : ∀ x y w, Additive.ofMul (a (x + y + w)) + Additive.ofMul (a x) + Additive.ofMul (a y)
      + Additive.ofMul (a w) = Additive.ofMul (e (f x y w)) + (Additive.ofMul (a (x + y))
      + Additive.ofMul (a (x + w)) + Additive.ofMul (a (y + w))) := fun x y w => by
    simpa only [ofMul_mul] using congrArg Additive.ofMul (hf x y w)
  have hnA : ∀ x, Additive.ofMul (a (-x)) = Additive.ofMul (e (n x)) + Additive.ofMul (a x) :=
    fun x => by simpa only [ofMul_mul] using congrArg Additive.ofMul (hn x)

  have hs1 : ∀ x y w, f x y w = f y x w := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA y x w
    rw [add_comm y x] at h2
    linear_combination (norm := module) h2 - h1
  have hs2 : ∀ x y w, f x y w = f x w y := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA x w y
    rw [add_right_comm x w y, add_comm w y] at h2
    linear_combination (norm := module) h2 - h1
  have hc : ∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y := by
    intro x x' x'' y
    apply he; apply tA
    simp only [map_mul, ofMul_mul]
    have h1 := hfA (x + x') x'' y
    have h2 := hfA x x' y
    have h3 := hfA x (x' + x'') y
    have h4 := hfA x' x'' y
    rw [← add_assoc x x' x''] at h3
    linear_combination (norm := module) h3 + h4 - h1 - h2
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference X U f hs1 hs2 hc
  have hgA : ∀ x y w, Additive.ofMul (e (f x y w)) + (Additive.ofMul (e (g (x + y)))
      + Additive.ofMul (e (g (x + w))) + Additive.ofMul (e (g (y + w))))
      = Additive.ofMul (e (g (x + y + w))) + Additive.ofMul (e (g x)) + Additive.ofMul (e (g y))
      + Additive.ofMul (e (g w)) := fun x y w => by
    simpa only [map_mul, ofMul_mul] using congrArg (fun v => Additive.ofMul (e v)) (hg x y w)

  obtain ⟨b, hb⟩ : ∃ b : X → V, ∀ x, b x = a x * (e (g x))⁻¹ := ⟨_, fun _ => rfl⟩
  have hbA : ∀ x, Additive.ofMul (b x) = Additive.ofMul (a x) - Additive.ofMul (e (g x)) :=
    fun x => by rw [hb, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hΘb : ∀ x y w, Additive.ofMul (b (x + y + w)) + Additive.ofMul (b x) + Additive.ofMul (b y)
      + Additive.ofMul (b w) = Additive.ofMul (b (x + y)) + Additive.ofMul (b (x + w))
      + Additive.ofMul (b (y + w)) := fun x y w => by
    simp only [hbA]
    linear_combination (norm := module) hfA x y w + hgA x y w
  have hb0 : Additive.ofMul (b 0) = 0 := by
    have h0 := hΘb 0 0 0
    simp only [add_zero] at h0
    linear_combination (norm := module) h0

  have hε : ∀ x y, Additive.ofMul (b (-(x + y))) - Additive.ofMul (b (x + y))
      = (Additive.ofMul (b (-x)) - Additive.ofMul (b x))
        + (Additive.ofMul (b (-y)) - Additive.ofMul (b y)) := fun x y => by
    have t := hΘb x y (-(x + y))
    have e1 : x + y + -(x + y) = 0 := add_neg_cancel _
    have e2 : x + -(x + y) = -y := by abel
    have e3 : y + -(x + y) = -x := by abel
    rw [e1, e2, e3] at t
    linear_combination (norm := module) t - hb0
  obtain ⟨h, hh⟩ : ∃ h : X → U, ∀ x, h x = n x * g x * (g (-x))⁻¹ := ⟨_, fun _ => rfl⟩
  have heh : ∀ x, Additive.ofMul (e (h x)) = Additive.ofMul (b (-x)) - Additive.ofMul (b x) :=
    fun x => by
      rw [hh, e.map_mul, e.map_mul, e.map_inv, ofMul_mul, ofMul_mul, ofMul_inv, hbA, hbA]
      linear_combination (norm := module) -(hnA x)
  have hhom : ∀ x y, h (x + y) = h x * h y := fun x y => by
    apply he; apply tA
    rw [map_mul, ofMul_mul, heh, heh, heh, neg_add_rev, add_comm (-y) (-x)]
    have := hε x y
    rw [neg_add_rev, add_comm (-y) (-x)] at this
    exact this
  obtain ⟨k, hk3, hkneg⟩ := GlobalTheory.hom_eq_evenness_defect_of_cube X U h hhom
  refine ⟨fun x => e (k x) * (b x)⁻¹, ?_, ?_, ?_⟩
  · intro x y w
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hk3 x y w)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk - hΘb x y w
  · intro x
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hkneg x)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk + heh x
  · intro x
    refine ⟨k x * g x, ?_⟩
    apply tA
    simp only [ofMul_mul, ofMul_inv, map_mul, hbA]
    abel

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_function_lift_units : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (U V : Type) [CommGroup U] [CommGroup V] (e : U →* V), Function.Injective e → ∀ a : X → V, (∀ x y w : X, ∃ u : U, a (x + y + w) * a x * a y * a w = e u * (a (x + y) * a (x + w) * a (y + w))) → (∀ x : X, ∃ u : U, a (-x) = e u * a x) → ∃ c : X → V, (∀ x y w : X, c (x + y + w) * c x * c y * c w = c (x + y) * c (x + w) * c (y + w)) ∧ (∀ x : X, c (-x) = c x) ∧ ∀ x : X, ∃ u : U, c x * a x = e u := by
  atlas_forward_decl GlobalTheory.exists_even_cube_correction
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiTopUnit

theorem unit_factor {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (y : Y) (c a : (FractionRing R)ˣ) (u : Rˣ)
    (h : c * a = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) :
    (gm (f ≫ jK R) y ⊤ (unitOn u)).val = (gm f y ⊤ (unitOn c)).val * gs (𝟙 Y) y ⊤ (scal f a.val) := by
  let φ : FractionRing R →+* Y.presheaf.stalk y := (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)
  have e1 : (gm f y ⊤ (unitOn c)).val = φ c.val := by rw [gm_val f y ⊤ trivial]; rfl
  have e2 : gs (𝟙 Y) y ⊤ (scal f a.val) = φ a.val := by rw [gs_eq _ y ⊤ trivial]; rfl
  have e3 : (gm (f ≫ jK R) y ⊤ (unitOn u)).val = φ (algebraMap R (FractionRing R) u.val) := by
    rw [gm_val _ y ⊤ trivial]
    have e := congrArg (fun q => q.hom u.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    show _ = (Y.presheaf.germ (f ⁻¹ᵁ ⊤) y trivial).hom ((f.app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (CommRingCat.ofHom (algebraMap R (FractionRing R)) u.val)))
    rw [e]
    rfl
  rw [e1, e2, e3, ← map_mul, ← Units.val_mul, h]
  rfl

theorem exists_psiOn_top_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  intro R _ _ _ D ga a hs c hc
  choose u hu using hc
  refine ⟨⟨fun χ => LB.pullGen D.P.L _ _ (GlobalTheory.UU.scaleGen (unitOn (u χ)) (ga χ)) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
    fun χ => DVR.pullGen_isGen _ _ _ _ (GlobalTheory.UU.scaleGen_isGen _ (hs χ).1) _,
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  refine (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)
  have hp := (hs χ).2 (Over.mk ((jK R ⁻¹ᵁ ⊤).ι ≫ jK R)) (Over.homMk (jK R ⁻¹ᵁ ⊤).ι) y J hJ
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  erw [hp]
  rw [unit_factor _ y (c χ) (a χ) (u χ) (hu χ), _root_.mul_assoc]
  rfl

end GlobalTheory.PsiTopUnit
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_scaling_integral_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  atlas_forward_decl GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.UnitPsi

theorem rescale_rescale {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (g' : (GlobalTheory.PolDeg.rescale D g).X → (FractionRing R)ˣ) :
    GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) g' = GlobalTheory.PolDeg.rescale D (fun χ => g' χ * g χ) := by
  unfold GlobalTheory.PolDeg.rescale
  congr 1
  funext χ
  unfold GlobalTheory.UU.scaleGen
  congr 1
  funext j
  have hu : unitOn (g' χ * g χ) = unitOn (g' χ) * unitOn (g χ) := map_mul _ _ _
  change _ * (_ * (D.psi χ).s j) = _
  rw [hu, map_mul, _root_.mul_assoc]

theorem even_step (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧ (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  obtain ⟨h, hh, hE⟩ := GlobalTheory.DefectHom.exists_evenDefect_hom R D hB
  obtain ⟨k, hk3, hkn⟩ := GlobalTheory.T.cubical_function_of_homomorphism D.X (FractionRing R)ˣ (fun a => (h a)⁻¹) (fun a b => by rw [hh, mul_inv])
  refine ⟨k, ?_, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D k).2 hB).2 hk3⟩
  have e := GlobalTheory.PolDeg.evenDefect_rescale D h k hE
  have e1 : (fun χ : D.X => h χ * k (-χ) * (k χ)⁻¹) = fun _ => 1 := by
    funext χ
    rw [hkn χ, mul_inv_cancel_left, mul_inv_cancel]
  rw [e1] at e
  exact (GlobalTheory.PolDeg.evenDefect_one_iff _).1 e

theorem top_step (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hE : D.PsiEven)
    (hB : D.TauBimult) : ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  obtain ⟨ga, a, hs⟩ := GlobalTheory.exists_psiScal R D
  obtain ⟨h3, h2⟩ := GlobalTheory.PsiScalUnit.main R D ga a hs
  let e : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  have he : Function.Injective e := fun u v e =>
    Units.ext (IsFractionRing.injective R (FractionRing R) (congrArg Units.val e))
  obtain ⟨c, hc3, hce, hci⟩ := GlobalTheory.T.cubical_function_lift_units D.X Rˣ (FractionRing R)ˣ e he a
    (fun x y w => by
      obtain ⟨u, hu⟩ := h3 hB x y w
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
    (fun x => by
      obtain ⟨u, hu⟩ := h2 hE x
      exact ⟨u, Units.ext (by rw [Units.val_mul]; exact hu)⟩)
  exact ⟨c, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).1 hE).2 hce, ((GlobalTheory.T.rescale_psi_even_tau_bimult_iff R D c).2 hB).2 hc3,
    GlobalTheory.T.psi_scaling_integral_rescale R D ga a hs c hci⟩

theorem exists_rescale_even_bimult_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧
      (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  intro R _ _ _ _ D
  obtain ⟨g₁, h₁⟩ := GlobalTheory.T.degeneration_rescale_tau_bimult_exists R D
  obtain ⟨g₂, e₂, b₂⟩ := even_step R (GlobalTheory.PolDeg.rescale D g₁) h₁
  obtain ⟨g₃, e₃, b₃, p₃⟩ := top_step R _ e₂ b₂
  refine ⟨fun χ => g₃ χ * g₂ χ * g₁ χ, ?_⟩
  rw [rescale_rescale, rescale_rescale] at e₃ b₃ p₃
  exact ⟨e₃, b₃, p₃⟩

end GlobalTheory.UnitPsi
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_rescale_even_bimult_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).PsiEven ∧ (GlobalTheory.PolDeg.rescale D g).TauBimult ∧ Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D g) ⊤) := by
  atlas_forward_decl GlobalTheory.UnitPsi.exists_rescale_even_bimult_top
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']


end GlobalTheory.PreLift

namespace GlobalTheory.PreLift


end GlobalTheory.PreLift

namespace GlobalTheory.PreLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ


end GlobalTheory.PreLift
end
end
