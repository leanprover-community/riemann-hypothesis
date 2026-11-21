import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOneParameterSubgroupOfRationalFamily
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcExtendsOfRegularSecondAxis
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  intro k _ G _ hG
  have hs : Smooth G.hom := hG.2.1
  let e : algOver k k ⟶ G := 1
  let x0 : (Sp k) := IsLocalRing.closedPoint k
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left) (x := e.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k R := by
    have h1 : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have : y = x0 := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact hx
  let l : algOver k k ⟶ algOver k R := Over.homMk (IsOpenImmersion.lift i e.left hr) (by
    have := Over.w e
    rw [← this]
    show _ ≫ Spec.map φ = _
    rw [hφ, IsOpenImmersion.lift_fac_assoc])
  obtain ⟨ε, hε⟩ := algOverHom_surjective l
  obtain ⟨s, hsg⟩ := hft.out
  refine ⟨R, inferInstance, inferInstance, j, ε, s.card,
    fun n => (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n)), hi, ?_, ?_, ?_⟩
  · rw [hε]
    ext1
    exact IsOpenImmersion.lift_fac i e.left hr
  · rw [eq_top_iff, ← hsg, Algebra.adjoin_le_iff]
    intro a ha
    have h1 : a - algebraMap k R (ε a) ∈ Algebra.adjoin k (Set.range fun n =>
        (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n))) :=
      Algebra.subset_adjoin ⟨s.equivFin ⟨a, ha⟩, by simp⟩
    have h2 := add_mem h1 (Subalgebra.algebraMap_mem _ (ε a))
    simpa using h2
  · intro n
    simp

end GlobalTheory.SS.ArcInf
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  atlas_forward_decl GlobalTheory.SS.ArcInf.exists_isChart
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  first | exact @GlobalTheory.SS.ArcInf.exists_basicOpen_factor | exact GlobalTheory.SS.ArcInf.exists_basicOpen_factor | (intros; apply GlobalTheory.SS.ArcInf.exists_basicOpen_factor <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf.TwoVarSetup

theorem exists_liftAway {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by
  have hu : ∀ y : Submonoid.powers x, IsUnit (τ y) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (τ (x ^ n))
    rw [map_pow]; exact h.pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩

variable {k : Type} [Field k]

theorem laurent_ext {F : Type} [CommRing F] [Algebra k F] {a b : FractionRing (PowerSeries k) →ₐ[k] F}
    (h : ∀ x : PowerSeries k, a (algebraMap _ _ x) = b (algebraMap _ _ x)) : a = b := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k))
  exact RingHom.ext h

theorem hasSubst_diag :
    MvPowerSeries.HasSubst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> exact PowerSeries.constantCoeff_X

theorem hasSubst_var (i : Fin 2) :
    PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp)

theorem diag_var (i : Fin 2) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) = PowerSeries.X := by
  rw [MvPowerSeries.subst_X hasSubst_diag]
  fin_cases i <;> rfl

theorem diag_subst (i : Fin 2) (x : PowerSeries k) :
    MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k)
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) = x := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (hasSubst_var i).const hasSubst_diag]
  simp only [diag_var]
  rw [← PowerSeries.subst_def]
  simp

theorem exists_diag : ∃ τ : MvPowerSeries (Fin 2) k →ₐ[k] FractionRing (PowerSeries k), ∀ y,
    τ y = algebraMap (PowerSeries k) _
      (MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) y) :=
  ⟨(IsScalarTower.toAlgHom k (PowerSeries k) _).comp (MvPowerSeries.substAlgHom hasSubst_diag), fun y => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]; rfl⟩

theorem exists_copy (i : Fin 2) : ∃ s : FractionRing (PowerSeries k) →ₐ[k]
      Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k),
    ∀ x : PowerSeries k, s (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
      (x.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)
  rw [map_mul] at hu
  obtain ⟨s, hs⟩ := exists_lift ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k)
    (Localization.Away (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (hasSubst_var i))) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    fin_cases i
    · exact isUnit_of_mul_isUnit_left hu
    · exact isUnit_of_mul_isUnit_right hu)
  refine ⟨s, fun x => ?_⟩
  rw [hs, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]; rfl

theorem point_one {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} (h : algOverHom ε ≫ j = 1) (F : Type) [CommRing F] [Algebra k F] :
    algOverHom ((Algebra.ofId k F).comp ε) ≫ j = 1 := by
  rw [algOverHom_comp, Category.assoc, h, MonObj.comp_one]

theorem exists_twoVar : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  intro k _ G _ A _ _ j ε r f hc a
  obtain ⟨τ₀, hτ₀⟩ := exists_diag (k := k)
  obtain ⟨s₀, hs₀⟩ := exists_copy (k := k) 0
  obtain ⟨s₁, hs₁⟩ := exists_copy (k := k) 1
  have hinj := IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  have hX : ∀ i, τ₀ (MvPowerSeries.X i) ≠ 0 := fun i => by
    rw [hτ₀, diag_var]
    exact (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  have hx : τ₀ (MvPowerSeries.X 0 * MvPowerSeries.X 1) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero (hX 0) (hX 1)
  generalize (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = x at s₀ s₁ hs₀ hs₁ hx
  obtain ⟨δ, hδ⟩ := exists_liftAway x τ₀ hx.isUnit
  have hδ₀ : δ.comp s₀ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₀, hδ, hτ₀, diag_subst]; rfl
  have hδ₁ : δ.comp s₁ = AlgHom.id k _ := laurent_ext fun y => by
    rw [AlgHom.comp_apply, hs₁, hδ, hτ₀, diag_subst]; rfl
  obtain ⟨e, he, hfac⟩ := GlobalTheory.SS.ArcInf.exists_basicOpen_factor k G A _ (FractionRing (PowerSeries k)) j
    ((algOverHom s₁ ≫ a) * (algOverHom s₀ ≫ a)⁻¹) δ ((Algebra.ofId k _).comp ε) hc.1 (by
      rw [point_one hc.2.1, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
        ← algOverHom_comp, ← algOverHom_comp, hδ₀, hδ₁, mul_inv_cancel])
  obtain ⟨n, e₀, he₀⟩ := IsLocalization.Away.surj x e
  have hτe : τ₀ e₀ ≠ 0 := by
    rw [← hδ, ← he₀, map_mul, map_pow, hδ]
    exact mul_ne_zero he (pow_ne_zero _ hx)
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (x * e₀)) (x * e₀)
  rw [map_mul] at hu
  obtain ⟨ρ, hρ⟩ := exists_liftAway x
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (Localization.Away (x * e₀)))
    (isUnit_of_mul_isUnit_left hu)
  simp only [IsScalarTower.coe_toAlgHom'] at hρ
  have hρe : IsUnit (ρ e) := by
    have h1 := isUnit_of_mul_isUnit_right hu
    rw [← hρ, ← he₀, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨χ, hχ⟩ := hfac _ ρ hρe
  obtain ⟨⟨b, M, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (x * e₀)) (fun i => χ (f i))
  choose h hh using hb
  simp only [Algebra.smul_def] at hh
  have hd : τ₀ ((x * e₀) * (x * e₀) ^ M) ≠ 0 := by
    rw [← pow_succ', map_pow, map_mul]
    exact pow_ne_zero _ (mul_ne_zero hx hτe)
  have htv : TwoVar j f a (fun i => (x * e₀) * h i) ((x * e₀) * (x * e₀) ^ M) := by
    intro F _ _ τ σ₀ σ₁ hτ hσ₀ hσ₁
    have h0 : τ (x * e₀) ≠ 0 := by
      rw [map_mul] at hτ; exact left_ne_zero_of_mul hτ
    obtain ⟨τ', hτ'⟩ := exists_liftAway (x * e₀) τ h0.isUnit
    have e0 : τ'.comp (ρ.comp s₀) = σ₀ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₀, hρ, hτ', hσ₀]
    have e1 : τ'.comp (ρ.comp s₁) = σ₁ := laurent_ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hs₁, hρ, hτ', hσ₁]
    refine ⟨τ'.comp χ, fun i => ?_, ?_⟩
    · rw [map_mul τ (x * e₀) (h i), ← hτ' (h i), hh, map_mul τ', hτ', map_mul τ (x * e₀),
        AlgHom.comp_apply]
      ring
    · rw [algOverHom_comp, Category.assoc, hχ, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
        GrpObj.comp_inv]
      simp only [← Category.assoc, ← algOverHom_comp]
      rw [e0, e1, inv_mul_cancel_right]
  refine ⟨_, _, ?_, fun i => ?_, htv⟩
  · intro h0
    apply hd
    rw [hτ₀, h0, map_zero]
  · obtain ⟨χ', h1, h2⟩ := htv _ τ₀ (AlgHom.id k _) (AlgHom.id k _) hd
      (fun y => by rw [hτ₀, diag_subst]; rfl) (fun y => by rw [hτ₀, diag_subst]; rfl)
    have h3 : χ' = (Algebra.ofId k _).comp ε := by
      apply eq_of_comp_eq hc.1
      rw [point_one hc.2.1]
      exact right_eq_mul.1 h2
    apply hinj
    rw [← hτ₀, map_zero, ← h1 i, h3, AlgHom.comp_apply, hc.2.2.2 i, map_zero, zero_mul]

end GlobalTheory.SS.ArcInf.TwoVarSetup
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcQuotient_twoVariable_coords : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ a : algOver k (FractionRing (PowerSeries k)) ⟶ G, ∃ (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) d ≠ 0 ∧ (∀ i, MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) (h i) = 0) ∧ TwoVar j f a h d := by
  atlas_forward_decl GlobalTheory.SS.ArcInf.TwoVarSetup.exists_twoVar
end

section
namespace GlobalTheory

open MvPowerSeries

theorem hasSubst_pair {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) :=
  hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa

theorem subst_pair_subst_X {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by
  have h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext _
  exact subst_X ha i

theorem subst_pair_subst_shear {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by
  have ha : HasSubst (![z, w] : Fin 2 → PowerSeries k) := hasSubst_pair hz hw
  have h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext s
  fin_cases s
  · exact subst_X ha 0
  · show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w
    rw [subst_add ha, subst_X ha, subst_X ha]
    rfl

theorem X_one_dvd_iff_subst_eq_zero {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by
  have ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) :=
    hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)
  constructor
  · rintro ⟨q, rfl⟩
    rw [subst_mul ha, subst_X ha]
    exact zero_mul _
  · intro hg
    have h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have h2 := subst_comp_subst_apply ha h1 g
    rw [hg, ← coe_substAlgHom h1, map_zero] at h2
    have h3 : rescale (![1, 0] : Fin 2 → k) g = 0 := by
      rw [rescale_eq_subst, h2]
      congr 1
      funext s
      fin_cases s
      · show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())
        rw [substAlgHom_X, one_smul]
      · show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0
        rw [map_zero, zero_smul]
    rw [X_dvd_iff]
    intro m hm
    have h4 := congrArg (coeff m) h3
    rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp)] at h4
    simpa [hm] using h4

theorem subst_two_variables_identities : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  intro k _
  refine ⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw =>
    ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩
  rw [X_one_dvd_iff_subst_eq_zero,
    subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_two_variables_identities_alt : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  atlas_forward_decl GlobalTheory.subst_two_variables_identities
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma weight_fin_two (m n : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) e = m * e 0 + n * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma leading_polynomial_eq_zero_iff_lt_weightedOrder {k : Type} [Field k] {m n : ℕ} (hm : 1 ≤ m)
    (f : MvPowerSeries (Fin 2) k) {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)) = 0 ↔
      (D : ℕ∞) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f := by
  have hcoeff : ∀ e ∈ S,
      (∑ e' ∈ S, Polynomial.C (MvPowerSeries.coeff e' f) * Polynomial.X ^ (e' 1)).coeff (e 1) =
        MvPowerSeries.coeff e f := by
    intro e he
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single e]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro e' he' hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h1
      apply hne
      have w1 := (hS e').1 he'
      have w2 := (hS e).1 he
      rw [weight_fin_two] at w1 w2
      rw [h1] at w2
      have h0 : e' 0 = e 0 :=
        Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (w1.trans w2.symm))
      ext i
      fin_cases i
      · exact h0
      · exact h1.symm
    · intro h; exact absurd he h
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have heq : MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f = D := le_antisymm hlt hD
    obtain ⟨e, hne, hwe⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder
      (![m, n] : Fin 2 → ℕ) (f := f) (by rw [heq]; rfl)
    rw [heq, Nat.cast_inj] at hwe
    have := hcoeff e ((hS e).2 hwe)
    rw [h0, Polynomial.coeff_zero] at this
    exact hne this.symm
  · intro hlt
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (by rw [(hS e).1 he]; exact hlt),
      map_zero, zero_mul]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma prod_pow_fin_two {k : Type} [Field k] (z w : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    (e.prod fun s j => (![z, w] : Fin 2 → PowerSeries k) s ^ j) = z ^ e 0 * w ^ e 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open PowerSeries in
private lemma coeff_pow_mul_pow_of_le_order {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order) (a b : ℕ) :
    (∀ j < m * a + n * b, coeff j (z ^ a * w ^ b) = 0) ∧
      coeff (m * a + n * b) (z ^ a * w ^ b) = coeff m z ^ a * coeff n w ^ b := by
  obtain ⟨z', rfl⟩ : X ^ m ∣ z := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hz)
  obtain ⟨w', rfl⟩ : X ^ n ∣ w := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hw)
  have hprod : (X ^ m * z') ^ a * (X ^ n * w') ^ b = X ^ (m * a + n * b) * (z' ^ a * w' ^ b) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  rw [hprod]
  refine ⟨fun j hj => by rw [coeff_X_pow_mul', if_neg (by omega)], ?_⟩
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow,
    map_pow]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_zero_of_lt {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {f : MvPowerSeries (Fin 2) k}
    {D : ℕ} (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f) {j : ℕ}
    (hj : j < D) : PowerSeries.coeff j (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) = 0 := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases hlt : Finsupp.weight (![m, n] : Fin 2 → ℕ) e < D
  · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
      (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
  · rw [weight_fin_two] at hlt
    rw [prod_pow_fin_two, ← PowerSeries.coeff,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 j (by omega), smul_zero]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_pow_mul_eval_leading {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {s t : k}
    (hzs : PowerSeries.coeff m z = s ^ m) (hwt : PowerSeries.coeff n w = s ^ n * t)
    {f : MvPowerSeries (Fin 2) k} {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    PowerSeries.coeff D (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) =
      s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := S)]
  · rw [Polynomial.eval_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hwe := (hS e).1 he
    rw [weight_fin_two] at hwe
    rw [prod_pow_fin_two, ← PowerSeries.coeff, ← hwe,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).2, hzs, hwt]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [pow_add, pow_mul, pow_mul]
    ring
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.mem_coe, hS]
    by_contra hne
    apply he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
        (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
    · rw [weight_fin_two] at hgt
      rw [prod_pow_fin_two, ← PowerSeries.coeff,
        (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 D (by omega), smul_zero]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.exists_polynomial_leading_quotient_subst :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  intro k _ _ m n hm hn r h d hd hdh
  have hfin : ((MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat : ℕ∞) =
      MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d :=
    ENat.coe_toNat ((MvPowerSeries.weightedOrder_eq_top_iff _).not.2 hd)
  set D := (MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat with hD_def
  have hWpos : ∀ x, (![m, n] : Fin 2 → ℕ) x ≠ 0 := by
    intro x; fin_cases x <;> simp <;> omega
  set S := (Finsupp.finite_of_nat_weight_le _ hWpos D).toFinset.filter
    fun e => Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D with hS_def
  have hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D := by
    intro e
    simp only [hS_def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hDd : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d := hfin.le
  have hDh : ∀ i, (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) :=
    fun i => hfin.le.trans (hdh i)
  refine ⟨∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e d) * Polynomial.X ^ (e 1),
    fun i => ∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e (h i)) * Polynomial.X ^ (e 1), ?_, ?_, ?_⟩
  · intro h0
    have := (leading_polynomial_eq_zero_iff_lt_weightedOrder hm d hDd S hS).1 h0
    rw [hfin] at this
    exact lt_irrefl _ this
  · intro i
    rw [leading_polynomial_eq_zero_iff_lt_weightedOrder hm (h i) (hDh i) S hS, hfin]
  · intro s t z w hs0 hz hw hzs hwt hPd
    have hz0 : PowerSeries.coeff 0 z = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)
    have hw0 : PowerSeries.coeff 0 w = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hn) hw)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hz0 hw0
    have hsub : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i
        · exact hz0
        · exact hw0
    have factor : ∀ f : MvPowerSeries (Fin 2) k,
        (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f →
        ∃ g : PowerSeries k, MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f =
          PowerSeries.X ^ D * g ∧ PowerSeries.constantCoeff g =
            s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
      intro f hf
      obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.2 fun j hj =>
        coeff_subst_eq_zero_of_lt hz hw hsub hf hj
      refine ⟨g, hg, ?_⟩
      have := coeff_subst_eq_pow_mul_eval_leading hz hw hsub hzs hwt hf S hS
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] at this
      exact this
    obtain ⟨gd, hgd, hgd0⟩ := factor d hDd
    have hgd0' : PowerSeries.constantCoeff gd ≠ 0 := by
      rw [hgd0]; exact mul_ne_zero (pow_ne_zero _ hs0) hPd
    refine ⟨?_, fun i => (factor (h i) (hDh i)).choose * gd⁻¹, fun i => ?_⟩
    · rw [hgd]
      exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
        fun h0 => hgd0' (by rw [h0, map_zero])
    · obtain ⟨hgi, hgi0⟩ := (factor (h i) (hDh i)).choose_spec
      constructor
      · rw [hgd, hgi, show (factor (h i) (hDh i)).choose * gd⁻¹ * (PowerSeries.X ^ D * gd) =
          PowerSeries.X ^ D * (factor (h i) (hDh i)).choose * (gd * gd⁻¹) by ring,
          PowerSeries.mul_inv_cancel _ hgd0', _root_.mul_one]
      · rw [map_mul, PowerSeries.constantCoeff_inv, hgi0, hgd0]
        field_simp

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leading_quotient_weighted_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  atlas_forward_decl GlobalTheory.SS.exists_polynomial_leading_quotient_subst
end

section
namespace GlobalTheory

theorem exists_forall_eval_add_ne_zero {k : Type} [Field k] [Infinite k] {Q : Polynomial k}
    (hQ : Q ≠ 0) (S : Finset k) : ∃ β : k, ∀ c ∈ S, Q.eval (c + β) ≠ 0 := by
  classical
  obtain ⟨β, hβ⟩ := Infinite.exists_notMem_finset
    ((S ×ˢ Q.roots.toFinset).image (fun x : k × k => x.2 - x.1))
  refine ⟨β, fun c hc h => hβ ?_⟩
  refine Finset.mem_image.2 ⟨(c, c + β), ?_, by simp⟩
  simp [hc, hQ, h]

theorem infinite_pow_char_eq_one_of_additive_family :
    ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type)
      [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k)
      (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k)
      (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) →
      Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) →
      (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
      (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
        em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  intro k _ _ p _ M _ A _ _ r f ε em Pd P ψ hgen hε hinj hem hPd hP hval hadd
  classical
  have hpow : ∀ α, Pd.eval α ≠ 0 → em (ψ α) ^ p = 1 := by
    intro α hα
    obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd
      ((Finset.range (p + 1)).image (fun n : ℕ => (n : k) * α))
    have hβ' : ∀ n : ℕ, n ≤ p → Pd.eval ((n : k) * α + β) ≠ 0 := fun n hn =>
      hβ _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
    have key : ∀ n : ℕ, n ≤ p → em (ψ α) ^ n * em (ψ β) = em (ψ ((n : k) * α + β)) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have e : ((n + 1 : ℕ) : k) * α + β = α + ((n : k) * α + β) := by push_cast; ring
        have h1 := hβ' (n + 1) hn
        rw [e] at h1
        rw [pow_succ', mul_assoc, ih (by omega), hadd _ _ hα (hβ' n (by omega)) h1, e]
    have h := key p le_rfl
    rw [CharP.cast_eq_zero, zero_mul, zero_add] at h
    exact mul_eq_right.1 h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hU : Set.Infinite {t : k | Pd.eval t ≠ 0} := by
    have : {t : k | Pd.eval t ≠ 0} = {t : k | Pd.IsRoot t}ᶜ := by
      ext t; simp
    rw [this]
    exact (Polynomial.finite_setOf_isRoot hPd).infinite_compl
  haveI : Infinite {t : k | Pd.eval t ≠ 0} := hU.to_subtype
  let g : {t : k | Pd.eval t ≠ 0} → {x : M // x ^ p = 1} := fun t => ⟨em (ψ t.1), hpow t.1 t.2⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  obtain ⟨⟨t₀, ht₀⟩⟩ : Nonempty (g ⁻¹' {y}) := inferInstance
  have hy' : (g ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hy'' : (Subtype.val '' (g ⁻¹' {y})).Infinite :=
    hy'.image Subtype.val_injective.injOn
  set χ := ψ t₀.1 with hχ
  have hpoly : ∀ i, P i = Polynomial.C (χ (f i)) * Pd := by
    intro i
    apply Polynomial.eq_of_infinite_eval_eq
    refine hy''.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 : g t = g t₀ := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at ht ht₀
      rw [ht, ht₀]
    have h2 : ψ t.1 = χ := hinj (congrArg Subtype.val h1)
    have h3 := hval t.1 t.2 i
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C]
    rw [← h3, h2]
  have hconst : ∀ t, Pd.eval t ≠ 0 → ψ t = χ := by
    intro t ht
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨i, rfl⟩
    have h3 := hval t ht i
    rw [hpoly i, Polynomial.eval_mul, Polynomial.eval_C] at h3
    exact mul_right_cancel₀ ht h3
  obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd {0, t₀.1}
  have hb0 : Pd.eval β ≠ 0 := by simpa using hβ 0 (by simp)
  have hb1 : Pd.eval (t₀.1 + β) ≠ 0 := hβ _ (by simp)
  have h4 := hadd _ _ t₀.2 hb0 hb1
  rw [hconst _ hb0, hconst _ hb1, ← hχ] at h4
  have h5 : χ = ε := hinj (by rw [hem]; exact mul_eq_right.1 h4)
  obtain ⟨i, hi⟩ := hP
  apply hi
  rw [hpoly i, h5, hε i]
  simp

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_pth_roots_of_additive_family : ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k) (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) → Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 → em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  atlas_forward_decl GlobalTheory.infinite_pow_char_eq_one_of_additive_family
end

section
namespace GlobalTheory

theorem powerSeries_generic_relation_chain :
    ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  intro k _ _ ρ Gen hs ht hg
  have h1 : ∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) →
      w.order = (m : ℕ∞) → ρ z w := by
    intro m n hmn z w hz hw
    obtain ⟨S, hS, hzS⟩ := hg m n hmn z hz
    obtain ⟨T, hT, hwT⟩ := hg m n hmn w hw
    obtain ⟨t, htt⟩ := (hS.union hT).exists_notMem
    simp only [Set.mem_union, not_or] at htt
    exact ht _ _ _ (hzS t htt.1) (hs _ _ (hwT t htt.2))
  refine ⟨h1, fun m₀ hG => ?_⟩
  have h2 : ∀ m, m₀ ≤ m → ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
      ρ z (PowerSeries.X ^ m₀) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun z hz => h1 _ _ (hG _ le_rfl) _ _ hz (PowerSeries.order_X_pow _)
    | succ m hm ih =>
      intro z hz
      obtain ⟨S, hS, hXS⟩ := hg m _ (hG m hm) (PowerSeries.X ^ m) (PowerSeries.order_X_pow _)
      obtain ⟨t, htt⟩ := (hS.insert 0).exists_notMem
      simp only [Set.mem_insert_iff, not_or] at htt
      have ho : (PowerSeries.C t * PowerSeries.X ^ (m + 1) : PowerSeries k).order
          = ((m + 1 : ℕ) : ℕ∞) := by
        rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
          PowerSeries.monomial_mul_monomial, zero_add, mul_one]
        exact PowerSeries.order_monomial_of_ne_zero _ _ htt.1
      exact ht _ _ _ (h1 _ _ (hG _ (Nat.le_succ_of_le hm)) _ _ hz ho)
        (ht _ _ _ (hs _ _ (hXS t htt.2)) (ih _ (PowerSeries.order_X_pow _)))
  intro m n z w hm hn hz hw
  exact ht _ _ _ (h2 m hm z hz) (hs _ _ (h2 n hn w hw))

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relation_of_gen_of_order_eq : ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  atlas_forward_decl GlobalTheory.powerSeries_generic_relation_chain
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Slope

open MvPowerSeries

variable {k : Type} [Field k]

lemma weight_two (m n : ℕ) (s : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) s = m * s 0 + n * s 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, mul_comm]

lemma exists_min (w : Fin 2 → ℕ) (f : MvPowerSeries (Fin 2) k) (hf : f ≠ 0) :
    ∃ s, coeff s f ≠ 0 ∧ (Finsupp.weight w s : ℕ∞) = weightedOrder w f :=
  exists_coeff_ne_zero_and_weightedOrder w ((ne_zero_iff_weightedOrder_finite w).1 hf)

lemma lt_iff (m n : ℕ) (f g : MvPowerSeries (Fin 2) k) :
    weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) g ↔
      ∃ s : Fin 2 →₀ ℕ, coeff s f ≠ 0 ∧ ∀ t : Fin 2 →₀ ℕ, coeff t g ≠ 0 →
        m * s 0 + n * s 1 < m * t 0 + n * t 1 := by
  constructor
  · intro h
    have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨s, hs, hs'⟩ := exists_min ![m, n] f hf
    refine ⟨s, hs, fun t ht => ?_⟩
    have := lt_of_lt_of_le (hs' ▸ h) (weightedOrder_le ![m, n] ht)
    rw [← weight_two, ← weight_two]
    exact_mod_cast this
  · rintro ⟨s, hs, h⟩
    refine lt_of_le_of_lt (weightedOrder_le _ hs) ?_
    by_cases hg : g = 0
    · subst hg
      simp
    · obtain ⟨t, ht, ht'⟩ := exists_min ![m, n] g hg
      rw [← ht', weight_two, weight_two]
      exact_mod_cast h t ht

lemma step (f d : MvPowerSeries (Fin 2) k) (hf : ∀ t : Fin 2 →₀ ℕ, coeff t f ≠ 0 → 1 ≤ t 1)
    (s₀ : Fin 2 →₀ ℕ) (hs₀ : coeff s₀ d ≠ 0) (hs₀' : s₀ 1 = 0) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (h : weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) d) :
    ∃ p, n * (s₀ 0).factorial < m * p ∧
      ¬ weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) d <
        weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) f := by
  classical
  obtain ⟨t, ht, h⟩ := (lt_iff m n f d).1 h
  set N := (s₀ 0).factorial with hN
  have hNpos : 0 < N := Nat.factorial_pos _
  have ht1 := hf t ht
  have htle : t 1 ≤ s₀ 0 := by
    have := h s₀ hs₀
    rw [hs₀'] at this
    by_contra hc
    push Not at hc
    nlinarith [Nat.zero_le (m * t 0), Nat.mul_le_mul hmn hc.le]
  have hex : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → s 1 < t 1 →
      ∃ p, N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    intro s hs hlt
    have h1 := h s hs
    have h2 : t 0 ≤ s 0 := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left m hc.le, Nat.mul_le_mul_left n hlt.le]
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le h2
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    have : b ∣ N := Nat.dvd_factorial (by omega) (by omega)
    obtain ⟨c, hc⟩ := this
    refine ⟨c * a, ?_⟩
    rw [ha, hb, hc]
    ring
  have hP : ∃ p, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 < t 1 ∧
      N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    obtain ⟨p, hp⟩ := hex s₀ hs₀ (by omega)
    exact ⟨p, s₀, hs₀, by omega, hp⟩
  obtain ⟨s₁, hs₁, hlt₁, heq₁⟩ := Nat.find_spec hP
  set p := Nat.find hP with hp
  have hbig : n * N < m * p := by
    have h1 := h s₁ hs₁
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt₁.le
    rw [hb] at h1 heq₁
    have h2 : n * N * b < m * p * b := by nlinarith
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
  refine ⟨p, hbig, ?_⟩
  rw [lt_iff]
  rintro ⟨s, hs, hs'⟩
  have h3 := hs' t ht
  by_cases hlt : s 1 < t 1
  · obtain ⟨q, hq⟩ := hex s hs hlt
    have hpq : p ≤ q := Nat.find_min' hP ⟨s, hs, hlt, hq⟩
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hb] at h3 hq
    nlinarith [Nat.mul_le_mul_right b hpq]
  · push Not at hlt
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt
    have h1 := h s hs
    rw [hb] at h3 h1
    have h4 : N * s 0 + p * b < N * t 0 := by nlinarith
    have h5 : m * t 0 < m * s 0 + n * b := by nlinarith
    have h6 := Nat.mul_lt_mul_of_pos_left h4 (k := m) hm
    have h7 := Nat.mul_lt_mul_of_pos_left h5 (k := N) hNpos
    nlinarith [Nat.mul_le_mul_right b hbig.le]

end GlobalTheory.SS.Slope

namespace GlobalTheory.SS

open MvPowerSeries Slope in

theorem weightedOrder_slope_comparison : ∀ (k : Type) [Field k] (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → ∀ Q : ℕ → ℕ → Prop, (∀ m n, Q m n ↔ ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ((∀ i, MvPowerSeries.X 1 ∣ h i) → ¬ MvPowerSeries.X 1 ∣ d → (∃ m n, 1 ≤ m ∧ m ≤ n ∧ ¬ Q m n) → ∃ m n, 1 ≤ m ∧ m ≤ n ∧ (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∃ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d = MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ (Q 1 1 → ∃ m₀, ∀ m, m₀ ≤ m → Q m (m + 1)) ∧ (∀ m n l, 1 ≤ l → (Q (l * m) (l * n) ↔ Q m n)) ∧ ((∀ n, 1 ≤ n → Q 1 n) → ∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) := by
  classical
  intro k _ r h d hd Q hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro hh hdX ⟨m, n, hm, hmn, hnQ⟩
    have hf : ∀ i (t : Fin 2 →₀ ℕ), coeff t (h i) ≠ 0 → 1 ≤ t 1 := by
      intro i t ht
      by_contra hc
      exact ht (X_dvd_iff.1 (hh i) t (by omega))
    obtain ⟨s₀, hs₀', hs₀⟩ : ∃ s : Fin 2 →₀ ℕ, s 1 = 0 ∧ coeff s d ≠ 0 := by
      rw [X_dvd_iff] at hdX
      push Not at hdX
      exact hdX
    by_contra hcon
    have key : ∀ m n, 1 ≤ m → m ≤ n → ¬ Q m n →
        ∃ p, n * (s₀ 0).factorial < m * p ∧ ¬ Q (s₀ 0).factorial p := by
      intro m n hm hmn hnQ
      by_cases hall : ∀ i, weightedOrder (![m, n] : Fin 2 → ℕ) d ≤
          weightedOrder (![m, n] : Fin 2 → ℕ) (h i)
      · exfalso
        apply hcon
        refine ⟨m, n, hm, hmn, hall, ?_⟩
        rw [hQ] at hnQ
        push Not at hnQ
        obtain ⟨i, hi⟩ := hnQ
        exact ⟨i, le_antisymm (hall i) hi⟩
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨p, hp, hp'⟩ := step (h i) d (hf i) s₀ hs₀ hs₀' m n hm hmn hi
        exact ⟨p, hp, fun hq => hp' ((hQ _ _).1 hq i)⟩
    set N := (s₀ 0).factorial with hN
    have hNpos : 0 < N := Nat.factorial_pos _
    have unb : ∀ j : ℕ, ∃ p, N + j ≤ p ∧ ¬ Q N p := by
      intro j
      induction j with
      | zero =>
        obtain ⟨p, hp, hp'⟩ := key m n hm hmn hnQ
        refine ⟨p, ?_, hp'⟩
        have : m * N < m * p := lt_of_le_of_lt (Nat.mul_le_mul_right _ hmn) hp
        have := lt_of_mul_lt_mul_left this (Nat.zero_le _)
        omega
      | succ j ih =>
        obtain ⟨q, hq, hq'⟩ := ih
        obtain ⟨p, hp, hp'⟩ := key N q hNpos (by omega) hq'
        refine ⟨p, ?_, hp'⟩
        rw [mul_comm] at hp
        have := lt_of_mul_lt_mul_left hp (Nat.zero_le _)
        omega
    obtain ⟨p, hp, hp'⟩ := unb (N * s₀ 0)
    apply hp'
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s₀, hs₀, fun t ht => ?_⟩
    have := hf i t ht
    rw [hs₀']
    nlinarith [Nat.mul_le_mul_left p this, Nat.zero_le (N * t 0)]
  · intro h11
    obtain ⟨s, hs, hs'⟩ := exists_min ![1, 1] d hd
    refine ⟨s 1 + 1, fun m hm => ?_⟩
    rw [hQ]
    intro i
    rw [lt_iff]
    refine ⟨s, hs, fun t ht => ?_⟩
    have h1 := lt_of_lt_of_le (hs' ▸ (hQ _ _).1 h11 i) (weightedOrder_le ![1, 1] ht)
    rw [weight_two, weight_two] at h1
    have h2 : 1 * s 0 + 1 * s 1 < 1 * t 0 + 1 * t 1 := by exact_mod_cast h1
    have h3 : s 0 + s 1 + 1 ≤ t 0 + t 1 := by omega
    nlinarith [Nat.mul_le_mul_left m h3, Nat.zero_le (t 1)]
  · intro m n l hl
    rw [hQ, hQ]
    refine forall_congr' fun i => ?_
    rw [lt_iff, lt_iff]
    refine exists_congr fun s => and_congr_right fun _ => forall_congr' fun t =>
      imp_congr_right fun _ => ?_
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.mul_lt_mul_left hl
  · intro hall i
    have hP : ∃ e, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 = e := by
      obtain ⟨s, hs, -⟩ := exists_min ![1, 1] d hd
      exact ⟨_, s, hs, rfl⟩
    obtain ⟨s₁, hs₁, he⟩ := Nat.find_spec hP
    set e := Nat.find hP with hedef
    have hmin : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → e ≤ s 1 := fun s hs =>
      Nat.find_min' hP ⟨s, hs, rfl⟩
    have hdv : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ d := by
      rw [X_pow_dvd_iff]
      intro s hs
      by_contra hc
      have := hmin s hc
      omega
    have hhu : (X 1 : MvPowerSeries (Fin 2) k) ^ e ∣ h i := by
      rw [X_pow_dvd_iff]
      intro t ht
      by_contra hc
      obtain ⟨s, hs, hs'⟩ := (lt_iff _ _ _ _).1 ((hQ _ _).1 (hall (t 0 + 1) (by omega)) i)
      have h1 := hs' t hc
      have h2 : t 1 + 1 ≤ s 1 := le_trans ht (hmin s hs)
      nlinarith [Nat.mul_le_mul_left (t 0 + 1) h2, Nat.zero_le (s 0)]
    obtain ⟨v, hv⟩ := hdv
    obtain ⟨u, hu⟩ := hhu
    refine ⟨u, v, ?_, by rw [hu, hv]; ring⟩
    rintro ⟨w, hw⟩
    have : (X 1 : MvPowerSeries (Fin 2) k) ^ (e + 1) ∣ d := ⟨w, by rw [hv, hw]; ring⟩
    exact hs₁ (X_pow_dvd_iff.1 this s₁ (by omega))

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrder_slope_comparison_alt : ∀ (k : Type) [Field k] (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → ∀ Q : ℕ → ℕ → Prop, (∀ m n, Q m n ↔ ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ((∀ i, MvPowerSeries.X 1 ∣ h i) → ¬ MvPowerSeries.X 1 ∣ d → (∃ m n, 1 ≤ m ∧ m ≤ n ∧ ¬ Q m n) → ∃ m n, 1 ≤ m ∧ m ≤ n ∧ (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∃ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d = MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ (Q 1 1 → ∃ m₀, ∀ m, m₀ ≤ m → Q m (m + 1)) ∧ (∀ m n l, 1 ≤ l → (Q (l * m) (l * n) ↔ Q m n)) ∧ ((∀ n, 1 ≤ n → Q 1 n) → ∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) := by
  atlas_forward_decl GlobalTheory.SS.weightedOrder_slope_comparison
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k]

abbrev toK (k : Type) [Field k] : PowerSeries k →ₐ[k] FractionRing (PowerSeries k) :=
  IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))

theorem toK_injective : Function.Injective (toK k) := IsFractionRing.injective (PowerSeries k) _

def ev0 (k : Type) [Field k] : PowerSeries k →ₐ[k] k :=
  { PowerSeries.constantCoeff (R := k) with commutes' := fun c => by simp [PowerSeries.algebraMap_apply] }

theorem laurentCoeffEvalLinear_apply (x : PowerSeries k) : ev0 k x = PowerSeries.constantCoeff x := rfl

section Red
variable {G : Over (Sp k)}

def Red (x : algOver k (FractionRing (PowerSeries k)) ⟶ G) (c : algOver k k ⟶ G) : Prop :=
  ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = x ∧ algOverHom (ev0 k) ≫ b = c

theorem Red.unique (hG : IsSeparated G.hom) {x : algOver k (FractionRing (PowerSeries k)) ⟶ G}
    {c c' : algOver k k ⟶ G} (h : Red x c) (h' : Red x c') : c = c' := by
  obtain ⟨b, h1, rfl⟩ := h
  obtain ⟨b', h2, rfl⟩ := h'
  have hd : IsDominant (algOverHom (toK k)).left := by
    rw [algOverHom_left]
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 ?_⟩
    intro x hx
    have : x = 0 := toK_injective (hx.trans (map_zero _).symm)
    simp [this]
  have hr : IsReduced (algOver k (PowerSeries k)).left := inferInstanceAs (IsReduced (Sp (PowerSeries k)))
  have : b = b' := by
    ext1
    refine ext_of_isDominant_of_isSeparated G.hom ?_ (algOverHom (toK k)).left ?_
    · rw [Over.w, Over.w]
    · rw [← Over.comp_left, ← Over.comp_left, h1, h2]
  rw [this]

variable [GrpObj G]

theorem Red.mul {x y : algOver k (FractionRing (PowerSeries k)) ⟶ G} {c c' : algOver k k ⟶ G}
    (h : Red x c) (h' : Red y c') : Red (x * y) (c * c') := by
  obtain ⟨b, rfl, rfl⟩ := h
  obtain ⟨b', rfl, rfl⟩ := h'
  exact ⟨b * b', MonObj.comp_mul _ _ _, MonObj.comp_mul _ _ _⟩

theorem Red.inv {x : algOver k (FractionRing (PowerSeries k)) ⟶ G} {c : algOver k k ⟶ G}
    (h : Red x c) : Red x⁻¹ c⁻¹ := by
  obtain ⟨b, rfl, rfl⟩ := h
  exact ⟨b⁻¹, GrpObj.comp_inv _ _, GrpObj.comp_inv _ _⟩

end Red

theorem exists_sig {z : PowerSeries k} (h : PowerSeries.constantCoeff z = 0 ∧ z ≠ 0) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (PowerSeries k),
      ∀ x : PowerSeries k, σ (algebraMap _ _ x) = toK k (x.subst z) := by
  have hs : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero' h.1
  obtain ⟨σ, hσ⟩ := exists_lift ((toK k).comp (PowerSeries.substAlgHom hs)) (by
    rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X]
    exact IsUnit.mk0 _ fun e => h.2 (toK_injective (e.trans (map_zero _).symm)))
  exact ⟨σ, fun x => by rw [hσ, AlgHom.comp_apply, PowerSeries.coe_substAlgHom]⟩

open scoped Classical in

def sig (z : PowerSeries k) : FractionRing (PowerSeries k) →ₐ[k] FractionRing (PowerSeries k) :=
  if h : PowerSeries.constantCoeff z = 0 ∧ z ≠ 0 then (exists_sig h).choose else AlgHom.id k _

theorem sig_apply {z : PowerSeries k} (h : PowerSeries.constantCoeff z = 0) (h0 : z ≠ 0) (x : PowerSeries k) :
    sig z (algebraMap _ _ x) = toK k (x.subst z) := by
  rw [sig, dif_pos ⟨h, h0⟩]
  exact (exists_sig ⟨h, h0⟩).choose_spec x

section Rel
variable {G : Over (Sp k)} [GrpObj G] (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)

def Rel (z w : PowerSeries k) (c : algOver k k ⟶ G) : Prop :=
  Red ((algOverHom (sig w) ≫ a) * (algOverHom (sig z) ≫ a)⁻¹) c

variable {a}

theorem Rel.trans {x y z : PowerSeries k} {c c' : algOver k k ⟶ G} (h : Rel a x y c) (h' : Rel a y z c') :
    Rel a x z (c' * c) := by
  have := Red.mul h' h
  rwa [_root_.mul_assoc, inv_mul_cancel_left] at this

theorem Rel.symm {x y : PowerSeries k} {c : algOver k k ⟶ G} (h : Rel a x y c) : Rel a y x c⁻¹ := by
  have := Red.inv h
  rwa [mul_inv_rev, inv_inv] at this

variable {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}
  {h : Fin r → MvPowerSeries (Fin 2) k} {d : MvPowerSeries (Fin 2) k}

theorem TwoVar.arc (ht : TwoVar j f a h d) {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) :
    ∃ χ : A →ₐ[k] FractionRing (PowerSeries k),
      (∀ i, χ (f i) * toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d) =
        toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i))) ∧
      (algOverHom (sig w) ≫ a) * (algOverHom (sig z) ≫ a)⁻¹ = algOverHom χ ≫ j := by
  have hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> assumption
  have hτ : ∀ x : MvPowerSeries (Fin 2) k, ((toK k).comp (MvPowerSeries.substAlgHom hs)) x =
      toK k (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) x) := fun x => by
    rw [AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
  obtain ⟨χ, h1, h2⟩ := ht _ ((toK k).comp (MvPowerSeries.substAlgHom hs)) (sig z) (sig w)
    (by rw [hτ]; exact fun e => hd (toK_injective (e.trans (map_zero _).symm)))
    (fun x => by rw [hτ, sig_apply hz hz0, ((GlobalTheory.T.subst_two_variables_identities_alt k).2 x z w hz hw).1])
    (fun x => by rw [hτ, sig_apply hw hw0, ((GlobalTheory.T.subst_two_variables_identities_alt k).2 x z w hz hw).2])
  exact ⟨χ, fun i => by rw [← hτ, ← hτ]; exact h1 i, by rw [h2, mul_inv_cancel_right]⟩

theorem TwoVar.rel (hc : IsChart G j ε f) (ht : TwoVar j f a h d) {z w : PowerSeries k}
    (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) (y : Fin r → PowerSeries k)
    (hy : ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i)) :
    ∃ χ : A →ₐ[k] k, (∀ i, χ (f i) = PowerSeries.constantCoeff (y i)) ∧ Rel a z w (algOverHom χ ≫ j) := by
  obtain ⟨χ, h1, h2⟩ := ht.arc hz hw hz0 hw0 hd
  have hf : ∀ i, χ (f i) = toK k (y i) := fun i => by
    have := h1 i
    rw [← hy i, map_mul] at this
    exact mul_right_cancel₀ (fun e => hd (toK_injective (e.trans (map_zero _).symm))) this
  have hm : ∀ x, χ x ∈ (toK k).range := fun x => by
    have : Algebra.adjoin k (Set.range f) ≤ (toK k).range.comap χ :=
      Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact ⟨y i, (hf i).symm⟩)
    exact this (hc.2.2.1 ▸ Algebra.mem_top)
  let χ₀ : A →ₐ[k] PowerSeries k :=
    (AlgEquiv.ofInjective (toK k) toK_injective).symm.toAlgHom.comp (χ.codRestrict _ hm)
  have e : (toK k).comp χ₀ = χ := by
    ext x
    exact congrArg Subtype.val ((AlgEquiv.ofInjective (toK k) toK_injective).apply_symm_apply ⟨χ x, hm x⟩)
  refine ⟨(ev0 k).comp χ₀, fun i => ?_, algOverHom χ₀ ≫ j, ?_, ?_⟩
  · have : χ₀ (f i) = y i := toK_injective ((AlgHom.congr_fun e (f i)).trans (hf i))
    rw [AlgHom.comp_apply, this, laurentCoeffEvalLinear_apply]
  · rw [h2, ← Category.assoc, ← algOverHom_comp, e]
  · rw [← Category.assoc, ← algOverHom_comp]

theorem TwoVar.of_rel_one (hc : IsChart G j ε f) (ht : TwoVar j f a h d) {z w : PowerSeries k}
    (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hd : MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0) (hr : Rel a z w 1) (i : Fin r) :
    ∃ y : PowerSeries k, PowerSeries.constantCoeff y = 0 ∧
      y * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) := by
  obtain ⟨χ, h1, h2⟩ := ht.arc hz hw hz0 hw0 hd
  obtain ⟨b, hb1, hb2⟩ := hr
  obtain ⟨e, he, hl⟩ := GlobalTheory.T.exists_basicOpen_factor_fieldPoint_affineOpen k G A (PowerSeries k) k j b (ev0 k) ε hc.1 (hb2.trans hc.2.1.symm)
  obtain ⟨χ₀, h0⟩ := hl (PowerSeries k) (AlgHom.id k _)
    (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.mk0 _ he))
  rw [algOverHom_id, Category.id_comp] at h0
  subst h0
  rw [← Category.assoc, ← algOverHom_comp] at hb1 hb2
  have e1 := eq_of_comp_eq hc.1 (hb1.trans h2)
  have e2 := eq_of_comp_eq hc.1 (hb2.trans hc.2.1.symm)
  refine ⟨χ₀ (f i), (AlgHom.congr_fun e2 (f i)).trans (hc.2.2.2 i), toK_injective ?_⟩
  rw [map_mul, ← h1 i, ← e1, AlgHom.comp_apply]

theorem const_of_le {m : ℕ} (hm : 1 ≤ m) {z : PowerSeries k} (hz : (m : ℕ∞) ≤ z.order) :
    PowerSeries.constantCoeff z = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)

theorem le_order_mon (t : k) (n : ℕ) : (n : ℕ∞) ≤ (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k).order :=
  PowerSeries.nat_le_order _ _ fun i hi => by simp [PowerSeries.coeff_X_pow, hi.ne]

theorem coeff_mon (t : k) (n : ℕ) : PowerSeries.coeff n (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k) = t := by
  simp [PowerSeries.coeff_X_pow]

theorem order_mon {t : k} (ht : t ≠ 0) (n : ℕ) : (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k).order = n :=
  le_antisymm (PowerSeries.order_le n (by rwa [coeff_mon])) (le_order_mon t n)

theorem ne_zero_of_coeff {n : ℕ} {z : PowerSeries k} (hz : PowerSeries.coeff n z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz

theorem coeff_ne_of_order {n : ℕ} {z : PowerSeries k} (hz : z.order = n) : PowerSeries.coeff n z ≠ 0 :=
  (PowerSeries.order_eq_nat.1 hz).1

theorem le_order_sub {n : ℕ∞} {z w : PowerSeries k} (hz : n ≤ z.order) (hw : n ≤ w.order) : n ≤ (z - w).order := by
  rw [sub_eq_add_neg]
  refine le_trans (le_min hz ?_) (PowerSeries.min_order_le_order_add _ _)
  rwa [PowerSeries.order_neg]

variable [IsAlgClosed k]

theorem TwoVar.lt_of_rel (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : d ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hr : ∀ z w : PowerSeries k, z.order = m → w.order = n → Rel a z w 1) (i : Fin r) :
    MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) := by
  by_contra hlt
  have hle := not_lt.1 hlt
  have hi : h i ≠ 0 := by
    intro e
    rw [e, MvPowerSeries.weightedOrder_zero, top_le_iff, MvPowerSeries.weightedOrder_eq_top_iff] at hle
    exact hd hle
  obtain ⟨P₁, Q₁, hP₁, -, h₁⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn 1 (fun _ => d) (h i) hi (fun _ => hle)
  obtain ⟨P₂, Q₂, hP₂, -, h₂⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn 0 Fin.elim0 d hd (fun i => i.elim0)
  obtain ⟨t, ht0⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card (Polynomial.X * P₁ * P₂)
    (mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero hP₁) hP₂)
    (lt_of_lt_of_le Cardinal.natCast_lt_aleph0 (Cardinal.aleph0_le_mk k))
  simp only [Polynomial.eval_mul, Polynomial.eval_X, ne_eq, mul_eq_zero, not_or] at ht0
  have c1 : PowerSeries.coeff m (PowerSeries.C (1 : k) * PowerSeries.X ^ m : PowerSeries k) = 1 ^ m := by
    rw [coeff_mon, one_pow]
  have c2 : PowerSeries.coeff n (PowerSeries.C t * PowerSeries.X ^ n : PowerSeries k) = 1 ^ n * t := by
    rw [coeff_mon, one_pow, _root_.one_mul]
  obtain ⟨-, y, hy⟩ := h₁ 1 t _ _ one_ne_zero (le_order_mon 1 m) (le_order_mon t n) c1 c2 ht0.1.2
  obtain ⟨hD, -⟩ := h₂ 1 t _ _ one_ne_zero (le_order_mon 1 m) (le_order_mon t n) c1 c2 ht0.2
  obtain ⟨y', hy0, hy'⟩ := ht.of_rel_one hc (const_of_le hm (le_order_mon 1 m)) (const_of_le hn (le_order_mon t n))
    (ne_zero_of_coeff (n := m) (by rw [coeff_mon]; exact one_ne_zero))
    (ne_zero_of_coeff (n := n) (by rw [coeff_mon]; exact ht0.1.1)) hD
    (hr _ _ (order_mon one_ne_zero m) (order_mon ht0.1.1 n)) i
  have e := (hy 0).1
  rw [← hy', ← _root_.mul_assoc] at e
  have e1 : y 0 * y' = 1 := mul_right_cancel₀ hD (e.trans (_root_.one_mul _).symm)
  have e2 := congrArg PowerSeries.constantCoeff e1
  simp [hy0] at e2

theorem TwoVar.gen_of_lt (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : d ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hq : ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i))
    (z : PowerSeries k) (hz : z.order = m) :
    ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1 := by
  obtain ⟨Pd, P, hPd, hP, hg⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn r h d hd (fun i => (hq i).le)
  have hz0 := coeff_ne_of_order hz
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (PowerSeries.coeff m z) (n := m) hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact hz0 hs.symm
  refine ⟨insert 0 ((fun t => s ^ n * t) '' {t | Pd.IsRoot t}),
    ((Polynomial.finite_setOf_isRoot hPd).image _).insert _, fun t hS => ?_⟩
  have e : s ^ n * (t / s ^ n) = t := mul_div_cancel₀ _ (pow_ne_zero _ hs0)
  have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
  have hp : Pd.eval (t / s ^ n) ≠ 0 := fun e' => hS (Or.inr ⟨_, e', e⟩)
  obtain ⟨hD, y, hy⟩ := hg s (t / s ^ n) z _ hs0 hz.ge (le_order_mon t n) hs.symm (by rw [coeff_mon, e]) hp
  obtain ⟨χ, h1, h2⟩ := ht.rel hc (const_of_le hm hz.ge) (const_of_le hn (le_order_mon t n)) (ne_zero_of_coeff hz0)
    (ne_zero_of_coeff (n := n) (by rwa [coeff_mon])) hD y (fun i => (hy i).1)
  have : χ = ε := hc.hom_ext fun i => by
    have := (hy i).2
    rw [(hP i).2 (hq i), Polynomial.eval_zero, mul_eq_zero] at this
    rw [h1, hc.2.2.2, this.resolve_right hp]
  rwa [this, hc.2.1] at h2

theorem TwoVar.shear (hc : IsChart G j ε f) (ht : TwoVar j f a h d) (hd : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hq : ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) :
    ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Pd ≠ 0 ∧
      (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) ∧
      ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n (w - z) = s ^ n * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j) := by
  classical
  obtain ⟨Pd, P, hPd, hP, hg⟩ := GlobalTheory.T.exists_leading_quotient_weighted_arcs k m n hm hn r _ _ hd hq
  refine ⟨Pd, P, fun t => if e : ∃ χ : A →ₐ[k] k, ∀ i, χ (f i) * Pd.eval t = (P i).eval t then e.choose else ε,
    hPd, hP, fun s t z w hs hz hw cz cw hp hw0 => ?_⟩
  obtain ⟨hD, y, hy⟩ := hg s t z (w - z) hs hz hw cz cw hp
  have z0 := const_of_le hm hz
  have w0 := const_of_le hn hw
  have key : ∀ x : MvPowerSeries (Fin 2) k, MvPowerSeries.subst (![z, w - z] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) x) =
      MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) x := fun x => by
    rw [((GlobalTheory.T.subst_two_variables_identities_alt k).1 x).2 z (w - z) z0 w0, add_sub_cancel]
  simp only [key] at hD hy
  obtain ⟨χ, h1, h2⟩ := ht.rel hc z0 (by rwa [map_sub, z0, sub_zero] at w0)
    (ne_zero_of_coeff (n := m) (by rw [cz]; exact pow_ne_zero _ hs)) hw0 hD y (fun i => (hy i).1)
  have e : ∃ χ : A →ₐ[k] k, ∀ i, χ (f i) * Pd.eval t = (P i).eval t := ⟨χ, fun i => by rw [h1, (hy i).2]⟩
  simp only [dif_pos e]
  have : e.choose = χ := hc.hom_ext fun i =>
    mul_right_cancel₀ hp (by rw [e.choose_spec i, h1, (hy i).2])
  exact ⟨e.choose_spec, by rwa [this]⟩

omit [IsAlgClosed k] in

theorem add_step {m n : ℕ} (hmn : m < n) {Pd : Polynomial k} {P : Fin r → Polynomial k} {ψ : k → (A →ₐ[k] k)}
    (hg : ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n (w - z) = s ^ n * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j)) (u t : k) (ht : Pd.eval t ≠ 0) :
    (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧
      Rel a (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C u * PowerSeries.X ^ n)
        (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C (t + u) * PowerSeries.X ^ n) (algOverHom (ψ t) ≫ j) := by
  have c : ∀ v : k, PowerSeries.coeff m
      (PowerSeries.C (1 : k) * PowerSeries.X ^ m + PowerSeries.C v * PowerSeries.X ^ n : PowerSeries k) = 1 := by
    intro v
    simp [PowerSeries.coeff_X_pow, hmn.ne]
  have e : (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C (t + u) * PowerSeries.X ^ n : PowerSeries k) -
      (PowerSeries.C 1 * PowerSeries.X ^ m + PowerSeries.C u * PowerSeries.X ^ n) =
      PowerSeries.C t * PowerSeries.X ^ n := by
    rw [map_add]; ring
  refine hg 1 t _ _ one_ne_zero ?_ ?_ ?_ ?_ ht (ne_zero_of_coeff (n := m) (by rw [c]; exact one_ne_zero))
  · refine le_trans (le_min (le_order_mon 1 m) (le_trans ?_ (le_order_mon u n))) (PowerSeries.min_order_le_order_add _ _)
    exact_mod_cast hmn.le
  · rw [e]; exact le_order_mon t n
  · rw [c, one_pow]
  · rw [e, coeff_mon, one_pow, _root_.one_mul]

theorem mul_step {m : ℕ} (hm : 1 ≤ m) {Pd : Polynomial k} {P : Fin r → Polynomial k} {ψ : k → (A →ₐ[k] k)}
    (hg : ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (m : ℕ∞) ≤ (w - z).order →
        PowerSeries.coeff m z = s ^ m → PowerSeries.coeff m (w - z) = s ^ m * t → Pd.eval t ≠ 0 → w ≠ 0 →
        (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧ Rel a z w (algOverHom (ψ t) ≫ j)) (z : PowerSeries k) (hz : z.order = m) (t : k) (h0 : t ≠ 0) (ht : Pd.eval (t - 1) ≠ 0) :
    (∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1)) ∧
      Rel a z (PowerSeries.C (t * PowerSeries.coeff m z) * PowerSeries.X ^ m) (algOverHom (ψ (t - 1)) ≫ j) := by
  have hz0 := coeff_ne_of_order hz
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (PowerSeries.coeff m z) (n := m) hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact hz0 hs.symm
  refine hg s (t - 1) _ _ hs0 hz.ge (le_order_sub (le_order_mon _ m) hz.ge) hs.symm ?_ ht
    (ne_zero_of_coeff (n := m) (by rw [coeff_mon]; exact mul_ne_zero h0 hz0))
  rw [map_sub, coeff_mon, hs]; ring

omit [IsAlgClosed k] in
theorem comp_sub_one_eq_zero {q : Polynomial k} : q.comp (Polynomial.X - Polynomial.C 1) = 0 ↔ q = 0 :=
  ⟨fun e => by
      have e' : (q.comp (Polynomial.X - Polynomial.C 1)).comp (Polynomial.X + Polynomial.C (1 : k)) = 0 := by
        rw [e, Polynomial.zero_comp]
      rw [Polynomial.comp_assoc] at e'
      simpa using e',
    fun e => by rw [e, Polynomial.zero_comp]⟩

theorem dichotomy_alg (p : ℕ) [CharP k p] (hG : SmConn G)
    (hna : ¬ ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = a) :
    Infinite {x : (algOver k k ⟶ G) // x ^ p = 1} ∨ ∃ f : Gm (Sp k) ⟶ G, IsMonHom f ∧ f ≠ 1 := by
  obtain ⟨A, _, _, j, ε, r, f, hc⟩ := GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG
  obtain ⟨h, d, hd1, hh1, ht⟩ := GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a
  have hsep := hG.2.2.1
  have hXd := mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1
  have hXh := fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)
  have hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0 := fun e => hXd (e ▸ dvd_zero _)
  have hd : d ≠ 0 := by
    rintro rfl
    apply hd1
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]
  by_cases hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))
  · exfalso
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)
    obtain ⟨ch1, ch2⟩ := GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1)
      (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
        ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1)
      (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using h.trans h') (fun _ _ h => h)
    have g11 := ch1 1 1 (fun z hz => by
      have hz0 := coeff_ne_of_order hz
      refine ⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}),
        ((Polynomial.finite_setOf_isRoot hPd).image _).insert _, fun t hS => ?_⟩
      have e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t := div_mul_cancel₀ _ hz0
      have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
      have hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0 := fun e' =>
        hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)
      obtain ⟨h1, h2⟩ := mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp
      have : ψ (t / PowerSeries.coeff 1 z - 1) = ε := hc.hom_ext fun i => by
        have := h1 i
        rw [(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero] at this
        rw [hc.2.2.2, this.resolve_right hp]
      rwa [this, hc.2.1, e] at h2)
    obtain ⟨-, s2, s3, s4⟩ := GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)
    obtain ⟨m₀, hm₀⟩ := s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)
    have all := ch2 (m₀ + 1) fun m hm =>
      ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))
    refine hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))
    refine (s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)
    intro z w hz hw
    exact all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw
  · obtain ⟨m, n, hm, hmn, hle, i, hi⟩ := (GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _
      (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' hm (hm.trans hmn) hle
    have hPi : P i ≠ 0 := fun e => ((hP i).1 e).ne hi
    rcases hmn.lt_or_eq with hlt | rfl
    · left
      refine GlobalTheory.T.infinite_pth_roots_of_additive_family k p _ A r f ε (fun χ => algOverHom χ ≫ j) Pd P ψ hc.2.2.1 hc.2.2.2
        (fun _ _ e => eq_of_comp_eq hc.1 e) hc.2.1 hPd ⟨i, hPi⟩ (fun t ht => (add_step hlt hg 0 t ht).1)
        fun t t' h1 h2 h3 => ?_
      have e1 := (add_step hlt hg 0 t' h2).2
      have e2 := (add_step hlt hg (t' + 0) t h1).2
      have e3 := (add_step hlt hg 0 (t + t') h3).2
      rw [_root_.add_assoc] at e3
      exact Red.unique hsep (e1.trans e2) e3
    · right
      have ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1) :=
        fun q t => by simp
      refine GlobalTheory.T.exists_oneParameterSubgroup_of_rational_family k G A j ε r f (Pd.comp (Polynomial.X - Polynomial.C 1))
        (fun i => (P i).comp (Polynomial.X - Polynomial.C 1)) (fun t => ψ (t - 1)) hG hc
        (mt comp_sub_one_eq_zero.1 hPd) ⟨i, mt comp_sub_one_eq_zero.1 hPi⟩ (fun t h0 h1 => ?_)
        fun t t' h0 h0' h1 h2 h3 => ?_
      · simp only [ev] at h1 ⊢
        exact (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1
      · rw [ev] at h1 h2 h3
        have e1 := (mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2
        have e3 := (mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2
        rw [coeff_mon, _root_.mul_one] at e1 e3
        have e2 := (mul_step hm hg _ (order_mon h0' m) t h0 h1).2
        rw [coeff_mon] at e2
        exact Red.unique hsep (e1.trans e2) e3

end Rel

end GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS
open ArcInf

theorem infinite_torsion_or_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left, a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → (¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → Infinite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ p = 1} ∨ ∃ f : Gm (Sp k) ⟶ G, IsMonHom f ∧ f ≠ 1 := by
  intro k _ _ p _ _ G _ hG a ha hna
  let a' : algOver k (FractionRing (PowerSeries k)) ⟶ G := Over.homMk a ha
  refine (dichotomy_alg (a := a') p hG ?_).imp_left fun (hI : Infinite {x : (algOver k k ⟶ G) // x ^ p = 1}) => ?_
  · rintro ⟨b, hb⟩
    exact hna ⟨b.left, congrArg (fun x => x.left) hb⟩
  · let e : 𝟙_ (Over (Sp k)) ≅ algOver k k := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ spMap (RingHom.id k) = 𝟙 _
      rw [Category.id_comp]
      exact Spec.map_id _)
    refine @Infinite.of_injective _ _ hI (fun x : {x : (algOver k k ⟶ G) // x ^ p = 1} =>
      (⟨e.hom ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩ : {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ p = 1})) ?_
    intro x y hxy
    exact Subtype.ext ((cancel_epi e.hom).1 (congrArg Subtype.val hxy))

end GlobalTheory.SS
end
end
