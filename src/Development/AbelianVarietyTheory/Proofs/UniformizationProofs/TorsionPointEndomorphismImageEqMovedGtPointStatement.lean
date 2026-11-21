import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TensorContentEqPolyContentScalarCoeffs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelationStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg

section
namespace GlobalTheory

theorem exists_smul_eq_bilin_of_anisotropic {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : X →+ X →+ ℤ) (hB : ∀ a, B a a = 0 → a = 0) (l : X →+ ℚ) :
    ∃ (M : ℤ) (x : X), 0 < M ∧ ∀ m, (B x m : ℚ) = M * l m := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose c hc using hint
  let φ : Module.Dual ℤ X := b.constr ℤ c
  have hφ : ∀ m, (φ m : ℚ) = d * l m := by
    have : (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap := by
      refine b.ext fun i => ?_
      have := hc i
      simpa [φ] using this
    intro m
    have := LinearMap.congr_fun this m
    simpa using this
  let Bh : X →+ Module.Dual ℤ X :=
    { toFun := fun x => (B x).toIntLinearMap
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let BL : X →ₗ[ℤ] Module.Dual ℤ X := Bh.toIntLinearMap
  have hBL : ∀ x m, BL x m = B x m := fun _ _ => rfl
  have hinj : Function.Injective BL := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hB
    rw [← hBL, ha]; rfl
  have hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X) := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact b.toDualEquiv.finrank_eq
  have hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrk
  obtain ⟨n, hn, hnφ⟩ := (isOfFinAddOrder_of_finite
    (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnφ
  obtain ⟨x, hx⟩ := hnφ
  refine ⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩
  have h1 : B x m = n * φ m := by
    rw [← hBL, hx]; simp
  rw [map_zsmul, AddMonoidHom.zsmul_apply, h1]
  simp only [smul_eq_mul]
  push_cast
  rw [hφ]; ring

theorem exists_rep_mod_shifted_form_small :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by
  intro X _ _ _ Q B hadd h2 hpos l k hk y
  have hQ0 : ∀ a, 0 ≤ Q a := by
    intro a
    by_cases ha : a = 0
    · have := h2 a
      rw [ha] at this ⊢
      simp at this
      omega
    · have := hpos a ha
      omega
  have hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a := by
    intro n a
    have e1 := h2 (n • a)
    have e2 := h2 a
    rw [map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2] at e1
    simp only [smul_eq_mul] at e1
    linarith
  obtain ⟨M, x, hM, hx⟩ := exists_smul_eq_bilin_of_anisotropic B (fun a ha => by
    by_contra h
    have := hpos a h
    have := h2 a
    omega) l
  let F : X → ℕ := fun z => (Q (M • (y + k • z) - x)).toNat
  obtain ⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z' :=
    ⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩
  refine ⟨z, fun m => ?_⟩
  have hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x) := by
    intro z'
    have := hz z'
    have a := hQ0 (M • (y + k • z) - x)
    have b := hQ0 (M • (y + k • z') - x)
    simp only [F] at this
    omega
  have key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m
      + (M * k * s) * (M * B (y + k • z) m - B x m) := by
    intro s
    have h := hz' (z + s • m)
    have e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m := by
      module
    rw [e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply] at h
    simp only [smul_eq_mul] at h
    linarith
  have k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m
      + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key 1
  have k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m
      + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key (-1)
  push_cast at k1 k2
  rw [hx] at k1 k2
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hp : (0 : ℚ) < M * M * k := by positivity
  set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.CrossTheta

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem cross_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (b : Y ⟶ Y) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k')))
    (H : ∀ y J, Good L y J → sval s₁ b y J * sval s₂' (𝟙 _) y J = sval s₂ b y J * sval s₁' (𝟙 _) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ (r ≫ b) z J * sval s₂' r z J = sval s₂ (r ≫ b) z J * sval s₁' r z J := by
  obtain ⟨I, hI, e⟩ := exists_good L hL (r z) (K := Bool) (fun c => cond c (b ≫ p) (𝟙 _ ≫ p))
    (fun c => J (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p))) (fun a c e => congrArg (fun q => J (r ≫ q)) e)
    (fun c => hJ (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p)))
  have v : ∀ (c : Y ⟶ Y) {m : ℤ} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => m))),
      I (c ≫ p) = J (r ≫ c ≫ p) → sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
    intro c m s hc
    rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
    exact gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _
  have h := congrArg (r.stalkMap z).hom (H (r z) I hI)
  rw [map_mul, map_mul, ← v b s₁ (e true), ← v b s₂ (e true), ← v (𝟙 _) s₁' (e false), ← v (𝟙 _) s₂' (e false),
    Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (a : A ⟶ A) [IsMonHom a] (x : T ⟶ A) :
    translT A x ≫ T ◁ a = T ◁ a ≫ translT A (x ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (a : A ⟶ A) [IsMonHom a] {k k' : ℤ} (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k' T) (hp : θ.pt = θ'.pt ≫ a)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A L k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A L k' T)}
    (h₁ : IsActOf A L k θ t₁ T₁) (h₂ : IsActOf A L k θ t₂ T₂) (h₁' : IsActOf A L k' θ' t₁' T₁')
    (h₂' : IsActOf A L k' θ' t₂' T₂') :
    (∀ y J, Good L y J → sval (L := L) t₁ (T ◁ a).left y J * sval (L := L) t₂' (𝟙 _) y J =
      sval (L := L) t₂ (T ◁ a).left y J * sval (L := L) t₁' (𝟙 _) y J) ↔
    (∀ y J, Good L y J → sval (L := L) T₁ (T ◁ a).left y J * sval (L := L) T₂' (𝟙 _) y J =
      sval (L := L) T₂ (T ◁ a).left y J * sval (L := L) T₁' (𝟙 _) y J) := by
  have c : (T ◁ a).left ≫ (translT A θ.pt).left = (translT A θ'.pt).left ≫ (T ◁ a).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}, Good L z J →
      (sval (L := L) T₁ (r ≫ (T ◁ a).left) z J * sval (L := L) T₂' r z J =
        sval (L := L) T₂ (r ≫ (T ◁ a).left) z J * sval (L := L) T₁' r z J ↔
      sval (L := L) t₁ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₂' (r ≫ (translT A θ'.pt).left) z J =
        sval (L := L) t₂ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₁' (r ≫ (translT A θ'.pt).left) z J) := by
    intro Z r z J hJ
    rw [ThetaPowOrder.act_sval h₁ _ z hJ, ThetaPowOrder.act_sval h₂ _ z hJ, ThetaPowOrder.act_sval h₁' _ z hJ,
      ThetaPowOrder.act_sval h₂' _ z hJ, Category.assoc, c, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L) t₂ _ z J), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J hJ
    have h := (key (𝟙 _) y hJ).2 (cross_val hL _ _ t₁ t₂ t₁' t₂' H _ y hJ)
    rwa [Category.id_comp] at h
  · intro H y J hJ
    have h := (key (translT A θ'.pt⁻¹).left y hJ).1 (cross_val hL _ _ T₁ T₂ T₁' T₂' H _ y hJ)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta

namespace GlobalTheory

theorem cross_iff_of_isActOf : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j j' : ℕ) (θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A.A A.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ a → ∀ (t₁ t₂ T₁ T₂ : SecA A F j) (t₁' t₂' T₁' T₂' : SecA A F j'), IsActOf A.A A.L j θ t₁ T₁ → IsActOf A.A A.L j θ t₂ T₂ → IsActOf A.A A.L j' θ' t₁' T₁' → IsActOf A.A A.L j' θ' t₂' T₂' → (Cross a t₁ t₂ t₁' t₂' ↔ Cross a T₁ T₂ T₁' T₂') := by
  intro _ R _ _ A F _ _ a ha j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  exact CrossTheta.cross_act A.isLB a θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem exists_addGauss (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    ∃ w : AddValuation (AddMonoidAlgebra F X) (WithTop ℚ),
      ∀ (f : AddMonoidAlgebra F X) (g : WithTop ℚ), g ≤ w f ↔ ∀ m, g ≤ v (f.coeff m) := by
  haveI : UniqueSums X :=
    (AddEquiv.uniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance
  exact ⟨AddValuation.ofValuation (GlobalTheory.gaussValAlg (G := X) (AddValuation.toValuation v)),
    fun f g => GlobalTheory.gaussValAlg_le_iff (G := X) (AddValuation.toValuation v) (f := f)⟩

theorem NullV.exists_lower {X : Type} {A : X → F} (hA : NullV v A) :
    ∃ M : ℚ, ∀ M' : ℚ, M' ≤ M → ∀ χ, (M' : WithTop ℚ) ≤ v (A χ) := by
  obtain ⟨M, hM⟩ := ((hA 0).image (fun χ => (v (A χ)).untopD 0)).bddBelow
  refine ⟨min M 0, fun M' hM' χ => ?_⟩
  by_cases hχ : v (A χ) < ((0 : ℚ) : WithTop ℚ)
  · have h1 : M ≤ (v (A χ)).untopD 0 := hM ⟨χ, hχ, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hχ.ne_top
    rw [← hr] at h1 ⊢
    rw [WithTop.untopD_coe] at h1
    exact WithTop.coe_le_coe.mpr (hM'.trans ((min_le_left _ _).trans h1))
  · exact (WithTop.coe_le_coe.mpr (hM'.trans (min_le_right _ _))).trans (not_lt.mp hχ)

theorem NullV.exists_trunc {X : Type} {A : X → F} (hA : NullV v A) (N : ℚ) :
    ∃ a : AddMonoidAlgebra F X, (∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) ∧
      (∀ χ, v (A χ) ≤ v (a.coeff χ)) ∧ ∀ χ, v (A χ) < (N : WithTop ℚ) → a.coeff χ = A χ := by
  classical
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (hA N).toFinset
    (fun χ => if v (A χ) < (N : WithTop ℚ) then A χ else 0) (fun χ hχ => ?_)), fun χ => ?_, fun χ => ?_,
    fun χ hχ => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    by_contra hn
    exact hχ (if_neg hn)
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · simp
    · simpa using hχ
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · exact le_rfl
    · simp
  · simp only [Finsupp.onFinset_apply, if_pos hχ]

theorem coeff_mapDomain_mul {X : Type} [AddCommGroup X] (h : X →+ X) (a c : AddMonoidAlgebra F X)
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem val_mul_sub_mul {x y x' y' : F} {M N : ℚ} (hx : (N : WithTop ℚ) ≤ v (x - x'))
    (hy : (N : WithTop ℚ) ≤ v (y - y')) (hy0 : (M : WithTop ℚ) ≤ v y) (hx0 : (M : WithTop ℚ) ≤ v x') :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (x * y - x' * y') := by
  have e : x * y - x' * y' = (x - x') * y + (y - y') * x' := by ring
  rw [e, WithTop.coe_add]
  refine v.map_le_add ?_ ?_ <;> rw [v.map_mul]
  · exact add_le_add hx hy0
  · exact add_le_add hy hx0

theorem SumV.fibre {X : Type} [AddCommGroup X] (h : X →+ X) (α : X) (f : X → X → F) {s : F}
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X ≃ {p : X × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X : Type} [AddCommGroup X] (h : X →+ X) {A C : X → F}
    {a c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X : Type} [AddCommGroup X] (h : X →+ X) {A₁ A₂ C₁ C₂ : X → F}
    {a₁ a₂ c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := SumV.fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

theorem sumV_cancel : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X →+ X), Function.Injective h → ∀ A₁ A₂ B₁ B₂ C₁ C₂ : X → F, NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X) (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := val_sum_sub_coeff (AddMonoidHom.id X) hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := val_sum_sub_coeff (AddMonoidHom.id X) hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PullPair

open LBGerm GlobalTheory.AbLaw

def chartPullTw {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t) (𝟙 X) where
  idx J := (fun _ => J 0, fun _ => J 1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1⟩
  g y J J' hJ hJ' := by
    have a₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 1
    have b₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J' 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 1
    refine (gm_linComb L _ _ (𝟙 X) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t y
      (fun _ => J 0, fun _ => J 1) (fun _ => J' 0, fun _ => J' 1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb L _ _ (𝟙 X) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp]

theorem exists_sec_twist {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (f : X ⟶ X) (e : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (y : X) : ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have hLB := h.isLB
  obtain ⟨n, hn, hc⟩ := h.exists_cover_mul
  obtain ⟨N, s, hs, ha⟩ := hc k hk
  have : CompactSpace X := h.compactSpace
  have : QuasiSeparatedSpace X := h.quasiSeparatedSpace
  obtain ⟨i, hi⟩ : ∃ i, y ∈ nonzeroLocus (s i) := by
    have hy : y ∈ (⨆ i, nonzeroLocus (s i)) := hs ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  have hM := LB.isLB_linComb hLB (fun _ : PUnit => f) (fun _ => e)
  have hH := isLB_lbPow hLB (n * k)
  obtain ⟨V, N', hyV, hV⟩ := GlobalTheory.TwistGen.exists_nhds hM hH (s i) (ha i) y hi
  obtain ⟨u, hu⟩ := hV 1
  have hmul : n * k * (N' + 1) = k * (n * (N' + 1)) := by ring
  refine ⟨n * (N' + 1), Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  rw [← hmul]
  refine ⟨chartSec (chartPullTw L f e (n * k) (N' + 1)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id]
  · exact hu hyV
  · intro z j hj
    refine ⟨![j.1 PUnit.unit, j.2 PUnit.unit], Set.mem_iInter.2 fun m => ?_⟩
    fin_cases m
    · exact Set.mem_iInter.1 hj.1 PUnit.unit
    · exact Set.mem_iInter.1 hj.2 PUnit.unit

theorem exists_cross : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A F j, ∃ t₁' t₂' : SecA A F (k * n), Cross a t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A.L z J → sA t₂ (ptSecT A.A 1).left z J ≠ 0) → (∀ z J, Good A.L z J → sA t₂' (ptSecT A.A 1).left z J ≠ 0)) := by
  intro _ R _ _ A F _ _ a ha j k hk
  have hamp : IsAmpleLB A.L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample
  have hUq : Unique (TFK (R := R) F).left := by
    unfold TFK
    exact inferInstanceAs (Unique (Spec (CommRingCat.of F)))
  obtain ⟨n, hn, u, hu⟩ := PullPair.exists_sec_twist hamp a.left (-(j : ℤ)) k hk
    ((1 : TFK (R := R) F ⟶ A.A).left default)
  have hασ : ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) A.A).left ≫ a.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have hF : FormEq (Sum.elim (fun m => (snd (TFK (R := R) F) A.A).left ≫ (![a.left, 𝟙 A.A.left] : Fin 2 → _) m)
      (fun _ : Fin 1 => ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left))
      (Sum.elim (![-(j : ℤ), ((k * n : ℕ) : ℤ)] : Fin 2 → ℤ) (fun _ : Fin 1 => (j : ℤ)))
      (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => ((k * n : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, hασ]
    rw [mul_right_comm, ← zpow_add, neg_add_cancel, zpow_zero, _root_.one_mul]
  refine ⟨n, hn, fun (t₁ t₂ : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (fun _ => (j : ℤ)))) => ?_⟩
  obtain ⟨s₁, hs₁⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₁ ((TFK (R := R) F) ◁ a).left))
  obtain ⟨s₂, hs₂⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₂ ((TFK (R := R) F) ◁ a).left))
  refine ⟨s₁, s₂, ?_, ?_⟩
  · intro z J hJ
    unfold sA
    rw [hs₁ _ _ z J hJ, hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
    simp only [Category.id_comp]
    ring
  · intro hne z J hJ
    have hr : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ ((TFK (R := R) F) ◁ a).left =
        (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_whiskerLeft, MonObj.one_comp]
    have hs : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
        (1 : TFK (R := R) F ⟶ A.A).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_snd]
    have hne' := hne z J hJ
    unfold sA at hne' ⊢
    rw [hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, hr]
    have hmem : ((ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left) z ∈
        nonzeroLocus u := by
      rw [hs, Subsingleton.elim z default]
      exact hu
    unfold nonzeroLocus at hmem
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hmem
    have hunit := ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval u _ z hJ i hi
    exact fun h0 => hne' ((hunit.mul_right_eq_zero).1 h0)

end GlobalTheory.PullPair
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallPoint
open CoefBasic

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f : Ix → F} (h : SumV v f 0)
    (i₀ : Ix) (q : ℚ) (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i)) : (q : WithTop ℚ) ≤ v (f i₀) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ S) (Finset.subset_insert _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ S).erase i₀, f i) :=
    v.map_le_sum fun i hi => hq i (Finset.ne_of_mem_erase hi)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S), zero_sub, v.map_neg] at h₁
  have := v.map_le_sub h₁ h₂
  rwa [add_sub_cancel_right] at this

theorem eq_zero_of_val {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {x u : F} (hu : v u = 0) {N : ℕ}
    (hN : 1 ≤ N) (h : ∀ n : ℕ, (((N * (n + 1) : ℕ) : ℚ) : WithTop ℚ) ≤ v (x * u ^ n)) : x = 0 := by
  by_contra hx
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
  obtain ⟨n, hn⟩ := exists_nat_gt q
  have e := h n
  rw [v.map_mul, v.map_pow, hu, nsmul_zero, add_zero, ← hq, WithTop.coe_le_coe] at e
  have : ((n + 1 : ℕ) : ℚ) ≤ ((N * (n + 1) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hN
  push_cast at this e
  linarith

abbrev PSec {X : Scheme.{0}} (L : LB X) (n : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)))

theorem exists_mul_pow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {N : ℕ} (σ ρ : PSec L N) (n : ℕ) :
    ∃ τ : PSec L (N * (n + 1)), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      sval τ r z J = sval σ r z J * sval ρ r z J ^ n := by
  obtain ⟨τ, hτ⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 X) (ε' := fun _ => ((N * (n + 1) : ℕ) : ℤ))
    (H1.SquareUnits.formEq_of_add fun U _ h => by
      simp
      module) (H1.SectionArithmetic.mulSec σ (H1.SectionArithmetic.powSec fun _ : Fin n => ρ))
  refine ⟨τ, fun Z r z J hJ => ?_⟩
  rw [hτ Z r z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_powSec _ _ z hJ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem eq_of_veryAmple {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (p q : T ⟶ A)
    (H : ∀ z : T.left, ∃ J, Good L z J ∧ ∃ u : (T.left.presheaf.stalk z)ˣ, ∀ σ : PSec L n,
      sval σ q.left z J = u.val * sval σ p.left z J) : p = q := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ σ : PSec L n, ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J),
      Good L z J → sval σ r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j) (r ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 A.left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [hi, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (H1.SectionArithmetic.pullSec (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j) i')
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  choose σ hσ using sec
  have key : p.left ≫ i' = q.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · obtain ⟨J, hJ, u, hu⟩ := H y
      exact ⟨J, hJ, u, fun j => by rw [← hσ j _ _ y J hJ, ← hσ j _ _ y J hJ, hu]⟩
  refine Over.OverMorphism.ext ?_
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id] using this

section Values

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

abbrev PGen (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) : Type :=
  LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => m.left) (fun _ => 1))

def Ev {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) {n : ℕ} (σ : PSec D.toPre.P.L n) (x : F) : Prop :=
  ∀ z J, Good D.toPre.P.L z J →
    sval σ (TWM.ιS hϖ hv ≫ m).left z J = cst F z x * (val G (TWM.ιS hϖ hv).left z J).val ^ n

variable {hϖ hv}

theorem exists_ev_int {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (σ : PSec D.toPre.P.L n) : ∃ x : TWO.Ov v, Ev hϖ hv G σ x ∧
      ∀ (z : Spec (CommRingCat.of (ResidueField (TWO.Ov v)))) (J), Good D.toPre.P.L z J →
        IsUnit (sval σ (Spec.map (CommRingCat.ofHom (residue (TWO.Ov v))) ≫ m.left) z J) → IsUnit x := by
  have hL := D.toPre.P.isLB
  obtain ⟨G', hG', vG'⟩ := exists_gen hL (φ' := fun _ : Fin 1 => m.left ≫ 𝟙 _) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (GeneratorPullback.powGen _ _ _ G n) (powGen_isGen _ _ _ _ hG n)
  obtain ⟨x₀, hx₀⟩ := TwistUnit.exists_ratio_local (R := TWO.Ov v) hL (H1.SectionArithmetic.pullSec σ m.left) G' hG'
  have key : ∀ {E : Type} [CommRing E] (φ : TWO.Ov v →+* E) (z : Spec (CommRingCat.of E)),
      gs (Spec.map (CommRingCat.ofHom φ)) z ⊤ x₀ = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀))) := fun φ z => by
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial x₀
    rw [Category.id_comp] at e
    exact e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (TWM.appTop_specMap (CommRingCat.ofHom φ) x₀))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀, fun z J hJ => ?_, fun z J hJ hu => ?_⟩
  · rw [Over.comp_left, ← H1.SectionArithmetic.sval_pullSec σ m.left _ z hJ]
    refine (hx₀ _ _ z J hJ).trans (congrArg₂ (· * ·) (key (algebraMap (TWO.Ov v) F) z) ?_)
    rw [vG' _ _ z J hJ, UUA.val_powGen', Units.val_pow_eq_pow_val]
  · have e := hx₀ _ (Spec.map (CommRingCat.ofHom (residue (TWO.Ov v)))) z J hJ
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ] at e
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit e).mp hu)
    rw [key] at h₁
    refine isUnit_of_map_unit (residue (TWO.Ov v)) _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁

theorem exists_ev {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (σ : PSec D.toPre.P.L n) : ∃ x : F, 0 ≤ v x ∧ Ev hϖ hv G σ x := by
  obtain ⟨x, hx, -⟩ := exists_ev_int G hG σ
  exact ⟨x, x.2, hx⟩

theorem exists_ev_unit (hA : AmpleSt) {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (hn : 4 ≤ n) : ∃ (σ : PSec D.toPre.P.L n) (x : F), v x = 0 ∧ Ev hϖ hv G σ x := by
  have hL := D.toPre.P.isLB
  let z : Spec (CommRingCat.of (ResidueField (TWO.Ov v))) := closedPoint _
  obtain ⟨σ, hσ⟩ := TwistUnit.unitAt_pow hA D.toPre.P n hn (𝟙 _)
    ((Spec.map (CommRingCat.ofHom (residue (TWO.Ov v))) ≫ m.left) z)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨x, hx, hu⟩ := exists_ev_int G hG σ
  exact ⟨σ, x, TWO.v_unit v (hu z J hJ (TwistUnit.isUnit_sval_of hL σ _ z hσ J hJ)).unit, hx⟩

theorem Ev.mul_pow {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} {G : PGen hϖ hv m} {N n : ℕ} {σ ρ : PSec D.toPre.P.L N}
    {τ : PSec D.toPre.P.L (N * (n + 1))} (hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval τ r z J = sval σ r z J * sval ρ r z J ^ n) {x y : F}
    (hx : Ev hϖ hv G σ x) (hy : Ev hϖ hv G ρ y) : Ev hϖ hv G τ (x * y ^ n) := fun z J hJ => by
  rw [hτ _ _ z J hJ, hx z J hJ, hy z J hJ]
  simp only [cst_eq, map_mul, map_pow]
  ring

theorem exists_fam (hG : GlobalFnsSt) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (hϖ : Irreducible ϖ)
    (hv : ValOver ϖ F v) {j : ℕ} (hj : 1 ≤ j) (σ : PSec D.toPre.P.L j) :
    ∃ S : Fam D.toPre F j, NuGe D Q F v j S 0 ∧ (∀ β, (∀ mu, β ≠ j • mu) → ∀ i, (S.s β).f i = 0) ∧
      ∀ (b : TF (R := V) F ⟶ D.toPre.P.A) z J, Good D.toPre.P.L z J →
        sval (S.s 0) (lift (𝟙 (TF (R := V) F)) b).left z J = sval σ b.left z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨σB, hσB⟩ := exists_sec hL (φ' := D.toPre.famφB 0) (ε' := DegPre.famε j) (fun U _ h => by
    have p := SectionScalarValuation.prod_famB D.toPre (𝟙 _) 0 j h
    have c : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero _
    simp only [Over.id_left, Category.id_comp, c, _root_.mul_one] at p
    rw [p, Fin.prod_univ_one, inv_mul_cancel_right, zpow_sub_one, inv_mul_cancel_right]) σ
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB 0 i) (DegPre.famε j)
      (DegPre.famφ D.toPre F 0) (DegPre.famε j) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨s, hs⟩ := exists_sec hL hformF (H1.SectionArithmetic.pullSec σB (DegPre.prB D.toPre F).left)
  have hs' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = sval σB (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ =>
    (hs Z ρ z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ ρ z hJ)
  obtain ⟨S, rfl, hS⟩ := FamFree.exists_fam_single hG D.tau_bimult hj 0 s
  refine ⟨S, ExactTerm.nuGe_of_single hϖ hQ hv hj S 0 0 hS
    ⟨1, fun _ => 1, fun _ => σB, fun _ => S.s 0, fun _ => ?_, fun _ => ?_, fun j => ?_⟩,
    fun β hβ => hS β fun mu e => hβ mu (by rw [← e, zero_add]), fun b z J hJ => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_one, QForm.Q_zero hϖ D hQ]; simp
  · rw [Fin.sum_univ_one, DVR.constBF_eq, map_one]
    simp [resTop]
  · rw [hs' _ _ z J hJ, ← Over.comp_left, lift_snd, hσB _ _ z J hJ]

theorem exists_frame_val {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen)
    (G₀ : PGen hϖ hv (1 : _ ⟶ D.toPre.P.A)) (hG₀ : G₀.IsGen) {j : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A}
    (hb : TWM.ιS hϖ hv ≫ m = b) (w : Frm D.toPre F j b) (hw : w.IsGen) :
    ∃ (c : F) (ω : ℚ), v c = ω ∧ GenV hϖ hv w ω ∧ ∀ z J, Good D.toPre.P.L z J →
      (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (val G₀ (TWM.ιS hϖ hv).left z J).val ^ j := by
  have hL := D.toPre.P.isLB
  obtain ⟨W, hW, vW⟩ := exists_gen hL (φ' := TWM.lineφO hϖ hv m) (ε' := DegPre.lineε j)
    (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, TWM.lineφO, DegPre.lineε])
    (LB.mulGen _ _ _ _ _ (GeneratorPullback.powGen _ _ _ G₀ j) (LB.invGen _ _ _ (GeneratorPullback.powGen _ _ _ G j)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hG₀ j) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ hG j)))
  have hφ : ∀ i, DegPre.lineφ D.toPre F b i = (TWM.ιS hϖ hv).left ≫ TWM.lineφO hϖ hv m i := fun i => by
    fin_cases i
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left)
        (MonObj.comp_one (M := D.toPre.P.A) (TWM.ιS hϖ hv)).symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) hb.symm
  obtain ⟨c, hc, vc⟩ := TWM.exists_ratio (F := F) hL w hw (LB.pullGen _ _ _ W (TWM.ιS hϖ hv).left)
    (pullGen_isGen _ _ _ _ hW _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hφ])
  obtain ⟨ω, hω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  have e : ∀ z J, Good D.toPre.P.L z J →
      (val w (𝟙 _) z J).val = cst F z c * (val W (TWM.ιS hϖ hv).left z J).val := fun z J hJ => by
    have e₁ := val_pull hJ W (TWM.ιS hϖ hv).left (𝟙 _)
    rw [Category.id_comp] at e₁
    exact (vc _ (𝟙 _) z J hJ).trans (congrArg (fun u : _ˣ => cst F z c * u.val) e₁)
  refine ⟨c, ω, hω.symm, ⟨_, hφ, W, hW, c, hω.symm, e⟩, fun z J hJ => ?_⟩
  rw [e z J hJ, vW _ _ z J hJ, val_mul hJ, val_inv, UUA.val_powGen', UUA.val_powGen', _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right, Units.val_pow_eq_pow_val]

theorem exists_rig : ∃ G₀ : PGen hϖ hv (1 : _ ⟶ D.toPre.P.A), G₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J →
    val G₀ (TWM.ιS hϖ hv).left z J = rigV D.toPre (TF (R := V) F).hom z J := by
  refine ⟨LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TWM.TO hϖ hv).hom,
    pullGen_isGen _ _ _ _ D.toPre.rig_gen _, fun z J hJ => ?_⟩
  have e := val_pull (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) hJ D.toPre.rig (TWM.TO hϖ hv).hom
    (TWM.ιS hϖ hv).left
  rw [Over.w] at e
  exact e

theorem gtV_zero {o : GtPtF D.toPre F} (ho : o.IsZero) : GtV hϖ hv o 0 := by
  intro χ
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := TWM.gtφO hϖ hv (D := D) 1 χ) (ε' := DegPre.gtε)
    (fun U _ h => by
      rw [Fintype.prod_empty]
      simp [Fin.prod_univ_four, TWM.gtφO, DegPre.gtε])
    (LB.oneGen D.toPre.P.L (Y := (TWM.TO hϖ hv).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have e₁ : TWM.ιS hϖ hv ≫ (1 : _ ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have e₂ := comp_cP D.toPre (TWM.ιS hϖ hv) χ
  refine ⟨_, fun i => ?_, t, ht, 1, by rw [v.map_one]; rfl, fun z J hJ => ?_⟩
  · rw [hb]
    fin_cases i
    · refine congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left)
        (show cP D.toPre _ χ * 1 = TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * 1) from ?_)
      rw [_root_.mul_one, _root_.mul_one, e₂]
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₂.symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₁.symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₁.symm
  · rw [hs χ z J hJ, vt _ _ z J hJ, val_one, cst_eq, map_one, _root_.one_mul]

theorem coef_zero {j : ℕ} (S : Fam D.toPre F j) (g : GtPtF D.toPre F) (w : Frm D.toPre F j g.b) {β : D.toPre.X}
    (h : ∀ i, (S.s β).f i = 0) : coef S g w β = 0 :=
  coef_eq fun z J hJ => by
    rw [UUA.sval_zero_of h _ z J (hJ.mem _ _), cst_eq, map_zero]
    simp only [MulZeroClass.zero_mul]

theorem coef_at_zero {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} {G : PGen hϖ hv m} {j : ℕ} (S : Fam D.toPre F j)
    (g : GtPtF D.toPre F) (hb : TWM.ιS hϖ hv ≫ m = g.b) (w : Frm D.toPre F j g.b) {σ : PSec D.toPre.P.L j} {x c : F}
    (hS : ∀ (b : TF (R := V) F ⟶ D.toPre.P.A) z J, Good D.toPre.P.L z J →
      sval (S.s 0) (lift (𝟙 (TF (R := V) F)) b).left z J = sval σ b.left z J) (hx : Ev hϖ hv G σ x)
    (hc : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j) : coef S g w 0 = c * x :=
  coef_eq fun z J hJ => by
    have e := hx z J hJ
    have e' := hc z J hJ
    rw [hb] at e
    rw [hS _ z J hJ, e, val_corr hJ g.s_zero, val_one, Units.val_one]
    simp only [cst_eq, map_mul] at e' ⊢
    linear_combination (-cstH z x) * e'

end Values

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.b = 1 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hM := D.toPre.P.isLB
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  have hob' : TWM.ιS hϖ hv ≫ (1 : _ ⟶ D.toPre.P.A) = o.b := (MonObj.comp_one _).trans hob.symm
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) d.b
  obtain ⟨G, hG⟩ : ∃ G : PGen hϖ hv m, G.IsGen := exists_gen_of_local (V := TWO.Ov v) _ hM _ _
  obtain ⟨G₀, hG₀, vG₀⟩ := exists_rig (hϖ := hϖ) (hv := hv) (D := D)
  have A : ∀ n j : ℕ, 1 ≤ n → j = k * n → ∀ (σ₁ σ₂ : PSec D.toPre.P.L j) (x₁ x₂ y₁ y₂ : F), Ev hϖ hv G σ₁ x₁ →
      Ev hϖ hv G σ₂ x₂ → Ev hϖ hv G₀ σ₁ y₁ → Ev hϖ hv G₀ σ₂ y₂ → v y₂ = 0 →
      ((j : ℚ) : WithTop ℚ) ≤ v (x₁ * y₂ - x₂ * y₁) := by
    intro n j hn hj σ₁ σ₂ x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hu
    have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w, hw, Hw⟩ := H n j hn hj w₁ hw₁
    obtain ⟨c, ω, hcω, hω, vw⟩ := exists_frame_val G hG G₀ hG₀ hm w hw
    have vw' : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j := fun z J hJ => by rw [vw z J hJ, vG₀ z J hJ]
    have vw₁ : ∀ z J, Good D.toPre.P.L z J → (val w₁ (𝟙 _) z J).val * (val G₀ (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z 1 * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j := fun z J hJ => by
      rw [hw₁.2 z J hJ, vG₀ z J hJ, cst_eq, map_one, Units.val_one]
    obtain ⟨S₁, n₁, z₁, e₁⟩ := exists_fam hL.1.globalFns hQ hϖ hv hj1 σ₁
    obtain ⟨S₂, n₂, z₂, e₂⟩ := exists_fam hL.1.globalFns hQ hϖ hv hj1 σ₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ mu,
        (((j : ℚ) * Q mu : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ (j • mu)) := fun S hS mu => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) ((I o).2.2.1 j w₁ hw₁ hob) hS (j • mu)
      rwa [hQj, Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ mu,
        ((ω : ℚ) : WithTop ℚ) ≤ v (coef S d w (j • mu)) := fun S hS mu => by
      refine le_trans (WithTop.coe_le_coe.2 ?_) (((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS (j • mu))
      have := (abs_le.1 (hlQ mu)).1
      rw [hQj, map_nsmul, ← hll, nsmul_eq_mul]
      nlinarith
    have hQ1 : ∀ mu, j • mu ≠ 0 → (j : ℚ) ≤ j * Q mu := fun mu h => by
      have : (1 : ℚ) ≤ Q mu := by exact_mod_cast QForm.Q_pos hϖ D hQ (fun e => h (by rw [e, smul_zero]))
      nlinarith
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 j fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          exact le_trans (WithTop.coe_le_coe.2 (hQ1 mu hχ)) (bo S₂ n₂ mu)
        · rw [coef_zero S₂ o w₁ (z₂ χ fun mu h => e ⟨mu, h⟩), v.map_zero]; exact le_top
      rw [coef_at_zero S₂ o hob' w₁ e₂ hy₂ vw₁, _root_.one_mul, hu, ← WithTop.coe_zero, WithTop.coe_le_coe] at this
      linarith
    have term : ∀ S S' : Fam D.toPre F j, NuGe D Q F v j S 0 → NuGe D Q F v j S' 0 →
        (∀ β, (∀ mu, β ≠ j • mu) → ∀ i, (S.s β).f i = 0) → ∀ χ, χ ≠ 0 →
        ((ω + j : ℚ) : WithTop ℚ) ≤ v (coef S d w χ * coef S' o w₁ (0 - χ)) := fun S S' hS hS' hz χ hχ => by
      by_cases e : ∃ mu, χ = j • mu
      · obtain ⟨mu, rfl⟩ := e
        rw [v.map_mul, zero_sub, ← smul_neg, WithTop.coe_add]
        refine add_le_add (bd S hS mu) (le_trans (WithTop.coe_le_coe.2 (hQ1 (-mu) ?_)) (bo S' hS' (-mu)))
        rwa [smul_neg, neg_ne_zero]
      · rw [coef_zero S d w (hz χ fun mu h => e ⟨mu, h⟩), MulZeroClass.zero_mul, v.map_zero]; exact le_top
    have key := le_of_sumV (Hw S₁ S₂ hne 0) 0 (ω + j) fun χ hχ =>
      v.map_le_sub (term S₁ S₂ n₁ n₂ z₁ χ hχ) (term S₂ S₁ n₂ n₁ z₂ χ hχ)
    rw [sub_zero, coef_at_zero S₁ d hm w e₁ hx₁ vw', coef_at_zero S₂ d hm w e₂ hx₂ vw',
      coef_at_zero S₁ o hob' w₁ e₁ hy₁ vw₁, coef_at_zero S₂ o hob' w₁ e₂ hy₂ vw₁,
      show c * x₁ * (1 * y₂) - c * x₂ * (1 * y₁) = c * (x₁ * y₂ - x₂ * y₁) by ring, v.map_mul, hcω,
      WithTop.coe_add] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have hN : 4 ≤ k * 4 := by omega
  obtain ⟨ρ, y, hy0, hy⟩ := exists_ev_unit hL.1.ample G₀ hG₀ hN
  obtain ⟨x, hx0', hx⟩ := exists_ev G hG ρ
  have hx0 : v x = 0 := by
    obtain ⟨ρ', x', hx'0, hx'⟩ := exists_ev_unit hL.1.ample G hG hN
    obtain ⟨y', hy'0, hy'⟩ := exists_ev G₀ hG₀ ρ'
    have h₁ := A 4 _ (by omega) rfl ρ' ρ x' x y' y hx' hx hy' hy hy0
    have h₂ : (0 : WithTop ℚ) < v (x' * y - x * y') :=
      lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < k * 4)) h₁
    by_contra hne
    have h₃ : 0 < v (x * y') := by
      rw [v.map_mul]; exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hx0' (Ne.symm hne)) hy'0
    have h₄ := v.map_lt_add h₂ h₃
    rw [sub_add_cancel, v.map_mul, hx'0, hy0, add_zero] at h₄
    exact lt_irrefl _ h₄
  have B : ∀ (σ : PSec D.toPre.P.L (k * 4)) (a b : F), Ev hϖ hv G σ a → Ev hϖ hv G₀ σ b → a * y = x * b := by
    intro σ a b ha hb
    refine sub_eq_zero.1 (eq_zero_of_val (v := v) (u := x * y) (N := k * 4)
      (by rw [v.map_mul, hx0, hy0, add_zero]) (by omega) fun n => ?_)
    obtain ⟨τ₁, hτ₁⟩ := exists_mul_pow hM σ ρ n
    obtain ⟨τ₂, hτ₂⟩ := exists_mul_pow hM ρ ρ n
    have := A (4 * (n + 1)) _ (by omega) (_root_.mul_assoc _ _ _) τ₁ τ₂ _ _ _ _ (ha.mul_pow hτ₁ hx) (hx.mul_pow hτ₂ hx)
      (hb.mul_pow hτ₁ hy) (hy.mul_pow hτ₂ hy) (by rw [v.map_mul, v.map_pow, hy0, nsmul_zero, add_zero])
    convert this using 2
    ring
  have hxne : x ≠ 0 := fun h => by rw [h, v.map_zero] at hx0; exact WithTop.top_ne_zero hx0
  have hyne : y ≠ 0 := fun h => by rw [h, v.map_zero] at hy0; exact WithTop.top_ne_zero hy0
  refine (eq_of_veryAmple hM (isAffineOpen_top _) (hL.1.ample _ D.toPre.P _ hN).2 1 d.b fun z => ?_).symm
  obtain ⟨J, hJ⟩ := exists_good' hM z
  refine ⟨J, hJ, Units.map (cstH (R := V) z).toMonoidHom (Units.mk0 (x / y) (div_ne_zero hxne hyne)) *
    val G (TWM.ιS hϖ hv).left z J ^ (k * 4) * (val G₀ (TWM.ιS hϖ hv).left z J ^ (k * 4))⁻¹, fun σ => ?_⟩
  obtain ⟨a, -, ha⟩ := exists_ev G hG σ
  obtain ⟨b, -, hb⟩ := exists_ev G₀ hG₀ σ
  have e : a = x / y * b := by
    have := B σ a b ha hb
    field_simp
    linear_combination this
  have ea := ha z J hJ
  have eb := hb z J hJ
  rw [hm] at ea
  rw [hob', hob] at eb
  rw [ea, eb, e, Units.val_mul, Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, cst_eq, cst_eq,
    map_mul]
  have := Units.inv_mul (val G₀ (TWM.ιS hϖ hv).left z J ^ (k * 4))
  show _ = cstH z (x / y) * _ * _ * _
  linear_combination (-(cstH z (x / y) * cstH z b * (val G (TWM.ιS hϖ hv).left z J ^ (k * 4)).val)) * this

end GlobalTheory.UT.SmallPoint
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

theorem le_of_sumV_sub {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f g : Ix → F}
    (h : SumV v (fun i => f i - g i) 0) (i₀ i₁ : Ix) (q : ℚ) (hf : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i))
    (hg : ∀ i, i ≠ i₁ → (q : WithTop ℚ) ≤ v (g i)) : (q : WithTop ℚ) ≤ v (f i₀ - g i₁) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ (insert i₁ S)) ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  have m₀ : i₀ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_self _ _
  have m₁ : i₁ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₀, f i) :=
    v.map_le_sum fun i hi => hf i (Finset.ne_of_mem_erase hi)
  have h₃ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₁, g i) :=
    v.map_le_sum fun i hi => hg i (Finset.ne_of_mem_erase hi)
  rw [Finset.sum_sub_distrib, ← Finset.add_sum_erase _ f m₀, ← Finset.add_sum_erase _ g m₁, zero_sub,
    v.map_neg] at h₁
  have := v.map_le_add (v.map_le_sub h₁ h₂) h₃
  convert this using 2
  ring

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have hdb : d.b = 1 := SmallPoint.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have K := GlobalTheory.UT.gt_onto_divisible_kernel hL V (maximalIdeal V) hA D F
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  have hlow : ∀ m, -(Q m : ℚ) ≤ l' m := fun m => hll m ▸ (abs_le.1 (hlQ m)).1
  obtain ⟨t, ht, -⟩ := K.2.2.2.1 d hdb
  have hto : IsTor 1 o := ⟨hob, fun χ z J hJ => by
    rw [((isZero_iff o).1 ho).2 χ z J hJ, MonoidHom.one_apply, Units.val_one, Units.val_one, cst_eq, map_one]⟩
  have hadd : o.IsAdd d d := (K.2.2.2.2 1 t o d d hto ht).2 (by rwa [_root_.one_mul])
  have hQ0 : ∀ m, (0 : ℚ) ≤ Q m := fun m => (abs_nonneg _).trans (hlQ m)
  have A : ∀ (κ₀ : D.toPre.X) (n j : ℕ), 4 ≤ n → j = k * n →
      (((j : ℚ) - 1 - 2 * Q κ₀ : ℚ) : WithTop ℚ) ≤ v ((t (Multiplicative.ofAdd κ₀)).val - 1) := by
    intro κ₀ n j hn hj
    have hj4 : 4 ≤ j := hj ▸ le_trans hn (Nat.le_mul_of_pos_left _ hk)
    have hj1 : 1 ≤ j := by omega
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    have hj1' : (1 : ℚ) ≤ j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w', hw'⟩ := (coef_basic V D.toPre F j d).2.1 hdb
    obtain ⟨w, hw, Hw⟩ := H n j (by omega) hj w₁ hw₁
    obtain ⟨c, hc0, vc, ec⟩ := ((coef_basic V D.toPre F j d).2.2 w' hw'.1).2.2.1 w hw
    have et := ((coef_basic V D.toPre F j o).2.2 w₁ hw₁.1).2.2.2 t d d w' ht hadd
      (fun z J hJ => (hw'.2 z J hJ).trans (hw₁.2 z J hJ).symm)
    obtain ⟨ω, hcω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
    have hω : GenV hϖ hv w ω := by
      obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, e⟩ := (I d).2.2.1 j w' hw' hdb
      refine ⟨φ₀, hφ, t₀, ht₀, c * x, by rw [v.map_mul, hx, ← hcω]; simp, fun z J hJ => ?_⟩
      rw [vc z J hJ, e z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]
    have hω₁ := (I o).2.2.1 j w₁ hw₁ hob
    obtain ⟨S₁, n₁, -, e₁⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ κ₀
    obtain ⟨S₂, n₂, z₂, e₂⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ 0
    rw [Pi.zero_apply, add_zero, add_zero] at e₁ e₂
    rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at e₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have hQs : ∀ mu, (Q κ₀ : ℚ) / j + j * Q mu - Q mu - Q κ₀ ≤ (Q (κ₀ + j • mu) : ℚ) / j := fun mu => by
      have h0 := hQ0 (mu + κ₀)
      have : (Q (κ₀ + j • mu) : ℚ) / j = Q κ₀ / j + j * Q mu + (Q (mu + κ₀) - Q mu - Q κ₀) := by
        rw [q_shift hϖ hQ, QForm.bOf]; push_cast; field_simp; ring
      linarith
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ χ) := fun S hS χ => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) hω₁ hS χ
      rwa [Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j + l' χ + ω : ℚ) : WithTop ℚ) ≤ v (coef S d w χ) := fun S hS χ => by
      have := ((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS χ
      rwa [zero_add] at this
    have hQ1 : ∀ mu : D.toPre.X, mu ≠ 0 → (1 : ℚ) ≤ Q mu := fun mu h => by
      exact_mod_cast QForm.Q_pos hϖ D hQ h
    have z₂' : ∀ (g : GtPtF D.toPre F) (u : Frm D.toPre F j g.b) (χ), (¬ ∃ mu, χ = j • mu) → coef S₂ g u χ = 0 :=
      fun g u χ e => coef_zero S₂ g u (z₂ χ fun mu h => e ⟨mu, by rw [h, zero_add]⟩)
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 1 fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          refine le_trans (WithTop.coe_le_coe.2 ?_) (bo S₂ n₂ _)
          have := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [hQj]
          nlinarith
        · rw [z₂' o w₁ χ e, v.map_zero]; exact le_top
      rw [e₂, WithTop.coe_le_coe] at this
      linarith
    have key := le_of_sumV_sub (Hw S₁ S₂ hne κ₀) κ₀ 0 (ω + (Q κ₀ : ℚ) / j + ((j : ℚ) - 1 - 2 * Q κ₀))
      (fun χ hχ => by
        by_cases e : ∃ mu, κ₀ - χ = j • mu
        · obtain ⟨mu, e⟩ := e
          obtain rfl : χ = κ₀ + j • (-mu) := by rw [smul_neg, ← e]; abel
          have h1 := hQ1 (-mu) fun e => hχ (by rw [e, smul_zero, add_zero])
          rw [v.map_mul, e]
          refine le_trans ?_ (add_le_add (bd S₁ n₁ _) (bo S₂ n₂ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, ← QForm.Q_neg hϖ D hQ mu, map_add, map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          have h3 := hlow κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow (-mu)) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' o w₁ _ e, MulZeroClass.mul_zero, v.map_zero]; exact le_top)
      (fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          have h1 := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [v.map_mul, sub_eq_add_neg κ₀, ← smul_neg]
          refine le_trans ?_ (add_le_add (bd S₂ n₂ _) (bo S₁ n₁ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          rw [QForm.Q_neg hϖ D hQ mu] at h2
          have h3 := hQ0 κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow mu) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' d w _ e, MulZeroClass.zero_mul, v.map_zero]; exact le_top)
    rw [sub_self, sub_zero, ec, ec, et, et, ofAdd_zero, map_one, Units.val_one,
      show c * ((t (Multiplicative.ofAdd κ₀)).val * coef S₁ o w₁ κ₀) * coef S₂ o w₁ 0 -
        c * (1 * coef S₂ o w₁ 0) * coef S₁ o w₁ κ₀ =
        c * coef S₁ o w₁ κ₀ * coef S₂ o w₁ 0 * ((t (Multiplicative.ofAdd κ₀)).val - 1) by ring,
      v.map_mul, v.map_mul, v.map_mul, ← hcω, e₁, e₂, ← WithTop.coe_add, ← WithTop.coe_add, add_zero,
      WithTop.coe_add (ω + (Q κ₀ : ℚ) / j)] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have B : ∀ κ₀, (t (Multiplicative.ofAdd κ₀)).val = 1 := fun κ₀ => by
    by_contra hx
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (sub_ne_zero.2 hx))
    obtain ⟨n, hn⟩ := exists_nat_gt (q + 1 + 2 * Q κ₀)
    have e := A κ₀ (n + 4) _ (by omega) rfl
    rw [← hq, WithTop.coe_le_coe] at e
    have : ((n + 4 : ℕ) : ℚ) ≤ ((k * (n + 4) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hk
    push_cast at this e
    linarith
  refine (isZero_iff d).2 ⟨hdb, fun χ z J hJ => Units.ext ?_⟩
  rw [ht.2 χ z J hJ, B, cst_eq, map_one, Units.val_one]

end GlobalTheory.UT.SmallZero
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  first | exact @GlobalTheory.UT.SmallZero.main | exact GlobalTheory.UT.SmallZero.main | (intros; apply GlobalTheory.UT.SmallZero.main <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic

attribute [local instance] gtGroup

theorem eq_zero_of_sumV_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {c : F}
    (h : SumV v (0 : Ix → F) c) : c = 0 := by
  by_contra hc
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (mt (AddValuation.top_iff v).1 hc)
  obtain ⟨S, hS⟩ := h (r + 1)
  have := hS S le_rfl
  simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero, ← hr, WithTop.coe_le_coe] at this
  linarith

theorem sumV_equiv {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix Ix' : Type} (e : Ix ≃ Ix') {x : Ix → F}
    {x' : Ix' → F} (hx : ∀ i, x i = x' (e i)) {c : F} (h : SumV v x c) : SumV v x' c := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.symm.toEmbedding) fun i hi => Finset.mem_map.2
    ⟨e i, hT (Finset.mem_map.2 ⟨i, hi, rfl⟩), e.symm_apply_apply i⟩
  rw [Finset.sum_map] at this
  simpa only [hx, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using this

theorem sumV_shift {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type} [AddCommGroup X] (h : X →+ X)
    (y y' : X) {B₁ B₂ C₁ C₂ b₁ b₂ c₁ c₂ : X → F} (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0) (α : X) :
    SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_rigT (ρ : LB.Gen (A.L.pull (eSec A.A))) (k : ℤ) {z : (TFK (R := R) F).left} {J} (hJ : Good A.L z J) :
    val (rigT A.A A.L ρ (TFK (R := R) F) k) (𝟙 _) z J =
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _ ≫ (TFK (R := R) F).hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => (TFK (R := R) F).hom ≫ eSec A.A) (𝟙 _)
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hm _).trans ?_))
  exact gm_pull (𝟙 _) (TFK (R := R) F).hom z _ (rigT_le A.A A.L _ hm) _

theorem exists_value {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {k : ℕ} (t : SecA A F k) :
    ∃ c : F, ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) *
        (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val :)
  refine ⟨c, fun z' J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z z'
  have a₁ := sval_tr (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t
    (ptSecT A.A 1).left hJ hJ'
  have a₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) hρ
    (𝟙 _ ≫ (TFK (R := R) F).hom) hJ hJ'
  have e : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (𝟙 _ ≫ (TFK (R := R) F).hom) ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd, Category.id_comp]; rfl
  rw [Fin.prod_univ_one, e] at a₁
  rw [Fintype.prod_unique, zpow_one] at a₂
  have hc' : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) = sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val := (cst_eq z c).trans hc
  rw [hc', val_rigT ρ k hJ, val_rigT ρ k hJ', a₂, mul_zpow, Units.val_mul, mul_comm (Units.val (_ ^ _)),
    ← _root_.mul_assoc, Units.inv_mul_cancel_right, mul_comm]
  exact a₁

theorem exists_act_pre (hG : GlobalFnsSt) {k : ℕ} (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (T : SecA A F k) :
    ∃ t : SecA A F k, IsActOf A.A A.L (k : ℤ) θ t T := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  exact ⟨SecM.toSec A.A ((ρ θ).symm (SecM.ofSec A.A T)), (hρ _ _ _).2 ((ρ θ).apply_symm_apply _)⟩

theorem act_zero {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} (E : EndU U) {o : GtPtF D.toPre F} (ho : o.IsZero) : E.Act o o := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  have := E.homB
  refine ⟨by rw [hb, MonObj.one_comp], fun χ z J hJ => ?_⟩
  have a := val_corr hJ (E.u_norm χ).2 (TF (R := R) F).hom
  rw [val_pull hJ, val_one] at a
  rw [hv _ z J hJ, hv _ z J hJ, hb, _root_.one_mul]
  exact a.symm

end

theorem exists_pre_coef (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {j : ℕ} (hj : 1 ≤ j) (q : QkPt D.toPre F j) {x : TFK (R := R) F ⟶ A.A}
    (hx : QkToAkU U.toUnifPre F j q x) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {g₀ g₁ : GtPtF D.toPre F}
    (hg : g₀.IsAdd q.g g₁) {ω₀ : Frm D.toPre F j g₀.b} (hω₀ : ω₀.IsGen) :
    ∃ θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F), θ.pt = x ∧ ∃ ω₁ : Frm D.toPre F j g₁.b, ω₁.IsGen ∧
      ∀ T S, U.ExpandsF F j w₀ T S → ∃ t s, IsActOf A.A A.L (j : ℤ) θ t T ∧ U.ExpandsF F j w₀ t s ∧
        ∀ α, coef S g₀ ω₀ (α + q.y) = coef s g₁ ω₁ α := by
  obtain ⟨hp, hθ⟩ := hx w₀ hw₀
  obtain ⟨θ, e, -⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.1.kerPow _ A F (jFK (R := R) F) j hj x hp
  obtain ⟨w, hw, H⟩ := hθ θ e
  obtain ⟨ω₁, hω₁, -, K⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL R I hA D F j hj q w hw g₀ g₁ hg ω₀ hω₀
  refine ⟨θ, e, ω₁, hω₁, fun T S hT => ?_⟩
  obtain ⟨t, ht⟩ := exists_act_pre hL.1.globalFns θ T
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F j hj w₀ hw₀).1 t
  exact ⟨t, s, ht, hs, K 1 j le_rfl (Nat.mul_one j).symm q (one_nsmul _).symm rfl w ω₀ ω₁
    ⟨hw, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₀, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩
    s S (H t T s S hs hT ht)⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E hE k hk p x hx g' hg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hB := D.tau_bimult
  have := E.homA
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv
  have EV := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D A G hG U F
  have LU := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F
  have MX := GlobalTheory.T.crossRelation_gives_convolution_relation hL V _ hA D A G hG U F E
  have BJ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨ρ, hρ⟩ := EV.1
  obtain ⟨w₀, hN⟩ := EV.2.1 ρ hρ
  have hw₀ := hN.1
  have hxk : x ^ k = 1 := (hx w₀ hw₀).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ E.aA) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D.toPre.X Q (QForm.bHom hϖ D hQ)
    (fun a b => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D hQ)
    (fun a ha => QForm.Q_pos hϖ D hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add, map_nsmul])
  have hp₁ : QkToAkU U.toUnifPre F k p₁ (x ≫ E.aA) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D.toPre F) (a b : D.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b := fun g a b ha hb =>
    (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up : ∀ (r : QkPt D.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG U hj1 q₁ (((LU k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀
    (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ j hj1 w₀ hw₀).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ j hj1 w₀ hw₀).2 S₂
  obtain ⟨n', hn', CR⟩ := GlobalTheory.PullPair.exists_cross hL V A F E.aA E.homA j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ _ hj' w₀ hw₀).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ _ hj' w₀ hw₀).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG U hj' q (((LU k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.cross_iff_of_isActOf hL V A F E.aA E.homA j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl : ∀ (g : GtPtF D.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D.toPre F i g.b) (s : Fam D.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  refine GlobalTheory.UT.sumV_cancel F v D.toPre.X E.h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw)
    (nl _ _ hj1 _ _ hw) (nl _ _ hj' _ _ hw₁'.1) (nl _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero E ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift v E.h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨c, hc⟩ := exists_value hρ T₂
  obtain ⟨c', hc'⟩ := exists_value hρ T₂'
  have σ := (SV _ _ _ (EV.2.2 w₀ ρ hN j T₂ S₂ hT₂ 0 w₁ ho hw₁ c hc)).1
  have σ' := (SV _ _ _ (EV.2.2 w₀ ρ hN _ T₂' S₂' hT₂' 0 w₁' ho hw₁' c' hc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hc' y J hJ).trans ?_)
  · have e : cstH (R := V) y c = 0 :=
      (cst_eq y c).symm.trans ((Units.mul_left_eq_zero _).1 ((hc y J hJ).symm.trans h))
    obtain rfl : c = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.UT.EndTors
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_endomorphism_image_eq_moved_gtPoint : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  first | exact @GlobalTheory.UT.EndTors.main | exact GlobalTheory.UT.EndTors.main | (intros; apply GlobalTheory.UT.EndTors.main <;> assumption)
end
