import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombBijective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecRelationDefect
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProdExpOppositeTranslates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultiple

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.UU

theorem finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by
  classical
  have h1 : ∑ i ∈ s, f i = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have h2 : ∑ i ∈ s', g i = ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) := by
    rw [Finset.sum_map]; simp
  have h3 : ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, g (σ i) :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg _ (fun hm => hi (by
      rw [Finset.mem_map]; exact ⟨σ i, hm, by simp⟩)))
  rw [h1, h2, h3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem adicSum_rel : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y Y₂ : Over (Spec (CommRingCat.of R))) (τ : Y ⟶ Y₂) (X : Scheme.{0}) (L : LB X) (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂.left ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y.left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y.left ⟶ X)) (εu : K'' → ℤ) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y.left, ⊤)) (Ix Ix' : Type) (σ : Ix ≃ Ix') (p : Ix → LB.Sec (LB.LinComb L φ ε)) (p' : Ix' → LB.Sec (LB.LinComb L φ' ε')) (S S'), AdicSum I p S → AdicSum I p' S' → (∀ i (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J → gs r z ⊤ c' * sval (p' (σ i)) r z J = gs r z ⊤ c * (sval (p i) (r ≫ τ.left) z J * (val u r z J).val)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval S' r z J = gs r z ⊤ c * (sval S (r ≫ τ.left) z J * (val u r z J).val) := by
  intro R _ I Y Y₂ τ X L K K' K'' _ _ _ φ ε φ' ε' φu εu u c c' Ix Ix' σ p p' S S' hS hS' h e Z r hr z J hJ
  obtain ⟨s, hs⟩ := hS e
  obtain ⟨s', hs'⟩ := hS' e
  have hr2 : Lvl I e ((r ≫ τ.left) ≫ Y₂.hom) := by
    rw [Category.assoc, Over.w τ]; exact hr
  obtain ⟨a1, a2⟩ := hs Z (r ≫ τ.left) hr2 z J hJ
  obtain ⟨b1, b2⟩ := hs' Z r hr z J hJ
  rw [a2, b2]
  exact finsum_rel σ _ _ _ _ _ s s' a1 b1 (fun i => h i Z r z J hJ)

end GlobalTheory.UU
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_mul_cubN_add {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'

theorem translationUnit_mul :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem units_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k l : ℕ) (mu β ga : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J) *
      (uVal D F l ga (cP D _ mu) r z J * val (DegPre.famMult D F l mu ga) (r ≫ fst _ _).left z J) *
      th D z J (cP D Z (β + k • mu)) (cP D Z (ga + l • mu)) (r ≫ DegPre.prB D F) =
    th D z J (cP D Z β) (cP D Z ga) ((r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F) *
      (uVal D F (k + l) (β + ga) (cP D _ mu) r z J *
        val (DegPre.famMult D F (k + l) mu (β + ga)) (r ≫ fst _ _).left z J) := by
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  have hm : r ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D Z mu := by rw [comp_cP, comp_cP]
  have hy : (r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (r ≫ DegPre.prB D F) * cP D Z mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, hm]
  have t := tau_mul (r ≫ fst (TF (R := R) F) D.P.A) hJ hB β ga mu
  rw [tau_symm _ hJ (β + ga), tau_symm _ hJ β, tau_symm _ hJ ga] at t
  have key := GlobalTheory.translationUnit_mul _ _ _ C k l (cP D Z β) (cP D Z ga) (cP D Z mu) (r ≫ DegPre.prB D F)
  rw [hy, uVal, uVal, uVal, hm, val_famMult _ hJ, val_famMult _ hJ, val_famMult _ hJ, cPoint_add, cPoint_add, cPoint_add,
    cPoint_nsmul, cPoint_nsmul]
  simp only [val_powGen, pow_add]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  have t' := congrArg Additive.ofMul t
  simp only [ofMul_mul, ofMul_inv] at key' t' ⊢
  linear_combination (norm := abel) key' - t'

theorem conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by
  rintro hG R _ _ D hB F _ _ k l s s' hs hs' mu _ β ga _ _ rfl rfl rfl u hu hc Z r z J hJ
  have e := congrArg Units.val (units_mul hB k l mu β ga Z r z J hJ)
  rw [famFE_val hG k s hs mu β Z r z J hJ, famFE_val hG l s' hs' mu ga Z r z J hJ,
    (gen_fe hG (k + l) mu (β + ga)).2 u hu hc Z r z J hJ]
  rw [Units.val_mul, Units.val_mul, Units.val_mul (th D z J _ _ _)] at e
  refine Eq.trans ?_ ((congrArg (sval (s β) (r ≫ DegPre.trF D F mu).left z J *
    sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * ·) e).trans (_root_.mul_assoc _ _ _).symm)
  rw [_root_.mul_mul_mul_comm, _root_.mul_assoc]
  rfl

end GlobalTheory.ConvTermFE
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relation_of_finite_levels : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro R _ I T B _ _ _ _ _ hI X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := sec_eq_zero_of_sval_finite_level R I T B hI X L hL K' φ' ε' d (fun e Z r hr z J hJ => by
    rw [hd Z r z J hJ, h e Z r hr z J hJ, sub_self])
  rw [← sub_eq_zero, ← hd Z r z J hJ]
  exact (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR

def cst {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c :=
  (gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _)

theorem cst_specMap {A R : Type} [CommRing A] [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (f : A →+* R) (c : A) : cst (q ≫ Spec.map (CommRingCat.ofHom f)) z c = cst q z (f c) := by
  have e := congrArg (fun t => t.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [e]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pullB_val {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α}
    {s : Raw D F k} (h : PullB D F φ k f s) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J := by
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) r z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left r z J hJ).2.1 (f α)
  have hJ' : Good D.P.L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ _
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

theorem whisker_trT {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst T D.P.A ≫ cP D T mu)).trans ?_
    rw [whiskerRight_snd, comp_cP, comp_cP]
    rfl

theorem cst_unit {r : R} (hr : r ≠ 0) (z : (DegPre.BF D F).left) : IsUnit (cst (DegPre.BF D F).hom z r) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (Category.assoc _ _ _).symm
  rw [e]
  refine (congrArg IsUnit ((cst_specMap _ z (algebraMap R (FractionRing R)) r).trans (cst_specMap _ z _ _))).mpr
    (IsUnit.map _ (IsUnit.map _ (Ne.isUnit ?_)))
  exact fun h => hr (IsFractionRing.injective R (FractionRing R) (h.trans (map_zero _).symm))

theorem form_delta {T : Over (Spec (CommRingCat.of R))} (k : ℕ) (α' α : D.X) (b : T ⟶ D.P.A) :
    FormEq (famφT D T α') (DegPre.famε k) (Sum.elim (fun i => (trT D b).left ≫ famφT D T α i) (deltaφT D α' α b))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) := fun U _ h => by
  refine Eq.symm (Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (c := ∏ i, h ((trT D b).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (c := ∏ i, h (famφT D T α' i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_)
  exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)

theorem noeth (V W : Type) [CommRing V] [IsNoetherianRing V] [CommRing W] [Algebra V W] [Module.Finite V W] :
    IsNoetherianRing Γ((TA V W).left, ⊤) := by
  haveI : IsNoetherianRing W := isNoetherian_of_tower V inferInstance
  exact isNoetherianRing_of_ringEquiv W (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm

theorem jac (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [IsLocalHom (algebraMap V W)] (r : V) (hr : r ∈ IsLocalRing.maximalIdeal V) :
    scal (TA V W).hom r ∈ Ideal.jacobson (⊥ : Ideal Γ((TA V W).left, ⊤)) := by
  let E : W ≃+* Γ((TA V W).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
  have e : scal (TA V W).hom r = E (algebraMap V W r) :=
    (congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V W)))).symm
  have hw : algebraMap V W r ∈ Ideal.jacobson (⊥ : Ideal W) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap V W) r hr
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  have := (Ideal.mem_jacobson_bot.1 hw (E.symm y)).map E
  simpa using this

theorem sval_twist {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TA R W ⊗ D.P.A).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (twist a f α) r z J =
      cst (R := W) (r ≫ (fst (TA R W) D.P.A).left) z (a (Multiplicative.ofAdd α)).val * sval (f α) r z J :=
  (sval_secScale _ _ r z hJ).trans (congrArg (· * _) (gs_scal (R := W) _ r z _))

theorem term_val {W : Type} [CommRing W] [Algebra R W] {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (a a' : Multiplicative D.X →* Wˣ) {β ga α : D.X}
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g ga) p)
    {Z : Over (Spec (CommRingCat.of R))} (r : Z ⟶ DegPre.BF D F) (z : Z.left) {J} (hJ : Good D.P.L z J) :
    sval p (r ≫ φ ▷ D.P.A).left z J =
      cst (R := W) (r ≫ fst _ _ ≫ φ).left z (a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd ga)).val *
        (sval (s β) r.left z J * sval (s' ga) r.left z J *
          (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd _ _)).val) := by
  have e : (r ≫ φ ▷ D.P.A).left ≫ (fst (TA R W) D.P.A).left = (r ≫ fst _ _ ≫ φ).left := by
    rw [← Over.comp_left, Category.assoc, whiskerRight_fst]
  rw [hp Z _ z J hJ, sval_twist a f β _ z hJ, sval_twist a' g ga _ z hJ, e, pullB_val hf β _ z hJ,
    pullB_val hg ga _ z hJ, Category.assoc, whiskerRight_snd, Units.val_mul, map_mul, Over.comp_left _ _ _ r (φ ▷ D.P.A)]
  ring

theorem term_rel (hG : GlobalFnsSt) (hB : D.TauBimult) {W : Type} [CommRing W] [Algebra R W]
    {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (hs : DegPre.FamFE D F k s) (hs' : DegPre.FamFE D F l s')
    (a a' : Multiplicative D.X →* Wˣ) (mu α β : D.X)
    (ha : a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1)
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g (α - β)) p)
    {p' : SecBT D (TA R W) (k + l) (α + (k + l) • mu)}
    (hp' : IsProdB (twist a f (β + k • mu)) (twist a' g (α + (k + l) • mu - (β + k • mu))) p')
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α))
    (z : (DegPre.BF D F).left) {J} (hJ : Good D.P.L z J) :
    sval p' (φ ▷ D.P.A).left z J =
      sval p ((φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left) z J * (val u (𝟙 _) z J).val := by
  have hγ : α + (k + l) • mu - (β + k • mu) = α - β + l • mu := by rw [add_nsmul]; abel
  have e₁ := term_val hf hg a a' hp' (𝟙 (DegPre.BF D F)) z hJ
  have e₂ := term_val hf hg a a' hp (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) z hJ
  have e₃ := ConvTermFE.conv_term_fe hG R D hB F k l s s' hs hs' mu α β (α - β) _ _ (add_sub_cancel _ _) rfl hγ u hu hc
    _ (𝟙 (DegPre.BF D F)) z J hJ
  have e₄ : (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ fst _ _ ≫ φ = 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ φ := by
    rw [Category.id_comp, Category.id_comp, DegPre.trF, lift_fst_assoc]
  have e₅ : a (Multiplicative.ofAdd (β + k • mu)) * a' (Multiplicative.ofAdd (α + (k + l) • mu - (β + k • mu))) =
      a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd (α - β)) := by
    rw [hγ, ofAdd_add, ofAdd_add, map_mul, map_mul, _root_.mul_mul_mul_comm, ha, _root_.mul_one]
  have e₆ : (φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left =
      ((𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ φ ▷ D.P.A).left := by
    rw [Category.id_comp, ← whisker_trT, Over.comp_left]
  rw [e₅, e₃, Category.id_comp (φ ▷ D.P.A)] at e₁
  rw [e₄] at e₂
  rw [e₆, e₁, e₂]
  exact (_root_.mul_assoc _ _ _).symm

theorem conv_famFE : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W), Function.Injective φ.left.appTop.hom → ∀ (k l : ℕ) (f : ∀ α, SecBT D (TA V W) k α) (g : ∀ α, SecBT D (TA V W) l α) (h : ∀ α, SecBT D (TA V W) (k + l) α) (s : Raw D F k) (s' : Raw D F l) (s'' : Raw D F (k + l)) (a a' : Multiplicative D.X →* Wˣ), (∀ mu : D.X, a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1) → PullB D F φ k f s → PullB D F φ l g s' → PullB D F φ (k + l) h s'' → DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ConvT (IsLocalRing.maximalIdeal V) (twist a f) (twist a' g) h → DegPre.FamFE D F (k + l) s'' := by
  intro hG V _ _ _ hV D hB W _ _ _ hW F _ _ φ hφ k l f g h s s' s'' a a' ha hf hg hh hs hs' hconv mu α u hu hc
  obtain ⟨u₀, r₁, r₂, hu₀, -, hr₂, hrel⟩ := GlobalTheory.UU.IntGen.main hG V D (TA V W) (k + l) α mu
  obtain ⟨p, hp, hS⟩ := hconv α
  obtain ⟨p', hp', hS'⟩ := hconv (α + (k + l) • mu)
  haveI := hV.1
  haveI := hW.1
  haveI := hW.2.2.2.1
  haveI := noeth V W
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TF (R := V) F).left := inferInstanceAs (IsAffine (Spec _))
  have hcs : ∀ (z : (DegPre.BF D F).left) (c : V),
      gs (φ ▷ D.P.A).left z ⊤ (scal (TA V W ⊗ D.P.A).hom c) = cst (DegPre.BF D F).hom z c := fun z c => by
    rw [gs_scal, Over.w]
  have hu' : ∀ (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
      cst (DegPre.BF D F).hom z r₂ * (val u (𝟙 _) z J).val =
        cst (DegPre.BF D F).hom z r₁ * (val u₀ (φ ▷ D.P.A).left z J).val := fun z J hJ => by
    have := hrel F φ u hu hc _ (𝟙 _) z J hJ
    rwa [gs_scal, gs_scal, Category.id_comp, Category.id_comp] at this
  have H := relation_of_finite_levels V (IsLocalRing.maximalIdeal V) (TA V W) D.P.A (jac V W) _ _ D.P.L D.P.isLB _ _ _
    _ _ _ _ _ _ (trT D (toUnit _ ≫ D.c mu)).left (h α) (h (α + (k + l) • mu)) u₀ (scal (TA V W ⊗ D.P.A).hom r₁)
    (scal (TA V W ⊗ D.P.A).hom r₂) hu₀ (form_delta _ _ _ _)
    (adicSum_rel V (IsLocalRing.maximalIdeal V) _ _ (trT D (toUnit _ ≫ D.c mu)) _ D.P.L _ _ _ _ _ _ _ _ _ u₀ _ _ _ _
      (Equiv.addRight (k • mu)) p p' _ _ hS hS' fun β =>
      sec_relation_descends _ D.P.A (TA V W) (TF (R := V) F) φ hφ _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ _ (p β)
        (p' (β + k • mu)) u₀ _ _ hu₀ (form_delta _ _ _ _) fun z J hJ => by
          rw [hcs, hcs, term_rel hG hB hf hg hs hs' a a' mu α β (ha mu) (hp β) (hp' _) u hu hc z hJ, mul_left_comm,
            hu' z J hJ, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun z J hJ => ?_
  have e := H _ (φ ▷ D.P.A).left z J hJ
  rw [hcs, hcs, mul_left_comm, ← hu' z J hJ, mul_left_comm, ← Over.comp_left, whisker_trT, Over.comp_left] at e
  rw [pullB_val hh _ _ z hJ, pullB_val hh _ _ z hJ, Category.id_comp, Category.id_comp]
  exact (cst_unit hr₂ z).mul_left_cancel e

end GlobalTheory.ConvFE
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntWit

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs
  · simp only [map_zero]
  · rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (gs_zero r z _)

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) :
    s.f j = 0 := by
  refine fn_ext (V := LB.wchart L φ j) fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem integral_witness : AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X), U.FE F k → U.Supp F k β → ∃ (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f ∧ PullB D F (toUnit _) k f s ∧ DegPre.FamFE D F k s ∧ (∃ j, (s β).f j ≠ 0) ∧ ∃ j, (f β).f j ≠ 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k β hFE hS
  obtain ⟨t, s, ⟨n, c, σ, f, hE, -, hB⟩, j₀, hj₀⟩ := hS
  obtain ⟨hG, hP⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U F (𝟙_ _) (toUnit _) k
  choose s' hs' using fun i => (hP (f i)).exists
  have hex : ∃ i, ∃ j, (s' i β).f j ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hj₀ (eq_zero_of_sval D.P.isLB (s β) (fun y J hJ => ?_) j₀)
    have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
    refine (hB β _ (𝟙 _) (toUnit (TF (R := V) F) ▷ D.P.A).left (w.trans (Category.id_comp _).symm) y J hJ).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (_ * ·) ((hs' i β y J hJ).symm.trans (sval_eq_zero _ (hn i) _ _ _))).trans (mul_zero _)
  obtain ⟨i, j, hj⟩ := hex
  obtain ⟨t', ht'⟩ := (hG (σ i)).exists
  refine ⟨σ i, f i, s' i, hE i, hs' i,
    hFE t' (s' i) (IntExp.expF_of_expT V _ D A G U F k (σ i) (f i) t' (s' i) (hE i) ht' (hs' i)), ⟨j, hj⟩, ?_⟩
  by_contra hn
  push Not at hn
  exact hj (eq_zero_of_sval D.P.isLB (s' i β)
    (fun y J hJ => (hs' i β y J hJ).trans (sval_eq_zero _ hn _ _ _)) j)

end GlobalTheory.UU.IntWit
end
end

section
namespace GlobalTheory

theorem coeff_eq_zero_of_sum_smul_eq_zero_of_separating {Y A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (P : (Y → A) → Prop) (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (s : Finset Y)
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → ∃ t, P t ∧ IsUnit (t y - t z))
    (a : Y → M) (h : ∀ t, P t → ∑ y ∈ s, t y • a y = 0) : ∀ y ∈ s, a y = 0 := by
  classical
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    intro y₀ hy₀
    by_cases hz : ∃ z ∈ s, z ≠ y₀
    · obtain ⟨z, hzs, hzy⟩ := hz
      obtain ⟨u, hu, hunit⟩ := hsep y₀ hy₀ z hzs (Ne.symm hzy)

      set b : Y → M := fun y => (u y - u z) • a y with hb
      have hbrel : ∀ t, P t → ∑ y ∈ s.erase z, t y • b y = 0 := by
        intro t ht
        rw [Finset.sum_erase s (by simp [hb])]
        have e : ∀ y, t y • b y = (t * u) y • a y - u z • (t y • a y) := by
          intro y
          simp only [hb, Pi.mul_apply, smul_smul, ← sub_smul]
          congr 1
          ring
        simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, h t ht, h (t * u) (hmul t u ht hu),
          smul_zero, sub_zero]
      have hsub : s.erase z ⊂ s := Finset.erase_ssubset hzs
      have key := ih (s.erase z) hsub
        (fun y hy w hw hne => hsep y (Finset.mem_of_mem_erase hy) w (Finset.mem_of_mem_erase hw) hne)
        b hbrel y₀ (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy₀⟩)
      exact (hunit.smul_eq_zero).mp key
    · push Not at hz
      have := h 1 h1
      rw [Finset.sum_eq_single_of_mem y₀ hy₀ (fun z hz' hne => absurd (hz z hz') hne)] at this
      simpa using this

theorem laurent_coeff_eq_zero_of_vanish_torsion :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by
  intro Y _ _ _ n hn s
  let b := Module.Free.chooseBasis ℤ Y

  refine ⟨∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs, ?_⟩
  intro j hj A _ _ ζ _ hζ hprim M _ _ a ha
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  let u : Aˣ := Units.ofPowEqOne ζ (n ^ j) hζ hN
  have hu : u ^ (n ^ j) = 1 := Units.pow_ofPowEqOne hζ hN

  let χ : _ → Multiplicative Y →* Aˣ := fun i =>
    (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hχ : ∀ i y, χ i (Multiplicative.ofAdd y) = u ^ (b.repr y i) := by
    intro i y
    simp [χ, zpowersHom]
  have hχord : ∀ i y, χ i y ^ (n ^ j) = 1 := by
    intro i y
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hχ, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  let P : (Y → A) → Prop := fun f =>
    ∃ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) ∧ f = fun y => (t (Multiplicative.ofAdd y) : A)
  refine coeff_eq_zero_of_sum_smul_eq_zero_of_separating P ⟨1, fun _ => one_pow _, by funext; simp⟩
    ?_ s ?_ a ?_
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', fun y => by rw [MonoidHom.mul_apply, mul_pow, ht, ht', one_mul],
      by funext y; simp⟩
  · intro y hy z hz hyz
    have hw : b.repr (y - z) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact sub_ne_zero.mpr hyz
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hw
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    refine ⟨_, ⟨χ i, hχord i, rfl⟩, ?_⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hχ, hχ, map_sub]
    let v : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom u
    have hv : IsPrimitiveRoot v (n ^ j) := IsPrimitiveRoot.coe_units_iff.mp (by simpa [v, u] using hprim)
    have hres : ∀ k : ℤ, IsLocalRing.residue A ((u ^ k : Aˣ) : A) = ((v ^ k : _ˣ) : _) := by
      intro k
      rw [show v ^ k = Units.map (IsLocalRing.residue A).toMonoidHom (u ^ k) from (map_zpow _ u k).symm]
      rfl
    rw [hres, hres, sub_ne_zero, Ne, Units.val_inj, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, ← Finsupp.sub_apply,
      ← map_sub, hv.zpow_eq_one_iff_dvd]
    intro hdvd
    apply hi
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have h1 : (b.repr (y - z) i).natAbs ≤ ∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : Y × Y => ∑ i, (b.repr (p.1 - p.2) i).natAbs)
        (fun _ _ => Nat.zero_le _) (show (y, z) ∈ s ×ˢ s from Finset.mem_product.mpr ⟨hy, hz⟩))
      exact Finset.single_le_sum (f := fun i => (b.repr (y - z) i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j < n ^ j := Nat.lt_pow_self hn.one_lt
    simp only [Int.natAbs_natCast]
    omega
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPrimitiveRoot_residue_of_isUnit {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]
    {ζ : W} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : W)) :
    IsPrimitiveRoot (IsLocalRing.residue W ζ) N := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
  by_contra hne
  have h1 : (ζ ^ l) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : ∑ i ∈ Finset.range N, (ζ ^ l) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ l) N
    rw [h1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (IsLocalRing.residue W) h2
  simp only [map_sum, map_pow, hl, one_pow, map_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h3
  have h4 := hN.map (IsLocalRing.residue W)
  rw [map_natCast] at h4
  exact h4.ne_zero (by simpa using h3)

theorem exists_finite_extension_primitive_residue :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V], (∃ n : ℕ, n.Prime ∧ IsUnit (n : V)) ∧ ∀ (n j : ℕ), n.Prime → IsUnit (n : V) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (ζ : W), (Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) ∧ Function.Injective φ.left.appTop.hom ∧ IsUnit (n : W) ∧ ζ ^ (n ^ j) = 1 ∧ IsPrimitiveRoot (IsLocalRing.residue W ζ) (n ^ j) := by
  intro V _ _ _ _ _
  refine ⟨?_, fun n j hn hu => ?_⟩
  · have h : IsUnit ((3 : V) + -2) := by norm_num
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact ⟨3, Nat.prime_three, by exact_mod_cast h⟩
    · exact ⟨2, Nat.prime_two, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  · let F := AlgebraicClosure (FractionRing V)
    have hpos : 0 < n ^ j := pow_pos hn.pos j
    have : NeZero (n ^ j) := ⟨hpos.ne'⟩
    have : NeZero ((n ^ j : ℕ) : F) := inferInstance
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (n ^ j)
    let W : Subalgebra V F := Algebra.adjoin V {z}
    have hzW : z ∈ W := Algebra.subset_adjoin rfl
    have hfin : Module.Finite V W :=
      Algebra.finite_adjoin_simple_of_isIntegral
        ⟨Polynomial.X ^ (n ^ j) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hpos.ne', by
          simp [hz.pow_eq_one]⟩
    have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun x y h =>
      IsFractionRing.injective V (FractionRing V) ((algebraMap (FractionRing V) F).injective
        (congrArg Subtype.val h))
    have hfree : Module.Free V W := Module.free_of_finite_type_torsion_free'
    have hW : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
    have hloc : IsLocalHom (algebraMap V W) := inferInstance
    have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
    have hζ : IsPrimitiveRoot (⟨z, hzW⟩ : W) (n ^ j) :=
      IsPrimitiveRoot.of_map_of_injective (f := W.val) hz Subtype.val_injective
    have hnW : IsUnit (n : W) := by simpa using hu.map (algebraMap V W)
    refine ⟨W, inferInstance, inferInstance, inferInstance,
      Over.homMk (Spec.map (CommRingCat.ofHom W.val.toRingHom)) ?_, ⟨z, hzW⟩,
      ⟨hfin, hfree, inferInstance, hloc, hc⟩, ?_, hnW, hζ.pow_eq_one,
      isPrimitiveRoot_residue_of_isUnit hζ (by exact_mod_cast hnW.pow j)⟩
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    · change Function.Injective (Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop.hom
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom W.val.toRingHom)
      have hi : Function.Injective ((Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop ≫
          (Scheme.ΓSpecIso _).hom).hom := by
        rw [h, CommRingCat.hom_comp, RingHom.coe_comp]
        exact Subtype.val_injective.comp (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hi
      exact hi.of_comp

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem levelff_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  have hl : IsLocalHom (f.stalkMap x).hom := inferInstance
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem levelff_gs_comp {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm

theorem sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R W _ _ _ _ I e Y X L hL K _ φ ε d H Z r hρ z J hJ
  let g : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hg : Flat g ∧ Surjective g := by
    refine (flat_and_surjective_SpecMap_iff _).2 ?_
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := hg
  let p : pullback (r ≫ Y.hom) g ⟶ Z := pullback.fst _ _
  have : Flat p := inferInstance
  have : Surjective p := inferInstance
  obtain ⟨z', rfl⟩ := p.surjective z
  obtain ⟨ρ, hρ⟩ := hρ
  choose J' hJ' using fun χ : pullback (r ≫ Y.hom) g ⟶ X => exists_chart hL (χ z')
  have h0 := H _ (p ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition.symm)
    ⟨p ≫ ρ, by rw [Category.assoc, hρ, Category.assoc]⟩ z' J' hJ'
  have hm : r (p z') ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have h1 := sec_trans d (p ≫ r) z' (j := fun k => J (r ≫ φ k)) hm (Good.mem hJ' φ (p ≫ r))
  have h2 : gs (p ≫ r) z' (LB.wchart L φ (fun k => J (r ≫ φ k))) (d.f (fun k => J (r ≫ φ k))) = 0 :=
    h1.trans ((congrArg _ h0).trans (mul_zero _))
  apply levelff_stalkMap_injective p z'
  rw [map_zero]
  exact (levelff_gs_comp p r z' _ hm _).symm.trans h2

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.NullExp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα

end GlobalTheory.NullExp
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.TorPtEx

theorem exists_gtPt {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (a : Multiplicative D.X →* Γ(T.left, ⊤)ˣ) : ∃ g : GtPt D T, g.b = 1 ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val (g.s χ) r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
  have h1 : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T 1 χ) DegPre.gtε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T 1 χ) (ε' := DegPre.gtε) (fun U _ h => by
        have e₁ : padd D.P.A (DegPre.cT D T χ) 1 = DegPre.cT D T χ := _root_.mul_one (DegPre.cT D T χ)
        have e₂ : DegPre.zeroT D T = 1 := rfl
        simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_succ, e₁, e₂])
      (DVR.scaleGen (a (Multiplicative.ofAdd χ)) (LB.oneGen D.P.L)) (DVR.scaleGen_isGen _ _ h1)
    refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem PEmpty.elim r) _) (val_one r))).trans
      (_root_.mul_one _)
  choose s hs hv using key
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, val_one, ofAdd_zero, map_one, map_one]
  · have c := (val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1).trans
      ((congrArg (cubV D.cub y J _ _) (Category.id_comp (1 : T ⟶ D.P.A))).trans ((isCub_cubV D.cub hJ).face₃ _ _))
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) c)).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ))).symm)
    rw [_root_.mul_one, ofAdd_add, map_mul, map_mul]; rfl

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ a : Multiplicative D.X →* Wˣ, ∃ x : TA V W ⟶ G, U.TorPt a x := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW a
  obtain ⟨g, hb, hv⟩ := exists_gtPt D (TA V W)
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom).comp a)
  obtain ⟨x, hx, -⟩ := RedOnto.main V hV D A G U W hW g
  refine ⟨x, fun e Z r xe h => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx e Z r xe h
  refine ⟨hb ▸ h₁, fun χ z J hJ => ?_⟩
  rw [h₂ χ z J hJ, hv χ Z r z J hJ, gm_val r z ⊤ trivial, gs_eq _ z ⊤ trivial]
  rfl

end GlobalTheory.UU.TorPtEx

end
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.FESection

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB k hk hF1 hFk ⟨β₁, hβ₁⟩ ⟨β₀, hβ₀⟩ α
  have hG := hL.globalFns
  obtain ⟨σ, f, sf, hσ, hpf, hfef, -, hf0⟩ := IntWit.integral_witness V hV D A G U (Kbar V) k β₀ hFk hβ₀
  obtain ⟨ϑ, g, sg, hϑ, hpg, hfeg, ⟨j₁, hs1⟩, -⟩ := IntWit.integral_witness V hV D A G U (Kbar V) 1 β₁ hF1 hβ₁
  have hg0 : ∃ j, (g (α - β₀)).f j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have h1 : ∀ j, (sg (α - β₀)).f j = 0 := fun j =>
      sec_ext_val (s' := DVR.SecOps.secZero) D.P.isLB (fun y J hJ => by
        rw [hpg _ y J hJ, DVR.UUA.sval_zero_of hn _ y J (hJ.mem _ _),
          DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]) j
    exact hs1 (FamFree.zero_of_eq_add_nsmul hG (⟨sg, hfeg⟩ : Fam D (Kbar V) 1)
      ⟨β₁ - (α - β₀), by rw [one_smul, add_sub_cancel]⟩ h1 j₁)
  obtain ⟨W, _, _, _, φ, a, hW, hφ, hnv⟩ := GlobalTheory.UU.exists_twist_conv_ne_zero V hV D k f g α β₀
    (GlobalTheory.NullExp.main V _ D A G U _ k σ f hσ) hf0 hg0
  obtain ⟨σ', f', hσ', hff, hpf'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) k σ f hσ
  obtain ⟨ϑ', g', hϑ', hgg, hpg'⟩ := expT_pull V _ D A G U _ (TA V W) (toUnit _) 1 ϑ g hϑ
  have hu : φ ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  obtain ⟨x, hx⟩ := TorPtEx.main V hV D A G U W hW a
  obtain ⟨σ'', hprod⟩ := GlobalTheory.UU.prodExp_opposite_translates hG V hV D A G U W hW a x hx k σ' ϑ' f' g' hσ' hϑ'
  obtain ⟨h, hh, hext⟩ := GlobalTheory.UU.ExpExt.main hL hL2 V hV D A G U W hW (k + 1) (by omega) σ''
  have hconv := GlobalTheory.ConvOfProd.main V _ D A G U _ k 1 _ _ h σ'' hprod hh
  obtain ⟨ht, hs⟩ := PullSec.pullEx V hV D A G U (Kbar V) (TA V W) φ (k + 1)
  obtain ⟨t, ht, -⟩ := ht σ''
  obtain ⟨s, hs, -⟩ := hs h
  refine ⟨t, s, hext _ φ t s ht hs, ?_, ?_⟩
  · refine GlobalTheory.ConvFE.conv_famFE hG V hV D hB W hW (Kbar V) φ hφ k 1 f' g' h sf sg s a (a ^ k)⁻¹ (fun mu => ?_)
      ((hpf' _ φ sf).2 (hu ▸ hpf)) ((hpg' _ φ sg).2 (hu ▸ hpg)) hs hfef hfeg hconv
    rw [one_smul, ofAdd_nsmul, map_pow, MonoidHom.inv_apply, MonoidHom.pow_apply, mul_inv_cancel]
  · obtain ⟨j, hj⟩ := hnv f' g' h hff hgg hconv
    by_contra hn
    push_neg at hn
    haveI := D.P.isAb.smooth
    haveI : Flat D.P.A.hom := inferInstance
    haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
    haveI : IsAffine (TF (R := V) (Kbar V)).left := inferInstanceAs (IsAffine (Spec _))
    refine hj (sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A _ _ φ hφ _ D.P.L D.P.isLB _ _ _ (h α)
      (fun z J hJ => ?_) j)
    exact (hs α z J hJ).symm.trans (DVR.UUA.sval_zero_of hn _ z J (hJ.mem _ _))

end GlobalTheory.UU.FESection
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionalEquation_section_nonzero_class : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  atlas_forward_decl GlobalTheory.UU.FESection.main
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem fe_all_degrees : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U =>
    D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  intro h1 h2 V _ _ _ hV D A G _ _ U hτ hFE
  have hsupp : ∀ N : ℕ, 1 ≤ N → ∃ β, U.Supp (Kbar V) N β := fun N hN => by
    obtain ⟨mu, hmu⟩ := (GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U N hN).2.1 0
    exact ⟨_, hmu⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hFE
  | succ k hk ih =>
    exact GlobalTheory.UU.SchurConst.main h1 h2 V hV D A G U (k + 1) (by omega)
      (GlobalTheory.T.exists_functionalEquation_section_nonzero_class h1 h2 V hV D A G U hτ k hk hFE ih (hsupp 1 le_rfl) (hsupp k hk))

end GlobalTheory.UU
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_equation_all_degrees_algebraic_closure : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  atlas_forward_decl GlobalTheory.UU.fe_all_degrees
end
