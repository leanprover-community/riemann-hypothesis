import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.AlgChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LocalResidues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zero' (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero, AddMonoidHom.zero_apply] at h
  omega

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nonneg_of_pos (hQ : ∀ x, 2 * Q x = Bf x x) (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x)
    (x : X) : 0 ≤ Q x := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
  · linarith [hpos x hx]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_eq_add_add_bilin (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (x y : X) : Q (x + y) = Q x + Q y + Bf x y := by
  have h := hQ (x + y)
  simp only [map_add, AddMonoidHom.add_apply] at h
  linarith [hQ x, hQ y, hsym y x]

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_zsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (k : ℤ) (x : X) :
    Q (k • x) = k ^ 2 * Q x := by
  have h := hQ (k • x)
  simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at h
  have h2 : 2 * Q (k • x) = 2 * (k ^ 2 * Q x) := by rw [h, ← hQ x]; ring
  exact mul_left_cancel₀ two_ne_zero h2

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma bilin_sq_le_four_mul_quad (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) (x y : X) : Bf x y ^ 2 ≤ 4 * Q x * Q y := by
  by_cases hx : x = 0
  · subst hx
    rw [quad_zero' hQ]
    simp
  · have hx1 := hpos x hx
    have hw := quad_nonneg_of_pos hQ hpos (Bf x y • x + (-(2 * Q x)) • y)
    rw [quad_add_eq_add_add_bilin hsym hQ, quad_zsmul' hQ, quad_zsmul' hQ] at hw
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_eq_mul, zsmul_eq_mul] at hw
    nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_add_le_add_sq_mul (hsym : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (hpos : ∀ x, x ≠ 0 → 1 ≤ Q x) {x y : X} {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hx : (Q x : ℝ) ≤ a ^ 2 * C) (hy : (Q y : ℝ) ≤ b ^ 2 * C) :
    (Q (x + y) : ℝ) ≤ (a + b) ^ 2 * C := by
  have hcs : (Bf x y : ℝ) ^ 2 ≤ 4 * (Q x : ℝ) * Q y := by
    exact_mod_cast bilin_sq_le_four_mul_quad hsym hQ hpos x y
  have hx0 : (0 : ℝ) ≤ Q x := by exact_mod_cast quad_nonneg_of_pos hQ hpos x
  have hy0 : (0 : ℝ) ≤ Q y := by exact_mod_cast quad_nonneg_of_pos hQ hpos y
  have hprod : (Q x : ℝ) * Q y ≤ (a ^ 2 * C) * (b ^ 2 * C) :=
    mul_le_mul hx hy hy0 (by positivity)
  have hB : (Bf x y : ℝ) ≤ 2 * a * b * C := by
    have h2 : (Bf x y : ℝ) ^ 2 ≤ (2 * a * b * C) ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  have hadd : (Q (x + y) : ℝ) = Q x + Q y + Bf x y := by
    exact_mod_cast quad_add_eq_add_add_bilin hsym hQ x y
  rw [hadd]
  nlinarith

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in
private lemma quad_nsmul' (hQ : ∀ x, 2 * Q x = Bf x x) (m : ℕ) (x : X) :
    Q (m • x) = (m : ℤ) ^ 2 * Q x := by
  have h := quad_zsmul' hQ (m : ℤ) x
  rwa [natCast_zsmul] at h

variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ} in

theorem _root_.GlobalTheory.small_combination_strict_min_mod :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) →
    (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) →
    ∀ (n D q : ℕ) (b : Fin n → X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) →
    (∀ j z, |(Bf (b j) z : ℝ)| ≤ M₀ * Q z) → (D : ℝ) * M₀ < q →
    ∀ e : Fin n → ℕ, ∑ j, e j ≤ D →
    ((Q (∑ j, e j • b j) : ℝ) ≤ (D : ℝ) ^ 2 * Cc) ∧
      ∀ z, z ≠ 0 → Q (∑ j, e j • b j) < Q (∑ j, e j • b j + q • z) := by
  intro X _ Bf Q hsym hQ hpos n D q b Cc M₀ hCc hM₀ hb hBb hq e he
  have hsumR : (∑ j, (e j : ℝ)) ≤ D := by exact_mod_cast he
  have hsum0 : (0 : ℝ) ≤ ∑ j, (e j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  constructor
  · have key : ∀ s : Finset (Fin n),
        (Q (∑ j ∈ s, e j • b j) : ℝ) ≤ (∑ j ∈ s, (e j : ℝ)) ^ 2 * Cc := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp [quad_zero' hQ]
      · intro j s hj ih
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        refine quad_add_le_add_sq_mul hsym hQ hpos (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hCc ?_ ih
        rw [quad_nsmul' hQ]
        push_cast
        exact mul_le_mul_of_nonneg_left (hb j) (by positivity)
    calc (Q (∑ j, e j • b j) : ℝ) ≤ (∑ j, (e j : ℝ)) ^ 2 * Cc := key Finset.univ
      _ ≤ (D : ℝ) ^ 2 * Cc :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hsum0 hsumR 2) hCc
  · intro z hz
    have hz1 : (1 : ℝ) ≤ Q z := by exact_mod_cast hpos z hz
    have hBv : Bf (∑ j, e j • b j) z = ∑ j, (e j : ℤ) * Bf (b j) z := by
      simp [map_sum, map_nsmul, nsmul_eq_mul]
    have hBvR : (Bf (∑ j, e j • b j) z : ℝ) = ∑ j, (e j : ℝ) * Bf (b j) z := by
      rw [hBv]; push_cast; rfl
    have hMz : (0 : ℝ) ≤ M₀ * Q z := mul_nonneg hM₀ (by linarith)
    have habs : |(Bf (∑ j, e j • b j) z : ℝ)| ≤ (∑ j, (e j : ℝ)) * (M₀ * Q z) := by
      rw [hBvR, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hBb j z) (Nat.cast_nonneg _)
    have h2 : (∑ j, (e j : ℝ)) * (M₀ * Q z) ≤ D * (M₀ * Q z) :=
      mul_le_mul_of_nonneg_right hsumR hMz
    have hlow := neg_abs_le (Bf (∑ j, e j • b j) z : ℝ)
    have hbound : -((D : ℝ) * M₀ * Q z) ≤ (Bf (∑ j, e j • b j) z : ℝ) := by nlinarith
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hM₀) hq
    have hadd : (Q (∑ j, e j • b j + q • z) : ℝ)
        = Q (∑ j, e j • b j) + (q : ℝ) ^ 2 * Q z + q * Bf (∑ j, e j • b j) z := by
      rw [quad_add_eq_add_add_bilin hsym hQ, quad_nsmul' hQ, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    have hfin : (Q (∑ j, e j • b j) : ℝ) < Q (∑ j, e j • b j + q • z) := by
      rw [hadd]
      nlinarith [mul_pos hq0 (mul_pos (show (0 : ℝ) < q - D * M₀ by linarith)
        (show (0 : ℝ) < Q z by linarith)),
        mul_nonneg hq0.le (show (0 : ℝ) ≤ Bf (∑ j, e j • b j) z + D * M₀ * Q z by linarith)]
    exact_mod_cast hfin

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralJets

section Unit

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {k : Type} [Field k] (t : Spec (CommRingCat.of k) ⟶ S)

theorem unitAt_square (hsq : SquareSt) (P : PolAV S) (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq S P (Over.mk t) x₁ x₂ (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨SectionArithmetic.pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [SectionArithmetic.sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV S) (b : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (Over.mk t) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square t hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square t hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

theorem exists_root [IsAlgClosed k] (hmul : MulNSt) (P : PolAV S) (a₀ : Over.mk t ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : Over.mk t ⟶ P.A, b ^ r = a₀ := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hmul S P r hr
  obtain ⟨u, hu⟩ := SectionDivision.exists_section (pullback.snd (mulA P.A r).left a₀.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ (mulA P.A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu, Category.id_comp]
  have hw : (u ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end Unit

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem exists_unit_sec (hL : Laws) (hTW : TwistBCSpanStatement) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D : DegPre V) (r : ℕ) (hr : 4 ≤ r) (χ : D.X) :
    ∃ β : D.SecB r χ, (η[D.P.A]).left (closedPoint V) ∈ nonzeroLocus β := by
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  have hf : IsLocalHom f := inferInstance
  let t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of V) := Spec.map (CommRingCat.ofHom f)
  let T : Over (Spec (CommRingCat.of V)) := Over.mk t
  let P := D.P
  have hLB := P.isLB
  let o : T ⟶ T ⊗ P.A := lift (𝟙 T) 1
  let y : (T ⊗ P.A).left := o.left (closedPoint k)
  have hy : (snd T P.A).left y = (η[D.P.A]).left (closedPoint V) := by
    have e : o ≫ snd T P.A = toUnit T ≫ η[P.A] := lift_snd _ _
    have e2 := congrArg (fun q => q.left (closedPoint k)) e
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at e2
    refine e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg _ ?_))
    exact IsLocalRing.comap_closedPoint f
  obtain ⟨b, hb⟩ := exists_root t hL.mulN P (toUnit _ ≫ D.c χ) r (by omega)
  have hE := unitAt_iter t hL.square P b y (r - 2)
  have hr2 : r - 2 + 2 = r := by omega
  have hr2' : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
  rw [hr2, hb, hr2'] at hE
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso P.A.left.topIso.hom)
  let hb' : (T ⊗ P.A).left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := (translPt P.A b).left ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hbι : hb' ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = (translPt P.A b).left := by
    show ((translPt P.A b).left ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι) ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨hgen, -⟩ := hL.ample _ P r hr
  obtain ⟨M', s', hcov'⟩ := hgen ⊤ (isAffineOpen_top _)
  obtain ⟨m0, hm0⟩ : ∃ m0, hb' y ∈ nonzeroLocus (s' m0) := Opens.mem_iSup.1 (by rw [hcov']; trivial)
  obtain ⟨kk', hkk'⟩ := Opens.mem_iSup.1 hm0
  have hG : UnitAt P.L (fun _ : Fin r => hb' ≫ (P.A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) y :=
    ⟨SectionArithmetic.pullSec (s' m0) hb', fun J hJ => by
      have := SectionArithmetic.sval_pullSec (s' m0) hb' (𝟙 _) y hJ
      rw [Category.id_comp] at this
      exact (congrArg IsUnit this).mpr (SectionArithmetic.isUnit_sval (s' m0) hb' y hJ kk' hkk')⟩
  obtain ⟨c, hc⟩ := exists_gen_of_local (V := V) P.L hLB ![(D.c χ).left, (η[P.A]).left] ![-1, 1]
  have hC : UnitAt P.L (fun i => (T ⊗ P.A).hom ≫ ![(D.c χ).left, (η[P.A]).left] i) ![-1, 1] y :=
    ⟨SectionArithmetic.pullSec (Geo.Tor.genSec c hc) (T ⊗ P.A).hom, fun J hJ => by
      rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ, sval_genSec c hc _ y hJ]
      exact Units.isUnit _⟩
  have a0 : (snd T P.A).left ≫ D.famφB χ 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.famφB χ 1 = (translPt P.A (toUnit T ≫ D.c χ)).left := by
    show (snd T P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ) = snd T P.A * (toUnit _ ≫ D.c χ) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.c χ)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm]
    show _ = (fst T P.A ≫ toUnit T ≫ D.c χ) * snd T P.A
    rw [← Category.assoc, comp_toUnit]
  have a2 : (snd T P.A).left ≫ D.famφB χ 2 = (T ⊗ P.A).hom ≫ (D.c χ).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.c χ).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  have a3 : (snd T P.A).left ≫ D.famφB χ 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.famφB χ i) (DegPre.famε r) y := by
    refine UnitAt.congr hLB (formEq_of_add fun U _ hh => ?_) ((hE.mul hG).mul hC)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_three,
      Fin.sum_univ_two]
    simp only [Sum.elim_inl, Sum.elim_inr, hbι, DegPre.famε, Matrix.cons_val, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← natCast_zsmul]
    module
  obtain ⟨m, c', β, hβ⟩ := hTW V D r (by omega) χ k f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart hLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  refine ⟨β i, ?_⟩
  rw [← hy]
  exact Opens.mem_iSup.2 ⟨_, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

section Alg

variable {F R : Type} [CommRing F] [CommRing R] [Algebra F R]

theorem one_le_pow {V : Submodule F R} (h1 : 1 ≤ V) : ∀ n : ℕ, 1 ≤ V ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    calc (1 : Submodule F R) = 1 * 1 := (_root_.mul_one 1).symm
      _ ≤ V ^ n * V := mul_le_mul' (one_le_pow h1 n) h1

theorem pow_mono {V : Submodule F R} (h1 : 1 ≤ V) {a b : ℕ} (hab : a ≤ b) : V ^ a ≤ V ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc V ^ a = V ^ a * 1 := (_root_.mul_one _).symm
    _ ≤ V ^ a * V ^ c := mul_le_mul' le_rfl (one_le_pow h1 c)

theorem pow_le_ideal_pow {W : Submodule F R} {m : Ideal R} (h : W ≤ m.restrictScalars F) :
    ∀ k : ℕ, W ^ k ≤ (m ^ k).restrictScalars F
  | 0 => by
    intro x _
    simp [Ideal.one_eq_top]
  | k + 1 => by
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    rw [Submodule.restrictScalars_mem, pow_succ]
    exact Ideal.mul_mem_mul (pow_le_ideal_pow h k ha) (h hb)

theorem pow_le_of_aug {V : Submodule F R} (h1 : 1 ≤ V) (aug : R →ₐ[F] F) (D : ℕ)
    (hD : RingHom.ker aug ^ (D + 1) = ⊥) (n : ℕ) : V ^ n ≤ V ^ D := by
  set m := RingHom.ker aug
  set W : Submodule F R := V ⊓ m.restrictScalars F
  have hVW : V ≤ 1 ⊔ W := by
    intro v hv
    have hc : v - algebraMap F R (aug v) ∈ m := by
      show aug _ = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    refine Submodule.mem_sup.2 ⟨algebraMap F R (aug v), Submodule.algebraMap_mem _, v - algebraMap F R (aug v),
      ⟨V.sub_mem hv (h1 (Submodule.algebraMap_mem _)), hc⟩, add_sub_cancel _ _⟩
  have hWm : W ≤ m.restrictScalars F := inf_le_right
  have key : ∀ n k : ℕ, W ^ k * V ^ n ≤ V ^ D := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero, _root_.mul_one]
      rcases le_or_gt k D with hk | hk
      · exact (pow_le_pow_left' (inf_le_left : W ≤ V) k).trans (pow_mono h1 hk)
      · refine (pow_le_ideal_pow hWm k).trans ?_
        intro x hx
        have : x ∈ m ^ (D + 1) := Ideal.pow_le_pow_right hk hx
        rw [hD, Ideal.mem_bot] at this
        rw [this]; exact zero_mem _
    | succ n ih =>
      intro k
      calc W ^ k * V ^ (n + 1) = W ^ k * (V ^ n * V) := by rw [pow_succ]
        _ ≤ W ^ k * (V ^ n * (1 ⊔ W)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hVW)
        _ = W ^ k * V ^ n ⊔ W ^ (k + 1) * V ^ n := by
          rw [Submodule.mul_sup, _root_.mul_one, Submodule.mul_sup, ← _root_.mul_assoc, pow_succ, mul_right_comm (W ^ k) W]
        _ ≤ _ := sup_le (ih k) (ih (k + 1))
  simpa using key n 0

theorem mem_span_pow {s : Set R} (h1 : (1 : R) ∈ s) (hs : Algebra.adjoin F s = ⊤) (aug : R →ₐ[F] F) (D : ℕ)
    (hD : RingHom.ker aug ^ (D + 1) = ⊥) (a : R) : a ∈ Submodule.span F s ^ D := by
  have h1' : 1 ≤ Submodule.span F s := Submodule.one_le.2 (Submodule.subset_span h1)
  have ha : a ∈ Algebra.adjoin F s := hs ▸ trivial
  suffices h : ∃ n, a ∈ Submodule.span F s ^ n by
    obtain ⟨n, hn⟩ := h
    exact pow_le_of_aug h1' aug D hD n hn
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by rw [pow_one]; exact Submodule.subset_span hx⟩
  | algebraMap c => exact ⟨0, by rw [pow_zero]; exact Submodule.algebraMap_mem c⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨max n₁ n₂, add_mem (pow_mono h1' (le_max_left _ _) h₁) (pow_mono h1' (le_max_right _ _) h₂)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨n₁ + n₂, by rw [pow_add]; exact Submodule.mul_mem_mul h₁ h₂⟩

end Alg

section Chart

open Chart

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {g : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ G}

theorem subalgebra_eq_top (hx : IsUnivChart G g x) (n : ℕ) (B : Subalgebra R (JetR R (Fin g) n))
    (y : Spec (CommRingCat.of B) ⟶ G.left) (hy : Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ y = (x n).left) :
    B = ⊤ := by
  have hw : y ≫ G.hom = (sp (R₀ := R) B).hom := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ G.hom)
    have e : Spec.map (φ ≫ CommRingCat.ofHom B.val.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap R (JetR R (Fin g) n))) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hy]
      exact Over.w (x n)
    have e' := Spec.map_injective e
    rw [← hφ]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R B))
    congr 1
    ext r
    exact congrArg (fun q => q.hom r) e'
  let y' : sp (R₀ := R) B ⟶ G := Over.homMk y hw
  have hy' : spMap B.val ≫ y' = x n := Over.OverMorphism.ext hy
  let aug := (jetAug R (Fin g) n).comp B.val
  have hker : RingHom.ker aug ^ (n + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have hle : Ideal.map B.val (RingHom.ker aug) ≤ RingHom.ker (jetAug R (Fin g) n) :=
      Ideal.map_le_iff_le_comap.mpr fun s hs => hs
    have := Ideal.mem_map_of_mem B.val ht
    rw [Ideal.map_pow] at this
    have h2 := Ideal.pow_right_mono hle _ this
    rw [ker_jetAug_pow, Ideal.mem_bot] at h2
    exact Ideal.mem_bot.2 (Subtype.ext h2)
  have h0 : spMap (jetAug R (Fin g) n) ≫ x n = 1 := spMap_jetAug_alt hx n
  have h1 : spMap aug ≫ y' = 1 := by
    rw [← h0, ← hy', ← Category.assoc, spMap_comp]
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 B aug n hker y' h1
  obtain ⟨ψ₀, -, hu⟩ := hx.2.2 (JetR R (Fin g) n) (jetAug R (Fin g) n) n (ker_jetAug_pow _ _) (x n) h0
  have e1 : B.val.comp ψ = ψ₀ := hu _ ⟨hψ1, by rw [← spMap_comp, Category.assoc, ← hψ2, hy']⟩
  have e2 : AlgHom.id R _ = ψ₀ := hu _ ⟨rfl, by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, spMap_left]
    show _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]⟩
  refine eq_top_iff.2 fun a _ => ?_
  have : a = B.val (ψ a) := AlgHom.congr_fun (e2.trans e1.symm) a
  rw [this]
  exact (ψ a).2

theorem jet_mem [IsLocalRing R] (hx : IsUnivChart G g x) (n : ℕ) (O : G.left.Opens)
    (hO : (η[G]).left (closedPoint R) ∈ O) (p : (sp (R₀ := R) (JetR R (Fin g) n)).left) : (x n).left p ∈ O := by
  let q := jetAug R (Fin g) n
  have hq : Function.Surjective q := aug_surj q
  have hker : RingHom.ker q.toRingHom ≤ p.asIdeal := fun a ha => by
    obtain ⟨m, hm⟩ := elt_nil _ (ker_jetAug_nil (R := R) (Fin g) n) a ha
    exact p.isPrime.mem_of_pow_mem m (by rw [hm]; exact zero_mem _)
  have := p.isPrime
  have hprime : (p.asIdeal.map q.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let p₀ : ↥(Spec (CommRingCat.of R)) := (⟨p.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum R)
  have hp : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap q.toRingHom (Ideal.map q.toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]
  have h0 : spMap q ≫ x n = toUnit _ ≫ η[G] := spMap_jetAug_alt hx n
  have e := congrArg (fun y : sp R ⟶ G => y.left.base p₀) h0
  simp only [Over.comp_left, spMap_left, Scheme.Hom.comp_apply] at e
  rw [← hp]
  refine (congrArg (· ∈ O) e).mpr ?_
  exact ((IsLocalRing.specializes_closedPoint (R := R) ((toUnit (sp (R₀ := R) R)).left p₀)).map
    (η[G]).left.continuous).mem_open O.isOpen hO

end Chart

section Ratio

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (τ : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (hτ : τ.IsGen) :
    ∃ u : Γ(Z, ⊤), ∀ z J, Good L z J → sval s h z J = gs (𝟙 Z) z ⊤ u * (val τ (𝟙 Z) z J).val := by
  obtain ⟨w, hw⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (formEq_of_add fun U _ hh => by simp [Fintype.sum_sum_type])
    (pullMulSec s h (LB.invGen L _ _ τ) (invGen_isGen _ _ _ _ hτ))
  have le : (⊤ : Z.Opens) ≤ LB.wchart L (K := PEmpty) (Y := Z) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Z.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim), fun z J hJ => ?_⟩
  have e := hw Z (𝟙 Z) z J hJ
  rw [sval_pullMulSec _ _ _ _ _ z hJ, Category.id_comp, val_inv, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg (· * _) ((gs_res (𝟙 Z) z le trivial _).trans e).symm)
  rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Ratio

section Main

open Chart

def germOf {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) : A →+* (Spec (CommRingCat.of A)).presheaf.stalk z :=
  ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem germOf_eq {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) (a : A) :
    germOf z a = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
  (gs_eq (𝟙 _) z ⊤ trivial _).symm

theorem germOf_hom {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) (u : Γ(Spec (CommRingCat.of A), ⊤)) :
    germOf z ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom u) = gs (𝟙 _) z ⊤ u := by
  rw [germOf_eq]
  congr 1
  simp

theorem germOf_ext {A : Type} [CommRing A] {a b : A} (h : ∀ z, germOf z a = germOf z b) : a = b :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    (fn_ext (V := ⊤) fun z _ => (germOf_eq z a).symm.trans ((h z).trans (germOf_eq z b)))

theorem isUnit_of_germOf {A : Type} [CommRing A] {a : A} (h : ∀ z, IsUnit (germOf z a)) : IsUnit a := by
  have : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    (Spec (CommRingCat.of A)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => h z
  simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem gs_const {V A : Type} [CommRing V] [CommRing A] (f : V →+* A) (z : Spec (CommRingCat.of A)) (c : V) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) = germOf z (f c) := by
  have e := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [germOf_eq, e]
  exact (congrArg (fun q => gs q z ⊤ _) (Category.id_comp _).symm).trans (gs_pull (𝟙 _) _ z ⊤ trivial _).symm

theorem jets (hL : Laws) (hTW : TwistBCSpanStatement) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D : DegPre V) (q n : ℕ) (hq : 4 * n + 4 ≤ q) (χ : D.X) (g : ℕ)
    (x : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin g) m) ⟶ D.P.A) (hx : IsUnivChart D.P.A g x)
    (τ : LB.Gen (LB.LinComb (Y := Spec (CommRingCat.of (JetR V (Fin g) n))) D.P.L (fun i => (x n).left ≫ D.famφB χ i) (DegPre.famε q))) (hτ : τ.IsGen)
    (a : JetR V (Fin g) n) : ∃ β : D.SecB q χ, ∀ (z : Spec (CommRingCat.of (JetR V (Fin g) n))) (J),
      Good D.P.L z J → sval β (x n).left z J = germOf z a * (val τ (𝟙 _) z J).val := by
  obtain ⟨r, rfl⟩ : ∃ r, q = 4 * n + r := ⟨q - 4 * n, by omega⟩
  have hLB := D.P.isLB
  obtain ⟨β₀, hβ₀⟩ := exists_unit_sec hL hTW V D r (by omega) χ
  let xn : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ D.P.A.left := (x n).left
  let W := (D.P.A.hom ⁻¹ᵁ ⊤).toScheme
  let iw : W ⟶ D.P.A.left := (D.P.A.hom ⁻¹ᵁ ⊤).ι
  have : IsIso iw := inferInstanceAs (IsIso D.P.A.left.topIso.hom)
  have : IsIso (⊤ : (Spec (CommRingCat.of V)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (CommRingCat.of V)).topIso.hom)
  let h0 : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ W := xn ≫ inv iw
  have h0i : h0 ≫ iw = xn := by
    show (xn ≫ inv iw) ≫ iw = xn
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨-, hva⟩ := hL.ample _ D.P 4 le_rfl
  obtain ⟨M, s, hcov, hs⟩ := hva ⊤ (isAffineOpen_top _)
  obtain ⟨i0, hi0⟩ : ∃ i0, inv iw ((η[D.P.A]).left (closedPoint V)) ∈ nonzeroLocus (s i0) :=
    Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hz0 : ∀ z, h0 z ∈ nonzeroLocus (s i0) := fun z => jet_mem hx n (inv iw ⁻¹ᵁ nonzeroLocus (s i0)) hi0 z
  have hle : ⊤ ≤ h0 ⁻¹ᵁ nonzeroLocus (s i0) := fun z _ => hz0 z
  obtain ⟨hD, rr, hrel, hsurj⟩ := hs i0
  let π := h0.appLE (nonzeroLocus (s i0)) ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin g) n))).hom
  have hπ : ∀ z b, germOf z (π.hom b) = gs h0 z _ b := fun z b =>
    (germOf_hom z _).trans ((gs_appLE h0 _ ⊤ hle (𝟙 _) z trivial b).trans (by rw [Category.id_comp]))
  have hπs : Spec.map π ≫ hD.fromSpec = h0 := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec h0 hD (isAffineOpen_top _) hle
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  let ρ : Fin (M + 1) → JetR V (Fin g) n := fun i => π.hom (rr i)
  have hσ0 : ∀ z J, Good D.P.L z J → IsUnit (sval (s i0) h0 z J) := fun z J hJ => by
    obtain ⟨kk, hkk⟩ := Opens.mem_iSup.1 (hz0 z)
    exact SectionArithmetic.isUnit_sval (s i0) h0 z hJ kk hkk
  have hβ0 : ∀ z J, Good D.P.L z J → IsUnit (sval β₀ xn z J) := fun z J hJ => by
    obtain ⟨kk, hkk⟩ := Opens.mem_iSup.1 (jet_mem hx n _ hβ₀ z)
    exact SectionArithmetic.isUnit_sval β₀ xn z hJ kk hkk
  have hrelv : ∀ i z J, Good D.P.L z J → sval (s i) h0 z J = germOf z (ρ i) * sval (s i0) h0 z J := fun i z J hJ =>
    (LocalResidues.sval_rel (s i) (s i0) _ (rr i) (hrel i) h0 z hJ (hz0 z)).trans (by rw [← hπ])
  have good : ∀ z : Spec (CommRingCat.of (JetR V (Fin g) n)), ∃ J, Good D.P.L z J := fun z => by
    choose J hJ using fun ψ : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ D.P.A.left => exists_chart hLB (ψ z)
    exact ⟨J, hJ⟩
  have hρ1 : ρ i0 = 1 := germOf_ext fun z => by
    obtain ⟨J, hJ⟩ := good z
    rw [map_one]
    exact ((hσ0 z J hJ).mul_left_inj.1 ((hrelv i0 z J hJ).symm.trans (_root_.one_mul _).symm))

  have hadj : Algebra.adjoin V (Set.range ρ) = ⊤ := by
    have hq' : (h0 ≫ (D.P.A.hom ∣_ ⊤)) ≫ (⊤ : (Spec (CommRingCat.of V)).Opens).ι =
        Spec.map (CommRingCat.ofHom (algebraMap V (JetR V (Fin g) n))) := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, h0i]
      exact Over.w (x n)
    have hc : ∀ b, π.hom (((D.P.A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i0)) le_top).hom b) ∈
        Algebra.adjoin V (Set.range ρ) := fun b => by
      let e := (⊤ : (Spec (CommRingCat.of V)).Opens).ι
      let c : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (((inv e).app ⊤).hom b)
      have : π.hom (((D.P.A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i0)) le_top).hom b) = algebraMap V _ c :=
        germOf_ext fun z => by
          refine (hπ z _).trans ((gs_appLE _ _ _ _ h0 z (hz0 z) b).trans (Eq.trans ?_ (gs_const _ z c)))
          have e1 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c = ((inv e).app ⊤).hom b := by simp [c]
          rw [e1]
          refine Eq.trans ?_ (gs_pull _ (inv e) z ⊤ trivial b).symm
          rw [← hq', Category.assoc (h0 ≫ _), IsIso.hom_inv_id, Category.comp_id]
      rw [this]
      exact Subalgebra.algebraMap_mem _ c
    have hall : ∀ b, π.hom b ∈ Algebra.adjoin V (Set.range ρ) := fun b => by
      obtain ⟨p, rfl⟩ := hsurj b
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval₂Hom_C]; exact hc c
      | add p p' hp hp' => rw [map_add, map_add]; exact add_mem hp hp'
      | mul_X p i hp =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine subalgebra_eq_top hx n _ (Spec.map (CommRingCat.ofHom
      (π.hom.codRestrict (Algebra.adjoin V (Set.range ρ)) hall)) ≫ hD.fromSpec ≫ iw) ?_
    rw [← Category.assoc, ← Spec.map_comp]
    refine Eq.trans ?_ h0i
    rw [← hπs, Category.assoc]
    rfl

  have key : ∀ α : Fin n → Fin (M + 1), ∃ S : D.SecB (4 * n + r) χ, ∀ z J, Good D.P.L z J →
      sval S xn z J = germOf z (∏ l, ρ (α l)) * (sval (s i0) h0 z J ^ n * sval β₀ xn z J) := by
    intro α
    obtain ⟨S, hS⟩ := exists_sec hLB (φ' := D.famφB χ) (ε' := DegPre.famε (4 * n + r))
      (formEq_of_add fun U _ hh => by
        have e : inv iw ≫ (D.P.A.hom ⁻¹ᵁ ⊤).ι = D.famφB χ 0 := IsIso.inv_hom_id iw
        rw [Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
        simp only [Sum.elim_inl, Sum.elim_inr, e, DegPre.famε, Matrix.cons_val, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Fintype.card_prod, ← natCast_zsmul]
        push_cast
        module)
      (SectionArithmetic.mulSec (SectionArithmetic.powSec fun l => SectionArithmetic.pullSec (s (α l)) (inv iw)) β₀)
    refine ⟨S, fun z J hJ => ?_⟩
    have hp : ∀ i, sval (SectionArithmetic.pullSec (s i) (inv iw)) xn z J = germOf z (ρ i) * sval (s i0) h0 z J := fun i =>
      (SectionArithmetic.sval_pullSec (s i) (inv iw) xn z hJ).trans (hrelv i z J hJ)
    have e1 : (∏ i, sval (SectionArithmetic.pullSec (s (α i)) (inv iw)) xn z J) =
        germOf z (∏ l, ρ (α l)) * sval (s i0) h0 z J ^ n :=
      (Finset.prod_congr rfl fun i _ => hp (α i)).trans (by rw [Finset.prod_mul_distrib, Fin.prod_const, map_prod])
    rw [hS _ xn z J hJ, SectionArithmetic.sval_mulSec _ _ _ z hJ, SectionArithmetic.sval_powSec _ _ z hJ, ← _root_.mul_assoc]
    exact congrArg₂ (· * ·) e1 rfl

  obtain ⟨S₀, hS₀⟩ := key fun _ => i0
  obtain ⟨u, hu⟩ := exists_ratio hLB S₀ xn τ hτ
  let w : JetR V (Fin g) n := (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin g) n))).hom.hom u
  have hw : ∀ z J, Good D.P.L z J →
      sval (s i0) h0 z J ^ n * sval β₀ xn z J = germOf z w * (val τ (𝟙 _) z J).val := fun z J hJ => by
    have := hS₀ z J hJ
    rw [hu z J hJ, hρ1, Finset.prod_const_one, map_one, _root_.one_mul, ← germOf_hom] at this
    exact this.symm
  obtain ⟨w', hw'⟩ : IsUnit w := isUnit_of_germOf fun z => by
    obtain ⟨J, hJ⟩ := good z
    exact isUnit_of_mul_isUnit_left ((congrArg IsUnit (hw z J hJ)).mp (((hσ0 z J hJ).pow n).mul (hβ0 z J hJ)))
  let N : Submodule V (JetR V (Fin g) n) :=
    { carrier := {v | ∃ β : D.SecB (4 * n + r) χ, ∀ z J, Good D.P.L z J →
        sval β xn z J = germOf z (v * w) * (val τ (𝟙 _) z J).val}
      add_mem' := by
        rintro v v' ⟨β, hβ⟩ ⟨β', hβ'⟩
        refine ⟨SectionArithmetic.secAdd β β', fun z J hJ => ?_⟩
        rw [add_mul, map_add, add_mul, ← hβ z J hJ, ← hβ' z J hJ]
        exact gs_add xn z _ (hJ.mem _ xn) _ _
      zero_mem' := ⟨SectionArithmetic.secZero _, fun z J hJ => by
        rw [zero_mul, map_zero, zero_mul]
        exact (gs_eq xn z _ (hJ.mem _ xn) _).trans ((congrArg _ (map_zero _)).trans (map_zero _))⟩
      smul_mem' := by
        rintro c v ⟨β, hβ⟩
        refine ⟨SectionArithmetic.secCMul (V := D.P.A.hom ⁻¹ᵁ ⊤) (fun _ _ _ => trivial)
          ((D.P.A.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c)) β, fun z J hJ => ?_⟩
        rw [Algebra.smul_def, _root_.mul_assoc, map_mul, _root_.mul_assoc, ← hβ z J hJ, ← gs_const]
        refine (gs_mul xn z _ (hJ.mem _ xn) _ _).trans (congrArg₂ (· * ·) ?_ rfl)
        refine (gs_res xn z _ (hJ.mem _ xn) _).trans ((gs_pull xn D.P.A.hom z ⊤ trivial _).trans ?_)
        exact congrArg (fun q => gs q z ⊤ _) (Over.w (x n)) }
  have hN : Submodule.span V (Set.range ρ) ^ n ≤ N := by
    rw [Submodule.span_pow (Set.range ρ)]
    refine Submodule.span_le.2 fun v hv => ?_
    obtain ⟨t, rfl⟩ := Set.mem_pow.1 hv
    choose α hα using fun l => (t l).2
    obtain ⟨S, hS⟩ := key α
    refine ⟨S, fun z J hJ => ?_⟩
    have : (List.ofFn fun i => (t i : JetR V (Fin g) n)).prod = ∏ l, ρ (α l) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun l _ => (hα l).symm
    rw [hS z J hJ, hw z J hJ, this, map_mul (germOf z), _root_.mul_assoc]
  obtain ⟨β, hβ⟩ := hN (mem_span_pow (s := Set.range ρ) ⟨i0, hρ1⟩ hadj (jetAug V (Fin g) n) n (ker_jetAug_pow _ _) (a * ↑w'⁻¹))
  refine ⟨β, fun z J hJ => (hβ z J hJ).trans ?_⟩
  rw [← hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Main

theorem integral_jets : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (q n : ℕ), 4 * n + 4 ≤ q → ∀ (χ : D.X) (g : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := V) (Chart.JetR V (Fin g) m) ⟶ D.P.A), Chart.IsUnivChart D.P.A g x → ∀ τ : LB.Gen (LB.LinComb D.P.L (fun i => (x n).left ≫ D.famφB χ i) (DegPre.famε q)), τ.IsGen → ∀ a : Chart.JetR V (Fin g) n, ∃ β : D.SecB q χ, (∀ (z : (Chart.sp (R₀ := V) (Chart.JetR V (Fin g) n)).left) (J), Good D.P.L z J → sval (β) (x n).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Chart.JetR V (Fin g) n))).inv.hom (a)) * (val τ (𝟙 _) z J).val) := by
  intro hL hTW V _ _ _ D q n hq χ g x hx τ hτ a
  obtain ⟨β, hβ⟩ := jets hL hTW V D q n hq χ g x hx τ hτ a
  exact ⟨β, fun z J hJ => (hβ z J hJ).trans (congrArg (· * _) (germOf_eq z a))⟩

end GlobalTheory.IntegralJets
end
end

section
namespace GlobalTheory.NotLeSqSup

theorem not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n

theorem main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this

end GlobalTheory.NotLeSqSup
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmallJets

section Alg

theorem isUnit_of_aug {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) {n : ℕ}
    (h : RingHom.ker aug ^ (n + 1) = ⊥) {a : A} (ha : IsUnit (aug a)) : IsUnit a := by
  have hm : a - algebraMap R A (aug a) ∈ RingHom.ker aug := by simp [RingHom.mem_ker]
  have hn : IsNilpotent (a - algebraMap R A (aug a)) := ⟨n + 1, by
    have := Ideal.pow_mem_pow hm (n + 1)
    rwa [h, Ideal.mem_bot] at this⟩
  have := hn.isUnit_add_right_of_commute (ha.map (algebraMap R A)) (Commute.all _ _)
  simpa using this

theorem isLocalRing_of_aug {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    {n : ℕ} (h : RingHom.ker aug ^ (n + 1) = ⊥) : IsLocalRing A := by
  have : Nontrivial A := aug.toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (aug a) with h1 | h1
  · exact Or.inl (isUnit_of_aug aug h h1)
  · exact Or.inr (isUnit_of_aug aug h (by rwa [map_sub, map_one]))

theorem eq_top_of_monomials {S A : Type} [CommRing S] [CommRing A] (f : S →+* A) (I : Ideal A) (n : ℕ)
    (hI : I ^ (n + 1) = ⊥) (hc : ∀ a, ∃ s, a - f s ∈ I) {r : ℕ} (v : Fin r → A) (t : Set A) (ht : I = Ideal.span t)
    (htv : ∀ y ∈ t, (∃ s, y = f s) ∨ ∃ j s s', y = f s * v j + f s') (N : AddSubgroup A)
    (hN : ∀ e : Fin r → ℕ, ∑ j, e j ≤ n → ∀ s, f s * ∏ j, v j ^ e j ∈ N) : N = ⊤ := by
  classical
  letI := f.toAlgebra
  let M : ℕ → Submodule S A := fun m => Submodule.span S {y | ∃ e : Fin r → ℕ, ∑ j, e j ≤ m ∧ y = ∏ j, v j ^ e j}
  have mono : ∀ m, M m ≤ M (m + 1) := fun m => Submodule.span_mono fun y ⟨e, he, hy⟩ => ⟨e, by omega, hy⟩
  have mulv : ∀ m j, ∀ y ∈ M m, y * v j ∈ M (m + 1) := by
    intro m j y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, rfl⟩ := hy
      refine Submodule.subset_span ⟨e + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
        omega
      · simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
        simp
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha
  have mult : ∀ m, ∀ y ∈ M m, ∀ u ∈ t, y * u ∈ M (m + 1) := by
    intro m y hy u hu
    rcases htv u hu with ⟨s, rfl⟩ | ⟨j, s, s', rfl⟩
    · rw [mul_comm]; exact mono m ((M m).smul_mem s hy)
    · have e : y * (f s * v j + f s') = s • (y * v j) + s' • y := by
        show _ = f s * _ + f s' * _
        ring
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ (mulv m j y hy)) (mono m (Submodule.smul_mem _ _ hy))
  have zero : ∀ a, a ∈ M 0 ⊔ (I ^ (0 + 1)).restrictScalars S := fun a => by
    obtain ⟨s, hs⟩ := hc a
    refine Submodule.mem_sup.2 ⟨s • 1, Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp⟩),
      a - f s, by simpa using hs, ?_⟩
    show f s * 1 + _ = _
    ring
  have step : ∀ m, ∀ a ∈ I ^ m, a ∈ M m ⊔ (I ^ (m + 1)).restrictScalars S := by
    intro m
    induction m with
    | zero => exact fun a _ => zero a
    | succ m ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
      rw [ht] at hy
      induction hy using Submodule.span_induction generalizing x with
      | mem y hy =>
        obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (ih x hx)
        rw [add_mul]
        refine Submodule.add_mem_sup (mult m p hp y hy) ?_
        rw [Submodule.restrictScalars_mem, pow_succ]
        exact Ideal.mul_mem_mul hi (ht ▸ Ideal.subset_span hy)
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem (ha x hx) (hb x hx)
      | smul s a _ ha =>
        rw [smul_eq_mul, ← _root_.mul_assoc]
        exact ha _ (Ideal.mul_mem_right _ _ hx)
  have all : ∀ m a, a ∈ M m ⊔ (I ^ (m + 1)).restrictScalars S := by
    intro m
    induction m with
    | zero => exact zero
    | succ m ih =>
      intro a
      obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (ih a)
      exact add_mem (Submodule.mem_sup_left (mono m hp)) (step (m + 1) i hi)
  have fin : ∀ y ∈ M n, ∀ s, f s * y ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨e, he, rfl⟩ := hy; exact hN e he
    | zero => simp
    | add a b _ _ ha hb => intro s; rw [mul_add]; exact add_mem (ha s) (hb s)
    | smul s' a _ ha =>
      intro s
      have := ha (s * s')
      rwa [map_mul, _root_.mul_assoc] at this
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (all n a)
  rw [Submodule.restrictScalars_mem, hI, Ideal.mem_bot] at hi
  simpa [hi] using fin p hp 1

open Chart ChartBaseChange

theorem finite_jet (R : Type) [CommRing R] [IsNoetherianRing R] (d n : ℕ) : Module.Finite R (JetR R (Fin d) n) :=
  Module.finite_of_surjective_of_ker_le_nilradical (jetAug R (Fin d) n) (aug_surj _)
    (fun a ha => elt_nil _ (ker_jetAug_nil (R := R) (Fin d) n) a ha) (IsNoetherian.noetherian _)

theorem mem_map_of_jetCoeff {R : Type} [CommRing R] (p : Ideal R) (d n : ℕ) {a : JetR R (Fin d) n}
    (ha : jetCoeff R (R ⧸ p) (Fin d) n a = 0) : a ∈ p.map (algebraMap R (JetR R (Fin d) n)) := by
  let π := Ideal.Quotient.mkₐ R (p.map (algebraMap R (JetR R (Fin d) n)))
  have hJ : ((RingHom.ker (jetAug R (Fin d) n)).map π) ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot]
  let g := jetLift (R ⧸ p) _ hJ (fun j => π (zR n j)) (fun j => Ideal.mem_map_of_mem _ (zR_mem_ker n j))
  have e : (g.restrictScalars R).comp (jetCoeff R (R ⧸ p) (Fin d) n) = π := jet_ext fun j => by
    show g (jetCoeff R (R ⧸ p) (Fin d) n (zR n j)) = _
    rw [jetCoeff_zR, jetLift_zR]
  have := AlgHom.congr_fun e a
  rw [AlgHom.comp_apply, ha, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

theorem eq_top_of_jetCoeff {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R)
    (hp : p ≤ maximalIdeal R) (d n : ℕ) (N : Submodule R (JetR R (Fin d) n))
    (h : ∀ y, ∃ a ∈ N, jetCoeff R (R ⧸ p) (Fin d) n a = y) : N = ⊤ := by
  have := finite_jet R d n
  refine eq_top_iff.2 (Submodule.le_of_le_smul_of_le_jacobson_bot (I := p) Module.Finite.fg_top
    (hp.trans (maximalIdeal_le_jacobson _)) fun a _ => ?_)
  obtain ⟨a', ha', e⟩ := h (jetCoeff R (R ⧸ p) (Fin d) n a)
  have hm := mem_map_of_jetCoeff p d n (a := a - a') (by rw [map_sub, e, sub_self])
  refine Submodule.mem_sup.2 ⟨a', ha', a - a', ?_, add_sub_cancel _ _⟩
  rw [Ideal.smul_top_eq_map]
  exact hm

end Alg

section Local

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_pull_of_ratio (hL : L.IsLB) {Z : Scheme.{0}} (s : LB.Sec (LB.LinComb L φ ε)) (m : Z ⟶ Y)
    (τ : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hτ : τ.IsGen) (u : Γ(Z, ⊤))
    (h : ∀ z J, Good L z J → sval s m z J = gs (𝟙 Z) z ⊤ u * (val τ (𝟙 Z) z J).val)
    {W : Scheme.{0}} (g : W ⟶ Z) (w : W) {J} (hJ : Good L w J) :
    sval s (g ≫ m) w J = gs g w ⊤ u * (val τ g w J).val := by
  have key : ∀ {W : Scheme.{0}} (g : W ⟶ Z) (w : W) {J}, Good L w J →
      sval (SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) u (Geo.Tor.genSec τ hτ)) g w J = gs g w ⊤ u * (val τ g w J).val :=
    fun g w J hJ => (gs_mul g w _ (hJ.mem _ g) _ _).trans (congrArg₂ (· * ·) (gs_res g w _ (hJ.mem _ g) _)
      (sval_genSec τ hτ g w hJ))
  have e := sec_ext_val hL (s := SectionArithmetic.pullSec s m) (s' := SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) u (Geo.Tor.genSec τ hτ))
    fun z J hJ => by rw [SectionArithmetic.sval_pullSec s m _ z hJ, Category.id_comp, h z J hJ, key _ z hJ]
  rw [← SectionArithmetic.sval_pullSec s m g w hJ, ← key g w hJ]
  exact congrArg (gs g w _) (e _)

theorem exists_val_local (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) {A : Type} [CommRing A] [IsLocalRing A]
    (r : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ ε)) : ∃ a : Aˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp A) (z : Z),
      g z = closedPoint A → (val t (g ≫ r) z (fun ψ => c (ψ z))).val = cst g z a := by
  let j : K → L.ι := fun k => c ((r ≫ φ k) (closedPoint A))
  have hm : ∀ p : Sp A, r p ∈ LB.wchart L φ j := fun p =>
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) r (U := LB.wchart L φ j)
      (Set.mem_iInter.2 fun k => hc ((r ≫ φ k) (closedPoint A)))).ge (Set.mem_univ p)
  have le : (⊤ : (Sp A).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ j := fun p _ => hm p
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom (res le (pullU r _ (t.s j))),
    fun Z g z hz => ?_⟩
  have e1 := val_of t (g ≫ r) z (fun ψ => c (ψ z)) j (fun k => congrArg c (by
    show ((g ≫ r) ≫ φ k) z = (r ≫ φ k) (closedPoint A)
    rw [Category.assoc, Scheme.Hom.comp_apply, hz]))
  refine (congrArg Units.val (e1.trans ((gm_pull g r z _ (hm _) _).symm.trans (gm_res g z le trivial _).symm))).trans
    ((gs_unit g z ⊤ trivial _).symm.trans (congrArg (gs g z ⊤) ?_))
  simp

theorem bijective_germOf (A : Type) [CommRing A] [IsLocalRing A] :
    Function.Bijective (IntegralJets.germOf (A := A) (closedPoint A)) := by
  have e : IntegralJets.germOf (A := A) (closedPoint A) = (stalkClosedPointIso (CommRingCat.of A)).inv.hom := by
    have := germ_stalkClosedPointIso_hom (CommRingCat.of A)
    rw [← Iso.eq_comp_inv, ← Iso.inv_comp_eq] at this
    exact congrArg CommRingCat.Hom.hom this
  rw [e]
  exact ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of A)).inv

theorem cst_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    cst (Geo.Tor.spMap f) z a = IntegralJets.germOf z (f a) := IntegralJets.gs_const f z a

end Local

theorem exists_unit_prod {S A X : Type} [CommRing S] [CommRing A] [AddCommGroup X] (f : S →+* A) (v : X → Aˣ)
    (hv : ∀ a b, ∃ u : Sˣ, (v (a + b) : A) * f u = v a * v b) {r : ℕ} (b : Fin r → X) (e : Fin r → ℕ) :
    ∃ u : Sˣ, (v (∑ j, e j • b j) : A) * f u = ∏ j, (v (b j) : A) ^ e j := by
  let H : Subgroup Aˣ := (Units.map f.toMonoidHom).range
  let θ : X →+ Additive (Aˣ ⧸ H) := AddMonoidHom.mk' (fun χ => Additive.ofMul (QuotientGroup.mk' H (v χ))) fun a b => by
    obtain ⟨u, hu⟩ := hv a b
    rw [← ofMul_mul, ← map_mul]
    refine congrArg Additive.ofMul (QuotientGroup.eq.2 ⟨u, eq_inv_mul_of_mul_eq (Units.ext hu)⟩)
  have h : QuotientGroup.mk' H (v (∑ j, e j • b j)) = QuotientGroup.mk' H (∏ j, v (b j) ^ e j) := by
    show Additive.toMul (θ (∑ j, e j • b j)) = _
    rw [map_sum, toMul_sum, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_nsmul, toMul_nsmul, map_pow]
    rfl
  obtain ⟨u, hu⟩ := QuotientGroup.eq.1 h
  refine ⟨u, ?_⟩
  have := congrArg Units.val (mul_eq_of_eq_inv_mul hu)
  simpa using this

section Torus

open Chart ChartBaseChange
open scoped CategoryTheory.Obj

theorem ker_jetAug_eq (k : Type) [CommRing k] (hk : IsField k) (X : Type) [AddCommGroup X] (r : ℕ)
    (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B)
    (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (hq : IsMonHom q) (hi : IsMonHom i)
    (hpb : IsPullback i (toUnit _) q η[B]) (d g n : ℕ) (x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin d) m) ⟶ G)
    (xB : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin g) m) ⟶ B) (hx : IsUnivChart G d x) (hxB : IsUnivChart B g xB)
    (ψ : JetR k (Fin g) n →ₐ[k] JetR k (Fin d) n) (hψ : x n ≫ q = Chart.spMap ψ ≫ xB n) (T : Fin r → JetR k (Fin d) n)
    (hT : ∀ j, jetAug k (Fin d) n (T j) = 0)
    (h : ∀ (φ : JetR k (Fin d) n →ₐ[k] DualNumber k)
      (y : sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j,
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) =
        y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) :
    RingHom.ker (jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (zR n l)) := by
  letI := hk.toField
  exact ker_jetAug_eq_span_torus_union_quotient k X r b G B q i hq hi hpb d g n x xB hx hxB ψ hψ T hT h

theorem ker_fst_sq (k : Type) [CommRing k] : RingHom.ker (TrivSqZeroExt.fstHom k k k) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro u hu u' hu'
  have h1 : u.fst = 0 := hu
  have h2 : u'.fst = 0 := hu'
  rw [Ideal.mem_bot]
  ext <;> simp [h1, h2]

theorem spMap_closedPoint_dual {k : Type} [CommRing k] (hk : IsField k) {d n : ℕ} [IsLocalRing (JetR k (Fin d) n)]
    [IsLocalRing (DualNumber k)] (φ : JetR k (Fin d) n →ₐ[k] DualNumber k) :
    Geo.Tor.spMap φ.toRingHom (closedPoint _) = closedPoint _ := by
  have ha : (TrivSqZeroExt.fstHom k k k).comp φ = jetAug k (Fin d) n := jet_ext fun l => by
    letI := hk.toField
    rw [jetAug_zR]
    exact ((elt_nil _ (ker_jetAug_nil (R := k) (Fin d) n) _ (zR_mem_ker n l)).map _).eq_zero
  have : IsLocalHom φ.toRingHom := ⟨fun s hs => isUnit_of_aug _ (ker_jetAug_pow _ _)
    (ha ▸ hs.map (TrivSqZeroExt.fstHom k k k))⟩
  exact IsLocalRing.comap_closedPoint φ.toRingHom

theorem one_add_normalised {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (v : A) (w : kˣ) (χ : B) (h : φ v = χ * algebraMap k B w.val) :
    1 + φ (algebraMap k A w⁻¹.val * v - 1) = χ := by
  rw [map_sub, map_mul, map_one, AlgHom.commutes, h, add_sub_cancel, mul_left_comm, ← map_mul, Units.inv_mul,
    map_one, _root_.mul_one]

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem torus_jets (hk : IsField (R ⧸ I ^ (e + 1))) (c : D.toPre.P.A.left → D.toPre.P.L.ι)
    (hc : ∀ x, x ∈ D.toPre.P.L.U (c x)) {d g : ℕ} (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx : IsUnivChart G d x) (xB : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ D.toPre.P.A)
    (hxB : IsUnivChart D.toPre.P.A g xB) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.toPre.X)
    [IsLocalRing (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)] [IsLocalRing (JetR R (Fin g) n)] :
    ∃ (p : Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n) ⟶ (thickObj R I e G).left)
      (f : JetR R (Fin g) n →+* JetR (R ⧸ I ^ (e + 1)) (Fin d) n) (v : D.toPre.X → (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)ˣ),
      p ≫ fGl I G e = Geo.Tor.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin d) n).toRingHom ≫ (x n).left ∧
      p ≫ pGl U e = Geo.Tor.spMap f ≫ (xB n).left ∧ Geo.Tor.spMap f (closedPoint _) = closedPoint _ ∧
      (∀ χ, (val (tG U e χ) p (closedPoint _) (fun ψ => c (ψ (closedPoint _)))).val =
        IntegralJets.germOf (closedPoint _) (v χ).val) ∧
      ∀ N : AddSubgroup (JetR (R ⧸ I ^ (e + 1)) (Fin d) n),
        (∀ a : Fin r → ℕ, ∑ j, a j ≤ n → ∀ s, f s * v (∑ j, a j • b j) ∈ N) → N = ⊤ := by
  have hloc : IsLocalRing (R ⧸ I ^ (e + 1)) := by letI := hk.toField; infer_instance
  have hmk : IsLocalHom (algebraMap R (R ⧸ I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hG : IsGrpPullback (thickObj R I e G) G (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (e + 1)))))
    (pullback.fst G.hom (thick R I e)) := isGrpPullback_pullback G (thick R I e)
  have hB : IsGrpPullback (thickObj R I e D.toPre.P.A) D.toPre.P.A
    (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (e + 1)))))
    (pullback.fst D.toPre.P.A.hom (thick R I e)) := isGrpPullback_pullback _ (thick R I e)
  choose x' hx' using fun m => push_surjective hG (Chart.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin d) m) ≫ x m)
  choose xB' hxB' using fun m => push_surjective hB (Chart.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) m) ≫ xB m)
  have hu := isUnivChart_baseChange hG hx hx'
  have huB := isUnivChart_baseChange hB hxB hxB'
  have hq := (U.gt e).q_hom
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := huB.2.2 _ (jetAug _ (Fin d) n) n (ker_jetAug_pow _ _) (x' n ≫ (U.gt e).q)
    (by rw [← Category.assoc, spMap_jetAug_alt hu n, MonObj.one_comp])
  let p : Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n) ⟶ (thickObj R I e G).left := (x' n).left
  let fa : JetR R (Fin g) n →ₐ[R] JetR (R ⧸ I ^ (e + 1)) (Fin d) n :=
    (ψ.restrictScalars R).comp (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) n)
  let f := fa.toRingHom
  have hp : p ≫ pGl U e = Geo.Tor.spMap f ≫ (xB n).left := by
    have e1 : push hB (x' n ≫ (U.gt e).q) = Chart.spMap fa ≫ xB n := by
      rw [hψ, push_spMap, hxB', ← Category.assoc, Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left) e1)
  have hfa : ∀ s, jetAug _ (Fin d) n (f s) = algebraMap R _ (jetAug R (Fin g) n s) := fun s =>
    AlgHom.congr_fun (jet_ext (ψ₁ := ((jetAug _ (Fin d) n).restrictScalars R).comp fa)
      (ψ₂ := (Algebra.ofId R _).comp (jetAug R (Fin g) n)) fun j => by
        show (jetAug _ (Fin d) n).comp ψ (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) n (zR n j)) =
          algebraMap R _ (jetAug R (Fin g) n (zR n j))
        rw [hψa, jetCoeff_zR, jetAug_zR, jetAug_zR, map_zero]) s
  have hfl : IsLocalHom f := ⟨fun s hs => isUnit_of_aug _ (ker_jetAug_pow (R := R) (Fin g) n)
    (hmk.1 _ (hfa s ▸ hs.map (jetAug _ (Fin d) n)))⟩
  have hfc : Geo.Tor.spMap f (closedPoint _) = closedPoint _ := IsLocalRing.comap_closedPoint f
  choose v hv using fun χ => exists_val_local c hc p (tG U e χ)
  have hv1 : ∀ χ, (val (tG U e χ) p (closedPoint _) (fun ψ => c (ψ (closedPoint _)))).val =
      IntegralJets.germOf (closedPoint _) (v χ).val := fun χ => by
    have := hv χ _ (𝟙 _) _ rfl
    rw [Category.id_comp] at this
    exact this.trans (IntegralJets.germOf_eq _ _).symm
  have hmul : ∀ χ χ', ∃ u : (JetR R (Fin g) n)ˣ, (v (χ + χ')).val * f u = v χ * v χ' := by
    intro χ χ'
    have hJ : Good (Z := Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)) D.toPre.P.L (closedPoint _)
      (fun ψ => c (ψ (closedPoint _))) := fun ψ => hc _
    let m : D.toPre.P.A ⟶ G3 D.toPre.P.A :=
      lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 _))
    obtain ⟨u, hu⟩ := exists_val_local (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) c hc
      ((xB n).left ≫ m.left) D.toPre.cub.t
    have e1 : lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG) = (U.gt e).pG ≫ m := by
      simp only [m, comp_lift, ← Category.assoc, comp_toUnit, Category.comp_id]
    have e2 : p ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
        Geo.Tor.spMap f ≫ (xB n).left ≫ m.left := by
      rw [e1, ← Category.assoc, ← hp, Category.assoc]
      rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') p).trans (val_mul hJ _ _ _))
    have h2 := ((congrArg Units.val ((val_pull hJ _ _ p).trans (congrArg (fun q => val _ q _ _) e2))).trans
      (hu _ _ _ hfc)).trans (cst_spMap f _ _)
    refine ⟨u, (bijective_germOf _).1 ?_⟩
    rw [map_mul, map_mul, ← hv1, ← hv1, ← hv1, ← h2]
    exact congrArg Units.val h
  refine ⟨p, f, v, congrArg (·.left) (hx' n), hp, hfc, hv1, fun N hN => ?_⟩
  let aug := jetAug (R ⧸ I ^ (e + 1)) (Fin d) n
  let w : Fin r → (R ⧸ I ^ (e + 1))ˣ := fun j => Units.map aug.toRingHom.toMonoidHom (v (b j))
  let T : Fin r → JetR (R ⧸ I ^ (e + 1)) (Fin d) n := fun j => algebraMap _ _ (w j)⁻¹.val * v (b j) - 1
  have hconst : ∀ a : R ⧸ I ^ (e + 1), ∃ s, f s = algebraMap _ _ a := fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨algebraMap R _ a, fa.commutes a⟩
  have hker := ker_jetAug_eq _ hk _ r b _ _ _ _ hq (U.gt e).i_hom (U.gt e).isKernel d g n x' xB' hu huB ψ hψ T
    (fun j => by
      simp only [T]
      rw [map_sub, map_mul, AlgHom.commutes, map_one, sub_eq_zero]
      exact (w j).inv_mul) ?_
  · refine eq_top_of_monomials f _ n (ker_jetAug_pow _ _) (fun a => ?_) (fun j => v (b j)) _ hker ?_ N
      fun a ha s => ?_
    · obtain ⟨s, hs⟩ := hconst (aug a)
      exact ⟨s, by rw [hs]; simp [RingHom.mem_ker, aug]⟩
    · rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
      · obtain ⟨s, hs⟩ := hconst (w j)⁻¹.val
        exact Or.inr ⟨j, s, -1, by rw [hs, map_neg, map_one, ← sub_eq_add_neg]⟩
      · exact Or.inl ⟨zR n l, congrArg ψ (jetCoeff_zR n l).symm⟩
    · obtain ⟨u, hu⟩ := exists_unit_prod f v hmul b a
      rw [← hu, mul_comm (v _).val, ← _root_.mul_assoc, ← map_mul]
      exact hN a ha _
  intro φ y hy j
  have hD : IsLocalRing (DualNumber (R ⧸ I ^ (e + 1))) := isLocalRing_of_aug _ (ker_fst_sq _)
  let φ₀ : JetR (R ⧸ I ^ (e + 1)) (Fin d) n →ₐ[R ⧸ I ^ (e + 1)] DualNumber (R ⧸ I ^ (e + 1)) :=
    (Algebra.ofId _ _).comp aug
  have h0 : Chart.spMap φ₀ ≫ x' n = 1 := JetGenerators.spMap_jetAug hu n
  have hJ : Good (Z := Sp (DualNumber (R ⧸ I ^ (e + 1)))) D.toPre.P.L (closedPoint _)
    (fun ψ => c (ψ (closedPoint _))) := fun ψ => hc _
  have h := TorusCoord.val_t_act (U.gt e) y 1 (b j) (𝟙 _) _ _ hJ
  have e1 : 𝟙 _ ≫ ((y ≫ (U.gt e).i) * 1).left = Geo.Tor.spMap φ.toRingHom ≫ p :=
    (Category.id_comp _).trans (congrArg (·.left) ((_root_.mul_one _).trans hy.symm))
  have e2 : 𝟙 _ ≫ (1 : sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ thickObj R I e G).left = Geo.Tor.spMap φ₀.toRingHom ≫ p :=
    (Category.id_comp _).trans (congrArg (·.left) h0.symm)
  replace h := (congrArg (fun q => val (tG U e (b j)) q _ _) e1).symm.trans
    (h.trans (congrArg (fun q => _ * val (tG U e (b j)) q _ _) e2))
  have h1 := (hv (b j) _ _ _ (spMap_closedPoint_dual hk φ)).trans (cst_spMap _ _ _)
  have h2 := (hv (b j) _ _ _ (spMap_closedPoint_dual hk φ₀)).trans (cst_spMap _ _ _)
  let χ : DualNumber (R ⧸ I ^ (e + 1)) := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (R ⧸ I ^ (e + 1))))).hom.hom
    (y.left.appTop.hom (charUnit _ _ (b j)).val)
  have h3 : (gm (𝟙 (Sp (DualNumber (R ⧸ I ^ (e + 1))))) (closedPoint _) ⊤
      (splitTorusPointsEquiv _ D.toPre.X _ y (Multiplicative.ofAdd (b j)))).val =
      IntegralJets.germOf (closedPoint _) χ :=
    (gs_unit _ _ ⊤ trivial _).symm.trans ((congrArg (gs _ _ ⊤) (splitTorusPointsEquiv_val _ _ _ y (b j))).trans
      (IntegralJets.germOf_hom _ _).symm)
  have h4 : φ (v (b j)) = χ * algebraMap _ _ (w j).val := (bijective_germOf _).1
    (h1.symm.trans ((congrArg Units.val h).trans ((congrArg₂ (· * ·) h3 h2).trans (map_mul _ _ _).symm)))
  exact (congrArg _ (one_add_normalised φ _ _ χ h4)).trans (Iso.hom_inv_id_apply _ _)

end Torus

section Main

open Chart ChartBaseChange

theorem expansion_single {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e q : ℕ) (σ : H0 U.LG.L q) (f : ∀ α, D.toPre.SecB q α)
    (hE : U.ExpandsAt e q σ f) {ϖ : R} (hϖ : ϖ ∈ I ^ (e + 1)) (χ : D.toPre.X)
    (hf : ∀ α, α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ (f α) f') {Z : Scheme.{0}}
    (p : Z ⟶ (thickObj R I e G).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) (jL : U.LG.L.ι)
    (hL : fGl I G e (p z) ∈ U.LG.L.U jL) :
    (wv U e p z (J (p ≫ pGl U e)) jL ^ q).val * sv U q σ (p ≫ fGl I G e) z jL =
      sval (f χ) (p ≫ pGl U e) z J * (val (tG U e χ) p z J).val := by
  obtain ⟨S, hS⟩ := expandsAt_val U e q σ f hE
  obtain ⟨h₀, h₁⟩ := hS _ p z J hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫
      Geo.Tor.spMap (Ideal.Quotient.mk (I ^ (e + 1))) := Over.w (U.gt e).pG
  have h0 : cst ((p ≫ pGl U e) ≫ D.toPre.P.A.hom) z ϖ = 0 := by
    rw [Category.assoc, hc, ← Category.assoc, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2 hϖ, cst, map_zero]
    exact gs_zero _ _ _ trivial
  refine (h₁ jL hL).trans (Finset.sum_eq_single χ (fun α _ hα => ?_) fun hχ => by rw [h₀ χ hχ, zero_mul])
  obtain ⟨f', hf'⟩ := hf α hα
  have : sval (f α) (p ≫ pGl U e) z J = 0 :=
    (secIsMul_gs hf' (p ≫ pGl U e) z _ (hJ.mem _ _)).trans (by rw [h0, zero_mul])
  rw [this, zero_mul]

theorem small_characters_span_jets : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ D.toPre.X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) → (∀ j z, |(QForm.bOf D.toPre Q (b j) z : ℝ)| ≤ M₀ * Q z) → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∀ (d : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := V) (Chart.JetR V (Fin d) m) ⟶ G), Chart.IsUnivChart G d x → ∀ τ : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (x n).left ≫ 𝟙 G.left) (fun _ => (q : ℤ))), τ.IsGen → ∃ (l : ℕ) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α) (χ : Fin l → D.toPre.X) (a : Fin l → Chart.JetR V (Fin d) n), (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ (∀ i, ∃ Φ : Fam D.toPre (FractionRing V) q, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f i α) (DegPre.prB D.toPre (FractionRing V)).left 1)) ∧ (∀ i, (Q (χ i) : ℝ) ≤ (n : ℝ) ^ 2 * Cc) ∧ (∀ i α, (∀ z, α ≠ χ i + q • z) → ∀ j, (f i α).f j = 0) ∧ (∀ i, (∀ (z : (Chart.sp (R₀ := V) (Chart.JetR V (Fin d) n)).left) (J), Good U.LG.L z J → sval (σ i) (x n).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Chart.JetR V (Fin d) n))).inv.hom (a i)) * (val τ (𝟙 _) z J).val)) ∧ Submodule.span V (Set.range a) = ⊤ := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U Q hQ r b Cc M₀ hC hM hb hB q n hq hn d x hx τ hτ
  classical
  let admitted : JetR V (Fin d) n → Prop := fun a => ∃ (σ : H0 U.LG.L q) (f : ∀ α, D.toPre.SecB q α) (χ : D.toPre.X),
    (∀ e, U.ExpandsAt e q σ f) ∧ (∃ Φ : Fam D.toPre (FractionRing V) q, ∀ α, GeneratorPullback.SecScal D.toPre.P.L
      (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α)
      (DegPre.prB D.toPre (FractionRing V)).left 1) ∧ (Q χ : ℝ) ≤ (n : ℝ) ^ 2 * Cc ∧
    (∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0) ∧
    ∀ (z : (sp (R₀ := V) (JetR V (Fin d) n)).left) (J), Good U.LG.L z J → sval σ (x n).left z J =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).inv.hom a) * (val τ (𝟙 _) z J).val
  suffices h : Submodule.span V {a | admitted a} = ⊤ by
    have := finite_jet V d n
    obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (h ▸ Module.Finite.fg_top)
    choose σ f χ h1 h2 h3 h4 h5 using fun i : Fin s.card => hs (s.equivFin.symm i).2
    refine ⟨s.card, σ, f, χ, fun i => (s.equivFin.symm i).1, h1, h2, h3, h4, h5, ?_⟩
    rw [← h, e]
    congr 1
    ext a
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (s.equivFin.symm i).2, fun ha => ⟨s.equivFin ⟨a, ha⟩, by simp⟩⟩
  have hk : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (by rw [zero_add, pow_one]; infer_instance)
  have hloc : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) := by letI := hk.toField; infer_instance
  have := D.toPre.P.isAb.smooth
  obtain ⟨g, xB, hxB⟩ := univChartLoc D.toPre.P.A
  have hl1 : IsLocalRing (JetR (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n) := isLocalRing_of_aug _ (ker_jetAug_pow _ _)
  have hl2 : IsLocalRing (JetR V (Fin g) n) := isLocalRing_of_aug _ (ker_jetAug_pow _ _)
  choose c hc using fun y : D.toPre.P.A.left => Geo.Tor.exists_chart D.toPre.P.isLB y
  obtain ⟨p, f, v, hp1, hp2, hfc, hv, hN⟩ := torus_jets U.toUnifPre 0 hk c hc n x hx xB hxB b
  let ρ := jetCoeff V (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n
  let z₀ : Sp (JetR (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n) := closedPoint _
  have hJ : Good D.toPre.P.L z₀ (fun ψ => c (ψ z₀)) := fun ψ => hc _
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' U.LG.isLB z₀
  let jL := J' ((Geo.Tor.spMap ρ.toRingHom ≫ (x n).left) ≫ 𝟙 _)
  have hjL : fGl (maximalIdeal V) G 0 (p z₀) ∈ U.LG.L.U jL :=
    (congrArg (fun m => m z₀ ∈ U.LG.L.U jL) (hp1.trans (Category.comp_id _).symm)).mpr (hJ' _)
  obtain ⟨w, hw⟩ := (bijective_germOf _).2 (wv U.toUnifPre 0 p z₀ (c ((p ≫ pGl U.toUnifPre 0) z₀)) jL ^ q *
    val τ (Geo.Tor.spMap ρ.toRingHom) z₀ J').val
  have hwu : IsUnit w := by
    have : IsLocalHom (IntegralJets.germOf z₀) := IsLocalHom.of_surjective _ (bijective_germOf _).2
    exact this.1 w ((congrArg IsUnit hw).mpr (Units.isUnit _))
  have key : ∀ a : Fin r → ℕ, ∑ j, a j ≤ n → ∀ s, ∃ y, admitted y ∧ w * ρ y = f s * v (∑ j, a j • b j) := by
    intro a ha s
    obtain ⟨hQ1, hQ2⟩ := small_combination_strict_min_mod _ (QForm.bHom hϖ D hQ) Q (QForm.bOf_comm D)
      (QForm.two_Q_eq hϖ D hQ) (fun _ => QForm.Q_pos hϖ D hQ) r n q b Cc M₀ hC hM hb hB hn a ha
    generalize ∑ j, a j • b j = χ at hQ1 hQ2
    obtain ⟨t, ht⟩ := exists_gen_of_local (V := JetR V (Fin g) n) D.toPre.P.L D.toPre.P.isLB
      (fun i => (xB n).left ≫ D.toPre.famφB χ i) (DegPre.famε q)
    obtain ⟨u, hu⟩ := exists_val_local c hc (𝟙 _) t
    have hu1 := (congrArg (fun m => (val t m z₀ _).val) (Category.comp_id _).symm).trans
      ((hu _ (Geo.Tor.spMap f) z₀ hfc).trans (cst_spMap f _ _))
    obtain ⟨β, hβ⟩ := IntegralJets.integral_jets hL hTW V D.toPre q n hq χ g xB hxB t ht (s * u⁻¹.val)
    obtain ⟨Φ, F, hF1, hF2, hF3, hF4⟩ := integralFamily_of_strictMin hL V ϖ hϖ D Q hQ q (by omega) χ β hQ2
    obtain ⟨σ, hσ⟩ := IntegralExpansion.main hL V D A G U q (by omega) Φ F hF1
    obtain ⟨y, hy⟩ := IntegralJets.exists_ratio U.LG.isLB σ (x n).left τ hτ
    let y' : JetR V (Fin d) n := (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).hom.hom y
    have hy' : (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).inv.hom y' = y := Iso.hom_inv_id_apply _ _
    refine ⟨y', ⟨σ, F, χ, hσ, ⟨Φ, hF1⟩, hQ1, hF3, fun z J h => hy'.symm ▸ hy z J h⟩, (bijective_germOf _).1 ?_⟩
    have e1 := expansion_single U.toUnifPre 0 q σ F (hσ 0)
      (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hϖ.not_isUnit) (0 + 1)) χ (fun α hα => by
        rw [zero_add, pow_one]; exact hF4 α hα) p z₀ hJ jL hjL
    have e2 : sv U.toUnifPre q σ (p ≫ fGl (maximalIdeal V) G 0) z₀ jL =
        IntegralJets.germOf z₀ (ρ y') * (val τ (Geo.Tor.spMap ρ.toRingHom) z₀ J').val :=
      (congrArg (fun m => sv U.toUnifPre q σ m z₀ jL) hp1).trans
        ((sval_pull_of_ratio U.LG.isLB σ (x n).left τ hτ y hy (Geo.Tor.spMap ρ.toRingHom) z₀ hJ').trans
          (congrArg (· * _) ((congrArg (gs _ z₀ ⊤) hy'.symm).trans (cst_spMap ρ.toRingHom z₀ y'))))
    have e3 : sval (F χ) (p ≫ pGl U.toUnifPre 0) z₀ (fun ψ => c (ψ z₀)) = IntegralJets.germOf z₀ (f s) :=
      (congrArg₂ (fun σ m => sval σ m z₀ _) hF2 hp2).trans
        ((sval_pull_of_ratio D.toPre.P.isLB β (xB n).left t ht _ hβ (Geo.Tor.spMap f) z₀ hJ).trans
          ((congrArg₂ (· * ·) (cst_spMap f z₀ _) hu1).trans (by
            rw [← map_mul, ← map_mul, Units.inv_mul_cancel_right])))
    have e4 := (congrArg (_ * ·) e2).symm.trans (e1.trans (congrArg₂ (· * ·) e3 (hv χ)))
    refine (map_mul _ _ _).trans (Eq.trans ?_ (e4.trans (map_mul _ _ _).symm))
    exact (congrArg (· * _) (hw.trans (Units.val_mul _ _))).trans
      ((mul_right_comm _ _ _).trans (_root_.mul_assoc _ _ _))
  refine eq_top_of_jetCoeff (maximalIdeal V ^ (0 + 1)) (Ideal.pow_le_self (by omega)) d n _ fun y => ?_
  have htop := hN ((Submodule.span V {a | admitted a}).toAddSubgroup.map
    ((AddMonoidHom.mulLeft w).comp ρ.toRingHom.toAddMonoidHom)) fun a ha s => by
      obtain ⟨y, h1, h2⟩ := key a ha s
      exact ⟨y, Submodule.subset_span h1, h2⟩
  obtain ⟨a, ha, e⟩ : w * y ∈ _ := htop.ge (AddSubgroup.mem_top _)
  exact ⟨a, ha, hwu.mul_left_cancel e⟩

end Main

end GlobalTheory.SmallJets
end
end
