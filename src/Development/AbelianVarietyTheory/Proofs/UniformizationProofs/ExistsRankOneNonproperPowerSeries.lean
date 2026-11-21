import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointEquivSmoothLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftMulHomPullbackFst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt

section
open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace GlobalTheory

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def pderivClass (j : Fin 3) : HomRing W :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial)

theorem pderivClass_mem (j : Fin 3) : pderivClass W j ∈ grading W 2 :=
  ⟨_, (isHomogeneous_polynomial W).pderiv, rfl⟩

def pderivOpen (j : Fin 3) : (scheme W).Opens := Proj.basicOpen (grading W) (pderivClass W j)

theorem ptHom_preimage_pderivOpen {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (h : IsUnimodularSol (W.map ρ) P) (j : Fin 3) :
    ptHom W ρ P h ⁻¹ᵁ pderivOpen W j = PrimeSpectrum.basicOpen
      (MvPolynomial.eval₂ ρ P (MvPolynomial.pderiv j W.toProjective.polynomial)) :=
  ProjPoint.ofHom_preimage_basicOpen (grading W) _ _ two_pos (pderivClass_mem W j)

def smoothOpen : (scheme W).Opens :=
  ⨆ p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}, coordOpen W p.1.1 ⊓ pderivOpen W p.1.2

theorem nonsingular_iff_exists_pderiv {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} (h : IsUnimodularSol V P) :
    V.toProjective.Nonsingular P ↔ ∃ i j : Fin 3, j ≠ i ∧ P i ≠ 0 ∧
      MvPolynomial.eval P (MvPolynomial.pderiv j V.toProjective.polynomial) ≠ 0 := by
  set D : Fin 3 → k := fun j =>
    MvPolynomial.eval P (MvPolynomial.pderiv j V.toProjective.polynomial) with hD
  change (_ ∧ (D 0 ≠ 0 ∨ D 1 ≠ 0 ∨ D 2 ≠ 0)) ↔ ∃ i j : Fin 3, j ≠ i ∧ P i ≠ 0 ∧ D j ≠ 0
  constructor
  · rintro ⟨-, hns⟩
    obtain ⟨i, hi⟩ : ∃ i, P i ≠ 0 := by
      by_contra! h0
      have := h.span_eq_top
      rw [Ideal.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; exact h0 i)] at this
      exact bot_ne_top this
    by_contra! hc
    have hj : ∀ j, j ≠ i → D j = 0 := fun j hj => hc i j hj hi
    have euler : 3 * _ = P 0 * D 0 + P 1 * D 1 + P 2 * D 2 := V.toProjective.polynomial_relation P
    have h0 : MvPolynomial.eval P V.toProjective.polynomial = 0 := h.equation
    rw [h0, mul_zero, ← Fin.sum_univ_three
      (fun j => P j * D j), Finset.sum_eq_single i (fun j _ h => by rw [hj j h, mul_zero])
      (by simp)] at euler
    have hall : ∀ j, D j = 0 := fun j => by
      by_cases h : j = i
      · exact h ▸ (mul_eq_zero.mp euler.symm).resolve_left hi
      · exact hj j h
    rcases hns with h | h | h
    exacts [h (hall 0), h (hall 1), h (hall 2)]
  · rintro ⟨i, j, -, -, hj⟩
    refine ⟨h.equation, ?_⟩
    fin_cases j
    exacts [Or.inl hj, Or.inr (Or.inl hj), Or.inr (Or.inr hj)]

theorem top_le_ptHom_preimage_smoothOpen_iff {k : Type u} [Field k] (ρ : R →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol (W.map ρ) P) :
    ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ smoothOpen W ↔ (W.map ρ).toProjective.Nonsingular P := by
  have e : (W.map ρ).toProjective.polynomial = MvPolynomial.map ρ W.toProjective.polynomial :=
    WeierstrassCurve.Projective.map_polynomial ..
  have hb : ∀ (x : PrimeSpectrum k) (a : k), x ∈ PrimeSpectrum.basicOpen a ↔ a ≠ 0 := by
    intro x a
    rw [PrimeSpectrum.mem_basicOpen, Ideal.eq_bot_of_prime x.asIdeal, Ideal.mem_bot]
  rw [nonsingular_iff_exists_pderiv h, e, smoothOpen, Scheme.Hom.preimage_iSup]
  simp only [MvPolynomial.pderiv_map, MvPolynomial.eval_map, Scheme.Hom.preimage_inf,
    ptHom_preimage_coordOpen, ptHom_preimage_pderivOpen]
  constructor
  · intro H
    obtain ⟨⟨⟨i, j⟩, hij⟩, h1, h2⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (H (Set.mem_univ (⟨⊥, inferInstance⟩ : PrimeSpectrum k)))
    exact ⟨i, j, hij, (hb _ _).mp h1, (hb _ _).mp h2⟩
  · rintro ⟨i, j, hij, h1, h2⟩ x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨i, j⟩, hij⟩, (hb _ _).mpr h1, (hb _ _).mpr h2⟩

abbrev PderivRing (i j : Fin 3) : Type u :=
  Localization.Away
    (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)

def pderivChart (i j : Fin 3) : Spec (.of (PderivRing W i j)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (DehomRing W i) (PderivRing W i j))) ≫ dehomChart W i

instance (i j : Fin 3) : IsOpenImmersion (pderivChart W i j) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (DehomRing W i) (PderivRing W i j)))) :=
    IsOpenImmersion.of_isLocalization
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)
  unfold pderivChart
  infer_instance

theorem range_pderivChart (i j : Fin 3) :
    Set.range (pderivChart W i j) = (coordOpen W i ⊓ pderivOpen W j : (scheme W).Opens) := by
  have hp : dehomChart W i ⁻¹ᵁ pderivOpen W j = PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i) := by
    rw [← eval₂_dehomCoord]
    exact ptHom_preimage_pderivOpen W _ _
      (.of_isUnit (equation_dehomCoord W i) i (by simp)) j
  have hr := PrimeSpectrum.localization_away_comap_range (PderivRing W i j)
    (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)
  rw [← hp] at hr
  rw [← opensRange_dehomChart]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [pderivChart, Scheme.Hom.comp_apply]
    exact ⟨⟨_, rfl⟩, hr.le ⟨y, rfl⟩⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    obtain ⟨z, rfl⟩ := hr.ge hy
    exact ⟨z, Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom
      (algebraMap (DehomRing W i) (PderivRing W i j)))) (dehomChart W i) z⟩

theorem coe_smoothOpen : (smoothOpen W : Set (scheme W)) =
    ⋃ p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}, Set.range (pderivChart W p.1.1 p.1.2) := by
  simp only [smoothOpen, TopologicalSpace.Opens.coe_iSup, range_pderivChart]

instance smoothOfRelativeDimension_smoothOpen :
    SmoothOfRelativeDimension 1 ((smoothOpen W).ι ≫ toSpec W) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} 1)
  have hr (p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) :
      Set.range (pderivChart W p.1.1 p.1.2) ⊆ Set.range (smoothOpen W).ι := by
    rw [Scheme.Opens.range_ι, coe_smoothOpen]
    exact Set.subset_iUnion (fun p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1} =>
      Set.range (pderivChart W p.1.1 p.1.2)) p
  let f (p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) :=
    IsOpenImmersion.lift (smoothOpen W).ι (pderivChart W p.1.1 p.1.2) (hr p)
  have hf (p) : f p ≫ (smoothOpen W).ι = pderivChart W p.1.1 p.1.2 := IsOpenImmersion.lift_fac ..
  have hi (p) : IsOpenImmersion (f p) := by
    have : IsOpenImmersion (f p ≫ (smoothOpen W).ι) := by
      rw [hf]
      infer_instance
    exact .of_comp _ (smoothOpen W).ι
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (Scheme.Cover.mkOfCovers (ULift.{u} {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) _ (fun p => f p.down)
      fun x => ?_) fun (p : ULift.{u} {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) => ?_
  · have hx : (smoothOpen W).ι x ∈ (smoothOpen W : Set (scheme W)) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    rw [coe_smoothOpen] at hx
    obtain ⟨p, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨⟨p⟩, y, (smoothOpen W).ι.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hf, hy]
  · change SmoothOfRelativeDimension 1 (f p.down ≫ (smoothOpen W).ι ≫ toSpec W)
    rw [← Category.assoc, hf, pderivChart, Category.assoc, dehomChart_toSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
    rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact isStandardSmoothOfRelativeDimension_away_pderiv W p.down.2 _

instance quasiCompact_smoothOpen : QuasiCompact ((smoothOpen W).ι ≫ toSpec W) := by
  have hc : IsCompact (smoothOpen W : Set (scheme W)) := by
    rw [coe_smoothOpen]
    exact isCompact_iUnion fun p => isCompact_range (pderivChart W p.1.1 p.1.2).continuous
  have : CompactSpace (smoothOpen W).toScheme := isCompact_iff_compactSpace.mp hc
  exact quasiCompact_of_compactSpace _

instance geometricallyIntegral_smoothOpen :
    GeometricallyIntegral ((smoothOpen W).ι ≫ toSpec W) := by
  refine ⟨geometrically_iff_of_commRing.mpr fun K _ _ Y fst snd h => ?_⟩
  have hb := isPullback_mapHom W (algebraMap R K) rfl
  let g : Y ⟶ scheme (W.map (algebraMap R K)) :=
    hb.lift (fst ≫ (smoothOpen W).ι) snd (by rw [Category.assoc]; exact h.w)
  have hg : g ≫ toSpec _ = snd := hb.lift_snd ..
  have hp : IsPullback fst g (smoothOpen W).ι (mapHom W (algebraMap R K) rfl) :=
    IsPullback.of_bot (by rw [hg]; exact h) (hb.lift_fst ..).symm hb
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp
    inferInstance
  have hz : Set.range (ptHom W (algebraMap R K) ![0, 1, 0] (isUnimodularSol_zero _)) ⊆
      Set.range (smoothOpen W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (top_le_ptHom_preimage_smoothOpen_iff W (algebraMap R K) ![0, 1, 0]
      (isUnimodularSol_zero _)).mpr WeierstrassCurve.Projective.nonsingular_zero (Set.mem_univ x)
  let s : Spec (.of K) ⟶ Y := h.lift (IsOpenImmersion.lift _ _ hz) (𝟙 _)
    (by rw [IsOpenImmersion.lift_fac_assoc, ptHom_toSpec, Category.id_comp])
  have : Nonempty Y := ⟨s (Classical.arbitrary (PrimeSpectrum K))⟩
  exact isIntegral_of_isOpenImmersion g

theorem exists_smoothLocus (R : Type) [CommRing R] (W : WeierstrassCurve R) :
    ∃ U : (scheme W).Opens, (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k)
      (h : IsUnimodularSol (W.map ρ) P),
        ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ toSpec W) ∧ QuasiCompact (U.ι ≫ toSpec W) ∧
      GeometricallyIntegral (U.ι ≫ toSpec W) :=
  ⟨smoothOpen W, fun _ _ ρ P h => top_le_ptHom_preimage_smoothOpen_iff W ρ P h,
    inferInstance, inferInstance, inferInstance⟩

end WeierstrassCurve

end GlobalTheory
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NodalCubic

open WeierstrassCurve WeierstrassCurve.Projective in
theorem addXYZ_param {k : Type} [Field k] (u v : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.addXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3] ![v * (1 - v), v ^ 2, (1 - v) ^ 3]
      = (u - v) ^ 3 • ![(u * v) * (1 - u * v), (u * v) ^ 2, (1 - u * v) ^ 3] := by
  ext i
  fin_cases i <;>
    simp [addXYZ, addX, addY, addZ, negAddY, negY] <;> ring

open WeierstrassCurve WeierstrassCurve.Projective in
theorem dblXYZ_param {k : Type} [Field k] (u : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.dblXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3]
      = u ^ 3 • ![(u * u) * (1 - u * u), (u * u) ^ 2, (1 - u * u) ^ 3] := by
  ext i
  fin_cases i <;>
    simp [dblXYZ, dblX, dblY, dblZ, negDblY, negY] <;> ring

theorem eq_of_param_equiv {k : Type} [Field k] {u v : k} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∃ c : kˣ, c • ![v * (1 - v), v ^ 2, (1 - v) ^ 3] = ![u * (1 - u), u ^ 2, (1 - u) ^ 3]) :
    u = v := by
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp [Units.smul_def] at h0 h1
  have h2 : (c : k) * v = u := by linear_combination h0 + h1
  have h3 : u * v = u * u := by linear_combination h1 - v * h2
  exact (mul_left_cancel₀ hu h3).symm

open WeierstrassCurve WeierstrassCurve.Projective in
theorem nonsingular_iff_nodal {k : Type} [Field k] (P : Fin 3 → k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P ↔
      P 1 ^ 2 * P 2 + P 0 * P 1 * P 2 = P 0 ^ 3 ∧
        (P 1 * P 2 ≠ 3 * P 0 ^ 2 ∨ 2 * P 1 * P 2 + P 0 * P 2 ≠ 0 ∨ P 1 ^ 2 + P 0 * P 1 ≠ 0) := by
  rw [nonsingular_iff, equation_iff]
  simp [sub_eq_zero]

theorem nonsingular_points : ∀ (k : Type) [Field k], (∀ u : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3]) ∧ (∀ u v : kˣ, ∃ c : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.add ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3] ![(v : k) * (1 - v), (v : k) ^ 2, (1 - (v : k)) ^ 3] = (c : k) • ![((u * v : kˣ) : k) * (1 - (u * v : kˣ)), ((u * v : kˣ) : k) ^ 2, (1 - ((u * v : kˣ) : k)) ^ 3]) ∧ ∀ P : Fin 3 → k, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P → P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ ∃ c : kˣ, P = (c : k) • ![(P 1 / (P 0 + P 1)) * (1 - P 1 / (P 0 + P 1)), (P 1 / (P 0 + P 1)) ^ 2, (1 - P 1 / (P 0 + P 1)) ^ 3] := by
  intro k _
  refine ⟨fun u => ?_, fun u v => ?_, fun P hP => ?_⟩
  · rw [nonsingular_iff_nodal]
    refine ⟨by simp; ring, Or.inr (Or.inr ?_)⟩
    have : ((u : k) ^ 2) ^ 2 + (u : k) * (1 - u) * (u : k) ^ 2 = (u : k) ^ 3 := by ring
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, this]
    exact pow_ne_zero 3 u.ne_zero
  · by_cases h : (u : k) = v
    · refine ⟨u ^ 3, ?_⟩
      rw [Units.val_mul, ← h, WeierstrassCurve.Projective.add_self, dblXYZ_param, Units.val_pow_eq_pow_val]
    · refine ⟨Units.mk0 (((u : k) - v) ^ 3) (pow_ne_zero 3 (sub_ne_zero.mpr h)), ?_⟩
      rw [WeierstrassCurve.Projective.add_of_not_equiv
        (fun h' => h (eq_of_param_equiv u.ne_zero v.ne_zero h')), addXYZ_param, Units.val_mul, Units.val_mk0]
  · rw [nonsingular_iff_nodal] at hP
    obtain ⟨he, hn⟩ := hP
    have key : P 1 * (P 0 + P 1) ≠ 0 := by
      intro h0
      have hx : P 0 = 0 := by
        have : P 0 ^ 3 = 0 := by linear_combination P 2 * h0 - he
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hy : P 1 = 0 := by
        rw [hx, zero_add] at h0
        exact mul_self_eq_zero.mp h0
      simp [hx, hy] at hn
    have hy : P 1 ≠ 0 := left_ne_zero_of_mul key
    have hs : P 0 + P 1 ≠ 0 := right_ne_zero_of_mul key
    refine ⟨hy, hs, Units.mk0 ((P 0 + P 1) ^ 2 / P 1) (div_ne_zero (pow_ne_zero 2 hs) hy), ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      ring
    · simp
      field_simp
    · simp
      field_simp
      linear_combination he

end GlobalTheory.NodalCubic
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NodalCubic

open GlobalTheory.WeierstrassCurve

noncomputable def evalAt {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    Γ(Z, ⊤) →+* k := (x.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom

theorem comp_toSpecΓ {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    x ≫ Z.toSpecΓ = Spec.map (CommRingCat.ofHom (evalAt x)) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

theorem evalAt_comp {Z Z' : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z)
    (f : Z ⟶ Z') (s : Γ(Z', ⊤)) : evalAt (x ≫ f) s = evalAt x (f.appTop.hom s) := by
  simp [evalAt]
  rfl

theorem evalAt_specMap {A : CommRingCat.{0}} {k : Type} [CommRing k] (φ : A ⟶ .of k) (a : A) :
    evalAt (Spec.map φ) ((Scheme.ΓSpecIso A).inv.hom a) = φ.hom a := by
  rw [evalAt, Scheme.ΓSpecIso_naturality]
  simp

theorem isUnit_of_forall_evalAt {Z : Scheme.{0}} (s : Γ(Z, ⊤))
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Z), evalAt x s ≠ 0) : IsUnit s := by
  apply RingedSpace.isUnit_of_isUnit_germ Z.toRingedSpace ⊤ s
  intro z hz
  have h1 : IsUnit ((Z.fromSpecResidueField z).appTop.hom s) :=
    (isUnit_map_iff (Scheme.ΓSpecIso (Z.residueField z)).commRingCatIsoToRingEquiv _).mp
      (Ne.isUnit (h _ (Z.fromSpecResidueField z)))
  have h3 : (Z.fromSpecResidueField z) ⁻¹ᵁ Z.basicOpen s = ⊤ := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h1]
  have h4 : (Z.fromSpecResidueField z) default ∈ Z.basicOpen s :=
    h3.ge (Set.mem_univ _)
  rw [Scheme.fromSpecResidueField_apply] at h4
  exact (Z.mem_basicOpen_top s z).mp h4

section Torus

variable {S : Scheme.{0}} {Z : Over S}

noncomputable def unitOf (t : Z ⟶ splitTorus S ℤ) : Γ(Z.left, ⊤)ˣ :=
  splitTorusPointsEquiv S ℤ Z t (Multiplicative.ofAdd 1)

theorem unitOf_mul (a b : Z ⟶ splitTorus S ℤ) : unitOf (a * b) = unitOf a * unitOf b := by
  simp [unitOf]

theorem unitOf_injective : Function.Injective (unitOf : (Z ⟶ splitTorus S ℤ) → _) :=
  fun _ _ h => (splitTorusPointsEquiv S ℤ Z).injective (MonoidHom.ext_mint h)

theorem unitOf_surjective : Function.Surjective (unitOf : (Z ⟶ splitTorus S ℤ) → _) :=
  fun u => ⟨(splitTorusPointsEquiv S ℤ Z).symm (zpowersHom _ u), by simp [unitOf]⟩

theorem unitOf_comp {Z' : Over S} (x : Z' ⟶ Z) (t : Z ⟶ splitTorus S ℤ) :
    (unitOf (x ≫ t)).val = x.left.appTop.hom (unitOf t).val := by
  simp [unitOf, splitTorusPointsEquiv_val]
  rfl

noncomputable def valOf {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}
    (t : Over.mk s ⟶ splitTorus S ℤ) : kˣ :=
  Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom (unitOf t)

variable {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}

theorem valOf_mul (a b : Over.mk s ⟶ splitTorus S ℤ) : valOf (a * b) = valOf a * valOf b := by
  rw [valOf, unitOf_mul, map_mul]; rfl

theorem valOf_injective : Function.Injective (valOf : (Over.mk s ⟶ splitTorus S ℤ) → kˣ) :=
  fun _ _ h => unitOf_injective (Units.map_injective
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective h)

theorem valOf_comp (x : Over.mk s ⟶ Z) (t : Z ⟶ splitTorus S ℤ) :
    (valOf (x ≫ t) : k) = evalAt x.left (unitOf t).val := by
  change (Scheme.ΓSpecIso (.of k)).hom.hom (unitOf (x ≫ t)).val = _
  rw [unitOf_comp]
  rfl

end Torus

def param {A : Type} [CommRing A] (u : A) : Fin 3 → A := ![u * (1 - u), u ^ 2, (1 - u) ^ 3]

abbrev node (K : Type) [CommRing K] : WeierstrassCurve K := ⟨1, 0, 0, 0, 0⟩

theorem node_map {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) :
    (node K).map ρ = node A := by
  ext <;> simp

theorem comp_param {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (u : A) :
    g ∘ param u = param (g u) := by
  ext i
  fin_cases i <;> simp [param]

theorem isUnimodularSol_param {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) (u : Aˣ) :
    IsUnimodularSol ((node K).map ρ) (param (u : A)) := by
  refine .of_isUnit ?_ 1 (u.isUnit.pow 2)
  rw [node_map, WeierstrassCurve.Projective.equation_iff]
  simp [param]
  ring

variable (K : Type) [Field K]

noncomputable def constHom (Z : Over (Spec (.of K))) : K →+* Γ(Z.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ Z.hom.appTop).hom

theorem toSpecΓ_constHom (Z : Over (Spec (.of K))) :
    Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (constHom K Z)) = Z.hom := by
  rw [constHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp]
  simp

noncomputable def paramHom : (splitTorus (Spec (.of K)) ℤ).left ⟶ scheme (node K) :=
  (splitTorus (Spec (.of K)) ℤ).left.toSpecΓ ≫
    ptHom (node K) (constHom K _) (param (unitOf (𝟙 _)).val) (isUnimodularSol_param _ _)

theorem paramHom_toSpec : paramHom K ≫ toSpec (node K) = (splitTorus (Spec (.of K)) ℤ).hom := by
  rw [paramHom, Category.assoc, ptHom_toSpec, toSpecΓ_constHom]

variable {K}

theorem comp_paramHom {k : Type} [CommRing k] {ρ : K →+* k}
    (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ) :
    x.left ≫ paramHom K = ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := by
  have e := comp_toSpecΓ (k := k) x.left
  have e2 : (evalAt (k := k) x.left).comp (constHom K _) = ρ := by
    have : Spec.map (CommRingCat.ofHom ((evalAt (k := k) x.left).comp (constHom K _))) =
        Spec.map (CommRingCat.ofHom ρ) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← e]
      exact (Category.assoc _ _ _).trans
        ((congrArg (x.left ≫ ·) (toSpecΓ_constHom K _)).trans (Over.w x))
    exact congrArg (·.hom) (Spec.map_injective this)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
  rw [SpecMap_ptHom]
  refine ptHom_congr _ _ _ _ e2 ?_ _
  rw [comp_param, ← valOf_comp, Category.comp_id]

theorem exists_over_point {Z : Over (Spec (.of K))} {k : Type} [CommRing k]
    (x : Spec (.of k) ⟶ Z.left) :
    ∃ (ρ : K →+* k) (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Z), y.left = x :=
  ⟨(Spec.preimage (x ≫ Z.hom)).hom, Over.homMk x (by simp), rfl⟩

theorem range_subset_of_forall_field {Z Y : Scheme.{0}} (f : Z ⟶ Y) (V : Y.Opens)
    (h : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Z), ⊤ ≤ (x ≫ f) ⁻¹ᵁ V) :
    Set.range f ⊆ V := by
  rintro _ ⟨z, rfl⟩
  have := h _ (Z.fromSpecResidueField z) (Set.mem_univ default)
  have h2 : f ((Z.fromSpecResidueField z) default) ∈ V := this
  rwa [Scheme.fromSpecResidueField_apply] at h2

theorem over_hom_ext_field {T Y : Over (Spec (.of K))} [IsReduced T.left] [IsSeparated Y.hom]
    {f g : T ⟶ Y} (h : ∀ (k : Type) [Field k] (ρ : K →+* k)
      (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ T), x ≫ f = x ≫ g) : f = g :=
  over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => h k _ x

section Locus

variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)

include hU

theorem exists_toLocus : ∃ f : splitTorus (Spec (.of K)) ℤ ⟶ Over.mk (U.ι ≫ toSpec (node K)),
    f.left ≫ U.ι = paramHom K := by
  have h : Set.range (paramHom K) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point x
    rw [comp_paramHom, hU, node_map]
    exact (nonsingular_points k).1 _
  have e := IsOpenImmersion.lift_fac U.ι (paramHom K) h
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι (paramHom K) h) ?_, e⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (paramHom_toSpec K))

theorem exists_nonsingular {k : Type} [Field k] {ρ : K →+* k}
    (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K))) :
    ∃ (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h ∧ (node k).toProjective.Nonsingular P := by
  obtain ⟨P, h, e⟩ := exists_eq_ptHom (node K) ρ (y.left ≫ U.ι)
    ((Category.assoc _ _ _).trans (Over.w y))
  refine ⟨P, h, e, ?_⟩
  rw [← node_map ρ, ← hU k ρ P h, ← e]
  intro z _
  exact (y.left z).2

theorem exists_fromLocus : ∃ g : Over.mk (U.ι ≫ toSpec (node K)) ⟶ splitTorus (Spec (.of K)) ℤ,
    ∀ (k : Type) [Field k] (ρ : K →+* k)
      (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K)))
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h → (valOf (y ≫ g) : k) = P 1 / (P 0 + P 1) := by
  have h : Set.range U.ι ⊆ Set.range (awayChart (node K) 1) := by
    rw [← (awayChart (node K) 1).coe_opensRange, opensRange_awayChart]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    have h1 := ((nonsingular_points k).2.2 P hn).1
    refine le_of_eq (Eq.symm ?_)
    refine (congrArg (· ⁻¹ᵁ _) e).trans ?_
    rw [ptHom_preimage_coordOpen]
    exact top_le_iff.mp fun p _ hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp h1.isUnit)
  let j := IsOpenImmersion.lift (awayChart (node K) 1) U.ι h
  have hj : j ≫ awayChart (node K) 1 = U.ι := IsOpenImmersion.lift_fac _ _ h
  let s : Γ(U.toScheme, ⊤) := j.appTop.hom ((Scheme.ΓSpecIso (.of (AwayRing (node K) 1))).inv.hom
    (awayCoord (node K) 1 0 + 1))
  have key : ∀ (k : Type) [Field k] (ρ : K →+* k) (x : Spec (.of k) ⟶ U.toScheme)
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      x ≫ U.ι = ptHom (node K) ρ P h →
        P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ evalAt x s * P 1 = P 0 + P 1 := by
    intro k _ ρ x P hP e
    have hn : (node k).toProjective.Nonsingular P := by
      rw [← node_map ρ, ← hU k ρ P hP, ← e]
      intro z _
      exact (x z).2
    obtain ⟨h1, h2, -⟩ := (nonsingular_points k).2.2 P hn
    refine ⟨h1, h2, ?_⟩
    have e2 : x ≫ j = Spec.map (CommRingCat.ofHom
        (awayEval (node K) 1 ρ P hP.equation h1.isUnit)) := by
      rw [← cancel_mono (awayChart (node K) 1), Category.assoc, hj, e,
        ptHom_eq_awayChart _ 1 _ _ _ h1.isUnit]
    rw [← evalAt_comp, e2, evalAt_specMap, CommRingCat.hom_ofHom, map_add, map_one, add_mul,
      awayEval_awayCoord_mul, _root_.one_mul]
  have hs : IsUnit s := by
    refine isUnit_of_forall_evalAt s fun k _ x h0 => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, -⟩ := exists_nonsingular U hU y
    obtain ⟨-, h2, h3⟩ := key k ρ y.left P hP e
    exact h2 (by rw [← h3]; exact mul_eq_zero_of_left h0 _)
  obtain ⟨g, hg⟩ := unitOf_surjective (Z := Over.mk (U.ι ≫ toSpec (node K))) hs.unit⁻¹
  refine ⟨g, fun k _ ρ y P hP e => ?_⟩
  obtain ⟨h1, h2, h3⟩ := key k ρ y.left P hP e
  have h4 : evalAt (k := k) y.left (unitOf g).val * evalAt (k := k) y.left s = 1 := by
    rw [hg]
    exact (map_mul _ _ _).symm.trans ((congrArg _ hs.val_inv_mul).trans (map_one _))
  rw [valOf_comp, eq_div_iff h2, ← h3, ← _root_.mul_assoc]
  exact (congrArg (· * P 1) h4).trans (_root_.one_mul _)

end Locus

theorem isMonHom_of_mul_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C}
    [GrpObj G] [GrpObj H] (f : G ⟶ H) (h : μ[G] ≫ f = (f ⊗ₘ f) ≫ μ[H]) : IsMonHom f where
  mul_hom := h
  one_hom := by
    have e : (η[G] ≫ f) * (η[G] ≫ f) = η[G] ≫ f := by
      have h1 : lift η[G] η[G] ≫ μ[G] = η[G] := by
        simpa using MonObj.lift_comp_one_left (𝟙 (𝟙_ C)) η[G]
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← h, ← Category.assoc, h1]
    rw [mul_eq_left.mp e, Hom.one_def]
    simp

theorem exists_splitTorus_iso : ∀ (K : Type) [Field K] (W : WeierstrassCurve K), W = ⟨1, 0, 0, 0, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : K →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro K _ W hW
  subst hW
  intro U hU hsm _ _ hadd
  obtain ⟨f, hf⟩ := exists_toLocus U hU
  obtain ⟨g, hg⟩ := exists_fromLocus U hU
  have hpt : ∀ (k : Type) [Field k] (ρ : K →+* k)
      (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ),
      (x ≫ f).left ≫ U.ι =
        ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := fun k _ ρ x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hf).trans (comp_paramHom x))
  have r1 : IsReduced (splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced (splitTorus (Spec (.of K)) ℤ).hom
  have r2 : IsReduced (Over.mk (U.ι ≫ toSpec (node K))).left :=
    @isReduced_of_smooth_of_isReduced _ _ (U.ι ≫ toSpec (node K)) hsm _
  have s3 : Smooth (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Spec (.of K)) ℤ).hom
      (splitTorus (Spec (.of K)) ℤ).hom ≫ (splitTorus (Spec (.of K)) ℤ).hom))
  have r3 : IsReduced (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced
      (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom
  have sep : IsSeparated (Over.mk (U.ι ≫ toSpec (node K))).hom :=
    inferInstanceAs (IsSeparated (U.ι ≫ toSpec (node K)))
  have ext : ∀ {Z : Over (Spec (.of K))} {a b : Z ⟶ Over.mk (U.ι ≫ toSpec (node K))},
      a.left ≫ U.ι = b.left ≫ U.ι → a = b := fun h =>
    Over.OverMorphism.ext ((cancel_mono U.ι).mp h)
  refine ⟨⟨f, g, ?_, ?_⟩, isMonHom_of_mul_hom f ?_⟩
  · refine over_hom_ext_field fun k _ ρ x => valOf_injective (Units.ext ?_)
    rw [← Category.assoc, hg k ρ _ _ _ (hpt k ρ x), Category.comp_id]
    have := (valOf x).ne_zero
    have e : param (valOf x : k) 0 + param (valOf x : k) 1 = valOf x := by
      simp [param]; ring
    rw [e, div_eq_iff this]
    simp [param, sq]
  · refine over_hom_ext_field fun k _ ρ y => ext ?_
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    obtain ⟨-, -, c, hc⟩ := (nonsingular_points k).2.2 P hn
    rw [← Category.assoc, hpt, Category.comp_id, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [hg k ρ y P hP e]; exact hc⟩
  · refine over_hom_ext_field fun k _ ρ x => ext ?_
    obtain ⟨h, e⟩ := hadd k ρ _ _ _ _ _ _ (hpt k ρ (x ≫ fst _ _)) (hpt k ρ (x ≫ snd _ _))
    have e1 : x ≫ μ = (x ≫ fst _ _) * (x ≫ snd _ _) := by
      rw [Hom.mul_def, lift_comp_fst_snd]
    have e2 : x ≫ (f ⊗ₘ f) = lift ((x ≫ fst _ _) ≫ f) ((x ≫ snd _ _) ≫ f) := by
      rw [← lift_map, lift_comp_fst_snd]
    obtain ⟨c, hc⟩ := (nonsingular_points k).2.1 (valOf (x ≫ fst _ _)) (valOf (x ≫ snd _ _))
    rw [← Category.assoc, ← Category.assoc, e1, e2, hpt, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [valOf_mul, node_map]; exact hc⟩

end GlobalTheory.NodalCubic
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MultiplicativeReduction

open GlobalTheory.WeierstrassCurve

theorem isProper_pullback_snd {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    {K : Type} [Field K] (f : R →+* K) (hΔ : f W.Δ ≠ 0) :
    IsProper (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f))) := by
  have hpb : IsPullback (mapHom W f rfl ∣_ U) ((mapHom W f rfl ⁻¹ᵁ U).ι ≫ toSpec (W.map f))
      (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  have htop : mapHom W f rfl ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    let k := (scheme (W.map f)).residueField x
    obtain ⟨ρ, P, h, hx⟩ : ∃ (ρ : K →+* k) (P : Fin 3 → k)
        (h : IsUnimodularSol ((W.map f).map ρ) P),
        (scheme (W.map f)).fromSpecResidueField x = ptHom (W.map f) ρ P h := by
      obtain ⟨g, hg⟩ := Spec.map_surjective
        ((scheme (W.map f)).fromSpecResidueField x ≫ toSpec (W.map f))
      exact ⟨g.hom, exists_eq_ptHom (W.map f) (A := k) g.hom _ hg.symm⟩
    have hE : ((W.map f).map ρ).IsElliptic := ⟨by
      rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
      exact (IsUnit.mk0 _ hΔ).map ρ⟩
    have h1 := (hU k (ρ.comp f) P (h.comp_of_map_eq rfl)).mpr h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage, ← hx] at h1
    have h2 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) ∈
        mapHom W f rfl ⁻¹ᵁ U := h1 (Set.mem_univ (IsLocalRing.closedPoint k))
    have h3 : (scheme (W.map f)).fromSpecResidueField x (IsLocalRing.closedPoint k) = x :=
      Scheme.fromSpecResidueField_apply x _
    exact h3 ▸ h2
  have : IsIso (mapHom W f rfl ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Scheme.topIso _).hom)
  rw [← hpb.isoPullback_inv_snd]
  infer_instance

theorem nonempty_torusExtension_splitTorus (K : Type) [Field K] :
    Nonempty (TorusExtension (splitTorus (Spec (CommRingCat.of K)) ℤ)) :=
  ⟨Geo.Tor.torusExtOfIso (GlobalTheory.Diag.baseChangeIso (𝟙 (Spec (CommRingCat.of K))) ℤ)
    (GlobalTheory.Diag.torusExtension _ ℤ (𝟙 _))⟩

theorem isSemiAbelian_and_specialFibre : ∀ (W : WeierstrassCurve (PowerSeries ℚ)), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : PowerSeries ℚ →+* K), f PowerSeries.X = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : PowerSeries ℚ →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f PowerSeries.X = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * PowerSeries.X : PowerSeries ℚ) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp

end GlobalTheory.MultiplicativeReduction
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeierstrassCurve

theorem mem_coordOpen_two_iff_notMem_range_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (a : scheme W) : a ∈ coordOpen W 2 ↔ a ∉ Set.range (zero W) := by
  constructor
  · rintro h ⟨p, rfl⟩
    exact (zero_preimage_coordOpen_two W).le h
  · intro h
    by_contra ha
    have h₀ : a ∈ originOpen W :=
      ((originOpen_sup_coordOpen_two W).ge (Set.mem_univ a)).resolve_right ha
    let g := (scheme W).fromSpecResidueField a
    have hg : ∀ t, g t = a := fun t => Scheme.fromSpecResidueField_apply a t
    have e := (eq_comp_zero_iff W g).2 ⟨fun t _ => by
      change g t ∈ originOpen W
      rwa [hg], by
      refine (basicOpen_eq_bot_iff _).1 ?_
      rw [← Scheme.preimage_basicOpen, basicOpen_originParam]
      refine le_bot_iff.1 fun t ht => ha ?_
      have : g t ∈ coordOpen W 2 := ht.2
      rwa [hg] at this⟩
    refine h ⟨toSpec W a, ?_⟩
    have t : Spec ((scheme W).residueField a) := Classical.arbitrary _
    have := congrArg (fun f => f t) e
    simp only [Scheme.Hom.comp_apply, hg] at this
    exact this.symm

theorem exists_polAV_section_origin : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic], ∃ (A : PolAV (Spec (CommRingCat.of K))) (e : A.A ≅ GlobalTheory.WeierstrassCurve.schemeOver W) (θ : H0 A.L 1), (η[A.A]).left ≫ e.hom.left = GlobalTheory.WeierstrassCurve.zero W ∧ A.g = 1 ∧ ∀ a : A.A.left, a ∈ nonzeroLocus θ ↔ e.hom.left a ∉ Set.range (GlobalTheory.WeierstrassCurve.zero W) := by
  intro K _ W _
  obtain ⟨G, hc, he, -⟩ := exists_grpObj_weierstrass K W W.isUnit_Δ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := originLB_polarisation K W hc he
  let A : PolAV (Spec (CommRingCat.of K)) :=
    { A := schemeOver W
      grp := G
      isAb := isAbelianScheme_schemeOver K W W.isUnit_Δ hc
      g := 1
      smoothDim := smoothOfRelativeDimension_toSpec W
      L := originLB W
      isLB := originLB_isLB W
      rigid := h₁
      sym := h₂
      ample := h₃
      ktriv := h₄ }
  refine ⟨A, Iso.refl _, LB.finPowSec (originLB_isLB W) (n := 0) (secToPow (originSec W) 1) (𝟙 _),
    (Category.comp_id _).trans he, rfl, fun a => ?_⟩
  have e := LB.nonzeroLocus_finPowSec (originLB_isLB W) (n := 0) (secToPow (originSec W) 1) (𝟙 _)
  rw [nonzeroLocus_secToPow _ le_rfl, nonzeroLocus_originSec] at e
  exact (Iff.of_eq (congrArg (fun U : (scheme W).Opens => (a : scheme W) ∈ U) e)).trans
    (mem_coordOpen_two_iff_notMem_range_zero W a)

end GlobalTheory.WeierstrassCurve
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

theorem mem_basicOpen_of_isClosed [AlgebraicGeometry.IsIntegral X] {t : Γ(X, ⊤)} {ξ : X}
    (hξ : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U →
      Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    {L : LB X} (s : L.Sec) {b : L.ι} (hb : ξ ∈ X.basicOpen (s.f b)) {Z : Set X} (hZ : IsClosed Z)
    (hZt : Z ⊆ X.basicOpen t)
    (hs : ∀ y ∈ X.basicOpen t, y ∉ Z → ∃ c, y ∈ X.basicOpen (s.f c))
    {x : X} (hx : x ∉ X.basicOpen t) {a : L.ι} (ha : x ∈ L.U a) : x ∈ X.basicOpen (s.f a) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (U := L.U a ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) (x := x) ⟨ha, fun h ↦ hx (hZt h)⟩
  have hWa : W ≤ L.U a := fun y hy ↦ (hWU hy).1
  have hξW : ξ ∈ W := ((hξ x).1 hx).mem_open W.isOpen hxW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hpr := hp W hW hξW
  set p := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with hpd
  set σ := X.presheaf.map (homOfLE hWa).op (s.f a) with hσd
  have hpb : X.basicOpen p = W ⊓ X.basicOpen t := X.basicOpen_res _ _
  have hσb : X.basicOpen σ = W ⊓ X.basicOpen (s.f a) := X.basicOpen_res _ _
  have hle : X.basicOpen p ≤ X.basicOpen σ := fun y hy ↦ by
    obtain ⟨h₁, h₂⟩ := hpb.le hy
    obtain ⟨c, hc⟩ := hs y h₂ (hWU h₁).2
    exact hσb.ge ⟨h₁, mem_basicOpen_of_chart s (hWa h₁) hc⟩
  have hrad : p ∈ (Ideal.span {σ}).radical := by
    rw [← PrimeSpectrum.basicOpen_le_basicOpen_iff]
    have := hW.fromSpec.preimage_mono hle
    rwa [hW.fromSpec_preimage_basicOpen, hW.fromSpec_preimage_basicOpen] at this
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr m).1 (Ideal.mem_span_singleton.1 hm)
  obtain rfl | hi0 := eq_or_ne i 0
  · have hu : IsUnit σ := associated_one_iff_isUnit.1 (by simpa using hi)
    exact (hσb.le ((X.basicOpen_of_isUnit hu).ge hxW)).2
  · obtain ⟨q, hq⟩ := (dvd_pow_self p hi0).trans hi.symm.dvd
    have h₁ : ξ ∈ X.basicOpen σ := hσb.ge ⟨hξW, mem_basicOpen_of_chart s (hWa hξW) hb⟩
    rw [hq, Scheme.basicOpen_mul] at h₁
    exact absurd (hpb.le h₁.1).2 ((hξ ξ).2 specializes_rfl)

end SpecialFibreGenerator

open SpecialFibreGenerator TopologicalSpace in

theorem exists_sec_generates_specialFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : LB G.left), N.IsLB → ∀ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ a, a ∈ nonzeroLocus s) → IsClosed ((pullback.fst G.hom (jK V)) '' {a | a ∉ nonzeroLocus s}) → ∃ θ : H0 N 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  intro V _ _ _ G _ _ hG N hN s ⟨a₀, ha₀⟩ hZ
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hN s (by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ha₀
    exact ⟨k, fun h ↦ by rw [h, Scheme.basicOpen_zero] at hk; exact hk⟩)
  have hξ := DvrModel.notMem_basicOpen_iff_specializes hϖ hs
  have hr := DvrModel.opensRange_generic hϖ hK
  refine ⟨secAlong σ (𝟙 _), fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := LB.mem_of_cover hN x
  refine mem_nonzeroLocus_secAlong σ (𝟙 _) (a := a) ?_
  refine mem_basicOpen_of_isClosed hξ (DvrModel.prime_res_generic hϖ hs) σ (b := b)
    (((hξ x₀).1 ((DvrModel.notMem_basicOpen_iff _ hϖ x₀).2 hx₀)).mem_open
      (Scheme.basicOpen _ _).isOpen hb) hZ ?_ (fun y hy hyZ ↦ ?_)
    ((DvrModel.notMem_basicOpen_iff _ hϖ x).2 hx) ha
  · rintro _ ⟨y, -, rfl⟩
    exact hr.le ⟨y, rfl⟩
  · obtain ⟨z, rfl⟩ := hr.ge hy
    have hz : z ∈ nonzeroLocus s := by_contra fun h ↦ hyZ ⟨z, h, rfl⟩
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
    refine ⟨k ⟨⟩, ?_⟩
    have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
      zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
    have h := congrArg (Scheme.basicOpen _) (hσ k)
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
      Scheme.basicOpen_of_isUnit _ (((h0.isUnit.map _).map _).map _)] at h
    exact (h.ge ⟨Scheme.basicOpen_le _ _ hk, hk⟩).2

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MultiplicativeReduction

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.WeierstrassCurve

theorem exists_sec_of_iso {X X' : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) (F : X' ⟶ X)
    (H : LBIso (L.pull F) N) (θ : H0 L 1) :
    ∃ s : N.Sec, ∀ y : X', y ∈ nonzeroLocus s ↔ F y ∈ nonzeroLocus θ := by
  have hP := linComb_isLB L hL (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))
  have mem : ∀ (i : L.ι) (y : X), y ∈ L.U i → y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i y hy => Set.mem_iInter.2 fun _ => hy
  let a : ChartPull L (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))) (𝟙 X) :=
    { idx := fun i _ => i
      le := fun i y hy => mem i y hy
      g := fun y i j hi hj => Eq.symm ((gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y _ _
        (mem i y hi) (mem j y hj)).trans (by rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.id_comp])) }
  have h₁ := LBIso.chartPull a (chartPullId _) ⟨_, idIso_isGen hP⟩
  have h₂ := LBIso.chartPull (Geo.Tor.chartPullPull _ F F rfl) (Geo.Tor.chartPullPull _ F F rfl) h₁
  obtain ⟨w, hw⟩ := LBIso.trans hN (pull_isLB hL F) (pull_isLB hP F) H.symm h₂
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) hP hN θ
  refine ⟨s', fun y => ?_⟩
  refine (mem_nonzeroLocus _ y).trans
    (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (F y)).symm)
  · obtain ⟨j, hj⟩ := exists_chart hP (F y)
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp, gs_stalkMap F y _ hj] at e
    exact ⟨j, hj, (isUnit_map_iff (F.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
  · obtain ⟨k, hk⟩ := exists_chart hN y
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at e
    exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap F y _ hj _).symm.trans e)).mp (u.map _))⟩

theorem exists_iso_schemeOver {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (W : WeierstrassCurve R)
    [(W.map f).IsElliptic] (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) :
    ∃ φ : (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)) ≅ schemeOver (W.map f),
      φ.hom.left ≫ mapHom W f rfl = pullback.fst _ _ ≫ U.ι := by
  have hr : Set.range (mapHom W f rfl) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    let t := (scheme (W.map f)).fromSpecResidueField y
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (t ≫ toSpec (W.map f))
    obtain ⟨P, h, e⟩ := exists_eq_ptHom (W.map f) (A := (scheme (W.map f)).residueField y) ρ.hom t hρ.symm
    have : ((W.map f).map ρ.hom).IsElliptic := inferInstance
    have h₁ := (hU _ (ρ.hom.comp f) P (h.comp_of_map_eq rfl)).2 h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ.hom P h, ← e] at h₁
    have h₂ := h₁ (Set.mem_univ (IsLocalRing.closedPoint _))
    change mapHom W f rfl (t _) ∈ U at h₂
    exact (congrArg (fun q => mapHom W f rfl q ∈ U) (Scheme.fromSpecResidueField_apply y _)).mp h₂
  have hm := IsOpenImmersion.lift_fac U.ι (mapHom W f rfl) hr
  have hp : IsPullback (IsOpenImmersion.lift U.ι (mapHom W f rfl) hr) (toSpec (W.map f)) (U.ι ≫ toSpec W)
      (Spec.map (CommRingCat.ofHom f)) := by
    have h₀ : IsPullback (IsOpenImmersion.lift U.ι (mapHom W f rfl) hr) (𝟙 _) U.ι (mapHom W f rfl) :=
      IsPullback.of_vert_isIso_mono ⟨hm.trans (Category.id_comp _).symm⟩
    simpa using h₀.paste_vert (isPullback_mapHom W f rfl)
  refine ⟨Over.isoMk hp.isoPullback.symm hp.isoPullback_inv_snd, ?_⟩
  change hp.isoPullback.inv ≫ _ = _
  exact ((congrArg (· ≫ U.ι) hp.isoPullback_inv_fst).symm.trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hm))).symm

theorem isUnimodularSol_twoPt {R A : Type} [CommRing R] [CommRing A] (a : R) (ρ : R →+* A) :
    IsUnimodularSol ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ) ![0, 0, 1] :=
  isUnimodularSol_some (by simp [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.map])

theorem nonsingular_twoPt {R k : Type} [CommRing R] [Field k] (a : R) (ρ : R →+* k) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.Nonsingular ![0, 0, 1] ↔ ρ a ≠ 0 := by
  rw [WeierstrassCurve.Projective.nonsingular_iff, WeierstrassCurve.Projective.equation_iff]
  simp [WeierstrassCurve.map]

theorem add_twoPt {R k : Type} [CommRing R] [Field k] (a : R) (ρ : R →+* k) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.add ![0, 0, 1] ![0, 0, 1] 0 = 0 ∧
      ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.add ![0, 0, 1] ![0, 0, 1] 2 = 0 := by
  rw [WeierstrassCurve.Projective.add_self]
  constructor
  · simp [WeierstrassCurve.Projective.dblXYZ, WeierstrassCurve.Projective.dblX, WeierstrassCurve.map]
  · simp [WeierstrassCurve.Projective.dblXYZ, WeierstrassCurve.Projective.dblZ, WeierstrassCurve.Projective.negY,
      WeierstrassCurve.map]

theorem isElliptic_generic : ((⟨1, 0, 0, PowerSeries.X, 0⟩ : WeierstrassCurve (PowerSeries ℚ)).map
    (algebraMap _ (FractionRing (PowerSeries ℚ)))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  have : (⟨1, 0, 0, PowerSeries.X, 0⟩ : WeierstrassCurve (PowerSeries ℚ)).Δ =
      PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  refine mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) fun h => ?_
  simpa using congrArg PowerSeries.constantCoeff h

theorem isClosed_twoPt {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {a : V}
    (ha : a ∈ IsLocalRing.maximalIdeal V) (W : WeierstrassCurve V) (hW : W = ⟨1, 0, 0, a, 0⟩) (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : V →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    (x : Spec (.of (FractionRing V)) ⟶ U.toScheme) (h : IsUnimodularSol (W.map (algebraMap V _)) ![0, 0, 1])
    (hx : x ≫ U.ι = ptHom W (algebraMap V _) ![0, 0, 1] h) : IsClosed (Set.range x) := by
  subst hW
  let σ := ptHom _ (RingHom.id V) ![0, 0, 1] (isUnimodularSol_twoPt a _)
  have hσ : ∀ (k : Type) [CommRing k] (ρ : V →+* k),
      Spec.map (CommRingCat.ofHom ρ) ≫ σ = ptHom _ ρ ![0, 0, 1] (isUnimodularSol_twoPt a _) := fun k _ ρ =>
    (SpecMap_ptHom _ _ _ _ ρ).trans (ptHom_congr _ _ _ _ (RingHom.comp_id ρ) (by ext i; fin_cases i <;> simp) _)
  have hs : σ ≫ toSpec _ = 𝟙 _ := (ptHom_toSpec ..).trans (Spec.map_id _)
  have : IsClosedImmersion (σ ≫ toSpec _) := by rw [hs]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ (toSpec _)
  have hx' : x ≫ U.ι = jK V ≫ σ := hx.trans (hσ _ _).symm
  have e : Set.range x = U.ι ⁻¹' Set.range σ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact ⟨jK V z, (congrArg (fun q => q z) hx').symm⟩
    · rintro y ⟨p, hp⟩
      by_cases h0 : p.asIdeal = ⊥
      · have hj : jK V (IsLocalRing.closedPoint _) = p := by
          refine PrimeSpectrum.ext ?_
          rw [h0]
          change Ideal.comap (algebraMap V (FractionRing V)) (IsLocalRing.maximalIdeal _) = ⊥
          rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
          exact IsFractionRing.injective _ _
        refine ⟨IsLocalRing.closedPoint _, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hp, ← hj]
        exact congrArg (fun q => q (IsLocalRing.closedPoint _)) hx'
      · exfalso
        have hm : p.asIdeal = IsLocalRing.maximalIdeal V :=
          IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h0 p.isPrime)
        refine (nonsingular_twoPt a (IsLocalRing.residue V)).1 ((hU _ _ _ (isUnimodularSol_twoPt a _)).1 ?_)
          ((IsLocalRing.residue_eq_zero_iff a).2 ha)
        rw [← hσ]
        intro z _
        have hz : Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) z = p := by
          refine PrimeSpectrum.ext ?_
          rw [hm]
          change Ideal.comap (IsLocalRing.residue V) z.asIdeal = _
          have := z.isPrime
          rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
        change σ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) z) ∈ U
        rw [hz, hp]
        exact y.2
  rw [e]
  exact σ.isClosedEmbedding.isClosed_range.preimage U.ι.continuous

open GlobalTheory.PolTranslate in

theorem transl_mem_range_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : 𝟙_ (Over S) ⟶ G} (hx : x * x = 1)
    (z : G.left) : (transl x).left z ∈ Set.range (η[G]).left ↔ z ∈ Set.range x.left := by
  have h₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e₁ : η[G] ≫ transl x = x := by
    rw [comp_transl, ← h₁, _root_.one_mul]; simp
  have e₂ : x ≫ transl x = η[G] := by
    rw [comp_transl, ← h₁, ← hx]; simp
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    have e := congrArg (fun q => q.left z) (transl_transl hx)
    exact (congrArg (fun q => q.left p) e₁).symm.trans ((congrArg (transl x).left hp).trans e)
  · rintro ⟨p, rfl⟩
    exact ⟨p, (congrArg (fun q => q.left p) e₂).symm⟩

theorem one_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G] :
    (η[(Over.pullback φ).obj G]).left ≫ pullback.fst G.hom φ = φ ≫ (η[G]).left := by
  rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

open GlobalTheory.PolTranslate in

theorem exists_pol_twoTorsion (hL : Laws) {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (φ : G ≅ schemeOver W)
    (hφ : (η[G]).left ≫ φ.hom.left = zero W) (x : 𝟙_ _ ⟶ G) (hx : x * x = 1) :
    ∃ (A : PolAV (Spec (CommRingCat.of K))) (e : G ≅ A.A) (θ : H0 A.L 1), IsMonHom e.hom ∧ A.g = 1 ∧
      ∀ z : G.left, e.hom.left z ∈ nonzeroLocus θ ↔ z ∉ Set.range x.left := by
  obtain ⟨A₀, e, θ, he, hg, hθ⟩ := exists_polAV_section_origin K W
  let e₀ : G ≅ A₀.A := φ ≪≫ e.symm
  have h₀ : e₀.hom ≫ e.hom = φ.hom := by simp [e₀]
  have hw : G.hom = e₀.hom.left ≫ A₀.A.hom := (Over.w e₀.hom).symm
  have : IsIso e₀.hom.left := ((Over.forget _).mapIso e₀).isIso_hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have hG : IsAbelianScheme G := by
    have := A₀.isAb.smooth
    have := A₀.isAb.proper
    have := A₀.isAb.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · rw [hw]; infer_instance
    · rw [hw]; infer_instance
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
        (IsPullback.of_horiz_isIso ⟨(Over.w e₀.hom).trans (Category.comp_id _).symm⟩) this
  have hη : η[G] ≫ e₀.hom = η[A₀.A] := by
    rw [← cancel_mono e.hom, Category.assoc, h₀]
    exact Over.OverMorphism.ext (hφ.trans he.symm)
  have := hL.rigidity _ G A₀.A hG A₀.isAb e₀.hom hη
  obtain ⟨A, e', θ', _, hg', hθ'⟩ := exists_translate K A₀ (x ≫ e₀.hom)
    (by rw [← MonObj.mul_comp, hx, MonObj.one_comp]) θ
  refine ⟨A, e₀ ≪≫ e'.symm, θ', inferInstanceAs (IsMonHom (e₀.hom ≫ e'.inv)), hg'.trans hg, fun z => ?_⟩
  have k : (e₀ ≪≫ e'.symm).hom ≫ (e'.hom * (toUnit _ ≫ x ≫ e₀.hom)) = transl x ≫ e₀.hom := by
    rw [MonObj.comp_mul, transl, MonObj.mul_comp]
    simp
  rw [hθ', ← transl_mem_range_iff hx]
  refine Iff.trans (iff_of_eq (congrArg (fun q => q.left z ∈ nonzeroLocus θ) k)) ?_
  refine (hθ _).trans (not_congr ?_)
  rw [← he]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, e₀.hom.left.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun q => q.left p) hη).trans (e.hom.left.isOpenEmbedding.injective hp)
  · rintro ⟨p, hp⟩
    exact ⟨p, congrArg e.hom.left ((congrArg (fun q => q.left p) hη).symm.trans (congrArg e₀.hom.left hp))⟩

theorem exists_semiAbelian_polarised : Laws → ∃ (G : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (eA : (Over.pullback (jK (PowerSeries ℚ))).obj G ≅ A.A) (i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj G), IsSemiAbelian G ∧ IsMonHom eA.hom ∧ IsMonHom i.hom ∧ A.g = 1 ∧ ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK (PowerSeries ℚ)))), w.IsGen) ∧ ∃ θ : H0 LG.L 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint (PowerSeries ℚ) → x ∈ nonzeroLocus θ := by
  intro hL
  obtain ⟨W, hW⟩ : ∃ W : WeierstrassCurve (PowerSeries ℚ), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, hη, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := isSemiAbelian_and_specialFibre W hW U hU hs hgi hqc hmul
  let f := algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
  have : (W.map f).IsElliptic := hW ▸ isElliptic_generic
  obtain ⟨φ, hφ⟩ := exists_iso_schemeOver f W U hU
  let G := Over.mk (U.ι ≫ toSpec W)
  let j := pullback.fst G.hom (jK (PowerSeries ℚ))
  have hη' : (η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left ≫ j ≫ U.ι = jK _ ≫ zero W := by
    rw [← hη, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U.ι) (one_pullback_fst _ G)
  have hP : IsUnimodularSol (W.map f) ![0, 0, 1] := hW ▸ isUnimodularSol_twoPt _ _
  have hX : f PowerSeries.X ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero
  have hPU := (hU _ f _ hP).2 (hW ▸ (nonsingular_twoPt _ f).2 hX)
  have hr : Set.range (ptHom W f _ hP) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPU (Set.mem_univ y)
  have ha := IsOpenImmersion.lift_fac U.ι (ptHom W f _ hP) hr
  have ha' : IsOpenImmersion.lift U.ι (ptHom W f _ hP) hr ≫ U.ι ≫ toSpec W = jK _ := by
    rw [← Category.assoc, ha, ptHom_toSpec]
  let a : Over.mk (jK (PowerSeries ℚ)) ⟶ G := Over.homMk _ ha'
  let x : 𝟙_ _ ⟶ (Over.pullback (jK (PowerSeries ℚ))).obj G :=
    Over.homMk (pullback.lift a.left (𝟙 _) (ha'.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have hxa : x.left ≫ j = a.left := pullback.lift_fst _ _ _
  have hx : x * x = 1 := by
    have h₁ : (1 : 𝟙_ _ ⟶ (Over.pullback (jK (PowerSeries ℚ))).obj G) = η[_] := by rw [Hom.one_def]; simp
    rw [h₁]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have h₂ := SmoothLocusBaseChange.lift_mul_pullback_fst (jK (PowerSeries ℚ)) G x x (𝟙 _) a a
      (hxa.symm.trans (Category.id_comp _).symm) (hxa.symm.trans (Category.id_comp _).symm)
    obtain ⟨h, h₃⟩ := hmul _ f a a _ _ hP hP ha ha
    refine (cancel_mono U.ι).1 ?_
    refine Eq.trans ?_ (hη'.symm.trans (Category.assoc _ _ _).symm)
    refine (congrArg (· ≫ U.ι) (h₂.trans (Category.id_comp _))).symm.trans (h₃.trans ?_)
    rw [SpecMap_zero, ptHom_eq_ptHom_iff_minors]
    obtain ⟨h₄, h₅⟩ := add_twoPt PowerSeries.X f
    rw [← hW] at h₄ h₅
    intro m l
    fin_cases m <;> fin_cases l <;> simp [h₄, h₅]
  have hz : (η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left ≫ φ.hom.left = zero (W.map f) := by
    apply (isPullback_mapHom W f rfl).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hφ).trans (hη'.trans (zero_mapHom W f rfl).symm))
    · exact (Over.w (η[(Over.pullback (jK (PowerSeries ℚ))).obj G] ≫ φ.hom)).trans (zero_toSpec _).symm
  obtain ⟨A, eA, θ, heA, hg, hθ⟩ := exists_pol_twoTorsion hL (W.map f) _ φ hz x hx
  obtain ⟨LG, c, s, hs₁, hs₂, w, hw⟩ := PolExtension.exists_cubical_symmetric_extension hL _ G hG A eA heA
  refine ⟨G, inferInstance, inferInstance, A, eA, i, hG, heA, hi, hg, LG, c, s, hs₁, hs₂, ⟨w, hw⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_of_iso A.isLB (pull_isLB LG.isLB j) eA.hom.left ⟨w, hw⟩ θ
  have ht' : ∀ z, z ∈ nonzeroLocus t ↔ z ∉ Set.range x.left := fun z => (ht z).trans (hθ z)
  refine exists_sec_generates_specialFibre _ G hG LG.L LG.isLB t
    ⟨(η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left (IsLocalRing.closedPoint _), (ht' _).2 ?_⟩ ?_
  · rintro ⟨p, hp⟩
    have h₁ : ptHom W f _ hP p ∈ coordOpen W 2 := (ptHom_preimage_coordOpen W f _ hP 2).ge
      (PrimeSpectrum.basicOpen_one.ge (Set.mem_univ p))
    have h₂ : ptHom W f _ hP p = zero W (jK _ (IsLocalRing.closedPoint _)) :=
      (congrArg (fun q => q p) ((congrArg (· ≫ U.ι) hxa).trans ha)).symm.trans
        ((congrArg (j ≫ U.ι) hp).trans (congrArg (fun q => q (IsLocalRing.closedPoint _)) hη'))
    rw [h₂] at h₁
    exact (zero_preimage_coordOpen_two W).le h₁
  · have e : j '' {z | z ∉ nonzeroLocus t} = Set.range a.left := by
      rw [← hxa]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := not_not.1 (mt (ht' z).2 hz)
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨x.left p, fun h => (ht' _).1 h ⟨p, rfl⟩, rfl⟩
    refine e ▸ isClosed_twoPt (a := PowerSeries.X) ?_ W hW U hU a.left hP ha
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl

end GlobalTheory.MultiplicativeReduction
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MultiplicativeTorusSetting

section Sections
variable {X Y Z : Scheme.{0}} {L : LB X}

theorem isUnit_gs_of_mem {M : LB X} (θ : LB.Sec M) (r : Z ⟶ X) (z : Z) {k : M.ι} (hk : r z ∈ M.U k)
    (h : r z ∈ nonzeroLocus θ) : IsUnit (gs r z _ (θ.f k)) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ M.U j := X.basicOpen_le _ hj
  rw [gs_compat θ r z hk hj']
  refine (Units.isUnit _).mul ?_
  rw [gs_stalkMap r z _ hj', gs_eq (𝟙 X) (r z) _ hj']
  exact IsUnit.map _ ((X.mem_basicOpen _ _ hj').1 hj)

theorem exists_sec_of_pow_one (θ : H0 L 1) : ∃ s : LB.Sec L, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J),
    Good L z J → gs r z _ (s.f (J r)) = sval θ r z J := by
  have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy =>
    Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun j => resG X (le j) (θ.f fun _ => j), fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy]
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((sec_trans θ (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    rw [trF, Fintype.prod_unique]
    simp only [Category.comp_id, Nat.cast_one, zpow_one]
  · rw [sval_of θ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z _ (hJ r) _

theorem exists_gen_of_isUnit (hL : L.IsLB) (s : LB.Sec L) (h : ∀ j, ∀ y ∈ L.U j, IsUnit (gs (𝟙 X) y _ (s.f j))) :
    ∃ t : LB.Gen (L.pull (𝟙 X)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      (val (L := L) (φ := fun _ : PUnit => 𝟙 X) (ε := fun _ => 1) t r z J).val = gs r z _ (s.f (J r)) := by
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff _).1 (pullIso_isGen hL (𝟙 X))) hL (pull_isLB hL _) s
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) j, r z ∈ L.U j →
      gs r z _ (s'.f fun _ => j) = gs r z _ (s.f j) := fun Z r z j hj => by
    have e := hs' Z r z j (fun _ => j) hj (mem_pull.2 hj)
    have a : gw (pullIso L (𝟙 X)) r z j (fun _ => j) = 1 := gm_self (pull_isLB hL _) r z (mem_pull.2 hj)
    rw [a, Units.val_one, _root_.one_mul, Category.comp_id] at e
    exact e.symm
  have hu : ∀ k, IsUnit (s'.f k) := fun k => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := (congrArg IsUnit (key _ (𝟙 X) y (k PUnit.unit) (mem_pull.1 hy))).mpr (h _ y (mem_pull.1 hy))
    rw [gs_eq _ _ _ (show (𝟙 X : X ⟶ X) y ∈ _ from hy)] at e
    exact e
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun Z r z J hJ => ?_⟩
  rw [val_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
  exact (gs_unit r z _ (mem_pull.2 (hJ r)) _).symm.trans (key Z r z _ (hJ r))

end Sections

theorem sec_eq_of_value (hT : SecTwistSt) {V : Type} [CommRing V] [IsDomain V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of V)} [Flat p]
    {d : A.A.left ⟶ X} (hd : IsPullback d A.A.hom p (jK V)) {L : LB X} (hL : L.IsLB) (hw : LBIso A.L (L.pull d))
    (e : Spec (CommRingCat.of (FractionRing V)) ⟶ A.A.left) (he : e ≫ A.A.hom = 𝟙 _) (s s' : LB.Sec L)
    (z : Spec (CommRingCat.of (FractionRing V))) (j : L.ι) (hj : (e ≫ d) z ∈ L.U j)
    (hu : IsUnit (gs (e ≫ d) z _ (s.f j))) (h : gs (e ≫ d) z _ (s.f j) = gs (e ≫ d) z _ (s'.f j)) (i : L.ι) :
    s.f i = s'.f i := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT A
  have key : ∀ s : LB.Sec L, ∃ a : FractionRing V, ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) j k,
      d (r z) ∈ L.U j → r z ∈ A.L.U k → gs (r ≫ d) z _ (s.f j) =
        (gw w r z j k).val * (cst (r ≫ A.A.hom) z a * gs r z _ (b.f k)) := fun s => by
    obtain ⟨t, ht⟩ := sec_pull_down ((isGen_iff w).1 hw) hL A.isLB s
    obtain ⟨a, ha, -⟩ := hb t
    refine ⟨a, fun Z r z j k h₁ h₂ => ?_⟩
    rw [ht Z r z j k h₁ h₂, ha k, gs_mul _ _ _ h₂, gs_constFn _ _ _ _ h₂]
  obtain ⟨a, ha⟩ := key s
  obtain ⟨a', ha'⟩ := key s'
  obtain ⟨k, hk⟩ := exists_chart A.isLB (e z)
  rw [ha _ e z j k hj hk] at hu h
  rw [ha' _ e z j k hj hk, Units.mul_right_inj,
    (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)).mul_left_inj, he] at h
  obtain rfl : a = a' := by
    by_contra hne
    have r := cst_regular (𝟙 (Spec (CommRingCat.of (FractionRing V)))) z (sub_ne_zero.2 hne)
    rw [cst_sub, h, sub_self] at r
    exact not_isLeftRegular_zero r
  refine Exist.CubicalExtension.app_injective_generic hd (L.U i) (fn_ext fun y hy => ?_)
  obtain ⟨k, hk⟩ := exists_chart A.isLB y
  exact (gs_pull (𝟙 _) d y _ hy _).trans ((ha _ (𝟙 _) y i k hy hk).trans
    ((ha' _ (𝟙 _) y i k hy hk).symm.trans (gs_pull (𝟙 _) d y _ hy _).symm))

theorem not_isProper_torus (k : Type) [Field k] [CharZero k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h => by
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, hp, h0⟩ := isIntegral_appTop_of_universallyClosed (splitTorus (Spec (CommRingCat.of k)) ℤ).hom
    (charUnit (Spec (CommRingCat.of k)) ℤ 1).val
  have root : ∀ a : kˣ, (p.map e.symm.toRingHom).IsRoot a.val := fun a => by
    let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ splitTorus (Spec (CommRingCat.of k)) ℤ :=
      (splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ (Units.map e.toMonoidHom a))
    have h₁ : t.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) ℤ 1).val = e a.val := by
      rw [← chV_val, chV, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (zpow_one (Units.map e.toMonoidHom a))
    have h₂ : t.left.appTop.hom.comp (splitTorus (Spec (CommRingCat.of k)) ℤ).hom.appTop.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
      exact congrArg CommRingCat.Hom.hom Scheme.Hom.id_appTop
    have h₃ := congrArg t.left.appTop.hom h0
    rw [Polynomial.hom_eval₂, h₂, h₁, map_zero] at h₃
    have h₄ := congrArg e.symm.toRingHom h₃
    rw [Polynomial.hom_eval₂, map_zero] at h₄
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h₄
  have inf : Set.Infinite {x | (p.map e.symm.toRingHom).IsRoot x} :=
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 1 : ℕ) : k))
      (fun a b h => by simpa using h) fun n => root (Units.mk0 _ (Nat.cast_ne_zero.2 n.succ_ne_zero))
  exact (hp.map _).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ inf)

def tqOfIso {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (i : splitTorus S X ≅ G)
    [IsMonHom i.hom] : TQ G X :=
  have e : G.hom = i.inv.left ≫ (splitTorus S X).hom := (Over.w i.inv).symm
  have : IsIso i.inv.left := inferInstanceAs (IsIso ((Over.forget S).map i.inv))
  { B := 𝟙_ (Over S)
    isAb := isAbelianScheme_unit S
    q := toUnit _
    i := i.hom
    q_hom := inferInstance
    i_hom := inferInstance
    q_flat := by rw [Rosenlicht.toUnit_left, e]; have := Diag.flat_hom S X; infer_instance
    q_surj := by rw [Rosenlicht.toUnit_left, e]; have := Diag.surjective_hom S X; infer_instance
    q_affine := by rw [Rosenlicht.toUnit_left, e]; have := Diag.isAffineHom_hom S X; infer_instance
    isKernel := by
      have : IsIso (η[𝟙_ (Over S)]) := by rw [toUnit_unique η[𝟙_ (Over S)] (𝟙 _)]; infer_instance
      exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
    loc := fun _ χ => ⟨⊤, trivial, chV i.inv χ, isWt_of_retraction i.inv i.hom_inv_id χ⟩ }

theorem exists_even_sec (hT : SecTwistSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] [Flat G.hom] {d : A.A.left ⟶ G.left} (gp : IsGrpPullback A.A G (jK V) d) (P : CP G)
    (hw : LBIso A.L (P.L.L.pull d)) (θ : H0 P.L.L 1) (h0 : eSec G (IsLocalRing.closedPoint V) ∈ nonzeroLocus θ) :
    ∃ s : LB.Sec P.L.L, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      (r z ∈ nonzeroLocus θ → IsUnit (gs r z _ (s.f (J r)))) ∧
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s.f (J r)) := by
  have := A.isAb.comm
  obtain ⟨θ', hθ'⟩ := exists_sec (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => ((1 : ℕ) : ℤ)) P.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two]))
    (pullMulSec θ (ι[G]).left (LB.invGen _ _ _ P.sym) (DVR.invGen_isGen _ _ _ _ P.sym_gen))
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one θ
  obtain ⟨s', hs'⟩ := exists_sec_of_pow_one θ'
  have un : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      r z ∈ nonzeroLocus θ → IsUnit (gs r z _ (s.f (J r))) := fun Z r z J hJ h => by
    rw [hs Z r z J hJ]
    exact isUnit_gs_of_mem θ r z (hJ.mem _ r) h
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s'.f (J r)) :=
    fun Z r z J hJ => by
      rw [hs Z _ z J hJ, hs' Z r z J hJ, hθ' Z r z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, mul_comm (sval _ _ _ _),
        Units.mul_inv_cancel_left]
  have he : eSec A.A ≫ d = (1 : Over.mk (jK V) ⟶ G).left := (cubeMapOf gp).e_comm.trans (one_left G (Over.mk (jK V))).symm
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := inferInstance
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  have top : eSec G ⁻¹ᵁ nonzeroLocus θ = ⊤ := (IsLocalRing.closed_point_mem_iff (R := V)).1 h0
  have key := sec_eq_of_value hT A gp.1 P.L.isLB hw (eSec A.A) (Over.w η[A.A]) s s' z (J (eSec A.A ≫ d)) (hJ _)
    (un _ _ z J hJ (by
      rw [he, one_left]
      exact top.ge (show jK V z ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial))) (by
      have e := ev _ (eSec A.A ≫ d) z J hJ
      have e₁ : (eSec A.A ≫ d) ≫ (ι[G]).left = eSec A.A ≫ d := by
        rw [he, ← Over.comp_left, ← Hom.inv_def, inv_one]
      have e₂ : val P.sym (eSec A.A ≫ d) z J = 1 := by
        rw [he]; exact P.val_sym_one (T := Over.mk (jK V)) hJ
      rwa [e₁, e₂, Units.val_one, _root_.one_mul] at e)
  exact ⟨s, fun Z r z J hJ => ⟨un Z r z J hJ, by rw [ev Z r z J hJ, key]⟩⟩

theorem exists_even_cubTriv {k : Type} [Field k] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Spec (CommRingCat.of k))} [GrpObj G₀]
    [IsCommMonObj G₀] (i : splitTorus (Spec (CommRingCat.of k)) X ≅ G₀) [IsMonHom i.hom] {P : CP G} {P₀ : CP G₀}
    {f : Spec (CommRingCat.of k) ⟶ S} {F : G₀.left ⟶ G.left} {hF : F ≫ G.hom = G₀.hom ≫ f}
    {w : LB.Iso P₀.L.L (P.L.L.pull F)} (hw : IsCPMap P₀ P f F hF w) (s : LB.Sec P.L.L)
    (hu : ∀ (y : G₀.left) (J), Good P.L.L y J → IsUnit (gs F y _ (s.f (J F))))
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good P.L.L z J →
      gs (r ≫ (ι[G]).left) z _ (s.f (J (r ≫ (ι[G]).left))) = (val P.sym r z J).val * gs r z _ (s.f (J r))) :
    ∃ σ : CubTriv P₀.c i.hom, σ.Even := by
  obtain ⟨s₀, hs₀⟩ := sec_pull_down ((isGen_iff w).1 hw.gen) P.L.isLB P₀.L.isLB s
  obtain ⟨t, ht, vt⟩ := exists_gen_of_isUnit P₀.L.isLB s₀ fun j y hy => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB y
    have e := hs₀ _ (𝟙 _) y (J F) j (hJ F) hy
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ hu y J hJ)
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.hom.left, (1 : splitTorus _ X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two]))
    (LB.mulGen _ _ _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => 𝟙 _) (fun _ => 1) t i.hom.left)
      (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => 𝟙 _) (fun _ => 1) t (1 : splitTorus _ X ⟶ G₀).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  have v : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ splitTorus _ X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t (x ≫ i.hom).left z J *
        (val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t (1 : T ⟶ G₀).left z J)⁻¹ :=
    fun T x z J hJ => by
      rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left,
        MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩, fun T x z J' hJ' => ?_⟩
  · have a := splitTorus_gen_cubical k X G₀ i inferInstance P₀.L P₀.c t ht T (x ≫ i.hom) (y ≫ i.hom) (u ≫ i.hom) z J hJ
    simp only [v T _ z J hJ, MonObj.mul_comp] at a ⊢
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    simp only [ofMul_mul, ofMul_inv] at a' ⊢
    linear_combination (norm := abel) a'
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (hw.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i.hom)
    have b : ∀ y : T ⟶ G₀, gs (y.left ≫ F) z _ (s.f (J (y.left ≫ F))) = (W y *
        val (L := P₀.L.L) (φ := fun _ : PUnit => 𝟙 _) (ε := fun _ => 1) t y.left z J').val := fun y => by
      rw [Units.val_mul, vt _ _ z J' hJ', hW]
      exact hs₀ _ y.left z _ _ (hJ (y.left ≫ F)) (hJ' _)
    have c := hs _ ((x ≫ i.hom).left ≫ F) z J hJ
    rw [← inv_left_comp hw.mul, b, b, ← Units.val_mul, Units.val_inj, ← _root_.mul_assoc, a, _root_.mul_assoc,
      mul_right_inj] at c
    show val σ _ z J' = _ * val σ _ z J'
    rw [v T _ z J' hJ', v T _ z J' hJ', GrpObj.inv_comp, c, _root_.mul_assoc]

theorem main : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (G : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G) (_ : IsCommMonObj G) (s : HidaSetting (PowerSeries ℚ) A G), A.g = 1 ∧ Module.finrank ℤ s.X = 1 ∧ ¬ IsProper (thickObj (PowerSeries ℚ) (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0 G).hom := by
  obtain ⟨laws, laws₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨G, _, _, A, eA, i, hG, hA, hi, hg, L, -, -, -, -, hw, θ, hθ⟩ :=
    MultiplicativeReduction.exists_semiAbelian_polarised laws
  have hV : CDVR (PowerSeries ℚ) := ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  obtain ⟨P, rfl⟩ := CubicalPackage.exists_package laws _ hV A G hG eA hA L hw
  have := hG.smooth
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK _) (eA.inv.left ≫ pullback.fst G.hom (jK _)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK _))).congr (Category.id_comp _) rfl
  have hinv : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨s, hs⟩ := exists_even_sec laws₂.secTwist A gp P
    (LBIso.chartPull (chartPullSec A.L _ eA.inv.left hinv) (chartPullSame P.L.L _ _ _ eA.inv.left fun _ => rfl) hw) θ
    (hθ _ (congrArg (fun q => q (IsLocalRing.closedPoint (PowerSeries ℚ))) (Over.w η[G])))
  obtain ⟨r, hr⟩ := thick_zero_factor (PowerSeries ℚ)
  obtain ⟨i₀, hi₀, -⟩ := grpPullback_iso
    (((SplitTorus.isGrpPullback_bcMap r ℤ).comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G _))).congr
      ((congrArg (r ≫ ·) (Category.id_comp _)).trans hr.symm) rfl)
    (isGrpPullback_pullback G (thick _ (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0))
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal (PowerSeries ℚ)) 0 P
  have hm : (IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) := Ideal.Quotient.field _
  have : CharZero (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) := algebraRat.charZero _
  obtain ⟨wA, hwA⟩ := hw
  refine ⟨A, G, inferInstance, inferInstance, ⟨hV, hG, eA, hA, P, wA, hwA, ℤ, tqOfIso i₀, P₀, ⟨w₀, h₀⟩,
    exists_even_cubTriv i₀ h₀ s (fun y J hJ => (hs _ _ y J hJ).1 (hθ _ ?_)) fun Z r z J hJ => (hs Z r z J hJ).2⟩,
    hg, Module.finrank_self ℤ, fun h => not_isProper_torus
      (PowerSeries ℚ ⧸ IsLocalRing.maximalIdeal (PowerSeries ℚ) ^ (0 + 1)) ?_⟩
  · exact (congrArg (fun q => q y) (pullback.condition.trans (congrArg (_ ≫ ·) hr))).trans
      (IsLocalRing.PrimeSpectrum.comap_residue _ (r (pullback.snd G.hom _ y)))
  · have : IsIso i₀.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i₀.hom))
    rw [← Over.w i₀.hom]
    infer_instance

end GlobalTheory.MultiplicativeTorusSetting

end
end
