import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChart

section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace DifferentiableLines.FlagIso

theorem hom_ext_local {W Z : Scheme.{0}} {a a' : W ⟶ Z}
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ W), t ≫ a = t ≫ a') : a = a' :=
  GlobalTheory.hom_ext_of_fromSpecStalk fun x => @h (W.presheaf.stalk x) _ (W.toLocallyRingedSpace.isLocalRing x) (W.fromSpecStalk x)

theorem isIso_restrict {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [IsReduced Z] (O : Z.Opens)
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso (f ∣_ O) := by
  have hm : Mono (f ∣_ O) := ⟨fun {W} a a' e => by
    rw [← cancel_mono (f ⁻¹ᵁ O).ι]
    refine mono W _ _ (fun w => (a w).2) ?_
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]⟩
  have hp : IsProper (f ∣_ O) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› O
  have : IsClosedImmersion (f ∣_ O) := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hp, hm⟩
  have : Surjective (f ∣_ O) := ⟨fun z => by
    obtain ⟨x, hx⟩ := surj z.1 z.2
    exact ⟨⟨x, show f x ∈ O from hx ▸ z.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective _

theorem isIso_of_integral {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [LocallyQuasiFinite f] [IsReduced X]
    [IsIntegral Z] [GlobalTheory.IsNormalScheme Z] (O : Z.Opens) (hO : (O : Set Z).Nonempty)
    (dO : Dense ((f ⁻¹ᵁ O : X.Opens) : Set X))
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso f := by
  have := isIso_restrict f O mono surj
  have hne : Nonempty O := hO.to_subtype
  have hne' : Nonempty O.toScheme := hO.to_subtype
  have : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have h1 : IsIrreducible (Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn
  have h2 : Set.range (inv (f ∣_ O) ≫ (f ⁻¹ᵁ O).ι) = ((f ⁻¹ᵁ O : X.Opens) : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, (inv (f ∣_ O)).surjective.range_comp, Scheme.Opens.range_ι]
  have : IrreducibleSpace X := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← dO.closure_eq, ← h2]
    exact h1.closure
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational f GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk O hne

theorem isIso_of_normal {X Z : Scheme.{0}} (f : X ⟶ Z) [IsProper f] [LocallyQuasiFinite f] [IsReduced X]
    [IsLocallyNoetherian Z] (hZ : IsNormalScheme Z) (O : Z.Opens) (hO : Dense (O : Set Z))
    (dO : Dense ((f ⁻¹ᵁ O : X.Opens) : Set X))
    (mono : ∀ (W : Scheme.{0}) (a a' : W ⟶ X), (∀ w, f (a w) ∈ O) → a ≫ f = a' ≫ f → a = a')
    (surj : ∀ z ∈ O, ∃ x, f x = z) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme) fun z => ?_
  let V : Z.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩
  have hz : z ∈ V := mem_irreducibleComponent
  refine ⟨V, hz, ?_⟩
  have : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_component _
  have : IsProper (f ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsProper) ‹_› V
  have : LocallyQuasiFinite (f ∣_ V) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (isPullback_morphismRestrict f V).flip ‹_›
  refine isIso_of_integral (f ∣_ V) (V.ι ⁻¹ᵁ O) ?_ ?_ (fun W a a' ha e => ?_) fun y hy => ?_
  · obtain ⟨y, hy, hy'⟩ := hO.inter_open_nonempty V V.isOpen ⟨z, hz⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  · rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]
    exact dO.preimage (f ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  · rw [← cancel_mono (f ⁻¹ᵁ V).ι]
    refine mono W _ _ (fun w => ?_) ?_
    · have := ha w
      change ((f ∣_ V) (a w)).1 ∈ O at this
      rwa [morphismRestrict_base_coe] at this
    · rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, e, Category.assoc]
  · obtain ⟨x, hx⟩ := surj y.1 hy
    exact ⟨⟨x, show f x ∈ V from hx ▸ y.2⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩

theorem exists_fac {S : Type} [CommRing S] [IsLocalRing S] {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (t : Sp S ⟶ X) (h : t (IsLocalRing.closedPoint S) ∈ Set.range j) : ∃ t' : Sp S ⟶ U, t' ≫ j = t :=
  ⟨IsOpenImmersion.lift j t (by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map t.continuous).mem_open j.isOpenEmbedding.isOpen_range h),
    IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_glue {X Z : Scheme.{0}}
    (R : ∀ (S : Type) [CommRing S] [IsLocalRing S], (Sp S ⟶ X) → (Sp S ⟶ Z) → Prop)
    (uniq : ∀ (S : Type) [CommRing S] [IsLocalRing S] t z z', R S t z → R S t z' → z = z')
    (loc : ∀ x : X, ∃ (U : Scheme.{0}) (j : U ⟶ X) (_ : IsOpenImmersion j) (a : U ⟶ Z), x ∈ Set.range j ∧
      ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ U), R S (t ≫ j) (t ≫ a)) :
    ∃ h : X ⟶ Z, ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ X), R S t (t ≫ h) := by
  choose U j hj a hx hR using loc
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X U j (fun x => ⟨x, hx x⟩) hj
  have hc : ∀ x y : X, pullback.fst (j x) (j y) ≫ a x = pullback.snd _ _ ≫ a y := fun x y =>
    hom_ext_local fun S _ _ t => by
      have h1 := hR x S (t ≫ pullback.fst (j x) (j y))
      have h2 := hR y S (t ≫ pullback.snd (j x) (j y))
      have e : (t ≫ pullback.snd (j x) (j y)) ≫ j y = (t ≫ pullback.fst (j x) (j y)) ≫ j x := by
        rw [Category.assoc, Category.assoc]
        exact congrArg (t ≫ ·) (pullback.condition (f := j x) (g := j y)).symm
      rw [e] at h2
      rw [← Category.assoc, ← Category.assoc]
      exact uniq S _ _ _ h1 h2
  refine ⟨𝒰.glueMorphisms a hc, fun S _ _ t => ?_⟩
  obtain ⟨x, t', rfl⟩ : ∃ (x : X) (t' : Sp S ⟶ U x), t' ≫ j x = t :=
    ⟨_, exists_fac (j (t (IsLocalRing.closedPoint S))) t (hx _)⟩
  have e : j x ≫ 𝒰.glueMorphisms a hc = a x := 𝒰.ι_glueMorphisms a hc x
  rw [Category.assoc t' (j x) (𝒰.glueMorphisms a hc), e]
  exact hR x S t'

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {V : X.Opens} (O : X.Opens) (hO : Dense (O : Set X))
    (s : Γ(X, V)) (h : X.presheaf.map (homOfLE (inf_le_left : V ⊓ O ≤ V)).op s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff] at h ⊢
  rw [Scheme.basicOpen_res] at h
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := hO.inter_open_nonempty _ (X.basicOpen s).isOpen
    ((Opens.not_nonempty_iff_eq_bot _).not.2 hne |> not_not.1)
  have : x ∈ V ⊓ O ⊓ X.basicOpen s := ⟨⟨X.basicOpen_le s hx, hx'⟩, hx⟩
  rw [h] at this
  exact this

end DifferentiableLines.FlagIso
end

section
noncomputable section

namespace DifferentiableLines.FlagIso

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str pm)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
open GlobalTheory GlobalTheory.CompHS Matrix
attribute [local instance] Over.cartesianMonoidalCategory

theorem initSpan_eq_of_tri {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} {v v' : Fin m → N}
    {B : Matrix (Fin m) (Fin m) R} (hB : B.BlockTriangular id) (hu : ∀ i, IsUnit (B i i))
    (h : ∀ i, v' i = ∑ j, B j i • v j) (i : ℕ) : initSpan R v' i = initSpan R v i := by
  have hd : IsUnit B.det := by
    rw [Matrix.det_of_isUpperTriangular hB]
    exact IsUnit.prod_univ_iff.2 hu
  let := Matrix.invertibleOfIsUnitDet B hd
  refine le_antisymm (initSpan_le_of_tri hB h i)
    (initSpan_le_of_tri (Matrix.blockTriangular_inv_of_blockTriangular hB) (fun i => ?_) i)
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e : ∀ k, ∑ j, B⁻¹ j i * B k j = (1 : Matrix (Fin m) (Fin m) R) k i := fun k => by
    rw [← Matrix.mul_nonsing_inv B hd, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  simp [e, Matrix.one_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {S S' : Type} [CommRing S] [CommRing S']

theorem exists_y (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ LogKS.interior Y) :
    ∃ (_ : Algebra c.F S) (y : Sp S ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ∧ x = y ≫ Y.j := by
  let y := IsOpenImmersion.lift Y.j x (by
    rintro _ ⟨q, rfl⟩
    exact h (Set.mem_univ q))
  exact ⟨((ev (y ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra, y, (spMap_ev_top _).symm,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩

theorem step_le_bc {Z Z' : Scheme.{0}} {π : Z ⟶ Y.X} {π' : Z' ⟶ Y.X} (F : Frames Y π) (F' : Frames Y π')
    {z : Sp S ⟶ Z} {z' : Sp S ⟶ Z'} {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π' = x) {k : F.J}
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (i : ℕ) (h : F.step z hx σ i ≤ F'.step z' hx' σ i) (φ : S →+* S')
    {x₁ : Sp S' ⟶ Y.X} (h₁ : (spMap φ ≫ z) ≫ π = x₁) (h₁' : (spMap φ ≫ z') ≫ π' = x₁) :
    F.step (spMap φ ≫ z) h₁ σ i ≤ F'.step (spMap φ ≫ z') h₁' σ i := by
  have e : spMap φ ≫ x = x₁ := by rw [← h₁, Category.assoc, hx]
  rw [F.step_eq k _ (le_preimage_comp _ hz)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rw [← F.tanPull_vecAt k φ z hz _ hx h₁ e]
  refine F'.tanPull_mem_step φ z' hx' rfl h₁' e σ i (h ?_)
  rw [F.step_eq k z hz]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

variable (p : Proj (RingHom.id c.F))

theorem pm_mul_u (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) :
    (pm p (X.F.M k).toMChart σ).map (X.π.appLE (X.F.M k).U (X.F.U k) (X.F.le k)).hom * X.F.u k σ = X.F.u k σ := by
  refine Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_dense (flagOpen X) (dense_flagOpen X) _ ?_)
  change resG X.YY inf_le_left _ = 0
  refine ext_ev fun S _ z hz => ?_
  have hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k := le_preimage_mono inf_le_left hz
  obtain ⟨_, y, hy, hx⟩ := exists_y (z ≫ X.π) (le_preimage_mono inf_le_right hz : ⊤ ≤ z ⁻¹ᵁ flagOpen X)
  have hM := X.F.inM hk hx
  have h1 : X.F.vecAt k z hk hx σ j ∈ eigLie c (y ≫ Y.j) σ := by
    rw [← X.top S y hy z hx k hk σ]
    exact Submodule.subset_span ⟨j, j.2, rfl⟩
  have h2 := congrFun (((LowRank.pm_gen p (X.F.M k).toMChart σ hy hM).1 _).1 ((vec_mem_eigLie _ _ hM σ _).1 h1)) i
  rw [ev_res z _ hz hk, map_zero, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) h2
  rw [map_mul, Matrix.map_apply, ev_appLE z X.π _ hk (hx ▸ hM), ev_congr hx _ _ hM]
  rfl

theorem pm_fix (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ X.π = x) (M : MChart Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U) (j : Fin (Dw.mult σ)) (cv : Fin M.n → S)
    (h : vec M x hM cv = X.F.vecAt k z hz hx σ j) : ((pm p M σ).map (ev x M.U hM)) *ᵥ cv = cv := by
  subst hx
  apply (vec M _ hM).injective
  rw [LowRank.vec_pm, h, Frames.vecAt, ← LowRank.vec_pm]
  congr 1
  funext i
  have e := congrArg (ev z _ hz) (congrFun (congrFun (pm_mul_u p X k σ) i) j)
  rw [Matrix.mul_apply, map_sum] at e
  rw [Matrix.mulVec, dotProduct]
  refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) e
  rw [map_mul, Matrix.map_apply, Matrix.map_apply, ev_appLE z X.π _ hz (X.F.inM hz rfl)]
  rfl

variable {p}

theorem exists_strictHenselian_absolutely_closed_local_ring (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ X.π = x) (e : ECh Y p) (h : ⊤ ≤ x ⁻¹ᵁ e.V) (hM : ⊤ ≤ x ⁻¹ᵁ e.M.U) :
    ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, IsUnit T.det ∧ ∀ j, X.F.vecAt k z hz hx σ j =
      vec e.M.toMChart x hM (fun r => (((e.u σ).map (ev x _ h)) * T) r j) := by
  have ex : ∀ j, ∃ a, ((e.u σ).map (ev x _ h)) *ᵥ a = (vec e.M.toMChart x hM).symm (X.F.vecAt k z hz hx σ j) :=
    fun j => (e.fix_iff σ x h hM _).1 (pm_fix p X k σ z hz hx e.M.toMChart hM j _ (LinearEquiv.apply_symm_apply _ _))
  choose a ha using ex
  have hv : ∀ j, X.F.vecAt k z hz hx σ j = vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j) := fun j => by
    rw [ha, LinearEquiv.apply_symm_apply]
  refine ⟨Matrix.of fun r j => a j r, ?_, hv⟩
  obtain ⟨w, hw⟩ := X.F.uAt_split k z hz σ
  let L : (Fin (Dw.mult σ) → S) →ₗ[S] (Fin (Dw.mult σ) → S) :=
    w.mulVecLin ∘ₗ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm.toLinearMap ∘ₗ
      (vec e.M.toMChart x hM).toLinearMap ∘ₗ ((e.u σ).map (ev x _ h)).mulVecLin
  have h1 : LinearMap.toMatrix' L * (Matrix.of fun r j => a j r) = 1 := by
    ext i j
    have e1 : L (a j) = fun i => (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j := by
      change w *ᵥ (vec (X.F.M k).toMChart x (X.F.inM hz hx)).symm
        (vec e.M.toMChart x hM (((e.u σ).map (ev x _ h)) *ᵥ a j)) = _
      rw [← hv, Frames.vecAt, LinearEquiv.symm_apply_apply, ← hw]
      rfl
    have e2 := congrFun ((LinearMap.toMatrix'_mulVec L (a j)).trans e1) i
    exact e2
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, _root_.mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

theorem T_bc (X : FlagCover Y) (k : X.F.J) (σ : E →+* ℂ) (z : Sp S ⟶ X.YY) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k)
    (e : ECh Y p) (h : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ e.V) (hM : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ e.M.U)
    (T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (hT : ∀ j, X.F.vecAt k z hz rfl σ j =
      vec e.M.toMChart _ hM (fun r => (((e.u σ).map (ev _ _ h)) * T) r j)) (φ : S →+* S')
    (hz₁ : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ X.F.U k) (h₁ : ⊤ ≤ ((spMap φ ≫ z) ≫ X.π) ⁻¹ᵁ e.V)
    (hM₁ : ⊤ ≤ ((spMap φ ≫ z) ≫ X.π) ⁻¹ᵁ e.M.U) (j : Fin (Dw.mult σ)) :
    X.F.vecAt k (spMap φ ≫ z) hz₁ rfl σ j =
      vec e.M.toMChart _ hM₁ (fun r => (((e.u σ).map (ev _ _ h₁)) * T.map φ) r j) := by
  have e₁ : spMap φ ≫ z ≫ X.π = (spMap φ ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  rw [← X.F.tanPull_vecAt k φ z hz hz₁ rfl rfl e₁, hT, tanPull_vec _ φ e₁ hM hM₁]
  congr 1
  funext r
  have hev : (e.u σ).map (ev ((spMap φ ≫ z) ≫ X.π) _ h₁) = ((e.u σ).map (ev _ _ h)).map φ := by
    ext r s
    simp only [Matrix.map_apply]
    rw [ev_congr e₁.symm _ h₁ (le_preimage_comp _ h), ev_spMap φ _ _ h]
    rfl
  rw [hev, ← Matrix.map_mul]
  rfl

variable {A : Atlas Y p} {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)
  (ht : FlagCellFrameChangeTriangular hZ)

theorem exists_cell_pt (b : A.B) {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V) (hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U)
    (T : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (w : Pm Dw.mult)
    (hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ),
      IsUnit (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ (z' : Sp S ⟶ Z) (hx' : z' ≫ π = x) (_ : ⊤ ≤ z' ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult)),
      ∀ σ i, initSpan S (fun j => vec (A.k b).M.toMChart x hM
        (fun r => ((((A.k b).u σ).map (ev x _ h)) * T σ) r j)) i = (cellFrames hZ ht).step z' hx' σ i := by
  choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors S (Dw.mult σ) ((T σ).submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* S := ev x _ h
  let xc : CellVar Dw.mult → S := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = x := hzπ.trans (spMap_ev _ (A.V b).2 h)
  refine ⟨_, hx, hz, fun σ n => ?_⟩
  rw [(cellFrames hZ ht).step_eq _ _ hz]
  refine initSpan_eq_of_tri (hU σ) (hUu σ) (fun i => ?_) n
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * T σ = ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * T σ) r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

def Rel (X : FlagCover Y) (z : Sp S ⟶ X.YY) (z' : Sp S ⟶ Z) : Prop :=
  ∃ hx' : z' ≫ π = z ≫ X.π, ∀ σ i, (cellFrames hZ ht).step z' hx' σ i = X.F.step z rfl σ i

theorem exists_local (X : FlagCover Y) (y : X.YY) :
    ∃ (U : Scheme.{0}) (j : U ⟶ X.YY) (_ : IsOpenImmersion j) (a : U ⟶ Z), y ∈ Set.range j ∧
      ∀ (S : Type) [CommRing S] [IsLocalRing S] (t : Sp S ⟶ U), Rel hZ ht X (t ≫ j) (t ≫ a) := by
  classical
  have hy : y ∈ ⨆ k, X.F.U k := by rw [X.F.cover]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
  obtain ⟨b, hb⟩ := A.cov (X.π y)
  obtain ⟨_, ⟨(W : X.YY.Opens), hW, rfl⟩, hyW, hle⟩ := X.YY.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V : X.YY.Opens) : Set X.YY) from ⟨hk, hb⟩) (Opens.isOpen _)
  have hle' : W ≤ X.F.U k ⊓ X.π ⁻¹ᵁ (A.k b).V := hle
  let R : Type := Γ(X.YY, W)
  let z₀ : Sp R ⟶ X.YY := tau hW
  have : IsOpenImmersion z₀ := IsAffineOpen.isOpenImmersion_fromSpec hW
  have hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ X.F.U k := tau_le hW (hle'.trans inf_le_left)
  have h₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).V := tau_le hW (hle'.trans inf_le_right)
  have hM₀ : ⊤ ≤ (z₀ ≫ X.π) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₀
  obtain ⟨q, hq⟩ : y ∈ Set.range z₀ := hW.range_fromSpec.ge hyW
  let q' : PrimeSpectrum R := q
  choose T hTu hT using fun σ => exists_strictHenselian_absolutely_closed_local_ring X k σ z₀ hz₀ rfl (A.k b) h₀ hM₀
  choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem R _ (T σ) q'.asIdeal q'.2
    fun h => q'.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  let m : (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1)) → R := fun i =>
    (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det
  let f : R := ∏ i, m i
  have hf : f ∉ q'.asIdeal := fun h => by
    have := q'.2
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hw i.1 _ _ hi
  let φ : R →+* Localization.Away f := algebraMap _ _
  have hφ : ∀ i, IsUnit (φ (m i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem m (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f)
  have : IsOpenImmersion (spMap φ) := IsOpenImmersion.of_isLocalization (R := CommRingCat.of R)
    (S := CommRingCat.of (Localization.Away f)) f
  have hz₁ : ⊤ ≤ (spMap φ ≫ z₀) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz₀
  have e₁ : spMap φ ≫ z₀ ≫ X.π = (spMap φ ≫ z₀) ≫ X.π := (Category.assoc _ _ _).symm
  have h₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).V := e₁ ▸ le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ ((spMap φ ≫ z₀) ≫ X.π) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  obtain ⟨z', hx', hz', hs⟩ := exists_cell_pt hZ ht b h₁ hM₁ (fun σ => (T σ).map φ) w fun σ n hn => by
    have h := hφ ⟨σ, ⟨n, Nat.lt_succ_of_le hn⟩⟩
    have e : (((T σ).map φ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn) =
        φ.mapMatrix (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hn) (Fin.castLE hn)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  have hs' : ∀ σ i, (cellFrames hZ ht).step z' hx' σ i = X.F.step (spMap φ ≫ z₀) rfl σ i := fun σ i =>
    (hs σ i).symm.trans ((congrArg (fun v => initSpan _ v i)
      (funext (T_bc X k σ z₀ hz₀ (A.k b) h₀ hM₀ (T σ) (hT σ) φ hz₁ h₁ hM₁))).symm.trans
        (X.F.step_eq k _ hz₁ rfl σ i).symm)
  refine ⟨_, spMap φ ≫ z₀, inferInstance, z', ?_, fun S _ _ t => ?_⟩
  · obtain ⟨q₁, hq₁⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge
      (show q' ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) from hf)
    have h3 : spMap φ (show Sp (Localization.Away f) from q₁) = q := hq₁
    exact ⟨q₁, (Scheme.Hom.comp_apply (spMap φ) z₀ _).trans ((congrArg z₀ h3).trans hq)⟩
  · obtain ⟨ψ, rfl⟩ : ∃ ψ : Localization.Away f →+* S, spMap ψ = t := ⟨_, spMap_ev_top t⟩
    have hx₂ : (spMap ψ ≫ z') ≫ π = (spMap ψ ≫ spMap φ ≫ z₀) ≫ X.π := by
      rw [Category.assoc, hx', ← Category.assoc]
    exact ⟨hx₂, fun σ i => le_antisymm (step_le_bc _ _ hx' rfl hz' σ i (hs' σ i).le ψ hx₂ rfl)
      (step_le_bc _ _ rfl hx' hz₁ σ i (hs' σ i).ge ψ rfl hx₂)⟩

end DifferentiableLines.FlagIso
end
end

section
noncomputable section

namespace DifferentiableLines.FlagIso

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str pm)
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CompHS
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {S : Type} [CommRing S]

theorem step_congr {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (e : z = z')
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    F.step z hx σ i = F.step z' hx' σ i := by
  subst e; rfl

theorem dense_interior {Z : Scheme.{0}} (π : Z ⟶ Y.X) (h : Dense (genMap π ⁻¹' Set.range Y.jQ)) :
    Dense ((π ⁻¹ᵁ LogKS.interior Y : Z.Opens) : Set Z) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  let r := pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))
  refine (r.surjective.denseRange.dense_image r.continuous h).mono ?_
  rintro _ ⟨z, ⟨x, hx⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [Model.j, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, FlagMod.genMap,
    pullback.lift_fst]

theorem lies_of_step [Algebra c.F S] (X : FlagCover Y) (z : Sp S ⟶ X.YY) (Q : FrPt Xo c S) (k : X.F.J)
    (hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hx : z ≫ X.π = frX Q ≫ Y.j)
    (h : ∀ σ i, initSpan S (frVec Y Q rfl σ) i = X.F.step z hx σ i) : X.F.Lies z Q := by
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y Q rfl σ i = ∑ j, b j i • X.F.vecAt k z hk hx σ j := fun σ =>
    exists_tri_of_eq (X.F.linearIndependent_vecAt k z hk hx σ) fun i => (h σ i).trans (X.F.step_eq k z hk hx σ i)
  choose U hU hu hv using ex
  exact GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart E H Dw l Xo c c.F (RingHom.id c.F) Y X.YY X.π X.F X.top S Q z k hk hx U hU hu hv

theorem step_eq_of_rfl {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (hx' : z' ≫ π = z ≫ π)
    (h : ∀ σ i, F.step z' hx' σ i = F.step z rfl σ i) {x : Sp S ⟶ Y.X} (e : z ≫ π = x) (e' : z' ≫ π = x)
    (σ : E →+* ℂ) (i : ℕ) : F.step z' e' σ i = F.step z e σ i := by
  subst e
  exact h σ i

theorem eq_of_step [IsLocalRing S] (X : FlagCover Y) (z z' : Sp S ⟶ X.YY) (hx' : z' ≫ X.π = z ≫ X.π)
    (hi : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ LogKS.interior Y) (h : ∀ σ i, X.F.step z' hx' σ i = X.F.step z rfl σ i) : z' = z := by
  obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing X.F.cover z'
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hx k hk
  have hl : X.F.Lies z Q := hQ.lies
  have e : z ≫ X.π = frX Q ≫ Y.j := hl.1
  have e' : z' ≫ X.π = frX Q ≫ Y.j := hx'.trans e
  have hl' : X.F.Lies z' Q := lies_of_step X z' Q k' hk' e' fun σ i =>
    (hl.initSpan_eq hk e rfl σ i).trans (step_eq_of_rfl X.F hx' h e e' σ i).symm
  exact (X.rep S Q).unique hl' hl

variable {p : Proj (RingHom.id c.F)} {A : Atlas Y p} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
  {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)
  (ht : FlagCellFrameChangeTriangular hZ)

theorem Rel.step_eq {X : FlagCover Y} {z : Sp S ⟶ X.YY} {z' : Sp S ⟶ Z} (h : Rel hZ ht X z z') {x : Sp S ⟶ Y.X}
    (hx : z ≫ X.π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    (cellFrames hZ ht).step z' hx' σ i = X.F.step z hx σ i := by
  subst hx
  exact h.2 σ i

include hZ in

theorem exists_iso (M : FlagModel Y) : ∃ h : M.YY ⟶ Z, IsIso h ∧ h ≫ π = M.π := by
  have ht := GlobalTheory.T.flagCellFrameChangeTriangular_of_cells E H Dw l Xo c Y p A Z π g κ hZ
  have hT := GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht
  have hu := GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht
  obtain ⟨h, hR⟩ := exists_glue (fun S _ _ z z' => Rel hZ ht M.toFlagCover z z')
    (fun S _ _ t z z' h h' => hu S z z' _ h.1 h'.1 fun σ i => (h.2 σ i).trans (h'.2 σ i).symm)
    (exists_local hZ ht M.toFlagCover)
  have hπ : h ≫ π = M.π := hom_ext_local fun S _ _ t => (Category.assoc _ _ _).symm.trans (hR S t).1
  have two : ∀ (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ M.YY), z' ≫ h = z ≫ h →
      ∃ hx : z' ≫ M.π = z ≫ M.π, ∀ σ i, M.F.step z' hx σ i = M.F.step z rfl σ i := fun S _ _ z z' e => by
    have hx : z' ≫ M.π = z ≫ M.π := by rw [← hπ, ← Category.assoc, e, Category.assoc]
    refine ⟨hx, fun σ i => ?_⟩
    rw [← (hR S z').step_eq hZ ht hx ((hR S z').1.trans hx), ← (hR S z).step_eq hZ ht rfl (hR S z).1]
    exact step_congr _ e _ _ σ i
  refine ⟨h, ?_, hπ⟩
  have := hZ.proper
  have : IsProper (h ≫ π) := hπ ▸ M.proper
  have : IsProper h := IsProper.of_comp h π
  have : LocallyQuasiFinite h := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points h fun Ω _ _ y => by
    rcases isEmpty_or_nonempty {x : Spec (.of Ω) ⟶ M.YY // x ≫ h = y} with h0 | ⟨⟨z, hz⟩⟩
    · infer_instance
    · exact ((M.fin Ω z).subset fun z' (hz' : z' ≫ h = y) => two Ω z z' (hz'.trans hz.symm)).to_subtype
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (π ≫ Y.s)
  have : IsReduced M.YY := isReduced_flag M.toFlagCover
  refine isIso_of_normal h hZ.normal (π ⁻¹ᵁ LogKS.interior Y)
    (dense_interior π (GlobalTheory.T.dense_flagBundle_preimage_moduli E H Dw l Xo c Y p A Z π g κ hZ)) ?_ (fun W a a' ha e => ?_) fun w hw => ?_
  · rw [← Scheme.Hom.comp_preimage, hπ]
    exact dense_interior M.π M.dense
  · refine hom_ext_local fun S _ _ t => ?_
    obtain ⟨hx, hs⟩ := two S (t ≫ a) (t ≫ a') (by rw [Category.assoc, Category.assoc, e])
    refine (eq_of_step M.toFlagCover _ _ hx (fun q _ => ?_) hs).symm
    have := ha (t q)
    rw [← hπ]
    exact this
  · let K : Type := Z.residueField w
    let t : Sp K ⟶ Z := Z.fromSpecResidueField w
    have hi : ⊤ ≤ (t ≫ π) ⁻¹ᵁ LogKS.interior Y := fun q _ => by
      have e : t q = w := Scheme.fromSpecResidueField_apply w q
      change π (t q) ∈ LogKS.interior Y
      rw [e]
      exact hw
    obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover t
    obtain ⟨Q, hQ⟩ := hT.exists_chartFr hy hx k' hk'
    have hl' := hQ.lies
    have hl := M.lies_ptY Q
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing M.F.cover (M.ptY Q)
    have e : M.ptY Q ≫ h = t := hu K _ _ _ ((hR K _).1.trans hl.1) hl'.1 fun σ i => by
      rw [(hR K _).step_eq hZ ht hl.1, ← hl.initSpan_eq hk hl.1 rfl, hl'.initSpan_eq hk' hl'.1 rfl]
    let q : Sp K := IsLocalRing.closedPoint K
    refine ⟨M.ptY Q q, ?_⟩
    rw [← Scheme.Hom.comp_apply, e]
    exact Scheme.fromSpecResidueField_apply w _

end DifferentiableLines.FlagIso

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem DifferentiableLines.flag_model_projective_embedding_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (M' : GlobalTheory.FlagMod.FlagModel Y) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, M'.YY ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ M'.YY)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A M'.π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∀ M : GlobalTheory.FlagMod.FlagModel Y, ∃ h : M.YY ⟶ M'.YY, IsIso h ∧ h ≫ M'.π = M.π := by
  intro E _ _ _ H Dw l Xo c Y p A M' g κ hκ hZ _ M
  exact DifferentiableLines.FlagIso.exists_iso hZ M
end
end
