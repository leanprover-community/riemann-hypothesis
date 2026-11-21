import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundle
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyFormulaNormalCoverRationalThetaConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

def openRatModel {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) [IsIntegral U.toScheme]
    (hsep : IsSeparated s) (hlft : LocallyOfFiniteType s) (hqc : QuasiCompact (U.ι ≫ s)) :
    letI : Algebra k U.toScheme.functionField :=
      (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
    RatModel k U.toScheme.functionField :=
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  { Z := U.toScheme
    s := U.ι ≫ s
    sep := inferInstance
    lft := inferInstance
    qc := hqc
    pt := U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    pt_s := by
      unfold spMap
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    gen := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, Scheme.fromSpecStalk_closedPoint⟩, ?_⟩
      rintro _ ⟨w, rfl⟩
      have : w = IsLocalRing.closedPoint U.toScheme.functionField :=
        Subsingleton.elim (α := PrimeSpectrum U.toScheme.functionField) _ _
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    onto := fun x => by
      obtain ⟨V, h, a, rfl⟩ := U.toScheme.presheaf.germ_exist (x := genericPoint U.toScheme) x
      exact ⟨V, a, ⟨_, h⟩, GlobalTheory.FlagBundle.valF_fromSpecStalk h a⟩ }

theorem lbIso_of_ratModels : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (A B : LB X), Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → A.IsLB → B.IsLB → (∀ (Ω : Type) [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (io : M.Z ⟶ X), IsOpenImmersion io → io ≫ s = M.s → LBIso (A.pull io) (B.pull io)) → LBIso A B := by
  intro k _ _ X s A B hN hsep hlft hqc hA hB hM
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover X (irreducibleComponents X) GlobalTheory.IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) A B hA hB ?_
  intro Z
  let U := GlobalTheory.IsNormalScheme.component Z
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  have hio : IsOpenImmersion U.ι := by infer_instance
  exact hM _ (openRatModel s U hsep hlft inferInstance) U.ι hio rfl

end GlobalTheory.UMin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_iso_on_rational_model_components : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (A B : LB X), Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → A.IsLB → B.IsLB → (∀ (Ω : Type) [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (io : M.Z ⟶ X), IsOpenImmersion io → io ≫ s = M.s → LBIso (A.pull io) (B.pull io)) → LBIso A B := by
  atlas_forward_decl GlobalTheory.UMin.lbIso_of_ratModels
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.lbIso_detOm_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)),
    (GlobalTheory.FlagMod.detOm Y).IsLB →
      LBIso (GlobalTheory.FlagMod.detOm Y) (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) := by
  intro E _ _ _ H Dw l Xo c Y hO
  exact GlobalTheory.HodgeCech.lbIso_detOm_det Y hO (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detInvariantDiff_iso_hodgeLineBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (GlobalTheory.FlagMod.detOm Y) (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) := by
  atlas_forward_decl GlobalTheory.UMin.lbIso_detOm_hodge
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.GroupBplus

namespace GlobalTheory.BplusDescent

variable {X : Scheme.{0}} [IsIntegral X]

def ringOver (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) : Subring U.Bp :=
  K'.toSubalgebra.toSubring.comap (algebraMap U.Bp (Kbar X))

theorem mem_ringOver {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {x : U.Bp} :
    x ∈ ringOver K' U ↔ (x : Kbar X) ∈ K' := Iff.rfl

def descMod (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Submodule (ringOver K' U) (Fin h → ringOver K' U) where
  carrier := {a | (fun i => (a i : U.Bp)) ∈ L}
  add_mem' {a b} ha hb := by
    have : (fun i => ((a + b) i : U.Bp)) = (fun i => (a i : U.Bp)) + fun i => (b i : U.Bp) := by
      funext i; simp
    change (fun i => ((a + b) i : U.Bp)) ∈ L
    rw [this]; exact L.add_mem ha hb
  zero_mem' := by
    have : (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) = 0 := by funext i; simp
    change (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) ∈ L
    rw [this]; exact L.zero_mem
  smul_mem' c a ha := by
    have : (fun i => ((c • a) i : U.Bp)) = (c : U.Bp) • fun i => (a i : U.Bp) := by
      funext i; simp
    change (fun i => ((c • a) i : U.Bp)) ∈ L
    rw [this]; exact L.smul_mem (c : U.Bp) ha

theorem mem_descMod {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {h : ℕ}
    {L : Submodule U.Bp (Fin h → U.Bp)} {a : Fin h → ringOver K' U} :
    a ∈ descMod K' U L ↔ (fun i => (a i : U.Bp)) ∈ L := Iff.rfl

def IsDescended (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Prop :=
  Module.Finite (ringOver K' U) (descMod K' U L) ∧ Module.Projective (ringOver K' U) (descMod K' U L) ∧
    L = Submodule.span U.Bp {x | ∃ a ∈ descMod K' U L, x = fun i => (a i : U.Bp)}

end GlobalTheory.BplusDescent
end
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

open TensorProduct

theorem map_bot_eq_genericPoint {Y : Scheme.{0}} [IsIntegral Y] {A : Type} [CommRing A] [IsDomain A]
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] :
    j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) = genericPoint Y := by
  have h : genericPoint (Spec (.of A)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum A) :=
    genericPoint_eq_bot_of_affine (.of A)
  rw [← h]
  exact genericPoint_eq_of_isOpenImmersion j

theorem exists_chart_trdeg_eq_relDim {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O) (W : Set Z.X) (hW : IsOpen W)
    (hη : genericPoint Z.X ∈ W) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Z.X)
      (_ : IsOpenImmersion j), Set.range j ⊆ W ∧
      j ≫ Z.str = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Z.relDim := by
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_affine_chart_trdeg_eq Z.str (genericPoint Z.X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq Z.str (hA.symm.trans hd)
  have h₂ := topologicalKrullDim_eq_of_isEmbedding Z.gen.ι.isOpenEmbedding.isEmbedding
    (Z := Z.str ⁻¹' {genericPoint (Spec (.of O))}) (by
      rw [Scheme.Opens.range_ι, genericPoint_eq_bot_of_affine]
      ext x
      exact mem_gen_iff_eq_bot.trans ⟨fun h => PrimeSpectrum.ext h, fun h => congrArg PrimeSpectrum.asIdeal h⟩)
  rw [h₁, topologicalKrullDim_gen] at h₂
  obtain rfl : d = Z.relDim := by exact_mod_cast h₂
  obtain ⟨_, ⟨b, rfl⟩, hb, hbW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (⟨⊥, inferInstance⟩ : PrimeSpectrum A)) (u := j ⁻¹' W)
    ((map_bot_eq_genericPoint j).symm ▸ hη : j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) ∈ W) (hW.preimage j.continuous)
  have hb0 : b ≠ 0 := hb
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hb0
  have : IsDomain (Localization.Away b) := IsLocalization.isDomain_localization hle
  have : FaithfulSMul A (Localization.Away b) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (Localization.Away b) := IsLocalization.isAlgebraic _ (.powers b)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) :=
    .of_isLocalization b
  refine ⟨Localization.Away b, inferInstance, inferInstance, inferInstance,
    .trans (S := A) inferInstance inferInstance, .trans O A _,
    Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbW ((PrimeSpectrum.localization_away_comap_range (Localization.Away b) b).le ⟨x, rfl⟩)
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  · rw [trdeg_eq_of_isAlgebraic_top O A, hd]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem topologicalKrullDim_genFibre : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Z₁ : Model O) (f : Hom Z₁ Z),
    topologicalKrullDim f.genFibre = f.relDim := by
  intro O _ _ _ Z Z₁ f
  refine f.dim_genFibre_le.antisymm ?_
  have hη : f.f (genericPoint Z₁.X) = genericPoint Z.X := by
    have := (genericPoint_spec Z₁.X).image f.f.continuous
    rw [Set.image_univ, f.f.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec Z.X)
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_chart_trdeg_eq_relDim Z Set.univ isOpen_univ trivial
  obtain ⟨B, _, _, _, _, _, j₁, _, hr, hj₁, hB⟩ :=
    exists_chart_trdeg_eq_relDim Z₁ (f.f ⁻¹' Set.range j)
      (j.isOpenEmbedding.isOpen_range.preimage f.f.continuous)
      ⟨_, (map_bot_eq_genericPoint j).trans hη.symm⟩
  have hr' : Set.range (j₁ ≫ f.f) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hr ⟨x, rfl⟩
  let ψ := Spec.preimage (IsOpenImmersion.lift j (j₁ ≫ f.f) hr')
  have hψ : Spec.map ψ ≫ j = j₁ ≫ f.f := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  let : Algebra A B := ψ.hom.toAlgebra
  have hpt (p : PrimeSpectrum B) : f.f (j₁ p) = j (PrimeSpectrum.comap (algebraMap A B) p) :=
    congr($hψ p).symm
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ ψ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hj, ← hj₁, ← Category.assoc, hψ, Category.assoc, f.comp_str]
  have : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq fun a => congr($(hc).hom a).symm
  have : Algebra.FiniteType A B := .of_restrictScalars_finiteType O A B
  have : FaithfulSMul A B := by
    have h := hpt ⟨⊥, inferInstance⟩
    rw [map_bot_eq_genericPoint, hη, ← map_bot_eq_genericPoint j] at h
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
    exact (congrArg PrimeSpectrum.asIdeal (j.isOpenEmbedding.injective h)).symm
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast A (A := B)
  have hadd := trdeg_add_eq O A (A := B)
  rw [hA, hB, he] at hadd
  obtain rfl : e = f.relDim := by
    have h₁ : Z.relDim + e = Z₁.relDim := by exact_mod_cast hadd
    have h₂ := f.relDim_add
    omega
  have := IsLocalization.tensorRight (S := B) (FractionRing A) (nonZeroDivisors A)
  have hemb := j₁.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.localization_comap_isEmbedding (FractionRing A ⊗[A] B)
        (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)))
  rw [← ringKrullDim_genericFibre_eq A (FractionRing A) he,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← topologicalKrullDim_eq_of_isEmbedding hemb rfl]
  refine (QCoh.topologicalKrullDim_mono ?_).trans (topologicalKrullDim_eq_of_isEmbedding
    (f.f.fiberι (genericPoint Z.X)).isEmbedding (f.f.range_fiberι _)).le
  rintro _ ⟨p, rfl⟩
  have hp := (PrimeSpectrum.localization_comap_range (FractionRing A ⊗[A] B)
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))).le ⟨p, rfl⟩
  refine (hpt _).trans ((congrArg j (PrimeSpectrum.ext (eq_bot_iff.2 fun a ha => ?_))).trans
    (map_bot_eq_genericPoint j))
  by_contra h0
  exact Set.disjoint_left.1 hp ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ ha

end GlobalTheory.Vert.Model
end

section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vert.Model

theorem eq_genericPoint_of_isFinite {X N : Scheme.{0}} [IsIntegral X] [IsIntegral N] (ν : N ⟶ X)
    [IsFinite ν] {n : N} (hn : ν n = genericPoint X) : n = genericPoint N := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := hU'.preimage ν
  have hnV : n ∈ ν ⁻¹ᵁ U := show ν n ∈ U from hn ▸ hηU
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : Nonempty (ν ⁻¹ᵁ U) := ⟨⟨_, hnV⟩⟩
  let φ := ν.appLE U (ν ⁻¹ᵁ U) le_rfl
  have hfin : φ.hom.Finite := by
    have := Scheme.Hom.finite_app ν U hU'
    rwa [Scheme.Hom.app_eq_appLE] at this
  letI := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(X, U) Γ(N, ν ⁻¹ᵁ U) :=
    ⟨fun b => hfin.to_isIntegral b⟩
  have hcomm := IsAffineOpen.SpecMap_appLE_fromSpec ν hU' hV le_rfl
  set p := hV.primeIdealOf ⟨n, hnV⟩
  have hp : hV.fromSpec p = n := hV.fromSpec_primeIdealOf ⟨n, hnV⟩
  have h1 : hU'.fromSpec (Spec.map φ p) = hU'.fromSpec ⟨⊥, inferInstance⟩ := by
    rw [map_bot_eq_genericPoint (A := Γ(X, U)) hU'.fromSpec, ← hn, ← hp]
    exact congr($hcomm p)
  have h2 := hU'.fromSpec.isOpenEmbedding.injective h1
  have h3 : p.asIdeal.comap (algebraMap Γ(X, U) Γ(N, ν ⁻¹ᵁ U)) = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h2
  have h4 : p = ⟨⊥, inferInstance⟩ := PrimeSpectrum.ext (Ideal.eq_bot_of_comap_eq_bot h3)
  rw [← hp, h4]
  exact map_bot_eq_genericPoint (A := Γ(N, ν ⁻¹ᵁ U)) hV.fromSpec

theorem exists_normal_hom (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] (Z : Model O) :
    ∃ (Z' : Model O) (n : Model.Hom Z' Z), GlobalTheory.IsNormalScheme Z'.X ∧ n.relDim = 0 := by
  set η := genericPoint Z.X
  let u : Spec (.of (Z.X.residueField η)) ⟶ Z.X := Spec.map (Z.X.residue η) ≫ Z.X.fromSpecStalk η
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ Z.str)
  have hu : u (IsLocalRing.closedPoint (Z.X.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have hφinj : Function.Injective φ.hom := by
    have hη : (Z.str η).asIdeal = ⊥ := mem_gen_iff_eq_bot.1 Z.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint (Z.X.residueField η)) = Z.str η := by
      rw [hφ]
      exact congrArg Z.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero (Z.X.residueField η) := charZero_of_injective_ringHom hφinj
  haveI : CharZero (IsLocalRing.ResidueField (Z.X.presheaf.stalk η)) := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType Z.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) Z.str η (Z.X.residue η)
      (RingHom.FiniteType.of_surjective _ (Z.X.residue_surjective η)).essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ Z.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ Z.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let Z' : Model O :=
    { X := u.normalization
      str := ν ≫ Z.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν Z.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint _), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec Z.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom Z' Z := ⟨ν, rfl⟩
  refine ⟨Z', n, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_⟩
  have hdim := topologicalKrullDim_genFibre O Z Z' n
  haveI : Subsingleton n.genFibre := by
    constructor
    intro a b
    have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint Z'.X := fun c => by
      have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
      exact eq_genericPoint_of_isFinite ν hc
    exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
  have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
  rw [hdim] at h0
  have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
  omega

end GlobalTheory.Vert.Model

end
end

section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem map_normFun {U U' : X.Opens} (hU : genericPoint X ∈ U) (hU' : genericPoint X ∈ U') (h : U' ≤ U) :
    (fieldPt φ).normalization.presheaf.map (homOfLE ((fieldPt φ).fromNormalization.preimage_mono h)).op ≫
      normFun φ hU' = normFun φ hU := by
  rw [normFun, normFun, Scheme.Hom.map_appLE_assoc]

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

theorem exists_normalization_in (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O) (_ : GlobalTheory.IsNormalScheme B.X) (K' : IntermediateField B.X.functionField (Kbar B.X))
    (hK : FiniteDimensional B.X.functionField K') :
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsFinite f.f ∧ (∀ U, Function.Injective (γ U)) ∧
      (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧
      (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)),
        γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) ∧
      ∀ U, (γ U).range = ringOver K' U := by
  set η := genericPoint B.X
  let ψ : B.X.presheaf.stalk (genericPoint B.X) ⟶ .of K' := CommRingCat.ofHom (algebraMap B.X.functionField K')
  let u : Spec (.of K') ⟶ B.X := fieldPt ψ
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ B.str)
  have hu : u (IsLocalRing.closedPoint K') = η := fieldPt_apply ψ _
  have hφinj : Function.Injective φ.hom := by
    have hη : (B.str η).asIdeal = ⊥ := Model.mem_gen_iff_eq_bot.1 B.genericPoint_mem_gen
    have e : Spec.map φ (IsLocalRing.closedPoint K') = B.str η := by
      rw [hφ]
      exact congrArg B.str hu
    rw [RingHom.injective_iff_ker_eq_bot]
    have e' := congrArg PrimeSpectrum.asIdeal e
    rw [hη] at e'
    rw [← e']
    ext a
    change _ ↔ φ.hom a ∈ IsLocalRing.maximalIdeal K'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
    rfl
  haveI : CharZero K' := charZero_of_injective_ringHom hφinj
  haveI : LocallyOfFiniteType B.str := inferInstance
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk (o := .of O) B.str η ψ
      (RingHom.finite_algebraMap.2 hK).finiteType.essFiniteType
  let ν := u.fromNormalization
  haveI : Flat (u.fromNormalization ≫ B.str) := by
    have : Flat (u.toNormalization ≫ u.fromNormalization ≫ B.str) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, ← hφ]
      exact Flat.SpecMap_iff.mpr (flat_of_dedekind_of_injective φ.hom hφinj)
    exact flat_normalization u _
  let B' : Model O :=
    { X := u.normalization
      str := ν ≫ B.str
      isIntegral := inferInstance
      isProjOver := isProjOver_comp_of_isFinite ν B.isProjOver
      flat := ‹_› }
  have hrange : Set.range ν = Set.univ := by
    have hcl : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
    have hmem : η ∈ Set.range ν :=
      ⟨u.toNormalization (IsLocalRing.closedPoint K'), by
        change (u.toNormalization ≫ u.fromNormalization) _ = η
        rw [Scheme.Hom.toNormalization_fromNormalization]
        exact hu⟩
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec B.X).def]
    exact hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  haveI : Surjective ν := ⟨fun x => hrange.ge (Set.mem_univ x)⟩
  let n : Model.Hom B' B := ⟨ν, rfl⟩
  have hx : ∀ U : AffOp B.X, genericPoint B.X ∈ U.1 := fun U =>
    ((genericPoint_spec B.X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)
  have hint : ∀ (U : AffOp B.X) (x : K'), (B.X.presheaf.germ U.1 _ (hx U) ≫ ψ).hom.IsIntegralElem x ↔
      IsIntegral Γ(B.X, U.1) (x : Kbar B.X) := fun U x => by
    refine exists_congr fun p => and_congr_right fun _ => ?_
    rw [← (map_eq_zero_iff K'.val.toRingHom Subtype.val_injective), Polynomial.hom_eval₂]
    rfl
  let γ : ∀ U : AffOp B.X, Γ(B'.X, n.f ⁻¹ᵁ U.1) →+* U.Bp := fun U =>
    (K'.val.toRingHom.comp (normFun ψ (hx U)).hom).codRestrict (integralClosure Γ(B.X, U.1) (Kbar B.X)) fun a =>
      (hint U _).1 (((normFun_spec ψ (hx U) U.2.1).2 _).1 ⟨a, rfl⟩)
  refine ⟨B', n, γ, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, ?_, hfin, fun U a b h => ?_, fun U a => ?_,
    fun U U' hle a => ?_, fun U => ?_⟩
  · have hdim := Model.topologicalKrullDim_genFibre O B B' n
    haveI : Subsingleton n.genFibre := by
      constructor
      intro a b
      have key : ∀ c : n.genFibre, (ν.fiberι η) c = genericPoint B'.X := fun c => by
        have hc : (ν.fiberι η) c ∈ ν ⁻¹' {η} := by
          rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
        exact Model.eq_genericPoint_of_isFinite ν hc
      exact (ν.fiberι η).isEmbedding.injective ((key a).trans (key b).symm)
    have h0 := topologicalKrullDim_zero_of_discreteTopology n.genFibre
    rw [hdim] at h0
    have h1 : n.relDim ≤ 0 := by exact_mod_cast h0
    omega
  · exact (normFun_spec ψ (hx U) U.2.1).1 (Subtype.ext (congrArg (fun z : U.Bp => (z : Kbar B.X)) h))
  · exact Subtype.ext (congrArg (fun g : Γ(B.X, U.1) ⟶ .of K' => (g.hom a : Kbar B.X)) (app_normFun ψ (hx U)))
  · exact Subtype.ext (congrArg (fun g : Γ(B'.X, n.f ⁻¹ᵁ U.1) ⟶ .of K' => (g.hom a : Kbar B.X))
      (map_normFun ψ (hx U) (hx U') hle))
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ((normFun ψ (hx U)).hom a).2
    · intro h
      obtain ⟨a, ha⟩ := ((normFun_spec ψ (hx U) U.2.1).2 ⟨x.1, h⟩).2 ((hint U _).2 x.2)
      exact ⟨a, Subtype.ext (congrArg (fun z : K' => (z : Kbar B.X)) ha)⟩

end GlobalTheory.BplusDescent

end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem isFinite_fromNormalization_fieldPt {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] {L : Type} [Field L] [CharZero L]
    (ψ : X.presheaf.stalk (genericPoint X) ⟶ .of L) (hψ : ψ.hom.Finite) :
    IsFinite (fieldPt ψ).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hne : (U : Set X).Nonempty
  · have hη := genericPoint_mem hne
    haveI : Nonempty U := hne.to_subtype
    letI : Algebra Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) :=
      ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    letI : Algebra Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      (normFun ψ hη).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.presheaf.germ U _ hη ≫ ψ).hom.toAlgebra
    letI : Algebra X.functionField L := ψ.hom.toAlgebra
    haveI : IsScalarTower Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (app_normFun ψ hη)).symm
    haveI := functionField_isFractionRing_of_isAffineOpen X U hU
    haveI : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : FiniteDimensional X.functionField L := hψ
    haveI : CharZero X.functionField := ψ.hom.charZero
    haveI : IsIntegralClosure Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) Γ(X, U) L :=
      ⟨(normFun_spec ψ hη hU).1, fun {x} => ((normFun_spec ψ hη hU).2 x).symm⟩
    exact IsIntegralClosure.finite Γ(X, U) X.functionField L _
  · haveI : Subsingleton Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) := by
      refine subsingleton_of_forall_eq 0 fun s => ?_
      rw [← basicOpen_eq_bot_iff]
      exact eq_bot_iff.2 fun z hz => (hne ⟨_, ((fieldPt ψ).normalization.basicOpen_le s hz :)⟩).elim
    letI := ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    change Module.Finite _ _
    infer_instance

end GlobalTheory.NormCover

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem exists_normalization_model : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω]
    (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω']
    [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z),
      Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ hN
  haveI : GlobalTheory.IsNormalScheme M.Z := GlobalTheory.IsNormalScheme.of_pred hN
  haveI := M.lft
  haveI := M.sep
  haveI := M.qc
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  let ρ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω :=
    M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z)) ≫
      Scheme.stalkClosedPointTo M.pt
  have hρ : fieldPt ρ = M.pt := by
    simp only [fieldPt, ρ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt
  let ψ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω' := ρ ≫ CommRingCat.ofHom (algebraMap Ω Ω')
  have hψ : fieldPt ψ = spMap (algebraMap Ω Ω') ≫ M.pt := by
    rw [← hρ]
    simp only [fieldPt, ψ, Spec.map_comp, Category.assoc]
  have hρs : Function.Surjective ρ.hom := by
    intro x
    obtain ⟨U, f, hU, rfl⟩ := M.onto x
    have hη := genericPoint_mem hU
    refine ⟨M.Z.presheaf.germ U _ hη f, ?_⟩
    have key : ∀ (g : Sp Ω ⟶ M.Z) (_ : fieldPt ρ = g) (e : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ e ≫ (Scheme.ΓSpecIso (.of Ω)).hom = M.Z.presheaf.germ U _ hη ≫ ρ := by
      rintro _ rfl e
      exact fieldPt_appLE ρ hη
    have e := M.top_le_preimage_pt hU
    rw [valF, dif_pos e]
    exact (congrArg (fun g => g.hom f) (key M.pt hρ e)).symm
  have hψfin : ψ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) (RingHom.Finite.of_surjective ρ.hom hρs)
  haveI hfin : IsFinite (fieldPt ψ).fromNormalization := isFinite_fromNormalization_fieldPt ψ hψfin

  have hgen : Set.range (fieldPt ψ).toNormalization = {genericPoint (fieldPt ψ).normalization} := by
    have hc : ∀ w : Sp Ω', w = IsLocalRing.closedPoint Ω' := fun w =>
      Subsingleton.elim (α := PrimeSpectrum Ω') _ _
    have hr : Set.range (fieldPt ψ).toNormalization = {(fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        rw [hc w]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hd : closure (Set.range (fieldPt ψ).toNormalization) = Set.univ := (fieldPt ψ).toNormalization.denseRange.closure_range
    rw [hr] at hd ⊢
    have hg : IsGenericPoint ((fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')) ⊤ := hd
    rw [hg.eq (genericPoint_spec (fieldPt ψ).normalization)]
  have hpts : (fieldPt ψ).toNormalization ≫ (fieldPt ψ).fromNormalization ≫ M.s = spMap (algebraMap k Ω') := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ, Category.assoc, M.pt_s, spMap, spMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have honto : ∀ x : Ω', ∃ (U : (fieldPt ψ).normalization.Opens) (f : Γ((fieldPt ψ).normalization, U)), (U : Set (fieldPt ψ).normalization).Nonempty ∧
      valF (fieldPt ψ).toNormalization U f = x := by
    intro x
    obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint M.Z) (U := ⊤) trivial
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    letI : Algebra Γ(M.Z, U) Ω' := (M.Z.presheaf.germ U _ hηU ≫ ψ).hom.toAlgebra
    letI : Algebra M.Z.functionField Ω' := ψ.hom.toAlgebra
    haveI := functionField_isFractionRing_of_isAffineOpen M.Z U hU
    haveI : IsScalarTower Γ(M.Z, U) M.Z.functionField Ω' := .of_algebraMap_eq' rfl
    haveI : FiniteDimensional M.Z.functionField Ω' := hψfin
    obtain ⟨⟨a, ha⟩, hax⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors Γ(M.Z, U)) x
      (Algebra.IsIntegral.isIntegral (R := M.Z.functionField) x)
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hηV : genericPoint M.Z ∈ M.Z.basicOpen a := by
      refine genericPoint_mem ?_
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => ha0 ((basicOpen_eq_bot_iff a).1 (SetLike.coe_injective h))
    have hV : IsAffineOpen (M.Z.basicOpen a) := hU.basicOpen a
    let r := M.Z.presheaf.map (homOfLE (M.Z.basicOpen_le a)).op
    letI : Algebra Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) := r.hom.toAlgebra
    letI : Algebra Γ(M.Z, M.Z.basicOpen a) Ω' := (M.Z.presheaf.germ _ _ hηV ≫ ψ).hom.toAlgebra
    haveI : IsScalarTower Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' := .of_algebraMap_eq' (by
      have e : r ≫ M.Z.presheaf.germ _ _ hηV = M.Z.presheaf.germ U _ hηU := TopCat.Presheaf.germ_res _ _ _ _
      change (M.Z.presheaf.germ U _ hηU ≫ ψ).hom = (r ≫ M.Z.presheaf.germ _ _ hηV ≫ ψ).hom
      simp only [← e, Category.assoc])
    have hunit : IsUnit (r.hom a) := M.Z.toRingedSpace.isUnit_res_basicOpen a
    have hxV : IsIntegral Γ(M.Z, M.Z.basicOpen a) x := by
      have h1 : IsIntegral Γ(M.Z, M.Z.basicOpen a) (algebraMap Γ(M.Z, U) Ω' a * x) := by
        have := hax.tower_top (A := Γ(M.Z, M.Z.basicOpen a))
        rwa [Submonoid.smul_def, Algebra.smul_def] at this
      have h2 : x = algebraMap Γ(M.Z, M.Z.basicOpen a) Ω' (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) *
          (algebraMap Γ(M.Z, U) Ω' a * x) := by
        rw [IsScalarTower.algebraMap_apply Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' a, ← _root_.mul_assoc, ← map_mul]
        have : (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) * algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) a = 1 :=
          hunit.val_inv_mul
        rw [this, map_one, _root_.one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    obtain ⟨c, hc⟩ := ((normFun_spec ψ hηV hV).2 x).2 hxV
    have hW : ⊤ ≤ (fieldPt ψ).toNormalization ⁻¹ᵁ ((fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a) := by
      intro w _
      show (fieldPt ψ).fromNormalization ((fieldPt ψ).toNormalization w) ∈ M.Z.basicOpen a
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, fieldPt_apply]
      exact hηV
    refine ⟨(fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a, c,
      ⟨_, hW (x := IsLocalRing.closedPoint Ω') trivial⟩, ?_⟩
    rw [valF, dif_pos hW]
    exact hc
  let M' : RatModel k Ω' :=
    { Z := (fieldPt ψ).normalization
      s := (fieldPt ψ).fromNormalization ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := (fieldPt ψ).toNormalization
      pt_s := hpts
      gen := hgen
      onto := honto }
  refine ⟨M', (fieldPt ψ).fromNormalization, (GlobalTheory.IsNormalScheme.normalization_of_isIntegral (fieldPt ψ)).pred _, hfin, ?_⟩
  exact (Scheme.Hom.toNormalization_fromNormalization (fieldPt ψ)).trans hψ

end GlobalTheory.NormCover
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalization_model_finiteExtension : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z), Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  atlas_forward_decl GlobalTheory.NormCover.exists_normalization_model
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH

namespace GlobalTheory.UMin.NormIso

def toFld (K : Type) [Field K] : ((Sp K).presheaf.stalk (IsLocalRing.closedPoint K))ˣ →* Kˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom

theorem toFld_gm {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    (toFld K (gm x _ U a)).val = valF x U a.val := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x U hU
  refine Eq.trans ?_ ((congrArg (fun φ => φ.hom a.val) e).trans (GlobalTheory.Points.valR_eq x U hU _).symm)
  exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((gm_val x _ U h a).trans
    (Scheme.Hom.germ_stalkMap_apply x U (IsLocalRing.closedPoint K) h a.val).symm)

theorem toFld_gm_spMap {K K' : Type} [Field K] [Field K'] (σ : K →+* K') {X : Scheme.{0}} (x : Sp K ⟶ X)
    (U : X.Opens) (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    toFld K' (gm (spMap σ ≫ x) _ U a) = Units.map σ.toMonoidHom (toFld K (gm x _ U a)) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  apply Units.ext
  rw [toFld_gm (spMap σ ≫ x) U (hU (x := spMap σ (IsLocalRing.closedPoint K')) trivial)]
  show _ = σ (toFld K (gm x _ U a)).val
  rw [toFld_gm x U h]
  exact GlobalTheory.Points.valR_spMap_comp σ x U hU _

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] {M : RatModel k Ω}

theorem pt_mem {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : M.pt (IsLocalRing.closedPoint Ω) ∈ U :=
  M.top_le_preimage_pt hU (x := IsLocalRing.closedPoint Ω) trivial

theorem unit_ext_pt {U : M.Z.Opens} {a b : Γ(M.Z, U)ˣ}
    (h : M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = toFld Ω (gm M.pt _ U b)) : a = b := by
  by_cases hU : (U : Set M.Z).Nonempty
  · have e := congrArg Units.val (h (pt_mem hU))
    rw [toFld_gm _ _ (pt_mem hU), toFld_gm _ _ (pt_mem hU)] at e
    exact Units.ext (M.valF_injective hU e)
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hU

theorem exists_unit {U : M.Z.Opens} (c : Ωˣ) (h : ∀ z ∈ U, c.val ∈ M.O z ∧ (c⁻¹).val ∈ M.O z) :
    ∃ a : Γ(M.Z, U)ˣ, M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = c := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
    obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
    have e : f * g = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hg, c.mul_inv])
    exact ⟨⟨f, g, e, (mul_comm _ _).trans e⟩, fun hp => Units.ext ((toFld_gm _ _ hp _).trans hf)⟩
  · exact ⟨1, fun hp => absurd ⟨_, hp⟩ hU⟩

variable {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] {M' : RatModel k Ω'}
  {π : M'.Z ⟶ M.Z}

theorem norm_mem_O [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) {W : M'.Z.Opens}
    (hW : π ⁻¹ᵁ U ≤ W) (f : Γ(M'.Z, W)) : Algebra.norm Ω (valF M'.pt W f) ∈ M.O z := by
  have hH : M.IsHom M' (IsScalarTower.toAlgHom k Ω Ω') π := hπ
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle' : π ⁻¹ᵁ V ≤ W := fun y hy => hW (hle hy)
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have hne' : ((π ⁻¹ᵁ V : M'.Z.Opens) : Set M'.Z).Nonempty := by
    refine ⟨M'.pt (IsLocalRing.closedPoint Ω'), ?_⟩
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ V
    rw [hπ]
    exact M.top_le_preimage_pt hne (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hfin : (π.app V).hom.Finite := IsFinite.finite_app π V hV
  have hint := hfin.to_isIntegral (resG M'.Z hle' f)
  let ρ : Γ(M.Z, V) →+* M.O z := (M.res V hne).codRestrict (M.O z) fun a => by
    rw [M.res_apply]; exact RatModel.valF_mem_O hzV a
  have hc : (algebraMap (M.O z) Ω').comp ρ = (M'.res _ hne').comp (π.app V).hom := by
    ext a
    show algebraMap Ω Ω' (M.res V hne a) = M'.res _ hne' (π.app V a)
    rw [M.res_apply, M'.res_apply, hH.valF_app hne]
    rfl
  have h1 : IsIntegral (M.O z) (valF M'.pt W f) := by
    obtain ⟨P, hP, hP0⟩ := hint
    refine ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, hc, ← M'.valF_resG hle' hne', ← M'.res_apply _ hne', ← Polynomial.hom_eval₂, hP0,
      map_zero]
  have := M.isIntegrallyClosed_O hN z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm Ω h1)
  exact hy ▸ y.2

theorem lbIso_lbPow_finrank [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) (A B : LB M.Z) (e : ℕ)
    (H : LBIso (A.pull π) (B.pull π)) :
    LBIso (lbPow A (Module.finrank Ω Ω' * e)) (lbPow B (Module.finrank Ω Ω' * e)) := by
  obtain ⟨w, hw⟩ := H
  set d := Module.finrank Ω Ω' * e with hd
  let N : Ω'ˣ →* Ωˣ := Units.map (Algebra.norm Ω)
  have hNa : ∀ c : Ωˣ, N (Units.map (algebraMap Ω Ω').toMonoidHom c) = c ^ Module.finrank Ω Ω' := fun c =>
    Units.ext (Algebra.norm_algebraMap c.val)
  have hle : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), π ⁻¹ᵁ ((LB.div (lbPow B d) (lbPow A d)).U p) ≤
      (LB.div (B.pull π) (A.pull π)).U p := fun p y hy =>
    ⟨mem_pull.2 (mem_powChart.1 hy.1), mem_pull.2 (mem_powChart.1 hy.2)⟩
  have hpt : ∀ {U : M.Z.Opens}, M.pt (IsLocalRing.closedPoint Ω) ∈ U →
      π (M'.pt (IsLocalRing.closedPoint Ω')) ∈ U := fun {U} h => by
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ U
    rw [hπ]
    exact M.top_le_preimage_pt ⟨_, h⟩ (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hex : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), ∃ a : Γ(M.Z, (LB.div (lbPow B d) (lbPow A d)).U p)ˣ,
      M.pt (IsLocalRing.closedPoint Ω) ∈ (LB.div (lbPow B d) (lbPow A d)).U p →
      toFld Ω (gm M.pt _ _ a) = N (toFld Ω' (gm M'.pt _ _ (w.s p))) ^ e := fun p => by
    refine exists_unit _ fun z hz => ?_
    have hp := hle p (hpt (pt_mem ⟨z, hz⟩))
    have key : ∀ u : Γ(M'.Z, (LB.div (B.pull π) (A.pull π)).U p)ˣ,
        (N (toFld Ω' (gm M'.pt _ _ u)) ^ e).val ∈ M.O z := fun u => by
      rw [Units.val_pow_eq_pow_val]
      refine pow_mem ?_ e
      show Algebra.norm Ω (toFld Ω' (gm M'.pt _ _ u)).val ∈ _
      rw [toFld_gm _ _ hp]
      exact norm_mem_O hN hπ hz (hle p) _
    refine ⟨key _, ?_⟩
    rw [← inv_pow, ← map_inv, ← map_inv, ← map_inv]
    exact key _
  choose s hs using hex
  refine ⟨⟨s⟩, fun p q => unit_ext_pt fun hy => ?_⟩
  have hy' : M'.pt (IsLocalRing.closedPoint Ω') ∈ (LB.div (B.pull π) (A.pull π)).U p ⊓
      (LB.div (B.pull π) (A.pull π)).U q := ⟨hle p (hpt hy.1), hle q (hpt hy.2)⟩
  have e₁ := congrArg (gm M'.pt (IsLocalRing.closedPoint Ω') _) (hw p q)
  rw [gm_res _ _ _ hy', map_mul, gm_res _ _ _ hy'] at e₁
  replace e₁ := e₁.trans (congrArg (· * _) (gm_div (A.pull π) (B.pull π) _ _ p q hy'))
  rw [gm_pull_g B π _ _ _ _ hy'.1.1 hy'.2.1, gm_pull_g A π _ _ _ _ hy'.1.2 hy'.2.2, hπ] at e₁
  have e₂ := congrArg (fun u => N (toFld Ω' u) ^ e) e₁
  simp only [map_mul, map_inv] at e₂
  have hB : M.pt (IsLocalRing.closedPoint Ω) ∈ B.U (p.1 PUnit.unit) ⊓ B.U (q.1 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.1, mem_powChart.1 hy.2.1⟩
  have hA : M.pt (IsLocalRing.closedPoint Ω) ∈ A.U (p.2 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.2, mem_powChart.1 hy.2.2⟩
  rw [toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hB, toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hA, hNa, hNa] at e₂
  rw [gm_res _ _ _ hy, map_mul, gm_res _ _ _ hy]
  refine Eq.trans ?_ (congrArg (fun u => toFld Ω (u * _)) (gm_div (lbPow A d) (lbPow B d) _ _ p q hy)).symm
  rw [gm_lbPow_g d _ _ _ _ hy.1.1 hy.2.1, gm_lbPow_g d _ _ _ _ hy.1.2 hy.2.2, map_mul, map_mul, map_inv, map_pow,
    map_pow, hs p hy.1, hs q hy.2, e₂, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]

theorem lbIso_lbPow_of_pull : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ M' π A B d hN _ hπ _ _ ⟨e, he⟩ H
  subst he
  exact lbIso_lbPow_finrank hN hπ A B e H

end GlobalTheory.UMin.NormIso
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pow_multiple_degree_descends_normal : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  atlas_forward_decl GlobalTheory.UMin.NormIso.lbIso_lbPow_of_pull
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.KeyOne

theorem isNormalScheme_of_isOpenImmersion {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (h : Geo.Tor.IsNormalScheme X) : Geo.Tor.IsNormalScheme Y := by
  intro y
  obtain ⟨h1, h2⟩ := h (f y)
  let e : X.presheaf.stalk (f y) ≃+* Y.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

theorem exists_lift_of_dense {P U : Scheme.{0}} (i : U ⟶ P) [IsOpenImmersion i] (hi : Dense (Set.range i))
    {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (a : M.Z ⟶ P) [IsOpenImmersion a] :
    ∃ y : Sp Ω ⟶ U, y ≫ i = M.pt ≫ a := by
  have hV : IsOpen (Set.range a) := a.isOpenEmbedding.isOpen_range
  have hne : (Set.range a).Nonempty := ⟨_, M.pt (IsLocalRing.closedPoint Ω), rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hi.inter_open_nonempty _ hV hne
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  have hsub : Set.range (M.pt ≫ a) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have := ((M.pt_specializes w z).map a.continuous).mem_open hU hz
    simpa using this
  exact ⟨IsOpenImmersion.lift i (M.pt ≫ a) hsub, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
    {Ω : Type} [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X) [IsOpenImmersion io] :
    ∃ y : Sp Ω ⟶ Xo.XF c, M.pt ≫ io = y ≫ Y.j := by
  have hid : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 _ from rfl]
      infer_instance
    infer_instance
  haveI := Y.jQ_open
  obtain ⟨y, hy⟩ := exists_lift_of_dense Y.jQ Y.jQ_dense M (io ≫ inv (pullback.fst Y.s (spMap (RingHom.id c.F))))
  refine ⟨y, ?_⟩
  rw [Model.j, ← Category.assoc, hy, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : LBIso (A.pull (g ≫ f)) (B.pull (g ≫ f))) : LBIso ((A.pull f).pull g) ((B.pull f).pull g) := by
  have hA' := pull_isLB hA f
  have hB' := pull_isLB hB f
  rw [← CechPic.cls_eq_iff (pull_isLB hA' g) (pull_isLB hB' g), CechPic.cls_pull hA' g, CechPic.cls_pull hB' g,
    CechPic.cls_pull hA f, CechPic.cls_pull hB f, ← CechPic.pull_comp, ← CechPic.pull_comp,
    ← CechPic.cls_pull hA _ (pull_isLB hA _), ← CechPic.cls_pull hB _ (pull_isLB hB _), CechPic.cls_eq_iff]
  exact h

theorem lbIso_pull_lbPow {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (a b d : ℕ)
    (h : LBIso (lbPow ((lbPow A a).pull f) d) (lbPow ((lbPow B b).pull f) d)) :
    LBIso ((lbPow A (a * d)).pull f) ((lbPow B (b * d)).pull f) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA _) f) (pull_isLB (isLB_lbPow hB _) f),
    CechPic.cls_pull (isLB_lbPow hA _) f, CechPic.cls_pull (isLB_lbPow hB _) f,
    CechPic.cls_lbPow hA, CechPic.cls_lbPow hB]
  rw [← CechPic.cls_eq_iff (isLB_lbPow (pull_isLB (isLB_lbPow hA _) f) _)
    (isLB_lbPow (pull_isLB (isLB_lbPow hB _) f) _), CechPic.cls_lbPow (pull_isLB (isLB_lbPow hA _) f),
    CechPic.cls_lbPow (pull_isLB (isLB_lbPow hB _) f), CechPic.cls_pull (isLB_lbPow hA _) f,
    CechPic.cls_pull (isLB_lbPow hB _) f, CechPic.cls_lbPow hA, CechPic.cls_lbPow hB] at h
  rw [map_nsmul, map_nsmul] at h
  rw [map_nsmul, map_nsmul, mul_nsmul, mul_nsmul, h]

end GlobalTheory.UMin.KeyOne

theorem GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hg Ω _ _ M io hio hs
  haveI := hio
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  have hMn : Geo.Tor.IsNormalScheme M.Z := GlobalTheory.UMin.KeyOne.isNormalScheme_of_isOpenImmersion io Y.normal
  obtain ⟨y, hy⟩ := GlobalTheory.UMin.KeyOne.exists_pt_eq Y M io
  have hpol := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω (y ≫ pullback.fst _ _)
  obtain ⟨⟨θ, hθ⟩, hθup⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ Ω _ hpol
  obtain ⟨Ω', _, _, pt, cc, hfd, -, hdeg, hlist, -⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension Xo.X Xo.univ.t.G Xo.univ.t.PP.L
    Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ m (n + 1) Ω _ θ hm hn hpol
  letI : Algebra c.F Ω' := ((algebraMap Ω Ω').comp (algebraMap c.F Ω)).toAlgebra
  haveI : IsScalarTower c.F Ω Ω' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  obtain ⟨M', π, hM'n, hπf, hπ⟩ := GlobalTheory.T.exists_normalization_model_finiteExtension c.F Ω M Ω' hMn
  have hup := GlobalTheory.T.thetaKeyFormula_normalCover_rational_thetaConstants E H Dw l Xo c o m n f hm hm3 hmu hn hf Y g hg Ω' M' (π ≫ io)
    (spMap (algebraMap Ω Ω') ≫ y) cc hM'n
    (by rw [← Category.assoc, hπ, Category.assoc, hy, Category.assoc])
    (by rw [Category.assoc]; exact ⟨_, pt, hθup _ hθ Ω' (algebraMap Ω Ω'), hlist⟩)
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := pull_isLB (ProjSpace.O1_isLB o n) g
  have hH := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2.isLB_det
  have hA := pull_isLB (isLB_lbPow hO 8) io
  have hB := pull_isLB (isLB_lbPow hH (4 * (n + 1).factorial)) io
  have key := GlobalTheory.T.lineBundleIso_pow_multiple_degree_descends_normal c.F Ω M Ω' M' π _ _ (n + 1).factorial hMn hπf hπ hA hB hdeg
    (GlobalTheory.UMin.KeyOne.lbIso_pull_pull (isLB_lbPow hO 8) (isLB_lbPow hH _) io π hup)
  exact GlobalTheory.UMin.KeyOne.lbIso_pull_lbPow hO hH io 8 (4 * (n + 1).factorial) (n + 1).factorial key
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_map_pull_O1_power_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  atlas_forward_decl GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaPullback

theorem theta_pull_O1_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)) (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hodd hm hunit hn hth Y g hg hdet
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (↥c.F) N
  haveI : IsProper Y.s := by rw [← hs]; infer_instance
  have hvb := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := LB.isLB_pull (ProjSpace.O1_isLB o n) g
  have hA : (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).IsLB := LB.isLB_linComb hO _ _
  have hB : (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
      (4 * (n + 1).factorial * (n + 1).factorial)).IsLB := LB.isLB_linComb hvb.isLB_det _ _
  have hC : (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)).IsLB :=
    LB.isLB_linComb hdet _ _
  have hAB := GlobalTheory.T.lineBundleIso_of_iso_on_rational_model_components (↥c.F) Y.X Y.s _ _ Y.normal inferInstance inferInstance inferInstance hA hB
    (fun Ω _ _ M io hio hio' => GlobalTheory.T.theta_map_pull_O1_power_hodge E H Dw l Xo c o m n f hodd hm hunit hn hth Y g hg Ω M io hio hio')
  have hCB : LBIso (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial))
      (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
        (4 * (n + 1).factorial * (n + 1).factorial)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (GlobalTheory.T.detInvariantDiff_iso_hodgeLineBundle E H Dw l Xo c Y hdet) _ _
  exact LBIso.trans hA hB hC hAB hCB.symm

end GlobalTheory.ThetaPullback
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_map_pull_O1_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)) (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)) := by
  atlas_forward_decl GlobalTheory.ThetaPullback.theta_pull_O1_pow
end
