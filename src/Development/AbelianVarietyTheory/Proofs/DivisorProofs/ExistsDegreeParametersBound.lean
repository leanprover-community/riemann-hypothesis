import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParametersStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDegreeLeWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagComponentDeepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecondStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_supLattice_component_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  first | exact @GlobalTheory.CompHS.Ready.degM_eq | exact GlobalTheory.CompHS.Ready.degM_eq | (intros; apply GlobalTheory.CompHS.Ready.degM_eq <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.ImageHeightFrame

theorem isImageHeight_unique : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh hh' => ImageHeightUnique.isImageHeight_unique hh hh'

end GlobalTheory.ImageHeightFrame
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedImageHeight_unique_frame : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' := by
  atlas_forward_decl GlobalTheory.ImageHeightFrame.isImageHeight_unique
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem GlobalTheory.HSCore.isHeight_imageHeight : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), IsTotallyComplex F → T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → T.IsHeight (CompHt.imageHeight Nm W ev T.D) := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hF hT hB hP
  obtain ⟨h, hh⟩ := GlobalTheory.Adelic.HeightExists.exists_isHeight F T.toHermSys hT.alg
    (GlobalTheory.ImageDegree.degree_image_eq_topSelf hQ F T.toLinSys hT.alg.variety hT.alg.bpf hB).1
  have h1 := hP.isImageHeight hh
  rwa [GlobalTheory.T.normalisedImageHeight_unique_frame hQ F V Ω Nm W ev T.D _ h hF (CompHt.isImageHeight_imageHeight ⟨h, h1⟩) h1]
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_birationalImage_eq_tuple_height : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), IsTotallyComplex F → T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → T.IsHeight (CompHt.imageHeight Nm W ev T.D) := by
  atlas_forward_decl GlobalTheory.HSCore.isHeight_imageHeight
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SysHyp

variable {F : Type} [Field F] [NumberField F]

theorem mulW_comm (G : Geo F) (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [Geo.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun i c y hy hi hc => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc,
    germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc]
  exact mul_left_comm _ _ _

theorem shift_comm (G : Geo F) (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · change G.mulW 0 u 0 = G.mulW 0 v 0
    rw [map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (G : Geo F) (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext l
  rcases l with _ | l
  · rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]
    rfl
  · change G.mulW l u ((Pi.single j m : Tot G) l) = _
    by_cases h : l = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (Nat.succ_injective e)), map_zero]

variable (X : Data F)

theorem coe_inclEquiv (j : ℕ) (x : X.V j) :
    (inclEquiv X j x : Tot X.toGeo) = Pi.single j (x : X.Sec j) := rfl

theorem coe_eq_single (j : ℕ) (x : LinearMap.range (incl X j)) :
    (x : Tot X.toGeo) = Pi.single j ((inclEquiv X j).symm x : X.Sec j) := by
  rw [← coe_inclEquiv, LinearEquiv.apply_symm_apply]

theorem isFull (Λ₀ : ℝ) (j : ℕ) : IsFull ((sysOf X Λ₀).M j) := by
  refine ⟨(X.full j).fg.map _, ?_⟩
  change Submodule.span F ((inclEquiv X j).toLinearMap '' (X.M j : Set (X.V j))) = ⊤
  rw [← Submodule.map_span, (X.full j).span, Submodule.map_top, LinearEquiv.range]

theorem short (Λ₀ : ℝ) {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (sysOf X Λ₀).Short j Λ := by
  obtain ⟨v, hm, hi, hn⟩ := h
  have hs : ⊤ ≤ Submodule.span F (Set.range v) :=
    (hi.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, X.latRank_M])).ge
  refine ⟨_, (Module.Basis.mk hi hs).map (inclEquiv X j), fun i => ?_⟩
  have e : (Module.Basis.mk hi hs).map (inclEquiv X j) i = inclEquiv X j (v i) := by
    rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  refine e ▸ ⟨⟨v i, hm i, rfl⟩, fun σ => ?_⟩
  change (X.nm j).nrm σ ((inclEquiv X j).symm (inclEquiv X j (v i))) ≤ Λ
  rw [LinearEquiv.symm_apply_apply]
  exact hn i σ

end GlobalTheory.HSShort.SysHyp

namespace GlobalTheory.HSShort

open SysHyp

theorem GeoHyp.sysOf_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ),
    GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  intro F _ _ X Λ₀ h
  have := h.totallyComplex
  refine ⟨X.geom.alg.variety.one_le, X.le_T, ⟨?_, X.geom.alg.spans, X.herm, fun k σ => h.normsLe k σ, h.one_le_Lam⟩,
    shift_comm X.toGeo, fun j _ => isFull X Λ₀ j, ?_, ?_, X.one_le_beta, h.hermSysHyp_one_le_lambdaZero, X.one_le_LamD, X.one_le_LamT,
    short X Λ₀ h.short0, short X Λ₀ h.shortD, short X Λ₀ h.shortT⟩
  · obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.geom.alg.bpf.ge (Set.mem_univ (genericPoint X.Y)))
    exact j.pos
  · rintro j hj k _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := h.mulStable j hj (X.w.col k) (Submodule.subset_span ⟨k, rfl⟩) f hf
    refine ⟨inclEquiv X (j + 1) g, ⟨g, hg, rfl⟩, ?_⟩
    exact ((shift_single X.toGeo j _ f).trans (congrArg (Pi.single (M := fun l => X.Sec l) (j + 1)) e.symm)).symm
  · intro σ j hj u m c f g e
    refine h.mulBound.mulBoundAt σ j hj u m c (fun i => (inclEquiv X j).symm (f i))
      (fun t => (inclEquiv X (j + 1)).symm (g t)) fun k i => ?_
    have e₁ := (coe_eq_single X (j + 1) (g (k, i))).symm.trans ((e k i).trans
      ((congrArg (shift X.toGeo (Pi.single k 1)) (coe_eq_single X j (f i))).trans (shift_single X.toGeo j _ _)))
    exact Pi.single_injective (M := fun l => X.Sec l) (j + 1) e₁

end GlobalTheory.HSShort
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuelLatticeSystem_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  atlas_forward_decl GlobalTheory.HSShort.GeoHyp.sysOf_hyp
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShortNum

theorem claimS_to_hsClaimS : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ →
    h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  intro T D n Λ β Λ₀ ΛD ΛT δ h h' d deg hD hT hn hΛ hβ hδ hh hC
  obtain ⟨hz0, hz1, hineq⟩ := hC
  unfold Formalism.NormVectorIdentities.Items.HSClaimS Formalism.NormVectorIdentities.Items.hsZ Formalism.NormVectorIdentities.Items.hsR Formalism.NormVectorIdentities.Items.hsLogRho Formalism.NormVectorIdentities.Items.hsG
  set z : ℝ := 1 - ((T - 1).choose D : ℝ) * δ / d with hz
  refine ⟨hz0, hz1, ?_⟩
  set ρ : ℝ := Real.log Λ + 26 * Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) with hρ
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hβpos : 0 < β := by linarith
  have h1 : Real.log (Real.exp ρ * T) = ρ + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' hTpos.ne', Real.log_exp]
  have h2 : Real.log (2 * Real.exp ρ * Real.sqrt β) = Real.log 2 + ρ + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hβpos).ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt hβpos.le]
  have hX : (2 : ℝ) ≤ 2 + |h| + Real.log Λ := by have := abs_nonneg h; linarith
  have hprod : 2 * n ≤ n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ) := by
    have a1 : n ≤ n * (D : ℝ) := by nlinarith
    have a2 : n ≤ n * (D : ℝ) * 1 * δ := by nlinarith
    nlinarith
  have hlog2n : Real.log 2 + Real.log n ≤ Real.log (n * (D : ℝ) * 1 * δ * (2 + |h| + Real.log Λ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hprod
  have hl2 := Real.log_two_gt_d9
  have hcst : HSShort.cst n Λ = Real.log n + Real.log Λ + (Real.log n + 1) / 2 := by
    unfold HSShort.cst; rw [Real.log_mul (by linarith) (by linarith)]
  have hc : HSShort.cst n Λ ≤ ρ := by rw [hcst, hρ]; linarith
  have hc0 : 0 ≤ HSShort.cst n Λ := by rw [hcst]; positivity
  rw [h1, h2]
  clear h1 h2 hprod hlog2n hcst hX
  generalize HSShort.cst n Λ = c at *
  clear_value ρ z
  generalize (T : ℝ) = t at *
  generalize (D : ℝ) = e at *
  generalize Real.log t = lt at *
  generalize Real.log n = ln at *
  generalize Real.log β = lb at *
  have hA : t * h - 3 * (e + 1) * |h| - Real.log Λ₀ - 26 * e ^ 2 * (ρ + lt)
        - (t + e + 1) * lb - (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2)
      ≤ t * h' - e * (e + 1) * c - Real.log Λ₀ - t / 2 * lb := by
    have e1 : t * h - t * ((ln + 1) / 2) ≤ t * h' := by
      have := mul_le_mul_of_nonneg_left hh hTpos.le
      linarith
    have e2 : e * (e + 1) * c ≤ 26 * e ^ 2 * (ρ + lt) := by
      have : e * (e + 1) ≤ 2 * e ^ 2 := by nlinarith
      have hD2 : 0 ≤ e ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this hc0, mul_nonneg hD2 hlogT, mul_le_mul_of_nonneg_left hc hD2,
        mul_nonneg hD2 hc0]
    have e3 : t / 2 * lb ≤ (t + e + 1) * lb := mul_le_mul_of_nonneg_right (by linarith) hlogβ
    have e4 : t * ((ln + 1) / 2) ≤ (t + e ^ 2) * ((e + 1) * (ln + 1) / 2 + 1 + 2) := by
      have hg : (ln + 1) / 2 ≤ (e + 1) * (ln + 1) / 2 + 1 + 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e) (by linarith : (0 : ℝ) ≤ ln + 1)]
      have hT' : t ≤ t + e ^ 2 := by linarith [sq_nonneg e]
      calc t * ((ln + 1) / 2) ≤ t * ((e + 1) * (ln + 1) / 2 + 1 + 2) :=
            mul_le_mul_of_nonneg_left hg hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT' (by positivity)
    have e5 : 0 ≤ 3 * (e + 1) * |h| := by positivity
    linarith
  have hB : t * c + t / 2 * lb + Real.log ΛD + Real.log ΛT
      ≤ t * (Real.log 2 + ρ + lb / 2) + Real.log ΛD + Real.log ΛT := by
    have : t * c ≤ t * (Real.log 2 + ρ) := mul_le_mul_of_nonneg_left (by linarith) hTpos.le
    linarith
  have hz1' : 0 ≤ 1 - z := by linarith
  have m1 := mul_le_mul_of_nonneg_left hA hz1'
  have m2 := mul_le_mul_of_nonneg_left hB hz0
  linarith

end GlobalTheory.HSShortNum
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ → h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  atlas_forward_decl GlobalTheory.HSShortNum.claimS_to_hsClaimS
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShortTop

theorem geoBound_of_abstract : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  intro hQ hB hT hS F _ _ X Λ₀ hG h hh
  obtain ⟨dd, f, hdpos, hf, hfh⟩ := hh
  obtain ⟨hdel, Q, hQ0, hQs⟩ := hB F X.toTuple X.geom hG.bir dd f hf
  have hHyp := GlobalTheory.T.hilbertSamuelLatticeSystem_hyp F X Λ₀ hG
  have hFlat := GlobalTheory.T.hilbertSamuel_filtration_at_good_sections hQ F X Λ₀ hG dd f Q hQs
  have hirr : Irreducible f := GlobalTheory.ChowHt.irreducible_of_irreducible_map hf.irred
  obtain ⟨hpos, hcl⟩ := hS F (Tot X.toGeo) (sysOf X Λ₀) hHyp dd f Q (by omega) hf.homog hirr hQ0 hFlat
  have hfr : Module.finrank F ((sysOf X Λ₀).V (sysOf X Λ₀).T) = X.d := by
    rw [X.d_eq_finrank]; exact (inclEquiv X X.T).finrank_eq.symm
  have hdeg : deg ((sysOf X Λ₀).nm (sysOf X Λ₀).T) ((sysOf X Λ₀).M (sysOf X Λ₀).T) = X.degM X.T := by
    have := GlobalTheory.IsoDeg.deg_map_eq F (X.V X.T) (LinearMap.range (incl X X.T)) (X.nm X.T)
      (comap (X.nm X.T) (inclEquiv X X.T).symm.toLinearMap (inclEquiv X X.T).symm.injective) (inclEquiv X X.T)
      (fun σ m c g => by simp only [csq, HermTools.comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]) (X.M X.T) (X.full X.T).fg
    exact this
  have hTie := (hT F X.toHermSys X.abelian₂ hHyp.lat h ⟨dd, f, hdpos, hf, hfh⟩ dd 1 f 1 hf le_rfl one_ne_zero).2
  rw [hfr, hdeg] at hcl
  have hd' : ((X.del : ℤ) : ℝ) = (dd : ℝ) := by rw [← hdel]; push_cast; rfl
  rw [hd']
  refine GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality X.T X.D X.n X.abelian₂ X.beta Λ₀ X.LamD X.LamT dd h _ X.d (X.degM X.T)
    (by exact_mod_cast hHyp.one_le) hHyp.le_T (by exact_mod_cast X.one_le_n) hHyp.lat.one_le hHyp.one_le_beta
    (by exact_mod_cast hdpos) ?_ hcl
  have h2 : h - (Real.log X.n + 1) / 2 ≤ ht X.w X.A f / (((X.D : ℝ) + 1) * dd) := by
    simp at hTie; linarith
  exact h2

end GlobalTheory.HSShortTop
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  atlas_forward_decl GlobalTheory.HSShortTop.geoBound_of_abstract
end

section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightTieProof

theorem formHeight_eq_ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) :
    formHeight δ w A f = ht w A f + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  have hr : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold ht formHeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  field_simp
  ring

theorem ht_pow (hM : HtMul) {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (e : ℕ) :
    ht w A (f ^ e) = e * ht w A f := by
  induction e with
  | zero =>
    have := (hM F B N n w A Λ hL).2 1 one_ne_zero
    simpa using this
  | succ k ih =>
    have hk : IsMultiHomogeneous (k • a) (f ^ k) :=
      isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 ha).pow k)
    rw [pow_succ, (hM F B N n w A Λ hL).1 (k • a) a _ _ (pow_ne_zero k hf) hf hk ha, ih]
    push_cast; ring

theorem heightTie : HtMul → HeightTie := by
  intro hM F _ _ T Λ hL h hh d e f c hf he hc
  obtain ⟨d', f', -, hf', e'⟩ := hh
  obtain ⟨rfl, c', hc', rfl⟩ := hf.isChowFormInt.unique hf'.isChowFormInt
  have hf0 := hf.isChowFormInt.ne_zero
  have hd := hf.isChowFormInt.pos
  rw [HeightUnique.formHeight_C_mul hL.pos d hL.spans hL.det hf0 hf.homog hc', formHeight_eq_ht] at e'
  have hpow : IsMultiHomogeneous (e • fun _ => d) (f ^ e) :=
    isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 hf.homog).pow e)
  have key : ht T.w T.A (C c * f ^ e) = e * ht T.w T.A f := by
    unfold ht
    rw [HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det (pow_ne_zero e hf0) hpow hc]
    exact ht_pow hM hL hf0 hf.homog e
  have hD : (0 : ℝ) < (T.D : ℝ) + 1 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have eq1 : ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) =
      h - (harmonic (T.N - 1) : ℝ) / 2 := by
    rw [key, div_eq_iff (by push_cast; positivity)]
    push_cast
    push_cast at e'
    have : ht T.w T.A f = ((T.D : ℝ) + 1) * d * h - ((T.D : ℝ) + 1) * d * (harmonic (T.N - 1) : ℝ) / 2 := by
      linarith
    rw [this]; ring
  refine ⟨eq1, ?_⟩
  rw [eq1]

  have hNn : T.N ≤ T.n := by
    have h1 := finrank_range_le_card (R := F) (b := T.w.col)
    rw [Set.finrank, hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hH : (harmonic (T.N - 1) : ℝ) ≤ 1 + Real.log (T.N - 1 : ℕ) := harmonic_le_one_add_log _
  have hlog : Real.log (T.N - 1 : ℕ) ≤ Real.log T.n := by
    rcases Nat.eq_zero_or_pos (T.N - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : T.N - 1 ≤ T.n))
  linarith

end GlobalTheory.HeightTieProof
end
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem geoBound_of_quoted' : Quoted → GeoBound := fun hQ =>
  GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound hQ (GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ hQ) (GlobalTheory.HeightTieProof.heightTie GlobalTheory.HSShort.htMul) GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface

end GlobalTheory.HSShort
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticHilbertSamuelBound : Quoted → GeoBound := by
  atlas_forward_decl GlobalTheory.HSShort.geoBound_of_quoted'
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.HSShort

theorem hsClaimS_component_geo : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k Λ₀ hH
  have hp := CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hb : (h.data f₁ f₂ th k).Birational := hH.bir
  have hd := ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ (h.data f₁ f₂ th k).geom hb hp.2
  have hh := GlobalTheory.T.height_birationalImage_eq_tuple_height hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ hH.totallyComplex (h.data f₁ f₂ th k).geom hb hp.2
  have hc := GlobalTheory.T.arithmeticHilbertSamuelBound hQ c.F (h.data f₁ f₂ th k) Λ₀ hH _ hh
  have hm := GlobalTheory.T.degree_supLattice_component_eq E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k P.T le_rfl
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  obtain ⟨-, eT, -, en, eL, eb, eD, eT', -⟩ := h.data_numbers f₁ f₂ th k
  rw [← hd, h.d_eq f₁ f₂ th k, eT, en, eL, eb, eD, eT', hm, hD, Int.cast_natCast] at hc
  exact hc

end GlobalTheory.HSShort
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_component_short_basis_bound : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  atlas_forward_decl GlobalTheory.HSShort.hsClaimS_component_geo
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

theorem GlobalTheory.HSApp.shortFamily_of_spanning : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, ∀ (Λ : ℝ) (m : ℕ) (v : Fin m → Cusp Z U (P.wt j)), (∀ i, v i ∈ latOn U Z _) → Submodule.span c.F (Set.range v) = ⊤ → (∀ i σ, petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ (v i).1 ≤ Λ) → (h.data f₁ f₂ th k).ShortFamily j Λ := by
  intro E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k j hj Λ m v hv hs hn
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' c.F v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let b := Module.Basis.mk hli (by rw [hsp, hs])
  have hcard : Fintype.card κ = latRank c.F ((h.data f₁ f₂ th k).M j) := by
    rw [(h.data f₁ f₂ th k).latRank_M j, ← (h.equivV f₁ f₂ th k hj).finrank_eq, Module.finrank_eq_card_basis b]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => h.equivV f₁ f₂ th k hj (v (a (e i))), fun i => ?_, ?_, fun i σ => ?_⟩
  · exact (h.equivV_mem f₁ f₂ th k hj _).2 (hv _)
  · exact ((hli.comp e e.injective).map' _ (h.equivV f₁ f₂ th k hj).ker)
  · rw [h.nrm_equivV f₁ f₂ th k hj]
    exact hn _ σ
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HSShortRun

open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) : Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dif_neg hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt_of_wtBig {P : WtPar Dw} (h : WtBig P) : ∀ i, GapGe (FlagTan.dimFlag Dw + 1) (P.wt i) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro i τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg i) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

end Weights

variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}

theorem claim_at (hP : Hypotheses₂) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : Quoted)
    (hN : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hPr : GlobalTheory.Published.Principalisation)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hC : GlobalTheory.Published.ToroidalChartsForFan)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (hE : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) {P : WtPar (T.Q.Dw j)} (hW : WtBig P)
    (hA : ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) {PP κ : ℝ} (hPP : 0 ≤ PP) (hκ : 0 ≤ κ)
    (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂)
    (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) {Λ β : ℝ} (hΛ : 1 ≤ Λ) (hβ : 1 ≤ β)
    (hfr : ∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ)
    (hberg : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ β)
    (hBir : BirOn Y.U Z (wtOf _ P.u₁ 0) ∧ BirOn Y.U Z (wtOf _ P.u₂ 0))
    (h0 : ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)))
    (hsh : ∀ i ≤ P.T, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt i)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt i) 0) σ (v q).1 ≤ Real.exp (PP * κ)) :
    1 ≤ (f₁.n : ℝ) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 P.T (CompHt.dimFlag (T.Q.Dw j)) f₁.n 1 Λ β (Real.exp (PP * κ))
      (Real.exp (PP * κ)) (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) (Y.dg P.u₁ Z) (Y.ht P.u₁ Z)
      (Y.rkC (P.wt P.T) Z) (Y.degC (P.wt P.T) Z) := by
  obtain ⟨TF, R, ω, h⟩ := GlobalTheory.T.deep_model_weight_section hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z P hW hA
  have hPk : 0 ≤ PP * κ := mul_nonneg hPP hκ
  let k : Consts := ⟨Λ, β, Real.exp (PP * κ), Real.exp (PP * κ), 0, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk⟩
  let th : R.L.Sec := 0
  have r₁ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hBir.1
  have r₂ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₂ ⟨R.toModif⟩ hBir.2
  have hΛ₀ : 1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) := Real.one_le_exp (by positivity)
  have sh : ∀ i ≤ P.T, (h.data f₁ f₂ th k).ShortFamily i (Real.exp (PP * κ)) := fun i hi => by
    obtain ⟨m, v, l, s, n⟩ := hsh i hi
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k i hi _ m v l s n
  have s0 : (h.data f₁ f₂ th k).ShortFamily 0 (Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1))) := by
    obtain ⟨m, v, l, s, n⟩ := h0
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k 0 P.T.zero_le _ m v l s n
  have hDT : FlagTan.dimFlag (T.Q.Dw j) ≤ P.T := (Nat.le_succ _).trans h.le_T
  have hyp := GlobalTheory.T.geoHyp_of_ready_of_shortFamily hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z TF P R ω h f₁ f₂ th k _ hW r₁ r₂ hberg hΛ hfr hΛ₀ s0
    (sh _ hDT) (sh _ le_rfl)
  have hC := GlobalTheory.T.hilbertSamuel_component_short_basis_bound hQ _ _ _ _ _ _ _ TF.X Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k _ hyp
  have hrk : Y.rkC (P.wt P.T) Z = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    show ((Formalism.HN.rkK _ : ℕ) : ℝ) = _
    rw [Formalism.HN.rkK, (h.good _ le_rfl).2.2, finrank_top]
  rw [Real.log_exp] at hC
  refine ⟨by exact_mod_cast (h.geo f₁ f₂ th k).one_le_n, ?_⟩
  rw [hrk]
  exact hC

set_option maxHeartbeats 1000000 in

theorem hsClaim_short : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  intro hX h2 hG hQ hS hK hL hDG hSz hF
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply h2
  have H₄ := GlobalTheory.T.good_weight_antitone_gap h2
  have H₃ : Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg
      (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
    apply GlobalTheory.T.log_degree_le_weight_bound <;> assumption
  refine Closed.imp (Closed.and (Closed.and (Closed.and (GlobalTheory.T.exists_cusp_frame_weights h2 hDG hSz hF) (GlobalTheory.T.birational_on_weight_parameters hX hG hQ hS h2 hSz))
    (Closed.and H₃ wtBig_run)) (Closed.and (Closed.and (GlobalTheory.T.weight_parameter_strict_antitone hSz) (GlobalTheory.T.size_bounds_for_family hSz))
    (Closed.and (GlobalTheory.T.lattice_basis_petersson_first h2 hDG hSz hF) (GlobalTheory.T.lattice_basis_petersson_second h2 hDG hSz hF)))) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨_, -, a₃⟩, _, -, a₄⟩, ⟨⟨_, -, a₅⟩, _, -, a₆⟩, ⟨_, -, a₇⟩, _, -, a₈⟩
  obtain ⟨x0, a⟩ := (((a₁.and a₂).and (a₃.and a₄)).and ((a₅.and a₆).and (a₇.and a₈)))
  clear a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨⟨a₁, a₂⟩, a₃, a₄⟩, ⟨a₅, a₆⟩, a₇, a₈⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨⟨f₂⟩, f₁, Λ, β, hΛ, hβ, hn, hlβ, hlΛ, hfr, hberg⟩ := a₁ i hi Y hY Z
  have hW := a₄ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := a₅ i hi
  obtain ⟨hLaw, hIn, -, -, -, -, -, -, -, -, -, -, hPP, -⟩ := a₆ i hi Y hY
  obtain ⟨hPk, hsh⟩ := a₈ i hi Y hY
  have hg := gapGe_wt_of_wtBig hW
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hκ0 : 0 ≤ kap p i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, c₂⟩ := claim_at hP hG hQ h2.q15 h2.q16 hS hK.toroidalChartsForFan hL hY.1 hE Z hW
    (fun j _ => (H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1 _ (fun τ => antitone_of_gapGe (by positivity) (hg j) τ)
      (fun τ => le_trans (by omega) (hg j τ ((dat p i).p - 1) (by omega)))).1)
    hPP0 hκ0 f₂ f₁ hΛ hβ hfr hberg (a₂ i hi Y hY Z) (a₇ i hi Y hY Z) (hsh Z)
  refine ⟨f₁.n, Λ, β, _, _, _, c₁, hΛ, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk, hn, hlβ, a₃ i hi Y hY Z, hlΛ,
    (Real.log_exp _).le, (Real.log_exp _).le, ?_, c₂⟩
  have e₁ : 0 ≤ CompHt.dimFlag (dat p i) * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
    positivity
  have e₂ : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP := by positivity
  have e₃ : 0 ≤ 2 * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP) * CompHt.dimFlag (dat p i) := by
    positivity
  linarith

end GlobalTheory.HSShortRun
end
