import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ (GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)), GlobalTheory.LogKSDiv.genPt TF Z ≫ s₀ TF.Y Z = spMap φ₀ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ τ i, f₀.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧ ∀ (a : 𝓞 E) (k : Fin n), IsCombAtG TF.Y.t (LogKS.chart U) v ((Matrix.diagonal fun j => constFn TF.Y.s U.1 (embK c (e.symm j).1 a)) k) (v k ≫ (TF.Y.t.act.act a).left) := by
  first | exact @GlobalTheory.LogKSDiv.spread_genFrame | exact GlobalTheory.LogKSDiv.spread_genFrame | (intros; apply GlobalTheory.LogKSDiv.spread_genFrame <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFracChart

theorem isFractionRing_and_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens)
    (hUV : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (hρ : spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι) :
    (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧
      ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  set V := barComp TF.Y Z
  set W : (X₀ TF.Y Z).Opens := V.ι ⁻¹ᵁ U.1 with hWdef
  have hU : IsAffineOpen U.1 := U.2
  have hWU : V.ι ''ᵁ W = U.1 := by
    rw [hWdef, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUV
  have hW : IsAffineOpen W := by
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, hWU]; exact hU
  have hch : LogKS.chart U = hU.fromSpec := rfl
  have hcomp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g) x = g (f x) := fun _ _ _ => rfl
  have hη : genericPoint (X₀ TF.Y Z) ∈ W := by
    obtain ⟨p⟩ : Nonempty (Sp (X₀ TF.Y Z).functionField) := inferInstance
    have h1 : (spMap ρ ≫ LogKS.chart U) p ∈ U.1 := by
      rw [hcomp, hch]; show _ ∈ (U.1 : Set TF.Y.X); rw [← hU.range_fromSpec]; exact Set.mem_range_self _
    rw [hρ, hcomp] at h1
    exact GlobalTheory.Cartier.gen_mem (x := GlobalTheory.LogKSDiv.genPt TF Z p) h1
  set σ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField :=
    ((X₀ TF.Y Z).presheaf.germ W _ hη).hom.comp (V.ι.appLE U.1 W le_rfl).hom with hσ
  have key : spMap ρ ≫ hU.fromSpec = spMap σ ≫ hU.fromSpec := by
    rw [← hch, hρ, GlobalTheory.LogKSDiv.genPt, ← hW.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec V.ι hU hW le_rfl, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hρe : ρ = σ := by
    have := Spec.map_injective ((cancel_mono hU.fromSpec).1 key)
    exact congrArg CommRingCat.Hom.hom this
  subst hρe
  haveI : Nonempty W := ⟨⟨_, hη⟩⟩
  have hle : U.1 ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hUV
  haveI : IsIso (V.ι.app U.1) := Scheme.Hom.isIso_app V.ι U.1 hle
  have hFr : IsFractionRing Γ(X₀ TF.Y Z, W) (X₀ TF.Y Z).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ W hW
  refine ⟨?_, ?_⟩
  · letI := σ.toAlgebra
    exact IsFractionRing.of_ringEquiv_left (asIso (V.ι.app U.1)).commRingCatIsoToRingEquiv (fun x => by
      show σ x = _
      simp only [σ, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
      rfl)
  · intro a
    rw [← GlobalTheory.Cartier.fnOf_comp_algX (s₀ TF.Y Z) W hη]
    simp only [σ, RingHom.comp_apply]
    congr 1
    show ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ TF.Y.s.appLE ⊤ U.1 (fun _ _ => trivial) ≫
      V.ι.appLE U.1 W le_rfl).hom a = _
    have e := Scheme.Hom.appLE_comp_appLE V.ι TF.Y.s ⊤ U.1 W (fun _ _ => trivial) le_rfl
    erw [e]
    rfl

end GlobalTheory.GenFracChart
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧ ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  atlas_forward_decl GlobalTheory.GenFracChart.isFractionRing_and_const
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.GenKSProof

theorem embK_conj_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c ((starRingEnd ℂ).comp τ) (H.bar x) = embK c τ x := by
  apply Subtype.ext
  show ((starRingEnd ℂ).comp τ) ((H.bar x : 𝓞 E) : E) = τ (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem embK_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c ((starRingEnd ℂ).comp τ) x := by
  apply Subtype.ext
  show τ ((H.bar x : 𝓞 E) : E) = ((starRingEnd ℂ).comp τ) (x : E)
  rw [RingHom.comp_apply, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem card_pairIx {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) : Fintype.card (GlobalTheory.LogKSDiv.PairIx H Dw) = Dw.dim := by
  have h := FlagTan.isHalf_psiSet H
  have hc : Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
    rw [← h.card, FlagTan.psiSet, Fintype.card_subtype]
  have hm : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      Dw.mult τ.1 * Dw.mult ((starRingEnd ℂ).comp τ.1) = Dw.p * Dw.q := fun τ => by
    rcases FlagTan.mult_conj (Dw := Dw) τ.1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b]
    · rw [a, show (starRingEnd ℂ).comp τ.1 = conjEmb τ.1 from rfl, b, mul_comm]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, hm, Finset.sum_const, Finset.card_univ, hc,
    smul_eq_mul, Datum.dim, mul_assoc]

theorem symPair_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (R : Type) [CommRing R] (κ : c.F → R) (n : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : GlobalTheory.LogKSDiv.PairIx H Dw) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P ∈
      LogKS.balanced H.bar (fun a => Matrix.diagonal fun j => κ (embK c (e.symm j).1 a)) := by
  refine (LogKS.mem_balanced_diagonal H.bar (fun j a => κ (embK c (e.symm j).1 a)) _).2 ⟨?_, fun a i k => ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext and_comm
  · simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
    by_cases h1 : i = e ⟨P.1.1, P.2.1⟩ ∧ k = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Equiv.symm_apply_apply, embK_conj_bar', sub_self, zero_mul]
    by_cases h2 : i = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ k = e ⟨P.1.1, P.2.1⟩
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Equiv.symm_apply_apply, embK_bar', sub_self, zero_mul]
    · rw [if_neg h1, if_neg h2, add_zero, mul_zero]

theorem exists_ext (k R K : Type) [CommRing k] [CommRing R] [Field K] (ρ : R →+* K) (α : k →+* K) (κ : k → R)
    (hfr : letI := ρ.toAlgebra; IsFractionRing R K) (hκ : ∀ a, ρ (κ a) = α a) (d : Derivation ℤ R R)
    (hd : ∀ a, d (κ a) = 0) :
    ∃ D : (letI := α.toAlgebra; Derivation k K K), ∀ r, D (ρ r) = ρ (d r) := by
  letI := ρ.toAlgebra
  obtain ⟨δ, hδ, hδρ⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (A := R) (B := K) (nonZeroDivisors R) (fun r => ρ (d r))
    (fun x y => by rw [map_add, map_add]) (fun x y => by
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]; rfl)
  have hα : ∀ a, δ (α a) = 0 := fun a => by
    rw [← hκ a]
    exact (hδρ (κ a)).trans (by rw [hd, map_zero])
  letI := α.toAlgebra
  have hs : ∀ (a : k) (x : K), δ (a • x) = a • δ x := fun a x => by
    show δ (α a * x) = α a * δ x
    rw [hδ.mul, hα, mul_zero, add_zero]
  let D0 : K →ₗ[k] K := { toFun := δ, map_add' := hδ.add, map_smul' := hs }
  exact ⟨{ toLinearMap := D0, map_one_eq_zero' := hδ.der_one, leibniz' := (fun x y => hδ.mul x y) },
    fun r => hδρ r⟩

theorem exists_genKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z f₀.v D := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ φ₀ f₀ hφ₀
  obtain ⟨U, hU, ρ, n, e, v, hch, htan, huq, hf, heig⟩ := GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen E H Dw l Xo c TF Z φ₀ f₀ hφ₀
  obtain ⟨hfr, hconst⟩ := GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart E H Dw l Xo c TF Z U hU ρ hch
  obtain ⟨e', he'⟩ := TF.logKS U n v _ htan huq heig
  let ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw := (Fintype.equivFinOfCardEq (card_pairIx H Dw)).symm
  let Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U :=
    fun j => e'.symm ⟨GlobalTheory.LogKSDiv.symPair e (ε j), symPair_mem_balanced H Dw l c _ _ n e (ε j)⟩
  have hD := fun j => exists_ext c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField ρ (GlobalTheory.Cartier.constFn (s₀ TF.Y Z))
    (constFn TF.Y.s U.1) hfr hconst (Dl j).1 (Dl j).2.1
  choose D hD using hD
  refine ⟨D, U, hU, ρ, n, e, v, ε, Dl, hch, htan, huq, fun τ i => hf τ i, fun j => ?_, hD⟩
  refine (he' (Dl j) _).2 ?_
  simp only [Dl, LinearEquiv.apply_symm_apply]

end GlobalTheory.LogKSDiv.GenKSProof
end
end
