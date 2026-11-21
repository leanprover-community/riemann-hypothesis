import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinati
import BuildAid.ForwardExisting

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

theorem IsKSR.baseChange (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  letI : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ epsRed S = epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1]
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarization_form_isotropic_filtration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExistsRing.polForm_exists | exact GlobalTheory.PolExistsRing.polForm_exists | (intros; apply GlobalTheory.PolExistsRing.polForm_exists <;> assumption)
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have := hA.comm
  have := a.hom
  exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
    (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v

end GlobalTheory.PolAdjointRing
end
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  atlas_forward_decl GlobalTheory.PolAdjointRing.polForm_adjoint
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing : GlobalTheory.Published.AbelianDeRham → ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring <;> assumption)
end

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback_ring {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR S ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR S) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  atlas_forward_decl GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grp_pullback_basis_lift_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasisRing.lifts_basis_mod_fil | exact GlobalTheory.LieBasisRing.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasisRing.lifts_basis_mod_fil <;> assumption)
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRing

theorem ksRow_exists_lieComb_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add, hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSRing
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  atlas_forward_decl GlobalTheory.KSRing.ksRow_exists_lieComb_ring
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
open GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.KSFam

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  rw [embK_coe, embK_coe]
  show starRingEnd ℂ (τ ((H.bar z : 𝓞 E) : E)) = τ (z : E)
  rw [H.9 z, NumberField.IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem ksFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  intro E _ _ _ H Dw l Xo c hP S _ _ y x' h1 h2
  suffices hM : ∃ M, GlobalTheory.FlagTan.IsKSR (psiSet H) y x' M by
    obtain ⟨M, hM⟩ := hM
    exact ⟨M, fun K _ _ ψ y' hy => GlobalTheory.FlagTan.isKSR_iff_isKS.mp (GlobalTheory.FlagTan.IsKSR.baseChange hP hy hM)⟩

  letI : GrpObj ((Over.pullback x').obj Xo.univ.t.G) := Functor.grpObjObj (F := Over.pullback x')
  letI : GrpObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    Functor.grpObjObj (F := Over.pullback (GlobalTheory.DeRham.epsRed S))
  have hA' := isGrpPullback_pullback Xo.univ.t.G x'
  have hi := isGrpPullback_pullback ((Over.pullback x').obj Xo.univ.t.G) (GlobalTheory.DeRham.epsRed S)
  have hA : IsGrpPullback ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G))
      Xo.univ.t.G y.x (pullback.fst _ _ ≫ pullback.fst _ _) := (hi.comp hA').congr h2 rfl
  haveI : IsCommMonObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hA
  have hab := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hsm := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA'
  have hab0 := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA
  have hsm' : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback x').obj Xo.univ.t.G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm
  have hsm0 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm'

  obtain ⟨ψ, hpol, hiso, hperf, hmax⟩ := GlobalTheory.T.exists_polarization_form_isotropic_filtration hP Xo hA

  obtain ⟨a', ha'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hA'
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a' hi
  have haπ : ∀ z, (a.act z).left ≫ (pullback.fst _ _ ≫ pullback.fst _ _) =
      (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (Xo.univ.t.act.act z).left := by
    intro z
    rw [← Category.assoc, ha z, Category.assoc, ha' z, Category.assoc]
  have hadj := GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point hP Xo hA a haπ hpol

  obtain ⟨ub, hub1, hubT, hubE, hubS⟩ := GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing y hA a haπ
  have hex : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ h, IsLieImage h (ub k.1 k.2) := fun k =>
    (hP.2.1 S _ _ hab0 hsm0).1.2 _ (hubT k.1 k.2)
  choose hb hhb using hex
  obtain ⟨hspan, hlin⟩ := GlobalTheory.T.grp_pullback_basis_lift_compatible hP y hA ub hub1 hb hhb
  have hreg := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing hP hi hab' hsm'
  have hcomp := fun z f w (e : IsKSValue hi f w) => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hi a a' ha z e
  have heig : ∀ (k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ))) (z : 𝓞 E),
      act (dp0 S) (𝟙 _) a z (hb k) - (algebraMap c.F S).comp (embK c k.1) z • hb k ∈
        Fil ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) := by
    intro k z
    haveI := a.hom z
    have e1 := (hhb k).push (a.act z)
    rw [hubE] at e1
    rw [act_apply]
    exact e1.sub_mem ((hhb k).smul _)
  have key : ∀ (τ : psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → S, ∃ w,
      IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hi ψ hb ⟨conjEmb τ.1, j⟩ w := fun τ j =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring hi a (fun z => H.bar z) ψ hiso hmax hperf hadj hreg hcomp
      (fun σ => (algebraMap c.F S).comp (embK c σ)) ub hb hspan hlin heig hubS τ.1 (conjEmb τ.1)
      (fun z => by simp only [RingHom.comp_apply, conj_embK']) j
  choose cf hcf using key
  exact ⟨fun k => cf k.1 k.2.1 k.2.2, _, inferInstance, _, inferInstance, _, _, _, hi, ψ, ub, hb, hA, hA', rfl, hpol,
    hub1, fun σ k => hhb ⟨σ, k⟩, fun τ j => hcf τ j⟩

end GlobalTheory.KSFam
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  atlas_forward_decl GlobalTheory.KSFam.ksFamily
end

section
namespace GlobalTheory.SecondComponentSum

theorem snd_eq_sum {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k])
    (hB : ∀ i : Fin D, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K)
    (hθ : ∀ a : k, TrivSqZeroExt.snd (θ (algebraMap k A a)) = (0 : K)) (s : A) :
    TrivSqZeroExt.snd (θ s) = ∑ b : Fin D, TrivSqZeroExt.snd (θ (f b)) *
      TrivSqZeroExt.fst (θ ((LinearMap.compDer (Module.Basis.coord B b)
        (KaehlerDifferential.D k A)) s)) := by
  classical

  let φ : A →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp θ
  let _ : Module A K := Module.compHom K φ
  let _ : Module k K := Module.compHom K (φ.comp (algebraMap k A))
  have : IsScalarTower k A K := ⟨fun c a x => by
    change φ (c • a) * x = φ (algebraMap k A c) * (φ a * x)
    rw [Algebra.smul_def, map_mul, mul_assoc]⟩
  have hsmul : ∀ (a : A) (x : K), a • x = TrivSqZeroExt.fst (θ a) * x := fun _ _ => rfl
  have hsndmul : ∀ a b : A, TrivSqZeroExt.snd (θ (a * b)) =
      TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
        TrivSqZeroExt.snd (θ a) * TrivSqZeroExt.fst (θ b) := by
    intro a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
  let ℓ : A →ₗ[k] K :=
    { toFun := fun a => TrivSqZeroExt.snd (θ a)
      map_add' := fun a b => by
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        change TrivSqZeroExt.snd (θ (c • a)) = φ (algebraMap k A c) * TrivSqZeroExt.snd (θ a)
        rw [Algebra.smul_def, hsndmul, hθ, zero_mul, add_zero]
        rfl }
  let d : Derivation k A K := Derivation.mk' ℓ fun a b => by
    change TrivSqZeroExt.snd (θ (a * b)) = TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
      TrivSqZeroExt.fst (θ b) * TrivSqZeroExt.snd (θ a)
    rw [hsndmul, mul_comm (TrivSqZeroExt.snd (θ a))]

  have key := congrArg d.liftKaehlerDifferential (B.sum_repr (KaehlerDifferential.D k A s))
  rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at key
  change d s = _
  rw [← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul, hB, Derivation.liftKaehlerDifferential_comp_D, hsmul, mul_comm]
  rfl

end GlobalTheory.SecondComponentSum
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_basis_kaehler_D {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension D k A] :
    ∃ (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]), ∀ i, B i = KaehlerDifferential.D k A (f i) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, fun i => by simp⟩

def derivHom {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (δ : Derivation k A A) :
    A →+* DualNumber A where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem snd_eq_sum_of_basis {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]) (hB : ∀ i, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K) (h : ∀ a, (θ (algebraMap k A a)).snd = 0) (s : A) :
    (θ s).snd = ∑ b, (θ (f b)).snd *
      (θ (((B.coord b).compDer (KaehlerDifferential.D k A)) s)).fst := by
  first
  | exact @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | (apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum ..)

theorem snd_eq_zero_of_isAlgebraic {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K]
    (φ : F →+* DualNumber K) (a : F) : (φ a).snd = 0 := by
  letI : Algebra ℚ (DualNumber K) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber K)
    (TrivSqZeroExt.fstHom K K K).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ φ.toRatAlgHom
    ((algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e := DFunLike.congr_fun this a
  change φ a = _ at e
  rw [e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_derivFrame (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X)
    (hp : p ∈ W) : ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  obtain ⟨V, hV, hx, hVW⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hp
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (dimFlag Dw)) M.str M.smooth
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(M.X, V)), p ∈ M.X.basicOpen (t : Γ(M.X, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(M.X, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).IsStandardSmoothOfRelativeDimension
      (dimFlag Dw) := by
    rw [← resG_comp_algX M.str (M.X.basicOpen_le (t : Γ(M.X, V)))]
    exact h₁
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (dimFlag Dw) c.F Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))) := h₂
  obtain ⟨f, B, hB⟩ := exists_basis_kaehler_D (D := dimFlag Dw) (k := c.F) (A := Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  refine ⟨_, IsAffineOpen.basicOpen hV _, fun b => derivHom ((B.coord b).compDer (KaehlerDifferential.D c.F _)),
    hxt, (M.X.basicOpen_le _).trans (hVW.trans le_rfl), fun b s => by simp [derivHom], fun K _ θ =>
    ⟨fun b => (θ (f b)).snd, fun s => ?_⟩⟩
  rw [snd_eq_sum_of_basis f B hB θ (fun a => snd_eq_zero_of_isAlgebraic (θ.comp (algebraMap c.F _)) a) s]
  simp [derivHom]

end GlobalTheory.CompHS
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_with_dual_number_derivations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  atlas_forward_decl GlobalTheory.CompHS.exists_derivFrame
end

section
namespace GlobalTheory

def dualNumberRingHomMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    DualNumber S →+* DualNumber S' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, mul_comm] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem dualNumber_deformation_extends_away :
    ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S']
      (d : S →+* DualNumber S), (∀ s, (d s).fst = s) →
      ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧
        ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  intro S S' _ _ _ g _ d hd
  let ψ : S →+* DualNumber S' := (dualNumberRingHomMap (algebraMap S S')).comp d
  have hψ : ∀ s, ψ s = TrivSqZeroExt.inl (algebraMap S S' (d s).fst)
      + TrivSqZeroExt.inr (algebraMap S S' (d s).snd) := fun s => rfl
  have hu : IsUnit (ψ g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ]
    simpa [hd] using IsLocalization.Away.algebraMap_isUnit (S := S') g
  refine ⟨IsLocalization.Away.lift g hu, ?_, ?_⟩
  · have h : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (IsLocalization.Away.lift g hu)
        = RingHom.id S' := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext s
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ, hd]
    intro s
    exact congrArg (fun F : S' →+* S' => F s) h
  · intro s
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ]
    rw [Algebra.smul_def, mul_one]

end GlobalTheory

alias _root_.GlobalTheory.T.exists_dualNumber_deformation_extend_away := _root_.GlobalTheory.dualNumber_deformation_extends_away
end

section
section
open AlgebraicGeometry

namespace GlobalTheory

theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
end

open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  atlas_forward_decl GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_ksComb_eq_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] (ψ : Γ(M.X, W₁) →+* K) (b : HIx Dw (psiSet H)), ∃ m : Fin (dimFlag Dw) → K, ∑ a, m a • (ψ ∘ Mx a) = Pi.single b 1 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx K _ ψ b
  letI : Algebra c.F K := (ψ.comp (algebraMap c.F Γ(M.X, W₁))).toAlgebra
  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := { ψ with commutes' := fun _ => rfl }
  obtain ⟨Qp, hQp⟩ := GlobalTheory.FlagMod.exists_frMap ψA Q₀
  have hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    rw [Category.assoc]; exact le_preimage_comp _ hk₁
  have hch : X.F.ChartFr k _ hk Qp := hQ₀.frMap hQp (Category.assoc _ _ _).symm hk
  have e : (spMap ψ ≫ tau hW₁) ≫ toFlag M = X.ptY Qp := GlobalTheory.FlagMod.FlagCover.eq_ptY hch.lies
  have ho : ⊤ ≤ (spMap ψ ≫ tau hW₁) ⁻¹ᵁ M.off := le_preimage_comp _ (tau_le hW₁ hoff)
  obtain ⟨v, hv⟩ := (hKS K Qp).exists_isTanFrame
  obtain ⟨zv, hzv, hzO⟩ := GlobalTheory.CompHS.exists_tanLift M (hv.isDef (.inl b)) e ho
  have hzW : ⊤ ≤ zv ⁻¹ᵁ W₁ := hzO W₁ (le_preimage_comp _ (tau_le hW₁ le_rfl))
  have hθ : spMap (ev zv W₁ hzW) ≫ tau hW₁ = zv := spMap_ev zv hW₁ hzW
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ zv = spMap ψ ≫ tau hW₁ := by
    have hU : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
      have := ho (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    refine (M.existsUnique_lift _ hU).unique ?_ rfl
    rw [← cancel_mono (inc₀ X Z)]
    have h1 : zv ≫ M.σ ≫ inc₀ X Z = X.ptY (v (.inl b)) := hzv
    have h2 : ((spMap ψ ≫ tau hW₁) ≫ M.σ) ≫ inc₀ X Z = X.ptY Qp := by
      rw [← e, Category.assoc]
    rw [h2, Category.assoc, Category.assoc, h1]
    exact X.ptY_frMap (hv.isDef (.inl b))
  have hfst : ∀ s, (ev zv W₁ hzW s).fst = ψ s := by
    have h1 := ev_spMap (GlobalTheory.FlagTan.red c K).toRingHom zv W₁ hzW
      (by rw [hred]; exact le_preimage_comp _ (tau_le hW₁ le_rfl))
    have h2 := ev_spMap_tau hW₁ ψ (le_preimage_comp _ (tau_le hW₁ le_rfl))
    rw [ev_congr hred _ _ (le_preimage_comp _ (tau_le hW₁ le_rfl)), h2] at h1
    intro s
    have := congrArg (fun f : Γ(M.X, W₁) →+* K => f s) h1
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  obtain ⟨m, hm⟩ := hspan K (ev zv W₁ hzW)
  have hsnd : ∀ s, (ev zv W₁ hzW s).snd = ∑ a, m a * ψ (d a s).snd := fun s => by
    rw [hm s]
    exact Finset.sum_congr rfl fun a _ => by rw [← hfst]; rfl
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K ψ hk Qp hch
    (ev zv W₁ hzW) m hfst hsnd
  have hpt : X.ptY w = X.ptY (v (.inl b)) := by
    rw [← hwpt, ← Category.assoc, hθ, hzv]
  have hx : w.x = (v (.inl b)).x := by
    have h1 := (X.lies_ptY w).1
    have h2 := (X.lies_ptY (v (.inl b))).1
    rw [hpt] at h1
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd w) (frX_snd _) (h1.symm.trans h2)]
  obtain ⟨M', -, hu⟩ := (hKS K Qp).existsUnique hwD.isTanX
  refine ⟨m, (hu _ hwKS).trans (hu _ ?_).symm⟩
  rw [hx]
  exact (hv.1 b).2

theorem GlobalTheory.HorFrame.exists_basicOpen_det_ks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx p hp
  obtain ⟨K, hK, ψ, hbo, hden⟩ := GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen hW₁ p hp
  choose m hm using fun b => GlobalTheory.HorFrame.exists_ksComb_eq_single M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx K ψ b
  obtain ⟨a, t, ht, hat⟩ := hden (HIx Dw (psiSet H) × Fin (dimFlag Dw)) (fun bc => m bc.1 bc.2)
  refine ⟨Matrix.of fun b c => a (b, c), hbo _ ?_⟩
  have hmap : ((Matrix.of fun b c => a (b, c)) * Matrix.of (fun a h => Mx a h)).map ψ =
      Matrix.scalar (HIx Dw (psiSet H)) (ψ t) := by
    ext b h
    have e := congrFun (hm b) h
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul] at e
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    simp only [← hat]
    calc ∑ x, m b x * ψ t * ψ (Mx x h) = ψ t * ∑ x, m b x * ψ (Mx x h) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e, Pi.single_apply]
          by_cases hh : h = b
          · subst hh; simp
          · simp [hh, Ne.symm hh]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
  exact pow_ne_zero _ ht
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  atlas_forward_decl GlobalTheory.HorFrame.exists_basicOpen_det_ks
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.HorFrame

def combDer {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) : R →+* DualNumber R where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (∑ i, A i * (δ i s).snd)
  map_one' := by
    have h : ∀ i, (δ i 1).snd = 0 := fun i => by rw [map_one]; rfl
    ext <;> simp [h]
  map_mul' x y := by
    have h : ∀ i, (δ i (x * y)).snd = x * (δ i y).snd + (δ i x).snd * y := fun i => by
      rw [map_mul, TrivSqZeroExt.snd_mul, hδ, hδ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, h, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    have h : ∀ i, (δ i 0).snd = 0 := fun i => by rw [map_zero]; rfl
    ext <;> simp [h]
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]

theorem combDer_fst {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) : (combDer δ hδ A s).fst = s := by
  simp [combDer]

theorem combDer_snd {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) :
    (combDer δ hδ A s).snd = ∑ i, A i * (δ i s).snd := by
  simp [combDer]

theorem fst_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by simp [dualMap]

theorem snd_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by simp [dualMap]

end GlobalTheory.HorFrame

open GlobalTheory.HorFrame in

theorem GlobalTheory.HorFrame.exists_horizontal_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS k W hW p hp
  haveI := c.fin
  obtain ⟨W₁, hW₁, d, hpW₁, hW₁W, hd, hspan⟩ := GlobalTheory.T.exists_affine_cover_with_dual_number_derivations M W p hp
  have hoff : W₁ ≤ M.off := fun x hx => (hW (hW₁W hx)).1
  have hτ : ⊤ ≤ tau hW₁ ⁻¹ᵁ W₁ := tau_le hW₁ le_rfl
  have hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ => (hW (hW₁W (hτ (Set.mem_univ s)))).2
  have hF₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
    have := hoff (hτ (Set.mem_univ s))
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg₁, hch⟩ := GlobalTheory.CompHS.exists_chartFr (tau hW₁ ≫ toFlag M) hF₁
  obtain ⟨Q₀, hQ₀⟩ := hch k hk₁
  have hdalg : ∀ b, (d b).comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber Γ(M.X, W₁)) :=
    fun b => RingHom.ext fun a => TrivSqZeroExt.ext
      (by rw [RingHom.comp_apply, hd]; rfl) (by
      rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F ((d b).comp (algebraMap c.F _)) a]; rfl)
  have hx1 : ∀ b, (spMap (d b) ≫ Q₀.x) ≫ Xo.s = sOf c (DualNumber Γ(M.X, W₁)) := fun b => by
    rw [Category.assoc, Q₀.x_over]
    unfold sOf
    rw [spMap_comp', ← RingHom.comp_assoc, hdalg]
  have hx2 : ∀ b, spMap (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom ≫ spMap (d b) ≫ Q₀.x
      = Q₀.x := fun b => by
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom.comp (d b) = RingHom.id _ :=
      RingHom.ext fun s => hd b s
    rw [this]
    exact (congrArg (· ≫ Q₀.x) (Spec.map_id _)).trans (Category.id_comp _)
  choose Mx hMx using fun b => GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation hP Q₀ (spMap (d b) ≫ Q₀.x) (hx1 b) (hx2 b)
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx p hpW₁
  set MxM : Matrix (Fin (dimFlag Dw)) (HIx Dw (psiSet H)) Γ(M.X, W₁) := Matrix.of (fun a h => Mx a h) with hMxM
  set g : Γ(M.X, W₁) := (B * MxM).det with hg
  have hW' : IsAffineOpen (M.X.basicOpen g) := hW₁.basicOpen g
  have hW'W₁ : M.X.basicOpen g ≤ W₁ := M.X.basicOpen_le g
  haveI := hW₁.isLocalization_basicOpen g
  set ρ := algebraMap Γ(M.X, W₁) Γ(M.X, M.X.basicOpen g) with hρ
  choose d' hd'1 hd'2 using fun b => GlobalTheory.T.exists_dualNumber_deformation_extend_away (S' := Γ(M.X, M.X.basicOpen g)) g (d b) (hd b)
  have hunit : IsUnit ((B * MxM).map ρ).det := by
    have : ((B * MxM).map ρ).det = ρ (B * MxM).det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit g
  set A := ((B * MxM).map ρ)⁻¹ * B.map ρ with hA
  have hAM : A * MxM.map ρ = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hunit]
  have hτ' : spMap ρ ≫ tau hW₁ = tau hW' := by
    have e1 := spMap_ev (tau hW') hW₁ (tau_le hW' hW'W₁)
    have e2 : ev (tau hW') W₁ (tau_le hW' hW'W₁) = ρ := RingHom.ext fun a => ev_tau hW' hW'W₁ _ a
    rw [← e2]
    exact e1
  refine ⟨M.X.basicOpen g, hW', fun b => combDer d' hd'1 (fun a => A b a), hB, hW'W₁.trans hW₁W,
    fun b s => combDer_fst _ _ _ _, ?_⟩
  intro K _ _ ψ hk Q hQ b
  have ez : (spMap ψ ≫ tau hW') ≫ toFlag M = (spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M := by
    rw [← hτ', ← spMap_comp' ρ ψ]
    simp only [Category.assoc]
  have hk' : ⊤ ≤ ((spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := ez ▸ hk
  have hQ' : X.F.ChartFr k _ hk' Q :=
    hQ.frMap (frMap_refl Q) ((spMap_algId _).trans ez) hk'
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K (ψ.comp ρ) hk' Q hQ'
    ((dualMap ψ).comp ((combDer d' hd'1 (fun a => A b a)).comp ρ)) (fun a => ψ (A b a))
    (fun s => by rw [RingHom.comp_apply, fst_dualMap, RingHom.comp_apply, combDer_fst]; rfl)
    (fun s => by
      rw [RingHom.comp_apply, snd_dualMap, RingHom.comp_apply, combDer_snd, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hd'2]
      rfl)
  refine ⟨w, hwD, ?_, ?_⟩
  · have key : ∀ h, ∑ a, ψ (A b a) * ψ (ρ (Mx a h)) = (Pi.single b (1 : K) : HIx Dw (psiSet H) → K) h := fun h => by
      have e := congrArg (fun N => ψ (N b h)) hAM
      simp only [Matrix.mul_apply, Matrix.map_apply, hMxM, Matrix.of_apply, map_sum, map_mul] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
      by_cases hh : h = b
      · subst hh; simp
      · simp [hh, Ne.symm hh]
    convert hwKS using 1
    funext h
    rw [Finset.sum_apply, ← key h]
    rfl
  · rw [← hwpt, ← hτ']
    simp only [← Category.assoc, spMap_comp']
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  atlas_forward_decl GlobalTheory.HorFrame.exists_horizontal_lift
end
