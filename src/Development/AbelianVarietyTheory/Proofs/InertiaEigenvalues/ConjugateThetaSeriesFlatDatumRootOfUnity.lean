import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberField
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDGalRul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostHalfRootAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuplesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolume
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphism
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClass

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open scoped ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictDom

theorem frame_mem_dom : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  intro D H Dw l Xo c σ V U dict io g e F ik φ th x₀ hσ hA hU hW hD hth hx₀ h
  obtain ⟨γ, -, -, -, hmat⟩ := hD.2 h
  have hX := hW (dict h).1
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ (U.X (dict h).1).p0 (U.X (dict h).1).Ψ
    (U.X (dict h).1).Gm (U.X (dict h).1).Gm_herm).2.1 _ fun τ => ?_).1
  rw [← hx₀ (dict h).1 τ.1 τ.2, hmat τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary V (hth (dict h).1 τ) (γ * h)
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose =
      -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end GlobalTheory.DictDom
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDictionary_frame_mem_open_frames : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  atlas_forward_decl GlobalTheory.DictDom.frame_mem_dom
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.PermUnif

variable {g g' : ℕ}

def permCLE (π : Fin g ≃ Fin g') : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (π : Fin g ≃ Fin g') (z : Fin g' → ℂ) (j : Fin g) : permCLE π z j = z (π j) := rfl

@[simp] theorem permCLE_symm_apply (π : Fin g ≃ Fin g') (z : Fin g → ℂ) (j : Fin g') :
    (permCLE π).symm z j = z (π.symm j) := by
  have : permCLE π (fun j' => z (π.symm j')) = z := funext fun j => by simp
  rw [(permCLE π).symm_apply_eq.2 this.symm]

def permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) : L →+ (Fin g' → ℂ) where
  toFun a j := P a (π.symm j)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem permP_apply {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L)
    (j : Fin g') : permP π P a j = P a (π.symm j) := rfl

theorem permCLE_permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L) :
    permCLE π (permP π P a) = P a := funext fun j => by simp

theorem hermForm_perm (π : Fin g ≃ Fin g') (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g' → ℂ) :
    hermForm (Hm.submatrix π.symm π.symm) z w = hermForm Hm (permCLE π z) (permCLE π w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, permCLE_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isPeriod_permP {D : Datum H} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (π : Fin g ≃ Fin g')
    (hπ : ∀ j, ty' (π j) = ty j) {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : IsPeriod D ty' (permP π P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hEF⟩ := hP
  refine ⟨fun a x j => ?_, fun x y hxy => hinj (funext fun j => ?_), ?_, ?_,
    ⟨Hm.submatrix π.symm π.symm, hH.submatrix _, fun z hz => ?_, fun x y => ?_⟩⟩
  · rw [permP_apply, permP_apply, hlin, ← hπ, Equiv.apply_symm_apply]
  · have := congrFun hxy (π j)
    simpa using this
  · haveI := hdisc
    refine DiscreteTopology.of_continuous_injective (f := fun v : (permP π P).range =>
      (⟨permCLE π v.1, ?_⟩ : P.range)) ?_ ?_
    · obtain ⟨x, hx⟩ := v.2
      exact ⟨x, by rw [← hx, permCLE_permP]⟩
    · exact Continuous.subtype_mk ((permCLE π).continuous.comp continuous_subtype_val) _
    · intro v w hvw
      exact Subtype.ext ((permCLE π).injective (congrArg Subtype.val hvw))
  · have hr : Set.range (permP π P) = ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range P := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨P x, ⟨x, rfl⟩, ?_⟩
        funext j
        simp
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, funext fun j => by simp⟩
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).surjective
  · rw [hermForm_perm]
    refine hpos _ fun h0 => hz (funext fun j => ?_)
    have := congrFun h0 (π.symm j)
    simpa using this
  · rw [hermForm_perm, permCLE_permP, permCLE_permP, hEF]

theorem isHolTo_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) {y : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (hy : IsHolTo Set.univ y) : IsHolTo Set.univ (fun z => y (L z)) := by
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hs : {b ∈ (Set.univ : Set (Fin g' → ℂ)) | ⊤ ≤ y (L b) ⁻¹ᵁ U} = L ⁻¹' {b ∈ Set.univ | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp
  rw [hs]
  exact ⟨ho.preimage L.continuous, hd.comp L.differentiableOn (fun b hb => hb)⟩

theorem isDerivAt0_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) (y : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem isometry_of_point_eq_perm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  intro E _ _ _ H Dw l Xo σ' g g' ty ty' F F' hpq hσ hty hty' π hπ k k' P P' hP hP' h
  have hL : ∀ a, permCLE π (permP π P a) = P a := permCLE_permP π P
  have hd := F.ex_diff k P hP
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all
    GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g' ty' hpq hσ hty' (F.Di k) (F'.Di k') (F.t k) (F'.t k') (permP π P) P'
    (F.u k P) (F'.u k' P') (fun z => F.ex k P (permCLE π z)) (F'.ex k' P')
  obtain ⟨gam, -, hEF, hM, -, -⟩ := (key (by
    refine ⟨F.over_σ k P hP, isPeriod_permP π hπ hP, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro z w
      rw [map_add]
      exact F.ex_add k P hP _ _
    · exact (F.ex_onto k P hP).comp (permCLE π).surjective
    · exact isHolTo_comp_cle (permCLE π) (y := fun z => (F.ex k P z).left) (GlobalTheory.ClassUniq.isHolTo_ex F k P hP)
    · intro w
      obtain ⟨v, hv, hu⟩ := hd.1 (permCLE π w)
      exact ⟨v, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v.left).2 hv,
        fun v' hv' => hu v' ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v'.left).1 hv')⟩
    · intro v hv
      have h0 : (permCLE π) 0 = 0 := map_zero _
      have hv0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (F.ex k P 0).left := by
        rw [← h0]; exact hv
      obtain ⟨w, hw, hu⟩ := hd.2 v hv0
      refine ⟨(permCLE π).symm w, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) _ v.left).2 (by
        rwa [(permCLE π).apply_symm_apply]), fun w' hw' => ?_⟩
      rw [← hu _ ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w' v.left).1 hw'),
        (permCLE π).symm_apply_apply]
    · intro z
      refine (F.ex_ker k P hP (permCLE π z)).trans ⟨?_, ?_⟩
      · rintro ⟨x, hx⟩
        refine ⟨x, funext fun j => ?_⟩
        have := congrFun hx (π.symm j)
        simpa using this
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hL x).symm⟩
    · intro a z
      have e : permCLE π (fun j => ty' j (a : E) * z j) = fun j => ty j (a : E) * permCLE π z j :=
        funext fun j => by simp [hπ]
      rw [e]
      exact F.ex_lin k P hP a (permCLE π z)
    · intro n a a₂ c hn hc
      rw [map_smul, map_smul, hL, hL]
      exact F.ex_weil k P hP n a a₂ c hn hc
    · intro a ha
      rw [map_smul, hL]
      exact F.ex_eta k P hP a ha
    · intro a
      rw [map_smul, hL]
      exact F.ex_etaA k P hP a) (by
    exact ⟨F'.over_σ k' P' hP', hP', ⟨F'.ex_add k' P' hP', F'.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F' k' P' hP',
      (F'.ex_diff k' P' hP').1, (F'.ex_diff k' P' hP').2⟩, F'.ex_ker k' P' hP', F'.ex_lin k' P' hP',
      F'.ex_weil k' P' hP', F'.ex_eta k' P' hP', F'.ex_etaA k' P' hP'⟩)).1 h
  exact ⟨gam, hEF, hM⟩

end GlobalTheory.PermUnif
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_points_eq_marked_isometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  atlas_forward_decl GlobalTheory.PermUnif.isometry_of_point_eq_perm
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
namespace GlobalTheory.MarkIso

open GlobalTheory.Member

set_option maxHeartbeats 2000000 in

theorem xi_det_eq_of_marked_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  intro D H Dw l V io hio A A' t t' X X' φ φ' g g' hW hW' hE hE' hL hL' hm hm' gam hgE hgm xi hxi1 hxi2
  have hGm : X'.Gm = X.Gm := hW'.1.trans hW.1.symm
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  let φL : A.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  let φL' : A'.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := X'.Λ.subtype ∘ₗ φ'.toLinearMap
  have hr : Set.range φL = X.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ a).2, fun hv => ⟨φ.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hr' : Set.range φL' = X'.Λ := by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (φ' a).2, fun hv => ⟨φ'.symm ⟨v, hv⟩,
      congrArg Subtype.val (φ'.apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hcc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    simp only [cc, map_neg] at this ⊢
    rw [this]
  obtain ⟨δ', hδ1, hδ2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry _ H A A' V.rank (-X.ξ0) X.Gm φL φL' gam hcc
    ⟨Subtype.val_injective.comp φ.injective, by rw [hr]; exact X.Λ_span, X.Gm_herm, X.Gm_det,
      fun x y => hE x y⟩
    ⟨Subtype.val_injective.comp φ'.injective, by rw [hr']; exact X'.Λ_span, hGm ▸ X'.Gm_herm, hGm ▸ X'.Gm_det,
      fun x y => by rw [hE' x y, hGm, hξ]; rfl⟩ hgE
  have hG0 : X.Gm = -(HSpace.gram V)ᵀ := by
    rw [hW.1]
    simp
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ⟩ := r3 δ' (by rw [← hG0]; exact hδ1)
  have hLg : Set.range φL = latG V g := hr.trans (hL.trans (Set.image_id _))
  have hLg' : Set.range φL' = latG V g' := hr'.trans (hL'.trans (Set.image_id _))
  obtain ⟨u, h1, h2, h3⟩ := GlobalTheory.ConjMark.exists_of_matched V g g' δ δ' 1 l.M (by have := l.three_le; omega) l.Mb _
    l.prod hδ (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hLg, ← hLg']
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, hδ2 a⟩
      · rintro ⟨a, ha⟩
        refine ⟨gam.symm a, ?_⟩
        have e := hδ2 (gam.symm a)
        rw [LinearEquiv.apply_symm_apply, ha] at e
        have e' := congrArg (fun t => ((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ t) e
        simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using e'.symm)
    (fun v hv => by rw [Matrix.one_mulVec]; exact hv)
    (fun b hb x hx => by
      rw [← hio] at hx
      obtain ⟨x, rfl⟩ := hx
      have hv : b • x ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
        Submodule.smul_mem_smul hb trivial
      rw [← map_smul]
      refine ⟨φL (t (b • x)), φL' (t' (b • x)), hm _ hv, hm' _ hv, ?_⟩
      obtain ⟨z, hz⟩ := hgm _ hv
      refine ⟨-φL' z, ?_, ?_⟩
      · rw [← SetLike.mem_coe, ← hLg']
        exact ⟨-z, map_neg _ _⟩
      · rw [Matrix.one_mulVec, ← hδ2, hz, map_add, map_nsmul, smul_neg]
        abel)
  have hδQ : δ ∈ GQ V := (r1 δ).2 ⟨δ', hδ⟩
  have h3' : (finHom V u).1.det * 1 - 1 ∈
      GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
    simpa [Algebra.TensorProduct.one_def] using h3
  have hq := GlobalTheory.DetTranslate.quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
    (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
    _ _ 1 (GlobalTheory.DetTranslate.det_int_of_gLat V h1) (GlobalTheory.DetTranslate.det_int_of_gLat V (GlobalTheory.DetTranslate.gLat_one V))
    (finHom_herm_det D V u).2.1 (finHom_herm_det D V 1).2.1 h3' (by simp)
  have hK := hxi1 u h1 (by
    obtain ⟨w, hw, e⟩ := hq
    refine ⟨w, hw, ?_⟩
    simpa using e)
  have h4 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) h2
  simp only [map_mul] at h4
  rw [hK, hxi2 δ hδQ, mul_one, one_mul] at h4
  exact h4

end GlobalTheory.MarkIso
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hio : LinearMap.range io = latG V 1)
    (A A' : Datum H) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La)
    (X X' : Data D.host.E V.rank) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (g g' : GA D V)
    (hW : ModelW V rfl X) (hW' : ModelW V rfl X')
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin V.rank → D.host.E) (φ b)))
    (hE' : ∀ a b, ((A'.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hL : (X.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g : Set _))
    (hL' : (X'.Λ : Set (Fin V.rank → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG V g' : Set _))
    (hm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V ((φ (t a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hm' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V ((φ' (t' a) : Fin V.rank → D.host.E) ∘ Fin.cast rfl) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (gam : A.La ≃ₗ[𝓞 D.host.E] A'.La) (hgE : ∀ a b, A'.EF (gam a) (gam b) = A.EF a b)
    (hgm : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ x, gam (t a) = t' a + l.M • x)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1), xi (Matrix.GeneralLinearGroup.det (finHom V g')) = xi (Matrix.GeneralLinearGroup.det (finHom V g)) := by
  atlas_forward_decl GlobalTheory.MarkIso.xi_det_eq_of_marked_isometry
end

section
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MarkVal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in

theorem val_at_mark {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) V r) (hC : C.OK) (hι : C.ι = ι)
    (hx : C.x₀ = x₀) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) (hf : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (d.l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0)
    (y : FrPt d.Xo₂ d.c₂ (CAt (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)))) (k : Fin C.F.n) (P : (C.F.Di k).La →+ (Fin C.g → ℂ))
    (hP : IsPeriod (C.F.Di k) (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (C.e j).1) P)
    (hy : y.x = C.F.u k P) (h γ : GA D V) (hM : C.Mark h k γ) :
    toC (evR d.Xo₂ d.c₂ d.cδ y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  classical
  subst hr hι hx
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) := hC.good
  have hor : ∀ j, IsOrthogonalFrame (U₂.X j) C.x₀ := by
    intro j τ hτ
    have h1 := hC.orth k
    have hG : (U₂.X j).Gm = (C.M.X k).Gm := by rw [(hW j).1, (hC.modelW k).1]
    have hp : (U₂.X j).p0 = (C.M.X k).p0 := ((hU.2.1 j).1).trans (hC.base.type k).1.symm
    have hΨ : τ ∈ (C.M.X k).Ψ := ((hC.base.type k).2 τ).2 (((hU.2.1 j).2 τ).1 hτ)
    rw [hG, hp]
    exact h1 τ hΨ

  have hdom := GlobalTheory.T.latticeDictionary_frame_mem_open_frames V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hU hW hD hth hor
  obtain ⟨h', hh'⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hC.pos hU hW hD hC.iota
    hth hor hdom y
  obtain ⟨P', -, hP', hy', -⟩ := hD.1.2 (dict₂ h').1 ⟨_, hdom h'⟩
  have hpt : C.F.u k P = F.u (ik (dict₂ h').1) P' := hy.symm.trans (hh'.trans hy')
  have hg : (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = H.rt0 := hC.good
  obtain ⟨gam, hgE, hgm⟩ := GlobalTheory.T.familyUniformisation_points_eq_marked_isometry C.F F hC.pos hg
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw C.g C.e)
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw g₀ e₀) (C.e.trans e₀.symm)
    (fun j => by simp) k (ik (dict₂ h').1) P P' hP hP' hpt
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
  have hxe := GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry d.l₂ V C.ι hC.iota.emb.2 (C.F.Di k) (F.Di (ik (dict₂ h').1)) (C.F.t k) (F.t (ik (dict₂ h').1))
    (C.M.X k) (U₂.X (dict₂ h').1) (C.M.φ k) (φ (dict₂ h').1) (γ * h) (γ' * h') (hC.modelW k) (hW _)
    (hC.base.ef k) (hD.1.1 _) hM.2.1 hΛ' hM.2.2 hm' gam hgE hgm xi hxi1 hxi2
  have hv := hval h' γ' ⟨hγ', hΛ', hm'⟩
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh', ← hxe, ← hv]
  show _ = (if h'' : (dict₂ h').2 ∈ (U₂.X (dict₂ h').1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h''⟩)) else 0)
  rw [dif_pos (hdom h')]

end GlobalTheory.MarkVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.MarkVal

set_option maxHeartbeats 4000000 in

theorem val_on_marked_space : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hfw i Tp tup M hM a C hOK hι hx f xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk
  exact val_at_mark (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i)
    (T.x₀ ((i : ℕ) + 1) M.s0) C hOK hι hx xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk

end GlobalTheory.MarkVal
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  atlas_forward_decl GlobalTheory.MarkVal.val_on_marked_space
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverXiDet

theorem natM_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
  rw [← l.prod] at h
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h

theorem natM_mem_of_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l l₂ : Level H)
    (I P : Ideal (𝓞 E)) (h : l₂.Mb = l.Mb * I) (hI : I ≤ P) : ((l₂.M : ℕ) : 𝓞 E) ∈ P := by
  have h1 := natM_mem_Mb l₂
  rw [h] at h1
  exact hI (Ideal.mul_le_right (I := l.Mb) (J := I) h1)

end GlobalTheory.CoverXiDet

namespace GlobalTheory.CoverXiDet

set_option maxHeartbeats 4000000 in

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hM t u _ hw
  have hL := hC.lev
  have hN : ∀ PP ∈ R.Q (tup t), (((M.dδ t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    natM_mem_of_half _ _ _ _ ((hM.cov t).1).2.2.2.1 ((hM.tuple t).half.2.1 PP hPP)
  obtain ⟨xi', hxi1, hxi2, -, -⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi (tup t))
    (hL.xi_fin (tup t)).choose (hL.xi_fin (tup t)).choose_spec.1 (hL.xi_fin (tup t)).choose_spec.2 (hL.xi_triv (tup t))
    (hL.xi_tame (tup t))
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Wc D i) u
  have e1 := (hM.tuple t).xi u x hx
  have e2 := hxi1 u x hx
  have e3 : xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    refine hxi2 _ (M.dδ t).l₂.odd (GlobalTheory.TupleCover.unrAt_of_not_mem R hL (tup t) _ hN) u ?_
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, (GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers D).symm ▸ hw1, hw2⟩
  apply Units.ext
  rw [e1, ← e2, e3]

end GlobalTheory.CoverXiDet
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverCharacter_trivial_on_level_determinants : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  atlas_forward_decl GlobalTheory.CoverXiDet.main
end

section
section
noncomputable section

namespace GlobalTheory.CoverConj

section General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.GalTw
  GlobalTheory.GalTw.CharSec
open scoped TensorProduct Matrix

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_conj_pt_fix (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ) (hτ : ∀ a, τ (σ a) = σ a) (y : FrPt Xo c (CAt σ)) :
    ∃ y₀ : FrPt Xo c (CAt σ), ∀ f ∈ sec Xo c 0 0, toC (evR Xo c f y) = τ (toC (evR Xo c f y₀)) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let φ : CAt σ →ₐ[c.F] CAt σ :=
    { toRingHom := (τ.symm : ℂ →+* ℂ)
      commutes' := fun a => by
        show τ.symm (σ a) = σ a
        conv_lhs => rw [← hτ a]
        exact τ.symm_apply_apply _ }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS D.host.E H Dw l Xo c _ _ φ y
  have hx : y.x = spMap (τ : ℂ →+* ℂ) ≫ z.x := by
    have h1 : z.x = spMap (τ.symm : ℂ →+* ℂ) ≫ y.x := hz.1
    have h2 : spMap (τ : ℂ →+* ℂ) ≫ spMap (τ.symm : ℂ →+* ℂ) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      simp
    rw [h1]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) h2).trans (Category.id_comp _))).symm
  exact ⟨z, fun f hf => conj_value σ σ τ (RingHom.ext fun a => (hτ a).symm) hf z y hx⟩

set_option maxHeartbeats 2000000 in

theorem galRul_eq_cmul_complex (V : HSp D) (r : ℕ) (σ : c.F →+* ℂ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) {ta : c.F ≃+* c.F} (hta : Fixes c ta) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a, τ (σ a) = σ (ta a)) (hcur : FixesCurve H τ 1) (xi xi' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (hx1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1)
    (hx2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1)
    (hconj : ∀ h : GA D V, τ (xi (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ) =
      (xi' (Matrix.GeneralLinearGroup.det (finHom V h)) : ℂˣ))
    (a₀ a₀' : ℂ) (ha' : a₀' ≠ 0) {f f' : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (hf' : f' ∈ sec Xo c 0 0)
    (hv : ∀ (y : FrPt Xo c (CAt σ)) k P, IsPeriod (C.F.Di k) (fun j => relab c σ (C.e j).1) P → y.x = C.F.u k P →
      ∀ h γ, C.Mark h k γ → toC (evR Xo c f y) = a₀ * (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ))
    (hv' : ∀ (y : FrPt Xo c (CAt σ)) k P, IsPeriod (C.F.Di k) (fun j => relab c σ (C.e j).1) P → y.x = C.F.u k P →
      ∀ h γ, C.Mark h k γ → toC (evR Xo c f' y) = a₀' * (xi' (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ)) :
    ∃ (u : GA D V) (ka : c.F), σ ka = τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹ ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
        evR Xo c (galRul hta f) y = algebraMap c.F k ka * evR Xo c f' y := by
  haveI : Countable c.F := (Module.finBasis ℚ c.F).equivFun.toEquiv.countable_iff.2 inferInstance
  have hg : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hC.good
  have hrt : τ H.rt0 = H.rt0 := by
    conv_lhs => rw [← hg, hτ, hta.base, hg]
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_perm_periodSpaces_complexAut D.host.E H Dw l Xo _ _ _ C.F hC.pos hC.good
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hC.good).2.2.2 Dw C.g C.e) hC.lA τ hrt
  obtain ⟨κ, ⟨u, hu⟩, hκ⟩ := GlobalTheory.T.autConj_translates_detCharacter_markings D H Dw l Xo c σ V r C hC hsig τ hrt hcur π hπ xi hx1 hx2
  have hcu := hconj u
  rw [← hu] at hcu
  have hgal : galRul hta f ∈ sec Xo c 0 0 := ((GlobalTheory.T.conjugateSection_values_semilinear D.host.E H Dw l Xo c ta hta).1 0 0 f hf).1
  have hne : ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hpt : ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c (galRul hta f) y) =
      (τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹) * toC (evR Xo c f' y) ∧
      toC (evR Xo c f' y) ≠ 0 := by
    intro y
    obtain ⟨y₀, hy, hval⟩ := exists_conj_point σ hta τ hτ y
    obtain ⟨i, P, hP, hiP⟩ := C.F.onto y₀.x y₀.x_over
    obtain ⟨P', hP', hiP'⟩ := hπ i P hP
    obtain ⟨h, -, hm⟩ := GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC i
    obtain ⟨h', -, hm'⟩ := GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC (π i)
    have e1 := hv y₀ i P hP hiP.symm h 1 hm
    have e2 := hv' y (π i) P' hP' (hy.trans (hiP ▸ hiP')) h' 1 hm'
    have e3 := hκ h 1 i h' 1 hm hm'
    have e4 := hval f hf
    refine ⟨?_, ?_⟩
    · rw [e4, e1, e2, ← hconj (1 * h'), e3, Units.val_mul, map_mul τ, map_mul τ, hcu]
      field_simp
    · rw [e2]
      exact mul_ne_zero ha' (Units.ne_zero _)
  obtain ⟨y1⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
    Xo c hC.pos σ
  have hmem : (τ a₀ / a₀' * ((xi' (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ) : ℂ)⁻¹) ∈ Set.range σ := by
    letI : Algebra c.F ℂ := σ.toAlgebra
    refine GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := c.F) _ fun s => ?_
    have hs : ∀ a, s.toRingEquiv (σ a) = σ a := fun a => s.commutes a
    obtain ⟨y₀, hy₀⟩ := exists_conj_pt_fix σ s.toRingEquiv hs y1
    have h1 := (hpt y1).1
    have hn := (hpt y1).2
    rw [hy₀ _ hgal, hy₀ _ hf', (hpt y₀).1, map_mul] at h1
    rw [hy₀ _ hf'] at hn
    exact mul_right_cancel₀ hn h1
  obtain ⟨ka, hka⟩ := hmem
  refine ⟨u, ka, hka, ?_⟩
  have hsplit : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (t : c.F),
      evR Xo c (galRul hta f + (-t) • f') y = evR Xo c (galRul hta f) y - algebraMap c.F S t * evR Xo c f' y := by
    intro S _ _ y t
    unfold evR
    rw [evalAt_add, evalAt_smul, map_neg, neg_mul, sub_eq_add_neg]
  have hz : galRul hta f + (-ka) • f' = 0 := by
    refine sec_eq_zero_of_complex σ (add_mem hgal (Submodule.smul_mem _ _ hf')) fun y => ?_
    rw [hsplit, sub_eq_zero]
    show toC (evR Xo c (galRul hta f) y) = σ ka * toC (evR Xo c f' y)
    rw [hka]
    exact (hpt y).1
  intro k _ _ _ y
  have e := hsplit k y ka
  rw [hz] at e
  have e0 : evR Xo c (0 : Rul Xo c) y = 0 := evalAt_zero _ _ y
  exact sub_eq_zero.1 (e.symm.trans e0)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

section Transport

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
  {c : Coeff l}

theorem cxiAt_of_eq (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {d d' : DeltaDat Xo c n} (e : d' = d)
    {U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r}
    {U₂' : Unf d'.Xo₂ d'.c₂ (σ0.comp (d'.eF.symm : d'.c₂.F →+* c.F)) r} (hU : HEq U₂' U₂)
    {dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r} {dict₂' : GA D V → Σ k, Frame (U₂'.X k).Ψ r} (hd : HEq dict₂' dict₂)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (h : GlobalTheory.OneMapAll.CXiAt V hr σ0 d' U₂' dict₂' ι x₀ xi c0) : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0 := by
  subst e
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hd
  exact h

theorem cδ_mem_of_eq {d d' : DeltaDat Xo c n} (e : d' = d) (h : d'.cδ ∈ sec d'.Xo₂ d'.c₂ 0 0) :
    d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 := e ▸ h

end Transport

set_option maxHeartbeats 4000000 in

theorem conj_cover_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup M hM τ ta hta hFix hcO hxiF
  obtain ⟨c0, ⟨m, hm0, hm⟩, hc⟩ := (GlobalTheory.OneMapAll.cXiVal_iff _ _ _ _ _ _ _ _ _).1 hM.cxi
  have hc0 : c0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne'] at hm
    exact zero_ne_one hm
  refine ⟨τ c0 / c0, ⟨m, hm0, by rw [div_pow, ← map_pow, hm, map_one, div_one]⟩, ?_⟩
  intro a b cx hab hU hd hct
  have hfix' : Fixes M.c' ta := by
    refine ⟨fun τ' x => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · rw [hta]
      exact hFix.host τ' x
    · rw [hta]
      exact hFix.core ⟨_, T.Q.c.le x.2⟩
  obtain ⟨hlev, hA, -⟩ := hM.cov a
  have h₂ := fixes_covAut (M.dδ a) hA hfix'
  refine ⟨h₂, ?_⟩
  obtain ⟨hT'⟩ := hT
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  obtain ⟨-, hpq, -, hq2⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT'.laws.pins ((i : ℕ) + 1) hj
  have hsig : (T.Q.Dw ((i : ℕ) + 1)).p = 0 ∨ (T.Q.Dw ((i : ℕ) + 1)).q = 0 ∨
      3 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    by_cases h0 : (T.Q.Dw ((i : ℕ) + 1)).q = 0
    · exact Or.inr (Or.inl h0)
    · right; right; omega
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hιok := GlobalTheory.TupleCover.iotaOK_and_frame T hT'.laws ((i : ℕ) + 1) hj M.s0
    (by have e : M.s0 = T.σ₀ := sOv_eq _ _ _; rw [e]; exact T.good_σ₀) (Wc D i) M.hV (rank_Wc i)
  let σ₂ : (M.dδ a).c₂.F →+* ℂ := (inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)
  obtain ⟨C, hC, hCι, hCx⟩ := (GlobalTheory.Member.exists_ctx D _ _ _ (M.dδ a).Xo₂ (M.dδ a).c₂ σ₂ (Wc D i) D.R.r (rank_Wc i) _
    hιok.1 hpos hA rfl).2.2 _ hιok.2
  have hτ₂ : ∀ x, τ (σ₂ x) = σ₂ (covAut (M.dδ a) ta x) := fun x => by
    show τ (((M.dδ a).eF.symm x : M.c'.F) : ℂ) =
      (((M.dδ a).eF.symm ((M.dδ a).eF (ta ((M.dδ a).eF.symm x))) : M.c'.F) : ℂ)
    rw [AlgEquiv.symm_apply_apply, hta]
  have hconj : ∀ h : GA D (Wc D i), τ ((M.xi a (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) : ℂˣ) : ℂ) =
      ((M.xi b (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) : ℂˣ) : ℂ) := fun h => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 h
    rw [(hM.tuple a).xi h x hx, (hM.tuple b).xi h x hx, hct.2 x]
  have hrat : ∀ t : Tp, ∀ γ ∈ GQ (Wc D i), M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1 := by
    intro t γ hγ
    obtain ⟨-, -, hr3, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
    obtain ⟨x, hx⟩ := hr3 γ hγ
    apply Units.ext
    rw [(hM.tuple t).xi γ _ hx, (hR.lev.xi (tup t)).1.2 x]
    simp
  have hl₂ : (M.dδ b).l₂ = (M.dδ a).l₂ := by rw [hab]
  have hxa := GlobalTheory.T.coverCharacter_trivial_on_level_determinants D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a
  have hxb : ∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F
      (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) :
        (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) →
      M.xi b (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    intro u hu hw
    rw [← hl₂] at hw
    exact GlobalTheory.T.coverCharacter_trivial_on_level_determinants D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM b u hu hw
  have hfa : (M.dδ a).cδ ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hfb : cx ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 :=
    cδ_mem_of_eq (d := { M.dδ a with cδ := cx }) hab (hM.cov b).1.2.2.2.2.2.2.2.1
  have hva := GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a C hC hCι hCx (M.dδ a).cδ (M.xi a) c0
    hfa hxa (hrat a) (hc a)
  have hvb := GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace D G Pl0 T0 A T R F κ v₀ hR ⟨hT'⟩ i Tp tup M hM a C hC hCι hCx cx (M.xi b) c0
    hfb hxb (hrat b) (cxiAt_of_eq _ _ _ (d := { M.dδ a with cδ := cx }) hab hU hd _ _ _ _ (hc b))
  obtain ⟨u, ka₂, hka, heq⟩ := galRul_eq_cmul_complex (Wc D i) D.R.r σ₂ C hC hsig h₂ τ hτ₂ hFix.curve (M.xi a) (M.xi b)
    hxa (hrat a) hconj c0 c0 hc0 hfa hfb hva hvb
  obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 u
  refine ⟨(M.dδ a).eF.symm ka₂, x⁻¹, ?_, fun k _ _ _ y => ?_⟩
  · show σ₂ ka₂ = _
    rw [hka, (hM.tuple b).xi u x hx, map_inv, Circle.coe_inv]
  · rw [AlgEquiv.apply_symm_apply]
    exact heq k y

end GlobalTheory.CoverConj
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  atlas_forward_decl GlobalTheory.CoverConj.conj_cover_const
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GalEqCls

theorem isThClsD_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
    {d d' : Formalism.L2.Pj.DeltaDat Xo c n} (hd : d' = d)
    {Cl Cl' : Type} [Fintype Cl] [Fintype Cl'] (e : Cl ≃ Cl')
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (w' : Cl' → (Fin n → LevQ Dw d'.l₂) → c.F)
    (hw : ∀ k, HEq (w k) (w' (e k)))
    (La : Cl → GenLat E n) (La' : Cl' → GenLat E n) (hLa : ∀ k, La' (e k) = La k)
    (Nc : Cl → ℕ) (Nc' : Cl' → ℕ) (hNc : ∀ k, Nc' (e k) = Nc k)
    (gam : Cl → ℕ) (gam' : Cl' → ℕ) (hgam : ∀ k, gam' (e k) = gam k)
    (vol : c.F) (ep : Cl → c.F) (ep' : Cl' → c.F) (hep : ∀ k, ep' (e k) = ep k)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (x : Cl → Vs) (x' : Cl' → Vs) (hx : ∀ k, x' (e k) = x k) (f : Rul Xo c)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) : IsThClsD Xo c d' w' La' Nc' gam' vol ep' io x' f := by
  subst hd
  intro k _ _ A A₂ hk y y₂ hy
  obtain ⟨vc, hvc, he⟩ := @h k _ _ A A₂ hk y y₂ hy
  refine ⟨fun cl => vc (e.symm cl), fun cl => ?_, ?_⟩
  · obtain ⟨k', rfl⟩ := e.surjective cl
    dsimp only
    rw [e.symm_apply_apply, ← eq_of_heq (hw k'), hLa, hNc, hx]
    exact hvc k'
  · rw [he]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    dsimp only
    rw [e.symm_apply_apply, hgam, hep]

theorem galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hf : Fixes M.c' ta := ⟨fun φ x => Subtype.ext (by rw [hta]; exact hfix.host φ x),
    fun a => Subtype.ext (by rw [hta]; exact hfix.core ⟨a, T.Q.c.le a.2⟩)⟩
  obtain ⟨k0, hk0, hcxi⟩ := GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hk0ne : k0 ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn, hkn⟩ := hk0
    rw [zero_pow hn.ne'] at hkn
    exact zero_ne_one hkn
  refine ⟨hf, k0⁻¹, ?_, ?_⟩
  · obtain ⟨n, hn, hkn⟩ := hk0
    exact ⟨n, hn, by rw [inv_pow, hkn, inv_one]⟩
  intro a b e hsame hconj
  obtain ⟨⟨cx, hcx⟩, hU, hdict, -, -, hcl⟩ := id hsame
  obtain ⟨h₂, ka, s1, hka, hev⟩ := hcxi a b cx hcx hU hdict hconj
  obtain ⟨u, s2, w', hu, hw'eq, hw⟩ :=
    GlobalTheory.T.conj_fourierCoefficients_conjugate_tuples D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  obtain ⟨hvol, hep⟩ := GlobalTheory.T.galoisConj_classScalars_and_volume D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  have hkane : ka ≠ 0 := fun h0 => by
    have h1 : ((ka : ℂ)) = 0 := by rw [h0]; rfl
    rw [hka] at h1
    exact mul_ne_zero hk0ne (Circle.coe_ne_zero _) h1
  have hune : u ≠ 0 := fun h0 => by
    have h1 : ((u : ℂ)) = 0 := by rw [h0]; rfl
    rw [hu] at h1
    exact Circle.coe_ne_zero _ h1
  refine ⟨(ka * u)⁻¹, (s1 * s2)⁻¹, ?_, ?_⟩
  · have e1 : (((ka * u)⁻¹ : M.c'.F) : ℂ) = ((ka : ℂ) * (u : ℂ))⁻¹ := by push_cast; rfl
    rw [e1, hka, hu, map_inv, map_mul, Circle.coe_inv, Circle.coe_mul]
    ring
  intro xs xs' hxs f hfs hsum
  obtain ⟨-, cga, hio⟩ := hP.io
  have hio' := fun v => GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio.2.2.1 ▸ LinearMap.mem_range_self M.io v)
  obtain ⟨hLev, -, hN⟩ := hP.cov a
  have hδ := hLev.2.2.2.2.2.2.2.1
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf (Vc D i).rank (M.dδ a) h₂ hN hδ cx
    ka u hkane hune hev (M.Cl' a) (M.w a) w' (M.La a) (M.Nc a) (M.gam a) (M.vol a) (M.ep a) (VsV D i M.c'.F) M.io
    (wtA (κ i)) hio' hw xs (fun k => xs' (e k))
    (fun k => GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix (xs k) (xs' (e k)) (hxs k))
    (Vc D i).rank f hfs hsum
  refine ⟨key.1, ?_⟩
  have key2 := key.2
  rw [hvol] at key2
  exact isThClsD_transfer hcx e w' (M.w b) hw'eq (M.La a) (M.La b) (fun k => (hcl k).2.1) (M.Nc a) (M.Nc b)
    (fun k => (hcl k).2.2.1) (M.gam a) (M.gam b) (fun k => (hcl k).2.2.2) (M.vol b) (fun k => ta (M.ep a k)) (M.ep b)
    (fun k => (hep k).symm) M.io (fun k => xs' (e k)) xs' (fun _ => rfl) _ key2

end GlobalTheory.GalEqCls
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  atlas_forward_decl GlobalTheory.GalEqCls.galRul_isSum
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCombine

variable {X B : Type} (φ : B → X → ℂ) (τ : ℂ ≃+* ℂ)

def Exp (Φ : X → ℂ) {n : ℕ} (a : Fin n → ℂ) (F : Fin n → B) : Prop :=
  ∀ g, Φ g = ∑ k, a k * φ (F k) g

def CF (ζ : ℂ) (Φ Φ' : X → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F → Exp φ Φ' (fun k => ζ * τ (a k)) F

variable {φ τ}

theorem conj_wd {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {Φ : X → ℂ} {n m : ℕ} {a : Fin n → ℂ} {F : Fin n → B}
    {b : Fin m → ℂ} {G : Fin m → B} (ha : Exp φ Φ a F) (hb : Exp φ Φ b G) (g : X) :
    ∑ k, τ (a k) * φ (F k) g = ∑ k, τ (b k) * φ (G k) g := by
  obtain ⟨p, c, H, hc⟩ := h0.1
  have hall : Exp φ Ψ (Fin.append c (Fin.append a (-b))) (Fin.append H (Fin.append F G)) := by
    intro x
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hc x, ← ha x, ← hb x]
    ring
  have e1 := h0.2 _ _ _ hc g
  have e2 := h0.2 _ _ _ hall g
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at e2
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, one_mul, neg_mul,
    Finset.sum_neg_distrib] at e1 e2
  rw [e1] at e2
  linear_combination -e2

theorem conj_comb {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {m : ℕ} (β : Fin m → ℂ) (Φs Φs' : Fin m → X → ℂ)
    (h : ∀ k, CF φ τ 1 (Φs k) (Φs' k)) (c : ℂ) :
    CF φ τ c (fun g => ∑ k, β k * Φs k g) (fun g => c * ∑ k, τ (β k) * Φs' k g) := by
  choose n b G hG using fun k => (h k).1
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat : Exp φ (fun g => ∑ k, β k * Φs k g) (fun q => β (e q).1 * b (e q).1 (e q).2)
      (fun q => G (e q).1 (e q).2) := by
    intro g
    rw [Fintype.sum_equiv e (fun q => β (e q).1 * b (e q).1 (e q).2 * φ (G (e q).1 (e q).2) g)
      (fun p => β p.1 * b p.1 p.2 * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨⟨_, _, _, hflat⟩, fun N a F ha g => ?_⟩
  have hw := conj_wd h0 ha hflat g
  rw [Fintype.sum_equiv e (fun q => τ (β (e q).1 * b (e q).1 (e q).2) * φ (G (e q).1 (e q).2) g)
      (fun p => τ (β p.1 * b p.1 p.2) * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma] at hw
  have hc : ∀ k, Φs' k g = ∑ j, τ (b k j) * φ (G k j) g := fun k => by
    rw [(h k).2 _ _ _ (hG k) g]
    simp only [one_mul]
  show c * ∑ k, τ (β k) * Φs' k g = ∑ k, c * τ (a k) * φ (F k) g
  simp only [hc, map_mul] at hw ⊢
  have e3 : ∑ k, c * τ (a k) * φ (F k) g = c * ∑ k, τ (a k) * φ (F k) g := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [e3, hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConjCombine

namespace GlobalTheory.ConjClassSum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem conjFun_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ GlobalTheory.ConjCombine.CF (fun (F : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) g =>
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) (F : T.toCore.R ((i : ℕ) + 1)) g)
      τ ζ Φ Φ' := Iff.rfl

theorem conjFun_congr {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands
  rw [GlobalTheory.OneMapAll.phi_eq O O' (T.cE ((i : ℕ) + 1))]

def psi {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
    rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2

theorem psi_smul {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (u : M.c'.F) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) :
    psi M κ z (u • f) g = (u : ℂ) * psi M κ z f g := by
  unfold psi
  rw [map_smul, map_smulₛₗ]
  show _ * ((u : ℂ) * _) = _
  ring

set_option maxHeartbeats 8000000 in

theorem conj_lifts : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hC hT0 hFW hio hQ i hOP hPT c hc τ hτ
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  obtain ⟨M, hMP, hlev, hext, hnorm, hcurve, hxiF, hcov⟩ :=
    GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hC hT0 ⟨fw⟩ hQ i hOP

  let τQ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => map_ratCast τ q)
  let ta : M.c'.F ≃+* M.c'.F := (τQ.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => τQ.restrictNormal_commutes M.c'.F a

  have hEq0 : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  have hlev2 : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hEqM : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt at hEq0 ⊢
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), hlev2]
    exact hEq0
  have hcM : ExtC R i (inC M.c') M.c0' c := (hext c).1 hc

  obtain ⟨ζ, z, hζ, -, hser⟩ := GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hCI D G Pl0 T0 A T R F κ v₀ O ph hsz hC hT0 ⟨fw⟩ hio hQ i hOP hPT T0 id M hMP
    hlev hext
  obtain ⟨hf, k0, hk0, hgal⟩ := GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple hCI D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hcurve hxiF
  obtain ⟨a0, ha0, hza⟩ := hζ
  obtain ⟨b0, hb0, hkb⟩ := hk0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha0.ne'] at hza
    exact zero_ne_one hza
  have hτζ : τ ζ ≠ 0 := (map_ne_zero τ).2 hζ0
  refine ⟨ζ * k0 / τ ζ, ⟨a0 * b0, Nat.mul_pos ha0 hb0, ?_⟩, fun t t' hct => ?_⟩
  · rw [div_pow, mul_pow, ← map_pow, pow_mul ζ a0 b0, hza, one_pow, pow_mul' k0 a0 b0, hkb, one_pow, map_one, div_one,
      one_mul]
  obtain ⟨e, hsame⟩ := hcov t t' hct.1
  obtain ⟨u, s, hu, hgal'⟩ := hgal t t' e hsame hct
  refine ⟨s, fun y y' hcf => ?_⟩
  obtain ⟨n, α, ys, ys', hy, hy', hval⟩ :=
    GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ c hcM hxiF t t' hct y y' hcf
  obtain ⟨h, J', hR, -⟩ := (hMP.tuple t).reps
  have hlevJ := ((GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ t t' hct).2.2.2 i hτ).1
  have hR' : RepsR R i t' (fun j => h (e.symm j)) (M.bad t') J' (M.Lh t') (M.gam t') (M.vol t') := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
    obtain ⟨-, -, -, hbad, hvol, hk⟩ := hsame
    have hQ' : R.Q t' = R.Q t := hct.1
    refine ⟨hbad ▸ h1, fun PP hPP => ?_, ?_, ?_, ?_, fun g => ?_, fun j => ?_⟩
    · rw [hbad]; exact h2 PP (hQ' ▸ hPP)
    · rw [hlevJ]; exact h3
    · rw [hlevJ]; exact h4
    · rw [hlevJ, hvol]; exact h5
    · obtain ⟨p, hp, huniq⟩ := h6 g
      refine ⟨e p, by simpa using hp, fun j hj => ?_⟩
      have := huniq (e.symm j) hj
      rw [← this]
      simp
    · obtain ⟨a1, a2, a3⟩ := h7 (e.symm j)
      have hkj := hk (e.symm j)
      simp only [Equiv.apply_symm_apply] at hkj
      exact ⟨hbad ▸ a1, hkj.1.trans a2, hkj.2.2.2.trans a3⟩

  choose xv xv' hxv using hval
  let xs : Fin n → M.Cl' t → VsV D i M.c'.F := fun k p => xv k (h p)
  let xs' : Fin n → M.Cl' t' → VsV D i M.c'.F := fun k j => xv' k (h (e.symm j))
  choose f hfc hfs using fun k => GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie i T0 id M
    hMP t (xs k)
  have hsec : ∀ k, f k ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := fun k =>
    cusp_le_sec _ _ _ _ _ (hfc k)
  have hA : ∀ k g, ph i * R.thF i t (ys k) (v₀ i (sg0 D A)) g = ζ * psi M (κ i) z (f k) g := fun k g => by
    refine (hser t h J' hR (ys k) (xs k) (fun p => (hxv k (h p)).2.1) (f k) (hsec k) (hfs k) g).trans ?_
    unfold psi
    ring
  have hG : ∀ k, u • galRul hf (f k) ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧
      GlobalTheory.OneMapAll.IsSum M t' (xs' k) (u • galRul hf (f k)) := fun k =>
    hgal' (xs k) (xs' k) (fun p => by simp only [xs, xs', Equiv.symm_apply_apply]; exact (hxv k (h p)).1) (f k) (hsec k)
      (hfs k)
  have hB : ∀ k g, ph i * R.thF i t' (ys' k) (v₀ i (sg0 D A)) g = ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g :=
    fun k g => by
    refine (hser t' (fun j => h (e.symm j)) J' hR' (ys' k) (xs' k) (fun j => (hxv k (h (e.symm j))).2.2)
      (u • galRul hf (f k)) (hG k).1 (hG k).2 g).trans ?_
    rw [show ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g = ζ * ((u : ℂ) * psi M (κ i) z (galRul hf (f k)) g) by ring,
      ← psi_smul]
    unfold psi
    ring
  have hbc : ∀ k, ConjFun M (κ i) τ 1 (psi M (κ i) z (f k)) (psi M (κ i) z (galRul hf (f k))) := fun k =>
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z (f k) (hfc k) hEqM
  have hbc0 : ConjFun M (κ i) τ 1 (psi M (κ i) z 0) (psi M (κ i) z (galRul hf 0)) :=
    GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z 0 (Submodule.zero_mem _) hEqM
  have hcomb := GlobalTheory.ConjCombine.conj_comb ((conjFun_iff M (κ i) τ 1 _ _).1 hbc0) (fun k => ζ * α k)
    (fun k => psi M (κ i) z (f k)) (fun k => psi M (κ i) z (galRul hf (f k)))
    (fun k => (conjFun_iff M (κ i) τ 1 _ _).1 (hbc k)) (ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ))
  have hΦ : (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) =
      fun g => ∑ k, (ζ * α k) * psi M (κ i) z (f k) g := by
    funext g
    rw [hy, map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, hA k g]
    ring
  have hΦ' : (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) =
      fun g => ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ) * ∑ k, τ (ζ * α k) * psi M (κ i) z (galRul hf (f k)) g := by
    funext g
    rw [hy', map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hu' : (u : ℂ) = k0 * ((R.xi t' s : Circle) : ℂ) := hu
    have hcan : ζ * k0 / τ ζ * τ ζ = ζ * k0 := div_mul_cancel₀ _ hτζ
    rw [mul_left_comm, hB k g, hu', map_mul]
    linear_combination (-(τ (α k) * ((R.xi t' s : Circle) : ℂ) * psi M (κ i) z (galRul hf (f k)) g)) * hcan
  rw [conjFun_congr (O i) M, conjFun_iff, hΦ, hΦ']
  exact hcomb

end GlobalTheory.ConjClassSum
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjClassSum.conj_lifts | exact GlobalTheory.ConjClassSum.conj_lifts | (intros; apply GlobalTheory.ConjClassSum.conj_lifts <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem GlobalTheory.ConjTwist.conjFun_ser : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc u hu τ hfix
  obtain ⟨ζ0, hζ, H⟩ := GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion hCI D G Pl0 T0 A T R F κ v₀ O ph hn hC hT0 hFW hIo hQ i hP hPh c hc τ hfix
  refine ⟨ζ0, hζ, fun t t' ht => ?_⟩
  obtain ⟨s, Hs⟩ := H t t' ht
  refine ⟨s, fun h hh x x' hx => ?_⟩
  obtain ⟨y, y', hy, he⟩ := GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries D G Pl0 T0 A T R F κ v₀ hC hFW i Unit (fun _ => A.μ0) (O i) hP.2 c hc τ t t' hfix ht h hh x x' hx
  have hv : (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) := funext hu
  have e1 : (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) = fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).1, hv]
  have e2 : (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) = fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g := by
    funext g
    rw [← (he u g).2, hv]
  rw [e1, e2]
  exact Hs y y' hy
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  atlas_forward_decl GlobalTheory.ConjTwist.conjFun_ser
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FlatConj.flat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hQG i τ t t' hV hFix hct f f' hf hf'
  obtain ⟨z, B, ε, r, ψP, hz, hB, hprim, hform⟩ := GlobalTheory.T.heckeChoice_flatVector_factoredForm D G Pl0 T0 A T R F hC hQG i t hV
  obtain ⟨s1, e1⟩ := hform t rfl f hf
  obtain ⟨s2, e2⟩ := hform t' hct.1 f' hf'
  obtain ⟨h1, hne, -, -⟩ := GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct
  have hg : ∀ PP ∈ R.Q t, ∃ a : (kP PP)ˣ, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      ((R.xiR t' PP a : ℂˣ) : ℂ) ^ r * GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    intro PP hP
    obtain ⟨a, -, ha⟩ := (@GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (GlobalTheory.FlatConj.resField PP) (GlobalTheory.FlatConj.resFintype PP) (Classical.decEq _)
      (ψP PP) (R.xiR t PP) r (hprim PP hP) (hne PP hP) _ rfl).2.2.2 τ (R.xiR t' PP) (h1 PP hP)
    exact ⟨a, ha⟩
  choose a ha using hg
  let v : Pl D.host.E → ℂ := fun PP => if h : PP ∈ R.Q t then ((R.xiR t' PP (a PP h) : ℂˣ) : ℂ) else 1
  obtain ⟨s3, e3⟩ := GlobalTheory.FlatConj.prod_val (R.xi t') (R.Q t) v fun PP hP => by
    simp only [v, dif_pos hP]
    exact GlobalTheory.FlatConj.xiR_val hC t' PP (hct.1 ▸ hP) _
  have hprod : ∏ PP ∈ R.Q t, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      (∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP hP => ?_
    simp only [v, dif_pos hP]
    exact ha PP hP
  refine ⟨z, _, _, s2 * s1⁻¹ * s3 ^ (-((r : ℤ) * ε)), hz, e1, e2, ?_⟩
  have hX : ((R.xi t' s1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hV3 : ((R.xi t' s3 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : τ (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) ^ ε * ((R.xi t s1 : Circle) : ℂ)) =
      B * ((∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε *
        ((R.xi t' s1 : Circle) : ℂ) := by
    rw [map_mul, map_mul, map_zpow₀, map_prod, hprod, hB τ hFix, ← hct.2 s1]
  rw [key, e3]
  simp only [map_mul, map_inv, map_zpow, Circle.coe_mul, Circle.coe_inv, Circle.coe_zpow]
  rw [mul_zpow, ← zpow_natCast, ← _root_.zpow_mul, _root_.zpow_neg]
  have hW : ((R.xi t' s3 : Circle) : ℂ) ^ ((r : ℤ) * ε) ≠ 0 := zpow_ne_zero _ hV3
  field_simp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChoice_flatScalar_conj_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  atlas_forward_decl GlobalTheory.FlatConj.flat_conj
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | exact GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | (intros; apply GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

namespace GlobalTheory.ConjTwist.FlatSeries

theorem scale {X B : Type} (J : B → X → ℂ) (τ : ℂ ≃+* ℂ) (ζ η C C' : ℂ) (Φ Φ' : X → ℂ)
    (h1 : ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, Φ g = ∑ k, a k * J (f k) g)
    (h2 : ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, Φ g = ∑ k, a k * J (f k) g) →
      ∀ g, Φ' g = ∑ k, ζ * τ (a k) * J (f k) g)
    (hC : C' = η * τ C) :
    (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, C * Φ g = ∑ k, a k * J (f k) g) ∧
      ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, C * Φ g = ∑ k, a k * J (f k) g) →
        ∀ g, C' * Φ' g = ∑ k, ζ * η * τ (a k) * J (f k) g := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, a, f, h⟩ := h1
    refine ⟨n, fun k => C * a k, f, fun g => ?_⟩
    rw [h g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro n a f ha g
    by_cases hC0 : C = 0
    · subst hC0
      obtain ⟨n₀, b, e, hb⟩ := h1
      have hC' : C' = 0 := by simp [hC]
      have hz : ∀ g, ∑ k, a k * J (f k) g = 0 := fun g => by simpa using (ha g).symm
      have hcat : ∀ g, Φ g = ∑ k, (Fin.append b a) k * J ((Fin.append e f) k) g := fun g => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [hz g, add_zero, hb g]
      have e1 := h2 _ _ _ hcat g
      have e2 := h2 _ _ _ hb g
      rw [Fin.sum_univ_add] at e1
      simp only [Fin.append_left, Fin.append_right] at e1
      rw [e2] at e1
      have e3 : ∑ k, ζ * τ (a k) * J (f k) g = 0 := by simpa using e1.symm
      have e4 : ∑ k, ζ * η * τ (a k) * J (f k) g = η * ∑ k, ζ * τ (a k) * J (f k) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e3, hC']
      simp
    · have hτ : τ C ≠ 0 := fun h => hC0 ((map_eq_zero_iff τ τ.injective).1 h)
      have hexp : ∀ g, Φ g = ∑ k, (C⁻¹ * a k) * J (f k) g := fun g => by
        have : Φ g = C⁻¹ * (C * Φ g) := by field_simp
        rw [this, ha g, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h2 _ _ _ hexp g, hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀]
      field_simp

end GlobalTheory.ConjTwist.FlatSeries

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {ζ η C C' : ℂ}
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') (hC : C' = η * τ C) :
    ConjFun O κ τ (ζ * η) (fun g => C * Φ g) (fun g => C' * Φ' g) := by
  have key := GlobalTheory.ConjTwist.FlatSeries.scale
    (fun (b : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (g : GA D (Wc D i)) =>
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (b : T.toCore.R ((i : ℕ) + 1)) g))
    τ ζ η C C' Φ Φ' h.1 (fun n a f ha g => h.2 n a f ha g) hC
  exact ⟨key.1, fun n a f ha g => key.2 n a f ha g⟩
end

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.ConjTwist.FlatSeries.conj_flat_series : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  obtain ⟨ζ0, hζ0, hser⟩ := GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate hCI D G Pl0 T0 A T R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  refine ⟨ζ0, hζ0, fun t t' hConj f f' hf hf' => ?_⟩
  obtain ⟨s, hs⟩ := hser t t' hConj
  obtain ⟨z, C, C', s₂, hz, rfl, rfl, hC⟩ :=
    GlobalTheory.T.heckeChoice_flatScalar_conj_twist D G Pl0 T0 A T R F κ v₀ hCore hQ i τ t t' hPins.2.lift.std hFix hConj f f' hf hf'
  refine ⟨s * s₂, fun h hh x x' hx => ?_⟩
  have hzG : z ∈ GfC (Vc D i) := hz.2.1
  have base := hs (h * z) ((GfC (Vc D i)).mul_mem hh hzG) x x' hx
  have sc := GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O i) (κ i) τ base hC
  have e1 : (fun g => ph i * ser R i t (C • R.ωP i t (z, 1) (R.vP i t)) u h (cc x) g) =
      fun g => C * (ph i * ser R i t (R.vP i t) u (h * z) (cc x) g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t z C hzG u h (cc x) g]
    ring
  have e2 : (fun g => ph i * ser R i t' (C' • R.ωP i t' (z, 1) (R.vP i t')) u h (cc x') g) =
      fun g => C' * (ph i * ser R i t' (R.vP i t') u (h * z) (cc x') g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t' z C' hzG u h (cc x') g]
    ring
  rw [e1, e2]
  have e3 : ζ0 * ((R.xi t' (s * s₂) : Circle) : ℂ) = ζ0 * ((R.xi t' s : Circle) : ℂ) * ((R.xi t' s₂ : Circle) : ℂ) := by
    rw [map_mul, Circle.coe_mul, mul_assoc]
  rw [e3]
  exact sc
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_thetaSeries_flatDatum_rootOfUnity : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  atlas_forward_decl GlobalTheory.ConjTwist.FlatSeries.conj_flat_series
end
