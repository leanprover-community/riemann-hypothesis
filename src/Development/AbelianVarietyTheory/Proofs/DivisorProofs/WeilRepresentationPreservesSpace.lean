import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProduct

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_place_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J), ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
    ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  first | exact @GlobalTheory.UnitaryPlaceSplit.exists_split_at | exact GlobalTheory.UnitaryPlaceSplit.exists_split_at | (intros; apply GlobalTheory.UnitaryPlaceSplit.exists_split_at <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_homogeneous_operator_linear : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  first | exact @GlobalTheory.SchurLin.schur_linear_model | exact GlobalTheory.SchurLin.schur_linear_model | (intros; apply GlobalTheory.SchurLin.schur_linear_model <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocOpLin

theorem acts_lin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  intro F _ _ κ _ v Op c φ φ' η η' ζ hφ hφ' h₁ h₂ h₃
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have hs : c • φ + φ' ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem c hφ) hφ'
  have e : ∀ α β : (κ → Fv F v) → ℂ, tens (evFin F v) (c • α + β) R =
      c • tens (evFin F v) α R + tens (evFin F v) β R := by
    intro α β
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : tens (evFin F v) ζ R = tens (evFin F v) (c • η + η') R := by
    rw [← h₃ R (hR _ hs), e, map_add, map_smul, h₁ R (hR φ hφ), h₂ R (hR φ' hφ'), e]
  funext y
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.LocOpLin
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_action_linear_in_vector : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  atlas_forward_decl GlobalTheory.LocOpLin.acts_lin
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_local_schwartz_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  first | exact @GlobalTheory.IntertwLocal.local_intertw | exact GlobalTheory.IntertwLocal.local_intertw | (intros; apply GlobalTheory.IntertwLocal.local_intertw <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_moment_matrix_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  first | exact @GlobalTheory.Div.CoordOpp.coord_opp_conj | exact GlobalTheory.Div.CoordOpp.coord_opp_conj | (intros; apply GlobalTheory.Div.CoordOpp.coord_opp_conj <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_unitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  first | exact @GlobalTheory.SympInv.symp_act | exact GlobalTheory.SympInv.symp_act | (intros; apply GlobalTheory.SympInv.symp_act <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  first | exact @GlobalTheory.LagrCoord.exists_coord | exact GlobalTheory.LagrCoord.exists_coord | (intros; apply GlobalTheory.LagrCoord.exists_coord <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  first | exact @GlobalTheory.OppLinChar.char_eq_psi_symp | exact GlobalTheory.OppLinChar.char_eq_psi_symp | (intros; apply GlobalTheory.OppLinChar.char_eq_psi_symp <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinOp

theorem local_op_eq_smul : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι g hg h hh φ hφ φ₁ hφ₁ hacts
  classical
  set co : Matrix (Fin a') (Fin (a + a')) (AE F E) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
      (1 : GL (Fin (a + a')) (Fv F v)).1) with hco
  have hL : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t) co ι := hι
  have hP' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  obtain ⟨hex1, hex2, -⟩ := GlobalTheory.T.theta_action_exists hPr F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v

  have hex1' : ∀ ξ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, ∃ η, ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
      η ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, h)) ξ η := by
    intro ξ
    by_cases hξ : ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v)
    · obtain ⟨η, hη, -⟩ := hex1 g hg h hh ξ hξ
      exact ⟨η, fun _ => hη⟩
    · exact ⟨0, fun h' => absurd h' hξ⟩
  choose T hTspec using hex1'

  set ιi := Function.invFunOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    with hιi
  have hinv := hL.bij.invOn_invFunOn
  have hi1 : ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ιi Ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ ι (ιi Ξ) = Ξ :=
    fun Ξ hΞ => ⟨hL.bij.surjOn.mapsTo_invFunOn hΞ, hinv.2 hΞ⟩
  have hi2 : ∀ ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ιi (ι ξ) = ξ := fun ξ hξ => hinv.1 hξ

  set gt := (mat g).map (piW t) with hgt
  set gi := (mat g⁻¹).map (piW t) with hgi
  set ht' := (mat h).map (piW t) with hht
  set hi := (mat h⁻¹).map (piW t) with hhi
  have hg1 : gt * gi = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g * mat g⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : gi * gt = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g⁻¹ * mat g = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh1 : ht' * hi = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h * mat h⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh2 : hi * ht' = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h⁻¹ * mat h = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : giᵀ * gtᵀ = 1 := by rw [← Matrix.transpose_mul, hg1, Matrix.transpose_one]
  have hPP' : gtᵀ * giᵀ = 1 := by rw [← Matrix.transpose_mul, hg2, Matrix.transpose_one]

  have at_conj : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u →
      At (evFin F v) (mat g * u * (mat h)ᵀ) := by
    intro u hu c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  have hmap : ∀ (f : AE F E →+* Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      (mat g * u * (mat h)ᵀ).map f = (mat g).map f * u.map f * ((mat h).map f)ᵀ := by
    intro f u
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hco_act : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), co (mat g * u * (mat h)ᵀ) = giᵀ * co u * hi := by
    intro u
    have hca : gtᵀ * co (mat g * u * (mat h)ᵀ) * ht' = co u := GlobalTheory.T.local_moment_matrix_transform F E σ a' (a + a') G.V' G.W v t g h u
    calc co (mat g * u * (mat h)ᵀ) = (giᵀ * gtᵀ) * co (mat g * u * (mat h)ᵀ) * (ht' * hi) := by
          rw [hPP, hh1, Matrix.one_mul, Matrix.mul_one]
      _ = giᵀ * (gtᵀ * co (mat g * u * (mat h)ᵀ) * ht') * hi := by simp only [Matrix.mul_assoc]
      _ = giᵀ * co u * hi := by rw [hca]

  set A : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ :=
    fun Ξ Y => ι (T (ιi Ξ)) (giᵀ * Y * hi) with hA
  have hlin : ∀ (c0 : ℂ), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ∀ Ξ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c0 • Ξ + Ξ') = c0 • A Ξ + A Ξ' := by
    intro c0 Ξ hΞ Ξ' hΞ'
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨hξ', hιξ'⟩ := hi1 Ξ' hΞ'
    have hs : c0 • ιi Ξ + ιi Ξ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ c0 hξ) hξ'
    have e1 : ιi (c0 • Ξ + Ξ') = c0 • ιi Ξ + ιi Ξ' := by
      have : ι (c0 • ιi Ξ + ιi Ξ') = c0 • Ξ + Ξ' := by rw [map_add, map_smul, hιξ, hιξ']
      rw [← this]; exact hi2 _ hs
    obtain ⟨-, hTa1⟩ := hTspec _ hξ
    obtain ⟨-, hTa2⟩ := hTspec _ hξ'
    obtain ⟨-, hTa3⟩ := hTspec _ hs
    have e2 := GlobalTheory.T.local_action_linear_in_vector F (Fin a' × Fin (a + a')) v (om' (g, h)) c0 (ιi Ξ) (ιi Ξ') _ _ _ hξ hξ' hTa1 hTa2 hTa3
    funext Y
    show ι (T (ιi (c0 • Ξ + Ξ'))) (giᵀ * Y * hi) = c0 * ι (T (ιi Ξ)) (giᵀ * Y * hi) + ι (T (ιi Ξ')) (giᵀ * Y * hi)
    rw [e1, e2, map_add, map_smul]
    rfl
  have hA0 : A 0 = 0 := by
    have h0 := hlin 1 0 (zero_mem _) 0 (zero_mem _)
    simp only [one_smul, add_zero] at h0
    have h2 : A 0 + A 0 = A 0 + 0 := by rw [add_zero]; exact h0.symm
    exact add_left_cancel h2
  have hadd : ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (f + f') = A f + A f' := fun f hf f' hf' => by simpa using hlin 1 f hf f' hf'
  have hsmul : ∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c • f) = c • A f :=
    fun c f hf => by simpa [hA0] using hlin c f hf 0 (zero_mem _)

  have hut_map : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), ∀ f : AE F E →+* Fv F v, u.map f = 0 →
      (mat g * u * (mat h)ᵀ).map f = 0 := by
    intro u f hu
    rw [hmap, hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsurj := fun Y => GlobalTheory.T.local_matrix_moment_surjective F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Y
  have htr : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => Ξ (Y + Z)) = fun Y => A Ξ (Y + Z) := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hcu⟩ := hsurj Z
    have hcu' : co u = Z := hcu
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => Ξ (Y + Z) := by
      funext Y
      rw [hL.trans u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ Y, hιξ, hcu']
    have e2 : ιi (fun Y => Ξ (Y + Z)) = ξ₁ := by rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    show ι (T (ιi (fun Y => Ξ (Y + Z)))) (giᵀ * Y * hi) = ι (T (ιi Ξ)) (giᵀ * (Y + Z) * hi)
    rw [e2, ← e3, hL.trans _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄, hco_act, hcu',
      Matrix.mul_add, Matrix.add_mul]

  have hmul : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * A Ξ Y := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hchar⟩ := GlobalTheory.T.local_matrix_moment_surjective_conj F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Z
    have hchar' : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, co x i j * Z i j) := hchar
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y := by
      funext Y
      obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
      have hcx' : co x = Y := hcx
      rw [← hcx', hL.mult u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ x hx hxt, hιξ, hchar' x hx hxt]
    have e2 : ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) = ξ₁ := by
      rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
    have hcx' : co x = Y := hcx
    have e4 : co (mat g * x * (mat h)ᵀ) = giᵀ * Y * hi := by rw [hco_act, hcx']
    have hs : symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u := GlobalTheory.T.symplectic_form_unitary_invariant F E σ a' (a + a') G.V' G.W g h x u
    show ι (T (ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y))) (giᵀ * Y * hi) =
      GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * ι (T (ιi Ξ)) (giᵀ * Y * hi)
    rw [e2, ← e3, ← e4, hL.mult _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄ _ (at_conj x hx)
      (hut_map x _ hxt), hs, hchar' x hx hxt, hcx']
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.additive_homogeneous_operator_linear (Fv F v) (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) a' (a + a') A hadd hsmul htr hmul
  have hιφ : ι φ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hL.bij.mapsTo hφ
  have eT : φ₁ = T φ := (hex1 g hg h hh φ hφ).unique ⟨hφ₁, hacts⟩ (hTspec φ hφ)
  refine ⟨cc, ⟨gtᵀ, giᵀ, hPP', hPP⟩, ⟨ht', hi, hh1, hh2⟩, fun Y => ?_⟩
  have key := congrFun (hcc (ι φ) hιφ) (gtᵀ * Y * ht')
  change ι (T (ιi (ι φ))) (giᵀ * (gtᵀ * Y * ht') * hi) = cc * ι φ (gtᵀ * Y * ht') at key
  have ee : giᵀ * (gtᵀ * Y * ht') * hi = Y := by
    simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hh1, Matrix.mul_one]
  rw [hi2 φ hφ, ← eT, ee] at key
  exact key

end GlobalTheory.OppLinOp

end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_local_theta_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  atlas_forward_decl GlobalTheory.OppLinOp.local_op_eq_smul
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SoStable

theorem so_stable : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT γ Φ' hΦ
  unfold Model.So at hΦ ⊢
  induction hΦ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, hloc, rfl⟩ := hx
    obtain ⟨g₁, g₂, hg, hg₁, hg₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ a' G.V'.J B.v₁ γ.1
    obtain ⟨h₁, h₂, hh, hh₁, hh₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ (a + a') G.W.J B.v₁ γ.2
    have hγ : γ = (g₁, h₁) * (g₂, h₂) := Prod.ext hg hh
    obtain ⟨f₂, φ₂, hSB₂, hcof₂, hv₂, he₂⟩ :=
      GlobalTheory.T.theta_trivial_at_place_product hP F E σ B a a' G X om om' hT B.v₁ g₂ h₂ hg₂ hh₂ f φ hSB hcof
    obtain ⟨φ', hSB', hne', hacts, he'⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT B.v₁ g₁ hg₁ h₁ hh₁ f₂ φ₂ hSB₂ hcof₂
    rw [hγ, map_mul, Module.End.mul_apply, he₂, he']
    refine Submodule.subset_span ⟨f₂, φ', hSB', ?_, ?_, rfl⟩
    · filter_upwards [hcof₂, (Set.finite_singleton B.v₁).compl_mem_cofinite] with w hw hw'
      rw [hne' w hw', hw]
    · obtain ⟨hφSB, ι, hι, hsupp⟩ := hloc
      refine ⟨hSB' _, ι, hι, fun Y hY => ?_⟩
      obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι g₁ hg₁ h₁ hh₁
        (φ₂ B.v₁) (hSB₂ _) (φ' B.v₁) (hSB' _) hacts
      rw [hPQ, hv₂, hsupp, mul_zero]
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit

end GlobalTheory.SoStable
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_preserves_space : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  atlas_forward_decl GlobalTheory.SoStable.so_stable
end
