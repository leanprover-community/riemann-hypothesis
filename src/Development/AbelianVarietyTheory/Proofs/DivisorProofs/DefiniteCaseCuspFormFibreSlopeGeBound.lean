import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPo
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKronecker
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbedd
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecordAtOfIsArcFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormMulDetGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily

section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), ∃ φ : (TIdx (part Dw a) → c.F) →ₗ[c.F] Rul Xo c, Function.Injective φ ∧ LinearMap.range φ = cuspOn U Z (wtZ a n) ∧ ∀ x, Reads Z P.y₀ a n x (φ x) := by
  first | exact @GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | exact GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | (intros; apply GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads <;> assumption)
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DualWeyl.EvBound

theorem sum_sq_norm_evalAt_onBasis_eq_one (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (g : UN n) :
    ∑ i, ‖evalAt g.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := GlobalTheory.DualWeyl.Repro.exists_repr la
  have h1 := GlobalTheory.DualWeyl.Repro.normSq_repr hla hk
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  let u : UN n := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
  rw [← h1, ← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← he, inner_toSpace, GlobalTheory.DualWeyl.Repro.form_rhoU_repr hk]
  rfl

theorem sum_sq_norm_evalAt_onBasis_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n,
    ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 :=
  fun n la hla u => (sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le

end GlobalTheory.DualWeyl.EvBound
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n, ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 := by
  atlas_forward_decl GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerProductFamily_mul_one_det : ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R), kron M * kron M' = kron (fun t => M t * M' t) ∧ kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧ (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  first | exact @GlobalTheory.DefPt.kronFamily_mul_one_det | exact GlobalTheory.DefPt.kronFamily_mul_one_det | (intros; apply GlobalTheory.DefPt.kronFamily_mul_one_det <;> assumption)
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  first | exact @GlobalTheory.DefPt.tval_translate | exact GlobalTheory.DefPt.tval_translate | (intros; apply GlobalTheory.DefPt.tval_translate <;> assumption)
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.TSup

theorem evalAt_intVec {n : ℕ} (la : Fin n → ℕ) (y : Matrix (Fin n) (Fin n) ℂ) (j : Idx la) :
    evalAt y (map (Int.castRingHom ℂ) (intVec la j)) =
      ∑ i, onMat la i j * evalAt y (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ) := by
  rw [← coe_basis]
  have h : basis la ℂ j = ∑ i, onMat la i j • (toSpace la).symm (onBasis la i) := by
    apply (toSpace la).injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply, onMat, Matrix.of_apply]
    exact ((onBasis la).sum_repr _).symm
  rw [h, Submodule.coe_sum, map_sum]
  simp [Submodule.coe_smul, map_smul]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ}

theorem tval_eq_onb (la : ∀ t, Fin (N t) → ℕ) (z : TIdx la → ℂ) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    tval la z y = ∑ J : TIdx la, ((kron fun t => onMat (la t)) *ᵥ z) J *
      ∏ t, evalAt (y t) (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) := by
  unfold tval
  simp_rw [evalAt_intVec, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

theorem norm_sum_mul_le {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem mul_norm_tval_le_fibNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  intro T _ _ N la hla x X u s hs
  have h1 : tval la x (fun t => X t * (u t).1) =
      tval la ((kron fun t => rhoMat (la t) (X t)) *ᵥ x) (fun t => (u t).1) := by
    have h := GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker T N la ℂ ℂ (RingHom.id ℂ) x X (fun t => (u t).1)
    simpa only [RingHom.id_apply, RingHom.coe_id, Matrix.map_id] using h
  have hk := (GlobalTheory.T.kroneckerProductFamily_mul_one_det T (fun t => Idx (la t)) ℂ (fun t => onMat (la t)) (fun t => rhoMat (la t) (X t))).1
  set E : TIdx la → ℂ := fun J => ∏ t, evalAt (u t).1
    (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) with hE
  have h2 : (s : ℂ) * tval la x (fun t => X t * (u t).1) = ∑ J, (fibY la s X *ᵥ x) J * E J := by
    rw [h1, tval_eq_onb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    have hsm : ∀ (M : Matrix (TIdx la) (TIdx la) ℂ) (v : TIdx la → ℂ), ((s : ℂ) • M) *ᵥ v = (s : ℂ) • (M *ᵥ v) := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [fibY, hsm, ← hk, ← Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : ∑ J, ‖E J‖ ^ 2 ≤ 1 := by
    have : ∑ J, ‖E J‖ ^ 2 = ∏ t, ∑ i, ‖evalAt (u t).1
        (((toSpace (la t)).symm (onBasis (la t) i) : nabla (la t) ℂ) : Pol (N t) ℂ)‖ ^ 2 := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [hE, norm_prod, Finset.prod_pow]
    rw [this]
    exact Finset.prod_le_one (fun t _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun t _ => GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one (N t) (la t) (hla t) (u t))
  have h4 : s * ‖tval la x (fun t => X t * (u t).1)‖ = ‖(s : ℂ) * tval la x (fun t => X t * (u t).1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  rw [h4, h2]
  refine (norm_sum_mul_le _ _).trans ?_
  calc _ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one]
        exact h3
    _ = _ := mul_one _

end GlobalTheory.TSup

end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  atlas_forward_decl GlobalTheory.TSup.mul_norm_tval_le_fibNorm
end

section
section
noncomputable section

namespace GlobalTheory.DefPt.IntNorm

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

open GlobalTheory.Frames GlobalTheory.LamT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

theorem metric_of_archFr {y₀ : FrPt Xo c c.F} {σ : c.F →+* ℂ} {N : ℝ} {X : Mats Dw ℂ} (h : ArchFr y₀ σ N X)
    {z y : FrPt Xo c (CAt σ)} (hz : FrMap (Algebra.ofId c.F (CAt σ)) y₀ z) {Y Gr : Mats Dw ℂ} {s : ℂ} {M : ℝ}
    (hy : FrChg (S := CAt σ) (fun τ => (Y τ)ᵀ) s z y) (hm : IsMetric y M Gr) :
    M = ‖s‖ ^ 2 * N ∧ ∀ τ, ∃ W : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, Y τ = X τ * W ∧ Wᴴ * W = Gr τ := by
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  have hm₁ := h.2.2 z y₁ hz hy₁
  obtain ⟨g, a, -, hg⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) y₁ y).1 (hy.1.trans hy₁.1.symm)
  obtain ⟨e1, e2⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) z y).2 _ _ _ _ hy
    ((frChg_refl_and_comp E H Dw l Xo c (CAt σ) z y₁ y).2 _ _ _ _ hy₁ hg)
  have hm₂ := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ y₁ y N _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (a : CAt σ)) (Units.ne_zero (M₀ := ℂ) a) hg hm₁
  obtain ⟨hN, hG⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hm hm₂
  have e3 : s = (show ℂ from (a : CAt σ)) := e2.trans (mul_one _)
  refine ⟨by rw [hN, e3], fun τ => ⟨Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ), ?_, ?_⟩⟩
  · have e4 : (Y τ)ᵀ = (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ) * (X τ)ᵀ := congrFun e1 τ
    rw [← Matrix.transpose_transpose (Y τ), e4, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [congrFun hG τ, Matrix.mul_one]

theorem isMetric_conj_one {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)} {y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))} {N : ℝ}
    (hpq : 1 ≤ Dw.p + Dw.q) (h : FrMap (GlobalTheory.FrameNorm.conjAlg σ) y y') (hm : IsMetric y N fun _ => 1) :
    IsMetric y' N fun _ => 1 := by
  have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq h hm
  have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
      fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
  rwa [h1] at hm'

theorem archFr_conj (hpq : 1 ≤ Dw.p + Dw.q) {y₀ : FrPt Xo c c.F} {σ : c.F →+* ℂ} {N N' : ℝ} {X X' : Mats Dw ℂ}
    (h : ArchFr y₀ σ N X) (h' : ArchFr y₀ ((starRingEnd ℂ).comp σ) N' X') :
    N' = N ∧ ∀ τ, ‖(X' τ).det‖ = ‖(X τ).det‖ := by
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  have hm := h.2.2 z y hz hy
  obtain ⟨z', hz'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) z
  obtain ⟨y', hy'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) y
  have h0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hz'
  rw [Subsingleton.elim ((GlobalTheory.FrameNorm.conjAlg σ).comp _) (Algebra.ofId _ _)] at h0
  have hc := (ChgBC.frChg_baseChange E H Dw l Xo c _ _ (GlobalTheory.FrameNorm.conjAlg σ) z y z' y' _ _ hy hz').1 hy'
  obtain ⟨hN, hW⟩ := metric_of_archFr h' h0 (Y := fun τ => (X τ).map (starRingEnd ℂ)) hc (isMetric_conj_one hpq hy' hm)
  refine ⟨?_, fun τ => ?_⟩
  · rw [hN]
    have : (GlobalTheory.FrameNorm.conjAlg σ) ((1 : (CAt σ)ˣ) : CAt σ) = 1 := map_one _
    rw [this]
    exact (show ‖(1 : ℂ)‖ ^ 2 * N' = N' by simp).symm
  · obtain ⟨W, h1, h2⟩ := hW τ
    have h3 : ‖W.det‖ = 1 := by
      have h4 := congrArg (fun M => ‖Matrix.det M‖) h2
      simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one, norm_one] at h4
      nlinarith [norm_nonneg W.det]
    have h5 := congrArg (fun M => ‖Matrix.det M‖) h1
    simp only [Matrix.det_mul, norm_mul, h3, mul_one] at h5
    rw [← h5, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.norm_conj]

theorem mem_range_of_le_one {w : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa w T.V io e) {b : c.F} (hb : w.valuation c.F b ≤ 1) : io b ∈ Set.range (algebraMap T.V T.Fr) := by
  by_cases h0 : b = 0
  · exact ⟨0, by simp [h0]⟩
  refine GlobalTheory.ArcQ.RecFr.mem_of_vV_nonneg ?_
  rw [ho.2]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 hb
  simp only [WithZero.log_one] at this
  simp only [vLa]
  omega

theorem map_tval {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {S S' : Type} [CommRing S]
    [CommRing S'] (φ : S →+* S') (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    φ (tval la x y) = tval la (fun I => φ (x I)) fun t => (y t).map φ := by
  simp only [tval, map_sum, map_mul, map_prod]
  refine Finset.sum_congr rfl fun I _ => congrArg _ (Finset.prod_congr rfl fun t _ => ?_)
  generalize intVec (la t) (I t) = p
  induction p using MvPolynomial.induction_on with
  | C a => simp [GlobalTheory.DualWeyl.evalAt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [GlobalTheory.DualWeyl.evalAt]

theorem val_nonneg {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {x : TIdx (part Dw a) → c.F} {f : Rul Xo c}
    (hr : Reads Z P.y₀ a n x f) (hx : x ∈ locLat (P.matA a n)) (w : HeightOneSpectrum (𝓞 c.F)) :
    ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f := by
  intro v hv
  rcases mem_valOn_or (Z := Z) hv with h | h
  swap
  · rw [h f hr.1]; exact le_top
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := h
  letI := io.toAlgebra
  show 0 ≤ nval T.V e (evR Xo c f y.1)
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hl⟩ := P.loc w
  obtain ⟨Y, u, hY, hc⟩ := hl T io e ho y.1 z y.2.2 hz ((P.only _ y.1 hy.2).trans hz.1.symm)
  have hev := hr.2 T.Fr z y.1 (fun τ => (P.B w τ).map io * (Y τ).map (algebraMap T.V T.Fr)) _ (fun τ => by
      rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det]
      exact ((hB τ).isUnit.map io).mul ((hY τ).map _))
    ((ha.isUnit.map io).mul (u.isUnit.map _)) hz hc
  have hmv := GlobalTheory.DefPt.tval_translate _ _ (part Dw a) c.F T.Fr io x (P.B w) fun τ => (Y τ).map (algebraMap T.V T.Fr)
  choose x' hx' using fun I => mem_range_of_le_one ho (hx w I)
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.nval_nonneg_of_int e ⟨(u : T.V) ^ n * tval (part Dw a) x' Y, ?_⟩
  rw [hev, map_mul, map_tval, map_pow]
  erw [hmv]
  simp only [hx', PtData.matA, fibA, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, tval,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem cabs_le_matNorm {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {x : TIdx (part Dw a) → c.F} {f : Rul Xo c} (hr : Reads Z P.y₀ a n x f) {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)}
    (hy : y.x = spMap (algebraMap c.F (CAt σ)) ≫ P.y₀.x) (hm : IsMetric y 1 fun _ => 1) :
    cabs (evR Xo c f y) ≤ matNorm (P.matY a n) σ x := by
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) P.y₀
  obtain ⟨g, s, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 (hy.trans hz.1.symm)
  have hev := hr.2 (CAt σ) z y (fun τ => (g τ)ᵀ) s (fun τ => by rw [Matrix.det_transpose]; exact hg τ) s.isUnit hz hc
  obtain ⟨hN, hW⟩ := metric_of_archFr (P.arch σ) hz
    (Y := fun τ => Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) hc hm
  choose W hW1 hW2 using hW
  have hs : cabs (s : CAt σ) = (Real.sqrt (P.N σ))⁻¹ := by
    rw [← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left hN.symm]
    exact (Real.sqrt_sq (norm_nonneg (show ℂ from (s : CAt σ)))).symm
  have hb := GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm _ _ (part Dw a) (fun τ i j hij => hd.1 τ hij) (fun I => σ (x I)) (P.X σ)
    (fun τ => ⟨W τ, Matrix.mem_unitaryGroup_iff'.2 (hW2 τ)⟩) ((Real.sqrt (P.N σ))⁻¹ ^ n) (by positivity)
  refine le_trans (le_of_eq ?_) hb
  have e : (fun τ => P.X σ τ * W τ) =
      fun τ => Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ) :=
    funext fun τ => (hW1 τ).symm
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, ← hs, e]
  congr 1
  exact norm_pow (α := ℂ) _ _

theorem cabs_le_matNorm_conj (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hd : Dom a n) {x : TIdx (part Dw a) → c.F} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (hr : Reads Z P.y₀ a n x f)
    {σ σ' : c.F →+* ℂ} (hσ : σ' = (starRingEnd ℂ).comp σ) {y : FrPt Xo c (CAt σ)}
    (hy : y.x = spMap (algebraMap c.F (CAt σ)) ≫ P.y₀.x) (hm : IsMetric y 1 fun _ => 1) :
    cabs (evR Xo c f y) ≤ matNorm (P.matY a n) σ' x := by
  subst hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨y', hy'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) y
  have hx : y'.x = spMap (algebraMap c.F (CAt ((starRingEnd ℂ).comp σ))) ≫ P.y₀.x := by
    rw [hy'.1, hy, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
    rfl
  have hb := cabs_le_matNorm P hd hr hx (isMetric_conj_one hpq hy' hm)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 f hf.1
    (GlobalTheory.FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
  rw [hev] at hb
  refine le_trans (le_of_eq ?_) hb
  exact (Complex.norm_conj _).symm

theorem exists_ortho {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (k : U.Comp) (x : (U.X k).dom) :
    ∃ y : FrPt Xo c (CAt σ), y.x = (U.un k x).x ∧ IsMetric y 1 (fun _ => 1) ∧
      homN U ξ (wtZ a n) f ⟨k, x.1⟩ = cabs (evR Xo c f y) := by
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hsec := hU.2.2.2.2.1 a n hd f hf k
  have hb := FrameDegreeData.bOf_mem (U.X k) x.2
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) x.2
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 x.1 x.2 _ hb
  obtain ⟨t₀, ht₀⟩ := (hU.2.2.2.1 k k x ⟨_, hz⟩).2 ⟨1, one_mem _, _, hb, by
    have : lact (1 : GL (Fin r) E) x.1 = x.1 := by
      funext τ
      simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rfl
    rw [this]⟩
  obtain ⟨g₀, -, -, hg₀⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ (U.un k x)).1 t₀).1 ht₀
  have hx₀ := hg₀.1
  clear hg₀ ht₀
  generalize rmul x.1 (FrameDegreeData.bOf (U.X k) x.1) = z at hz ho hp hx₀
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k ⟨z, hz⟩ (hξ k) ho
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (Real.sqrt (2 * Real.pi * ξ))⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρκ : ρ * (2 * Real.pi * ξ) * ρ = 1 := by
    have := Real.mul_self_sqrt hκ.le
    have h2 := Real.sqrt_pos.2 hκ
    rw [hρ]
    generalize Real.sqrt (2 * Real.pi * ξ) = q at this h2
    rw [← this]
    field_simp
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  let Y : Mats Dw ℂ := fun _ => (ρ : ℂ) • 1
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) (U.un k ⟨z, hz⟩) (fun τ => (Y τ)ᵀ) 1 fun τ => by
    have : IsUnit ((Y τ)ᵀ).det := by simp [Y, hρc]
    exact this
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ _ y 1 _ Y 1 one_ne_zero hy hm0
  have hG : (fun b => (Y b)ᴴ * (((2 * Real.pi * ξ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) * Y b) =
      fun _ => 1 := by
    funext b
    have h3 : (ρ : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ) * ρ = 1 := by exact_mod_cast hρκ
    simp only [Y, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_assoc, h3, one_smul]
  rw [hG, norm_one, one_pow, mul_one] at hm1
  refine ⟨y, hy.1.trans hx₀, hm1, ?_⟩
  let t : Formalism.L2.Pj.Ix Dw → (CAt σ)ˣ := fun i => i.elim 1 fun _ => Units.mk0 (G₀ := ℂ) ρ hρc
  have ht : FrBor t (U.un k ⟨z, hz⟩) y := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ y y).1 t).2
    ⟨_, fun τ i j hij => show (Y τ)ᵀ i j = 0 by simp [Y, hij.ne'], fun τ i => show (Y τ)ᵀ i i = (ρ : ℂ) by simp [Y], hy⟩
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hlie : ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), ρ ^ a (p.1, p.2) = lieFac Dw ξ a := by
    have hs : ρ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [hρ, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    simp only [hs, ← Real.exp_nat_mul]
    rw [← Real.exp_sum, lieFac, ← Finset.sum_mul]
    congr 1
    rw [Fintype.sum_sigma]
    ring
  have hw : cabs (wchar (ex Dw a n) t) = lieFac Dw ξ a := by
    have h1 : cabs (t none : CAt σ) = 1 := norm_one (α := ℂ)
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, h1, one_pow, one_mul, ← hlie]
    refine Finset.prod_congr rfl fun p _ => ?_
    have h2 : cabs (t (some p) : CAt σ) = ρ := show ‖(ρ : ℂ)‖ = ρ by rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    rw [h2]
    rfl
  have hrd : ‖rdU U f k z‖ = cabs (evR Xo c f (U.un k ⟨z, hz⟩)) := by
    have e : rdU U f k z = toC (evR Xo c f (U.un k ⟨z, hz⟩)) := dif_pos hz
    rw [e]; rfl
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho), hrd] at hp
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw, homN, lieFacZ_wtZ, modelWt_wtZ, hp]
  rfl

theorem integral_and_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ σ, P.N ((starRingEnd ℂ).comp σ) = P.N σ ∧ ∀ τ, ‖(P.X ((starRingEnd ℂ).comp σ) τ).det‖ = ‖(P.X σ τ).det‖) ∧ ∀ (x : TIdx (part Dw a) → c.F) (f : Rul Xo c), f ∈ sec Xo c a n → Reads Z P.y₀ a n x f → (x ∈ locLat (P.matA a n) → ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f) ∧ ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ (wtZ a n) f z ≤ matNorm (P.matY a n) σ x := by
  intro E _ _ _ H Dw l Xo c r U ξ a n hD hd Z P
  have hpq : 1 ≤ Dw.p + Dw.q := hD.p.trans (Nat.le_add_right _ _)
  refine ⟨fun σ => archFr_conj hpq (P.arch σ) (P.arch _), fun x f hf hr => ⟨val_nonneg P hr, fun σ z hz => ?_⟩⟩
  obtain ⟨h, hZ⟩ := hz
  have hg := goodEmb_goodOf c σ
  obtain ⟨y, hy, hm, hn⟩ := exists_ortho hg (hD.unf _ hg) (hD.xi _ hg) hpq hd hf z.1 ⟨z.2, h⟩
  have hx := hy.trans (P.only _ _ hZ)
  refine le_trans (le_of_eq hn) ?_
  clear hn hy hZ
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    have := cabs_le_matNorm P hd hr hx hm
    exact this.trans (le_of_eq (by rw [e]))
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    exact cabs_le_matNorm_conj hpq P hd hf hr (by rw [e]; ext b; simp) hx hm

end GlobalTheory.DefPt.IntNorm

end
end

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ σ, P.N ((starRingEnd ℂ).comp σ) = P.N σ ∧ ∀ τ, ‖(P.X ((starRingEnd ℂ).comp σ) τ).det‖ = ‖(P.X σ τ).det‖) ∧ ∀ (x : TIdx (part Dw a) → c.F) (f : Rul Xo c), f ∈ sec Xo c a n → Reads Z P.y₀ a n x f → (x ∈ locLat (P.matA a n) → ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f) ∧ ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ (wtZ a n) f z ≤ matNorm (P.matY a n) σ x := by
  atlas_forward_decl GlobalTheory.DefPt.IntNorm.integral_and_norm_le
end

section
section
noncomputable section

namespace GlobalTheory.DefPt.ThetaDeg

section Key

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.Frames GlobalTheory.CM
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem rule_frChg {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {K : Type} [Field K] [CharZero K] [Algebra c.F K] (M : Mats Dw K) (a : K) (y y' : FrPt Xo c K)
    (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x) (hb : FrChg M a y y') (hT : Tied e y.s y.u Φ)
    (hT' : Tied e y'.s y'.u Φ') :
    a ^ 8 * (κ K Φ'.key : K) = (∏ τ, (M τ).det) ^ 4 * (κ K Φ.key : K) := by
  classical
  obtain ⟨hx, hc, hs⟩ := hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hκ.2.1 K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hκ.1 K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    a _ hsc hcomb
  have e3 : ((Matrix.blockDiagonal' M).submatrix e e).det = ∏ τ, (M τ).det := by
    rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']
  exact e2.trans (congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1)

theorem hermForm_eq_zero (T : PAT H (Sp ℂ)) (u : HolUnif T.pol.A T.pol.L T.pol.g)
    {Hm : Matrix (Fin T.pol.g) (Fin T.pol.g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ) {φ ψ : E →+* ℂ} (hne : φ ≠ ψ)
    {v w : epsR ℂ ⟶ T.t.G} {V W : Fin T.pol.g → ℂ} (tv : IsTangent v) (tw : IsTangent w) (hV : u.IsDiff V v)
    (hW : u.IsDiff W w) (ev : ∀ a : 𝓞 E, (v ≫ T.t.act.act a).left = spMap (epsMul (φ a)) ≫ v.left)
    (ew : ∀ a : 𝓞 E, (w ≫ T.t.act.act a).left = spMap (epsMul (ψ a)) ≫ w.left) : hermForm Hm V W = 0 := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT T.pol _ u Hm χ hAH
  choose ρ hρ using fun s : 𝓞 E => (HomLinear.exists_linear_of_isMonHom T.t.G T.t.G T.ab T.ab _ _ _ _ u u h1 h2
    (T.t.act.act s) (T.t.act.hom s)).imp fun _ h => h.1
  have hadj : ∀ a z w, hermForm Hm (ρ a z) w = hermForm Hm z (ρ (H.bar a) w) := fun a =>
    (weilEq_iff_hermForm_eq hT hL T.pol T.pol T.pol T.pol u u u u Hm Hm χ χ hAH hAH (T.t.act.act a) (𝟙 _) (𝟙 _)
      (T.t.act.act (H.bar a)) (ρ a) LinearMap.id LinearMap.id (ρ (H.bar a)) (hρ a)
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm) (hρ _)).1
      (weilEq_of_lamEq hL ℂ T.pol T.pol T.pol T.pol _ _ _ _ (T.t.act.hom a) inferInstance inferInstance
        (T.t.act.hom _) (by
          unfold LamEq
          rw [Category.comp_id, Category.comp_id]
          exact T.t.adj a))
  have key : ∀ {φ : E →+* ℂ} {v : epsR ℂ ⟶ T.t.G} {V : Fin T.pol.g → ℂ}, IsTangent v → u.IsDiff V v →
      (∀ a : 𝓞 E, (v ≫ T.t.act.act a).left = spMap (epsMul (φ a)) ≫ v.left) → ∀ a : 𝓞 E, ρ a V = φ a • V := by
    intro φ v V tv hV ev a
    have := T.t.act.hom a
    have h₁ := HomLinear.isDiff_comp u u (T.t.act.act a) (ρ a) (hρ a) tv hV
    have h₂ := CMCurveTest.isDiff_scaleVec u hV (φ a)
    have e : CMCurveTest.scaleVec (φ a) v = v ≫ T.t.act.act a := Over.OverMorphism.ext (ev a).symm
    rw [e] at h₂
    exact (h1 _ (HomLinear.isTangent_comp _ tv)).unique h₁ h₂
  by_contra h0
  refine hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have h := hadj a V W
  rw [key tv hV ev, key tw hW ew, H.bar_eq, IsCMField.complexEmbedding_complexConj] at h
  simp only [hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RCLike.star_def,
    Complex.conj_conj] at h h0
  exact mul_right_cancel₀ h0 h

theorem norm_rule_of_isMetricAt {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {x : Sp ℂ ⟶ Xo.X} {s : LB.Sec (PPx x)}
    {uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)} {N : ℝ}
    {φ : (E →+* ℂ) → (E →+* ℂ)} (hφ : Function.Injective φ) (tan : ∀ τ i, IsTanAt x (uu τ i))
    (eig : ∀ τ i (a : 𝓞 E), uu τ i ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (φ τ a)) ≫ uu τ i)
    (hB : TanBasis x fun j => uu (e j).1 (e j).2) (h : IsMetricAt x s uu N fun _ => 1) :
    ∃ Φ : FibKey Xo ℂ x, Tied e s uu Φ ∧ ‖(κ ℂ Φ.key : ℂ)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, ht, hA, hR, hF, hD, hN, h7, h8⟩ := h
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x Φ.T.t.G Φ.m.φ Φ.m.cart
  have hv : IsLieBasis fun j => w (e j).1 (e j).2 := (hb _ _).2 (by
    rw [show (fun j => (w (e j).1 (e j).2).left ≫ Φ.m.φ) = fun j => uu (e j).1 (e j).2 from
      funext fun j => (h7 _ _).1]
    exact hB)
  obtain rfl : Φ.T.g = g := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis Φ.T.t.act Φ.basis).indexEquiv (GlobalTheory.Serre.Lie.basis Φ.T.t.act hv))
  refine ⟨{ Φ with v := _, basis := hv }, ⟨ht, rfl, fun j => (h7 _ _).1⟩, ?_⟩
  have ht' : ∀ b i, IsTangent (w b i) := fun b i =>
    (GlobalTheory.MetricChange.lift_comb Φ.m.cart).1 _ ((h7 b i).1.symm ▸ tan b i)
  have he : ∀ b i (a : 𝓞 E), (w b i ≫ Φ.T.t.act.act a).left =
      spMap (epsMul (φ b a)) ≫ (w b i).left := fun b i a => by
    refine Φ.m.cart.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, Φ.m.act a, ← Category.assoc, Category.assoc (spMap _)]
      exact (congrArg (· ≫ _) (h7 b i).1).trans ((eig b i a).trans (congrArg (_ ≫ ·) (h7 b i).1.symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (spMap_epsScaleR_comp _).symm
  let W' : Matrix (Fin Φ.T.g) (Fin Φ.T.g) ℂ := Matrix.of fun j => W (e j).1 (e j).2
  have hG : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W' j) (W' i)) = 1 := by
    ext i j
    obtain ⟨⟨b, i⟩, rfl⟩ := e.symm.surjective i
    obtain ⟨⟨b', j⟩, rfl⟩ := e.symm.surjective j
    have hW : ∀ p, W' (e.symm p) = W p.1 p.2 := fun p => by
      show W (e (e.symm p)).1 (e (e.symm p)).2 = _
      rw [e.apply_symm_apply]
    rw [Matrix.of_apply, hW, hW]
    by_cases hbb : b' = b
    · subst hbb
      rw [← h8]
      simp [Matrix.one_apply]
    · have hne : φ b' ≠ φ b := fun h => hbb (hφ h)
      rw [hermForm_eq_zero Φ.T u hA hne (ht' _ _) (ht' _ _) (h7 _ _).2 (h7 _ _).2 (he _ _) (he _ _), mul_zero,
        Matrix.one_apply_ne fun h => hbb (congrArg Sigma.fst (e.symm.injective h)).symm]
  have hdet := TopDifferential.det_gram Hm W'
  rw [hG, Matrix.det_one, Complex.one_re] at hdet
  obtain ⟨Ef, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all Φ.T.pol _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hD
  have h1 : (1 : ℝ) = (volume Fd).toReal / (Real.pi ^ Φ.T.g * ‖W'.det‖ ^ 2) := by
    rw [eq_inv_of_mul_eq_one_left hvol, eq_inv_of_mul_eq_one_left hdet.symm]
    exact (div_self (inv_ne_zero (right_ne_zero_of_mul_eq_one hvol))).symm
  have key := hκ.2.2.2.2 (FibKey.key { Φ with v := _, basis := hv }) u Hm W' χ θ Fd N 1 hA hR hF (fun j => (h7 _ _).2) hD hN h1
  rw [one_pow, mul_one] at key
  exact key

theorem norm_rule_of_isMetric {κ : KeyRule} (hκ : IsKeyRule κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) {N : ℝ} (h : IsMetric y N fun _ => 1) :
    ∃ Φ : FibKey Xo ℂ y.x, Tied (S := ℂ) e y.s y.u Φ ∧ ‖(κ ℂ Φ.key : ℂ)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) :=
  norm_rule_of_isMetricAt hκ e (φ := fun b => σ.comp (embF c b))
    (fun _ _ h => RingHom.ext fun x => congrArg Subtype.val (σ.injective (RingHom.congr_fun h x))) y.tan y.eig
    ((GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c (CAt σ) y.x y.u g e y.tan y.eig).1 y.basis) h

end Key

section Places

open CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.FlatLine GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.KeyFourth
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyIntegralVal
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem arch_clause {κ : KeyRule} (hκ : IsKeyRule κ) (hr : 1 ≤ Dw.p + Dw.q) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {y₀ : FrPt Xo c c.F} {Φ₀ : FibKey Xo c.F y₀.x}
    (h₀ : Tied e y₀.s y₀.u Φ₀) {σ : c.F →+* ℂ} {N : ℝ} {X : Mats Dw ℂ} (h : ArchFr y₀ σ N X) :
    4 * ∑ τ, Real.log ‖(X τ).det‖ + Real.log ‖σ (κ c.F Φ₀.key : c.F)‖ + 4 * Real.log N =
      2 * g * Real.log (2 * Real.pi) := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId _ _) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  obtain ⟨Φ, hΦ, hn⟩ := norm_rule_of_isMetric hκ e y (h.2.2 z y hz hy)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ z.x, Tied (S := ℂ) e z.s z.u Ψ :=
    @exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra z hr
  have e1 : (κ ℂ Ψ.key : ℂ) = σ (κ c.F Φ₀.key : c.F) := hκ.2.1 c.F ℂ σ _ _
    (@tied_keyPB E _ _ _ H Dw l Xo c g e c.F ℂ _ _ _ _ σ.toAlgebra (Algebra.ofId c.F (CAt σ)) y₀ z Φ₀ Ψ hz h₀ hΨ)
  have e2 := @rule_frChg E _ _ _ H Dw l Xo c κ hκ g e ℂ _ _ σ.toAlgebra (fun τ => (X τ)ᵀ) 1 z y Ψ Φ hy hΨ hΦ
  simp only [one_pow, one_mul, Matrix.det_transpose] at e2
  replace hn : ‖(∏ τ, (X τ).det) ^ 4 * σ (κ c.F Φ₀.key : c.F)‖ * N ^ 4 = (2 * Real.pi) ^ (2 * g) :=
    (congrArg (fun t : ℂ => ‖t‖ * N ^ 4) (e2.trans (congrArg (_ * ·) e1))).symm.trans hn
  rw [norm_mul, norm_pow, norm_prod] at hn
  have p1 : ∀ τ ∈ (Finset.univ : Finset (E →+* ℂ)), ‖(X τ).det‖ ≠ 0 := fun τ _ => norm_ne_zero_iff.2 (h.2.1 τ)
  have p2 := pow_ne_zero 4 (Finset.prod_ne_zero_iff.2 p1)
  have p3 : ‖σ (κ c.F Φ₀.key : c.F)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero σ).2 (Units.ne_zero _))
  have e3 := congrArg Real.log hn
  rw [Real.log_mul (mul_ne_zero p2 p3) (pow_ne_zero 4 h.1.ne'), Real.log_mul p2 p3, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_prod p1] at e3
  push_cast at e3
  exact e3

theorem loc_clause {κ : KeyRule} (hκ : IsKeyRule κ) (hr : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {y₀ : FrPt Xo c c.F} {Φ₀ : FibKey Xo c.F y₀.x}
    (h₀ : Tied e y₀.s y₀.u Φ₀) {w : HeightOneSpectrum (𝓞 c.F)} {a : c.F} {B : Mats Dw c.F} (h : LocFr y₀ w a B) :
    4 * ∑ τ, (vAdd w (B τ).det : ℝ) + (vAdd w (κ c.F Φ₀.key : c.F) : ℝ) - 8 * (vAdd w a : ℝ) ≤
      4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  classical
  obtain ⟨T, io, ho, -, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F w
  letI := io.toAlgebra
  obtain ⟨y, z, hy, hz, hx⟩ := Model.exists_integral hr hg y₀ w T io 1 ho
  obtain ⟨Y, u₀, hY, hc⟩ := h.2.2 T io 1 ho y z hy hz hx
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io 1 ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det hκ hr hg e ho τ' hτ y hy
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ)
    inferInstance a1 a2 δ hδ
  have hb := (nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD).2
  rw [← hu, nval_of_ne (Units.ne_zero _), EReal.coe_le_coe_iff] at hb
  simp only [hδv, Int.cast_natCast, Nat.cast_one, div_one] at hb
  obtain ⟨Ψ, hΨ⟩ := exists_tied E H Dw l Xo c g e T.Fr z hr
  have e1 : (κ T.Fr Ψ.key : T.Fr) = io (κ c.F Φ₀.key : c.F) := hκ.2.1 c.F T.Fr io _ _
    (tied_keyPB E H Dw l Xo c g e c.F T.Fr (Algebra.ofId c.F T.Fr) y₀ z Φ₀ Ψ hz h₀ hΨ)
  have e2 := rule_frChg hκ e _ _ z y Ψ Φ hc hΨ hΦ
  simp only [Matrix.det_transpose, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e2
  have key : ∀ (s : c.F) (v : T.V), s ≠ 0 → IsUnit v → vV T.V (io s * algebraMap T.V T.Fr v) = vAdd w s := by
    intro s v hs hv
    rw [vV_mul ((map_ne_zero io).2 hs) (hv.map _).ne_zero, ho.2]
    simp [vV, valV_algebraMap_unit T hv, vLa, vAdd]
  have ne : ∀ (s : c.F) (v : T.V), s ≠ 0 → IsUnit v → io s * algebraMap T.V T.Fr v ≠ 0 := fun s v hs hv =>
    mul_ne_zero ((map_ne_zero io).2 hs) (hv.map _).ne_zero
  have pw : ∀ (a : T.Fr) (k : ℕ), vV T.V (a ^ k) = k * vV T.V a := fun a k => by simp [vV]
  have hp : ∀ s : Finset (E →+* ℂ), vV T.V (∏ τ ∈ s, io (B τ).det * algebraMap T.V T.Fr (Y τ).det) =
      ∑ τ ∈ s, vAdd w (B τ).det := fun s => by
    induction s using Finset.induction_on with
    | empty => simp [vV]
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ, vV_mul (ne _ _ (h.2.1 τ) (hY τ))
        (Finset.prod_ne_zero_iff.2 fun i _ => ne _ _ (h.2.1 i) (hY i)), ih, key _ _ (h.2.1 τ) (hY τ)]
  have e3 := congrArg (vV T.V) e2
  rw [vV_mul (pow_ne_zero _ (ne _ _ h.1 u₀.isUnit)) (Units.ne_zero _), vV_mul (pow_ne_zero _
    (Finset.prod_ne_zero_iff.2 fun i _ => ne _ _ (h.2.1 i) (hY i))) (Units.ne_zero _), pw, pw, hp,
    key _ _ h.1 u₀.isUnit, e1, ho.2] at e3
  have e4 : (8 : ℝ) * (vAdd w a : ℝ) + (vV T.V (κ T.Fr Φ.key : T.Fr) : ℝ) =
      4 * ∑ τ, (vAdd w (B τ).det : ℝ) + (vAdd w (κ c.F Φ₀.key : c.F) : ℝ) := by
    rw [Nat.cast_one, one_mul] at e3
    exact_mod_cast e3
  linarith

theorem lineDeg_le {K : Type} [Field K] [NumberField K] {J : Type} [Fintype J] {k : K} (hk : k ≠ 0)
    (a : HeightOneSpectrum (𝓞 K) → ℝ) (b o : J → HeightOneSpectrum (𝓞 K) → ℝ) (m : J → ℝ) (N : (K →+* ℂ) → ℝ)
    (x : J → (K →+* ℂ) → ℝ) (C L : ℝ) (hN : ∀ σ, 0 < N σ) (ha : (Function.support a).Finite)
    (hb : ∀ j, (Function.support (b j)).Finite) (ho : ∀ j, (Function.support (o j)).Finite)
    (hL : ∀ j, ∑ᶠ w, o j w * lw K w = L)
    (h₁ : ∀ σ, 4 * ∑ j, Real.log (x j σ) + Real.log ‖σ k‖ + 4 * Real.log (N σ) = C)
    (h₂ : ∀ w, 4 * ∑ j, b j w + (vAdd w k : ℝ) - 8 * a w ≤ 4 * ∑ j, m j * o j w) :
    (∑ j, lineDeg (x j) (b j)) / 2 + C / 8 - (∑ j, m j) * L / 2 ≤ lineDeg (fun σ => (Real.sqrt (N σ))⁻¹) a := by
  classical
  have hK : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have hS := (ha.union (finite_vAdd hk)).union ((Set.finite_iUnion hb).union (Set.finite_iUnion ho))
  have fs : ∀ f : HeightOneSpectrum (𝓞 K) → ℝ, Function.support f ⊆ hS.toFinset →
      ∑ᶠ w, f w * lw K w = ∑ w ∈ hS.toFinset, f w * lw K w := fun f hf =>
    finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_left _ _).trans hf)
  have s1 := fs a (by rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inl (Or.inl h))
  have s2 := fs (fun w => (vAdd w k : ℝ)) (by rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inl (Or.inr h))
  have s3 := fun j => fs (b j) (by
    rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inr (Or.inl (Set.mem_iUnion.2 ⟨j, h⟩)))
  have s4 := fun j => (hL j).symm.trans (fs (o j) (by
    rw [Set.Finite.coe_toFinset]; exact fun w h => Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, h⟩))))
  have h0 := lineDeg_num hk
  unfold lineDeg at h0 ⊢
  simp only [s1, s2, s3] at h0 ⊢
  generalize hS.toFinset = S at *
  have t1 : 4 * ∑ j, ∑ w ∈ S, b j w * lw K w + ∑ w ∈ S, (vAdd w k : ℝ) * lw K w - 8 * ∑ w ∈ S, a w * lw K w ≤
      4 * ((∑ j, m j) * L) := by
    have := Finset.sum_le_sum (s := S) fun w _ => mul_le_mul_of_nonneg_right (h₂ w)
      (show 0 ≤ lw K w from div_nonneg (Real.log_natCast_nonneg _) hK.le)
    simp only [sub_mul, add_mul, mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_mul] at this
    rw [Finset.sum_comm (s := S), Finset.sum_comm (s := S)] at this
    simp only [← Finset.mul_sum, ← s4] at this
    rwa [Finset.sum_mul]
  have t2 : 4 * ∑ j, (∑ σ, Real.log (x j σ)) / (Module.finrank ℚ K : ℝ) +
      (∑ σ : K →+* ℂ, Real.log ‖σ k‖) / (Module.finrank ℚ K : ℝ) +
      4 * ((∑ σ, Real.log (N σ)) / (Module.finrank ℚ K : ℝ)) = C := by
    have := Finset.sum_congr (s₁ := Finset.univ) rfl fun σ _ => h₁ σ
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Embeddings.card,
      nsmul_eq_mul] at this
    rw [Finset.sum_comm] at this
    rw [← Finset.sum_div]
    field_simp
    linarith
  have t3 : ∑ σ, Real.log (Real.sqrt (N σ))⁻¹ = -(1 / 2) * ∑ σ, Real.log (N σ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by rw [Real.log_inv, Real.log_sqrt (hN σ).le]; ring
  rw [t3, Finset.sum_sub_distrib, mul_div_assoc (-(1 / 2) : ℝ)]
  linarith

end Places

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∑ τ : Psi H, P.degLie τ.1) / 2 + ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) ≤ P.degTh := by
  intro E _ _ _ H Dw l Xo c r U ξ h Z P
  have hr : 1 ≤ Dw.p + Dw.q := h.p.trans (Nat.le_add_right _ _)
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.KeyFourth.exists_tied E H Dw l Xo c _ e c.F P.y₀ hr
  have key := lineDeg_le (κ c.F Φ₀.key).ne_zero (fun w => (vAdd w (P.a w) : ℝ))
    (fun τ w => (vAdd w (P.B w τ).det : ℝ))
    (fun τ w => (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.ord_vw w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.conjDifferent (embF c τ)) : ℝ)) (fun τ => (Dw.mult τ : ℝ)) P.N
    (fun τ σ => ‖(P.X σ τ).det‖) _ _ (fun σ => (P.arch σ).1)
    (P.fin.subset fun w hw h' => hw (by simp [h'.1, vAdd]))
    (fun τ => P.fin.subset fun w hw h' => hw (by simp [h'.2, vAdd]))
    (fun τ => finite_ord _) (fun τ => sum_ord _) (fun σ => arch_clause hκ hr e h₀ (P.arch σ))
    (fun w => loc_clause hκ hr h.good e h₀ (P.loc w))
  have hsub : ∀ f : (E →+* ℂ) → ℝ, (∀ τ, Dw.mult τ = 0 → f τ = 0) → ∑ τ, f τ = ∑ τ : Psi H, f τ.1 := fun f hf => by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0) f,
      Finset.sum_eq_zero (s := Finset.univ) (f := fun τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} => f τ.1)
        fun τ _ => hf _ (by rw [Datum.mult, if_neg τ.2, h.q]), add_zero]
    convert rfl
  have h1 : ∑ τ, (Dw.mult τ : ℝ) = (Fintype.card (Psi H) : ℝ) * Dw.p := by
    rw [hsub _ fun τ h => by rw [h, Nat.cast_zero],
      Finset.sum_congr rfl fun (τ : Psi H) _ => show (Dw.mult τ.1 : ℝ) = Dw.p by rw [Datum.mult, if_pos τ.2]]
    simp
  have h2 : (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : ℝ) = (Fintype.card (Psi H) : ℝ) * Dw.p := by
    rw [← h1]; simp [Fintype.card_sigma]
  have h3 : ∑ τ, P.degLie τ = ∑ τ : Psi H, P.degLie τ.1 := hsub _ fun τ h => by
    have : IsEmpty (Fin (Dw.mult τ)) := by rw [h]; infer_instance
    simp [PtData.degLie, detDeg, lineDeg, vAdd]
  rw [h1, h2] at key
  rw [← h3]
  change (∑ τ, P.degLie τ) / 2 + _ - _ ≤ P.degTh at key
  linarith

end GlobalTheory.DefPt.ThetaDeg

end
end

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∑ τ : Psi H, P.degLie τ.1) / 2 + ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) ≤ P.degTh := by
  atlas_forward_decl GlobalTheory.DefPt.ThetaDeg.main
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_action_preserves_adelic_matrices : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → IsAdelic fun w => fibA la (a w) (B w) := by
  first | exact @GlobalTheory.FibAdel.fibA_isAdelic | exact GlobalTheory.FibAdel.fibA_isAdelic | (intros; apply GlobalTheory.FibAdel.fibA_isAdelic <;> assumption)
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K), IsAdelic A → Submodule.IsLattice K (locLat A) := by
  first | exact @GlobalTheory.LocMatLat.isLattice_locLat | exact GlobalTheory.LocMatLat.isLattice_locLat | (intros; apply GlobalTheory.LocMatLat.isLattice_locLat <;> assumption)
end

section
section
noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefFibre

theorem vAdd_pow' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) :
    vAdd w (x ^ n) = n * vAdd w x := by
  simp [vAdd, map_pow, WithZero.log_pow]

theorem vAdd_one' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem subsingleton_idx : ∀ (N : ℕ) (la : Fin N → ℕ), N = 0 → Subsingleton (Idx la) := by
  rintro N la rfl
  constructor
  rintro ⟨m, -⟩ ⟨m', -⟩
  congr 1
  ext ⟨i, _⟩
  exact i.elim0

theorem dim_eq_one_of_zero {N : ℕ} (la : Fin N → ℕ) (hla : Antitone la) (h : N = 0) : dim la = 1 := by
  haveI := subsingleton_idx N la h
  have h1 := dim_pos hla
  have h2 : dim la ≤ 1 := by rw [dim_eq_card]; exact Fintype.card_le_one_iff_subsingleton.2 inferInstance
  omega

theorem fibreAt_defCase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ →
      ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n c₁ hD hDom hFl Z
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component E H Dw l Xo c r U ξ hD Z
  haveI hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hanti : ∀ τ, Antitone (part Dw a τ) := fun τ i j hij => hDom.1 τ (show (i : ℕ) ≤ j from hij)
  obtain ⟨φ, hinj, hrange, hreads⟩ := GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hconj, hint⟩ := GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hlie, -⟩ := GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree E H Dw l Xo c r U ξ hD Z P
  have hth := GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint E H Dw l Xo c r U ξ hD Z P
  have hIntOne : ∀ (w : HeightOneSpectrum (𝓞 c.F)) (m : ℕ), IntAt w (1 : Matrix (Fin m) (Fin m) c.F) :=
    fun w m i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hBad : ∀ τ, IsAdelic fun w => P.B w τ := fun τ => by
    refine ⟨fun w => (P.loc w).2.1 τ, P.fin.subset fun w hw h => hw ?_⟩
    show IntAt w (P.B w τ) ∧ IntAt w (P.B w τ)⁻¹
    have hB : P.B w τ = 1 := by rw [h.2]; rfl
    rw [hB, inv_one]
    exact ⟨hIntOne w _, hIntOne w _⟩
  have ha0 : ∀ w, P.a w ^ n ≠ 0 := fun w => pow_ne_zero _ (P.loc w).1
  have hsupp1 : (Function.support fun w => vAdd w (P.a w)).Finite :=
    P.fin.subset fun w hw h => hw (by simp only; rw [h.1, vAdd_one'])
  have hsupp : (Function.support fun w => vAdd w (P.a w ^ n)).Finite :=
    hsupp1.subset fun w hw h => hw (by simp only at h ⊢; rw [vAdd_pow', h, mul_zero])
  have hspos : ∀ σ, 0 < (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ =>
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (P.arch σ).1)) n
  have hsconj : ∀ σ, (Real.sqrt (P.N ((starRingEnd ℂ).comp σ)))⁻¹ ^ n = (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ => by
    rw [(hconj σ).1]
  obtain ⟨hdet, hslope⟩ := GlobalTheory.T.slope_dualWeylFibreLattice_ge c.F (E →+* ℂ) Dw.mult (part Dw a) hanti (fun w => P.a w ^ n) P.B
    (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) P.X ha0 hsupp hBad hspos (fun σ τ => (P.arch σ).2.1 τ) hsconj
    (fun σ τ => (hconj σ).2 τ)
  have hlat : IsAdelic fun w => fibA (part Dw a) (P.a w ^ n) (P.B w) :=
    GlobalTheory.T.fibre_action_preserves_adelic_matrices c.F (E →+* ℂ) Dw.mult (part Dw a) (fun w => P.a w ^ n) P.B ha0 hsupp hBad
  have hsec : ∀ x, φ x ∈ sec Xo c a n := fun x => by
    have h1 : φ x ∈ cuspOn U Z (wtZ a n) := hrange ▸ ⟨x, rfl⟩
    have h2 := cuspOn_le U Z (wtZ a n) h1
    rw [cuspW_wtZ] at h2
    exact cusp_le_sec Xo c U a n h2
  have hne : ∀ τ, Nonempty (Idx (part Dw a τ)) := fun τ =>
    Fintype.card_pos_iff.1 ((dim_eq_card _) ▸ dim_pos (hanti τ))

  have hline : lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) (fun w => (vAdd w (P.a w ^ n) : ℝ)) = n * P.degTh := by
    simp only [PtData.degTh, lineDeg, vAdd_pow', Int.cast_mul, Int.cast_natCast, Real.log_pow]
    have hf := fin_mul (ρ := fun w => (vAdd w (P.a w) : ℝ)) (hsupp1.subset fun w hw => by simpa [Function.mem_support] using hw) (lw c.F)
    simp only [mul_assoc]
    rw [← mul_finsum, ← Finset.mul_sum]
    ring

  have hterm : ∀ τ : E →+* ℂ, ¬ τ (H.rt : E) = H.rt0 →
      (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2 = 0 := fun τ hτ => by
    have hm : Dw.mult τ = 0 := by simp [Datum.mult, hτ, hD.q]
    have hm' : (Dw.mult τ : ℝ) = 0 := by rw [hm]; simp
    rw [dim_eq_one_of_zero _ (hanti τ) hm, hm', div_zero, zero_mul]
    simp
  have hpsi : ∀ τ : Psi H,
      (size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) * detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) -
        Real.log (dim (part Dw a τ.1)) / 2 =
      (size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2 := fun τ => by
    have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
    have hl : P.degLie τ.1 = c₁ := by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]
    have hm' : (Dw.mult τ.1 : ℝ) = Dw.p := by rw [hm]
    rw [hm', show detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) = P.degLie τ.1 from rfl, hl]
  have hsum := (Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
    (fun τ => (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2)).symm
  have h0 : ∑ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) = 0 :=
    Finset.sum_eq_zero fun τ _ => hterm τ.1 τ.2
  rw [h0, add_zero] at hsum
  have hsum' : ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) :=
    Finset.sum_congr rfl fun τ _ => hpsi τ
  have hlieSum : ∑ τ : Psi H, P.degLie τ.1 = (Fintype.card (Psi H) : ℝ) * c₁ := by
    rw [Finset.sum_congr rfl fun τ _ => (show P.degLie τ.1 = c₁ by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound : defBound Dw a n c₁ = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
      Real.log (dim (part Dw a τ.1)) / 2) + (Fintype.card (Psi H) : ℝ) * ((n : ℝ) / 2 * c₁) +
      (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) := by
    have hS : ∑ τ : Psi H, ((((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) + (n : ℝ) / 2) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2)) = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2) + ∑ _τ : Psi H, ((n : ℝ) / 2 * c₁) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [defBound, hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hth hn
  rw [hlieSum] at hmul
  refine ⟨TIdx (part Dw a), inferInstance, inferInstance, ⟨fun τ => (hne τ).some⟩, locLat (P.matA a n), P.matY a n, φ,
    GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily c.F _ (P.matA a n) hlat, hdet, ?_, hinj, hrange, fun x hx w v hv =>
      (hint x (φ x) (hsec x) (hreads x)).1 hx w v hv, fun σ x z hz => (hint x (φ x) (hsec x) (hreads x)).2 σ z hz⟩
  refine le_trans ?_ hslope
  have htot : ∑ t : E →+* ℂ, ((size (part Dw a t) : ℝ) / (Dw.mult t : ℝ) *
      detDeg (fun w => P.B w t) (fun σ => P.X σ t) - Real.log (dim (part Dw a t)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) := by
    rw [hsum]
    convert hsum' using 3
  rw [hline, htot, hbound]
  nlinarith [hmul]

end GlobalTheory.DefFibre
end
end

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteCase_cuspForm_fibre_slope_ge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ → ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  atlas_forward_decl GlobalTheory.DefFibre.fibreAt_defCase
end
