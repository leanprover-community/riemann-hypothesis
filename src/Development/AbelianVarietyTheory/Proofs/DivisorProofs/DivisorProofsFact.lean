import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFifth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLocalConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_generated_prime_to_l : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (l : ℕ) [Fact l.Prime],
    ∃ c₀ : 𝔠.elt, (c₀ : F) ≠ 0 ∧ ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀ := by
  first | exact @GlobalTheory.FracGen.exists_gen | exact GlobalTheory.FracGen.exists_gen | (intros; apply GlobalTheory.FracGen.exists_gen <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_exists_for_cm_object : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A),
      GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ ∧ IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ((2 : R) • ψ) := by
  first | exact @GlobalTheory.PolPairing.exists_isCorrForm_diag | exact GlobalTheory.PolPairing.exists_isCorrForm_diag | (intros; apply GlobalTheory.PolPairing.exists_isCorrForm_diag <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_rank_eq_finrank_cm : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E)) (R : Type)
    [CommRing R] [IsDomain R] (X : Obj (FR E) 𝔠 (Sp R)) (n : ℕ), (HdR X.A ≃ₗ[R] (Fin n → R)) → n = Module.finrank ℚ E := by
  intro H E _ _ _ 𝔠 R _ _ X n e
  letI := X.grp
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  let e1 : Module.Dual R (primDR X.A) ≃ₗ[R] (Fin n → R) := e
  let e2 : primDR X.A ≃ₗ[R] Module.Dual R (Fin n → R) :=
    (Module.evalEquiv R (primDR X.A)).trans e1.symm.dualMap
  have hP : ∀ p : PrimeSpectrum R, Module.rankAtStalk (primDR X.A) p = n := by
    intro p
    rw [Module.rankAtStalk_eq_of_equiv e2, Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_eq_card_basis (Pi.basisFun R (Fin n)).dualBasis, Fintype.card_fin]
    rfl
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have h1 := hrk p
  rw [hP p] at h1
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  rw [h1, ← h3, mul_comm]

end GlobalTheory.DeRham
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_rank_eq_cm_degree : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E)) (R : Type)
    [CommRing R] [IsDomain R] (X : Obj (FR E) 𝔠 (Sp R)) (n : ℕ), (HdR X.A ≃ₗ[R] (Fin n → R)) → n = Module.finrank ℚ E := by
  atlas_forward_decl GlobalTheory.DeRham.hdR_rank_eq_finrank_cm
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

theorem perfect_of_primeTo (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal)
    (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hunit : ∀ n : ℕ, n.Coprime l → IsUnit (n : R)) (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt) (hc₀ : (c₀ : F) ≠ 0)
    (hgen : ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀)
    (ψ : LinearMap.BilinForm R (HdR X.A)) (hψ : GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ) :
    Function.Bijective ψ := by
  obtain ⟨m, hm0, hml, hm⟩ := exists_uniform 𝔠 l c₀ hgen

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp R) X.A X.ab
  have hBg := hBg _ X.dim
  haveI : IsCommMonObj B := hB.comm

  obtain ⟨c₁, hc₁⟩ := exists_totPos 𝔠 c₀ hc₀
  have hL := pull_isLB (X.isLB c₁) (lift (𝟙 X.A) (𝟙 X.A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod X.ab X.ab hL (X.pos c₁ hc₁) hL (X.pos c₁ hc₁)
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv X.ab X.ab hH hamp (X.isLB c₀) (X.rig₁ c₀) (X.rig₂ c₀)
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive (X.isLB c₀) a₁ a₂

  have hker : ∀ (T : Over (Sp R)) (x : T ⟶ X.A), x ≫ lam = 1 → x ^ m = 1 := by
    intro T x hx
    have tr : Triv (ev (X.P c₀) (fst X.A T) (snd X.A T ≫ x)) := by
      rw [triv_ev_iff (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.assoc, hx,
        comp_one]
      exact evc_one_right hd.isLB hd.zero _
    have k := X.ker c₀ T x tr (m : 𝓞 F) hm
    rw [act_natCast, comp_pow, Category.comp_id] at k
    exact k
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse R X.A B _ X.ab hB X.dim hBg lam hlam m hm0 hker
  have hpush := bijective_push (dp0 R) (𝟙 _) lam μ' m (hunit m hml) e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR X.ab X.dim hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  have e : LBIso (ev Q (fst X.A X.A) (snd X.A X.A ≫ lam)) (ev (X.P c₀) (fst X.A X.A ≫ 𝟙 X.A) (snd X.A X.A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB (X.isLB c₀) _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev (X.isLB c₀), GlobalTheory.BirigidLift.evc_of_cls hd.isLB (X.isLB c₀) hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 R) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB (X.isLB c₀) hφ hψ (𝟙 X.A) lam e x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.PolPrimeTo
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_over_dvr_prime_to_l : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
    (∀ n : ℕ, n.Coprime l → IsUnit (n : R)) → ∀ (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt), (c₀ : F) ≠ 0 →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀) →
    ∀ ψ : LinearMap.BilinForm R (HdR X.A), GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ → Function.Bijective ψ := by
  atlas_forward_decl GlobalTheory.PolPrimeTo.perfect_of_primeTo
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
namespace GlobalTheory.ConductorMult

theorem exists_natMul_mem_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  intro E _ _ _ c hc x
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
  have hyx : IsIntegral ℤ ((y : E) * x) := by
    have := hy x (Finset.mem_singleton_self x)
    simpa [zsmul_eq_mul] using this
  have hyx' : IsIntegral ℤ ((y.natAbs : E) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℕ) : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]
      exact hyx
    · have h' : (y.natAbs : ℤ) = -y := by omega
      have : ((y.natAbs : ℕ) : E) = -(y : E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]
      exact hyx.neg
  set z : 𝓞 E := ⟨(y.natAbs : E) * x, hyx'⟩ with hz
  have hN : Ideal.absNorm c ≠ 0 := mt Ideal.absNorm_eq_zero_iff.1 hc
  have hyn : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  refine ⟨Ideal.absNorm c * y.natAbs, Nat.mul_ne_zero hN hyn, ?_⟩
  have h := GlobalTheory.EigenPair.natMul_mem_orderC c z
  have hzE : ((z : 𝓞 E) : E) = (y.natAbs : E) * x := rfl
  rw [hzE] at h
  rw [Nat.cast_mul, _root_.mul_assoc]
  exact h

end GlobalTheory.ConductorMult
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominator_in_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  atlas_forward_decl GlobalTheory.ConductorMult.exists_natMul_mem_orderC
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
noncomputable section

namespace GlobalTheory.CommonEigField

open Module

theorem finrank_common_eig_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} {O : Type}
    (A : O → Matrix (Fin n) (Fin n) K) (m0 : O → K) :
    finrank K (⨅ a, LinearMap.ker (Matrix.toLin' (A a) - m0 a • LinearMap.id) : Submodule K (Fin n → K)) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' ((A a).map f) - f (m0 a) • LinearMap.id) :
        Submodule L (Fin n → L)) := by
  letI := f.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 f.injective
  refine ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := K) (k := L) (fun a => Matrix.toLin' (A a))
    (fun a => Matrix.toLin' ((A a).map f)) (fun a c => ?_) m0
  funext i
  simp only [Matrix.toLin'_apply, Function.comp_apply]
  exact (RingHom.map_mulVec f (A a) c i).symm

theorem finrank_eigK_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {n : ℕ}
    (ρ : orderC c →+* Module.End R (Fin n → R)) (σ : E →+* K) :
    finrank K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      finrank K (⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) : Submodule K (Fin n → K)) := by
  classical
  let e := TensorProduct.piScalarRight R K K (Fin n)
  have hint : ∀ (a : orderC c) (y : K ⊗[R] (Fin n → R)),
      e ((ρ a).baseChange K y) = Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K)) (e y) := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x v =>
      funext i
      simp only [LinearMap.baseChange_tmul, e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Matrix.toLin'_apply]
      rw [← LinearMap.toMatrix'_mulVec (ρ a) v]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hmap : Submodule.map (e : K ⊗[R] (Fin n → R) →ₗ[K] (Fin n → K)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      ⨅ a : orderC c, LinearMap.ker (Matrix.toLin' ((LinearMap.toMatrix' (ρ a)).map (algebraMap R K))
        - σ a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

theorem finrank_common_eig_basis {L : Type} [Field L] {W : Type*} [AddCommGroup W] [Module L W] {n : ℕ}
    (B : Module.Basis (Fin n) L W) {O : Type} (T : O → Module.End L W) (C : O → Matrix (Fin n) (Fin n) L)
    (hT : ∀ a i, T a (B i) = ∑ k, C a k i • B k) (m0 : O → L) :
    finrank L (⨅ a, Module.End.eigenspace (T a) (m0 a) : Submodule L W) =
      finrank L (⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) : Submodule L (Fin n → L)) := by
  classical
  let e := B.equivFun
  have hint : ∀ a (w : W), e (T a w) = Matrix.toLin' (C a) (e w) := by
    intro a
    have h : T a = (e.symm.toLinearMap ∘ₗ Matrix.toLin' (C a)) ∘ₗ e.toLinearMap := by
      refine B.ext fun i => ?_
      rw [hT]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Module.Basis.equivFun_apply,
        Module.Basis.repr_self, Finsupp.single_eq_pi_single, Matrix.toLin'_apply, Matrix.mulVec_single_one,
        Module.Basis.equivFun_symm_apply, Matrix.col_apply]
    intro w
    rw [h]
    simp
  have hmap : Submodule.map (e : W →ₗ[L] (Fin n → L)) (⨅ a, Module.End.eigenspace (T a) (m0 a)) =
      ⨅ a, LinearMap.ker (Matrix.toLin' (C a) - m0 a • LinearMap.id) := by
    ext x
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← e.injective.eq_iff, hint, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
  rw [← e.finrank_map_eq, hmap]

end GlobalTheory.CommonEigField

namespace GlobalTheory

open Module

theorem finrank_eigK_eq_finrank_eig_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E))
    (R : Subring ℂ) (n : ℕ)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (B : Module.Basis (Fin n) ℂ W) (T : orderC c → Module.End ℂ W),
    (∀ a i, T a (B i) = ∑ k, ((ρ a (Pi.single i 1) k : R) : ℂ) • B k) →
    ∀ σ : E →+* FractionRing R, Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank ℂ (⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ a)) : Submodule ℂ W) := by
  intro E _ _ _ c R n ρ j hj W _ _ B T hT σ
  rw [CommonEigField.finrank_eigK_eq, CommonEigField.finrank_common_eig_map j,
    CommonEigField.finrank_common_eig_basis B T
      (fun a => ((LinearMap.toMatrix' (ρ a)).map (algebraMap R (FractionRing R))).map j) ?_]
  intro a i
  rw [hT]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply, hj]

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_action_matrix_eigenvalues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Subring ℂ) (n : ℕ)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (B : Module.Basis (Fin n) ℂ W) (T : orderC c → Module.End ℂ W),
    (∀ a i, T a (B i) = ∑ k, ((ρ a (Pi.single i 1) k : R) : ℂ) • B k) →
    ∀ σ : E →+* FractionRing R, Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank ℂ (⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ a)) : Submodule ℂ W) := by
  atlas_forward_decl GlobalTheory.finrank_eigK_eq_finrank_eig_complex
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

theorem exists_basis_push_eq_sum : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  intro hAb E _ _ _ c 𝔠 R X₀ X p cm hpull n eH
  have h : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  have hm : (GlobalTheory.Published.AbelianDeRham.bcMor h).IsBC := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p h).1
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hAb.1 X₀.ab X₀.dim
  let b : Module.Basis (Fin n) R (HdR X₀.A) := Module.Basis.ofEquivFun eH
  let cb : Module.Basis (Fin n) R (primDR X₀.A) :=
    b.dualBasis.map (Module.evalEquiv R (primDR X₀.A)).symm
  have hcb : ∀ i j, b i (cb j) = if j = i then 1 else 0 := by
    intro i j
    simp [cb, Finsupp.single_apply, eq_comm]
  let L : ℂ ⊗[R] primDR X₀.A ≃ₗ[ℂ] primDR X.A := LinearEquiv.ofBijective _ hm
  let c' : Module.Basis (Fin n) ℂ (primDR X.A) := (Algebra.TensorProduct.basis ℂ cb).map L
  have hc' : ∀ j, c' j = (GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j) := fun j ↦ by
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact one_smul ℂ ((GlobalTheory.Published.AbelianDeRham.bcMor h).pull (cb j))
  let B := c'.dualBasis
  have hB : ∀ i, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (b i) (B i) := by
    intro i x
    rw [← cb.sum_repr x]
    simp only [map_sum, map_smulₛₗ, ← hc', B, Module.Basis.dualBasis_apply_self, hcb, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp
  have hb : ∀ i, b i = eH.symm (Pi.single i 1) := fun i ↦ by simp [b]
  have hsum : ∀ v : Fin n → R, (GlobalTheory.Published.AbelianDeRham.bcMor h).Corr (∑ k, v k • b k)
      (∑ k, ((v k : R) : ℂ) • B k) := by
    intro v x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hB _, map_sum, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hB k x]
    rfl
  refine ⟨B, fun a α _ hα i ↦ ?_⟩
  haveI := cm.hom a
  have e1 := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor h) (cm.act a) α hα.symm (hB i)
  set v := (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) with hv
  have e2 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = ∑ k, v k • b k := by
    have e3 : push (dp0 R) (𝟙 _) (cm.act a) (b i) = eH.symm v := by
      show act (dp0 R) (𝟙 _) cm a (b i) = _
      rw [hv, hb i]
      simp
    rw [e3, ← b.sum_equivFun (eH.symm v)]
    simp [b]
  rw [e2] at e1
  exact hm.unique e1 (hsum v)

end GlobalTheory.DRLine
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_basis_base_change : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  atlas_forward_decl GlobalTheory.DRLine.exists_basis_push_eq_sum
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

theorem eigK_finrank_eq_one : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (σ : E →+* FractionRing R),
      Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ) = 1 := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcmF hα j hj φK hφK n eH σ
  classical
  choose α hαM hαp hαU using hα
  let T : orderC (condQ 𝔣 Q) → Module.End ℂ (HdR X.A) := fun a ↦ haveI := hαM a; push (dp0 ℂ) (𝟙 _) (α a)
  obtain ⟨B, hB⟩ := GlobalTheory.T.de_rham_basis_base_change hDR E (condQ 𝔣 Q) 𝔠 R X₀ X p cm hpull n eH
  have hTB : ∀ a i, T a (B i) = ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k :=
    fun a i ↦ by haveI := hαM a; exact hB a (α a) (hαp a) i
  rw [GlobalTheory.T.order_action_matrix_eigenvalues E (condQ 𝔣 Q) R n _ j hj (HdR X.A) B T hTB σ]
  obtain ⟨ε, hε⟩ := hPC
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (X.isLB U.c) _
  obtain ⟨P, hspan, hrank, -, hpush, -⟩ := hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) hLB U.u

  have hmem : ∀ x : E, x ∈ lattice (condQ 𝔣 Q) y ↔ algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO (condQ 𝔣 Q) := fun x ↦ Iff.rfl
  let L : AddSubgroup E :=
    { carrier := lattice (condQ 𝔣 Q) y
      add_mem' := fun {a b} ha hb ↦ by
        show a + b ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_add, add_mul]; exact Subring.add_mem _ ((hmem a).1 ha) ((hmem b).1 hb)
      zero_mem' := by
        show (0 : E) ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_zero, zero_mul]; exact Subring.zero_mem _
      neg_mem' := fun {a} ha ↦ by
        show -a ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_neg, neg_mul]; exact Subring.neg_mem _ ((hmem a).1 ha) }
  have hLs : ∀ a ∈ orderC (condQ 𝔣 Q), ∀ x ∈ L, a * x ∈ L := fun a ha x hx ↦ by
    show a * x ∈ lattice (condQ 𝔣 Q) y
    rw [hmem, map_mul, _root_.mul_assoc]
    refine Subring.mul_mem _ ?_ ((hmem x).1 hx)
    exact Subring.le_topologicalClosure _ ⟨a, ha, rfl⟩
  let Φ : E → (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun x j ↦ φ (U.e j) x
  have hΦ : ∀ x ∈ L, Φ x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, by funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  let P' : L →+ HdR X.A :=
    { toFun := fun x ↦ P ⟨Φ x, hΦ x x.2⟩
      map_zero' := by
        have : (⟨Φ ((0 : L) : E), hΦ _ (0 : L).2⟩ : U.u.Λ) = 0 := Subtype.ext (by funext j; simp [Φ])
        rw [this, map_zero]
      map_add' := fun x x' ↦ by
        have : (⟨Φ ((x + x' : L) : E), hΦ _ (x + x').2⟩ : U.u.Λ) = ⟨Φ x, hΦ x x.2⟩ + ⟨Φ x', hΦ x' x'.2⟩ :=
          Subtype.ext (by funext j; simp [Φ])
        rw [this, map_add] }
  have hspan' : Submodule.span ℂ (Set.range P') = ⊤ := by
    rw [← hspan]; congr 1
    ext v; constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨x, hx, hw⟩ := (U.lat w).1 w.2
      refine ⟨⟨x, hx⟩, ?_⟩
      show P _ = P w
      congr 1; apply Subtype.ext; rw [hw]; funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have hT : ∀ (a : orderC (condQ 𝔣 Q)) (x x' : L), (x' : E) = a * x → T a (P' x) = P' x' := by
    intro a x x' hx'
    haveI := hαM a
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j ↦ φ (U.e j) (a : E) * w j
        map_add' := fun w w' ↦ by funext j; simp [mul_add]
        map_smul' := fun r w ↦ by funext j; simp; ring }
    exact hpush (α a) M (fun w ↦ hαU a w) _ _ (by funext j; simp [M, Φ, hx', map_mul])
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero h𝔣.1 ?_
    rw [Finset.prod_ne_zero_iff]
    exact fun q _ ↦ q.ne_bot
  exact GlobalTheory.T.cm_representation_eigen_decomposition E (orderC (condQ 𝔣 Q)) (GlobalTheory.T.bounded_denominator_in_order E _ hc0) L hLs (HdR X.A) P' hspan' hdim T hT (j.comp σ)

end GlobalTheory.DRLine
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_galois_descent : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (σ : E →+* FractionRing R),
      Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ) = 1 := by
  atlas_forward_decl GlobalTheory.DRLine.eigK_finrank_eq_one
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMAdjoint

theorem adjoint_of_holUnif (hP : GlobalTheory.Published.PeriodComparison) {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) (u : HolUnif A L g) (h : Fin g → ℝ)
    {χ : u.Λ → ℂ} (hah : u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ) {ψ : LinearMap.BilinForm ℂ (HdR A)}
    (hψ : IsPolForm (dp0 ℂ) (𝟙 _) A L ψ) (α β : A ⟶ A) [IsMonHom α] [IsMonHom β] (m m' : Fin g → ℂ)
    (hm : ∀ j, m' j = starRingEnd ℂ (m j))
    (hα : ∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) (hβ : ∀ w, u.ex (fun j ↦ m' j * w j) = u.ex w ≫ β) (x y : HdR A) :
    ψ (push (dp0 ℂ) (𝟙 _) α x) y = ψ x (push (dp0 ℂ) (𝟙 _) β y) := by
  obtain ⟨ε, hP⟩ := hP
  obtain ⟨P, hspan, -, -, hnat, hform⟩ := hP A g hA hg L hL u
  have key : ∀ (δ : A ⟶ A) [IsMonHom δ] (n : Fin g → ℂ), (∀ w, u.ex (fun j ↦ n j * w j) = u.ex w ≫ δ) → ∀ z : u.Λ,
      ∃ z' : u.Λ, (z' : Fin g → ℂ) = (fun j ↦ n j * z.1 j) ∧ push (dp0 ℂ) (𝟙 _) δ (P z) = P z' := by
    intro δ _ n hδ z
    have hz : (fun j ↦ n j * z.1 j) ∈ u.Λ := by
      rw [← u.ker, hδ, (u.ker _).2 z.2, MonObj.one_comp]
    exact ⟨⟨_, hz⟩, rfl, hnat δ (LinearMap.mulLeft ℂ n) hδ z _ rfl⟩
  have e : ψ ∘ₗ push (dp0 ℂ) (𝟙 _) α = ψ.compl₂ (push (dp0 ℂ) (𝟙 _) β) := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨z, rfl⟩
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨w, rfl⟩
    obtain ⟨z', hz', ez⟩ := key α m hα z
    obtain ⟨w', hw', ew⟩ := key β m' hβ w
    rw [LinearMap.comp_apply, LinearMap.compl₂_apply, ez, ew, hform _ χ ψ hah hψ, hform _ χ ψ hah hψ, hz', hw']
    congr 3
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hm, RCLike.star_def, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  exact LinearMap.congr_fun₂ e x y

theorem exists_polForm_pull {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem ne_zero_of_isTotPos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x : F} (h : IsTotPos x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using h (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

theorem adjoint_of_scale {R O M : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing O] [AddCommGroup M] [Module R M]
    (ρ : O →+* Module.End R M) {ψ ψ₀ : LinearMap.BilinForm R M} {n : ℕ} (hn : n ≠ 0) {t a b : O}
    (ht : ∀ x z, (n : R) * ((2 : R) • ψ₀) x z = ψ x (ρ t z)) (adj : ∀ x z, ψ (ρ a x) z = ψ x (ρ b z)) (x z : M) :
    ψ₀ (ρ a x) z = ψ₀ x (ρ b z) := by
  have e := adj x (ρ t z)
  rw [← Module.End.mul_apply (ρ b), ← map_mul, mul_comm b, map_mul, Module.End.mul_apply, ← ht, ← ht] at e
  have e2 := mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) e
  simp only [LinearMap.smul_apply, smul_eq_mul] at e2
  exact mul_left_cancel₀ two_ne_zero e2

theorem half_form_adjoint : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      ∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h') := by
  intro hP hD _ E _ _ _ _ I _ d φ _ 𝔣 _ l _ Q _ _ y _ lam 𝔠 R _ _ X₀ X U p cm hX hF hcm _ _ _ _ c₀ ψ₀ _ hψ₀ a b hab h h'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.PureLift.exists_isPolForm hD.1 X₀.ab X₀.dim (L := X₀.diag U.c) (pull_isLB (X₀.isLB U.c) _)
  letI : Algebra R ℂ := R.subtype.toAlgebra
  have m := GlobalTheory.Published.AbelianDeRham.bcMor (R := R) (R' := ℂ) hX.grp
  have hBC : m.IsBC := (hD.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hX.grp).1
  obtain ⟨ψ', hψ', hc⟩ := exists_polForm_pull R.subtype hX m U.c hψ
  obtain ⟨χ, hχ⟩ := U.ah
  obtain ⟨α, _, eα, hα⟩ := hcm a
  obtain ⟨β, _, eβ, hβ⟩ := hcm b
  haveI := cm.hom
  have adj : ∀ x z : HdR X₀.A, ψ (act (dp0 R) (𝟙 _) cm a x) z = ψ x (act (dp0 R) (𝟙 _) cm b z) := by
    intro x z
    obtain ⟨x', hx⟩ := hBC.exists x
    obtain ⟨z', hz⟩ := hBC.exists z
    refine R.subtype_injective ?_
    rw [act_apply, act_apply, ← hc _ _ _ _ (hx.push m (cm.act a) α eα.symm) hz,
      ← hc _ _ _ _ hx (hz.push m (cm.act b) β eβ.symm)]
    exact adjoint_of_holUnif hP X.ab X.dim (pull_isLB (X.isLB U.c) _) U.u (fun j ↦ U.h (U.e j)) hχ hψ' α β _ _
      (fun j ↦ by rw [hab, IsCMField.complexEmbedding_complexConj]) hα hβ x' z'
  obtain ⟨n, t, hn, ht⟩ := GlobalTheory.T.polarization_forms_commensurable hD _ 𝔠 R X₀ c₀ U.c (ne_zero_of_isTotPos U.pos) _ ψ hψ₀ hψ
  have et : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) t) := by
    haveI := X₀.rm.hom
    rw [act_apply, act_apply]
    exact push_congr _ _ (hF t).symm
  exact adjoint_of_scale (act (dp0 R) (𝟙 _) cm) hn (fun x z ↦ (ht x z).trans (congrArg (fun T ↦ ψ x (T z)) et)) adj h h'

end GlobalTheory.CMAdjoint
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_level_structure : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      ∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h') := by
  atlas_forward_decl GlobalTheory.CMAdjoint.half_form_adjoint
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_reduction_good : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
      (c₀ : FR E) ≠ 0 → IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) → Function.Bijective ψ₀ →
      (∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h')) →
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  first | exact @GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul | exact GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul | (intros; apply GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

noncomputable section

namespace GlobalTheory.LatModel

theorem cmLattice_of_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 ∧
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) ∧
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) ∧
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  intro hPC hDR hDC hPM E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH
  obtain ⟨c₀, hc₀, hgen⟩ := GlobalTheory.T.fractional_ideal_generated_prime_to_l (FR E) 𝔠 l
  obtain ⟨ψ₀, hcorr, hpol⟩ := GlobalTheory.T.polarization_form_exists_for_cm_object hDR (FR E) 𝔠 R X₀ c₀
  have hunit : ∀ m : ℕ, m.Coprime l → IsUnit (m : R) := by
    intro m hm
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by
        rintro rfl
        exact (Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left l |>.mp hm)
      exact_mod_cast this
    have hv : 0 ≤ padicValRat l ((m : ℚ)⁻¹) := by
      rw [padicValRat.inv, padicValRat.of_nat]
      have : padicValNat l m = 0 :=
        padicValNat.eq_zero_of_not_dvd fun h ↦ (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hm.symm h
      simp [this]
    have hmem := hR.2.2.1 ((m : ℚ)⁻¹) hv
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    have : ((m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm0
    simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one]
    rw [Rat.cast_inv, Rat.cast_natCast] at *
    exact mul_inv_cancel₀ (by simpa using this)
  have hbij : Function.Bijective ψ₀ := GlobalTheory.T.polarization_form_over_dvr_prime_to_l hDR hDC (FR E) 𝔠 l R hunit X₀ c₀ hc₀ hgen ψ₀ hcorr
  have hadj := GlobalTheory.T.cm_auxiliary_set_level_structure hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK c₀ ψ₀ hc₀ hpol
  have hFil := GlobalTheory.T.cm_auxiliary_set_local_conditions hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK n eH
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  refine ⟨c₀, ψ₀, hc₀, hgen, hpol, ⟨inferInstance, inferInstance, ?_,
    GlobalTheory.T.cm_auxiliary_set_galois_descent hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK n eH, ?_, hFil, ?_, ?_, ?_⟩,
    GlobalTheory.T.cm_auxiliary_set_reduction_good hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK e a he hL n eH c₀ ψ₀
      hc₀ hpol hbij hadj hFil⟩
  · rw [Module.finrank_fin_fun]
    exact GlobalTheory.T.de_rham_rank_eq_cm_degree hDR E 𝔠 R X₀ n eH
  · intro x h hx hxh
    obtain ⟨k, hk, hkh⟩ := Submodule.mem_map.1 hxh
    refine Submodule.mem_map.2 ⟨eH.symm h, ?_, by simp⟩
    have hk' : k = x • eH.symm h := by
      apply eH.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact hkh
    subst hk'
    rw [Fil, Submodule.mem_dualAnnihilator] at hk ⊢
    intro w hw
    have := hk w hw
    rw [LinearMap.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hx
  · have : ⇑(ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) =
        ⇑eH.symm.dualMap ∘ ⇑ψ₀ ∘ ⇑eH.symm := by
      funext x
      rfl
    rw [this]
    exact eH.symm.dualMap.bijective.comp (hbij.comp eH.symm.bijective)
  · intro x
    have := hpol.isAlt (eH.symm x)
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · intro a' b' hab h h'
    show ψ₀ (eH.symm (eH (act (dp0 R) (𝟙 _) cm a' (eH.symm h)))) (eH.symm h') =
      ψ₀ (eH.symm h) (eH.symm (eH (act (dp0 R) (𝟙 _) cm b' (eH.symm h'))))
    rw [eH.symm_apply_apply, eH.symm_apply_apply]
    exact hadj a' b' hab (eH.symm h) (eH.symm h')

end GlobalTheory.LatModel
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorProofs_fact : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 ∧
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) ∧
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) ∧
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  atlas_forward_decl GlobalTheory.LatModel.cmLattice_of_model
end
