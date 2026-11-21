import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonNorm_eq_of_levelCover_pullback : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f : cuspW Xo c U (wtZ a n)) (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)), Pull d (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) → ∀ σ₂ : d.c₂.F →+* ℂ, normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ g = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp (d.eF : c.F →+* d.c₂.F)) f := by
  first | exact @GlobalTheory.LevPullNorm.levPull_normW | exact GlobalTheory.LevPullNorm.levPull_normW | (intros; apply GlobalTheory.LevPullNorm.levPull_normW <;> assumption)
end

section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GeomPointLift

theorem nonempty_algHom_of_isAlgClosed (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (C ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ M)
  exact ⟨(IsAlgClosed.lift : (C ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hft : Algebra.FiniteType A B) (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  letI : Algebra A k := φ.toAlgebra
  haveI : Nontrivial (k ⊗[A] B) := Module.FaithfullyFlat.rTensor_nontrivial A B k
  haveI : Algebra.FiniteType k (k ⊗[A] B) := inferInstance
  obtain ⟨f⟩ := nonempty_algHom_of_isAlgClosed k (k ⊗[A] B)
  refine ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A k (k ⊗[A] B), AlgHom.commutes]
  rfl

end GlobalTheory.GeomPointLift

example : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := GlobalTheory.GeomPointLift.exists_lift
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  first | exact @GlobalTheory.GeomPointLift.exists_lift | exact GlobalTheory.GeomPointLift.exists_lift | (intros; apply GlobalTheory.GeomPointLift.exists_lift <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleGeomDescent

open scoped TensorProduct

theorem eq_of_geometric_points' {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rwa [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this

theorem descent : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ _ hff het b hb
  have hBr : _root_.IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced A B
  have : Algebra.Smooth B (B ⊗[A] B) := inferInstance
  have hCr : _root_.IsReduced (B ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B (B ⊗[A] B)
  have hC : (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b := by
    refine eq_of_geometric_points' _ _ fun k _ _ χ => ?_
    have key := hb k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom) ?_
    · simpa using key
    · ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hx := (Algebra.IsEffective.of_faithfullyFlat A B b).mp (by simp [hC])
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha⟩

end GlobalTheory.EtaleGeomDescent
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  atlas_forward_decl GlobalTheory.EtaleGeomDescent.descent
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem exists_lift_finiteEtale_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  intro Y Z π hfin het hsurj K _ p x
  let P := pullback π x
  let f : P ⟶ Sp p.R := pullback.snd π x
  have : IsFinite f := inferInstance
  have : Etale f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine P := isAffine_of_isAffineHom f
  let g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R) := P.isoSpec.inv ≫ f
  let φ : CommRingCat.of p.R ⟶ Γ(P, ⊤) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hg_et : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hg_surj : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hφet : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et
  have hφff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩
  letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra
  have hBet : Algebra.Etale p.R Γ(P, ⊤) := hφet
  have hBff : Module.FaithfullyFlat p.R Γ(P, ⊤) := hφff
  have hpred : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hBred : _root_.IsReduced Γ(P, ⊤) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)
  letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra
  haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType K Γ(P, ⊤))
  have hrad : (RingHom.ker s).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))
  let q : TRing K := ⟨n, RingHom.ker s, hrad⟩
  let e : q.R ≃ₐ[K] Γ(P, ⊤) := Ideal.quotientKerAlgEquivOfSurjective hs
  let φK : p.R →ₐ[K] Γ(P, ⊤) := { φ.hom with commutes' := fun _ => rfl }
  let ι : p.R →ₐ[K] q.R := e.symm.toAlgHom.comp φK
  refine ⟨q, ι, ?_, ?_⟩
  · letI := ι.toRingHom.toAlgebra
    let e' : Γ(P, ⊤) ≃ₐ[p.R] q.R := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)
    exact ⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩
  · refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩
    have hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom := rfl
    rw [Category.assoc, Category.assoc, pullback.condition]
    change _ ≫ g ≫ x = _
    rw [← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  atlas_forward_decl GlobalTheory.exists_lift_finiteEtale_testRing
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGood

theorem hom_spQ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℚ) : f = g := by
  have key : ∀ h : X ⟶ Sp ℚ, h = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ h.appTop) := by
    intro h
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key f, key g]
  congr 2
  ext1
  exact RingHom.ext_rat _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_objMap_lower' {l l₂ : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B'} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj Dw l b' s} {o₂ : Obj Dw l₂ b₂ s₂} {o' : Obj Dw l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    Nonempty (ObjMap (GlobalTheory.ObjLower.lower o' h hρ hζ) o (g ≫ π)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₁ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.eta_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₂ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.etaA_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

theorem eq_of_levelMaps {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} (hd : l.Dvd l₂)
    (jK : KA l →+* KA l₂) (hjK : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {r r' : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (m' : SABMap Xo₂.univ.t Xo.univ.t r')
    (he : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (heA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (he' : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = r' ≫ (Xo.univ.eta a).left)
    (heA' : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = r' ≫ (Xo.univ.etaA a).left)
    {T : Scheme.{0}} [IsReduced T] (iU : T ⟶ Xo₂.X) (h : iU ≫ r ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK)
    (h' : iU ≫ r' ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK) : iU ≫ r = iU ≫ r' := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o', ⟨u⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) (KA l₂) (baseKA l₂) (baseKA l₂) (RingHom.id _) Xo₂.X T Xo₂.s
    (iU ≫ Xo₂.s) iU rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨w⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m he heA u
  obtain ⟨w'⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m' he' heA' u
  have hρ : jK (baseKA l).ρ = (GlobalTheory.baseOfFinerLevel hA).ρ :=
    Subtype.ext ((hjK _).trans ((GlobalTheory.coe_baseKA_rho l).trans (GlobalTheory.coe_baseKA_rho l₂).symm))
  have hζ : jK (baseKA l).ζ = (GlobalTheory.baseOfFinerLevel hA).ζ :=
    Subtype.ext ((hjK _).trans (GlobalTheory.coe_levelFieldIncl hA _).symm)
  have hu := GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H Dw l Xo (KA l₂) (GlobalTheory.baseOfFinerLevel hA) jK T
    (iU ≫ Xo₂.s) (GlobalTheory.ObjLower.lower o' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA))
    inferInstance hρ hζ
  exact hu.unique ⟨by rw [Category.assoc, h, Category.assoc], ⟨w⟩⟩ ⟨by rw [Category.assoc, h', Category.assoc], ⟨w'⟩⟩

theorem formallyUnramified_spQ (l : Level H) : FormallyUnramified (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact Algebra.FormallyUnramified.of_isSeparable ℚ (KA l)

theorem locallyOfFiniteType_spQ (l : Level H) : LocallyOfFiniteType (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end GlobalTheory.CoverGood

theorem GlobalTheory.CoverGood.exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  intro E _ _ _ H Dw l Xo c d hpq hl
  obtain ⟨hdvd, hM, -, -, -, ⟨he, heA⟩, hlift, -, -⟩ := hl
  obtain ⟨r₀, jK, m₀, hjK, hr₀s, he₀, heA₀, -, hrF⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h₁, h₂, hfin, het, -, -⟩ := hrF c d.c₂ d.hF.symm
  have hdiv : d.l₂.M / l.M = d.pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  rw [← hdiv] at he

  have hab : (d.r ≫ Xo.s) ≫ spMap (algebraMap ℚ (KA l)) = (d.Xo₂.s ≫ spMap jK) ≫ spMap (algebraMap ℚ (KA l)) :=
    GlobalTheory.CoverGood.hom_spQ_ext _ _
  have := GlobalTheory.CoverGood.formallyUnramified_spQ l
  have := GlobalTheory.CoverGood.locallyOfFiniteType_spQ l
  have hop : IsOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified _ hab
  have hcl : IsClosedImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  have hred₂ : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim d.Xo₂.s)).1
  have hredU : IsReduced (equalizer (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    isReduced_of_isOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
  have hagree : equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ d.r =
      equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ r₀ :=
    GlobalTheory.CoverGood.eq_of_levelMaps hdvd jK hjK d.m m₀ he heA he₀ heA₀ _
      (equalizer.condition (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
      (by rw [hr₀s])

  obtain ⟨U, iU, hop', hcl', hagree', hlU⟩ : ∃ (U : Scheme.{0}) (iU : U ⟶ d.Xo₂.X), IsOpenImmersion iU ∧
      IsClosedImmersion iU ∧ iU ≫ d.r = iU ≫ r₀ ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ d.Xo₂.X),
        x ≫ d.r ≫ Xo.s = x ≫ d.Xo₂.s ≫ spMap jK → ∃ u : Sp K ⟶ U, u ≫ iU = x :=
    ⟨_, _, hop, hcl, hagree, fun K _ x hx =>
      ⟨equalizer.lift x (by simpa only [Category.assoc] using hx), equalizer.lift_ι _ _⟩⟩
  clear hop hcl hagree hredU
  haveI := hop'; haveI := hcl'; haveI := hfin; haveI := het
  have hsp : spMap (IntermediateField.inclusion d.hF.symm.le).toRingHom ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) =
      spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨pullback iU (pullback.fst d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)),
    pullback.snd _ _ ≫ rF, pullback.fst _ _ ≫ iU, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, _, _, j, ⟨k0, hk0⟩⟩ := GlobalTheory.ZM.IsGaloisCover.exists_algClosed_point (Xo.XF c) x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ pullback.snd _ _ : Sp K ⟶ Sp c.F)
    letI : Algebra c.F K := φ.hom.toAlgebra
    letI : Algebra d.c₂.F K := ((algebraMap c.F K).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a := fun a => by
      show algebraMap c.F K (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    have hjs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := hφ.symm
    have hx₀ : (j ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, sOf, spMap, spMap, ← Spec.map_comp]
      rfl
    obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed _ hx₀
    obtain ⟨y₂, hy₂⟩ := hlift K hk y
    have hyr : y₂.x ≫ d.r = y.x := hy₂.1
    have hgood : y₂.x ≫ d.r ≫ Xo.s = y₂.x ≫ d.Xo₂.s ≫ spMap jK := by
      rw [reassoc_of% hyr, y.x_over, reassoc_of% y₂.x_over, sOf, sOf]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext t
      show algebraMap c.F K (IntermediateField.inclusion c.le t) =
        algebraMap c.F K (d.eF.symm (IntermediateField.inclusion d.c₂.le (jK t)))
      exact congrArg (algebraMap c.F K) (Subtype.ext (hjK t).symm)
    obtain ⟨u, hu⟩ := hlU K y₂.x hgood
    have hw : y₂.x ≫ d.Xo₂.s =
        spMap (algebraMap d.c₂.F K) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
      rw [y₂.x_over, sOf, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have hr₀ : y₂.x ≫ r₀ = y.x := by
      rw [← hu, Category.assoc, ← hagree', ← Category.assoc, hu, hyr]
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Sp K ⟶ d.Xo₂.XF d.c₂, w ≫ pullback.fst _ _ = y₂.x ∧
        w ≫ pullback.snd _ _ = spMap (algebraMap d.c₂.F K) :=
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨z, hz⟩ : ∃ z : Sp K ⟶ pullback iU (pullback.fst d.Xo₂.s
        (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)), z ≫ pullback.snd _ _ = w :=
      ⟨pullback.lift u w (by rw [hu, hw₁]), pullback.lift_snd _ _ _⟩
    have e : z ≫ pullback.snd _ _ ≫ rF = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, reassoc_of% hz, reassoc_of% hw₁, hr₀, hy]
      · rw [Category.assoc, Category.assoc, h₂, reassoc_of% hz, reassoc_of% hw₂, hjs, spMap, spMap,
          spMap, ← Spec.map_comp]
        rfl
    exact ⟨z k0, by rw [← Scheme.Hom.comp_apply, e, hk0]⟩
  · simp only [Category.assoc]
    rw [hagree', h₁, pullback.condition_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% h₂, hsp, pullback.condition]
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_goodCover_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  atlas_forward_decl GlobalTheory.CoverGood.exists_good_cover
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_lift_pt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType

theorem exists_eq_of_geom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points

theorem exists_etale_lift : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing

theorem exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := GlobalTheory.T.exists_finiteEtale_goodCover_levelMap

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev algAbove (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] : Algebra d.c₂.F S :=
  ((algebraMap c.F S).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra

theorem algAbove_compat (d : DeltaDat Xo c 0) (S : Type) [CommRing S] [Algebra c.F S] :
    letI := algAbove d S
    ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := by
  intro a
  show algebraMap c.F S (d.eF.symm (d.eF a)) = _
  rw [AlgEquiv.symm_apply_apply]

def Val (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) (p : TRing c.F) (y : FrPt Xo c p.R) (v : p.R) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (φ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap φ y z → FrOver d z₂ z →
      φ v = evR d.Xo₂ d.c₂ g z₂

def Lifts (d : DeltaDat Xo c 0) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

theorem val_unique (d : DeltaDat Xo c 0) (hL : Lifts d) {g : Rul d.Xo₂ d.c₂} {p : TRing c.F} {y : FrPt Xo c p.R}
    {v v' : p.R} (h : Val d g p y v) (h' : Val d g p y v') : v = v' := by
  by_contra hne
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstance
  have hJ : (⊥ : Ideal p.R).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (fun x ⟨m, hm⟩ => Ideal.mem_bot.2 (IsNilpotent.eq_zero ⟨m, Ideal.mem_bot.1 hm⟩))
  have hn : v - v' ∉ (⊥ : Ideal p.R).jacobson := by
    rw [hJ]
    exact fun h₀ => hne (sub_eq_zero.1 (Ideal.mem_bot.1 h₀))
  rw [Ideal.jacobson, Ideal.mem_sInf] at hn
  push Not at hn
  obtain ⟨m, ⟨-, hm⟩, ha⟩ := hn
  haveI := hm
  letI := Ideal.Quotient.field m
  let χ : p.R →ₐ[c.F] AlgebraicClosure (p.R ⧸ m) :=
    (IsScalarTower.toAlgHom c.F (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m))).comp (Ideal.Quotient.mkₐ c.F m)
  letI := algAbove d (AlgebraicClosure (p.R ⧸ m))
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ χ y
  obtain ⟨z₂, hz₂⟩ := hL _ (algAbove_compat d _) z
  have e := (h _ (algAbove_compat d _) χ z z₂ hz hz₂).trans (h' _ (algAbove_compat d _) χ z z₂ hz hz₂).symm
  apply ha
  have e' : algebraMap (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m)) (Ideal.Quotient.mk m (v - v')) = 0 := by
    have : χ (v - v') = 0 := by rw [map_sub, e, sub_self]
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (algebraMap _ _).injective).1 e')

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def ptF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by rw [y.x_over, sOf, ← Spec.map_comp]; rfl)

theorem sOf_cover (d : DeltaDat Xo c 0) (p q : TRing c.F) (ι : p.R →ₐ[c.F] q.R) :
    letI := algAbove d q.R
    spMap ι.toRingHom ≫ spMap (algebraMap c.F p.R) ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) = sOf d.c₂ q.R := by
  letI := algAbove d q.R
  simp only [sOf, spMap, ← Spec.map_comp]
  congr 1
  ext t
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact ι.commutes _

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

include hpq hl in
theorem val_exists {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : ∃ v, Val d g p y v := by
  obtain ⟨Z, π, z₂, hfin, het, hsur, hr, hs⟩ := exists_good_cover E H Dw l Xo c d hpq hl
  obtain ⟨q, ι, ⟨hff, het'⟩, z, hz⟩ := exists_etale_lift _ _ π hfin het hsur c.F p (ptF y)
  letI := algAbove d q.R
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsReduced q.R := (Ideal.isRadical_iff_quotient_reduced q.I).1 q.rad
  have e1 : (z ≫ z₂) ≫ d.r = spMap ι.toRingHom ≫ y.x := by
    rw [Category.assoc, hr, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_fst]
  have e2 : (z ≫ z₂) ≫ d.Xo₂.s = sOf d.c₂ q.R := by
    rw [Category.assoc, hs, ← Category.assoc, hz, Category.assoc, ptF, pullback.lift_snd_assoc]
    exact sOf_cover d p q ι
  obtain ⟨y', hy'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ι y
  obtain ⟨y₂, -, hy₂⟩ := GlobalTheory.FrameLift.exists_frOver d (algAbove_compat d q.R) y' (z ≫ z₂) (e1.trans hy'.1.symm) e2
  have hN₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of d.Xo₂ d.c₂ (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂)
    (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂) g hg.1
  letI : Algebra p.R q.R := ι.toRingHom.toAlgebra
  haveI : IsScalarTower c.F p.R q.R := IsScalarTower.of_algebraMap_eq fun t => (ι.commutes t).symm
  obtain ⟨v, hv⟩ := exists_eq_of_geom p.R q.R hff het' (evR d.Xo₂ d.c₂ g y₂) (by
    intro k _ _ φ ψ hφψ
    letI : Algebra c.F k := (φ.comp (algebraMap c.F q.R)).toAlgebra
    letI := algAbove d k
    have hc : ∀ t : c.F, ψ (algebraMap c.F q.R t) = φ (algebraMap c.F q.R t) := fun t => by
      rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, ← hφψ, RingHom.comp_apply]
    let φ' : q.R →ₐ[c.F] k := { φ with commutes' := fun _ => rfl }
    let ψ' : q.R →ₐ[c.F] k := { ψ with commutes' := fun t => hc t }
    let φ₂ : q.R →ₐ[d.c₂.F] k := { φ with commutes' := fun _ => rfl }
    let ψ₂ : q.R →ₐ[d.c₂.F] k := { ψ with commutes' := fun t => hc _ }
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
    obtain ⟨w', hw'⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ ψ' y'
    obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
    obtain ⟨w₂', hw₂'⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ ψ₂ y₂
    have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
    have o₂ : FrOver d w₂' w' := GlobalTheory.FrameLift.frOver_map d (ψ := ψ') (ψ₂ := ψ₂) rfl hy₂ hw' hw₂'
    have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
    have t₂ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι ψ' hy' hw'
    have ec : ψ'.comp ι = φ'.comp ι := AlgHom.ext fun t => (RingHom.congr_fun hφψ t).symm
    rw [ec] at t₂
    obtain rfl : w = w' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (φ'.comp ι) y).1 w w' t₁ t₂
    have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
    have k₂ := hN₂ q.R k ψ₂ y₂ w₂' hw₂'
    have k₃ := hF k (algAbove_compat d k) w₂ w₂' w o₁ o₂
    exact k₁.symm.trans (k₃.trans k₂))
  refine ⟨v, fun k _ _ _ _ hk φ zz zz₂ hzz hzz₂ => ?_⟩
  have hft : Algebra.FiniteType p.R q.R := by haveI := het'; infer_instance
  obtain ⟨φ₁, hφ₁⟩ := exists_lift_pt p.R q.R hff hft k φ.toRingHom
  have hc : ∀ t : c.F, φ₁ (algebraMap c.F q.R t) = algebraMap c.F k t := fun t => by
    rw [IsScalarTower.algebraMap_apply c.F p.R q.R, ← RingHom.comp_apply, hφ₁]
    exact φ.commutes t
  let φ' : q.R →ₐ[c.F] k := { φ₁ with commutes' := hc }
  have hc₂ : ∀ t : d.c₂.F, φ₁ (algebraMap d.c₂.F q.R t) = algebraMap d.c₂.F k t := fun t => by
    show φ₁ (algebraMap c.F q.R (d.eF.symm t)) = _
    rw [hc, ← hk, AlgEquiv.apply_symm_apply]
  let φ₂ : q.R →ₐ[d.c₂.F] k := { φ₁ with commutes' := hc₂ }
  obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y'
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ _ _ φ₂ y₂
  have o₁ : FrOver d w₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ₂) rfl hy₂ hw hw₂
  have t₁ := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ι φ' hy' hw
  have ec : φ'.comp ι = φ := AlgHom.ext fun t => RingHom.congr_fun hφ₁ t
  rw [ec] at t₁
  obtain rfl : w = zz := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ φ y).1 w zz t₁ hzz
  have k₁ := hN₂ q.R k φ₂ y₂ w₂ hw₂
  have k₃ := hF k hk w₂ zz₂ w o₁ hzz₂
  rw [← k₃, k₁, ← hv]
  exact (RingHom.congr_fun hφ₁ v).symm

end GlobalTheory.CoverDesc

namespace GlobalTheory.CoverDesc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem lifts_of_isLev (d : DeltaDat Xo c 0) (hl : d.IsLev) : Lifts d := by
  obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hl
  exact hlift

open Classical in

def ruleDown (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Rul Xo c := fun p y =>
  if h : ∃ v, Val d g p y v then h.choose else 0

variable (d : DeltaDat Xo c 0) (hpq : 1 ≤ Dw.p + Dw.q) (hl : d.IsLev)

include hpq hl in
theorem val_ruleDown {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) (p : TRing c.F) (y : FrPt Xo c p.R) : Val d g p y (ruleDown d g p y) := by
  have h := val_exists d hpq hl hg hF p y
  have e : ruleDown d g p y = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

include hpq hl in
theorem ruleDown_mem {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul d.Xo₂ d.c₂} (hg : g ∈ sec d.Xo₂ d.c₂ a n)
    (hF : GlobalTheory.LevPull.FibConst d g) : ruleDown d g ∈ sec Xo c a n := by
  have hV := val_ruleDown d hpq hl hg hF
  have hL := lifts_of_isLev d hl
  refine ⟨fun p q φ y z hz => ?_, fun p t y y' hb => ?_⟩
  · refine val_unique d hL (hV q z) fun k _ _ _ _ hk χ w w₂ hw hw₂ => ?_
    have := hV p y k hk (χ.comp φ) w w₂ (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ χ hz hw) hw₂
    rw [← this, AlgHom.comp_apply]
  · refine val_unique d hL (hV p y') fun k _ _ _ _ hk φ z' z₂' hz' hz₂' => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ y
    have hbz := frBorBC (Xo := Xo) (c := c) p.R k φ t y y' z z' hb hz hz'
    obtain ⟨z₂, hz₂⟩ := hL k hk z
    have ex : z₂.x ≫ d.r = z'.x := by rw [hbz.1, ((GlobalTheory.FrameLift.frOver_iff d _ _).1 hz₂).1]
    obtain ⟨z₂'', hx'', hz₂''⟩ := GlobalTheory.FrameLift.exists_frOver d hk z' z₂.x ex z₂.x_over
    have hb₂ := GlobalTheory.FrameLift.frBor_lift d GlobalTheory.abelianSchemeLaws_all.1.globalFns hz₂ hz₂'' hx'' hbz
    have w₁ := GlobalTheory.CoverSec.wtRed d.Xo₂ d.c₂ a n g hg k _ z₂ z₂'' hb₂
    have w₂ := hF k hk z₂' z₂'' z' hz₂' hz₂''
    have w₃ := hV p y k hk φ z z₂ hz hz₂
    rw [w₂, w₁, ← w₃, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]

end GlobalTheory.CoverDesc

section Main

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem GlobalTheory.CoverDesc.section_descends :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  intro E _ _ _ H Dw l Xo c d hpq hl a n g hg hF
  have hm := GlobalTheory.CoverDesc.ruleDown_mem d hpq hl hg hF
  refine ⟨_, hm, fun k _ _ _ _ hk y₂ y ho => ?_⟩
  obtain ⟨p, φ, y₀, hy₀⟩ := GlobalTheory.TransferCompare.allTest_framed Xo c k y
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hm.1 hy₀]
  exact (GlobalTheory.CoverDesc.val_ruleDown d hpq hl hg hF p y₀ k hk φ y y₂ hy₀ ho).symm

end Main
end
end

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_constant_on_fibres_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  atlas_forward_decl GlobalTheory.CoverDesc.section_descends
end

section
section
open NumberField

namespace GlobalTheory

theorem differentIdeal_int_le_differentIdeal (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] :
    differentIdeal ℤ (𝓞 K') ≤ differentIdeal (𝓞 K) (𝓞 K') := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 K')]
  exact Ideal.mul_le_left

theorem span_rational_le_span_and_different_smul_le :
    ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  intro K K' L _ _ _ _ _ _ _ _ _ n M hM
  set φ : (Fin n → K') → (Fin n → L) := fun x i => algebraMap K' L (x i) with hφ
  set P := Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) with hP
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  ·
    have himg : ∀ y ∈ Submodule.span (𝓞 K') {y : Fin n → K' | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K K' (y0 i)}, φ y ∈ P := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨hyM, y0, rfl⟩ := hy
        exact Submodule.subset_span ⟨y0, hyM, rfl⟩
      | zero =>
        have h0 : φ 0 = 0 := by funext i; simp [hφ]
        rw [h0]; exact P.zero_mem
      | add a b _ _ ha hb =>
        have : φ (a + b) = φ a + φ b := by funext i; simp [hφ]
        rw [this]; exact P.add_mem ha hb
      | smul c a _ ha =>
        have : φ (c • a) = algebraMap (𝓞 K') (𝓞 L) c • φ a := by
          funext i
          change algebraMap K' L ((c : K') * a i) = ((algebraMap (𝓞 K') (𝓞 L) c : 𝓞 L) : L) * φ a i
          rw [map_mul]; rfl
        rw [this]; exact P.smul_mem _ ha
    rw [Ideal.map, Submodule.span_smul_span, Submodule.span_le]
    intro z hz
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul.mp hz
    have hdK : d ∈ differentIdeal (𝓞 K) (𝓞 K') := differentIdeal_int_le_differentIdeal K K' hd
    have hmem := differentIdeal_smul_mem_span_rational K K' n M hM d hdK x hx
    have h := himg _ hmem
    have : φ (d • x) = algebraMap (𝓞 K') (𝓞 L) d • φ x := by
      funext i
      change algebraMap K' L ((d : K') * x i) = ((algebraMap (𝓞 K') (𝓞 L) d : 𝓞 L) : L) * φ x i
      rw [map_mul]; rfl
    rw [this] at h
    exact h

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_stable_lattice_rational_span_inclusions : ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  atlas_forward_decl GlobalTheory.span_rational_le_span_and_different_smul_le
end

section
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pull_zero (d : DeltaDat Xo c 0) : Pull d 0 0 := by
  intro k _ _ _ _ _ y₂ y _
  exact (evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm

theorem pull_add {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g)
    (h' : Pull d f' g') : Pull d (f + f') (g + g') := by
  intro k _ _ _ _ hk y₂ y hy
  unfold evR
  rw [evalAt_add, evalAt_add]
  exact congrArg₂ (· + ·) (h k hk y₂ y hy) (h' k hk y₂ y hy)

theorem pull_smul {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (t : c.F) (h : Pull d f g) :
    Pull d (t • f) ((d.eF t : d.c₂.F) • g) := by
  intro k _ _ _ _ hk y₂ y hy
  unfold evR
  rw [evalAt_smul, evalAt_smul, hk t]
  exact congrArg _ (h k hk y₂ y hy)

theorem pull_sum {d : DeltaDat Xo c 0} {m : ℕ} (t : Fin m → c.F) (f : Fin m → Rul Xo c)
    (g : Fin m → Rul d.Xo₂ d.c₂) (h : ∀ i, Pull d (f i) (g i)) :
    Pull d (∑ i, t i • f i) (∑ i, (d.eF (t i) : d.c₂.F) • g i) := by
  classical
  suffices H : ∀ s : Finset (Fin m), Pull d (∑ i ∈ s, t i • f i) (∑ i ∈ s, (d.eF (t i) : d.c₂.F) • g i) from H _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using pull_zero d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact pull_add (pull_smul _ (h i)) ih

theorem fibConst_zero (d : DeltaDat Xo c 0) : FibConst d 0 := (pull_zero d).fibConst

theorem fibConst_add {d : DeltaDat Xo c 0} {g g' : Rul d.Xo₂ d.c₂} (h : FibConst d g) (h' : FibConst d g') :
    FibConst d (g + g') := by
  intro k _ _ _ _ hk y₂ y₂' y h₁ h₂
  unfold evR
  rw [evalAt_add, evalAt_add]
  exact congrArg₂ (· + ·) (h k hk y₂ y₂' y h₁ h₂) (h' k hk y₂ y₂' y h₁ h₂)

theorem fibConst_smul {d : DeltaDat Xo c 0} {g : Rul d.Xo₂ d.c₂} (t : d.c₂.F) (h : FibConst d g) :
    FibConst d (t • g) := by
  intro k _ _ _ _ hk y₂ y₂' y h₁ h₂
  unfold evR
  rw [evalAt_smul, evalAt_smul]
  exact congrArg _ (h k hk y₂ y₂' y h₁ h₂)

theorem rulBC_zero {c' : Coeff l} (hle : c.F ≤ c'.F) : rulBC hle (0 : Rul Xo c) = 0 := by
  funext p y
  letI := resAlg hle p.R
  exact evalAt_zero _ _ _

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

set_option maxHeartbeats 1000000 in

theorem exists_pullMap {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hU : ∀ f ∈ sec Xo c' a n, ∃! g, g ∈ sec d.Xo₂ d.c₂ a n ∧ Pull d f g)
    (hc : ∀ f : cuspW Xo c U (wtZ a n), ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d (rulBC hle (f : Rul Xo c)) g →
      g ∈ cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)) :
    ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n),
      ∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂) := by
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsec' : ∀ f : cuspW Xo c U (wtZ a n), rulBC hle (f : Rul Xo c) ∈ sec Xo c' a n := fun f =>
    (hlin.1 a n _ (cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2))).1
  choose P hPs hPp using fun f : cuspW Xo c U (wtZ a n) => (hU _ (hsec' f)).exists
  have hadd : ∀ f f' : cuspW Xo c U (wtZ a n), rulBC hle ((f + f' : cuspW Xo c U (wtZ a n)) : Rul Xo c) =
      rulBC hle (f : Rul Xo c) + rulBC hle (f' : Rul Xo c) := fun f f' => by
    simpa using hlin.2 1 f f'
  have hsmul : ∀ (t : c.F) (f : cuspW Xo c U (wtZ a n)), rulBC hle ((t • f : cuspW Xo c U (wtZ a n)) : Rul Xo c) =
      incF c c' hle t • rulBC hle (f : Rul Xo c) := fun t f => by
    simpa [rulBC_zero] using hlin.2 t f 0
  have hPadd : ∀ f f', P (f + f') = P f + P f' := fun f f' =>
    (hU _ (hsec' (f + f'))).unique ⟨hPs _, hPp _⟩
      ⟨add_mem (hPs f) (hPs f'), by rw [hadd]; exact pull_add (hPp f) (hPp f')⟩
  have hPsmul : ∀ (t : c.F) f, P (t • f) = (d.eF (incF c c' hle t) : d.c₂.F) • P f := fun t f =>
    (hU _ (hsec' (t • f))).unique ⟨hPs _, hPp _⟩
      ⟨Submodule.smul_mem _ _ (hPs f), by rw [hsmul]; exact pull_smul _ (hPp f)⟩
  exact ⟨{ toFun := fun f => ⟨P f, hc f _ (hPs f) (hPp f)⟩
           map_add' := fun f f' => Subtype.ext (hPadd f f')
           map_smul' := fun t f => Subtype.ext (hPsmul t f) }, fun f => hPp f⟩

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}

set_option maxHeartbeats 1000000 in

theorem span_integral_descent {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hgal : letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra;
      IsGalois c.F d.c₂.F)
    (π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n))
    (hπ : ∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂))
    (hlat : ∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n))
    (hint : ∀ F ∈ sec Xo c' a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d F g → (IntAt d.Xo₂ d.c₂ g ↔ IntAt Xo c' F))
    (C : Submodule c.F (cuspW Xo c U (wtZ a n))) (δ : 𝓞 d.c₂.F) (hδ : δ ∈ differentIdeal ℤ (𝓞 d.c₂.F))
    (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)) (hgL : g ∈ latW U₂ (wtZ a n))
    (hgC : g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n))))) :
    δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsecC : ∀ f : cuspW Xo c U (wtZ a n), (f : Rul Xo c) ∈ sec Xo c a n := fun f =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2)
  have hsec₂ : ∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (g : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ a n := fun g =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U₂) a n).le g.2)
  obtain ⟨m, μ, x, hx⟩ := Submodule.mem_span_set'.1 hgC
  choose b hbC hb using fun i => (x i).2
  have hrul : ∀ v : Fin m → c'.F, (∑ i, v i • rulBC hle (b i : Rul Xo c)) ∈ sec Xo c' a n := fun v =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hlin.1 a n _ (hsecC (b i))).1
  let Φ : (Fin m → d.c₂.F) →ₗ[𝓞 d.c₂.F] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n) :=
    { toFun := fun v => ∑ i, v i • π (b i)
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t v => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_assoc t (v i) (π (b i)) }
  have hΦ : ∀ v, Φ v = ∑ i, v i • π (b i) := fun v => rfl
  have hpullS : ∀ v : Fin m → d.c₂.F,
      Pull d (∑ i, d.eF.symm (v i) • rulBC hle (b i : Rul Xo c)) (Φ v : Rul d.Xo₂ d.c₂) := by
    intro v
    have := pull_sum (fun i => d.eF.symm (v i)) (fun i => rulBC hle (b i : Rul Xo c))
      (fun i => (π (b i) : Rul d.Xo₂ d.c₂)) (fun i => hπ (b i))
    rw [hΦ, Submodule.coe_sum]
    simpa only [Submodule.coe_smul, AlgEquiv.apply_symm_apply] using this
  let M : Submodule (𝓞 d.c₂.F) (Fin m → d.c₂.F) := (latW U₂ (wtZ a n)).comap Φ
  have hmemM : ∀ v, v ∈ M ↔ IntAt Xo c' (∑ i, d.eF.symm (v i) • rulBC hle (b i : Rul Xo c)) := fun v =>
    hint _ (hrul _) _ (hsec₂ _) (hpullS v)
  letI alg : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra
  haveI : IsGalois c.F d.c₂.F := hgal
  have hstab : ∀ s : d.c₂.F ≃ₐ[c.F] d.c₂.F, ∀ v ∈ M, (fun i => s (v i)) ∈ M := by
    intro s v hv
    rw [hmemM] at hv ⊢
    let s' : c'.F ≃+* c'.F := (d.eF.toRingEquiv.trans s.toRingEquiv).trans d.eF.symm.toRingEquiv
    have hs' : ∀ y : c.F, s' (incF c c' hle y) = incF c c' hle y := by
      intro y
      have h0 : s (d.eF (incF c c' hle y)) = d.eF (incF c c' hle y) := s.commutes y
      show d.eF.symm (s (d.eF (incF c c' hle y))) = incF c c' hle y
      rw [h0, AlgEquiv.symm_apply_apply]
    have e : ∀ i, s' (d.eF.symm (v i)) = d.eF.symm (s (v i)) := fun i => by
      show d.eF.symm (s (d.eF (d.eF.symm (v i)))) = _
      rw [AlgEquiv.apply_symm_apply]
    have := GlobalTheory.GalSup.intAt_galois _ H Dw l Xo c c' hle a n s' hs' m (fun i => d.eF.symm (v i))
      (fun i => (b i : Rul Xo c)) (fun i => hsecC (b i)) hv
    simpa only [e] using this
  have hT := (GlobalTheory.T.galois_stable_lattice_rational_span_inclusions c.F d.c₂.F d.c₂.F m M hstab).2
  have hΦμ : Φ μ = g := by
    rw [hΦ, ← hx]
    exact Finset.sum_congr rfl fun i _ => by rw [hb i]
  have hμM : μ ∈ M := by
    show Φ μ ∈ latW U₂ (wtZ a n)
    rw [hΦμ]
    exact hgL
  have hπs : ∀ y : Fin m → c.F, π (∑ i, y i • b i) = Φ (fun i => algebraMap c.F d.c₂.F (y i)) := by
    intro y
    rw [map_sum, hΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    rfl
  have h2 := hT (Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hδ) (Submodule.subset_span ⟨μ, hμM, rfl⟩))
  have h3 : Submodule.span (𝓞 d.c₂.F) ((fun (y : Fin m → c.F) i => algebraMap d.c₂.F d.c₂.F (algebraMap c.F d.c₂.F (y i))) ''
      {y | (fun i => algebraMap c.F d.c₂.F (y i)) ∈ M}) ≤
      (Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)})).comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨∑ i, y i • b i, ⟨C.sum_mem fun i _ => C.smul_mem _ (hbC i), ?_⟩, hπs y⟩
    rw [← hlat, hπs]
    exact hy
  have h4 := h3 h2
  rw [Submodule.mem_comap, map_smul] at h4
  have h5 : δ • Φ μ ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := h4
  rwa [hΦμ] at h5

end GlobalTheory.LevRingDesc

namespace GlobalTheory.LevRingDesc

set_option maxHeartbeats 2000000 in

theorem levRing_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  intro D j H Dw l Xo c c' hle U dict d U₂ dict₂ hL hL₂ hlev hgal a n hdom hev
  have hpq : Dw.q < Dw.p := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.sigW] at hp hq
    omega
  have h1 : 1 ≤ Dw.p + Dw.q := by omega
  have hB : (Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d := Or.inl ⟨by omega, hL.levA⟩
  obtain ⟨hL', hN'⟩ := GlobalTheory.LawsFieldChange.laws_fieldChange D j H Dw l Xo c c' hle U dict hL
  obtain ⟨hU, hinj⟩ := GlobalTheory.CoverSec.section_pullback_existsUnique _ H Dw l Xo c' d h1 hlev hB a n
  have hlin := GlobalTheory.FieldBC.rulBC_sec_val_linear _ H Dw l Xo c c' hle
  have hsecC : ∀ f : cuspW Xo c U (wtZ a n), (f : Rul Xo c) ∈ sec Xo c a n := fun f =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U) a n).le f.2)
  have hsec' : ∀ f : cuspW Xo c U (wtZ a n), rulBC hle (f : Rul Xo c) ∈ sec Xo c' a n := fun f =>
    (hlin.1 a n _ (hsecC f)).1
  have hsec₂ : ∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (g : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ a n := fun g =>
    cusp_le_sec _ _ _ _ _ ((cuspW_wtZ (U := U₂) a n).le g.2)
  have hcusp := GlobalTheory.T.cuspForm_iff_levelCover_pullback D j H Dw l Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) d U₂ dict₂ hL'
    hL₂ hlev a n hdom hev
  have hint := GlobalTheory.CoverInt.pull_intAt_iff _ H Dw l Xo c' d h1 hlev hB a n
  obtain ⟨π, hπ⟩ := exists_pullMap hle U d U₂ a n hU fun f g hg hp => by
    rw [cuspW_wtZ]
    obtain ⟨h, -⟩ := hN' a n hdom f
    have hc : rulBC hle (f : Rul Xo c) ∈ cusp Xo c' (unfBC hle U) a n := by rwa [← cuspW_wtZ]
    exact (hcusp _ (hsec' f) _ hg hp).2 hc
  have hlat : ∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n) := fun f =>
    (hint _ (hsec' f) _ (hsec₂ _) (hπ f)).trans (GlobalTheory.IntCoefExt.intAt_rulBC_iff _ H Dw l Xo c c' hle a n _ (hsecC f))
  refine ⟨π, hπ, ?_, ?_, hlat, ?_, fun C δ hδ g hgL hgC =>
    span_integral_descent hle U d U₂ a n hgal π hπ hlat hint C δ hδ g hgL hgC⟩
  · intro m b hb
    have hv : LinearIndependent c.F (fun k => (b k : Rul Xo c)) :=
      hb.map' (cuspW Xo c U (wtZ a n)).subtype (Submodule.ker_subtype _)
    have hv' := GlobalTheory.CuspFieldChange.linearIndependent_rulBC hle (fun k => hsecC (b k)) hv
    rw [Fintype.linearIndependent_iff] at hv' ⊢
    intro t ht i
    have hp := pull_sum (fun k => d.eF.symm (t k)) (fun k => rulBC hle (b k : Rul Xo c))
      (fun k => (π (b k) : Rul d.Xo₂ d.c₂)) (fun k => hπ (b k))
    have h0 : (∑ k, (d.eF (d.eF.symm (t k)) : d.c₂.F) • (π (b k) : Rul d.Xo₂ d.c₂)) = 0 := by
      simp only [AlgEquiv.apply_symm_apply]
      have := congrArg Subtype.val ht
      simpa only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero] using this
    rw [h0] at hp
    have := hv' _ (hinj _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hsec' (b k))) hp) i
    simpa using this
  · intro σ₂ f
    obtain ⟨h, hn⟩ := hN' a n hdom f
    rw [GlobalTheory.T.peterssonNorm_eq_of_levelCover_pullback D j H Dw l Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) d U₂ dict₂ hL' hL₂ hlev
      a n hdom hev ⟨_, h⟩ (π f) (hπ f) σ₂, hn]
    rfl
  · intro g
    constructor
    · intro hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, rfl⟩ := hx
        exact (hπ f).fibConst
      | zero => exact fibConst_zero d
      | add x y _ _ hx hy => exact fibConst_add hx hy
      | smul t x _ hx => exact fibConst_smul t hx
    · intro hF
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.section_constant_on_fibres_descends _ H Dw l Xo c' d h1 hlev a n _ (hsec₂ g) hF
      have hc' : f' ∈ cusp Xo c' (unfBC hle U) a n := (hcusp _ hf' _ (hsec₂ g) hp).1 (by rw [← cuspW_wtZ]; exact g.2)
      rw [GlobalTheory.CuspFieldChange.cusp_unfBC_eq_span hle U a n] at hc'
      have key : ∀ x ∈ Submodule.span c'.F (rulBC hle '' (cusp Xo c U a n : Set (Rul Xo c))),
          ∃ g' ∈ Submodule.span d.c₂.F (Set.range π), Pull d x (g' : Rul d.Xo₂ d.c₂) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨f0, hf0, rfl⟩ := hx
          have hf0' : f0 ∈ cuspW Xo c U (wtZ a n) := by rw [cuspW_wtZ]; exact hf0
          exact ⟨π ⟨f0, hf0'⟩, Submodule.subset_span ⟨_, rfl⟩, hπ ⟨f0, hf0'⟩⟩
        | zero => exact ⟨0, zero_mem _, pull_zero d⟩
        | add x y _ _ hx hy =>
          obtain ⟨g1, hg1, p1⟩ := hx
          obtain ⟨g2, hg2, p2⟩ := hy
          exact ⟨g1 + g2, add_mem hg1 hg2, pull_add p1 p2⟩
        | smul t x _ hx =>
          obtain ⟨g1, hg1, p1⟩ := hx
          exact ⟨d.eF t • g1, Submodule.smul_mem _ _ hg1, pull_smul t p1⟩
      obtain ⟨g', hg', hp'⟩ := key f' hc'
      have e : g = g' := Subtype.ext ((hU f' hf').unique ⟨hsec₂ g, hp⟩ ⟨hsec₂ g', hp'⟩)
      rw [e]
      exact hg'

end GlobalTheory.LevRingDesc
end
end

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  atlas_forward_decl GlobalTheory.LevRingDesc.levRing_descent
end
