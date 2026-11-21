import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinRootXPowSubC
import BuildAid.ForwardExisting

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.AbhFin

theorem finite_integralClosure_of_formallyUnramified (R K C : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [FiniteDimensional K C]
    [Algebra.FormallyUnramified K C] : Module.Finite R (integralClosure R C) := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite K C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  haveI := Fintype.ofFinite (MaximalSpectrum C)
  haveI : ∀ m : MaximalSpectrum C, Module.Finite R (integralClosure R (C ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Algebra.FormallyUnramified K (C ⧸ m.asIdeal) :=
      Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Algebra.IsSeparable K (C ⧸ m.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    exact IsIntegralClosure.finite R K (C ⧸ m.asIdeal) _
  let red : ∀ m : MaximalSpectrum C, integralClosure R C →ₗ[R] integralClosure R (C ⧸ m.asIdeal) := fun m =>
    (((Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R C).val).codRestrict
      (integralClosure R (C ⧸ m.asIdeal))
      (fun a => (show IsIntegral R (a : C) from a.2).map (Ideal.Quotient.mkₐ R m.asIdeal))).toLinearMap
  refine Module.Finite.of_injective (LinearMap.pi red) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply (IsArtinianRing.equivPi C).injective
  show _ = IsArtinianRing.equivPi C 0
  rw [map_zero]
  funext m
  exact congrArg Subtype.val (congrFun ha m)

theorem main : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : R) (e : ℕ), Irreducible π → IsUnit (e : R) → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))] [IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], Module.Finite (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) (integralClosure (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) (TensorProduct R (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) L)) := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ π e hπ he _ _
  classical
  set f : R[X] := X ^ e - C π with hf
  set g : K[X] := X ^ e - C (algebraMap R K π) with hg
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hfm : f.Monic := monic_X_pow_sub_C _ he0
  have hgm : g.Monic := monic_X_pow_sub_C _ he0
  have hπK : IsUnit (algebraMap R K π) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)).isUnit
  haveI : Algebra.Etale K (AdjoinRoot g) :=
    GlobalTheory.etale_adjoinRoot_X_pow_sub_C K e _ (by simpa using he.map (algebraMap R K)) hπK
  haveI : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis' hgm).finite
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hfm).finite
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  let C' := L ⊗[K] AdjoinRoot g
  haveI : Algebra.FormallyUnramified L C' := inferInstance
  haveI : Algebra.FormallyUnramified K C' := Algebra.FormallyUnramified.comp K L C'
  haveI : FiniteDimensional K C' := inferInstance
  haveI : IsScalarTower R K C' := inferInstance
  have hfinC : Module.Finite R (integralClosure R C') :=
    finite_integralClosure_of_formallyUnramified R K C'

  have hroot : aeval (AdjoinRoot.root g) f = 0 := by
    have h := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [hf, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, h]
    exact (IsScalarTower.algebraMap_apply R K (AdjoinRoot g) π).symm
  let φ : AdjoinRoot f →ₐ[R] AdjoinRoot g := AdjoinRoot.liftAlgHom f (Algebra.ofId R (AdjoinRoot g)) (AdjoinRoot.root g) hroot
  let ψ : L ⊗[R] AdjoinRoot f →ₐ[L] C' :=
    Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := L))
      (((Algebra.TensorProduct.includeRight : AdjoinRoot g →ₐ[K] C').restrictScalars R).comp φ)
      (fun _ _ => Commute.all _ _)
  let bR := Algebra.TensorProduct.basis L (AdjoinRoot.powerBasis' hfm).basis
  let bK := Algebra.TensorProduct.basis L (AdjoinRoot.powerBasis' hgm).basis
  have hdeg : f.natDegree = g.natDegree := by
    rw [hf, hg, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]
  have hψb : ∀ i, ψ (bR i) = bK (Fin.cast hdeg i) := by
    intro i
    have hφ : φ (AdjoinRoot.root f) = AdjoinRoot.root g := AdjoinRoot.liftAlgHom_root _ _ _ _
    simp only [bR, bK, Algebra.TensorProduct.basis_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, ψ,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply, map_pow,
      hφ, Fin.val_cast, Fin.coe_cast]
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hli := bK.linearIndependent.comp (Fin.cast hdeg) (Fin.cast_injective hdeg)
    rw [← bR.sum_repr x, map_sum] at hx
    simp only [map_smul, hψb] at hx
    have h0 : ∀ i, bR.repr x i = 0 := Fintype.linearIndependent_iff.1 hli _ hx
    rw [← bR.sum_repr x]
    simp [h0]
  let Φ : AdjoinRoot f ⊗[R] L →ₐ[R] C' :=
    (ψ.restrictScalars R).comp (Algebra.TensorProduct.comm R (AdjoinRoot f) L).toAlgHom
  have hΦ : Function.Injective Φ := hinj.comp (Algebra.TensorProduct.comm R (AdjoinRoot f) L).injective
  let M := integralClosure (AdjoinRoot f) (AdjoinRoot f ⊗[R] L)
  let lin : M →ₗ[R] integralClosure R C' :=
    { toFun := fun x => ⟨Φ (x : AdjoinRoot f ⊗[R] L), (isIntegral_trans (R := R) (A := AdjoinRoot f) _ x.2).map Φ⟩
      map_add' := fun x y => Subtype.ext (map_add Φ (x : AdjoinRoot f ⊗[R] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Φ r (x : AdjoinRoot f ⊗[R] L)) }
  have hlin : Function.Injective lin := fun x y h =>
    Subtype.ext (hΦ (congrArg Subtype.val h))
  haveI : Module.Finite R M := Module.Finite.of_injective lin hlin
  exact Module.Finite.of_restrictScalars_finite R (AdjoinRoot f) M

end GlobalTheory.AbhFin
end

section
section
open IsLocalRing
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.NormFin

theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisation_dvr_tensor_separable_finite : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  atlas_forward_decl GlobalTheory.NormFin.main
end
