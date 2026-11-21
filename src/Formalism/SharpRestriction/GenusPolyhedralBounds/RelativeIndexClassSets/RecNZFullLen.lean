import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RecNZFullFacts

noncomputable section

namespace Formalism.MainNotions.Gaps.RN

open TensorProduct IsLocalRing IsDiscreteValuationRing



open Classical in

theorem length_pi_span_quot (A O : Type*) [CommRing A] [CommRing O] [Algebra A O] (ι : Type*) [Fintype ι]
    (N : Submodule A (ι → A)) :
    Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A)))) =
      Module.length O (O ⊗[A] ((ι → A) ⧸ N)) := by
  set S := Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A))) with hS

  let Φ : (ι → O) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) :=
    { toFun := fun v => ∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)
      map_add' := fun v w => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }
  have hmk : ∀ x : ι → A, (Submodule.Quotient.mk x : (ι → A) ⧸ N) =
      ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) := by
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : A) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [← Submodule.mkQ_apply, map_sum, map_smul]
  have hΦg : ∀ x : ι → A, Φ (algebraMap A O ∘ x) = (1 : O) ⊗ₜ[A] (Submodule.Quotient.mk x : (ι → A) ⧸ N) := by
    intro x
    change ∑ i, algebraMap A O (x i) ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) = _
    rw [hmk x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hker : S ≤ LinearMap.ker Φ := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hx0 : (Submodule.Quotient.mk x : (ι → A) ⧸ N) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
    show Φ (algebraMap A O ∘ x) = 0
    rw [hΦg x, hx0, TensorProduct.tmul_zero]
  let Φbar : ((ι → O) ⧸ S) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) := S.liftQ Φ hker
  let ψ1 : (ι → A) →ₗ[A] (ι → O) ⧸ S :=
    (S.mkQ.restrictScalars A) ∘ₗ (LinearMap.compLeft (Algebra.linearMap A O) ι)
  have hN : N ≤ LinearMap.ker ψ1 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (algebraMap A O ∘ x) : (ι → O) ⧸ S) = 0
    rw [Submodule.Quotient.mk_eq_zero, hS]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  let ψ0 : ((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S := N.liftQ ψ1 hN
  let Ψ : O ⊗[A] ((ι → A) ⧸ N) →ₗ[O] (ι → O) ⧸ S :=
    TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton O (((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S) ψ0)
  have h1 : Φbar ∘ₗ Ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.AlgebraTensorModule.lift_tmul,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply, map_smul]
    change c • Φ (algebraMap A O ∘ x) = _
    rw [hΦg x, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hs : ∀ i : ι, algebraMap A O ∘ (Pi.single i (1 : A) : ι → A) = Pi.single i (1 : O) := by
    intro i
    ext k
    by_cases h : k = i <;> simp [Pi.single_apply, h]
  have h2 : Ψ ∘ₗ Φbar = LinearMap.id := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    change Ψ (∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)) = _
    rw [map_sum]
    simp only [Ψ, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, Submodule.liftQ_apply]
    change ∑ i, v i • (Submodule.Quotient.mk (algebraMap A O ∘ Pi.single i 1) : (ι → O) ⧸ S) = _
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hs]
  exact LinearEquiv.length_eq (LinearEquiv.ofLinear Φbar Ψ h1 h2)


end Formalism.MainNotions.Gaps.RN

end
