module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureFinite

theorem integralClosure_finite_of_etale (R K L : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.Etale K L] : Module.Finite R (integralClosure R L) := by
  classical
  obtain ⟨I, hI, Ai, hF, hA, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  letI : ∀ i, Algebra R (Ai i) := fun i => ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K (Ai i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : ∀ i, L →ₐ[K] Ai i := fun i => (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  haveI : ∀ i, Module.Finite K (Ai i) := fun i =>
    Module.Finite.of_surjective (ψ i).toLinearMap (by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (Pi.single i y)
      exact ⟨x, by simp [ψ, hx]⟩)
  haveI : ∀ i, Module.Finite R (integralClosure R (Ai i)) := fun i =>
    IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))
  let φ : integralClosure R L →ₗ[R] (∀ i, integralClosure R (Ai i)) :=
    LinearMap.pi (fun i =>
      (((ψ i).restrictScalars R).toLinearMap.comp (integralClosure R L).val.toLinearMap).codRestrict
        (integralClosure R (Ai i)).toSubmodule
        (fun x => IsIntegral.map ((ψ i).restrictScalars R) x.2))
  haveI : IsNoetherian R (∀ i, integralClosure R (Ai i)) := inferInstance
  have hφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    have := congrArg (fun f => ((f i : integralClosure R (Ai i)) : Ai i)) h
    exact this
  haveI := isNoetherian_of_injective φ hφ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite

namespace GlobalTheory.ClosureFinite

end GlobalTheory.ClosureFinite
