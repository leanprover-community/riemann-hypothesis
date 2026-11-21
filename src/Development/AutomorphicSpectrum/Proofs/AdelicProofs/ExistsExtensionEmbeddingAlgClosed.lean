import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import BuildAid.ForwardExisting

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_comp_eq_of_numberField (k k' A : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    ∃ j' : k' →+* A, j'.comp f = j := by
  let _ : Algebra k k' := f.toAlgebra
  let _ : Algebra k A := j.toAlgebra
  have : IsScalarTower ℚ k k' := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ k') q, eq_ratCast (algebraMap ℚ k) q,
      map_ratCast]
  have : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField
