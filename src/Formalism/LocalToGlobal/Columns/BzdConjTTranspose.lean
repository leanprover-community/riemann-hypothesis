import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end SlopeTestRemainingChoices

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def stdPairB : StdV K lam →ₗ[K] StdV K lam →ₗ[K] K := pairBK (oneW lam)

instance bzd_finite : Module.Finite K (StdV K lam) := Module.Finite.of_basis (bVV K (oneW lam))

theorem stdPairB_injective : Function.Injective (stdPairB K lam) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  exact (pairingBNondegenerate_holds K Unit n (oneW lam)).1 x fun y => by
    have := congrArg (fun f : Module.Dual K (StdV K lam) => f y) hx
    exact this

def stdDualEquiv : StdV K lam ≃ₗ[K] Module.Dual K (StdV K lam) :=
  LinearMap.linearEquivOfInjective (stdPairB K lam) (stdPairB_injective K lam) (Subspace.dual_finrank_eq).symm

def stdGramAt (v : InfinitePlace K) : Matrix (VVIdx (oneW lam)) (VVIdx (oneW lam)) ℂ :=
  Matrix.of fun i j => v.embedding (stdPairB K lam (bVV K (oneW lam) i) (bVV K (oneW lam) j))

end Std


end Formalism.L2.Col
