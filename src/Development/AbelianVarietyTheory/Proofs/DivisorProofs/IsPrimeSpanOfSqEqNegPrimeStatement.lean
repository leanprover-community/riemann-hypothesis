import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import BuildAid.ForwardExisting

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  atlas_forward_decl GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime
