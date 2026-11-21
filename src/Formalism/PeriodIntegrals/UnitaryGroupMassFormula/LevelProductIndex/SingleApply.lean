import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVSumTmul

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) z) = sigR σ (v.adicCompletion F) (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [prV, sigR, evalV, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, evalV, Algebra.TensorProduct.map_tmul]

def single {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F := by
  classical
  exact adOf (Pi.single v a) (fun w => by
    by_cases h : w = v
    · subst h; simpa using ha
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _)

theorem single_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) : single v a ha v = a := by
  classical
  simp [single, adOf_apply]



end PI.LPI
