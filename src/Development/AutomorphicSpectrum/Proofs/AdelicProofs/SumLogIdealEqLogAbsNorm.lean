import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdealSum

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem sum_logIdeal_eq_log_norm_absNorm : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ :=
  @PositivityTheory.Xgf.sum_logIdeal_eq_log_absNorm

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_logIdeal_eq_log_absNorm : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.sum_logIdeal_eq_log_norm_absNorm
