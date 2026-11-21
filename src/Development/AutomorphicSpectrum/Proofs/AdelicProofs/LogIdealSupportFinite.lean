import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
import BuildAid.ForwardExisting

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finite_logIdeal_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ →
    {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite :=
  @PositivityTheory.Xgf.logIdeal_support_finite

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero
