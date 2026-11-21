import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.SesquilinearFractions.RatProductFormula
import BuildAid.ForwardExisting

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem rat_product_formula_complex : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 :=
  PositivityTheory.Xgf.rat_product_formula

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_product_formula : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.rat_product_formula_complex
