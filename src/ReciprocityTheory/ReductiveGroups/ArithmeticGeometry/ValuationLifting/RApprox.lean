import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.Development
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.RhoProjectionAssembly

section
theorem ReciprocityTheory.ChartRestriction.G.Lift.valuation_approximation : ReciprocityTheory.ChartRestriction.G.Lift.ApproxStatement :=
  ReciprocityTheory.ChartRestriction.G.Lift.VA.valApprox_of ReciprocityTheory.ChartRestriction.G.Lift.VA.pair_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.near_one_approximation ReciprocityTheory.ChartRestriction.G.Lift.VA.rho_projection_assembly
end

section
namespace ReciprocityTheory.ChartRestriction.G.Lift

theorem exists_val_eq {Ω : Type} [Field Ω] {ι : Type} [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (n : ι → ℤ) :
    ∃ x : Ω, ∀ i, v i x = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  valuation_approximation Ω ι v hgen hind n

end ReciprocityTheory.ChartRestriction.G.Lift
end
