import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange

section
open Matrix

noncomputable section

namespace CompanionTheory.D.LK

open ReciprocityTheory.ChartRestriction.DS

def DSUniqP : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ PI.UpqRep.UJset ε, ∀ x, U (σ g x) = σ' g (U x)

end CompanionTheory.D.LK
end
end

section
namespace CompanionTheory.D.LK

theorem discrete_series_unique_of : DSUniqP := GlobalTheory.CompanionTheory.DSUniq.ds_unique hMultAlg hKModExists hOrthCyc

end CompanionTheory.D.LK
end
