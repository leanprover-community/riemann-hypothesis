import Mathlib
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LatticeFinitelyGenerated

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain

def LocFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (Y : Submodule (𝓞 K) V), Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      Submodule.span K (Set.range b) = Submodule.span K (Y : Set V) ∧ (∀ i, b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • y ∈ Submodule.span (𝓞 K) (Set.range b)

section Den

variable {K : Type} [Field K] [NumberField K]


end Den


end PI.DvRows
