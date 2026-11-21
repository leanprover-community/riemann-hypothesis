import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaH

section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem exists_finset_separating_points {A : Type} (W : Submodule ℂ (A → ℂ)) :
    FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 :=
  _root_.Bl.FirstLemmaH.goal1 W

end GlobalTheory.CompanionTheory.LimV
end

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_determining_set : ∀ {A : Type} (W : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points
