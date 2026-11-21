import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem exists_integralBasis_infinitePlace (F : Type) [Field F] [NumberField F]
    (hF : IsTotallyReal F) : Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have h2 : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ InfinitePlace F :=
    Fintype.equivOfCardEq (by
      rw [hcard, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank])
  exact ⟨(RingOfIntegers.basis F).reindex e⟩

end GlobalTheory.CompanionTheory.SW.ThW
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace
