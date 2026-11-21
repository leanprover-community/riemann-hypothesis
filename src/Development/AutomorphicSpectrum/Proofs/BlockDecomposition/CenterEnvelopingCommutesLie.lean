import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction

section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem Zalg_comm_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z :=
  GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep
end

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_enveloping_commutes_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie
