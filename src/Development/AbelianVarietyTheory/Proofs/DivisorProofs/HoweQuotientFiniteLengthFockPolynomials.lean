import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne

section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  obtain ⟨hStab, hAdm⟩ := GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants P Q R S x
  refine ⟨⟨hLie, hWt, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne P Q R S x⟩

end GlobalTheory.HoweR
end

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeQuotientFiniteLength_fockPolynomials : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  atlas_forward_decl GlobalTheory.HoweR.fock_pack
