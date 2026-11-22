module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem firstTypePrime_lt_rowPrime (D : D7) (u : D.what₂.Word) : D.host.g 0 < (D.mem u).A.T := by
  have h := (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd D.host.d _ _ (by have := D.host.hyp.2.2.2.1; omega)
    ((GlobalTheory.Mem.An.normOne_iff_host D.R D.host _ _).2 (D.T_norm u))).1
  have h' : (D.mem u).A.T ≡ 1 [MOD D.host.g 0] := Nat.ModEq.of_dvd (Dvd.dvd.mul_left ⟨D.host.g 0 * D.host.g 1 ^ 2, by ring⟩ _) h
  have h1 := (D.mem u).A.T_prime.one_lt
  have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' h1.le).1 h'.symm)
  omega

end GlobalTheory.EX.DC

end
