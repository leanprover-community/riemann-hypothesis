import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.BlockValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoinvReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsComb
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvariantTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTopGeneral
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordInj
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMono
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfAtStair
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfMonomialPsumOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfUpdateZero
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfVandermondePsumOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombDetDescFactorial
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombExtendWord
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookBranch
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookShapeFacts
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombPcntAppend
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortLe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShiftDistinct
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShift
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombStripSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauOfWord
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowLattice
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowPrefix
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombWordOfTableau
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombYoungRowCard
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltCoeffInjective
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymDecomposition
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagCoeffBlockPermute
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffNotDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffPrime
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDividedDifferencePoly
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagInjSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralKillsPowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondeMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondePos
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralViaQuotient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagPowerSumPreimage
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagProdPrimesDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagQuotientHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictConstantCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictDecomposition
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictPowerSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictSymmetric
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagStaircaseOrbit
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSwapDivisible
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusCharacterFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookCharacterSumIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookDimensionSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookTableauCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaA
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaB
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaC
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLinearTermValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Pluecker
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTablePos
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBoundOfPrimeBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestInnerTsumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestKSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBoundOfFactor
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestTermWellDefined
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAevalSignedRename
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantRenamePlace
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAltPartitionExpansion
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAntisymmetrizePlace
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteGenerating
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternant
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternantZero
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatExponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchEvalPowerSumHom
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchHookResidues
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchJTMatrixDetAtRoots
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchNonHookResidues
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumHomWeighted
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchProdOneSubRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchResidueCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityBialternant
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsEq
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsPerm
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityVandermondeNe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurEvalMatrix
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurRowsToK
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSmallBlockProduct
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchStrictAntiSplit
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurPowerSumCoefficient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurSignCoefficient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchWeightedPreimage
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PShiftSumRule
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PTotalIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.SameFactorDegreeClauseOfValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AntisymmetrizeBlockVandermondeOf
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StaircaseIsHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.TenNinthsLe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.RestAt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.SumPderivRealApply

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := rfl

theorem CharacterAtIdentity.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) : CharacterAtIdentity.Statement := by
  intro m lam hlam
  rw [symmetricGroupCharacter_eq_cf, h2 m (∑ i, lam i) lam hlam, h1 m lam hlam]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombCardYoungCells.proof : CombCardYoungCells.Statement := by
  intro m lam
  classical
  unfold youngCells
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)
  have hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_range (lam i), ← hset, Finset.card_filter]

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombVandermondeSucc.proof : CombVandermondeSucc.Statement := by
  intro n v
  unfold vandermondeOf
  have hI : ∀ {k : ℕ} (i : Fin k), Ioi i = univ.filter (fun j => i < j) := by
    intro k i; ext j; simp
  simp only [hI, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagHomogeneousComponentMul.proof : FlagHomogeneousComponentMul.Statement := by
  intro σ P G k n hP
  exact HomogeneousComponentMul.proof σ ℚ P G k n hP

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagPowerSumSymmetric.proof : FlagPowerSumSymmetric.Statement := by
  intro f N k τ w
  simp only [blockPowerSum, map_sum, map_pow, Flag.blockPermute_X]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : RootRing f N) ^ k)

end RestTerms

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem FlagRestrictHomogeneous.proof : FlagRestrictHomogeneous.Statement := by
  intro f N τ R k hR
  have h := hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by
    intro p
    split_ifs
    · exact isHomogeneous_X ℚ _
    · exact isHomogeneous_zero _ _ _)
  rw [one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagSymmetricMulAntisym.proof : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Comb

theorem FrobeniusDimensionFormula.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem IntegralIsDividedDifference.proof (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) : IntegralIsDividedDifference.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
  · intro H hH
    exact h1 f N H hH

end RestTerms

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestBound.proof (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P

end RestTerms

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

theorem RestPolynomialDecomposes.proof (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem RestPolynomialHomogeneousDecomposition.proof (h1 : CoinvAboveTop.Statement)
    (h2 : RestPolynomialHomogeneous.Statement) :
    RestPolynomialHomogeneousDecomposition.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, hF⟩ := h1 ℚ f (r + a) (topDegree f (r + a) + 1) (restPolynomial f r a c)
    (h2 f r a c) (by unfold Coinv.coinvTop topDegree; omega)
  exact ⟨Q, hF, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem SchAlternantHomogeneous.proof : SchAlternantHomogeneous.Statement := by
  intro ι _ _ e
  unfold alternant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i) :=
    IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, Matrix.of_apply, one_smul, Units.neg_smul]
  · exact h
  · exact h.neg

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity

open Finset

def HookCharacterSumIdentitySmall.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → r ≤ a →
    (a : ℚ) * numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) =
      ∑ k ∈ Finset.Icc 2 (r + a), ∑ l ∈ Finset.range (min r k),
        (-1 : ℚ) ^ l * symmetricGroupCharacter (fun i => a + hookShape r k l i)
          ((k - 1) :: List.replicate (r * a + 1) 1)

end GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem CoinvStepReduction.full : CoinvStepReduction.Statement :=
  CoinvStepReduction.proof

theorem CoinvMonomialReduction.full : CoinvMonomialReduction.Statement :=
  CoinvMonomialReduction.proof CoinvStepReduction.full

theorem CoinvPolynomialReduction.full : CoinvPolynomialReduction.Statement :=
  CoinvPolynomialReduction.proof CoinvMonomialReduction.full

theorem CoinvIdealRepresentation.full : CoinvIdealRepresentation.Statement :=
  CoinvIdealRepresentation.proof

theorem HomogeneousComponentMul.full : HomogeneousComponentMul.Statement :=
  HomogeneousComponentMul.proof

theorem CoinvIdealComponent.full : CoinvIdealComponent.Statement :=
  CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full

theorem CoinvStaircaseDegree.full : CoinvStaircaseDegree.Statement :=
  CoinvStaircaseDegree.proof

theorem CoinvStaircaseComponent.full : CoinvStaircaseComponent.Statement :=
  CoinvStaircaseComponent.proof CoinvStaircaseDegree.full

theorem CoinvAtTop.full : CoinvAtTop.Statement :=
  CoinvAtTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

theorem CoinvariantTopDegree.full : CoinvariantTopDegree.Statement :=
  CoinvariantTopDegree.proof CoinvAtTop.full

theorem FlagCoeffBlockPermute.full : FlagCoeffBlockPermute.Statement :=
  FlagCoeffBlockPermute.proof

theorem FlagAltCoeffInjective.full : FlagAltCoeffInjective.Statement :=
  FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full

theorem FlagInjSumBound.full : FlagInjSumBound.Statement :=
  FlagInjSumBound.proof

theorem FlagStaircaseOrbit.full : FlagStaircaseOrbit.Statement :=
  FlagStaircaseOrbit.proof

theorem FlagVandermondeHomogeneous.full : FlagVandermondeHomogeneous.Statement :=
  FlagVandermondeHomogeneous.proof

theorem FlagAltTopDegree.full : FlagAltTopDegree.Statement :=
  FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full

theorem FlagAntisymHomogeneous.full : FlagAntisymHomogeneous.Statement :=
  FlagAntisymHomogeneous.proof

theorem FlagIntegralPermute.full : FlagIntegralPermute.Statement :=
  FlagIntegralPermute.proof FlagCoeffBlockPermute.full

theorem FlagIntegralAntisymmetrize.full : FlagIntegralAntisymmetrize.Statement :=
  FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full

theorem FlagIntegralTopComponent.full : FlagIntegralTopComponent.Statement :=
  FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full

theorem FlagHomogeneousComponentMul.full : FlagHomogeneousComponentMul.Statement :=
  FlagHomogeneousComponentMul.proof

theorem FlagIntegralVandermondeMul.full : FlagIntegralVandermondeMul.Statement :=
  FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full

theorem FlagIntegralViaQuotient.full : FlagIntegralViaQuotient.Statement :=
  FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full

theorem FlagIntegralTopDegree.full : FlagIntegralTopDegree.Statement :=
  FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full

theorem FlagIntegralVandermondePos.full : FlagIntegralVandermondePos.Statement :=
  FlagIntegralVandermondePos.proof

theorem IntegralIsDividedDifference.full : IntegralIsDividedDifference.Statement :=
  IntegralIsDividedDifference.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full

theorem FlagSwapDivisible.full : FlagSwapDivisible.Statement :=
  FlagSwapDivisible.proof

theorem FlagDiffPrime.full : FlagDiffPrime.Statement :=
  FlagDiffPrime.proof

theorem FlagDiffNotDvd.full : FlagDiffNotDvd.Statement :=
  FlagDiffNotDvd.proof

theorem FlagProdPrimesDvd.full : FlagProdPrimesDvd.Statement :=
  FlagProdPrimesDvd.proof

theorem FlagVandermondeDvd.full : FlagVandermondeDvd.Statement :=
  FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full

theorem FlagDividedDifferencePoly.full : FlagDividedDifferencePoly.Statement :=
  FlagDividedDifferencePoly.proof FlagVandermondeDvd.full

theorem FlagSymmetricMulAntisym.full : FlagSymmetricMulAntisym.Statement :=
  FlagSymmetricMulAntisym.proof

theorem FlagPowerSumSymmetric.full : FlagPowerSumSymmetric.Statement :=
  FlagPowerSumSymmetric.proof

theorem FlagAntisymDecomposition.full : FlagAntisymDecomposition.Statement :=
  FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full

theorem FlagQuotientHomogeneous.full : FlagQuotientHomogeneous.Statement :=
  FlagQuotientHomogeneous.proof

theorem FlagRestrictHomogeneous.full : FlagRestrictHomogeneous.Statement :=
  FlagRestrictHomogeneous.proof

theorem FlagRestrictSymmetric.full : FlagRestrictSymmetric.Statement :=
  FlagRestrictSymmetric.proof

theorem FlagRestrictPowerSum.full : FlagRestrictPowerSum.Statement :=
  FlagRestrictPowerSum.proof

theorem FlagRestrictDecomposition.full : FlagRestrictDecomposition.Statement :=
  FlagRestrictDecomposition.proof FlagRestrictPowerSum.full

theorem FlagPowerSumPreimage.full : FlagPowerSumPreimage.Statement :=
  FlagPowerSumPreimage.proof

theorem FlagRestrictConstantCoeff.full : FlagRestrictConstantCoeff.Statement :=
  FlagRestrictConstantCoeff.proof

theorem LemmaA.full : LemmaA.Statement :=
  LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full FlagRestrictDecomposition.full FlagPowerSumPreimage.full FlagRestrictConstantCoeff.full FlagIntegralViaQuotient.full

theorem RestTermWellDefined.full : RestTermWellDefined.Statement :=
  RestTermWellDefined.proof LemmaA.full

theorem SchAevalSignedRename.full : SchAevalSignedRename.Statement :=
  SchAevalSignedRename.proof

theorem SchAntisymmetrizePlace.full : SchAntisymmetrizePlace.Statement :=
  SchAntisymmetrizePlace.proof

theorem SchAlternantHomogeneous.full : SchAlternantHomogeneous.Statement :=
  SchAlternantHomogeneous.proof

theorem SchSmallBlockProduct.full : SchSmallBlockProduct.Statement :=
  SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full

theorem SchAlternantRenamePlace.full : SchAlternantRenamePlace.Statement :=
  SchAlternantRenamePlace.proof

theorem SchConcatExponent.full : SchConcatExponent.Statement :=
  SchConcatExponent.proof

theorem SchConcatAlternant.full : SchConcatAlternant.Statement :=
  SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full

theorem SchConcatAlternantZero.full : SchConcatAlternantZero.Statement :=
  SchConcatAlternantZero.proof

theorem SchBlockVandermondeOne.full : SchBlockVandermondeOne.Statement :=
  SchBlockVandermondeOne.proof

theorem SchSchurHomogeneous.full : SchSchurHomogeneous.Statement :=
  SchSchurHomogeneous.proof

theorem LemmaB.full : LemmaB.Statement :=
  LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full

theorem CombCardYoungCells.full : CombCardYoungCells.Statement :=
  CombCardYoungCells.proof

theorem CombTableauRowCount.full : CombTableauRowCount.Statement :=
  CombTableauRowCount.proof

theorem CombTableauRowPrefix.full : CombTableauRowPrefix.Statement :=
  CombTableauRowPrefix.proof

theorem CombTableauRowLattice.full : CombTableauRowLattice.Statement :=
  CombTableauRowLattice.proof

theorem CombYoungRowCard.full : CombYoungRowCard.Statement :=
  CombYoungRowCard.proof

theorem CombWordOfTableau.full : CombWordOfTableau.Statement :=
  CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full

theorem CombCellOfWordMem.full : CombCellOfWordMem.Statement :=
  CombCellOfWordMem.proof

theorem CombCellOfWordInj.full : CombCellOfWordInj.Statement :=
  CombCellOfWordInj.proof

theorem CombCellOfWordMono.full : CombCellOfWordMono.Statement :=
  CombCellOfWordMono.proof

theorem CombTableauOfWord.full : CombTableauOfWord.Statement :=
  CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full

theorem CombTableEqWords.full : CombTableEqWords.Statement :=
  CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full

theorem CombCfUpdateZero.full : CombCfUpdateZero.Statement :=
  CombCfUpdateZero.proof

theorem CombCfAtStair.full : CombCfAtStair.Statement :=
  CombCfAtStair.proof CombCfUpdateZero.full

theorem CombCfMonomialPsumOne.full : CombCfMonomialPsumOne.Statement :=
  CombCfMonomialPsumOne.proof

theorem CombDetDescFactorial.full : CombDetDescFactorial.Statement :=
  CombDetDescFactorial.proof

theorem CombCfVandermondePsumOne.full : CombCfVandermondePsumOne.Statement :=
  CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full

theorem FrobeniusDimensionFormula.full : FrobeniusDimensionFormula.Statement :=
  FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full

theorem LemmaC.full : LemmaC.Statement :=
  LemmaC.proof FrobeniusDimensionFormula.full

theorem SchPowerSumHomWeighted.full : SchPowerSumHomWeighted.Statement :=
  SchPowerSumHomWeighted.proof

theorem SchWeightedPreimage.full : SchWeightedPreimage.Statement :=
  SchWeightedPreimage.proof SchPowerSumHomWeighted.full

theorem SchPowerSumAtRootsOfUnity.full : SchPowerSumAtRootsOfUnity.Statement :=
  SchPowerSumAtRootsOfUnity.proof

theorem SchEvalPowerSumHom.full : SchEvalPowerSumHom.Statement :=
  SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full

theorem SchSchurRowsToK.full : SchSchurRowsToK.Statement :=
  SchSchurRowsToK.proof

theorem SchProdOneSubRootsOfUnity.full : SchProdOneSubRootsOfUnity.Statement :=
  SchProdOneSubRootsOfUnity.proof

theorem SchCompleteGenerating.full : SchCompleteGenerating.Statement :=
  SchCompleteGenerating.proof

theorem SchCompleteAtRootsOfUnity.full : SchCompleteAtRootsOfUnity.Statement :=
  SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full

theorem SchSchurEvalMatrix.full : SchSchurEvalMatrix.Statement :=
  SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full

theorem SchRootOfUnityBialternant.full : SchRootOfUnityBialternant.Statement :=
  SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full

theorem SchRootOfUnityRowsPerm.full : SchRootOfUnityRowsPerm.Statement :=
  SchRootOfUnityRowsPerm.proof

theorem SchRootOfUnityRowsEq.full : SchRootOfUnityRowsEq.Statement :=
  SchRootOfUnityRowsEq.proof

theorem SchHookResidues.full : SchHookResidues.Statement :=
  SchHookResidues.proof

theorem SchResidueCount.full : SchResidueCount.Statement :=
  SchResidueCount.proof

theorem SchNonHookResidues.full : SchNonHookResidues.Statement :=
  SchNonHookResidues.proof SchResidueCount.full

theorem SchRootOfUnityVandermondeNe.full : SchRootOfUnityVandermondeNe.Statement :=
  SchRootOfUnityVandermondeNe.proof

theorem SchJTMatrixDetAtRoots.full : SchJTMatrixDetAtRoots.Statement :=
  SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full

theorem SchSchurAtRootsOfUnity.full : SchSchurAtRootsOfUnity.Statement :=
  SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full

theorem SchurPowerSumCoefficient.full : SchurPowerSumCoefficient.Statement :=
  SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full

theorem CombHookShapeFacts.full : CombHookShapeFacts.Statement :=
  CombHookShapeFacts.proof

theorem CombHookBranch.full : CombHookBranch.Statement :=
  CombHookBranch.proof CombHookShapeFacts.full

theorem CombHookCount.full : CombHookCount.Statement :=
  CombHookCount.proof CombHookShapeFacts.full CombHookBranch.full

theorem HookDimensionSum.full : HookDimensionSum.Statement :=
  HookDimensionSum.proof CombTableEqWords.full CombHookShapeFacts.full CombHookCount.full

theorem SchStrictAntiSplit.full : SchStrictAntiSplit.Statement :=
  SchStrictAntiSplit.proof

theorem SchAltPartitionExpansion.full : SchAltPartitionExpansion.Statement :=
  SchAltPartitionExpansion.proof SchStrictAntiSplit.full

theorem FrobeniusCharacterFormula.full : FrobeniusCharacterFormula.Statement :=
  FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full

theorem CombSortLe.full : CombSortLe.Statement :=
  CombSortLe.proof

theorem CombSortShift.full : CombSortShift.Statement :=
  Comb.CombSortShift.proof CombSortLe.full

theorem CombSortShiftDistinct.full : CombSortShiftDistinct.Statement :=
  CombSortShiftDistinct.proof

theorem CombPcntAppend.full : CombPcntAppend.Statement :=
  CombPcntAppend.proof

theorem CombExtendWord.full : CombExtendWord.Statement :=
  CombExtendWord.proof CombPcntAppend.full

theorem CombStripSum.full : CombStripSum.Statement :=
  CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full

theorem CombCfBound.full : CombCfBound.Statement :=
  CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full

theorem CharacterBound.full : CharacterBound.Statement :=
  CharacterBound.proof CombTableEqWords.full CombCfBound.full

theorem CharacterAtIdentity.full : CharacterAtIdentity.Statement :=
  CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full

theorem CoinvAboveTop.full : CoinvAboveTop.Statement :=
  CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

theorem VandermondeOfHomogeneous.full : VandermondeOfHomogeneous.Statement :=
  VandermondeOfHomogeneous.proof

theorem RestPolynomialHomogeneous.full : RestPolynomialHomogeneous.Statement :=
  RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full

theorem RestPolynomialHomogeneousDecomposition.full : RestPolynomialHomogeneousDecomposition.Statement :=
  RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full

theorem RestPolynomialDecomposes.full : RestPolynomialDecomposes.Statement :=
  RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full

theorem SameFactorFormula.full : SameFactorFormula.Statement :=
  SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem SchurSignCoefficient.full : SchurSignCoefficient.Statement :=
  SchurSignCoefficient.proof SchurPowerSumCoefficient.full

theorem HookTableauCount.full : HookTableauCount.Statement :=
  HookTableauCount.proof FrobeniusDimensionFormula.full

theorem HookSumBound.full : HookSumBound.Statement :=
  HookSumBound.proof LemmaC.full HookTableauCount.full

theorem SameFactorBound.full : SameFactorBound.Statement :=
  SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem OtherFactorFormula.full : OtherFactorFormula.Statement :=
  OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem OtherFactorBound.full : OtherFactorBound.Statement :=
  OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem ShiftSumRule.full : ShiftSumRule.Statement :=
  ShiftSumRule.proof ShiftTotalValues.intersectionNumber_baseChange FlagIntegralKillsPowerSums.intersectionNumber_baseChange

theorem LinearTermValue.full : LinearTermValue.Statement :=
  LinearTermValue.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full

theorem HookCharacterSumIdentity.full : HookCharacterSumIdentity.Statement :=
  HookCharacterSumIdentity.proof ShiftSumRule.full LinearTermValue.full SameFactorFormula.full SchurSignCoefficient.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem CombVandermondeSucc.full : CombVandermondeSucc.Statement :=
  CombVandermondeSucc.proof

theorem TotalIdentity.full : TotalIdentity.Statement :=
  TotalIdentity.proof FrobeniusDimensionFormula.full CombVandermondeSucc.full

theorem RestInnerTsumBound.full : RestInnerTsumBound.Statement :=
  RestInnerTsumBound.proof

theorem RestKSumBound.full : RestKSumBound.Statement :=
  RestKSumBound.proof

theorem RestPrimeBoundOfFactor.full : RestPrimeBoundOfFactor.Statement :=
  RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full

theorem RestPrimeBound.full : RestPrimeBound.Statement :=
  RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full

theorem RestBoundOfPrimeBound.full : RestBoundOfPrimeBound.Statement :=
  RestBoundOfPrimeBound.proof

theorem RestBound.full : RestBound.Statement :=
  RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full

theorem FlagIntegralKillsPowerSums.full : FlagIntegralKillsPowerSums.Statement :=
  FlagIntegralKillsPowerSums.intersectionNumber_baseChange

theorem DividedDifferenceOfVandermonde.full : DividedDifferenceOfVandermonde.Statement :=
  DividedDifferenceOfVandermonde.intersectionNumber_baseChange

theorem XBound.full : XBound.Statement :=
  XBound.intersectionNumber_baseChange

theorem XOverPrime.full : XOverPrime.Statement :=
  XOverPrime.intersectionNumber_baseChange

theorem GeometricTail.full : GeometricTail.Statement :=
  GeometricTail.intersectionNumber_baseChange

theorem ExponentialTail.full : ExponentialTail.Statement :=
  ExponentialTail.intersectionNumber_baseChange

theorem ChebyshevThetaBound.full : ChebyshevThetaBound.Statement :=
  ChebyshevThetaBound.intersectionNumber_baseChange

theorem PrimeLogSquareTail.full : PrimeLogSquareTail.Statement :=
  PrimeLogSquareTail.intersectionNumber_baseChange

theorem RestConstants.full : RestConstants.Statement :=
  RestConstants.intersectionNumber_baseChange

theorem IntegerLogSquareTail.full : IntegerLogSquareTail.Statement :=
  IntegerLogSquareTail.intersectionNumber_baseChange

theorem ShiftTotalValues.full : ShiftTotalValues.Statement :=
  ShiftTotalValues.intersectionNumber_baseChange

theorem FibreTranslationInvariance.full : FibreTranslationInvariance.Statement :=
  FibreTranslationInvariance.intersectionNumber_baseChange

theorem PlueckerCauchyBinet.full : PlueckerCauchyBinet.Statement :=
  PlueckerCauchyBinet.intersectionNumber_baseChange

theorem PlueckerHadamard.full : PlueckerHadamard.Statement :=
  PlueckerHadamard.intersectionNumber_baseChange

theorem SmallRankBound.full : SmallRankBound.Statement :=
  SmallRankBound.intersectionNumber_baseChange

theorem SmallRankWeakHypothesis.full : SmallRankWeakHypothesis.Statement :=
  SmallRankWeakHypothesis.intersectionNumber_baseChange

end RestTerms

end GroundTheory.Heights₂.Heights
end
