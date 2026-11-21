import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem BaseChangeLogBound.proof (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hC : ConeLogBound.Statement) : BaseChangeLogBound.Statement := by
  intro K _ _ n e δ h I f u σ hI hf hδ hu
  obtain ⟨hprime, c, hc, g, hg, heq⟩ := hB K n (e + 1) I f σ hI hf
  have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
    (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
  have hne : MvPolynomial.map σ f ≠ 0 := fun h0 =>
    hf.1 (map_injective σ σ.injective (by rw [h0, map_zero]))
  rw [heq] at hδσ hne
  obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδσ hne
  unfold cycleIntegral
  calc ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * coneIntegral h W e (fsLog h fun j => σ (u j))
      ≤ ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * (δW W * Real.log (h.norm fun j => σ (u j))) :=
        Finset.sum_le_sum fun W hW => mul_le_mul_of_nonneg_left
          (hC n e (δW W) h W (g W) _ (hprime W hW) (hg W hW) (hδW W hW) (hAv K n I u σ hI hu W hW))
          (Nat.cast_nonneg _)
    _ = δ * Real.log (h.norm fun j => σ (u j)) := by
        rw [← hsum]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W _ => ?_
        ring

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

theorem ChowFormSwap.full : ChowFormSwap.Statement := chowFormSwap

theorem GaussLemma.full : GaussLemma.Statement := gaussLemma

theorem MahlerMul.full : MahlerMul.Statement := mahlerMul

theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

theorem ChowHeightConst.full : ChowHeightConst.Statement := chowHeightConst

theorem ConeLogBound.of_leaves (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement :=
  ConeLogBound.proof hMass hFin hInt hNull

theorem BaseChangeLogBound.of_leaves (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) (hMass : ConeIntegralMass.Statement)
    (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : BaseChangeLogBound.Statement :=
  BaseChangeLogBound.proof hB hAv (ConeLogBound.proof hMass hFin hInt hNull)

theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

theorem ChowHeightLowerBound.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ChowHeightLowerBound.Statement :=
  chowHeightLowerBound_of (ChowHeightRecursion.proof hV hA hB hAv) hS
    (BaseChangeLogBound.of_leaves hB hAv hMass hFin hInt hNull) ChowHeightMul.full

theorem ChowHeightCharacterised.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hPt : ProjPrimeHasPoint.Statement) : ChowHeightCharacterised.Statement :=
  ChowHeightCharacterised.proof (ChowHeightRecursion.proof hV hA hB hAv) hS ChowHeightMul.full hPt

end GroundTheory.Heights₂.Heights
end
