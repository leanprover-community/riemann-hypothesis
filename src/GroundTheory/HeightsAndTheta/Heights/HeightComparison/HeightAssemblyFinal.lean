import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Height
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitArchSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterZero
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterLe
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.of_parts (hV : OrbitDivVertical.Statement)
    (hF : OrbitFiniteSum.Statement) (hA : OrbitArchSum.Statement) :
    HeightAsIntersection.Statement :=
  HeightAsIntersection.proof OrbitCurve.full OrbitDegree.full (HeightRecR.proof hV hF hA)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem OrbitArchSum.of_conjSum (hB : OrbitConjSum.Statement) : OrbitArchSum.Statement := by
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, ha, hsa, -⟩ := hs
  have hinv : ∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) →
      Geo.logNorm A.toGeo s (fun p ↦ c p.1 * z p) = Geo.logNorm A.toGeo s z := by
    intro c z hc _
    rw [Geo.logNorm, Geo.logNorm, A.toGeo.smul c z hc, eval_smul_of_isMultiHomog s a hsa c z,
      norm_mul, norm_prod]
    simp only [ha, zpow_natCast, norm_pow]
    rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))]
  have hfin := (Nat.card_pos_iff.mp (OrbitDegree.full ι n x hx)).2
  have e0 : (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j).h z)) =
      (Fin.elim0 : Fin 0 → (Coord n → ℂ) → ℝ) := funext fun j ↦ j.elim0
  have hB' := hB ι n x _ hx hinv
  rw [Geo.arInt, e0, PtsIntegralPoints.homogProof ι (blockIdx n) _ _
    (OrbitCurve.isMultiHomogIdeal_orbitIdeal x) hfin hinv]
  have hterm : ∀ σ : coordField x →+* ℂ,
      Geo.logNorm A.toGeo s (fun p ↦ σ (coordVec x p.1 p.2)) =
        Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) := by
    intro σ
    rw [Geo.logNorm, ← eval_map_flatCone]
    rw [A.toGeo_h_of_blockNonzero (w := fun p ↦ σ (coordVec x p.1 p.2)) (blockNonzero_sigma hx σ)]
    rfl
  simp only [hterm] at hB'
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_mul_eq_mul_div, hB', mul_div_cancel_left₀ _ hK.ne']

theorem HeightAsIntersection.of_orbit_parts (hD : OrbitDegreeRatio.Statement)
    (hL : OrbitLocalSum.Statement) (hZ : OrbitCenterZero.Statement)
    (hB : OrbitConjSum.Statement) : HeightAsIntersection.Statement :=
  HeightAsIntersection.of_parts OrbitDivVertical.proof (OrbitFiniteSum.proof hD hL hZ)
    (OrbitArchSum.of_conjSum hB)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.of_chart_and_centre (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement)
    (hLe : OrbitCenterLe.Statement) (hIff : OrbitCenterMemIff.Statement)
    (hDiv : OrbitCenterDivSupp.Statement) : HeightAsIntersection.Statement :=
  HeightAsIntersection.of_orbit_parts OrbitDegreeRatio.proof
    (OrbitLocalSum.proof hR hM hF hU hP hC hS hT) (OrbitCenterZero.proof hLe hIff hDiv)
    OrbitConjSum.proof

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightAsIntersection.full : HeightAsIntersection.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightAsIntersection.of_chart_and_centre OrbitChartRing.proof hM
    (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
    OrbitChartMult.proof
    (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
      (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
    OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof OrbitCenterLe.proof hIff
    (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)

end GroundTheory.Heights₂.Heights
end
