import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PAddHeightsridge
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatNmSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PDualBasisExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightedHomogeneousComponentMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VolumeFundamentalDomainEq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroAlt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroBis
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PHomogGeneratorsExist
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLatticeLineExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineDegreeBundle
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineIdealDual
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PPointHeightDegree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PReadsMul
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartPowNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemPointsOfGeneratorsVanish
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicNew
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsFormOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.NormSqEvalConeScale
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtMapLiftOldOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtVal
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightEqMapDomain
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AnalyticAtEvalConeComp
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousAeval
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroTer
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.BirationalOfBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousSepBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VarsSubsetRangeBlockIncl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.CardLeOfSeparated
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MonomialValuesOneBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusMetric
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSec
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSupSmall
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartFormEvalAgree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.HilbDegreeBoundAltOfStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousMonomialOf
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsOneBlockLinMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsNatMulIsIntegralFin
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LatticePointPairForms
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartRingDescriptionAltHolds
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeConj
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FiniteTwistsDegreeFormOfFirst
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemChartRingZOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemConePointsProjIdealIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.RenameBlockIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LocalChangeOfVectorSpace
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsLast

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem GeometricArithmeticNumbers.proof (hF : WeightedDegree.Statement) (hZ : FibreCompDimZ.Statement) :
    GeometricArithmeticNumbers.Statement := by
  intro ι _ _ n P D hdim a p hp
  rw [hF ι n P D hdim a p, NumbersDVR.cycEval, finsum_mem_def]
  refine finsum_congr fun W ↦ ?_
  by_cases hW : W ∈ Geo.divSupp (ι := blockIdx n) P.ideal (C (p : ℤ))
  · rw [Set.indicator_of_mem hW]
    have hW' : W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W := hW
    have hWp : W.IsPrime := hW.1.1.1
    have hpW : (C (p : ℤ) : MvPolynomial (Coord n) ℤ) ∈ W :=
      hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hC : Geo.IsMultiHomog (ι := blockIdx n) (C (p : ℤ) : MvPolynomial (Coord n) ℤ) 0 := by
      intro m hm k
      have h0 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h0
      split_ifs at h0 with h
      · subst h
        simp
      · exact absurd rfl h0
    have hMP : Geo.IsMultiProjPrime (ι := blockIdx n) W :=
      ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
        P.isMultiProjPrime.2.1 hC hW.1, hW.2⟩
    have hdimW : ringKrullDim (Geo.MRing (blockIdx n) ⧸ W) =
        ((D + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
      refine hZ (Coord n) P.ideal P.isPrime P.isHorizontal (D + Fintype.card ι) p hp.out ?_ W hW.1
      rw [show D + Fintype.card ι + 1 = D + 1 + Fintype.card ι by omega]
      exact hdim
    have hm : Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W =
        (NumbersDVR.multAt (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W).toNat := by
      rw [Geo.multAt, dif_pos hWp]
      rfl
    rw [NumbersDVR.divCycle, dif_pos hW', hm,
      Bridge.intNum_map_eq_geoNum p D W hMP hpW hdimW a]
  · have hW' : ¬(W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W) := hW
    rw [Set.indicator_of_notMem hW, NumbersDVR.divCycle, dif_neg hW', zero_mul]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem ArithVariety.isArithVar_of_ringKrullDim {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ι → ℕ} (P : ArithVariety n) {D : ℕ}
    (hdim : ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞)) :
    Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) :=
  ⟨inferInstance, P.isMultiProjPrime, P.isHorizontal, hdim⟩

theorem FibrePoints.proof (hG : GeometricArithmeticNumbers.Statement) : FibrePoints.Statement := by
  intro hDeg ι _ _ _ n P D hdim L hL
  have hP : Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) := P.isArithVar_of_ringKrullDim hdim
  have hfin := Geo.divSupp_finite (ι := blockIdx n) P.ideal (C ((2 : ℕ) : ℤ))
  rw [hDeg ι (blockIdx n) P.ideal D L 2 hP hL Nat.prime_two,
    hG ι n P D hdim (fun j ↦ (L j).a) 2]
  have hcast := (Int.castAddHom ℝ).map_finsum_mem
    (fun V ↦ (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C ((2 : ℕ) : ℤ)}) V : ℤ) *
      Geo.geoNum (ι := blockIdx n) D V (fun j ↦ (L j).a)) hfin
  simp only [Int.coe_castAddHom, Int.cast_mul, Int.cast_natCast] at hcast
  exact hcast.symm

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem ArithVariety.chartMonomial_mem_of_not_isLive (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)}
    (hc : ¬ P.IsLive c) {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  unfold ArithVariety.IsLive at hc
  push Not at hc
  obtain ⟨k, hk⟩ := hc
  unfold chartMonomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  exact P.ideal.mul_mem_right _ (P.ideal.pow_mem_of_mem hk _ (hd k))

theorem ChartCrossRatio.proof : ChartCrossRatio.Statement := by
  intro ι _ _ n P D d g hg c c' j
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
      ring
    · rw [hg.dead c' hc', mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr
      (P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc hg.pos))

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem YPlusArithVar.proof (hPrime : ChartPrimality.Statement) (hDim : ExtensionDimension.Statement) :
    YPlusArithVar.Statement := by
  intro ι _ _ n P D Ω _ y x' E hR hA
  obtain ⟨Q, hQ⟩ := hPrime ι n P D
  obtain ⟨_, _, _, hd⟩ := hA
  rw [← hR.ext_eq]
  refine ⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩
  rw [← hR.ideal_eq] at hd
  change ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _
  rw [hDim ι n P D]
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd
  rw [hd, Fintype.card_option]
  norm_cast

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem WeightedDegree.equiv :
    GroundTheory.Heights₂.Heights.WeightedDegree.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.WeightedDegree.Statement := by
  constructor
  · intro h ι _ _ n P D hD a p hp
    have := Fact.mk hp
    exact h ι n P D hD a p
  · intro h ι _ _ n P D hD a p hp
    exact h ι n P D hD a p hp.out

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

namespace HadamardGramBound

theorem linearIndependent_of_mem_span {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (v b : Fin r → E) (hv : LinearIndependent ℝ v)
    (hb : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) : LinearIndependent ℝ b := by
  have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ (Set.range b) (hb i)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = r := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have h2 : r ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := by
    have := Submodule.finrank_mono hle
    omega
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) ≤ r := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) b
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank]
  omega

theorem equiv : GroundTheory.Heights₂.Heights.HadamardGramBound.Statement ↔
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound.Statement := by
  constructor
  · intro hA E _ _ r v hv hn
    have key : ∀ b : Fin r → E, (∀ i, v i ∈ Submodule.span ℤ (Set.range b)) →
        0 ≤ -Real.log (Real.sqrt (gram b)) := by
      intro b hb
      obtain ⟨_, h1⟩ := hA E r v b hv hn hb
      rw [neg_nonneg]
      have h1' : gram b ≤ 1 := h1
      refine Real.log_nonpos (Real.sqrt_nonneg _) ?_
      simpa using Real.sqrt_le_sqrt h1'
    refine ⟨key v fun i ↦ Submodule.subset_span ⟨i, rfl⟩, fun b _ hb ↦ key b fun i ↦ ?_⟩
    have h := hb i
    rwa [← Submodule.span_int_eq_addSubgroupClosure] at h
  · intro hB V _ _ r v b hv hn hb
    have hbli := linearIndependent_of_mem_span v b hv hb
    have hpos : 0 < gram b := (Matrix.posDef_gram_of_linearIndependent hbli).det_pos
    have h := (hB V r v hv hn).2 b hbli fun i ↦ by
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      exact hb i
    rw [neg_nonneg, Real.log_nonpos_iff (Real.sqrt_nonneg _),
      Real.sqrt_le_left zero_le_one, one_pow] at h
    exact ⟨hpos, h⟩

end HadamardGramBound

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ChartCrossRatio.equiv :
    GroundTheory.Heights₂.Heights.ChartCrossRatio.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartCrossRatio.Statement := by
  constructor
  · intro h ι _ _ n P D G c c' j
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem c c' j
  · intro h ι _ _ n P D d g hg c c' j
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) c c' j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartDenominatorAlt.equiv :
    GroundTheory.Heights₂.Heights.ChartDenominatorAlt.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartDenominatorAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D G Γ
    obtain ⟨hpos, hsmooth⟩ :=
      hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    rw [den_eq G Γ]
    exact ⟨hsmooth, hpos⟩
  · intro hB ι _ _ n P D d g h r f δ hf
    obtain ⟨hsmooth, hpos⟩ :=
      hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem h)
        (GenSystem.ofIsHomogGenerators hf)
    rw [den_ofFormSystem h hf]
    exact ⟨hpos, hsmooth⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

theorem map_comp_extMap (D : Heights.AddBlockData P) :
    (MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P)).comp D.extMap =
      (mConeMap (AddBlockData.ofObjects D).yPlus).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    refine Eq.trans ?_ (map_intCast (mConeMap (AddBlockData.ofObjects D).yPlus) r).symm
    simp [Heights.AddBlockData.extMap]
  · intro v
    refine Eq.trans ?_ (MvPolynomial.aeval_X (R := ℤ)
      (fun p : Coord D.extSizes ↦ C ((AddBlockData.ofObjects D).yPlus p) * X p.1) v).symm
    rcases v with ⟨_ | k, i⟩
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        AddBlockData.ofObjects]
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        funFieldEquiv_mkF_X]

theorem ext_ofObjects (D : Heights.AddBlockData P) :
    (AddBlockData.ofObjects D).ext = D.extIdeal := by
  ext f
  show mConeMap (AddBlockData.ofObjects D).yPlus f = 0 ↔ D.extMap f = 0
  have h : MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P) (D.extMap f) =
      mConeMap (AddBlockData.ofObjects D).yPlus f :=
    RingHom.congr_fun (map_comp_extMap D) f
  constructor
  · intro h0
    apply MvPolynomial.map_injective _ (funFieldEquiv P).injective
    rw [map_zero]
    exact h.trans h0
  · intro h0
    exact h.symm.trans (by rw [h0, map_zero])

theorem ExtensionDimension.equiv :
    GroundTheory.Heights₂.Heights.ExtensionDimension.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ExtensionDimension.Statement := by
  constructor
  · intro h ι _ _ n P D
    obtain ⟨E, rfl⟩ : ∃ E, AddBlockData.ofObjects E = D :=
      ⟨AddBlockData.toObjects D, AddBlockData.ofObjects_toObjects D⟩
    rw [ext_ofObjects]
    exact h ι n P E
  · intro h ι _ _ n P D
    have := h ι n P (AddBlockData.ofObjects D)
    rw [ext_ofObjects] at this
    exact this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

theorem ChartFormsAlt.equiv :
    _root_.GroundTheory.Heights₂.Heights.ChartFormsAlt.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartFormsAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hA ι n P (toObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨g, hg⟩ := hd₀ d hd
    obtain ⟨G, hGd, -⟩ := (exists_chartForms_iff_isFormSystem D d g).2 hg
    exact ⟨G, hGd⟩
  · intro hB ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hB ι n P (ofObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨G, hGd⟩ := hd₀ d hd
    exact ⟨G.g, (isFormSystem_iff_exists_chartForms D d G.g).2 ⟨G, hGd, rfl⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open AddBlockEq

theorem ConePointsConverse.equiv :
    GroundTheory.Heights₂.Heights.ConePointsConverse.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ConePointsConverse.Statement := by
  constructor
  · intro hA ι _ _ n P D G z hz c hc
    have h := hA ι n P (split_model_to_place_model D) G.d G.g G.isFormSystem z hz c hc
    rw [addBlockEquiv_symm_conePoints] at h
    have e : (D.join z fun j ↦ evalCone z (G.g c j)) = (split_model_to_place_model D).joinPt z fun j ↦ evalCone z (G.g c j) := by
      funext o
      cases o <;> rfl
    rw [e]
    exact h
  · intro hB ι _ _ n P D d g hg z hz c hc
    have h := hB ι n P (toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hg) z hz c hc
    rw [extPoints_eq, ← addBlockEquiv_join]
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ConePoints.equiv :
    GroundTheory.Heights₂.Heights.ConePoints.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ConePoints.Statement := by
  constructor
  · intro hA ι _ _ n P D G
    obtain ⟨h1, h2⟩ := hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem
    refine ⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩
    · have e : (AddBlockData.toObjects D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
      have := h1 c i j
      rw [e] at this
      exact this
    · have e : (AddBlockData.toObjects D).extPoints = conePoints D.ext ℂ :=
        AddBlockEq.addBlockEquiv_symm_conePoints D
      rw [← e] at hw
      exact h2 w hw
  · intro hB ι _ _ n P D d g hg
    obtain ⟨h1, h2⟩ := hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg)
    have e : (AddBlockData.ofObjects D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    refine ⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩
    · have := h1 c i j
      rw [e] at this
      exact this
    · have e' : D.extPoints = conePoints (AddBlockData.ofObjects D).ext ℂ := AddBlockEq.extPoints_eq D
      rw [e'] at hw
      exact h2 w hw

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartPrimality.equiv :
    GroundTheory.Heights₂.Heights.ChartPrimality.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartPrimality.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hA ι n P (AddBlockEq.split_model_to_place_model D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_symm_extIdeal D)⟩
  · intro hB ι _ _ n P D
    obtain ⟨Q, hQ⟩ := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D)
    exact ⟨Q, hQ.trans (AddBlockEq.addBlockEquiv_extIdeal D)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem SectionCycle.equiv :
    GroundTheory.Heights₂.Heights.SectionCycle.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionCycle.Statement := by
  constructor
  · intro hA ι _ _ n P D G c j hg W
    have e : (AddBlockEq.split_model_to_place_model D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
    have h := hA ι n P (AddBlockEq.split_model_to_place_model D) G.d G.g G.isFormSystem c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h
  · intro hB ι _ _ n P D d g hfs c j hg W
    have e : (AddBlockEq.toIndefiniteRowSideFullHecke D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    have h := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hfs) c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ChartVanishing.equiv :
    GroundTheory.Heights₂.Heights.ChartVanishing.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartVanishing.Statement := by
  constructor
  · intro h ι _ _ n P D G z hz c
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem z hz c
  · intro h ι _ _ n P D d g hg z hz c
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) z hz c

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntDomainDim.full : IntDomainDim.Statement :=
  IntDomainDim.proof

theorem ConeTrdeg.full : ConeTrdeg.Statement :=
  ConeTrdeg.proof

theorem FibreCompDimZ.full : FibreCompDimZ.Statement :=
  FibreCompDimZ.proof

theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.proof

theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.proof

theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.proof

theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.proof

theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.proof

theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.proof

theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.proof

theorem HomogGeneratorsExist.full : HomogGeneratorsExist.Statement :=
  HomogGeneratorsExist.proof

theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.proof

theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.proof

theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.proof

theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.proof

theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.proof

theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.proof

theorem MonomialMapNorm.full : MonomialMapNorm.Statement :=
  MonomialMapNorm.proof

theorem SpanningAtDominantWeight.full : SpanningAtDominantWeight.Statement :=
  SpanningAtDominantWeight.proof

theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.proof

theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.proof

theorem SectionSmall.full : SectionSmall.Statement :=
  SectionSmall.proof

theorem DualBasisExists.full : DualBasisExists.Statement :=
  DualBasisExists.proof

theorem OneBlockStandard.full : OneBlockStandard.Statement :=
  OneBlockStandard.proof

theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.proof

theorem ChartLatSection.full : ChartLatSection.Statement :=
  ChartLatSection.proof

theorem ChartLatNmSection.full : ChartLatNmSection.Statement :=
  ChartLatNmSection.proof

theorem ReadsMul.full : ReadsMul.Statement :=
  ReadsMul.proof

theorem YPlusSec.full : YPlusSec.Statement :=
  YPlusSec.proof

theorem LineIdealDual.full : LineIdealDual.Statement :=
  LineIdealDual.proof

theorem IdealIndexPlaces.full : IdealIndexPlaces.Statement :=
  IdealIndexPlaces.proof

theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.proof ChartVanishing.full

theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.proof ChartVanishing.full

theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.proof ChartVanishing.full

theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.proof ChartDenominatorAlt.full ConePoints.full ChartCrossRatio.full

theorem PlurisubharmonicMetric.full : PlurisubharmonicMetric.Statement :=
  PlurisubharmonicMetric.proof ConePoints.full ChartMetric.full

theorem SectionNorm.full : SectionNorm.Statement :=
  SectionNorm.proof ConePoints.full ChartMetric.full

theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.proof ChartFormsAlt.full

theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.proof BlockSurjectivity.full

theorem BlockImage.full : BlockImage.Statement :=
  BlockImage.proof IntDomainDim.full ConeTrdeg.full

theorem GeometricArithmeticNumbers.full : GeometricArithmeticNumbers.Statement :=
  GeometricArithmeticNumbers.proof WeightedDegree.full FibreCompDimZ.full

theorem FibrePoints.full : FibrePoints.Statement :=
  FibrePoints.proof GeometricArithmeticNumbers.full

theorem LatticeLineExists.full : LatticeLineExists.Statement :=
  LatticeLineExists.proof OneBlockPoints.full

theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.proof OneBlockPoints.full LatticeLineExists.full LineIdealDual.full IdealIndexPlaces.full

theorem AddBlockBridge.full : AddBlockBridge.Statement :=
  AddBlockBridge.proof ChartLatSection.full

theorem YPlusArithVar.full : YPlusArithVar.Statement :=
  YPlusArithVar.proof ChartPrimality.full ExtensionDimension.full

theorem YPlusMetric.full : YPlusMetric.Statement :=
  YPlusMetric.proof ChartFormsAlt.full HomogGeneratorsExist.full ChartMetric.full ConePoints.full

theorem YPlusSmall.full : YPlusSmall.Statement :=
  YPlusSmall.proof ChartFormsAlt.full ConePointsConverse.full

theorem YPlusSupSmall.full : YPlusSupSmall.Statement :=
  YPlusSupSmall.proof ChartFormsAlt.full ConePoints.full

theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.proof (CoordConeArithVar.proof IntDomainDim.full)

end GroundTheory.Heights₂.Heights

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.equiv.mp GroundTheory.Heights₂.Heights.WeightedDegree.full

theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.equiv.mp GroundTheory.Heights₂.Heights.BoundedMonomials.full

theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.equiv.mp GroundTheory.Heights₂.Heights.HadamardGramBound.full

theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.equiv.mp GroundTheory.Heights₂.Heights.MonomialMap.full

theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.equiv.mp GroundTheory.Heights₂.Heights.OneBlockPoints.full

theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.equiv.mp GroundTheory.Heights₂.Heights.ChartRingDescription.full

theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.equiv.mp GroundTheory.Heights₂.Heights.ChartCrossRatio.full

theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartDenominatorAlt.full

theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.equiv.mp GroundTheory.Heights₂.Heights.ExtensionDimension.full

theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartFormsAlt.full

theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.equiv.mp GroundTheory.Heights₂.Heights.ChartMetric.full

theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.equiv.mp GroundTheory.Heights₂.Heights.ConePointsConverse.full

theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.equiv.mp GroundTheory.Heights₂.Heights.ConePoints.full

theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.equiv.mp GroundTheory.Heights₂.Heights.ChartPrimality.full

theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.equiv.mp GroundTheory.Heights₂.Heights.SectionCycle.full

theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.equiv.mp GroundTheory.Heights₂.Heights.SmallSections.full

theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.equiv.mp GroundTheory.Heights₂.Heights.ChartVanishing.full

theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.equiv.mp GroundTheory.Heights₂.Heights.BlockSurjectivity.full

theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.equiv.mp GroundTheory.Heights₂.Heights.SupNormEquality.full

theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.equiv.mp GroundTheory.Heights₂.Heights.SectionInjectivity.full

theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.equiv.mp GroundTheory.Heights₂.Heights.LatticePacking.full

theorem SectionNorm.full : SectionNorm.Statement :=
  (SectionNorm.equiv GroundTheory.Heights₂.Heights.ChartMetric.full).mp GroundTheory.Heights₂.Heights.SectionNorm.full

theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.hilbDegreeBound_alt_of_statement GroundTheory.Heights₂.Heights.LatticePointCount.full

theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.imp GroundTheory.Heights₂.Heights.OneBlockModel.full

theorem LineDegreeBundle.full : LineDegreeBundle.Statement :=
  LineDegreeBundle.proof

theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.forward LineDegreeBundle.full GroundTheory.Heights₂.Heights.PointHeightDegree.full

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end
