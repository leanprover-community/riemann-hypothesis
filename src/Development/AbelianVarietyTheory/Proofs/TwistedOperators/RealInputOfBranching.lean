import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoostDecompositionNormBoundOfEmbeddingLaws
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryNearIdentityEqExpLogBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsLieIff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientProjection
import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeighted
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayleyA
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_stabiliser_embedding_norm_laws : EmbLaws := by
  first | exact @GlobalTheory.SepReal.embLaws | exact GlobalTheory.SepReal.embLaws | (intros; apply GlobalTheory.SepReal.embLaws <;> assumption)
end

section
open MeasureTheory

namespace GlobalTheory.SeparatedSetCardBound

theorem card_le_of_separated {G E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : G → E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (T : Finset G)
    (hT : ∀ h ∈ T, ‖φ h‖ ≤ R) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖) :
    (T.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  haveI := hμ
  set d := Module.finrank ℝ E
  have hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_iff]
    rintro z ⟨hza, hzb⟩
    have hs := hsep a ha b hb hab
    rw [Metric.mem_ball, dist_eq_norm] at hza hzb
    have h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖ := by
      calc ‖φ a - φ b‖ = ‖(z - φ b) - (z - φ a)‖ := by congr 1; abel
        _ ≤ ‖z - φ b‖ + ‖z - φ a‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖ := by
      calc ‖z‖ = ‖(z - φ h) + φ h‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - φ h‖ + ‖φ h‖ := norm_add_le _ _
    linarith [hT h hh]
  have hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [div_pow, le_div_iff₀ hrd]
  exact hle

theorem main : ∀ {G E : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.SFinite μ] [inst_8 : NormedAddCommGroup E] [inst_9 : NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E), Continuous φ → ∀ (W : Set G) (R r : ℝ), (0 : ℝ) ≤ R → (0 : ℝ) < r → (∀ (g h : G), ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ (2 : ℝ) * r → h⁻¹ * g ∈ W) → (μ : Set G → ENNReal) {g : G | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * (μ : Set G → ENNReal) W := by
  intro G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW
  classical
  let P : Finset G → Prop := fun T =>
    (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖
  let A : Set ℕ := {n | ∃ T, P T ∧ T.card = n}
  have hA0 : A.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hAb : BddAbove A := by
    refine ⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨T, hT, rfl⟩
    have h1 := card_le_of_separated φ R r hR hr T hT.1 hT.2
    have h2 := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨T, hT, hTc⟩ := Nat.sSup_mem hA0 hAb
  have hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W := by
    intro g hg
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne
    have hg' : ‖φ g‖ ≤ R := hg
    have hgT : g ∉ T := fun hgT => hne g hgT (hW g g hg' (by simp; positivity))
    have far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖ := by
      intro h hh
      by_contra hle
      push_neg at hle
      exact hne h hh (hW g h (hT.1 h hh) hle)
    have hP : P (insert g T) := by
      refine ⟨?_, ?_⟩
      · intro h hh
        rw [Finset.mem_insert] at hh
        rcases hh with rfl | hh
        · exact hg'
        · exact hT.1 h hh
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact far b hb
        · rw [norm_sub_rev]; exact far a ha
        · exact hT.2 a ha b hb hab
    have hmem : (insert g T).card ∈ A := ⟨_, hP, rfl⟩
    have hle := le_csSup hAb hmem
    rw [Finset.card_insert_of_notMem hgT, ← hTc] at hle
    omega
  calc μ {g : G | ‖φ g‖ ≤ R} ≤ μ (⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W) := measure_mono hcover
    _ ≤ ∑ h ∈ T, μ ((fun x => h⁻¹ * x) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = T.card * μ W := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)

end GlobalTheory.SeparatedSetCardBound
end

section
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.VolBallPf

theorem double_count {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E) (hφ : Continuous φ) (W : Set G) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 < r) (hW : ∀ g h, ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ 2 * r → h⁻¹ * g ∈ W) :
    μ {g | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
  first
  | exact @_root_.GlobalTheory.SeparatedSetCardBound.main
  | exact _root_.GlobalTheory.SeparatedSetCardBound.main
  | (apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)

def toEuc {m : ℕ} (A : Mat m) : EuclideanSpace ℂ (Fin m × Fin m) := WithLp.toLp 2 fun p => A p.1 p.2

theorem norm_vec {m : ℕ} (A : Mat m) : ‖toEuc A‖ = hsn A := by
  simp [toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem toEuc_sub {m : ℕ} (A B : Mat m) : toEuc A - toEuc B = toEuc (A - B) := by
  ext p; simp [toEuc]

theorem continuous_vec {m : ℕ} : Continuous (toEuc : Mat m → _) := by
  unfold toEuc
  fun_prop

theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hsn (umat g⁻¹) = hsn (umat g) := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := determinant_character_mul_inv g
  have h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
    calc umat g⁻¹ = Jm ε * Jm ε * umat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
      _ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg]
      _ = Jm ε * (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [h2]
  unfold hsn
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem hsn_mul {m : ℕ} (A B : Mat m) : hsn (A * B) ≤ hsn A * hsn B := sqrt_frobenius_mul_le A B

theorem hsn_add {m : ℕ} (A B : Mat m) : hsn (A + B) ≤ hsn A + hsn B := sqrt_frobenius_add_le A B

end GlobalTheory.SepReal.VolBallPf

namespace GlobalTheory.SepReal

open VolBallPf

theorem volBall : VolBall := by
  intro m ε δ R hδ hR
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix m ε).1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ} :=
      isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const
    refine lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)
    · simpa [norm_vec, hsn, umat] using hδ
    · have : ‖toEuc (umat g - 1)‖ < δ := hg
      rw [norm_vec] at this
      exact this.le
  · refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))
    have h1 : hsn (umat g - 1) ≤ δ := hg
    have h2 := hsn_add (umat g - 1) 1
    rw [sub_add_cancel] at h2
    have h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m) := by linarith
    exact (Real.sqrt_le_iff.1 h3).2
  · have key := double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le
      (by positivity) (fun g h hh hgh => by
        rw [norm_vec] at hh
        rw [toEuc_sub, norm_vec] at hgh
        show hsn (umat (h⁻¹ * g) - 1) ≤ δ
        have h1 : umat h⁻¹ * umat h = 1 := by
          have := determinant_character_mul_inv h⁻¹
          rw [inv_inv] at this
          exact this
        have h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h) := by
          rw [Matrix.mul_sub, h1]; rfl
        rw [h2]
        refine (hsn_mul _ _).trans ?_
        rw [hsn_inv]
        calc hsn (umat h) * hsn (umat g - umat h) ≤ R * (2 * (δ / (2 * R))) :=
              mul_le_mul hh hgh (Real.sqrt_nonneg _) hR.le
          _ = δ := by field_simp)
    have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2 := by
      rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [sq]
    have hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ := by field_simp; ring
    simp only [norm_vec, hfr, hq] at key
    exact key

end GlobalTheory.SepReal

end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_of_ball_bound : VolBall := by
  atlas_forward_decl GlobalTheory.SepReal.volBall
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.powerIntegrability

theorem one_le_hsn {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hsn (umat g) := by
  set a : Fin m := ⟨0, hm⟩
  have h : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h2 := congrFun (congrFun h a) a
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at h2
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] at h2
  have hn : (1 : ℝ) ≤ ∑ l, ‖umat g l a‖ ^ 2 := by
    have e1 : ‖((if ε a = true then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
    rw [← e1, ← h2]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp [sq]
  have hc : ∑ l, ‖umat g l a‖ ^ 2 ≤ ∑ l, ∑ b, ‖umat g l b‖ ^ 2 :=
    Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun b => ‖umat g l b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)
  unfold hsn
  exact Real.one_le_sqrt.mpr (hn.trans hc)

theorem continuous_hsn_umat {m : ℕ} (ε : Fin m → Bool) : Continuous fun g : UJ ε => hsn (umat g) := by
  unfold hsn
  have hu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hu)).norm.pow 2

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal.powerIntegrability

theorem const_le (m : ℕ) (hm : 1 ≤ m) : 2 * (33 : ℝ) ^ (2 * m ^ 2) ≤ Real.exp (10 * (m : ℝ) ^ 2) := by
  have hk : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have e1 : Real.exp (10 * (m : ℝ) ^ 2) = Real.exp 10 ^ (m ^ 2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have e10 : (2178 : ℝ) ≤ Real.exp 10 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (2178 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1.le 10
  have e2 : (33 : ℝ) ^ (2 * m ^ 2) = 1089 ^ (m ^ 2) := by rw [pow_mul]; norm_num
  rw [e1, e2]
  calc 2 * (1089 : ℝ) ^ (m ^ 2) ≤ 2 ^ (m ^ 2) * 1089 ^ (m ^ 2) := by
        gcongr; exact le_self_pow₀ (by norm_num) (by omega)
    _ = 2178 ^ (m ^ 2) := by rw [← mul_pow]; norm_num
    _ ≤ Real.exp 10 ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) e10 _

theorem term_le (m : ℕ) (A : ℝ) (hA : 4 * (m : ℝ) ^ 2 + 1 ≤ A) (j : ℕ) :
    ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2) ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hb : 1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4) ≤ 33 * 4 ^ j := by
    have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]; ring
    rw [this]; linarith
  have hr0 : 0 ≤ (2 : ℝ) ^ (-A) := by positivity
  have hq : (2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2) ≤ 1 / 2 := by
    have e : (4 : ℝ) ^ (2 * m ^ 2) = (2 : ℝ) ^ ((4 * m ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    rw [e, ← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (-A + ((4 * m ^ 2 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  calc ((2 : ℝ) ^ (-A)) ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)
      ≤ ((2 : ℝ) ^ (-A)) ^ j * (33 * 4 ^ j) ^ (2 * m ^ 2) := by
        gcongr
    _ = 33 ^ (2 * m ^ 2) * ((2 : ℝ) ^ (-A) * 4 ^ (2 * m ^ 2)) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j]; ring
    _ ≤ 33 ^ (2 * m ^ 2) * (1 / 2) ^ j := by
        gcongr

end GlobalTheory.SepReal.powerIntegrability

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.powerIntegrability in

theorem powInt_of_volBall : VolBall → PowInt := by
  intro hV m ε A hm hA
  obtain ⟨-, hfin, -⟩ := hV m ε (1 / 4) 1 (by norm_num) one_pos
  set μN := muG ε (nbh ε (1 / 4)) with hμN
  set r : ℝ := (2 : ℝ) ^ (-A) with hr
  have hcont := continuous_hsn_umat ε
  have hpos : ∀ g : UJ ε, 0 < hsn (umat g) := fun g => lt_of_lt_of_le one_pos (one_le_hsn hm g)
  have hf_cont : Continuous fun g : UJ ε => hsn (umat g) ^ (-A) :=
    hcont.rpow_const fun g => Or.inl (hpos g).ne'
  have hf_nn : ∀ g : UJ ε, 0 ≤ hsn (umat g) ^ (-A) := fun g => (Real.rpow_pos_of_pos (hpos g) _).le
  let S : ℕ → Set (UJ ε) := fun j => {g | hsn (umat g) ≤ (2 : ℝ) ^ (j + 1)}
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hcont.measurable measurable_const
  have hpt : ∀ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g := by
    intro g
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (one_le_hsn hm g) (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show g ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    have key : r ^ j = ((2 : ℝ) ^ j) ^ (-A) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [key]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith [sq_nonneg (m : ℝ)])
  have hL : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε ≤ ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
    calc ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε
        ≤ ∫⁻ g, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε := lintegral_mono hpt
      _ = ∑' j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (r ^ j)) g ∂muG ε :=
          lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (r ^ j) * muG ε (S j) := by
          congr 1; funext j; exact lintegral_indicator_const (hS j) _
      _ ≤ ∑' j, ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hb := (hV m ε (1 / 4) ((2 : ℝ) ^ (j + 1)) (by norm_num) (by positivity)).2.2
          calc ENNReal.ofReal (r ^ j) * muG ε (S j)
              ≤ ENNReal.ofReal (r ^ j) * (ENNReal.ofReal ((1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN) :=
                by gcongr
            _ = ENNReal.ofReal (r ^ j * (1 + 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 / (1 / 4)) ^ (2 * m ^ 2)) * μN := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (33 ^ (2 * m ^ 2) * (1 / 2) ^ j) * μN := by
                exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (term_le m A hA j)) (zero_le')
            _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * 2⁻¹ ^ j * μN := by
                have h2 : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = 2⁻¹ ^ j := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_mul (by positivity), h2]
      _ = ENNReal.ofReal (33 ^ (2 * m ^ 2)) * (∑' j : ℕ, (2⁻¹ : ENNReal) ^ j) * μN := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (2 : ENNReal)]
  have hLfin : ∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε < ⊤ :=
    lt_of_le_of_lt hL (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hnn : 0 ≤ᵐ[muG ε] fun g => hsn (umat g) ^ (-A) := Filter.Eventually.of_forall hf_nn
  refine ⟨⟨hf_cont.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hLfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_cont.aestronglyMeasurable]
  calc (∫⁻ g, ENNReal.ofReal (hsn (umat g) ^ (-A)) ∂muG ε).toReal
      ≤ (ENNReal.ofReal (2 * 33 ^ (2 * m ^ 2)) * μN).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hL
    _ = 2 * 33 ^ (2 * m ^ 2) * μN.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Real.exp (10 * (m : ℝ) ^ 2) * μN.toReal :=
        mul_le_mul_of_nonneg_right (const_le m hm) ENNReal.toReal_nonneg

end GlobalTheory.SepReal

end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume : VolBall → PowInt := by
  atlas_forward_decl GlobalTheory.SepReal.powInt_of_volBall
end

section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.Folding

theorem inUJ_inv_left {m : ℕ} {ε : Fin m → Bool} {M : Mat m} (hM : M ∈ UJset ε) :
    (Jm ε * Mᴴ * Jm ε) * M = 1 := by
  have h : Mᴴ * Jm ε * M = Jm ε := hM
  calc Jm ε * Mᴴ * Jm ε * M = Jm ε * (Mᴴ * Jm ε * M) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jm_mul_self]

theorem inUJ_inv_right {m : ℕ} {ε : Fin m → Bool} {M : Mat m} (hM : M ∈ UJset ε) :
    M * (Jm ε * Mᴴ * Jm ε) = 1 := mul_eq_one_comm.mp (inUJ_inv_left hM)

def mk {m : ℕ} {ε : Fin m → Bool} (M : Mat m) (hM : M ∈ UJset ε) : UJ ε :=
  ⟨⟨M, Jm ε * Mᴴ * Jm ε, inUJ_inv_right hM, inUJ_inv_left hM⟩, hM⟩

theorem umat_mem {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : umat g ∈ UJset ε := g.2

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

end Frob

theorem continuous_umat {m : ℕ} {ε : Fin m → Bool} : Continuous (umat : UJ ε → Mat m) :=
  Units.continuous_val.comp continuous_subtype_val

variable {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

def iota (hmem : ∀ h ∈ UJset ε', embH e h ∈ UJset ε) (hmul : ∀ h h', embH e (h * h') = embH e h * embH e h') :
    UJ ε' →* UJ ε where
  toFun h := mk (embH e (umat h)) (hmem _ (umat_mem h))
  map_one' := by
    apply Subtype.ext; apply Units.ext
    exact embH_one e
  map_mul' h h' := by
    apply Subtype.ext; apply Units.ext
    exact hmul _ _

end GlobalTheory.SepReal.Folding

namespace GlobalTheory.SepReal.Folding

variable {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

end GlobalTheory.SepReal.Folding
end
end

section
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.PowDec

theorem hsn_sq_le {m : ℕ} (g : Mat m) : hsn g ^ 2 ≤ m * Real.exp (2 * GlobalTheory.Count.dHS g) := by
  have hA := Matrix.isHermitian_conjTranspose_mul_self g
  have h1 : hsn g ^ 2 = ∑ j, hA.eigenvalues j := by
    have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
    rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace,
      hA.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  rw [h1]
  have hle : ∀ j, hA.eigenvalues j ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
    intro j
    have hx : |Real.log (hA.eigenvalues j) / 2| ≤ GlobalTheory.Count.dHS g := by
      unfold GlobalTheory.Count.dHS
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun i => (Real.log (hA.eigenvalues i) / 2) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rcases le_or_gt (hA.eigenvalues j) 0 with h0 | h0
    · exact h0.trans (Real.exp_pos _).le
    · calc hA.eigenvalues j = Real.exp (2 * (Real.log (hA.eigenvalues j) / 2)) := by
            rw [show 2 * (Real.log (hA.eigenvalues j) / 2) = Real.log (hA.eigenvalues j) by ring,
              Real.exp_log h0]
        _ ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
            apply Real.exp_le_exp.2
            linarith [le_abs_self (Real.log (hA.eigenvalues j) / 2)]
  calc ∑ j, hA.eigenvalues j ≤ ∑ _j : Fin m, Real.exp (2 * GlobalTheory.Count.dHS g) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = m * Real.exp (2 * GlobalTheory.Count.dHS g) := by simp

theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : 0 < hsn g := by
  unfold hsn
  apply Real.sqrt_pos.2
  by_contra hle
  push_neg at hle
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := le_antisymm hle (by positivity)
  have hg0 : g = 0 := by
    ext a b
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
    have h2 := hsum a (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h2
    simpa using h2 b (Finset.mem_univ _)
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  rw [hg0] at hJ
  have := congrFun (congrFun hJ ⟨0, hm⟩) ⟨0, hm⟩
  simp [Jm] at this
  split_ifs at this <;> simp at this

theorem hsn_sq_definite {m : ℕ} {ε : Fin m → Bool} (hq : GlobalTheory.Count.rkR ε = 0) {g : Mat m} (hg : g ∈ UJset ε) :
    hsn g ^ 2 = m := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have hJc : Jm ε = 1 ∨ Jm ε = -1 := by
    unfold GlobalTheory.Count.rkR at hq
    rcases Nat.min_eq_zero_iff.1 hq with h | h
    · right
      have hf : ∀ a, ε a = false := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = true := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
    · left
      have hf : ∀ a, ε a = true := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = false := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
  have hu : gᴴ * g = 1 := by
    rcases hJc with h | h
    · rw [h, Matrix.mul_one] at hJ; exact hJ
    · rw [h] at hJ
      have : -(gᴴ * g) = -1 := by simpa [Matrix.mul_neg, Matrix.neg_mul] using hJ
      exact neg_inj.1 this
  have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
  rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hu]
  simp

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal.PowDec

theorem rkR_le {m : ℕ} (ε : Fin m → Bool) : GlobalTheory.Count.rkR ε ≤ m := by
  unfold GlobalTheory.Count.rkR
  exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))

theorem gap_ok {m : ℕ} (hm : 1 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ≤ m := by exact_mod_cast rkR_le ε
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have h2 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : 0 ≤ (m : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 120 * m)]

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.PowDec in

theorem decPow : DecPow := by
  intro m ε lam B hm hlam hgap _ H _ _ π hπ v₀ hv₀ g hg
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hdec := (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap m ε lam H π hlam hπ
    (1000 * (m : ℝ) ^ 3) hgap (gap_ok (by omega) ε) g hg v₀ hv₀.2 v₀ hv₀.2).1
  rw [hv₀.1, mul_one, mul_one] at hdec
  unfold GlobalTheory.Dec.decHS at hdec
  set t := GlobalTheory.Count.dHS g with ht
  set q := GlobalTheory.Count.rkR ε with hqdef
  have hx := hsn_pos (by omega) hg
  set A : ℝ := 40 * (m : ℝ) ^ 2 with hA
  have hpow : hsn g ^ (-A) = Real.exp (Real.log (hsn g) * (-A)) := Real.rpow_def_of_pos hx _
  rw [hpow, ← Real.exp_add]
  refine hdec.trans (Real.exp_le_exp.2 ?_)
  have hlogm : Real.log m ≤ m := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  ·
    have hs2 := hsn_sq_definite hq hg
    have hL : 2 * Real.log (hsn g) = Real.log m := by
      rw [← Real.log_rpow hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hs2]
    have hM : min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) = 0 := by
      rw [hq]; simp; positivity
    rw [hM]
    nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  · have hs2 := hsn_sq_le g
    have hL : 2 * Real.log (hsn g) ≤ Real.log m + 2 * t := by
      have h1 : Real.log (hsn g ^ 2) ≤ Real.log (m * Real.exp (2 * t)) := Real.log_le_log (by positivity) hs2
      rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
      push_cast at h1; linarith
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqm : (q : ℝ) ≤ m := by exact_mod_cast rkR_le ε
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hsq : Real.sqrt (2 * (q : ℝ)) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hsq0 : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by positivity)

    have hkey : t - 1 ≤ (m : ℝ) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := by
      rcases le_total t 1 with h1 | h1
      · have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
        nlinarith
      · have a1 : t ≤ (m : ℝ) * t ^ 2 := by nlinarith
        have a2 : t ≤ (m : ℝ) * (t / Real.sqrt (2 * (q : ℝ))) := by
          rw [mul_div_assoc', le_div_iff₀ hsq0]; nlinarith
        rcases min_choice (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) with e | e <;> rw [e] <;> linarith
    have hL' : Real.log (hsn g) * A ≤ 20 * (m : ℝ) ^ 3 + 40 * (m : ℝ) ^ 2 * t := by
      rw [hA]
      nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2),
        mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 20 * (m : ℝ) ^ 2)]
    have hk2 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 125 * (m : ℝ) ^ 2)
    nlinarith

end GlobalTheory.SepReal

end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay : DecPow := by
  atlas_forward_decl GlobalTheory.SepReal.decPow
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.LieWords

theorem dR_eq_dAct {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mat m → (H →L[ℂ] H)) : dR π = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π := by
  funext X w
  unfold dR GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit
  congr 1

theorem one_le_of_bound {m : ℕ} (hm : 3 ≤ m) {lam : Fin m → ℝ} (hc : IsHCParam lam) {B : ℝ}
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ B := by
  have hint : ∀ a c : Fin m, a < c → 1 ≤ lam a - lam c := by
    intro a c hac
    obtain ⟨ka, hka⟩ := hc.2 a
    obtain ⟨kc, hkc⟩ := hc.2 c
    have e : lam a - lam c = ((ka - kc : ℤ) : ℝ) := by push_cast; linarith
    have hpos : (0 : ℝ) < ((ka - kc : ℤ) : ℝ) := by rw [← e]; linarith [hc.1 hac]
    have h1 : (0 : ℤ) < ka - kc := by exact_mod_cast hpos
    have h2 : (1 : ℝ) ≤ ((ka - kc : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have h01 := hint ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h12 := hint ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have a0 := abs_le.mp (hB ⟨0, by omega⟩)
  have a2 := abs_le.mp (hB ⟨2, by omega⟩)
  linarith [a0.1, a0.2, a2.1, a2.2]

theorem stepConst_le {m : ℕ} (hm : 3 ≤ m) {B : ℝ} (hB : 1 ≤ B) (P : ℕ) (hP : P ≤ m + 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) P ≤ (8 * (m : ℝ) * B) ^ 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
  rw [Real.sq_sqrt hB0]
  have h12 : (m : ℝ) ^ (1 / 2 : ℝ) ≤ m := by
    calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m := Real.rpow_one _
  have h32 : (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have hPr : (P : ℝ) ≤ m + 1 := by exact_mod_cast hP
  have a1 : (m : ℝ) ^ (1 / 2 : ℝ) * B ≤ m * B := mul_le_mul_of_nonneg_right h12 hB0
  have hmB : 1 ≤ (m : ℝ) * B := by nlinarith
  have a2 : (m : ℝ) * B ≤ (m * B) ^ 2 := by nlinarith
  have a3 : (m : ℝ) ^ 2 ≤ (m * B) ^ 2 := by
    have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
    rw [mul_pow]
    calc (m : ℝ) ^ 2 = (m : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
  have a4 : 3 * (P : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have e : (8 * (m : ℝ) * B) ^ 2 = 64 * (m * B) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg ((m : ℝ) * B)]

theorem rk_le {m : ℕ} (hm : 3 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hrk : GlobalTheory.Count.rkR ε ≤ m := by
    unfold GlobalTheory.Count.rkR
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrk) (by norm_num)
  have h32 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have h0 : 0 ≤ ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have h2 : 120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (m : ℝ) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h32) (by positivity)
  nlinarith

end GlobalTheory.SepReal.LieWords

open GlobalTheory.SepReal.LieWords in

theorem GlobalTheory.SepReal.lieBound : LieBound := by
  intro m ε lam B hm hc hgap hB H _ _ π hDS v₀ hv₀
  haveI : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) π := hDS.2.2.1
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hgap2 : ∀ a b : Fin m, ε a ≠ ε b → 2 * (m : ℝ) < |lam a - lam b| := by
    intro a b hab
    have h := hgap a b hab
    nlinarith [sq_nonneg (m : ℝ)]
  have hK := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub m ε lam H π hc hDS hgap2
  have hZ := GlobalTheory.DSId.LowCharGap.lowChar m ε lam H π hc hDS _ hgap (rk_le hm ε)
  have hB1 : 1 ≤ B := one_le_of_bound hm hc hB
  have hb : ∀ a, |lam a| ≤ (Real.sqrt B) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; exact hB
  have hSB := GlobalTheory.StepBoundOneRep.stepBound_of_eigen m ε H π lam (Real.sqrt B) hU hK hZ hb
  refine ⟨?_, ?_⟩
  · have hs := GlobalTheory.StepBoundOneRep.smooth_of_mem_lowKSub ε lam π hU hK v₀ hv₀.2
    have hJ : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (Jm_mul_self ε))
    exact (GlobalTheory.SmChart.smV_iff_smoothOnH hJ hU.1 v₀).2 hs
  · rw [dR_eq_dAct]
    intro l
    induction l with
    | nil => intro _ _; simp [hv₀.1]
    | cons X l ih =>
      intro hl hlen
      have hX : inG ε X := hl X List.mem_cons_self
      have hl' : ∀ Y ∈ l, Y ∈ lieOf (Jm ε) := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hlen' : l.length ≤ m + 2 := by simp at hlen; omega
      have hmem : l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam π l.length :=
        Submodule.subset_span ⟨l, v₀, le_rfl, hl', hv₀.2, rfl⟩
      have h1 := (hSB l.length).2.2.2 X hX _ hmem
      have hcst := stepConst_le hm hB1 l.length (by simp at hlen; omega)
      have hrest := ih hl' hlen'
      have hsq : Real.sqrt (hs X) = hsn X := rfl
      have hh : 0 ≤ hsn X := Real.sqrt_nonneg _
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      calc ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π X (l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀)‖
          ≤ Real.sqrt (hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) l.length *
              ‖l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀‖ := h1
        _ ≤ ((8 * (m : ℝ) * B) ^ 2 * hsn X) * (l.map fun X => (8 * (m : ℝ) * B) ^ 2 * hsn X).prod := by
          rw [hsq]
          refine mul_le_mul ?_ hrest (norm_nonneg _) (by positivity)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hcst hh
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_lieWord_normBound : LieBound := by
  atlas_forward_decl GlobalTheory.SepReal.lieBound
end

section
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

open scoped ContDiff

namespace GlobalTheory.SepReal

theorem expS_mem_UJset {m : ℕ} {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.MainNotions.S.UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, neg_mul]
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  have hc : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hJu, hJinv]
  have hcomm : Commute (-(t • X)) (t • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-(t • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp (t • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem orbit_sub_le {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π) {X : Mat m}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) {v : H} (hv : SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v) :
    ‖π (NormedSpace.exp X) v - v‖ ≤ ‖dR π X v‖ := by
  set f : ℝ → H := fun s => π (NormedSpace.exp (s • X)) v with hf
  have hcd : ContDiff ℝ ∞ f := by
    have h1 := hv 1 (fun _ => X) (fun _ => hX)
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    have h3 := h1.comp h2
    convert h3 using 1
    funext s
    simp [f, List.ofFn_succ]
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt f (π (NormedSpace.exp (t • X)) (dR π X v)) t := by
    intro t
    set Lt := π (NormedSpace.exp (t • X)) with hLt
    have h0 : HasDerivAt f (dR π X v) 0 := (hdiff 0).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (Lt.restrictScalars ℝ) (f u)) ((Lt.restrictScalars ℝ) (dR π X v)) (t - t) := by
      rw [sub_self]; exact (Lt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := h1.comp_sub_const t t
    have hfun : f = fun s : ℝ => (Lt.restrictScalars ℝ) (f (s - t)) := by
      funext s
      have he : NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
        congr 2; ring
      simp only [f, he, hπ.1.2 _ (expS_mem_UJset hX t) _ (expS_mem_UJset hX (s - t))]
      rfl
    rw [hfun]
    exact h2
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => π (NormedSpace.exp (t • X)) (dR π X v)) (C := ‖dR π X v‖)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hπ.2.1 _ (expS_mem_UJset hX t) _))
  simpa [f, hπ.1.1] using hb

end GlobalTheory.SepReal

namespace GlobalTheory.SepReal

theorem exists_lowUnit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)} (hds : IsDS ε lam π) : ∃ v, IsLowUnit ε lam π v := by
  obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    simp [norm_smul, this]
  · exact (le_sSup hS : S ≤ lowKSub ε lam π) (S.smul_mem _ hvS)

theorem one_le_eightMB {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 3 ≤ m) (hlam : IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ 8 * (m : ℝ) * B := by
  have i0 : 0 < m := by omega
  have i1 : 1 < m := by omega
  have hlt : lam ⟨1, i1⟩ < lam ⟨0, i0⟩ := hlam.1 (show (⟨0, i0⟩ : Fin m) < ⟨1, i1⟩ from by simp [Fin.lt_def])
  obtain ⟨k0, hk0⟩ := hlam.2 ⟨0, i0⟩
  obtain ⟨k1, hk1⟩ := hlam.2 ⟨1, i1⟩
  have hk : (k1 : ℝ) < k0 := by linarith
  have hk' : k1 < k0 := by exact_mod_cast hk
  have hk'' : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hk'
  have h0 := hB ⟨0, i0⟩
  have h1 := hB ⟨1, i1⟩
  rw [abs_le] at h0 h1
  have hB2 : 1 / 2 ≤ B := by linarith
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem degUpper_of (hlog : LogNear) (hlie : LieBound) (_hvol : VolBall) : DegUpper := by
  unfold DegUpper ForDS
  intro m ε lam B hm hlam hgap hB H _ _ π hds d hd
  obtain ⟨v₀, hv₀⟩ := exists_lowUnit hds
  obtain ⟨hsm, hbd⟩ := hlie m ε lam B hm hlam hgap hB H π hds v₀ hv₀
  have hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π := hds.2.2.1
  have hB1 := one_le_eightMB hm hlam hB
  set c : ℝ := (8 * (m : ℝ) * B) ^ 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by linarith
  set δ : ℝ := 1 / (4 * c) with hδ
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hv1 : ‖v₀‖ = 1 := hv₀.1

  have key : ∀ g ∈ nbh ε δ, (1 / 4 : ℝ) ≤ ‖coefOn π v₀ v₀ g‖ ^ 2 := by
    intro g hg
    have hgU : umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
    obtain ⟨X, hX, hXn, hXe⟩ := hlog m ε δ hδ4 (umat g) hgU hg
    have h1 := hbd [X] (by simpa using hX) (by simp)
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1
    have h2 : ‖dR π X v₀‖ ≤ 1 / 2 := by
      calc ‖dR π X v₀‖ ≤ c * hsn X := h1
        _ ≤ c * (2 * δ) := by gcongr
        _ = 1 / 2 := by rw [hδ]; field_simp; ring
    have h3 : ‖π (umat g) v₀ - v₀‖ ≤ 1 / 2 := by
      rw [← hXe]; exact (orbit_sub_le hπ hX hsm).trans h2
    have h4 : coefOn π v₀ v₀ g = 1 + ⟪v₀, π (umat g) v₀ - v₀⟫_ℂ := by
      simp only [coefOn, inner_sub_right, inner_self_eq_norm_sq_to_K, hv1]
      push_cast; ring
    have h5 : ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ 1 / 2 := by
      calc ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ ‖v₀‖ * ‖π (umat g) v₀ - v₀‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 := by rw [hv1, one_mul]; exact h3
    have h6 : 1 / 2 ≤ ‖coefOn π v₀ v₀ g‖ := by
      rw [h4]
      have := norm_sub_norm_le (1 : ℂ) (-⟪v₀, π (umat g) v₀ - v₀⟫_ℂ)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    nlinarith

  obtain ⟨hdpos, hI⟩ := hd
  obtain ⟨hint, hval⟩ := hI v₀ v₀ v₀ v₀
  have hpt : ∀ g : UJ ε, coefOn π v₀ v₀ g * star (coefOn π v₀ v₀ g) = ((‖coefOn π v₀ v₀ g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint' : Integrable (fun g => ‖coefOn π v₀ v₀ g‖ ^ 2) (muG ε) := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  have hval' : ∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε = 1 / d := by
    have h := hval
    simp only [hpt, inner_self_eq_norm_sq_to_K, hv1] at h
    rw [integral_complex_ofReal] at h
    have h' : ((∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hlint : ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ) ≤ ENNReal.ofReal (1 / d) := by
    calc ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ)
        ≤ ENNReal.ofReal (1 / 4) * muG ε {g | ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2)} := by
          gcongr
          intro g hg
          exact ENNReal.ofReal_le_ofReal (key g hg)
      _ ≤ ∫⁻ g, ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2) ∂muG ε :=
          mul_meas_ge_le_lintegral₀ hint'.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
      _ = ENNReal.ofReal (1 / d) := by
          rw [← hval', ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun g => by positivity)]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)] at ht
  have : (muG ε (nbh ε δ)).toReal ≤ 4 * (1 / d) := by linarith
  rwa [mul_one_div] at this

end GlobalTheory.SepReal
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume : LogNear → LieBound → VolBall → DegUpper := by
  atlas_forward_decl GlobalTheory.SepReal.degUpper_of
end

section
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.FormalDegreeRatio

theorem thrStar_lt {N : ℕ} (ε : Fin N → Bool) {M : ℝ} (hNM : (N : ℝ) ≤ M) (hM : 1 ≤ M) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * M ^ 3 - 1 := by
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ N := by
      unfold ReciprocityTheory.ChartRestriction.DS.pOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ N := by
      unfold ReciprocityTheory.ChartRestriction.DS.qOf
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact le_trans (by exact_mod_cast this) hNM
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ M := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := min_le_right _ _
    exact le_trans (by exact_mod_cast this) hq
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hs : Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := by
    calc Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ Real.sqrt ((2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 1 := Real.sqrt_sq (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := Nat.cast_nonneg _
  have hqq0 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := Nat.cast_nonneg _
  have h1 : (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ M * M * M := by
    gcongr
  have h2 : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 16 * M * M := by
    gcongr
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hMM : M * M * M = M ^ 3 := by ring
  have hMM2 : 16 * M * M = 16 * M ^ 2 := by ring
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  have hmax : max ((N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1)
      (16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))) <
      1000 * M ^ 3 - 2 := by
    refine max_lt ?_ ?_
    · nlinarith
    · nlinarith
  linarith

theorem fdeg_const (N : ℕ) (ε : Fin N → Bool) : ∃ c : ℝ, 0 < c ∧ ∀ (lam : Fin N → ℝ) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h →
    (∃ a, ε a = true) → (∃ a, ε a = false) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat N → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, hF⟩ := ReciprocityTheory.ChartRestriction.DS.fdCons_muG N ε
  refine ⟨c, hc, fun lam h hlam hgap hh ht hf H _ _ σ hσ => ?_⟩
  have : CompleteSpace H := hσ.1
  have : Nontrivial H := hσ.2.1
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
    obtain ⟨a, ha⟩ := ht
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
    obtain ⟨a, ha⟩ := hf
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact Finset.card_pos.2 ⟨a, by simpa using ha⟩
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp hq
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := ReciprocityTheory.ChartRestriction.DS.fdc_eight hh
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hval := hF lam H σ v hlam hσ h hgap hh hp hq hΨ hv
  obtain ⟨d, hd⟩ := ReciprocityTheory.ChartRestriction.DS.fdcGood_of_isDS hσ
  have := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε)
  have hc' : (0 : ℝ) < (Measure.haarScalarFactor (Formalism.REAL.muG ε) (ReciprocityTheory.ChartRestriction.DS.muCD ε) : ℝ) := by
    exact_mod_cast hs
  obtain ⟨s, hs0, hEq⟩ : ∃ s : ℝ, 0 < s ∧ Formalism.REAL.muG ε = ENNReal.ofReal s • ReciprocityTheory.ChartRestriction.DS.muCD ε :=
    ⟨_, hc', by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩
  have hd2 := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hs0 hd
  rw [← hEq] at hd2
  have e : d / s = c * Formalism.QuantumDeterminants.fdegHC lam := by
    rw [← ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' hd2 hv]
    exact hval
  rwa [e] at hd2

theorem isHCParam_sub {N : ℕ} {lam : Fin N → ℝ} (s : Fin N) (hl : Formalism.QuantumDeterminants.IsHCParam lam)
    (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) : Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have := hw a b hab
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> linarith
  · obtain ⟨m, hm⟩ := hl.2 a
    by_cases ha : a = s
    · subst ha
      refine ⟨m - 1, ?_⟩
      simp only [Pi.sub_apply, Pi.single_eq_same]
      push_cast
      linarith
    · refine ⟨m, ?_⟩
      simp only [Pi.sub_apply, Pi.single_apply, if_neg ha]
      linarith

theorem gap_sub {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (s : Fin N) {h : ℝ}
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) : Formalism.QuantumDeterminants.GapAtLeast ε (lam - Pi.single s 1) (h - 1) := by
  intro a b hab
  have h1 := hg a b hab
  have e : (lam - Pi.single s 1 : Fin N → ℝ) a - (lam - Pi.single s 1 : Fin N → ℝ) b =
      (lam a - lam b) - ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b) := by
    simp only [Pi.sub_apply]; ring
  have ht : |(Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have := abs_sub_abs_le_abs_sub (lam a - lam b) ((Pi.single s (1 : ℝ) : Fin N → ℝ) a - (Pi.single s (1 : ℝ) : Fin N → ℝ) b)
  rw [e]
  linarith

theorem fdegHC_le {N : ℕ} (lam : Fin N → ℝ) (s : Fin N) (hw : ∀ a c, a < c → 2 ≤ lam a - lam c) :
    Formalism.QuantumDeterminants.fdegHC lam ≤ 2 ^ (N - 1) * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1) := by
  set lam' := lam - Pi.single s 1 with hlam'
  have hfac : ∀ a b : Fin N, a < b → |lam a - lam b| ≤ (if a = s then (2 : ℝ) else 1) * |lam' a - lam' b| := by
    intro a b hab
    have hne : a ≠ b := hab.ne
    have h2 := hw a b hab
    by_cases ha : a = s
    · subst ha
      have e1 : lam' a = lam a - 1 := by simp [hlam']
      have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hne.symm]
      rw [if_pos rfl, e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · rw [if_neg ha, one_mul]
      by_cases hb : b = s
      · subst hb
        have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b - 1 := by simp [hlam']
        rw [e1, e2, abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
      · have e1 : lam' a = lam a := by simp [hlam', Pi.single_apply, ha]
        have e2 : lam' b = lam b := by simp [hlam', Pi.single_apply, hb]
        rw [e1, e2]
  have hcount : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1) ≤
      2 ^ (N - 1) := by
    rw [Finset.prod_eq_single s (fun a _ ha => by simp [ha]) (fun h => absurd (Finset.mem_univ s) h)]
    simp only [if_pos rfl, Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    have hsub : univ.filter (fun b : Fin N => s < b) ⊆ univ.erase s := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [hb.ne']
    calc (univ.filter (fun b : Fin N => s < b)).card ≤ (univ.erase s).card := Finset.card_le_card hsub
      _ = N - 1 := by simp [Finset.card_erase_of_mem]
  have hnum : ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b| ≤
      2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
    calc ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b|
        ≤ ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
            ((if a = s then (2 : ℝ) else 1) * |lam' a - lam' b|) :=
          Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _) fun a _ =>
            Finset.prod_le_prod (fun b _ => abs_nonneg _) fun b hb => hfac a b (Finset.mem_filter.1 hb).2
      _ = (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (if a = s then (2 : ℝ) else 1)) *
            ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_mul_distrib]
      _ ≤ 2 ^ (N - 1) * ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam' a - lam' b| :=
          mul_le_mul_of_nonneg_right hcount (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
  have hD : 0 < ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => by
      have hab : a < b := (Finset.mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum hD.le

theorem degRatio_holds : DegRatio := by
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  obtain ⟨i0, hi0⟩ := hP.neg
  have hε't : ∃ a, ε' a = true := by
    by_contra hne
    push_neg at hne
    have h1 := hP.pos
    have h0 : (univ.filter fun i => ε' i = true) = ∅ := by
      ext i
      simp [hne i]
    rw [h0, Finset.card_empty] at h1
    have : 0 < (univ.filter fun i => ε' i = false).card := Finset.card_pos.2 ⟨i0, by simp [hi0]⟩
    omega
  have hεt : ∃ a, ε a = true := ⟨e none, hP.signs.1⟩
  have hεf : ∃ a, ε a = false := ⟨e (some i0), by rw [hP.signs.2 i0]; exact hi0⟩
  obtain ⟨c, hc, hF⟩ := fdeg_const (n + 1) ε
  obtain ⟨c', -, hF'⟩ := fdeg_const n ε'
  have hM : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hthr : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε (by push_cast; exact le_refl _) hM
  have hthr' : ReciprocityTheory.ChartRestriction.DS.thrStar ε' + 1 < 1000 * ((n : ℝ) + 1) ^ 3 - 1 :=
    thrStar_lt ε' (by linarith) hM
  refine ⟨⟨c' * Formalism.QuantumDeterminants.fdegHC mu, hF' mu _ hP.hmu hP.gap' (by linarith) hε't ⟨i0, hi0⟩ H' σ hσ⟩,
    c * Formalism.QuantumDeterminants.fdegHC lam, hF lam _ hP.hlam hP.gap (by linarith) hεt hεf H π hπ, fun s K _ _ ρ hρ => ?_⟩
  refine ⟨c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1),
    hF _ _ (isHCParam_sub s hP.hlam hP.wide) (gap_sub ε lam s hP.gap) hthr hεt hεf K ρ hρ, ?_⟩
  have h2 := fdegHC_le lam s hP.wide
  simp only [Nat.add_sub_cancel] at h2
  calc c * Formalism.QuantumDeterminants.fdegHC lam ≤ c * (2 ^ n * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ = 2 ^ n * (c * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) := by ring

end GlobalTheory.SepReal.FormalDegreeRatio
end
end

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_loweringWeight_ratio_le : DegRatio := by
  atlas_forward_decl GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SepReal.ProjSm

variable {m : ℕ}

theorem mem_iff (ε : Fin m → Bool) (g : Mat m) : g ∈ UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem mul_mem' {ε : Fin m → Bool} {g h : Mat m} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  rw [mem_iff] at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem one_mem' (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := by
  rw [mem_iff]; simp

theorem exp_mem {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ lieOf (Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have JJ := Formalism.REAL.Jm_mul_self ε
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  set Y : Mat m := t • X with hY
  have hYh : Yᴴ = Formalism.REAL.Jm ε * (-Y) * Formalism.REAL.Jm ε := by
    have : Xᴴ = -(Formalism.REAL.Jm ε * X) * Formalism.REAL.Jm ε := by
      have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
      calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, JJ, Matrix.mul_one]
        _ = _ := by rw [h1]
    rw [hY, Matrix.conjTranspose_smul, this]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg]
  have hc : NormedSpace.exp Yᴴ = Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε := by
    have hJi : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv JJ
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) (-Y) ⟨⟨_, _, JJ, JJ⟩, rfl⟩
    rw [hJi] at this
    rw [hYh, this]
  rw [mem_iff, ← Matrix.exp_conjTranspose, hc]
  have he : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-Y) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp Y
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-Y) * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * NormedSpace.exp Y) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [JJ, Matrix.mul_one, he, Matrix.mul_one]

theorem list_mem {m : ℕ} {ε : Fin m → Bool} : ∀ l : List (Mat m), (∀ x ∈ l, x ∈ UJset ε) → l.prod ∈ UJset ε
  | [], _ => by simpa using one_mem' ε
  | a :: l, h => by
    rw [List.prod_cons]
    exact mul_mem' (h a (by simp)) (list_mem l fun x hx => h x (by simp [hx]))

theorem embH_list {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) : ∀ l : List (Mat n), embH e l.prod = (l.map (embH e)).prod
  | [] => by simp [embH_one]
  | a :: l => by rw [List.prod_cons, embH_mul, embH_list e l, List.map_cons, List.prod_cons]

variable {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}
  {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Mat (n + 1) → (H →L[ℂ] H)} {σ : Mat n → (H' →L[ℂ] H')} {j : H' →L[ℂ] H} {P : H →L[ℂ] H'}

end GlobalTheory.SepReal.ProjSm
end
end

section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.RealAsm

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_Jm' (ε : Fin m → Bool) : IsUnit (Jm ε) := by
  refine IsUnit.of_mul_eq_one (Jm ε) ?_
  simp only [Jm, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem umat_mem (ε : Fin m → Bool) (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem one_mem (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := (1 : UJ ε).2

theorem continuous_umat (ε : Fin m → Bool) : Continuous (fun g : UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem smV_translate {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Mat m → (H →L[ℂ] H)} (hπ : IsDS ε lam π) {g : Mat m}
    (hg : g ∈ UJset ε) {v : H} (hv : SmV (lieOf (Jm ε)) π v) : SmV (lieOf (Jm ε)) π (π g v) :=
  GlobalTheory.SmLinSub.rep_mem (isUnit_Jm' ε) hπ.2.2.1 hv hg

theorem smV_const_smul {L : Set (Mat m)} {π : Mat m → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : SmV L π v) : SmV L π (a • v) :=
  fun k Xs hX => by simpa only [map_smul] using (hv k Xs hX).const_smul a

theorem integrable_low_coef (hD : DecPow) (hI : PowInt) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (B : ℝ) (hn : 3 ≤ n)
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (1000 * (n : ℝ) ^ 3)) (hB : ∀ a, |lam a| ≤ B)
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    Integrable (fun h : UJ ε => ⟪w, σ (umat h) w⟫_ℂ) (muG ε) := by
  have hdec := hD n ε lam B hn hl hg hB H σ hσ w hw
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA : 4 * (n : ℝ) ^ 2 + 1 ≤ 40 * (n : ℝ) ^ 2 := by nlinarith
  have hpow := (hI n ε (40 * (n : ℝ) ^ 2) (by omega) hA).1
  refine (hpow.const_mul (Real.exp (100 * (n : ℝ) ^ 3))).mono' ?_ (Filter.Eventually.of_forall fun h => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.inner ((hσ.2.2.1.2.2 w).comp_continuous (continuous_umat ε) (umat_mem ε))
  · exact hdec _ (umat_mem ε h)

theorem big_mul (a b : ℝ) (n : ℕ) (B : ℝ) : big a n B * big b n B = big (a + b) n B := by
  unfold big
  rw [← Real.exp_add]
  ring_nf

theorem big_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : big a n B ≤ big b n B := by
  unfold big
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith)
  have h2 : 0 ≤ ((n : ℝ) + 1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_right hab h2
  exact mul_le_mul_of_nonneg_right this h1

theorem big_pos (a : ℝ) (n : ℕ) (B : ℝ) : 0 < big a n B := Real.exp_pos _

theorem one_le_B {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {B : ℝ} (hP : Par e ε lam ε' mu B) : 1 ≤ B := by
  have hn := hP.three_le
  have h := hP.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h0 := abs_le.1 (hP.bound.1 ⟨0, by omega⟩)
  have h1 := abs_le.1 (hP.bound.1 ⟨1, by omega⟩)
  linarith [h0.1, h0.2, h1.1, h1.2]

theorem gap_mono {k : ℕ} {ε : Fin k → Bool} {lam : Fin k → ℝ} {a b : ℝ} (hab : a ≤ b) (h : GapAtLeast ε lam b) :
    GapAtLeast ε lam a := fun x y hxy => hab.trans (h x y hxy)

end GlobalTheory.SepReal.RealAsm

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.RealAsm

end GlobalTheory.SepReal

end
end
