import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrouStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectors
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityUnfoldSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaussDensDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSplitUnitVectorOrthComplement

section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen : ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  first | exact @GlobalTheory.adelicStab_isCompact_isOpen | exact GlobalTheory.adelicStab_isCompact_isOpen | (intros; apply GlobalTheory.adelicStab_isCompact_isOpen <;> assumption)
end

section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite := by
  first | exact @GlobalTheory.RatDiscrete.subgroup_countable_discrete | exact GlobalTheory.RatDiscrete.subgroup_countable_discrete | (intros; apply GlobalTheory.RatDiscrete.subgroup_countable_discrete <;> assumption)
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PerpReduce

section Lat

variable {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)

instance ringHomSurjective_mapRingEquiv : RingHomSurjective (RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E) :=
  ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩

def vecMap (n : ℕ) : (Fin n → E') →ₛₗ[(RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E)] (Fin n → E) where
  toFun y := fun i => e (y i)
  map_add' a b := by funext i; simp
  map_smul' r a := by
    funext i
    show e ((r : E') * a i) = e (r : E') * e (a i)
    rw [map_mul]

def latMap (L : Submodule (𝓞 E') (Fin n → E')) : Submodule (𝓞 E) (Fin n → E) := L.map (vecMap e n)

theorem mem_latMap (L : Submodule (𝓞 E') (Fin n → E')) (y : Fin n → E') :
    (fun i => e (y i)) ∈ latMap e L ↔ y ∈ L := by
  refine ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
  have : z = y := funext fun i => e.injective (congrFun h i)
  exact this ▸ hz

theorem exists_vec (x : Fin n → E) : ∃ y : Fin n → E', x = fun i => e (y i) :=
  ⟨fun i => e.symm (x i), by funext i; simp⟩

theorem latMap_fg (L : Submodule (𝓞 E') (Fin n → E')) (h : L.FG) : (latMap e L).FG := h.map _

theorem latMap_span (L : Submodule (𝓞 E') (Fin n → E'))
    (h : Submodule.span E' (L : Set (Fin n → E')) = ⊤) :
    Submodule.span E (latMap e L : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := exists_vec e x
  have hy : y ∈ Submodule.span E' (L : Set (Fin n → E')) := h ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ((mem_latMap e L y).2 hy)
  | zero =>
    have : (fun i => e ((0 : Fin n → E') i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => e ((a + b) i)) = (fun i => e (a i)) + (fun i => e (b i)) := by funext i; simp
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => e ((r • a) i)) = e r • (fun i => e (a i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem mem_range_iff (a : E') :
    e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.symm b, ?_⟩
    show e.symm (b : E) = a
    rw [show (b : E) = e a from hb]; simp
  · rintro ⟨b, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e b, rfl⟩

variable [StarRing E] [StarRing E'] (he : ∀ y, e (star y) = star (e y))
include he

theorem hform_map (J : Matrix (Fin n) (Fin n) E') (y x : Fin n → E') :
    Formalism.UG.hform (starRingEnd E) (J.map e) (fun i => e (y i)) (fun i => e (x i)) =
      e (Formalism.UG.hform (starRingEnd E') J y x) := by
  simp [Formalism.UG.hform, starRingEnd_apply, he]

theorem isHerm_map {J : Matrix (Fin n) (Fin n) E'} (hJ : Formalism.UG.IsHerm (starRingEnd E') J) :
    Formalism.UG.IsHerm (starRingEnd E) (J.map e) := by
  ext i j
  have h : star (J j i) = J i j := congrFun (congrFun hJ i) j
  show star (e (J j i)) = e (J i j)
  rw [← h, he]

theorem latMap_dual {J : Matrix (Fin n) (Fin n) E'} {L : Submodule (𝓞 E') (Fin n → E')}
    (h : ∀ x : Fin n → E', x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (starRingEnd E') J y x ∈ (algebraMap (𝓞 E') E').range) (x : Fin n → E) :
    x ∈ latMap e L ↔
      ∀ y ∈ latMap e L, Formalism.UG.hform (starRingEnd E) (J.map e) y x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨x, rfl⟩ := exists_vec e x
  rw [mem_latMap, h]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec e y
    rw [hform_map e he, mem_range_iff]
    exact H y ((mem_latMap e L y).1 hy)
  · rw [← mem_range_iff e, ← hform_map e he]
    exact H _ ((mem_latMap e L y).2 hy)

end Lat

theorem det_map_ne {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)
    {J : Matrix (Fin n) (Fin n) E'} (h : J.det ≠ 0) : (J.map e).det ≠ 0 := by
  have := (IsUnit.mk0 _ h).map (e : E' →+* E)
  rw [RingHom.map_det] at this
  exact this.ne_zero

def sibOf (I I' : AutInst) (e : I'.E ≃+* I.E) (he : ∀ y, e (star y) = star (e y)) : Sib I :=
  have h := fun v : InfinitePlace I.F =>
    GlobalTheory.AutInhab.exists_frame (GlobalTheory.AutInhab.isHerm_map I.cm (isHerm_map e he I'.J_herm) (I.φ v))
      (GlobalTheory.AutInhab.isUnit_det_map (det_map_ne e I'.J_det) (I.φ v))
  { n := I'.n
    J := I'.J.map e
    J_herm := isHerm_map e he I'.J_herm
    J_det := det_map_ne e I'.J_det
    L := latMap e I'.L
    L_span := latMap_span e _ I'.L_span
    L_fg := latMap_fg e _ I'.L_fg
    L_dual := latMap_dual e he I'.L_dual
    ε := fun v => (h v).choose
    P := fun v => (h v).choose_spec.choose
    P_unit := fun v => (h v).choose_spec.choose_spec.1
    P_spec := fun v => (h v).choose_spec.choose_spec.2 }

theorem exists_sib : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  intro I I' e s x A xf ⟨he, hn, hx, hxA, hA, hxL, hL⟩
  refine ⟨sibOf I I' e he, A, ⟨hn, hx, hxA, hA, hxL, fun y => ?_⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec (n := I'.n) e y
    exact (mem_latMap e I'.L y).trans (hL y)
  · intro c μ _ _ c' μ' _ _ hc hc'
    refine GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus (sibOf I I' e he).inst I' e (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) 1 he rfl ?_
      (fun y => ?_) c μ c' μ' hc hc'
    · show (1 : Matrix (Fin I'.n) (Fin I'.n) I.E)ᴴ * I'.J.map e * (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) =
        I'.J.map e
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · rw [GlobalTheory.GaussMean.Test.lamX_one]
      show _ ↔ (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) *ᵥ (fun i => e (y i)) ∈ latMap e I'.L
      rw [Matrix.one_mulVec, mem_latMap]

end GlobalTheory.PerpReduce
end
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthComplement_unitVector_same_fields : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  atlas_forward_decl GlobalTheory.PerpReduce.exists_sib
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem translate_inter_null {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    (μ : Measure G) (fund : Set G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) (hf : MeasurableSet fund)
    (hd : ∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) {a b : G} (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hab : a ≠ b) :
    μ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 := by
  have hc : a⁻¹ * b ∈ Γ := Γ.mul_mem (Γ.inv_mem ha) hb
  have hc1 : a⁻¹ * b ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
  have hset : (fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund
      ⊆ (fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨b⁻¹ * y, h2, ?_⟩, h1⟩
    show a⁻¹ * b * (b⁻¹ * y) = a⁻¹ * y
    group
  refine measure_mono_null hset (nonpos_iff_eq_zero.mp ?_)
  calc μ ((fun y => a⁻¹ * y) ⁻¹' ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund))
      ≤ μ.map (fun y => a⁻¹ * y) ((fun y => (a⁻¹ * b) * y) '' fund ∩ fund) :=
        MeasureTheory.Measure.le_map_apply (measurable_const_mul _).aemeasurable _
    _ = 0 := by rw [hμ _ (Γ.inv_mem ha)]; exact hd _ hc hc1

private theorem withDensity_preimage_inv_mul_eq_setLIntegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (a : G) (hμa : μ.map (fun y => a * y) = μ)
    (fund : Set G) (hf : MeasurableSet fund) :
    μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund) = ∫⁻ g in fund, Φ (a * g) ∂μ := by
  classical
  have hT : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) := hf.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, ← lintegral_indicator hT, ← lintegral_indicator hf]
  have hm : Measurable (((fun y => a⁻¹ * y) ⁻¹' fund).indicator Φ) := hΦ.indicator hT
  have key := MeasureTheory.lintegral_map (μ := μ) hm (measurable_const_mul a)
  rw [hμa] at key
  rw [key]
  congr 1
  funext x
  by_cases hx : x ∈ fund
  · have hx' : a * x ∈ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∈ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : a * x ∉ (fun y => a⁻¹ * y) ⁻¹' fund := by
      show a⁻¹ * (a * x) ∉ fund
      rwa [inv_mul_cancel_left]
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hx', if_neg hx]

private theorem withDensity_preimage_mul_eq_of_invariant {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) (Φ : G → ENNReal) (hΦ : Measurable Φ) (s : G) (hμs : μ.map (fun y => s * y) = μ)
    (hΦs : ∀ g, Φ (s * g) = Φ g) (Q : Set G) (hQ : MeasurableSet Q) :
    μ.withDensity Φ ((fun y => s * y) ⁻¹' Q) = μ.withDensity Φ Q := by
  classical
  have hT : MeasurableSet ((fun y => s * y) ⁻¹' Q) := hQ.preimage (measurable_const_mul _)
  rw [withDensity_apply _ hT, withDensity_apply _ hQ, ← lintegral_indicator hT, ← lintegral_indicator hQ]
  have key := MeasureTheory.lintegral_map (μ := μ) (hΦ.indicator hQ) (measurable_const_mul s)
  rw [hμs] at key
  rw [key]
  congr 1
  funext y
  by_cases hy : s * y ∈ Q
  · have hy' : y ∈ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy, hΦs]
  · have hy' : y ∉ (fun y => s * y) ⁻¹' Q := hy
    rw [Set.indicator_apply, Set.indicator_apply, if_neg hy', if_neg hy]

theorem lintegral_tsum_cosets_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  intro G _ _ _ Γ S μ fund Φ ι _ r hΓ hSΓ hμ hf hcov hd hΦ hΦS hr hrep
  have hTm : ∀ a : G, MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' fund) :=
    fun a => hf.preimage (measurable_const_mul _)
  have hSc : (S : Set G).Countable := hΓ.mono hSΓ
  have hD0m : MeasurableSet (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := MeasurableSet.iUnion fun i => hTm _
  have hnull : ∀ a b : G, a ∈ Γ → b ∈ Γ → a ≠ b →
      μ.withDensity Φ ((fun y => a⁻¹ * y) ⁻¹' fund ∩ (fun y => b⁻¹ * y) ⁻¹' fund) = 0 :=
    fun a b ha hb hab => withDensity_absolutelyContinuous μ Φ
      (translate_inter_null Γ μ fund hμ hf hd ha hb hab)
  have hL : ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ
      = μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) := by
    rw [lintegral_tsum (f := fun i g => Φ (r i * g)) fun i => (hΦ.comp (measurable_const_mul (r i))).aemeasurable]
    rw [measure_iUnion₀ ?_ fun i => (hTm _).nullMeasurableSet]
    · exact tsum_congr fun i =>
        (withDensity_preimage_inv_mul_eq_setLIntegral μ Φ hΦ (r i) (hμ _ (hr i)) fund hf).symm
    · intro i j hij
      refine hnull _ _ (hr i) (hr j) fun he => hij ?_
      have h1 : r i * (r i)⁻¹ ∈ S := by simpa using S.one_mem
      exact (hrep _ (hr i)).unique h1 (by rw [he]; simpa using S.one_mem)
  rw [hL]
  unfold GlobalTheory.FlagMeas.covol
  apply le_antisymm
  · refine le_iInf fun D => le_iInf fun hDm => le_iInf fun hDc => ?_
    calc μ.withDensity Φ (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund)
        ≤ μ.withDensity Φ (⋃ s ∈ (S : Set G), (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => s * y) ⁻¹' D) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨s, hs, hsx⟩ := hDc x (Set.mem_univ x)
          exact Set.mem_biUnion hs ⟨hx, hsx⟩
      _ ≤ ∑' p : (S : Set G), μ.withDensity Φ ((⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ (fun y => (p : G) * y) ⁻¹' D) :=
          measure_biUnion_le _ hSc _
      _ = ∑' p : (S : Set G), μ.withDensity Φ ((fun y => (p : G)⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine tsum_congr fun p => ?_
          have hpS : (p : G) ∈ S := p.2
          rw [← withDensity_preimage_mul_eq_of_invariant μ Φ hΦ (p : G) (hμ _ (hSΓ hpS)) (fun g => hΦS _ hpS g) _
            ((hD0m.preimage (measurable_const_mul _)).inter hDm)]
          congr 1
          ext y
          simp only [Set.mem_inter_iff, Set.mem_preimage, inv_mul_cancel_left]
      _ = μ.withDensity Φ (⋃ s ∈ (S : Set G), (fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) := by
          refine (measure_biUnion₀ hSc ?_ fun s _ =>
            ((hD0m.preimage (measurable_const_mul _)).inter hDm).nullMeasurableSet).symm
          intro s hs s' hs' hne
          have hsub : ((fun y => s⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ∩
              ((fun y => s'⁻¹ * y) ⁻¹' (⋃ i, (fun y => (r i)⁻¹ * y) ⁻¹' fund) ∩ D) ⊆
              ⋃ i, ⋃ j, (fun y => (s * r i)⁻¹ * y) ⁻¹' fund ∩ (fun y => (s' * r j)⁻¹ * y) ⁻¹' fund := by
            rintro y ⟨⟨hy1, -⟩, hy2, -⟩
            simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 hy2
            obtain ⟨i, hi⟩ := hy1
            obtain ⟨j, hj⟩ := hy2
            simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, _root_.mul_inv_rev, mul_assoc]
            exact ⟨i, j, hi, hj⟩
          refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun j => ?_)
          refine hnull _ _ (Γ.mul_mem (hSΓ hs) (hr i)) (Γ.mul_mem (hSΓ hs') (hr j)) fun he => hne ?_
          have h1 : s * r i * (r i)⁻¹ ∈ S := by rw [mul_inv_cancel_right]; exact hs
          have h2 : s * r i * (r j)⁻¹ ∈ S := by rw [he, mul_inv_cancel_right]; exact hs'
          have hij := (hrep _ (Γ.mul_mem (hSΓ hs) (hr i))).unique h1 h2
          subst hij
          exact mul_right_cancel he
      _ ≤ μ.withDensity Φ D := measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_right)
  · refine iInf_le_of_le _ (iInf_le_of_le hD0m (iInf_le _ ?_))
    intro x _
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    obtain ⟨i, hi, -⟩ := hrep γ⁻¹ (Γ.inv_mem hγ)
    refine ⟨(γ⁻¹ * (r i)⁻¹)⁻¹, S.inv_mem hi, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    show (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) ∈ fund
    have e : (r i)⁻¹ * ((γ⁻¹ * (r i)⁻¹)⁻¹ * x) = γ * x := by group
    rw [e]; exact hγx

end GlobalTheory.StabUnfold
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_tsum_cosets_fundamentalDomain_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  atlas_forward_decl GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
end

section
open MeasureTheory

namespace GlobalTheory.StabUnfold

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj K K' x S hK hK'o hK'c hK'K hS
  obtain ⟨b₀, hb₀m, hb₀⟩ := _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one G H ν j hj
  have hSeq : S = ⋃ h : H, (fun g => j h * x * g) '' (K : Set G) := by
    ext g
    rw [hS g]
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor <;> rintro ⟨h, k, hk, e⟩ <;> exact ⟨h, k, hk, e.symm⟩
  have hSopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_iUnion fun h => isOpenMap_mul_left (j h * x) _ hK
  have hSm : MeasurableSet S := hSopen.measurableSet
  set T : Set G := (fun g => x⁻¹ * g) ⁻¹' (K : Set G) with hT_def
  have hTm : MeasurableSet T := measurable_const_mul x⁻¹ hK.measurableSet
  have hc0 : ν K' ≠ 0 := (hK'o.measure_pos ν ⟨1, K'.one_mem⟩).ne'
  have hcT : ν K' ≠ ∞ := hK'c.measure_lt_top.ne
  have hSinv : ∀ h g, j h * g ∈ S ↔ g ∈ S := by
    intro h g
    rw [hS, hS]
    constructor
    · rintro ⟨h', k, hk, e⟩
      refine ⟨h⁻¹ * h', k, hk, ?_⟩
      have e' : g = (j h)⁻¹ * (j h' * x * k) := by rw [← e]; group
      rw [e', map_mul, map_inv]; group
    · rintro ⟨h', k, hk, e⟩
      exact ⟨h * h', k, hk, by rw [e, map_mul]; group⟩
  have hTS : ∀ g, g ∈ T → g ∈ S := by
    intro g hg
    rw [hS]
    exact ⟨1, x⁻¹ * g, hg, by simp⟩
  have hcoset : ∀ g ∈ S, ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 1 := by
    intro g hg
    obtain ⟨h0, k, hk, rfl⟩ := (hS g).1 hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k))
        = (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) := by
      intro h
      have hiff : j h * (j h0 * x * k) ∈ T ↔ h * h0 ∈ (K' : Set H) := by
        show x⁻¹ * (j h * (j h0 * x * k)) ∈ K ↔ h * h0 ∈ K'
        rw [hK'K, map_mul]
        have e2 : x⁻¹ * (j h * (j h0 * x * k)) = x⁻¹ * (j h * j h0) * x * k := by group
        rw [e2, Subgroup.mul_mem_cancel_right _ hk]
      by_cases hm : h * h0 ∈ (K' : Set H)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.1 hm)]
    calc ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k)) ∂ν
        = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) ∂ν := lintegral_congr e
      _ = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) h ∂ν :=
          lintegral_mul_right_eq_self (fun h => (K' : Set H).indicator (fun _ => (ν K')⁻¹) h) h0
      _ = 1 := by rw [lintegral_indicator_const hK'o.measurableSet, ENNReal.inv_mul_cancel hc0 hcT]
  have hzero : ∀ g, g ∉ S → ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 0 := by
    intro g hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) = 0 := fun h =>
      Set.indicator_of_notMem (fun hT => hg ((hSinv h g).1 (hTS _ hT))) _
    simp [e]
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  refine ⟨fun g => T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g,
    (measurable_const.indicator hTm).add (hb₀m.indicator hSm.compl), fun g => ?_, ?_⟩
  · dsimp only
    rw [lintegral_add_left (show Measurable fun h => T.indicator (fun _ => (ν K')⁻¹) (j h * g)
      from (measurable_const.indicator hTm).comp (hjg g))]
    by_cases hg : g ∈ S
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = 0 := fun h =>
        Set.indicator_of_notMem (show j h * g ∉ Sᶜ from fun hc => hc ((hSinv h g).2 hg)) _
      simp only [e, lintegral_zero, add_zero]
      exact hcoset g hg
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = b₀ (j h * g) := fun h =>
        Set.indicator_of_mem (show j h * g ∈ Sᶜ from fun hs => hg ((hSinv h g).1 hs)) _
      rw [hzero g hg, zero_add]
      simp only [e]
      exact hb₀ g
  · have e : ∀ g, S.indicator 1 g * (T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g)
        = T.indicator (fun _ => (ν K')⁻¹) g := by
      intro g
      by_cases hg : g ∈ S
      · simp [hg]
      · have hgT : g ∉ T := fun hT => hg (hTS g hT)
        simp [hg, hgT]
    rw [lintegral_congr e, lintegral_indicator_const hTm, hT_def, measure_preimage_mul,
      ENNReal.div_eq_inv_mul]

end GlobalTheory.StabUnfold
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_massOne_cutoff_doubleCoset_integral : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  atlas_forward_decl GlobalTheory.StabUnfold.exists_cutoff_doubleCoset
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem lintegral_pi_prod_mul : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  intro ι _ X _ μ _ Y _ ν _ f g hf hg
  have hm : Measurable fun x : ∀ i, X i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
  rw [← GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf]
  exact lintegral_prod_mul hm.aemeasurable hg.aemeasurable

end GlobalTheory.StabUnfold
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_pi_prod_mul_fintype_product : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  atlas_forward_decl GlobalTheory.StabUnfold.lintegral_pi_prod_mul
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj : ∀ (I I' : AutInst) (j : I'.Gf →* I.Gf) (xf : I.Gf), (∀ (N : ℕ) (g : I'.Gf), g ∈ I'.Kg N ↔ xf⁻¹ * j g * xf ∈ I.Kg N) → Topology.IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | exact GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg | (intros; apply GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ v, qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧ star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧ (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  first | exact @GlobalTheory.StabUnfold.isPerp_at_place | exact GlobalTheory.StabUnfold.isPerp_at_place | (intros; apply GlobalTheory.StabUnfold.isPerp_at_place <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  first | exact @GlobalTheory.StabCosets.gaussSum_cosets | exact GlobalTheory.StabCosets.gaussSum_cosets | (intros; apply GlobalTheory.StabCosets.gaussSum_cosets <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_orthogonal_stabilizer_embedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  first | exact @GlobalTheory.StabUnfold.exists_finEmb | exact GlobalTheory.StabUnfold.exists_finEmb | (intros; apply GlobalTheory.StabUnfold.exists_finEmb <;> assumption)
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace : ∀ (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ), m + 1 = n → qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧ ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  first | exact @GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | exact GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | (intros; apply GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal <;> assumption)
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold.RatPts

open GlobalTheory.RatDiscrete

theorem eq_map_of_resolution {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) {n m : ℕ}
    {x u : Fin n → E} {A : Matrix (Fin n) (Fin m) E} {A' : Matrix (Fin m) (Fin n) E}
    (h : vecMulVec x u + A * A' = 1) (M : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) E)
    (hx : M *ᵥ (fun i => ι (x i)) = fun i => ι (x i)) (hA : M * A.map ι = A.map ι * g.map ι) :
    M = (vecMulVec x u + A * g * A').map ι := by
  have h1 : (vecMulVec x u + A * A').map ι = 1 := by
    rw [h]; exact Matrix.map_one ι (map_zero ι) (map_one ι)
  have hvm : ∀ y w : Fin n → E, (vecMulVec y w).map ι = vecMulVec (fun i => ι (y i)) (fun i => ι (w i)) := by
    intro y w; ext i j; simp [vecMulVec_apply]
  have key : M * vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) =
      vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) := by
    ext i j
    have hi := congrFun hx i
    simp only [mulVec, dotProduct] at hi
    simp only [mul_apply, vecMulVec_apply]
    rw [← hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
  calc M = M * (vecMulVec x u + A * A').map ι := by rw [h1, Matrix.mul_one]
    _ = (vecMulVec x u + A * g * A').map ι := by
      rw [Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hvm,
        Matrix.mul_add, key, ← Matrix.mul_assoc, hA]

theorem exists_isImage (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA, IsImage I γ a := by
  have hU : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have hG : ∀ v, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
    intro v
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map (I.φ v)) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    exact (I.cm.cmUnram.2.1 (I.φ v) _).symm
  have hR : ∀ v, Formalism.REAL.inUJ (I.ε v)
      ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) := by
    intro v
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hdH : IsUnit (I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
    unfold Formalism.REAL.inUJ
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)ᴴ)⁻¹ (I.P v)ᴴ, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG v]
  have hC : ∀ v (X Y : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * X * I.P v) * ((I.P v)⁻¹ * Y * I.P v) = (I.P v)⁻¹ * (X * Y) * I.P v := by
    intro v X Y
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hE : ∀ v (X : Matrix (Fin I.n) (Fin I.n) I.E) (Y : Matrix (Fin I.n) (Fin I.n) I.E), X * Y = 1 →
      ((I.P v)⁻¹ * X.map (I.φ v) * I.P v) * ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v) = 1 := by
    intro v X Y hXY
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    rw [hC, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hd]
  let ι := Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)
  have hF : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι) *
      I.J.map ι * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι = I.J.map ι := by
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map ι) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [ι, Formalism.UG.cT, Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  let af : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := Units.map (RingHom.mapMatrix ι).toMonoidHom γ
  have haf : af ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    exact hF
  refine ⟨(fun v => ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      hE v _ _ (Units.mul_inv γ), hE v _ _ (Units.inv_mul γ)⟩, hR v⟩, ⟨af, haf⟩), fun v => rfl, rfl⟩

theorem isImage_embA {I : AutInst} (D : Sib I) {x u : Fin I.n → I.E} {A : Matrix (Fin I.n) (Fin D.n) I.E}
    {A' : Matrix (Fin D.n) (Fin I.n) I.E} (h : vecMulVec x u + A * A' = 1)
    {jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)} {jf : D.inst.Gf →* I.Gf}
    (hv : IsInfEmb D x A jv) (hf : IsFinEmb D x A jf) {γ : Matrix (Fin D.n) (Fin D.n) I.E} {g : D.inst.GA}
    (hg : IsImage D.inst γ g) : IsImage I (vecMulVec x u + A * γ * A') (embA D jv jf g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · have hPu := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hDu := (Matrix.isUnit_iff_isUnit_det _).mp (D.P_unit v)
    obtain ⟨h1, h2⟩ := hv v (g.1 v)
    have hxv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (x i)) =
        fun i => I.φ v (x i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change I.P v *ᵥ (uMat (jv v (g.1 v)) *ᵥ infVec I v x) = _
      rw [h1, infVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have key : I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v =
        A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
      calc I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v
          = I.P v * (uMat (jv v (g.1 v)) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v)) := by
            simp only [Matrix.mul_assoc]
        _ = I.P v * (((I.P v)⁻¹ * A.map (I.φ v) * D.P v) *
            ((D.P v)⁻¹ * γ.map (I.φ v) * D.P v)) :=
            congrArg (I.P v * ·) (h2.trans (congrArg (infMat D v A * ·) (hg1 v)))
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (D.P v) (D.P v)⁻¹, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mul,
              ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    have hAv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) =
        A.map (I.φ v) * γ.map (I.φ v) := by
      calc (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v)
          = (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) * D.P v * (D.P v)⁻¹ := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v * (D.P v)⁻¹ := by rw [key]
        _ = A.map (I.φ v) * γ.map (I.φ v) := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
    have hM := eq_map_of_resolution (I.φ v) h (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) γ hxv hAv
    change uMat (jv v (g.1 v)) = _
    rw [← hM]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul]
  · change I.fmat (jf g.2) = _
    exact eq_map_of_resolution (Formalism.UG.inclE (F := I.F) (Af I.F)) h (I.fmat (jf g.2)) γ (hf g.2).1
      ((hf g.2).2.trans (congrArg (afMat I A * ·) hg2))

theorem inclE_injective (I : AutInst) :
    Function.Injective (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) := by
  have hnf : ¬ IsField (𝓞 I.F) := by
    exact NumberField.RingOfIntegers.not_isField I.F
  obtain ⟨p, hp0, hpp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨p, hpp, hp0⟩
  have : Nontrivial (Af I.F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg (fun a : Af I.F => (a.1 v : v.adicCompletion I.F)) h)⟩⟩
  intro a b hab
  exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (A := I.E) (B := Af I.F)
    (RingHom.injective _) hab

end GlobalTheory.StabUnfold.RatPts

namespace GlobalTheory.StabUnfold

open GlobalTheory.RatDiscrete RatPts

theorem image_rational_eq_stab : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  intro I D s x A xf hP jv jf hv hf
  obtain ⟨hn, hβ, hxA, hAJ, -, -⟩ := hP
  have hJ : I.Jᴴ = I.J := by
    have hh := I.J_herm
    unfold Formalism.UG.IsHerm at hh
    ext i j
    have hij := congrFun (congrFun hh i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
    rw [Matrix.conjTranspose_apply]
    exact hij
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]; cases s <;> simp [GlobalTheory.GaussMean.sgn]
  obtain ⟨u, A', hA'A, hA'x, huA, hux, hres, hAJx⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ
  obtain ⟨j, hjv, hjr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer I.E (starRingEnd I.E) I.n D.n I.J D.J x u A A'
    (isUnit_iff_ne_zero.mpr hβ0) hxA hAJx hAJ hA'A hA'x huA hux hres
  ext y
  constructor
  · rintro ⟨g, ⟨γ, hγ, hg1, hg2⟩, rfl⟩
    have hIm := isImage_embA D hres hv hf (γ := (γ : Matrix (Fin D.n) (Fin D.n) I.E)) (g := g) ⟨hg1, hg2⟩
    have hj := hjv ⟨γ, hγ⟩
    refine ⟨⟨(j ⟨γ, hγ⟩ : GL (Fin I.n) I.E), (j ⟨γ, hγ⟩).2, ?_⟩, (hf g.2).1⟩
    change IsImage I _ _
    rw [hj]
    exact hIm
  · rintro ⟨⟨δ, hδ, hy1, hy2⟩, hyx⟩
    have h3 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) i)) =
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by
      rw [← GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.map_mulVec_incl, ← hy2]
      exact hyx
    have hδx : (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = x := by
      funext i
      exact inclE_injective I (congrFun h3 i)
    obtain ⟨γ₀, hγ₀⟩ := hjr ⟨δ, hδ⟩ hδx
    obtain ⟨g, hg⟩ := exists_isImage D.inst (γ₀ : GL (Fin D.n) I.E) γ₀.2
    refine ⟨g, ⟨(γ₀ : GL (Fin D.n) I.E), γ₀.2, hg.1, hg.2⟩, ?_⟩
    have hIm := isImage_embA D hres hv hf hg
    have hM : vecMulVec x u + A * ((γ₀ : GL (Fin D.n) I.E) : Matrix (Fin D.n) (Fin D.n) I.E) * A' =
        (δ : Matrix (Fin I.n) (Fin I.n) I.E) := by
      rw [← hjv γ₀, hγ₀]
    rw [hM] at hIm
    exact subsingleton_isImage I _ hIm ⟨hy1, hy2⟩

end GlobalTheory.StabUnfold
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_rationalOrthComplementUnitary_eq_rationalStabilizer : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  atlas_forward_decl GlobalTheory.StabUnfold.image_rational_eq_stab
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem exists_intertwiner_decomp_of_kernel_intertwines {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h5 : vecMulVec x u + A * A' = 1) (z : Fin n → R) :
    z = (u ⬝ᵥ z) • x + A *ᵥ (A' *ᵥ z) := by
  have h : (vecMulVec x u + A * A') *ᵥ z = z := by rw [h5, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at h
  conv_lhs => rw [← h]
  congr 1
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem coords_smul_add_mulVec {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1) (a : R) (w : Fin m → R) :
    u ⬝ᵥ (a • x + A *ᵥ w) = a ∧ A' *ᵥ (a • x + A *ᵥ w) = w := by
  constructor
  · rw [dotProduct_add, dotProduct_smul, h4, Matrix.dotProduct_mulVec, h3, zero_dotProduct, smul_eq_mul,
      mul_one, add_zero]
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, smul_zero,
      zero_add]

theorem conj_stab_and_cong_of_split {R : Type} [CommRing R] (S : Subring R) {n m : ℕ}
    (L : Submodule S (Fin n → R)) (L' : Submodule S (Fin m → R))
    (X Xi G : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) R)
    (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (hX : X * Xi = 1) (hXi : Xi * X = 1)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1)
    (h5 : vecMulVec x u + A * A' = 1)
    (hL : ∀ z, Xi *ᵥ z ∈ L ↔ ∃ a ∈ S, ∃ w ∈ L', z = a • x + A *ᵥ w)
    (hGx : G *ᵥ x = x) (hGA : G * A = A * g) :
    ((∀ w, w ∈ L' ↔ g *ᵥ w ∈ L') ↔ ∀ y, y ∈ L ↔ (Xi * G * X) *ᵥ y ∈ L) ∧
      ∀ c : R, (∀ w ∈ L', ∃ w' ∈ L', (g - 1) *ᵥ w = c • w') ↔
        ∀ y ∈ L, ∃ z ∈ L, (Xi * G * X - 1) *ᵥ y = c • z := by
  have hu0 : ∀ w, u ⬝ᵥ (A *ᵥ w) = 0 := fun w => by
    rw [Matrix.dotProduct_mulVec, h3, zero_dotProduct]
  have hA0 : ∀ w, A' *ᵥ (A *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hM : ∀ z, Xi *ᵥ z ∈ L ↔ u ⬝ᵥ z ∈ S ∧ A' *ᵥ z ∈ L' := by
    intro z
    rw [hL]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨e1, e2⟩ := coords_smul_add_mulVec x u A A' h1 h2 h3 h4 a w
      rw [e1, e2]
      exact ⟨ha, hw⟩
    · rintro ⟨ha, hw⟩
      exact ⟨_, ha, _, hw, exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z⟩
  have hG : ∀ z, G *ᵥ z = (u ⬝ᵥ z) • x + A *ᵥ (g *ᵥ (A' *ᵥ z)) := by
    intro z
    conv_lhs => rw [exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGx, Matrix.mulVec_mulVec, hGA, ← Matrix.mulVec_mulVec]
  have hXiX : ∀ y, Xi *ᵥ (X *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec]
  have hXXi : ∀ y, X *ᵥ (Xi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]
  have hconj : ∀ y, (Xi * G * X) *ᵥ y = Xi *ᵥ (G *ᵥ (X *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hGm : ∀ p, (G - 1) *ᵥ p = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
    intro p
    have hp := exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 p
    calc (G - 1) *ᵥ p = G *ᵥ p - p := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = ((u ⬝ᵥ p) • x + A *ᵥ (g *ᵥ (A' *ᵥ p))) - ((u ⬝ᵥ p) • x + A *ᵥ (A' *ᵥ p)) := by
          rw [← hp, hG]
      _ = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
          abel
  have hsub : ∀ y, (Xi * G * X - 1) *ᵥ y = Xi *ᵥ (A *ᵥ ((g - 1) *ᵥ (A' *ᵥ (X *ᵥ y)))) := by
    intro y
    rw [← hGm]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, hconj, Matrix.one_mulVec, hXiX]
  refine ⟨⟨fun hg y => ?_, fun h w => ?_⟩, fun c => ⟨fun hc y hy => ?_, fun h w hw => ?_⟩⟩
  · rw [hconj y]
    conv_lhs => rw [← hXiX y]
    rw [hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2]
    exact Iff.and Iff.rfl (hg _)
  · have hw := h (Xi *ᵥ (A *ᵥ w))
    rw [hconj, hXXi, hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1,
      (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2, hu0, hA0] at hw
    simpa [S.zero_mem] using hw
  · rw [← hXiX y, hM] at hy
    obtain ⟨w', hw', hgw⟩ := hc _ hy.2
    refine ⟨Xi *ᵥ (A *ᵥ w'), ?_, ?_⟩
    · rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw'⟩
    · rw [hsub, hgw, Matrix.mulVec_smul, Matrix.mulVec_smul]
  · have hy : Xi *ᵥ (A *ᵥ w) ∈ L := by
      rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw⟩
    obtain ⟨z, hz, hcz⟩ := h _ hy
    rw [hsub, hXXi, hA0] at hcz
    have e := congrArg (fun v => A' *ᵥ (X *ᵥ v)) hcz
    simp only [hXXi, hA0, Matrix.mulVec_smul] at e
    refine ⟨A' *ᵥ (X *ᵥ z), ?_, e⟩
    have hz' : Xi *ᵥ (X *ᵥ z) ∈ L := by rw [hXiX]; exact hz
    exact ((hM _).1 hz').2

theorem mem_level_iff_of_isFinEmb (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (jf : D.inst.Gf →* I.Gf) (hj : IsFinEmb D x A jf) :
    (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧
      ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  obtain ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩ := hp
  have hJ : I.Jᴴ = I.J := by
    have h := I.J_herm
    unfold Formalism.UG.IsHerm at h
    conv_rhs => rw [← h]
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]
  have hβ' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]
    cases s <;> simp [sgn]
  obtain ⟨u, A', e1, e2, e3, e4, e5, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ' hxJA hAJA
  have h1 : afMat I A' * afMat I A = 1 := by
    simp only [afMat]
    rw [← Matrix.map_mul, e1, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have h2 : afMat I A' *ᵥ afVec I x = 0 := by
    funext i
    have := RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) A' x i
    rw [e2, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : afVec I u ᵥ* afMat I A = 0 := by
    funext i
    have := RingHom.map_vecMul (Formalism.UG.inclE (F := I.F) (Af I.F)) A u i
    rw [e3, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h4 : afVec I u ⬝ᵥ afVec I x = 1 := by
    have := RingHom.map_dotProduct (Formalism.UG.inclE (F := I.F) (Af I.F)) u x
    rw [e4, map_one] at this
    exact this.symm
  have h5 : vecMulVec (afVec I x) (afVec I u) + afMat I A * afMat I A' = 1 := by
    have hv : vecMulVec (afVec I x) (afVec I u) = (vecMulVec x u).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp [afVec, vecMulVec]
    rw [hv]
    simp only [afMat]
    rw [← Matrix.map_mul, ← Matrix.map_add _ (map_add (Formalism.UG.inclE (F := I.F) (Af I.F))), e5, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have hX : I.fmat xf * I.fmat xf⁻¹ = 1 := by simp [AutInst.fmat]
  have hXi : I.fmat xf⁻¹ * I.fmat xf = 1 := by simp [AutInst.fmat]
  have hprod : ∀ g, I.fmat (xf⁻¹ * jf g * xf) = I.fmat xf⁻¹ * I.fmat (jf g) * I.fmat xf := by
    intro g
    simp [AutInst.fmat]
  have key := fun g => conj_stab_and_cong_of_split (IntAf I.F I.E) I.Lf D.inst.Lf (I.fmat xf) (I.fmat xf⁻¹)
    (I.fmat (jf g)) (D.inst.fmat g) (afVec I x) (afVec I u) (afMat I A) (afMat I A') hX hXi h1 h2 h3 h4 h5
    (adelicLattice_split I D s x A xf ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩) (hj g).1 (hj g).2
  have hK : ∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset := by
    intro g
    show (∀ w, w ∈ D.inst.Lf ↔ D.inst.fmat g *ᵥ w ∈ D.inst.Lf) ↔
      ∀ y, y ∈ I.Lf ↔ I.fmat (xf⁻¹ * jf g * xf) *ᵥ y ∈ I.Lf
    rw [hprod]
    exact (key g).1
  refine ⟨hK, fun N g => ?_⟩
  show (g ∈ D.inst.Kset ∧ ∀ y ∈ D.inst.Lf, ∃ z ∈ D.inst.Lf,
      (D.inst.fmat g - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z) ↔
    (xf⁻¹ * jf g * xf ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (xf⁻¹ * jf g * xf) - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z)
  rw [hprod]
  exact Iff.and (hK g) ((key g).2 _)

end GlobalTheory.StabUnfold
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_congruence_level_iff_orthEmbedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf → (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧ ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  atlas_forward_decl GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb
end

section
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem real_quot {n m : ℕ} (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε) (hn : m + 1 = n)
    (h1 : qEps ε x₀ = sgn ℝ s) (h2 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h3 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε')
    (h4 : ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) (c c' : ℝ) (hc : IsGauge ε c)
    (hc' : IsGauge ε' c') (b : Formalism.REAL.UJ ε → ENNReal) (hb : Measurable b)
    (hb1 : ∀ g, ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) :
    ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) =
      ENNReal.ofReal c' * ENNReal.ofReal (2 ^ n * gaussDens ε (sgn ℝ s)) := by
  subst hn
  obtain ⟨c₀, h0, -, hu⟩ := GlobalTheory.T.riemannianHaarGauge_exists_pos_unique m ε'
  have hpos : 0 < c' := hu c' hc' ▸ h0
  have hne : ENNReal.ofReal c' ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hinv : (ENNReal.ofReal c')⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  have hmul : ENNReal.ofReal c' * (ENNReal.ofReal c')⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top
  have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser m ε ε' s x₀ B j h1 h2 h3 h4 c c' hc hc'
    (fun g => (ENNReal.ofReal c')⁻¹ * b g) (hb.const_mul _) (fun g => by
      rw [lintegral_const_mul' _ _ hinv, hb1, mul_one, hmul])
  rw [← key]
  simp_rw [mul_left_comm _ (ENNReal.ofReal c')⁻¹]
  rw [lintegral_const_mul' _ _ hinv, mul_left_comm _ (ENNReal.ofReal c')⁻¹, ← mul_assoc (ENNReal.ofReal c'),
    hmul, one_mul]

theorem exists_rat (I : AutInst) : ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ (Γ : Set I.GA).Countable ∧
    DiscreteTopology Γ := by
  obtain ⟨⟨Γ, hΓ⟩, hc, hf⟩ := GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic I
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen I
  refine ⟨Γ, hΓ, hΓ ▸ hc, ?_⟩
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : I.GA)
  have hfin : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn (hf C hC)) ?_
    intro γ hγ
    exact ⟨hΓ ▸ γ.2, hγ⟩
  have hn : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C) ∈ nhds (1 : Γ) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hC1
  exact discreteTopology_of_isOpen_singleton_one (isOpen_singleton_of_finite_mem_nhds _ hn hfin)

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  obtain ⟨c₀, h0, -, hu⟩ := GlobalTheory.T.riemannianHaarGauge_exists_pos_unique n ε
  exact hu c h ▸ h0

theorem haar_muA (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure ∧ (I.muA μf).IsMulRightInvariant := by
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen I
  have := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨?_, ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf).2.1⟩⟩
  unfold AutInst.muA
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  exact Measure.prod.instIsHaarMeasure _ _

theorem unfold_sib (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (c' : InfinitePlace I.F → ℝ) (μf' : Measure D.inst.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
    (fund : Set I.GA) (hc : IsGaugeAll I c) (hc' : IsGaugeAll D.inst c') (hf : I.IsFundDom (I.muA μf) fund) :
    ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
      gaugeVol D.inst c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s)) := by
  obtain ⟨hKc, hKo, i1, i2⟩ := GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen I
  obtain ⟨hKc', hKo', i1', i2'⟩ := GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen D.inst
  have i3 := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  have i3' := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints D.inst
  obtain ⟨i4, -⟩ := haar_muA I μf
  obtain ⟨i4', i5'⟩ := haar_muA D.inst μf'
  have i6' : μf'.IsMulRightInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant D.inst μf').2.2.2.1⟩
  obtain ⟨jf, hjf, hrange⟩ := GlobalTheory.T.exists_finiteAdelic_orthogonal_stabilizer_embedding I D s x A xf hp
  have hloc := GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place I D s x A xf hp
  choose jv hjc hjv using fun v => GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace I.n D.n (I.ε v) (D.ε v) s _ _ hp.1 (hloc v).1 (hloc v).2.1
    (hloc v).2.2
  obtain ⟨hK, hKg⟩ := GlobalTheory.T.mem_congruence_level_iff_orthEmbedding I D s x A xf hp jf hjf
  have hjfc := GlobalTheory.T.isClosedEmbedding_of_congruenceSubgroups_conj I D.inst jf xf hKg
  have hj : Topology.IsClosedEmbedding (embA D jv jf) :=
    (Topology.IsClosedEmbedding.piMap hjc).prodMap hjfc
  obtain ⟨Γ, hΓ, hΓc, -⟩ := exists_rat I
  obtain ⟨Γ', hΓ', -, hΓd⟩ := exists_rat D.inst
  have hS : ((Γ'.map (embA D jv jf) : Subgroup I.GA) : Set I.GA) = stabF I x := by
    rw [Subgroup.coe_map, hΓ']
    exact GlobalTheory.T.image_rationalOrthComplementUnitary_eq_rationalStabilizer I D s x A xf hp jv jf hjv hjf
  obtain ⟨hopen, hmv, hleft, hright, hreal⟩ := GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant I x
  have hind : Measurable ({h : I.Gf | x ∈ lamX I (1, h)}.indicator (1 : I.Gf → ENNReal)) :=
    measurable_one.indicator hopen.measurableSet
  have hΦ : Measurable (gaussAt I x) := by
    unfold gaussAt
    exact (Finset.measurable_prod _ fun v _ => (hmv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hind.comp measurable_snd)
  have hinv : ∀ h g, gaussAt I x (embA D jv jf h * g) = gaussAt I x g := by
    intro h g
    unfold gaussAt
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      exact congrArg (fun y => ENNReal.ofReal (gauss y)) (hreal v _ (g.1 v) (hjv v (h.1 v)).1)
    · have := hleft (jf h.2) g.2 (hjf h.2).1
      rw [show (embA D jv jf h * g).2 = jf h.2 * g.2 from rfl]
      by_cases hg : x ∈ lamX I (1, g.2)
      · rw [Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from this.2 hg),
          Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from fun h' => hg (this.1 h')),
          Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
  obtain ⟨ι, hι, r, hr1, hr2, hr3⟩ := GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets I s x hp.2.1
  have hmem : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; rfl
  have hmemS : ∀ γ, γ ∈ Γ'.map (embA D jv jf) ↔ γ ∈ stabF I x := fun γ => by rw [← hS]; rfl
  have horb := GlobalTheory.T.lintegral_tsum_cosets_fundamentalDomain_eq_covol I.GA Γ (Γ'.map (embA D jv jf)) (I.muA μf) fund (gaussAt I x) ι r hΓc
    (fun γ h => (hmem γ).2 ((hmemS γ).1 h).1) (fun γ _ => (GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf).1 γ) hf.1
    (fun y => by obtain ⟨γ, h1, h2⟩ := hf.2.1 y; exact ⟨γ, (hmem γ).2 h1, h2⟩)
    (fun γ h => hf.2.2 γ ((hmem γ).1 h)) hΦ
    (by rintro _ ⟨h, -, rfl⟩ g; exact hinv h g) (fun i => (hmem _).2 (hr1 i))
    (fun γ h => by simp only [hmemS]; exact hr2 γ ((hmem γ).1 h))
  have i7 : ∀ v, (Formalism.REAL.muG (D.ε v)).IsMulRightInvariant := fun v => ⟨Formalism.REAL.indefinite_unitary_unimodular _ _⟩
  choose bv hbv hbv1 using fun v => GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup _ _ (Formalism.REAL.muG (D.ε v)) (jv v) (hjc v)
  obtain ⟨bf, hbf, hbf1, hbf2⟩ := GlobalTheory.T.exists_massOne_cutoff_doubleCoset_integral I.Gf D.inst.Gf μf μf' jf hjfc (Ksub I) (Ksub D.inst) xf
    {h : I.Gf | x ∈ lamX I (1, h)} hKo hKo' hKc' hK (fun g => by
      constructor
      · intro hg
        obtain ⟨h, h1, k, hk, e⟩ := GlobalTheory.T.stabilizer_transitive_adelic_unit_length_vectors I s x xf g hp.2.1 hp.2.2.2.2.1 hg
        obtain ⟨h', rfl⟩ := hrange h h1
        exact ⟨h', k, hk, e⟩
      · rintro ⟨h, k, hk, rfl⟩
        exact (hright _ k hk).2 ((hleft _ _ (hjf h).1).2 hp.2.2.2.2.1))
  have hb : Measurable fun g : I.GA => (∏ v, bv v (g.1 v)) * bf g.2 :=
    (Finset.measurable_prod _ fun v _ => (hbv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hbf.comp measurable_snd)
  have hb1 : ∀ g : I.GA, ∫⁻ h, (∏ v, bv v ((embA D jv jf h * g).1 v)) * bf (embA D jv jf h * g).2
      ∂(D.inst.muA μf') = 1 := by
    intro g
    have := GlobalTheory.T.lintegral_pi_prod_mul_fintype_product _ _ (fun v => Formalism.REAL.muG (D.ε v)) _ μf' (fun v h => bv v (jv v h * g.1 v))
      (fun h => bf (jf h * g.2))
      (fun v => (hbv v).comp (((hjc v).continuous.mul continuous_const).measurable))
      (hbf.comp ((hjfc.continuous.mul continuous_const).measurable))
    simp only [hbv1, hbf1, Finset.prod_const_one, mul_one] at this
    exact this
  have hun := GlobalTheory.T.leftQuotientCovolume_withDensity_unfold_subgroup I.GA D.inst.GA (I.muA μf) (D.inst.muA μf') (embA D jv jf) hj Γ' (gaussAt I x) _ hΦ hb
    hinv hb1
  have hint : ∫⁻ g, gaussAt I x g * ((∏ v, bv v (g.1 v)) * bf g.2) ∂(I.muA μf) =
      (∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g ∂(Formalism.REAL.muG (I.ε v))) *
        (μf I.Kset / μf' D.inst.Kset) := by
    have := GlobalTheory.T.lintegral_pi_prod_mul_fintype_product _ _ (fun v => Formalism.REAL.muG (I.ε v)) _ μf
      (fun v g => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g)
      (fun g => {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g * bf g)
      (fun v => (hmv v).mul (hbv v)) (hind.mul hbf)
    rw [hbf2] at this
    refine Eq.trans (lintegral_congr fun g => ?_) this
    unfold gaussAt
    rw [Finset.prod_mul_distrib, mul_mul_mul_comm]
  have hq := fun v => real_quot (I.ε v) (D.ε v) s _ _ (jv v) hp.1 (hloc v).1 (hloc v).2.1 (hloc v).2.2 (hjv v)
    (c v) (c' v) (hc v) (hc' v) (bv v) (hbv v) (hbv1 v)
  have hs : sgn ℝ s ≠ 0 := by unfold sgn; split_ifs <;> norm_num
  have hd : ∀ v, 0 ≤ gaussDens (I.ε v) (sgn ℝ s) := fun v => ((GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous _ (I.ε v)).1 _ hs).2
  have hprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun v _ => hq v
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc' v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (by positivity) (hd v), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).2.2.2.2.1, ← pow_mul] at hprod
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, (Ksub I).one_mem⟩).ne'
  have hKt : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  simp_rw [hr3]
  rw [horb, hun, hint, hΓ', gaugeVol, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  generalize covol D.inst.GFset (D.inst.muA μf') Set.univ = a
  generalize (μf' D.inst.Kset)⁻¹ = t
  have h1 := ENNReal.mul_inv_cancel hK0 hKt
  calc _ = a * t * (ENNReal.ofReal (∏ v, c v) * ∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) *
        bv v g ∂(Formalism.REAL.muG (I.ε v))) * (μf I.Kset * (μf I.Kset)⁻¹) := by ring
    _ = _ := by rw [hprod, h1]; ring

theorem gaugeUnfold : GaugeUnfold := by
  intro I I' e s x A xf _ hp c μf _ _ c' μf' _ _ fund hc hc' hf
  obtain ⟨D, B, hD, hvol⟩ := GlobalTheory.T.exists_orthComplement_unitVector_same_fields I I' e s x A xf hp
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary D.inst
  choose d _ hd _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique D.n (D.ε v)
  rw [← hvol d μ c' μf' hd hc']
  exact unfold_sib I D s x B xf hD c μf d μ fund hc hd hf

end GlobalTheory.StabUnfold
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianSum_stabiliserUnfolding : GaugeUnfold := by
  atlas_forward_decl GlobalTheory.StabUnfold.gaugeUnfold
end
