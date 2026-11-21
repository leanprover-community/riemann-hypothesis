import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphProjectionMass

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphMass

variable {n : ℕ}

theorem norm_le_of_frameProj (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ I)
    (hx : WithLp.ofLp x = frameProj b I z) : ‖x‖ ≤ ‖z‖ := by
  have h1 : ‖x‖ ^ 2 = ∑ i ∈ I, ‖inner ℂ (b i) z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun hx i
    simp only [frameProj] at this
    simp [this]
  have h2 := b.orthonormal.sum_inner_products_le (s := I) (x := z)
  nlinarith [norm_nonneg x, norm_nonneg z]

theorem frameProj_basisFun_repr (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr z) = frameProj b I z := by
  funext i
  simp only [frameProj]
  rw [EuclideanSpace.basisFun_inner, b.repr_apply_apply]

theorem frameFibreCount_image_repr (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr '' A) x =
      frameFibreCount b I A x := by
  have h : {y ∈ b.repr '' A | frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I y = x} =
      b.repr '' {z ∈ A | frameProj b I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [frameProj_basisFun_repr] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [frameProj_basisFun_repr]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

theorem image_repr_eq_graph (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I₀ : Finset (Fin n)) {d : ℕ} (hd : I₀.card = d) (Ω : Set (I₀ → ℂ))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω' : Set (EuclideanSpace ℂ (Fin d)))
      (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
      IsOpen Ω' ∧ DifferentiableOn ℂ F Ω' ∧ b.repr '' (g '' Ω) = graphPt e F '' Ω' := by
  classical
  let σ : I₀ ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hd])
  let m := Fintype.card {j : Fin n // j ∉ I₀}
  let τ : {j : Fin n // j ∉ I₀} ≃ Fin m := Fintype.equivFin _
  let e : Fin n ≃ Fin d ⊕ Fin m := (Equiv.sumCompl (· ∈ I₀)).symm.trans (Equiv.sumCongr σ τ)
  let P : EuclideanSpace ℂ (Fin d) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i => EuclideanSpace.proj (σ i)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => innerSL ℂ (b (τ.symm k)))
  have hP : ∀ x i, P x i = x (σ i) := fun x i => rfl
  have hQ : ∀ z k, Q z k = inner ℂ (b (τ.symm k)) z := fun z k => rfl
  have hPsurj : Function.Surjective P := fun w =>
    ⟨(EuclideanSpace.equiv (Fin d) ℂ).symm (fun i => w (σ.symm i)), by funext i; simp [hP]⟩
  refine ⟨m, e, P ⁻¹' Ω, Q ∘ g ∘ P, hΩ.preimage P.continuous, ?_, ?_⟩
  · exact Q.differentiable.comp_differentiableOn
      (hg.comp P.differentiable.differentiableOn fun x hx => hx)
  · have key : ∀ x ∈ P ⁻¹' Ω, graphPt e (Q ∘ g ∘ P) x = b.repr (g (P x)) := by
      intro x hx
      have hfx := hfix (P x) hx
      ext j
      by_cases hj : j ∈ I₀
      · have he : e j = Sum.inl (σ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_pos hj]
        have := congrFun hfx ⟨j, hj⟩
        simp only [frameProj, hP] at this
        simp [graphPt, he, b.repr_apply_apply, this]
      · have he : e j = Sum.inr (τ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_neg hj]
        simp [graphPt, he, b.repr_apply_apply, hQ]
    rw [Set.image_congr key, ← Set.image_image (fun w => b.repr (g w)) P,
      Set.image_preimage_eq Ω hPsurj, Set.image_image]

theorem mass_piece (hPF : ProjectionFormula.Statement)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount b I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (EuclideanSpace.basisFun (Fin n) ℂ) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr]

theorem tsum_frameFibreCount_le (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) {A : Set (EuclideanSpace ℂ (Fin n))} (As : ℕ → Set (EuclideanSpace ℂ (Fin n)))
    (hsub : ∀ k, As k ⊆ A) (hdisj : Pairwise (Disjoint on As)) (x : I → ℂ) :
    ∑' k, frameFibreCount b I (As k) x ≤ frameFibreCount b I A x := by
  have hfin : ∀ s : Finset ℕ,
      ∑ k ∈ s, frameFibreCount b I (As k) x = frameFibreCount b I (⋃ k ∈ s, As k) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [frameFibreCount]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, ih, Finset.set_biUnion_insert]
      simp only [frameFibreCount]
      rw [← ENat.toENNReal_add, ← Set.encard_union_eq]
      · congr 2
        ext z
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        tauto
      · refine Set.disjoint_of_subset (Set.sep_subset _ _) (Set.sep_subset _ _) ?_
        refine Set.disjoint_iUnion₂_right.2 fun j hj => hdisj ?_
        rintro rfl
        exact hk hj
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [hfin s]
  simp only [frameFibreCount]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨?_, hz.2⟩)
  exact Set.iUnion₂_subset (fun k _ => hsub k) hz.1

theorem tsum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞) :
    ∑' k, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑' k, f k x ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ k ∈ s, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑ k ∈ s, f k x ∂μ := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hk ih =>
          rw [Finset.sum_insert hk]
          simp_rw [Finset.sum_insert hk]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ x, ∑' k, f k x ∂μ := lintegral_mono fun x => ENNReal.sum_le_tsum s

theorem frameFibreCount_ball_le (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (R : ℝ) (x : EuclideanSpace ℂ I) :
    frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x) ≤
      (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
        (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x := by
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℂ I) R
  · rw [Set.indicator_of_mem hx]
    refine le_trans ?_ (le_iSup (fun y => frameFibreCount b I S y) (WithLp.ofLp x))
    simp only [frameFibreCount]
    exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hz.1.1, hz.2⟩)
  · rw [Set.indicator_of_notMem hx]
    have h : {z ∈ S ∩ Metric.ball 0 R | frameProj b I z = WithLp.ofLp x} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => hx ?_
      rw [mem_ball_zero_iff]
      exact (norm_le_of_frameProj b I z x hz.2.symm).trans_lt (mem_ball_zero_iff.1 hz.1.2)
    simp only [frameFibreCount]
    rw [h]
    simp

end LocalGraphMass

open LocalGraphMass in

theorem LocalGraphMass.proof (hPF : ProjectionFormula.Statement) : LocalGraphMass.Statement := by
  intro n d b I₀ S hd hS R
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ Metric.ball 0 R ∩ disjointed W k =
      g (f k) '' Ω (f k) ∩ (Metric.ball 0 R ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ Metric.ball 0 R ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ Metric.ball 0 R ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece hPF b I₀ hd _ _ (hΩ _) (hg _) (hfix _) _
          (Metric.isOpen_ball.measurableSet.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I S x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := by
        refine Finset.sum_le_sum fun I _ => ?_
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) := tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                tsum_frameFibreCount_le b I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
                (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x => frameFibreCount_ball_le b I S R x
          _ = _ := lintegral_indicator_const Metric.isOpen_ball.measurableSet _

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphProjectionMass

variable {n : ℕ}

theorem frameFibreCount_image_repr_map (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (c.map b.repr) I (b.repr '' A) x = frameFibreCount c I A x := by
  have hP : ∀ z, frameProj (c.map b.repr) I (b.repr z) = frameProj c I z := by
    intro z
    funext i
    simp only [frameProj, OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]
  have h : {y ∈ b.repr '' A | frameProj (c.map b.repr) I y = x} =
      b.repr '' {z ∈ A | frameProj c I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [hP] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [hP]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

theorem mass_piece_frame (hPF : ProjectionFormula.Statement)
    (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount c I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := LocalGraphMass.image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (c.map b.repr) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr_map]

theorem lintegral_count_le (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by
  set e := I.orderIsoOfFin hI
  set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs
  let φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm
  have hφ : ∀ x k, φ x k = x (e k) := fun x k => rfl
  have hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z := by
    intro z k
    rw [hc]
    simp [rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]
  have hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x := by
    intro x z
    constructor
    · intro h
      ext k
      rw [hrow, hφ]
      exact congrFun h (e k)
    · intro h
      funext i
      have := congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h
      simp only [hrow, hφ, OrderIso.apply_symm_apply] at this
      exact this
  set T := rowsProj U s '' A
  set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)
  have hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤
      (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x := by
    intro x
    have hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x} := by
      ext z
      exact and_congr Iff.rfl (hiff x z)
    by_cases hx : φ x ∈ T
    · rw [Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from
        subset_toMeasurable _ T hx)]
      simp only [frameFibreCount]
      rw [hset]
      exact le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)
    · have h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅ := by
        rw [hset]
        exact Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩
      simp only [frameFibreCount]
      rw [h0]
      simp
  calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        lintegral_mono hle
    _ = N * μH[((2 * d : ℕ) : ℝ)] (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T) :=
        lintegral_indicator_const ((measurableSet_toMeasurable _ _).preimage φ.continuous.measurable) _
    _ = N * μH[((2 * d : ℕ) : ℝ)] T := by
        rw [φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq,
          Set.inter_univ, measure_toMeasurable]

end LocalGraphProjectionMass

open LocalGraphProjectionMass in

theorem LocalGraphProjectionMass.proof (hPF : ProjectionFormula.Statement) :
    LocalGraphProjectionMass.Statement := by
  intro n d b I₀ S hd hS U hU B hB
  classical
  obtain ⟨c, hc⟩ := MassFinite.exists_frame U hU
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  let G : (Fin d → Fin n) → ℝ≥0∞ := fun s =>
    (⨆ x : EuclideanSpace ℂ (Fin d),
        (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
      μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ B ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by
        refine Finset.sum_le_sum fun I hI => ?_
        have hIc := (Finset.mem_powersetCard.1 hI).2
        refine le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              LocalGraphMass.tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                LocalGraphMass.tsum_frameFibreCount_le c I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ G (I.orderEmbOfFin hIc) := lintegral_count_le U c hc I hIc (S ∩ B)
    _ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by
        refine Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2))
          (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩)
          (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)
        · have := congrArg Set.range h
          rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at this
          exact Finset.coe_inj.1 this
        · have hmono := (Finset.mem_filter.1 ht).2
          have hcard : (Finset.univ.image t).card = d := by
            rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
          refine ⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩
          exact (Finset.orderEmbOfFin_unique hcard
            (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm
        · exact iSup_pos (Finset.mem_powersetCard.1 hI).2

end

end GroundTheory.Heights₂.Heights
end
