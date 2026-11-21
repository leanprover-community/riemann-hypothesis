import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Mathlib
import Mathlib.LinearAlgebra.Lagrange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTer
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PWeightDiag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PVanish
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PArchZero
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ContinuousClassKernel
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelImpliesRegularClassFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicTermsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceOfInputs

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PSmoothSum

lemma le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

end MainStatements.WeightKernel.PSmoothSum

namespace MainStatements.WeightKernel

open PSmoothSum in
theorem smoothSum : SmoothSum := by
  intro X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : X)
  let φ : ContDiffBump (0 : X) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : X × P → ℂ := fun q => ((φ q.1 : ℝ) : ℂ) * W q
  have hG : ContDiff ℝ ∞ G :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW
  have hsupp : tsupport G ⊆ tsupport φ ×ˢ univ := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)
    intro q hq
    refine ⟨subset_tsupport _ ?_, mem_univ _⟩
    intro h0
    apply hq
    simp [G, h0]
  have hcpt : IsCompact (tsupport φ ×ˢ K) := φ.hasCompactSupport.isCompact.prod hK
  have hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn
    refine ⟨max M 0, fun x y hy => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)
    · have : (x, y) ∉ tsupport G := fun h => hx (hsupp h).1
      have h0 : iteratedFDeriv ℝ k G (x, y) = 0 := by
        by_contra hne
        exact this (support_iteratedFDeriv_subset k hne)
      simp [h0]
  choose M hM using hbound
  let L : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  have hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K →
      ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k := by
    intro y k x hy
    have heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L := by
      funext z
      simp [L]
    have hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y))) := hG.comp (contDiff_id.add contDiff_const)
    rw [heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hxy : L x + (0, y) = (x, y) := by simp [L]
    rw [hxy]
    exact mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩
  · refine contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_
    · intro i
      exact contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))
    · intro k _
      exact ha.mul_right _
    · intro k i x _
      have hci : ContDiffAt ℝ k (fun z => G (z, p i)) x :=
        ((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt
      have := iteratedFDeriv_const_smul_apply' (a := a i) hci
      simp only [smul_eq_mul] at this
      rw [this]
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))
  · intro x hx
    have hx' : dist x 0 ≤ R := hR hx
    have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      show dist x 0 ≤ max R 0 + 1
      linarith [le_max_left R 0])
    simp [G, h1]

end MainStatements.WeightKernel
end
end

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MainStatements.WeightKernel.PClosedGraph

variable {Ω I : Type} [MeasurableSpace Ω] {m : Measure Ω} {u : I → Ω → ℂ}

lemma summable_norm_lp (a : lp (fun _ : I => ℂ) 1) : Summable (fun i => ‖a i‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)
  simpa using h

lemma norm_lp_eq (a : lp (fun _ : I => ℂ) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

lemma summable_mul {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : I → ℂ) (ha : Summable fun i => ‖a i‖) :
    Summable (fun i => a i * u i x) := by
  refine Summable.of_norm_bounded (ha.mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

lemma norm_tsum_mul_le {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : lp (fun _ : I => ℂ) 1) :
    ‖∑' i, a i * u i x‖ ≤ ‖a‖ * M := by
  have ha := summable_norm_lp a
  have hs := summable_mul hM a ha
  calc ‖∑' i, a i * u i x‖ ≤ ∑' i, ‖a i * u i x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, ‖a i‖ * M := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
    _ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]

lemma tsum_single [DecidableEq I] (i : I) (x : Ω) : ∑' j, (lp.single 1 i (1 : ℂ) : lp (fun _ : I => ℂ) 1) j * u j x = u i x := by
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

end MainStatements.WeightKernel.PClosedGraph

open MainStatements.WeightKernel.PClosedGraph in
theorem MainStatements.WeightKernel.closedGraph : MainStatements.WeightKernel.ClosedGraph := by
  intro Ω I _ m u hbd hint
  choose M hM using hbd
  let Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ := fun a x => ∑' i, a i * u i x
  have hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m := fun a => hint a (summable_norm_lp a)
  have hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b := by
    intro a b
    funext x
    simp only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]
    exact Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a))
      (summable_mul (hM x) b (summable_norm_lp b))
  have hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x := by
    intro c a
    funext x
    simp only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  let T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m :=
    { toFun := fun a => Integrable.toL1 (Tf a) (hTi a)
      map_add' := by
        intro a b
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hadd a b))
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hsmul c a)) }
  have hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a) := fun a => rfl
  have hcont : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun s a y hs hy => ?_
    have hmeas := tendstoInMeasure_of_tendsto_Lp hy
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    apply Lp.ext
    filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)]
      with x hx1 hx2 hx3
    rw [hTapp a, hx2]
    have hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]
          exact hs
        simpa using h0.mul_const (M x)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have e : Tf (s n) x - Tf a x = Tf (s n - a) x := by
        have := congrFun (hadd (s n - a) a) x
        simp only [sub_add_cancel, Pi.add_apply] at this
        rw [this]
        ring
      rw [e]
      exact norm_tsum_mul_le (hM x) (s n - a)
    have hsub := hpt.comp hns.tendsto_atTop
    refine tendsto_nhds_unique hx1 ?_
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hTapp, hx3]
  let T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m := ⟨T, hcont⟩
  refine ⟨‖T'‖, fun i => ?_⟩
  classical
  let e : lp (fun _ : I => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have hTe : Tf e = u i := funext fun x => tsum_single i x
  have hint_i : Integrable (u i) m := hTe ▸ hTi e
  refine ⟨hint_i, ?_⟩
  have hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(hTi e).coeFn_toL1] with x hx
    rw [hTapp, hx, hTe]
  have hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖ := T'.le_opNorm e
  have he : ‖e‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  rw [← hn]
  calc ‖T e‖ = ‖T' e‖ := rfl
    _ ≤ ‖T'‖ * ‖e‖ := hle
    _ = ‖T'‖ := by rw [he, mul_one]
end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PKerUnif

theorem ker_eq_sum {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (C : Set H) (x : Ω)
    (hf : {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite) (hφ : ∀ y ∉ C, φ y = 0) :
    MainStatements.WeightKernel.ker c q φ x = ∑ i ∈ hf.toFinset, c i x * φ (q i x) := by
  unfold MainStatements.WeightKernel.ker
  apply tsum_eq_sum
  intro i hi
  rw [Set.Finite.mem_toFinset] at hi
  by_cases h1 : c i x = 0
  · simp [h1]
  · have h2 : q i x ∉ C := fun h => hi ⟨h1, h⟩
    simp [hφ _ h2]

end MainStatements.WeightKernel.PKerUnif

open MainStatements.WeightKernel.PKerUnif in
theorem MainStatements.WeightKernel.kerUnif : SmoothSum → ClosedGraph → KerUnif := by
  intro hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan
  obtain ⟨M, hM⟩ := ((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  have hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M := fun y hy k hk =>
    hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)
  obtain ⟨R, hR⟩ := (hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)
  obtain ⟨Bd, hBd⟩ := hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by
    intro x
    refine ⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩
    rw [ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by
    intro a ha
    have hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0 := by
      intro y hy
      have : ∀ k : K, a k * W (matCoord ι y, p k) = 0 := fun k => by rw [hvan k.1 k.2 y hy, mul_zero]
      simp [this]
    let bump : ContDiffBump (0 : Mx n) :=
      ⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩
    obtain ⟨Φ, hΦs, hΦ⟩ := hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp)
      (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha
    have hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z,
        (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩
      simp only [Complex.ofRealCLM_apply]
      by_cases hy : y ∈ C
      · have hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have h1 : bump (matCoord ι y) = 1 := bump.one_of_mem_closedBall hin
        rw [h1, hΦ _ hin2]
        simp
      · by_cases hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)
        · rw [hΦ _ hb]
          simp [hz y hy]
        · have h0 : bump (matCoord ι y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)
          simp [h0, hz y hy]
    refine (hker.int _ hψ).congr (ae_of_all m fun x => ?_)
    have hf := hker.fin x C hC
    have hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k)) := by
      intro i hi
      have hq := ((Set.Finite.mem_toFinset _).1 hi).2
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)
    have hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k) :=
      fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)
    symm
    calc ∑' k : K, a k * ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑' k : K, ∑ i ∈ hf.toFinset, c i x * (a k * W (matCoord ι (q i x), p k)) := by
          congr 1; ext k; rw [hu k, Finset.mul_sum]; congr 1; ext i; ring
      _ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) :=
          Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _
      _ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by
          congr 1; ext i; rw [tsum_mul_left]
      _ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x :=
          (ker_eq_sum c q _ C x hf hz).symm)
  exact ⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem kerSwap : KerUnif → KerSwap := by
  intro hU H _ _ _ _ _ _ _ _ n ι hι μ _ Ω I _ _ m _ c q hk P _ _ _ W p K C hW hp hK hC hWC
  obtain ⟨B, hB⟩ := hU H n ι hι Ω I m c q hk P W p K C hW hp hK hC hWC
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hmc : Continuous (matCoord ι) := hι.continuous
  set G : H × H → ℂ := fun z => W (matCoord ι z.1, p z.2) with hG
  have hGc : Continuous G := hW.continuous.comp ((hmc.comp continuous_fst).prodMk (hp.comp continuous_snd))
  set F : H → Ω → ℂ := fun k x => ker c q (fun y => W (matCoord ι y, p k)) x with hF

  have hvan : ∀ x, ∀ k ∈ K, ∀ i, i ∉ (hk.fin x C hC).toFinset → c i x * W (matCoord ι (q i x), p k) = 0 := by
    intro x k hkK i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with h | h
    · simp [h]
    · simp [hWC k hkK _ h]

  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict K).prod m) := by
    obtain ⟨u, hu⟩ := (atTop : Filter (Finset I)).exists_seq_tendsto
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N (z : H × Ω) => ∑ i ∈ u N, c i z.2 * W (matCoord ι (q i z.2), p z.1)) ?_ ?_
    · intro N
      refine (Finset.measurable_sum _ fun i _ => ?_).aestronglyMeasurable
      refine ((hk.mc i).comp measurable_snd).mul ?_
      have : Measurable fun z : H × Ω => ((q i z.2, z.1) : H × H) :=
        ((hk.mq i).comp measurable_snd).prodMk measurable_fst
      exact hGc.measurable.comp this
    · have hae : ∀ᵐ z ∂((μ.restrict K).prod m), z.1 ∈ K :=
        Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_restrict_mem hKm)
      filter_upwards [hae] with z hz
      have hs : HasSum (fun i => c i z.2 * W (matCoord ι (q i z.2), p z.1))
          (∑' i, c i z.2 * W (matCoord ι (q i z.2), p z.1)) :=
        (summable_of_ne_finset_zero (s := (hk.fin z.2 C hC).toFinset) (hvan z.2 z.1 hz)).hasSum
      exact hs.comp hu
  have hint : Integrable (Function.uncurry F) ((μ.restrict K).prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hKm] with k hkK
      exact (hB k hkK).1
    · refine Integrable.mono' (integrable_const B) hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hKm] with k hkK
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hB k hkK).2
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF, ker]
  have hT := hvan x
  set T := (hk.fin x C hC).toFinset
  rw [setIntegral_congr_fun hKm (fun k hkK => tsum_eq_sum (s := T) (hT k hkK))]
  rw [integral_finsetSum]
  · rw [tsum_eq_sum (s := T)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_const_mul _ _
    · intro i hi
      simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      rcases hi with h | h
      · simp [h]
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun k hkK => hWC k hkK _ h), mul_zero]
  · intro i _
    exact (ContinuousOn.integrableOn_compact hK
      (continuous_const.mul (hW.continuous.comp (continuous_const.prodMk hp))).continuousOn)

end MainStatements.WeightKernel
end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix Polynomial
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PLagr

variable {n : ℕ}

lemma cd_mul {F G : Mx n → Matrix (Fin n) (Fin n) ℂ} (hF : ∀ a b, ContDiff ℝ ∞ (fun Y => F Y a b))
    (hG : ∀ a b, ContDiff ℝ ∞ (fun Y => G Y a b)) : ∀ a b, ContDiff ℝ ∞ (fun Y => (F Y * G Y) a b) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => (hF a j).mul (hG j b)

lemma cd_pow (k : ℕ) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => ((Matrix.of Y) ^ k) a b) := by
  induction k with
  | zero => intro a b; simp only [pow_zero]; exact contDiff_const
  | succ k ih =>
    simp only [pow_succ]
    exact cd_mul ih (fun a b => by simp only [Matrix.of_apply]; exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) a b)

lemma cd_aeval (P : ℂ[X]) : ∀ a b, ContDiff ℝ ∞ (fun Y : Mx n => (aeval (Matrix.of Y) P) a b) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => intro a b; simp only [map_add, Matrix.add_apply]; exact (hp a b).add (hq a b)
  | monomial k c =>
    simp only [Polynomial.aeval_monomial]
    exact cd_mul (fun a b => contDiff_const) (cd_pow k)

lemma conj_pow (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (k : ℕ) :
    (g' * D * g) ^ k = g' * D ^ k * g :=
  _root_.UpperTheory.Reformulated.B.Yhd8.main g g' D h1 h2 k

lemma aeval_conj (g g' D : Matrix (Fin n) (Fin n) ℂ) (h1 : g' * g = 1) (h2 : g * g' = 1) (P : ℂ[X]) :
    aeval (g' * D * g) P = g' * aeval D P * g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, conj_pow g g' D h1 h2,
      ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

lemma aeval_diag (l : Fin n → ℂ) (P : ℂ[X]) :
    aeval (diagonal l) P = diagonal fun j => P.eval (l j) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Matrix.diagonal_add]; simp [Polynomial.eval_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [Polynomial.eval_monomial]

end PLagr

open PLagr in
theorem lagr : Lagr := by
  intro n l hl
  refine ⟨fun i Y => fun a b => (aeval (Matrix.of Y) (Lagrange.basis Finset.univ l i)) a b, fun i => ?_, ?_⟩
  · exact contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_aeval _ a b
  · intro i g g' h1 h2
    change aeval (g' * diagonal l * g) (Lagrange.basis Finset.univ l i) = _
    rw [aeval_conj g g' _ h1 h2, aeval_diag]
    have hv : (fun j => (Lagrange.basis Finset.univ l i).eval (l j)) = Pi.single i 1 := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same, Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)]
      · rw [Pi.single_eq_of_ne h, Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)]
    rw [hv, Matrix.diagonal_single]

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PShiftT

def rho (S : ℂ → ℝ) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then ((Real.sqrt (S z) : ℝ) : ℂ)
  else if ‖z‖ < 1 then (((Real.sqrt (S (star z)⁻¹) : ℝ) : ℂ))⁻¹ else 1

lemma key (S : ℂ → ℝ) (hS : ∀ z, 0 < S z) (z w : ℂ) (h : star z * w = 1) :
    star (rho S z) * rho S w = 1 := by
  have hz : z ≠ 0 := by rintro rfl; simp at h
  have hw : w = (star z)⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hw
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(star z)⁻¹‖ = ‖z‖⁻¹ := by rw [norm_inv, norm_star]
  have hcc : (star (star z)⁻¹)⁻¹ = z := by rw [star_inv₀, star_star, inv_inv]
  have e : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hipos : 0 < ‖z‖⁻¹ := inv_pos.mpr hpos
  rcases lt_trichotomy 1 ‖z‖ with h1 | h1 | h1
  · have h2 : ‖z‖⁻¹ < 1 := by nlinarith
    have hs : (((Real.sqrt (S z)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS z)).ne'
    simp only [rho, hn, hcc]
    rw [if_pos h1, if_neg (by linarith), if_pos h2, Complex.star_def, Complex.conj_ofReal]
    exact mul_inv_cancel₀ hs
  · have h2 : ‖z‖⁻¹ = 1 := by rw [← h1, inv_one]
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    simp
  · have h2 : 1 < ‖z‖⁻¹ := by nlinarith
    have hs : (((Real.sqrt (S (star z)⁻¹)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hS _)).ne'
    simp only [rho, hn, hcc]
    rw [if_neg (by linarith), if_pos h1, if_pos h2, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact inv_mul_cancel₀ hs

end MainStatements.WeightKernel.PShiftT

namespace MainStatements.WeightKernel

open MainStatements.WeightKernel.PShiftT in
theorem shiftT : ShiftT := by
  intro n J l hl hJ σ hσ
  classical
  let S : ℂ → ℝ := fun z => if h : ∃ i, l i = z then σ (Classical.choose h) else 1
  have hSpos : ∀ z, 0 < S z := by
    intro z
    simp only [S]
    split_ifs
    · exact hσ _
    · exact zero_lt_one
  have hSl : ∀ i, S (l i) = σ i := by
    intro i
    have h : ∃ j, l j = l i := ⟨i, rfl⟩
    simp only [S, dif_pos h]
    rw [hl (Classical.choose_spec h)]
  refine ⟨fun i => rho S (l i), ?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply] at hij ⊢
    by_cases h0 : J i j = 0
    · simp [h0]
    have e1 : star (l i) * l j = 1 := by
      have : (star (l i) * l j) * J i j = 1 * J i j := by rw [one_mul]; calc _ = star (l i) * J i j * l j := by ring
          _ = J i j := hij
      exact mul_right_cancel₀ h0 this
    have e2 : star (rho S (l i)) * rho S (l j) = 1 := key S hSpos _ _ e1
    calc _ = (star (rho S (l i)) * rho S (l j)) * J i j := by ring
      _ = J i j := by rw [e2, one_mul]
  · intro i hi
    show ‖rho S (l i)‖ ^ 2 = σ i
    rw [rho, if_pos hi, hSl, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hσ i).le]

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

lemma entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    star (l i) * l j = 1 := by
  have e := congrFun (congrFun h i) j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul] at e
  have e2 : (star (l i) * l j - 1) * J i j = 0 := by
    simp only [Pi.star_apply] at e
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)

lemma norm_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    ‖l i‖ * ‖l j‖ = 1 := by
  have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)
  simpa [norm_mul, norm_star] using e

end MainStatements.WeightKernel.PBoundT

namespace MainStatements.WeightKernel

open PBoundT in
theorem boundT : BoundT := by
  intro n J l hdet hinj hl a b ha
  refine ⟨max b (max (1 / a) 1), ?_⟩
  intro τ hτ hbd j
  have col : ∃ i, J i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : J.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j hc
    rw [this] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨i, hij⟩ := col
  have hl2 := norm_entry J l hl i j hij
  have hτ2 := norm_entry J τ hτ i j hij
  rcases lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt
  · have hli : 1 < ‖l i‖ := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ ‖l j‖ := norm_nonneg _
      nlinarith
    have ha' := (hbd i hli).1
    have hτj : ‖τ j‖ ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      have h0 : 0 ≤ ‖τ j‖ := norm_nonneg _
      nlinarith
    exact le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hli : ‖l i‖ = 1 := by
      rw [heq, mul_one] at hl2
      exact hl2
    have ent := entry J l hl i j hij
    have hsq : l i * star (l i) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]
      simp
    have hij' : l i = l j := by
      have : l i * (star (l i) * l j) = l i := by rw [ent, mul_one]
      rw [← mul_assoc, hsq, one_mul] at this
      exact this.symm
    have hieq : i = j := hinj hij'
    subst hieq
    have h0 : 0 ≤ ‖τ i‖ := norm_nonneg _
    have h1 : ‖τ i‖ = 1 := by nlinarith
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_trans (hbd j hgt).2 (le_max_left _ _)

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ ℂ x).comp (contDiff_apply ℝ (Fin n → ℂ) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PIdentOne

def gR {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℝ :=
  B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) * φ (h⁻¹ * s * h)

def G {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℂ :=
  (gR ι s B φ z h : ℂ)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} {ι : H →* Matrix (Fin n) (Fin n) ℂ}
    {s : H} {B : Mx n × Mx n → ℝ} {φ : H → ℝ}

theorem gR_cont (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (hφc : Continuous φ) (z : H) :
    Continuous (gR ι s B φ z) := by
  unfold gR
  have hBc : Continuous B := hB.smooth.continuous
  exact (hBc.comp (continuous_const.prodMk (hι.comp (continuous_const.mul continuous_id)))).mul
    (hφc.comp ((continuous_inv.mul continuous_const).mul continuous_id))

theorem gR_supp (hB : IsWeight ι s B) (hφ : HasCompactSupport φ) (z : H) :
    HasCompactSupport (gR ι s B φ z) := by
  obtain ⟨K, hK, hKp⟩ := hB.proper {z⁻¹ * s * z} (tsupport φ) isCompact_singleton hφ
  refine HasCompactSupport.intro (hK.image (continuous_const_mul z)) fun h hh => ?_
  by_contra hne
  apply hh
  refine ⟨z⁻¹ * h, hKp z (z⁻¹ * h) (Set.mem_singleton _) ?_ ?_, mul_inv_cancel_left z h⟩
  · rw [mul_inv_cancel_left z h]
    exact subset_tsupport _ (fun h0 => hne (by simp [gR, h0]))
  · exact fun h0 => hne (by simp [gR, h0])

theorem fiber (hB : IsWeight ι s B) (dt : Measure (cent s)) [dt.IsMulRightInvariant] (z h : H) :
    ∫ t : cent s, G ι s B φ z (t * h) ∂dt = ∫ t : cent s, G ι s B φ 1 (t * h) ∂dt := by
  obtain ⟨t₀, ht₀, e⟩ := hB.shift z h 1 h
  have key : ∀ v : H, v * s = s * v → (v * h)⁻¹ * s * (v * h) = h⁻¹ * s * h := fun v hv => by
    calc (v * h)⁻¹ * s * (v * h) = h⁻¹ * (v⁻¹ * (s * v)) * h := by group
      _ = h⁻¹ * (v⁻¹ * (v * s)) * h := by rw [hv]
      _ = h⁻¹ * s * h := by group
  have hc : ∀ u : cent s, ((u : H) * h)⁻¹ * s * (u * h) = h⁻¹ * s * h := fun u => key u (mem_cent.1 u.2)
  calc ∫ t : cent s, G ι s B φ z (t * h) ∂dt
        = ∫ t : cent s, G ι s B φ 1 (((t * ⟨t₀, ht₀⟩ : cent s) : H) * h) ∂dt := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [G, gR]
          rw [hc t, hc (t * ⟨t₀, ht₀⟩), ← mul_assoc z⁻¹, e t t.2]
          simp [mul_assoc]
    _ = _ := integral_mul_right_eq_self (fun t : cent s => G ι s B φ 1 ((t : H) * h)) ⟨t₀, ht₀⟩

theorem integral_eq (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (z : H) :
    ∫ h, G ι s B φ z h ∂μ = ∫ h, G ι s B φ 1 h ∂μ := by
  have hi : ∀ w, Integrable (G ι s B φ w) μ := fun w =>
    (Complex.continuous_ofReal.comp (gR_cont hι hB hφc w)).integrable_of_hasCompactSupport
      ((gR_supp hB hφ w).comp_left Complex.ofReal_zero)
  have w1 := (weil_integral (dt := dt) (isClosed_cent s) (hi z)).2.2
  have w2 := (weil_integral (dt := dt) (isClosed_cent s) (hi 1)).2.2
  rw [← w1, ← w2]
  exact congrArg (quotInt _ dt μ) (funext fun x => fiber hB dt z x)

theorem orig_eq (μ : Measure H) [μ.IsHaarMeasure] (z : H) :
    ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ =
      ∫ h, G ι s B φ z h ∂μ := by
  refine (integral_mul_left_eq_self (μ := μ) (fun k => (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) *
    (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ)) z⁻¹).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [G, gR, Complex.ofReal_mul]
  rw [show (z⁻¹ * h)⁻¹ * (z⁻¹ * s * z) * (z⁻¹ * h) = h⁻¹ * s * h by group]

theorem ne_zero (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (hφc : Continuous φ) (hφ : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφs : 0 < φ s) :
    ∫ h, G ι s B φ 1 h ∂μ ≠ 0 := by
  have hpos : 0 < ∫ h, gR ι s B φ 1 h ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (gR_cont hι hB hφc 1)
      (gR_supp hB hφ 1) (fun h => mul_nonneg (hB.nonneg _) (hφ0 _)) ?_
    simp only [gR, inv_one, one_mul, mul_one]
    exact (mul_pos hB.pos hφs).ne'
  simp only [G]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end MainStatements.WeightKernel.PIdentOne

theorem MainStatements.WeightKernel.identOne : IdentOne := by
  intro H _ _ _ _ _ _ _ _ n ι hι s B hB μ _ dt _ _ φ hφc hφ hφ0 hφs
  exact ⟨_, PIdentOne.ne_zero hι hB μ hφc hφ hφ0 hφs, fun z =>
    (PIdentOne.orig_eq μ z).trans (PIdentOne.integral_eq hι hB μ dt hφc hφ z)⟩

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem identTwo : IdentTwo := by
  intro H _ _ _ _ _ _ _ _ n ι hc s B hB μ _ _ dt _ _ φ hφc hφs hO h
  have : μ.IsInvInvariant := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  set f : H → ℂ := fun z => φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) with hfdef
  set F : H → ℂ := fun k => φ (k * (h⁻¹ * s * h) * k⁻¹) *
    (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) with hFdef
  have hsub : ∫ k, F k ∂μ = ∫ z, f z ∂μ := by
    have h1 := integral_mul_right_eq_self (μ := μ) (fun k => F k) h
    have h2 := integral_inv_eq_self (fun k => F (k * h)) μ
    rw [← h1, ← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e : z⁻¹ * h * (h⁻¹ * s * h) * (z⁻¹ * h)⁻¹ = z⁻¹ * s * z := by group
    simp only [hFdef, hfdef, e]
  have hBc : Continuous B := hB.smooth.continuous
  have hfc : Continuous f := by
    have h1 : Continuous fun z : H => z⁻¹ * s * z := by fun_prop
    have h2 : Continuous fun z : H => z⁻¹ * h := by fun_prop
    exact (hφc.comp h1).mul (Complex.continuous_ofReal.comp (hBc.comp ((hc.comp h1).prodMk (hc.comp h2))))
  obtain ⟨K, hK, hKp⟩ := hB.proper (tsupport φ) {h⁻¹ * s * h} hφs isCompact_singleton
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (hK.image (f := fun k => h * k⁻¹) (by fun_prop)) fun z hz => ?_
    by_contra hne
    apply hz
    have hne' : φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) ≠ 0 := hne
    have m1 : z⁻¹ * s * z ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hne')
    have m2 : B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) ≠ 0 := by
      intro h0; apply hne'; rw [h0]; simp
    have m3 : (z * (z⁻¹ * h))⁻¹ * s * (z * (z⁻¹ * h)) ∈ ({h⁻¹ * s * h} : Set H) := by
      rw [mul_inv_cancel_left]; exact Set.mem_singleton _
    exact ⟨z⁻¹ * h, hKp z (z⁻¹ * h) m1 m3 m2, by group⟩
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hW := (weil_integral (T := cent s) (dt := dt) (dh := μ) (isClosed_cent s) hfi).2.2
  set κ : ℂ := ∫ t : cent s, (B (matCoord ι s, matCoord ι ((t : H)⁻¹)) : ℂ) ∂dt with hκ
  have hfib : ∀ x, ∫ t : cent s, f (t * x) ∂dt = φ (x⁻¹ * s * x) * κ := by
    intro x
    obtain ⟨t₀, ht₀, hsh⟩ := hB.shift x h 1 1
    have e1 : ∀ t : cent s, ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * s * x := by
      intro t
      have hts := mem_cent.1 t.2
      have : (t : H)⁻¹ * s * t = s := by rw [mul_assoc, ← hts, inv_mul_cancel_left]
      calc ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * s * t) * x := by group
        _ = x⁻¹ * s * x := by rw [this]
    have e2 : ∀ t : cent s, f (t * x) = φ (x⁻¹ * s * x) *
        (B (matCoord ι s, matCoord ι ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H)⁻¹)) : ℂ) := by
      intro t
      have hs' := hsh (t : H)⁻¹ (inv_mem t.2)
      simp only [inv_one, one_mul, mul_one] at hs'
      have hco : (t : H)⁻¹ * t₀ = ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
      simp only [hfdef, e1]
      rw [show ((t : H) * x)⁻¹ * h = x⁻¹ * (t : H)⁻¹ * h by group, hs', hco]
    simp_rw [e2]
    rw [integral_const_mul]
    congr 1
    exact integral_mul_left_eq_self (fun t : cent s => (B (matCoord ι s, matCoord ι ((t : H))⁻¹) : ℂ)) _
  have hfun : (fun x => ∫ t : cent s, f (t * x) ∂dt) = fun x => conjFn s φ x * κ := funext fun x => hfib x
  show ∫ k, F k ∂μ = 0
  rw [hsub, ← hW, hfun]
  have h0 := hO.2
  unfold quotInt descend at h0 ⊢
  show ∫ q, conjFn s φ q.out * κ ∂quotMeas (cent s) dt μ = 0
  rw [integral_mul_const, h0, zero_mul]

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing GlobalTheory.Proof.parabolic_and_constant_term
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem MainStatements.WeightKernel.cuspAny : MainStatements.WeightKernel.CuspAny := by
  intro D V hodd T U hNoFixed μf hμf ff hff fa hA 𝔉 hP
  have := hμf
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hNoFixed).1
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
  exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
    ν x y).2

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.PArchGroup

theorem cT_star' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem isUnit_of_form {n : ℕ} {J M : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (h : Mᴴ * J * M = J) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h2
  exact hJ.ne_zero h2.symm

theorem isClosed_form {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * J * M = J} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

end MainStatements.WeightKernel.PArchGroup

namespace MainStatements.WeightKernel

open PArchGroup in
theorem archGroup : ArchGroup := by
  intro D V w τ
  have h := isCMExt_host D
  have hu : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
  have hJ : IsUnit (V.gram.map τ.1).det := by
    rw [show V.gram.map τ.1 = τ.1.mapMatrix V.gram from rfl, ← RingHom.map_det]
    exact hu.map _
  have hr : ∀ M, M ∈ Set.range (archMat D.sp.cm.sig V.gram τ) ↔ Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1 := by
    intro M
    constructor
    · rintro ⟨g, rfl⟩
      rw [archMat_eq_archEquiv V.gram h τ g, ← cT_star']
      exact (archEquiv V.gram h τ g).2
    · intro hM
      have hU := isUnit_of_form hJ hM
      have hmem : hU.unit ∈ Formalism.UG.UJ (starRingEnd ℂ) (V.gram.map τ.1) := by
        change Formalism.UG.cT (starRingEnd ℂ) (hU.unit : Matrix (Fin _) (Fin _) ℂ) * V.gram.map τ.1 *
          (hU.unit : Matrix (Fin _) (Fin _) ℂ) = V.gram.map τ.1
        rw [cT_star', IsUnit.unit_spec]
        exact hM
      refine ⟨(archEquiv V.gram h τ).symm ⟨hU.unit, hmem⟩, ?_⟩
      rw [archMat_eq_archEquiv V.gram h τ, MulEquiv.apply_symm_apply]
      exact IsUnit.unit_spec hU
  refine ⟨hJ, ⟨isEmbedding_archMat V.gram h τ, ?_⟩, hr⟩
  have : Set.range (matCoord (archMat D.sp.cm.sig V.gram τ)) =
      {M : Matrix (Fin _) (Fin _) ℂ | Mᴴ * V.gram.map τ.1 * M = V.gram.map τ.1} := by
    ext M
    exact hr M
  rw [this]
  exact isClosed_form _

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel

theorem archUnimod : ArchUnimod := by
  intro D V w μ hμ
  obtain ⟨hcm, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJ' V
  haveI : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := D.sp.cm.sig) w.Completion hcm hJ).1
  exact hU.2.2.2.2.2.2 μ hμ

end MainStatements.WeightKernel

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.WeightKernel

theorem regClassInt_holds : MainStatements.RegularCuspidalTrace.RegClassInt := MainStatements.WeightKernel.RegInt.regClassInt PositivityTheory.Prw.siegelCore_holds

end MainStatements.WeightKernel
end
