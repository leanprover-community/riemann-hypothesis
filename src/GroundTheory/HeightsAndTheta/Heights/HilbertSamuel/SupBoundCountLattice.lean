import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SupBoundBlock.eval_torus_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      c k₀ ^ n * eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem SupBoundBlock.normRatio_torus {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) (A : HermLine ι)
    (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [SupBoundBlock.eval_torus_blockDeg hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem SupBoundBlock.isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem SupBoundBlock.proof (hS : SupNormAgainstL2.Statement) (hR : ResolutionPullback.Statement)
    (hN : NonvanishingDense.Statement) : SupBoundBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨A, L, W, dV, -, hW, hμ, hsec⟩ := hR D K ι Ω d
  obtain ⟨⟨C, hC⟩, -⟩ := hS A L W dV hW
  refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w (map (Int.castRingHom ℂ) f)‖ / d.A.h w ^ n with hg
  set M := max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f with hM
  obtain ⟨s, hs, hps⟩ := hsec n f hf

  have hL2 : Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt 2 * blockL2Norm d n f := by
    have hI : sectionL2NormSq W dV n s = ∫ x, g (blockPt d x) ^ 2 ∂d.dV := by
      rw [sectionL2NormSq, hμ]
      exact integral_congr_ae (Eventually.of_forall hps)
    have h2 : 0 ≤ ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV := integral_nonneg fun _ => sq_nonneg _
    rw [hI, blockL2Norm, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf

  have hres : ∀ x, g (blockPt d x) ≤ M := by
    intro x
    have h1 : g (blockPt d x) ≤ Real.sqrt (ptNormSq W n s x) := by
      rw [hps x, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    have h3 := hC n hn s hs x
    rw [hpow] at h3
    have ha : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc g (blockPt d x) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := h1.trans h3
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * blockL2Norm d n f) := by
          gcongr
      _ = M := by rw [hM]; ring

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (SupBoundBlock.normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hres x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace SupBoundCount

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem continuousOn_lift (d : HSMBlockDatum D K ι Ω) (x₀ : d.R.X) :
    ContinuousOn (d.R.lift x₀) (d.R.U x₀) := by
  intro y hy
  refine (continuousAt_pi.2 fun p => ?_).continuousWithinAt
  obtain ⟨j, hj⟩ := d.R.A.cover y
  have hpt : d.R.A.chart j y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x₀ :=
    ⟨(d.R.A.chart j).map_source hj, by simpa [(d.R.A.chart j).left_inv hj] using hy⟩
  have han := d.R.holo x₀ p j _ hpt
  have h2 : ContinuousAt ((fun y => d.R.lift x₀ y p) ∘ (d.R.A.chart j).symm ∘ d.R.A.chart j) y :=
    han.continuousAt.comp ((d.R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(d.R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(d.R.A.chart j).left_inv hy']

theorem continuous_blockPt {β : Type*} [TopologicalSpace β] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → β} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Continuous fun x => Φ (blockPt d x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have h1 : ContinuousAt (d.R.lift x₀) x₀ := (continuousOn_lift d x₀).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Φ (d.R.lift x₀ x)) x₀ :=
    (hc.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds h0)).comp h1
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show Φ (d.R.lift x₀ x) = Φ (d.R.lift x x)
  rw [he, hinv c _ hc0]

theorem conjPt_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    conjPt (fun p => c p.1 * z p) = fun p => starRingEnd ℂ (c p.1) * conjPt z p := by
  funext p
  simp [conjPt]

theorem conjPt_blockNonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, conjPt z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [conjPt] using hi⟩

theorem continuous_conjPt' : Continuous (conjPt : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) :=
  continuous_pi fun p => Complex.continuous_conj.comp (continuous_apply p)

theorem continuous_conj_blockPt {β : Type*} [TopologicalSpace β] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → β} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Continuous fun x => Φ (conjPt (blockPt d x)) :=
  continuous_blockPt d (Φ := fun z => Φ (conjPt z))
    (hc.comp continuous_conjPt'.continuousOn fun _ hz => conjPt_blockNonzero hz)
    fun c z hc0 => by rw [conjPt_torus, hinv _ _ fun k => (map_ne_zero _).2 (hc0 k)]

theorem integrable_blockPt {E : Type*} [NormedAddCommGroup E] (d : HSMBlockDatum D K ι Ω)
    {Φ : ((Σ k, ι k) → ℂ) → E} (hc : ContinuousOn Φ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → Φ (fun p => c p.1 * z p) = Φ z) :
    Integrable (fun x => Φ (blockPt d x)) d.dV ∧ Integrable (fun x => Φ (conjPt (blockPt d x))) d.dV := by
  have := d.vol.1
  exact ⟨integrableOn_univ.1 ((continuous_blockPt d hc hinv).continuousOn.integrableOn_compact isCompact_univ),
    integrableOn_univ.1 ((continuous_conj_blockPt d hc hinv).continuousOn.integrableOn_compact isCompact_univ)⟩

theorem eval_conjPt (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  have : (starRingEnd ℂ).comp ((eval z).comp (map (Int.castRingHom ℂ))) =
      (eval (conjPt z)).comp (map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_) <;> simp [conjPt]
  exact (RingHom.congr_fun this f).symm

theorem conjPt_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    conjPt z ∈ mcPts P :=
  ⟨conjPt_blockNonzero hz.1, fun f hf => by rw [eval_conjPt, hz.2 f hf, map_zero]⟩

theorem blockPt_mem (d : HSMBlockDatum D K ι Ω) (x : d.R.X) : blockPt d x ∈ mcPts (mCoordIdeal d.y) :=
  d.R.mem x x (d.R.mem_U x)

theorem eval_map_int_rat (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f)) = eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.map_map]
  congr 2

theorem h_continuousOn (d : HSMBlockDatum D K ι Ω) : ContinuousOn d.A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  d.semipos.1.continuousOn

theorem prod_unitDeg (c : K → ℂ) (k₀ : K) : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
  rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
  simp [unitDeg]

theorem ratio_continuousOn (d : HSMBlockDatum D K ι Ω) (f : MRing ι) (n : ℕ) :
    ContinuousOn (fun z => ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousOn.div ((h_continuousOn d).pow n)
    fun z hz => pow_ne_zero _ (d.A.pos z hz).ne'

theorem ratio_torus (d : HSMBlockDatum D K ι Ω) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg d.k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    ‖eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f)‖ / d.A.h (fun p => c p.1 * z p) ^ n =
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n :=
  SupBoundBlock.normRatio_torus hf d.A d.deg ⟨c, hc, rfl⟩

def pairRe (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ((eval z (map (Int.castRingHom ℂ) f)).re * (eval z (map (Int.castRingHom ℂ) f')).re +
    (eval z (map (Int.castRingHom ℂ) f)).im * (eval z (map (Int.castRingHom ℂ) f')).im) / A.h z ^ (2 * n)

theorem pairValH_re (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) :
    (pairValH A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') z).re = pairRe A n f f' z := by
  simp only [pairValH, eval_map_int_rat, pairRe, Complex.div_ofReal_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

theorem pairValH_torus (d : HSMBlockDatum D K ι Ω) {n : ℕ} {f f' : MRing ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) (hf' : IsMultiHomog f' (blockDeg d.k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') (fun p => c p.1 * z p) =
      pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') z := by
  simp only [pairValH, eval_map_int_rat]
  rw [SupBoundBlock.eval_torus_blockDeg hf, SupBoundBlock.eval_torus_blockDeg hf', d.A.smul c z hc, d.deg,
    prod_unitDeg]
  set u := c d.k₀ ^ n
  set w := eval z (map (Int.castRingHom ℂ) f)
  set w' := eval z (map (Int.castRingHom ℂ) f')
  have hu : u * starRingEnd ℂ u = ((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm n 2]
  have hne : ((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.2 (hc d.k₀))
  calc u * w * starRingEnd ℂ (u * w') / (((‖c d.k₀‖ * d.A.h z) ^ (2 * n) : ℝ) : ℂ)
      = (u * starRingEnd ℂ u) * (w * starRingEnd ℂ w') /
          (((‖c d.k₀‖ ^ (2 * n) : ℝ) : ℂ) * ((d.A.h z ^ (2 * n) : ℝ) : ℂ)) := by
        rw [map_mul, mul_pow]
        push_cast
        ring
    _ = w * starRingEnd ℂ w' / ((d.A.h z ^ (2 * n) : ℝ) : ℂ) := by
        rw [hu]
        exact mul_div_mul_left _ _ hne

theorem pairValH_continuousOn (d : HSMBlockDatum D K ι Ω) (n : ℕ) (f f' : MRing ι) :
    ContinuousOn (pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f'))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have he : pairValH d.A n (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) f') = fun z =>
      eval z (map (Int.castRingHom ℂ) f) * starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f')) /
        ((d.A.h z ^ (2 * n) : ℝ) : ℂ) := by
    funext z
    simp only [pairValH, eval_map_int_rat]
  rw [he]
  refine ContinuousOn.div (((MvPolynomial.continuous_eval _).mul
    (Complex.continuous_conj.comp (MvPolynomial.continuous_eval _))).continuousOn)
    (Complex.continuous_ofReal.comp_continuousOn ((h_continuousOn d).pow _)) fun z hz => ?_
  exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (d.A.pos z hz).ne')

theorem blockGram_eq (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l =
      (1 / 2) * ((∫ x, pairRe d.A n (f k) (f l) (blockPt d x) ∂d.dV) +
        ∫ x, pairRe d.A n (f k) (f l) (conjPt (blockPt d x)) ∂d.dV) := by
  have hi := integrable_blockPt d (pairValH_continuousOn d n (f k) (f l))
    (pairValH_torus d (hf k) (hf l))
  have e1 := (integral_re hi.1).symm
  have e2 := (integral_re hi.2).symm
  simp only [RCLike.re_to_complex, pairValH_re] at e1 e2
  simp only [blockGram]
  rw [e1, e2]

theorem pairRe_integrable (d : HSMBlockDatum D K ι Ω) (n : ℕ) {f f' : MRing ι}
    (hf : IsMultiHomog f (blockDeg d.k₀ n)) (hf' : IsMultiHomog f' (blockDeg d.k₀ n)) :
    Integrable (fun x => pairRe d.A n f f' (blockPt d x)) d.dV ∧
      Integrable (fun x => pairRe d.A n f f' (conjPt (blockPt d x))) d.dV := by
  have hi := integrable_blockPt d (pairValH_continuousOn d n f f') (pairValH_torus d hf hf')
  simp only [← pairValH_re]
  exact ⟨hi.1.re, hi.2.re⟩

def comb {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∑ k, (a k : ℂ) * eval z (map (Int.castRingHom ℂ) (f k))

theorem comb_re {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    (comb f a z).re = ∑ k, a k * (eval z (map (Int.castRingHom ℂ) (f k))).re := by
  simp [comb, Complex.re_sum]

theorem comb_im {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    (comb f a z).im = ∑ k, a k * (eval z (map (Int.castRingHom ℂ) (f k))).im := by
  simp [comb, Complex.im_sum]

theorem quad_pairRe (A : HermLine ι) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι) (a : Fin r → ℝ)
    (z : (Σ k, ι k) → ℂ) :
    ∑ k, a k * ∑ l, pairRe A n (f k) (f l) z * a l = ‖comb f a z‖ ^ 2 / A.h z ^ (2 * n) := by
  rw [Complex.sq_norm, Complex.normSq_apply, comb_re, comb_im, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [pairRe]
  ring

theorem sum_integral {X : Type*} [MeasurableSpace X] (μ : Measure X) {r : ℕ} (a b : Fin r → Fin r → ℝ)
    (g : Fin r → Fin r → X → ℝ) (hg : ∀ k l, Integrable (g k l) μ) :
    ∑ k, ∑ l, a k l * (∫ x, g k l x ∂μ) * b k l = ∫ x, ∑ k, ∑ l, a k l * g k l x * b k l ∂μ := by
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => ((hg k l).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun l _ => ((hg k l).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_mul_const, integral_const_mul]

theorem gram_quad (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) =
      (1 / 2) * ((∫ x, ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n) ∂d.dV) +
        ∫ x, ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n) ∂d.dV) := by
  simp only [dotProduct, Matrix.mulVec, blockGram_eq d n f hf]
  have h1 := sum_integral d.dV (fun k _ => a k) (fun _ l => a l)
    (fun k l x => pairRe d.A n (f k) (f l) (blockPt d x)) fun k l => (pairRe_integrable d n (hf k) (hf l)).1
  have h2 := sum_integral d.dV (fun k _ => a k) (fun _ l => a l)
    (fun k l x => pairRe d.A n (f k) (f l) (conjPt (blockPt d x)))
    fun k l => (pairRe_integrable d n (hf k) (hf l)).2
  simp only [← quad_pairRe, Finset.mul_sum, ← mul_assoc] at h1 h2 ⊢
  rw [← h1, ← h2, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isMultiHomog_zsum {r : ℕ} (f : Fin r → MRing ι) (m : Fin r → ℤ) {e : K → ℕ}
    (hf : ∀ k, IsMultiHomog (f k) e) : IsMultiHomog (∑ k, m k • f k) e := by
  classical
  intro μ hμ k
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hμ)
  exact hf j μ (MvPolynomial.support_smul hj) k

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem comb_int {r : ℕ} (f : Fin r → MRing ι) (m : Fin r → ℤ) (z : (Σ k, ι k) → ℂ) :
    comb f (fun k => (m k : ℝ)) z = eval z (map (Int.castRingHom ℂ) (∑ k, m k • f k)) := by
  simp [comb, map_sum, zsmul_eq_mul]

theorem blockL2Norm_sum_eq_sqrt_gram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (m : Fin r → ℤ) :
    blockL2Norm d n (∑ k, m k • f k) = Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
      (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ))) := by
  rw [gram_quad d n f hf, blockL2Norm]
  simp only [comb_int, div_pow, ← pow_mul']

theorem blockL2Norm_le_one_of_sup_bound (d : HSMBlockDatum D K ι Ω) (n : ℕ) {F : MRing ι} (hF : IsMultiHomog F (blockDeg d.k₀ n))
    (h : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖eval z (map (Int.castRingHom ℂ) F)‖ ≤ d.A.h z ^ n) :
    blockL2Norm d n F ≤ 1 := by
  have := d.vol.1
  have hi := integrable_blockPt d (Φ := fun z => (‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n) ^ 2)
    ((ratio_continuousOn d F n).pow 2) fun c z hc => by rw [ratio_torus d hF c z hc]
  have hle : ∀ z ∈ mcPts (mCoordIdeal d.y),
      (‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n) ^ 2 ≤ 1 := by
    intro z hz
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    have h1 : ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ 1 := (div_le_one hp).2 (h z hz)
    have h0 : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n := by positivity
    nlinarith
  have h1 : ∫ x, (‖eval (blockPt d x) (map (Int.castRingHom ℂ) F)‖ / d.A.h (blockPt d x) ^ n) ^ 2 ∂d.dV ≤ 1 :=
    calc _ ≤ ∫ _, (1 : ℝ) ∂d.dV := integral_mono hi.1 (integrable_const _) fun x => hle _ (blockPt_mem d x)
      _ = 1 := by simp
  have h2 : ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) F)‖ /
      d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV ≤ 1 :=
    calc _ ≤ ∫ _, (1 : ℝ) ∂d.dV := integral_mono hi.2 (integrable_const _)
          fun x => hle _ (conjPt_mem_mcPts (blockPt_mem d x))
      _ = 1 := by simp
  rw [blockL2Norm]
  calc Real.sqrt _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

theorem isSmallH_iff (d : HSMBlockDatum D K ι Ω) (n : ℕ) {F : MRing ι} (hF : IsMultiHomog F (blockDeg d.k₀ n)) :
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y F) ↔
      ∀ z ∈ mcPts (mCoordIdeal d.y), ‖eval z (map (Int.castRingHom ℂ) F)‖ ≤ d.A.h z ^ n := by
  constructor
  · intro h z hz
    have := h (blockDeg d.k₀ n) 0 F 1 z hF isMultiHomog_one'
      (fun k => by by_cases hk : k = d.k₀ <;> simp [d.deg, blockDeg, unitDeg, hk]) (by simp) hz
    simpa using this
  · intro h dg dh g g' z hg hg' hdeg hval hz
    have hdg : dg = blockDeg d.k₀ n + dh := by
      funext k
      have := hdeg k
      rw [d.deg] at this
      by_cases hk : k = d.k₀
      · subst hk
        simp only [unitDeg, if_true, mul_one] at this
        simp only [Pi.add_apply, blockDeg, if_true]
        omega
      · simp only [unitDeg, hk, if_false, mul_zero, add_zero] at this
        simp only [Pi.add_apply, blockDeg, hk, if_false, zero_add]
        omega
    have hmh : IsMultiHomog (g - F * g') dg := isMultiHomog_sub' hg (hdg ▸ isMultiHomog_mul' hF hg')
    have hy : aeval d.y (g - F * g') = 0 := by rw [map_sub, map_mul, hval, sub_self]
    have hmem : g - F * g' ∈ mCoordIdeal d.y := by
      show mConeMap d.y _ = 0
      rw [ProjLine.mConeMap_eq_of_isMultiHomog d.y hmh, hy, map_zero, zero_mul]
    have h0 := hz.2 _ hmem
    rw [map_sub, map_mul, eval_sub, eval_mul, sub_eq_zero] at h0
    rw [h0, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg _)

end SupBoundCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Module Metric
open scoped ENNReal

noncomputable section

namespace MinkowskiCount

section Count

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in

theorem finite_latticePoints (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

theorem unitBallVolume_pos (R : ℕ) : 0 < unitBallVolume R :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem volume_ball_one :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem volume_ball_half_le (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _

theorem log_count (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith

end Count

theorem cube_le_unitBallVolume (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h

theorem proof : MinkowskiCount.Statement :=
  ⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩

end MinkowskiCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace SupBoundCount

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem mCoordIdeal_le_coordIdeal (y : (Σ k, ι k) → Ω) : mCoordIdeal y ≤ coordIdeal ℤ y := by
  have hext : coneMap ℤ y =
      ((aeval fun _ : K => (Polynomial.X : Polynomial Ω)).restrictScalars ℤ).comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [coneMap, mConeMap]
  intro f hf
  change coneMap ℤ y f = 0
  rw [hext, AlgHom.comp_apply]
  change _ = 0 at hf
  have hf' : mConeMap y f = 0 := hf
  rw [hf', map_zero]

theorem aeval_map_int (y : (Σ k, ι k) → Ω) (g : MRing ι) : aeval y (map (Int.castRingHom ℚ) g) = aeval y g := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem coeff_eq_zero {y : (Σ k, ι k) → Ω} {r : ℕ} {f : Fin r → MRing ι}
    (hli : LinearIndependent ℤ fun k => aeval y (f k)) (hne : (mcPts (mCoordIdeal y)).Nonempty)
    {a : Fin r → ℂ} (h : ∀ z ∈ mcPts (mCoordIdeal y), ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) = 0) :
    a = 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne

  have hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    by_contra hk
    push_neg at hk
    obtain ⟨i, hi⟩ := hz₀.1 k
    apply hi
    have hmem : (X ⟨k, i⟩ : MRing ι) ∈ mCoordIdeal y := by
      change mConeMap y (X ⟨k, i⟩) = 0
      simp [mConeMap, hk i]
    simpa using hz₀.2 _ hmem
  choose i₀ hi₀ using hblk
  set u : MRing ι := ∏ k, X ⟨k, i₀ k⟩
  have hu : aeval y u ≠ 0 := by
    simp only [u, map_prod, aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hi₀ k
  set b : Fin r → MvPolynomial (Σ k, ι k) ℚ := fun k => map (Int.castRingHom ℚ) (f k * u)
  have hq : LinearIndependent ℚ fun k => aeval y (f k) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hs : LinearIndependent ℚ fun k => aeval y (b k) := by
    have hinj : LinearMap.ker (LinearMap.mulRight ℚ (aeval y u)) = ⊥ :=
      LinearMap.ker_eq_bot.2 fun s t hst => mul_right_cancel₀ hu hst
    have heq : (fun k => aeval y (b k)) = (LinearMap.mulRight ℚ (aeval y u)) ∘ fun k => aeval y (f k) := by
      funext k
      simp [b, aeval_map_int, LinearMap.mulRight_apply]
    rw [heq]
    exact hq.map' _ hinj
  refine coeff_eq_zero_of_vanish hs fun z hz => ?_
  have hsec : ∀ k, secFun (b k) z = eval z (map (Int.castRingHom ℂ) (f k)) * eval z (map (Int.castRingHom ℂ) u) := by
    intro k
    simp only [secFun, b, eval_map_int_rat, map_mul, eval_mul]
  simp only [hsec, ← mul_assoc, ← Finset.sum_mul]
  by_cases hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [h z ⟨hz', fun g hg => hz g (mCoordIdeal_le_coordIdeal y hg)⟩, zero_mul]
  · push_neg at hz'
    obtain ⟨k, hk⟩ := hz'
    refine mul_eq_zero_of_right _ ?_
    simp only [u, map_prod, map_X, eval_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (hk (i₀ k))

variable {D : ℕ}

theorem pairRe_comm (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) :
    pairRe A n f f' z = pairRe A n f' f z := by
  simp only [pairRe]
  ring

theorem comb_smul {r : ℕ} (f : Fin r → MRing ι) (t : ℝ) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    comb f (t • a) z = t * comb f a z := by
  simp [comb, Finset.mul_sum, mul_assoc]

theorem quad_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (a : Fin r → ℝ) :
    (t • a) ⬝ᵥ (G *ᵥ (t • a)) = t ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem continuous_comb {r : ℕ} (f : Fin r → MRing ι) (z : (Σ k, ι k) → ℂ) :
    Continuous fun a : Fin r → ℝ => comb f a z := by
  unfold comb
  fun_prop

theorem continuous_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) :
    Continuous fun a : Fin r → ℝ => a ⬝ᵥ (G *ᵥ a) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem sup_real (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F)
    (a : Fin r → ℝ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal d.y)) :
    ‖comb f a z‖ / d.A.h z ^ n ≤
      c * Real.sqrt (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hint : ∀ m : Fin r → ℤ, ‖comb f (fun k => (m k : ℝ)) z‖ / d.A.h z ^ n ≤
      c * Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
        (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ))) := by
    intro m
    rw [comb_int, ← blockL2Norm_sum_eq_sqrt_gram d n f hf m]
    exact hsup _ (isMultiHomog_zsum f m hf) z hz
  have hrat : ∀ q : Fin r → ℚ, ‖comb f (fun k => (q k : ℝ)) z‖ / d.A.h z ^ n ≤
      c * Real.sqrt ((fun k => (q k : ℝ)) ⬝ᵥ
        (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (q k : ℝ))) := by
    intro q
    set N : ℕ := ∏ k, (q k).den with hNdef
    have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Finset.prod_pos fun k _ => (q k).den_pos)
    set m : Fin r → ℤ := fun k => (q k).num * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℤ) with hmdef
    have hm : (fun k => (q k : ℝ)) = (1 / (N : ℝ)) • fun k => (m k : ℝ) := by
      funext k
      have h1 : ((q k : ℚ) : ℝ) * ((q k).den : ℝ) = ((q k).num : ℝ) := by
        exact_mod_cast Rat.mul_den_eq_num (q k)
      have h2 : (N : ℝ) = ((q k).den : ℝ) * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ) := by
        rw [hNdef, ← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ k)]
        push_cast
        rfl
      simp only [Pi.smul_apply, smul_eq_mul, hmdef]
      push_cast
      rw [← h1, h2]
      have hd : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
      have hp : ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast (q j).den_nz
      field_simp
    set t : ℝ := 1 / (N : ℝ)
    have ht : 0 < t := by positivity
    rw [hm, comb_smul, quad_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, norm_mul,
      Complex.norm_of_nonneg ht.le, mul_div_assoc]
    calc t * (‖comb f (fun k => (m k : ℝ)) z‖ / d.A.h z ^ n)
        ≤ t * (c * Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
          (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hint m) ht.le
      _ = _ := by ring
  have hd : DenseRange (fun q : Fin r → ℚ => fun k => (q k : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on a ?_ hrat
  exact isClosed_le ((continuous_norm.comp (continuous_comb f z)).div_const _)
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_quad _)))

theorem mcPts_nonempty (d : HSMBlockDatum D K ι Ω) : (mcPts (mCoordIdeal d.y)).Nonempty := by
  have := d.vol.1
  obtain ⟨x⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : d.dV Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  exact ⟨_, blockPt_mem d x⟩

theorem gram_posDef (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (hli : LinearIndependent ℤ fun k => aeval d.y (f k))
    {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) :
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · refine Matrix.IsHermitian.ext fun k l => ?_
    rw [star_trivial, blockGram_eq d n f hf, blockGram_eq d n f hf]
    simp only [pairRe_comm d.A n (f l) (f k)]
  · rw [star_trivial]
    by_contra hle
    push_neg at hle
    apply ha
    have hz : ∀ z ∈ mcPts (mCoordIdeal d.y),
        ∑ k, ((a k : ℝ) : ℂ) * eval z (map (Int.castRingHom ℂ) (f k)) = 0 := by
      intro z hz
      have h1 := sup_real d n f hf hc hsup a hz
      rw [Real.sqrt_eq_zero'.2 hle, mul_zero] at h1
      have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
      have h2 : ‖comb f a z‖ ≤ 0 := by
        have := (div_le_iff₀ hp).1 h1
        simpa using this
      exact norm_eq_zero.1 (le_antisymm h2 (norm_nonneg _))
    have := coeff_eq_zero hli (mcPts_nonempty d) hz
    funext k
    have := congrFun this k
    simpa using this

theorem quad_inv_le {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {x : Fin r → ℝ} {c : ℝ}
    (h : ∀ a : Fin r → ℝ, (a ⬝ᵥ x) ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a))) : x ⬝ᵥ (G⁻¹ *ᵥ x) ≤ c ^ 2 := by
  have hu : IsUnit G.det := (hG.det_pos).ne'.isUnit
  set a := G⁻¹ *ᵥ x with ha
  have hGa : G *ᵥ a = x := by rw [ha, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hq : 0 ≤ x ⬝ᵥ a := by
    have := hG.posSemidef.dotProduct_mulVec_nonneg a
    rw [star_trivial, hGa, dotProduct_comm] at this
    exact this
  have h1 := h a
  rw [hGa, dotProduct_comm a x] at h1
  rcases hq.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

theorem rank_le (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (hli : LinearIndependent ℤ fun k => aeval d.y (f k))
    {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) :
    (r : ℝ) ≤ 2 * c ^ 2 := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  have hG : G.PosDef := hGdef ▸ gram_posDef d n f hf hli hc hsup
  have hGe : ∀ k l, G k l = (1 / 2) * ((∫ x, pairRe d.A n (f k) (f l) (blockPt d x) ∂d.dV) +
      ∫ x, pairRe d.A n (f k) (f l) (conjPt (blockPt d x)) ∂d.dV) := fun k l => by
    rw [hGdef]
    exact blockGram_eq d n f hf k l
  have hu : IsUnit G.det := hG.det_pos.ne'.isUnit
  have := d.vol.1
  have hr : (r : ℝ) = ∑ k, ∑ l, G⁻¹ k l * G l k * 1 := by
    have h1 := congrArg Matrix.trace (nonsing_inv_mul G hu)
    rw [trace_one, Fintype.card_fin] at h1
    rw [← h1]
    simp [trace, mul_apply]
  have hQ : ∀ a, 0 ≤ a ⬝ᵥ (G *ᵥ a) := fun a => by
    simpa using hG.posSemidef.dotProduct_mulVec_nonneg a
  have hpt : ∀ w ∈ mcPts (mCoordIdeal d.y),
      ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 ≤ 2 * c ^ 2 := by
    intro w hw
    set H := d.A.h w ^ n with hH
    have hH0 : 0 < H := pow_pos (d.A.pos w hw.1) n
    set x : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).re / H with hx
    set y' : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).im / H with hy'
    have hsum : ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 =
        x ⬝ᵥ (G⁻¹ *ᵥ x) + y' ⬝ᵥ (G⁻¹ *ᵥ y') := by
      simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [pairRe, hx, hy', hH, pow_mul']
      field_simp
    have hbd : ∀ a : Fin r → ℝ, ‖comb f a w‖ / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) := fun a => by
      rw [hGdef]
      exact sup_real d n f hf hc hsup a hw
    have hxa : ∀ a, (a ⬝ᵥ x) ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
      intro a
      have e : a ⬝ᵥ x = (comb f a w).re / H := by
        simp only [dotProduct, hx, comb_re, Finset.sum_div, mul_div_assoc]
      rw [e]
      have h1 : |(comb f a w).re| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) :=
        le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hH0.le) (hbd a)
      have h0 : 0 ≤ |(comb f a w).re| / H := by positivity
      calc ((comb f a w).re / H) ^ 2 = (|(comb f a w).re| / H) ^ 2 := by rw [div_pow, div_pow, sq_abs]
        _ ≤ (c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by rw [mul_pow, Real.sq_sqrt (hQ a)]
    have hya : ∀ a, (a ⬝ᵥ y') ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
      intro a
      have e : a ⬝ᵥ y' = (comb f a w).im / H := by
        simp only [dotProduct, hy', comb_im, Finset.sum_div, mul_div_assoc]
      rw [e]
      have h1 : |(comb f a w).im| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) :=
        le_trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) hH0.le) (hbd a)
      have h0 : 0 ≤ |(comb f a w).im| / H := by positivity
      calc ((comb f a w).im / H) ^ 2 = (|(comb f a w).im| / H) ^ 2 := by rw [div_pow, div_pow, sq_abs]
        _ ≤ (c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by rw [mul_pow, Real.sq_sqrt (hQ a)]
    rw [hsum]
    have := quad_inv_le hG hxa
    have := quad_inv_le hG hya
    linarith
  have hI : ∀ k l, Integrable (fun x => pairRe d.A n (f l) (f k) (blockPt d x)) d.dV ∧
      Integrable (fun x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) d.dV :=
    fun k l => pairRe_integrable d n (hf l) (hf k)
  have h1 := sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1)
    (fun k l x => pairRe d.A n (f l) (f k) (blockPt d x)) fun k l => (hI k l).1
  have h2 := sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1)
    (fun k l x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) fun k l => (hI k l).2
  have hr' : (r : ℝ) = (1 / 2) *
      ((∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (blockPt d x) ∂d.dV) * 1) +
        ∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) ∂d.dV) * 1) := by
    rw [hr, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hGe]
    ring
  rw [hr', h1, h2]
  have hint1 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1) d.dV :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).1.const_mul _).mul_const _)
  have hint2 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1)
      d.dV :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).2.const_mul _).mul_const _)
  have i1 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1 ∂d.dV ≤ 2 * c ^ 2 :=
    calc _ ≤ ∫ _, 2 * c ^ 2 ∂d.dV := integral_mono hint1 (integrable_const _) fun x => hpt _ (blockPt_mem d x)
      _ = 2 * c ^ 2 := by simp
  have i2 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1 ∂d.dV ≤ 2 * c ^ 2 :=
    calc _ ≤ ∫ _, 2 * c ^ 2 ∂d.dV := integral_mono hint2 (integrable_const _)
          fun x => hpt _ (conjPt_mem_mcPts (blockPt_mem d x))
      _ = 2 * c ^ 2 := by simp
  linarith

theorem exists_gram {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Fin r → EuclideanSpace ℝ (Fin r), Matrix.gram ℝ B = G := by
  classical
  set U : Matrix (Fin r) (Fin r) ℝ := ↑hG.1.eigenvectorUnitary
  set M : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (hG.1.eigenvalues i)) * star U
  have hMM : star M * M = G := by
    conv_rhs => rw [hG.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp only [M, U, star_mul, star_star, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, star_trivial,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    simp [Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
  refine ⟨fun k => WithLp.toLp 2 (fun i => M i k), ?_⟩
  ext k l
  rw [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, ← hMM]
  simp [dotProduct, mul_apply, Matrix.star_eq_conjTranspose, mul_comm]

theorem count_of_gram {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {ρ : ℝ} (hρ : 0 < ρ)
    (P : (Fin r → ℤ) → Prop)
    (hP1 : ∀ m : Fin r → ℤ, (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) ≤ ρ ^ 2 → P m)
    (hP2 : ∀ m : Fin r → ℤ, P m → (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) ≤ 1) :
    {m | P m}.Finite ∧
      Real.log (unitBallVolume r) + r * Real.log (ρ / 2) - (1 / 2) * Real.log G.det ≤
        Real.log (Nat.card {m // P m}) := by
  classical
  obtain ⟨B, hB⟩ := exists_gram hG
  have hli : LinearIndependent ℝ B := Matrix.linearIndependent_of_posDef_gram (hB ▸ hG)
  have hcard : Fintype.card (Fin r) = Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) := by simp
  obtain ⟨Bb, hBb⟩ : ∃ Bb : Module.Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)), ⇑Bb = B :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' B hli hcard, coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  let e : (Fin r → ℤ) → EuclideanSpace ℝ (Fin r) := fun m => ∑ k, m k • B k
  have hnorm : ∀ m, ‖e m‖ ^ 2 = (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) := by
    intro m
    rw [← real_inner_self_eq_norm_sq, ← hB]
    simp only [e, sum_inner, inner_sum, dotProduct, mulVec, Matrix.gram_apply, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ (m l), ← Int.cast_smul_eq_zsmul ℝ (m k), real_inner_smul_left,
      real_inner_smul_right, real_inner_comm (B l) (B k)]
    ring
  have hmem : ∀ x, x ∈ Submodule.span ℤ (Set.range Bb) ↔ ∃ m, e m = x := by
    intro x
    rw [hBb, Submodule.mem_span_range_iff_exists_fun]
  have hliZ : LinearIndependent ℤ B := hli.restrict_scalars' ℤ
  have heinj : Function.Injective e := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • B k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hliZ _ h0 k)
  have hfinP : {m | P m}.Finite := by
    refine ((MinkowskiCount.finite_latticePoints (Submodule.span ℤ (Set.range Bb)) 1).preimage
      heinj.injOn).subset fun m hm => ⟨(hmem _).2 ⟨m, rfl⟩, ?_⟩
    have h1 := hP2 m hm
    rw [← hnorm] at h1
    nlinarith [norm_nonneg (e m)]
  refine ⟨hfinP, ?_⟩
  have hM := MinkowskiCount.proof.1 (EuclideanSpace ℝ (Fin r)) (Submodule.span ℤ (Set.range Bb)) ρ hρ
  rw [finrank_euclideanSpace_fin] at hM
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range Bb)) = Real.sqrt G.det := by
    rw [covolume_eq_sqrt_det_gram _ (Bb.restrictScalars ℤ), ← hB]
    congr 3
    funext k
    simp [Module.Basis.restrictScalars_apply, hBb]
  rw [hcov, Real.log_sqrt hG.det_pos.le] at hM
  have hT : {x | x ∈ Submodule.span ℤ (Set.range Bb) ∧ ‖x‖ ≤ ρ} = e '' {m | ‖e m‖ ≤ ρ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hxn⟩
      obtain ⟨m, rfl⟩ := (hmem x).1 hx
      exact ⟨m, hxn, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(hmem _).2 ⟨m, rfl⟩, hm⟩
  rw [hT, Set.ncard_image_of_injective _ heinj] at hM
  have hsub : {m | ‖e m‖ ≤ ρ} ⊆ {m | P m} := fun m hm => by
    refine hP1 m ?_
    rw [← hnorm]
    have : ‖e m‖ ≤ ρ := hm
    nlinarith [norm_nonneg (e m)]
  have hpos : 0 < ({m | ‖e m‖ ≤ ρ}.ncard : ℝ) := by
    have h0 : (0 : Fin r → ℤ) ∈ {m | ‖e m‖ ≤ ρ} := by
      simp [e, hρ.le]
    exact_mod_cast Set.ncard_pos (hfinP.subset hsub) |>.2 ⟨_, h0⟩
  have hle : ({m | ‖e m‖ ≤ ρ}.ncard : ℝ) ≤ (Nat.card {m // P m} : ℝ) := by
    show _ ≤ ((Nat.card ↥{m | P m} : ℕ) : ℝ)
    rw [Nat.card_coe_set_eq]
    exact_mod_cast Set.ncard_le_ncard hsub hfinP
  have := Real.log_le_log hpos hle
  linarith

theorem isMultiHomog_zero' (e : K → ℕ) : IsMultiHomog (0 : MRing ι) e := by
  intro m hm
  simp at hm

theorem isMultiHomog_add' {f g : MRing ι} {e : K → ℕ} (hf : IsMultiHomog f e) (hg : IsMultiHomog g e) :
    IsMultiHomog (f + g) e := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem exists_form_of_mem (y : (Σ k, ι k) → Ω) (e : K → ℕ) {s : Ω}
    (hs : s ∈ Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s}) :
    ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s := by
  induction hs using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, isMultiHomog_zero' e, map_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', rfl⟩ := hz
    exact ⟨g + g', isMultiHomog_add' hg hg', map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨a • g, fun m hm => hg m (MvPolynomial.support_smul hm), ?_⟩
    rw [map_zsmul]

theorem exists_isSecBasisM (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) :
    ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y k₀ n p.2 := by
  classical
  set e := blockDeg k₀ n with he
  set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s} with hN
  set Ms : Set ((Σ k, ι k) →₀ ℕ) := {m | ∀ k, ∑ i, m ⟨k, i⟩ = e k} with hMs
  have hMsf : Ms.Finite := by
    refine ((Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (e p.1)) fun p => Set.finite_Iic _).preimage
      (DFunLike.coe_injective.injOn)).subset fun m hm p _ => ?_
    obtain ⟨k, i⟩ := p
    show m ⟨k, i⟩ ≤ e k
    rw [← hm k]
    exact Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set T : Set Ω := (fun m => aeval y (monomial m (1 : ℤ))) '' Ms with hT
  have hTf : T.Finite := hMsf.image _
  have hle : N ≤ Submodule.span ℤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [← mul_one (coeff m g), ← smul_eq_mul, ← smul_monomial, map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, fun k => hg m hm k, rfl⟩)
  have : IsNoetherian ℤ (Submodule.span ℤ T) := isNoetherian_span_of_finite ℤ hTf
  have : IsNoetherian ℤ N := isNoetherian_of_le hle
  let bN := Module.finBasis ℤ N
  have hval : ∀ j, ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = (bN j : Ω) := fun j =>
    exists_form_of_mem y e (bN j).2
  choose g hg hgy using hval
  refine ⟨⟨Module.finrank ℤ N, fun j => map (Int.castRingHom ℚ) (g j)⟩, fun j => ⟨g j, hg j, rfl⟩, ?_, ?_⟩
  · have h1 : (fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype ∘ bN := by
      funext j
      simp [aeval_map_int, hgy]
    rw [h1]
    exact bN.linearIndependent.map' _ (Submodule.ker_subtype _)
  · have h1 : (Set.range fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype '' Set.range bN := by
      rw [← Set.range_comp]
      congr 1
      funext j
      simp [aeval_map_int, hgy]
    rw [h1, Submodule.span_image, bN.span_eq, Submodule.map_subtype_top]
    rfl

theorem finrank_secM {y : (Σ k, ι k) → Ω} {k₀ : K} {n r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ}
    (hb : IsSecBasisM y k₀ n b) : Module.finrank ℤ (secM y (blockDeg k₀ n)) = r := by
  rw [← hb.2.2]
  have e : (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup ≃+
      (Submodule.span ℤ (Set.range fun j => aeval y (b j))) := AddEquiv.refl _
  rw [e.toIntLinearEquiv.finrank_eq, finrank_span_eq_card hb.2.1, Fintype.card_fin]

end SupBoundCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
