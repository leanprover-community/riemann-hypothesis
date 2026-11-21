import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPosLowerBoundNearMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChangeStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOneStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOneStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PowFourComplementaryModEight
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantLogBoundedNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange

section
open NumberField Complex Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Topology Real

namespace GlobalTheory

theorem cusp_pnorm_le_exp_neg_of_isIso (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (v : Fin r → E) (hP : P ∈ X.SS la)
    (hξ : X.IsIso v) :
    ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt v x τ) →
      X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  obtain ⟨M, hM, htrans⟩ := HalfMax.exists_period X la
  obtain ⟨C0, hC0⟩ := hP.1.2
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hpi := Real.pi_pos
  refine ⟨2 ^ (w / 2) * C0, π / M, by positivity, fun z0 hz0 t' ht' htt' => ?_⟩
  obtain ⟨hv, hvv, hv0⟩ := id hξ
  set e : X.Ψ → Fin r → ℂ := fun τ => Data.emb τ.1 v with he
  have he0 : ∀ τ : X.Ψ, e τ ≠ 0 := by
    intro τ h
    apply hv0
    funext a
    have := congr_fun h a
    simpa [e, Data.emb] using this
  have heIso : X.IsIsoV e := fun τ => ⟨by
    show hermC τ.1 X.Gm (fun a => τ.1 (v a)) (fun a => τ.1 (v a)) = 0
    rw [EmbeddingHermitianPairs.hermC_emb, hvv, map_zero], he0 τ⟩
  set t : ℝ := t' / 2 with ht
  have ht0 : 0 < t := by linarith
  have htt : ∀ τ, 2 * t ≤ X.ttV e z0 τ := by
    intro τ
    have h : t' ≤ X.ttV e z0 τ := htt' τ
    linarith
  have hfl : ∀ s, X.flowV e s z0 = X.flow v s z0 := fun s => rfl
  have hdom : ∀ ζ : ℂ, -(2 * t) < ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom := by
    intro ζ hζ
    rw [← hfl]
    refine ((flowDomainCriterion_holds r X e heIso z0 hz0 (fun _ => ζ)).1).2 (fun τ => ?_)
    show 0 < 1 + ζ.im / X.ttV e z0 τ
    have h := htt τ
    have hpos' : 0 < X.ttV e z0 τ := by linarith
    have : -1 < ζ.im / X.ttV e z0 τ := by rw [lt_div_iff₀ hpos']; linarith
    linarith
  set g : ℂ → ℂ := fun ζ => if -(2 * t) < ζ.im then P (X.flow v (fun _ => ζ) z0) else 0 with hg
  obtain ⟨γ, hγ, hχ, hγm⟩ := htrans v hv hvv
  have hper : Function.Periodic g M := by
    intro ζ
    simp only [hg, Complex.add_im, Complex.ofReal_im, add_zero]
    split_ifs with h
    · have hy := hdom ζ h
      have hlact : X.flow v (fun _ => ζ + (M : ℂ)) z0 = lact γ (X.flow v (fun _ => ζ) z0) := by
        funext τ
        show X.flowMat v τ (ζ + M) * mat z0 τ =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (X.flow v (fun _ => ζ) z0) τ
        rw [AdmissibleHermitianColumns.mat_flow, hγm τ, ← Matrix.mul_assoc,
          EmbeddingHermitianPairs.flowMat_mul X hvv, add_comm]
      rw [hlact, hP.1.1.2.2 γ hγ _ hy, hχ, one_mul]
    · rfl
  have hopen := FourierCoefficientDomain.isOpen_dom X
  have hdiff : ∀ ζ : ℂ, -(2 * t) < ζ.im → DifferentiableAt ℂ g ζ := by
    intro ζ hζ
    have hev : g =ᶠ[𝓝 ζ] fun ζ => P (X.flow v (fun _ => ζ) z0) := by
      have : {ζ : ℂ | -(2 * t) < ζ.im} ∈ 𝓝 ζ :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ
      filter_upwards [this] with ζ' h'
      simp only [hg, if_pos (show -(2 * t) < ζ'.im from h')]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hF : DifferentiableAt ℂ (fun ζ : ℂ => X.flow v (fun _ => ζ) z0) ζ :=
      ((FlowMeanContinuity.flow_differentiable X v z0).comp
        (differentiable_pi.2 fun _ => differentiable_id)) ζ
    exact (hP.1.1.1.differentiableAt (hopen.mem_nhds (hdom ζ hζ))).comp ζ hF
  have hzero : Tendsto g (comap im atTop) (𝓝 0) :=
    HalfMax.tendsto_zero X la P hP hz0 hξ
      (fun ζ hζ => hdom ζ (by linarith)) g
      (fun ζ hζ => by simp only [hg, if_pos (show -(2 * t) < ζ.im by linarith)])
  have hnz : 0 < X.nfac la z0 := flowTermNormDecay.nfac_pos X la hz0
  set B : ℝ := 2 ^ (w / 2) * C0 / X.nfac la z0 with hB
  have hBd : ∀ ζ : ℂ, ζ.im = -t → ‖g ζ‖ ≤ B := by
    intro ζ hζ
    have hlt : -(2 * t) < ζ.im := by linarith
    simp only [hg, if_pos hlt]
    set y := X.flow v (fun _ => ζ) z0 with hy
    have hyd := hdom ζ hlt
    have hnf : 0 < X.nfac la y := flowTermNormDecay.nfac_pos X la hyd
    have hratio : X.nfac la z0 / X.nfac la y ≤
        ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) :=
      (m3bNorm_holds r X e heIso la z0 hz0 (fun _ => ζ) (by rw [hfl]; exact hyd)).2
    have hprod : ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
        (X.spread la τ / 2) ≤ (2 : ℝ) ^ (w / 2) := by
      have hterm : ∀ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) ≤ (2 : ℝ) ^ (X.spread la τ / 2) := by
        intro τ
        have h := htt τ
        have hT : 0 < X.ttV e z0 τ := by linarith
        have hq1 : 1 / 2 ≤ 1 + ζ.im / X.ttV e z0 τ := by
          rw [hζ, neg_div]
          have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
          linarith
        have hq2 : 1 + ζ.im / X.ttV e z0 τ ≤ 1 := by
          rw [hζ, neg_div]
          have : 0 ≤ t / X.ttV e z0 τ := by positivity
          linarith
        have hqpos : 0 < 1 + ζ.im / X.ttV e z0 τ := by linarith
        have hinv : (1 + ζ.im / X.ttV e z0 τ)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hqpos two_pos]
          linarith
        have hsp := flowTermNormDecay.spread_nonneg' X la τ
        exact Real.rpow_le_rpow (le_trans hqpos.le (le_max_left _ _))
          (max_le (by linarith) hinv) (by linarith)
      calc _ ≤ ∏ τ : X.Ψ, (2 : ℝ) ^ (X.spread la τ / 2) :=
            Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans (by
              have h := htt τ
              have hT : 0 < X.ttV e z0 τ := by linarith
              have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
              rw [hζ, neg_div]
              linarith) (le_max_left _ _)) _) (fun τ _ => hterm τ)
        _ = (2 : ℝ) ^ (∑ τ : X.Ψ, X.spread la τ / 2) := (Real.rpow_sum_of_pos two_pos _ _).symm
        _ = (2 : ℝ) ^ (w / 2) := by rw [← Finset.sum_div]
    have h1 : ‖P y‖ * X.nfac la y ≤ C0 := hC0 y hyd
    have h2 : X.nfac la z0 ≤ 2 ^ (w / 2) * X.nfac la y := by
      rw [div_le_iff₀ hnf] at hratio
      exact hratio.trans (mul_le_mul_of_nonneg_right hprod hnf.le)
    rw [hB, le_div_iff₀ hnz]
    calc ‖P y‖ * X.nfac la z0 ≤ ‖P y‖ * (2 ^ (w / 2) * X.nfac la y) := by gcongr
      _ = 2 ^ (w / 2) * (‖P y‖ * X.nfac la y) := by ring
      _ ≤ 2 ^ (w / 2) * C0 := by gcongr
  have hsch := PeriodicSchwarzLemma.periodic_schwarz hM ht0 (show t < 2 * t by linarith) hper hdiff hzero hBd
  have hg0 : g 0 = P z0 := by
    simp only [hg, Complex.zero_im, if_pos (show -(2 * t) < (0 : ℝ) by linarith)]
    congr 1
    exact EmbeddingHermitianPairs.flow_zero X v z0
  rw [hg0] at hsch
  have hexp : -2 * π * t / M = -(π / M) * t' := by
    rw [ht]
    ring
  rw [hexp, hB, ← mul_div_assoc, le_div_iff₀ hnz] at hsch
  calc X.pnorm la P z0 = ‖P z0‖ * X.nfac la z0 := rfl
    _ ≤ _ := hsch
    _ = _ := mul_comm _ _

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (la : Wt X.Ψ N) (P : Frame X.Ψ N → ℂ) (ξ : Fin N → E), P ∈ X.SS la → X.IsIso ξ → ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt ξ x τ) → X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  atlas_forward_decl GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped Matrix

namespace GlobalTheory.ShFam.OrbitUnip

def LinGrowth {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ v w : Fin N → ℂ, w ≠ 0 → ∃ L : (Fin N → ℂ) →ₗ[ℂ] ℂ, L w ≠ 0 ∧ ∃ C : ℝ, ∀ k : ℕ, ‖L (A ^ k *ᵥ v)‖ ≤ C * (1 + k)

theorem LinGrowth.norm_le_one {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth A) {μ : ℂ}
    (hμ : A.charpoly.IsRoot μ) : ‖μ‖ ≤ 1 := by
  have h1 : μ ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hμ
  have h2 : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']; exact h1
  obtain ⟨v, hv⟩ := h2.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by simpa using hv.apply_eq_smul
  have hk : ∀ k : ℕ, A ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  obtain ⟨L, hL, C, hC⟩ := h v v hv.2
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖L v‖ := norm_pos_iff.2 hL
  have t0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hlt
  have t1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hlt
  have t2 := (t0.add t1).const_mul C
  simp only [add_zero, mul_zero] at t2
  have hle : ∀ k : ℕ, ‖L v‖ ≤ C * ((k : ℝ) ^ 0 / ‖μ‖ ^ k + (k : ℝ) ^ 1 / ‖μ‖ ^ k) := by
    intro k
    have := hC k
    rw [hk, map_smul, norm_smul, norm_pow] at this
    have hp : 0 < ‖μ‖ ^ k := pow_pos (by linarith) k
    rw [← add_div, ← mul_div_assoc, le_div_iff₀ hp, pow_zero, pow_one]
    linarith
  have := ge_of_tendsto' t2 hle
  linarith

theorem LinGrowth.sq_eq_zero {N : ℕ} {n : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth (1 + n)) (hn : IsNilpotent n) :
    n ^ 2 = 0 := by
  have key : ∀ v : Fin N → ℂ, n ^ 3 *ᵥ v = 0 → n ^ 2 *ᵥ v = 0 := by
    intro v hv
    by_contra hw
    obtain ⟨L, hL, C, hC⟩ := h v _ hw
    have hk : ∀ k : ℕ, (1 + n) ^ k *ᵥ v = v + (k : ℂ) • (n *ᵥ v) + ((k : ℂ) * (k - 1) / 2) • (n ^ 2 *ᵥ v) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e2 : n *ᵥ (n *ᵥ v) = n ^ 2 *ᵥ v := by rw [Matrix.mulVec_mulVec, sq]
        have e3 : n *ᵥ (n ^ 2 *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, ← pow_succ', hv]
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
          Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e2, e3]
        push_cast
        module
    set a := ‖L v‖
    set b := ‖L (n *ᵥ v)‖
    set c := ‖L (n ^ 2 *ᵥ v)‖
    have hc : 0 < c := norm_pos_iff.2 hL
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hle : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * (k - 1) / 2 * c ≤ C * (1 + k) + a + k * b := by
      intro k hk1
      have h1 := hC k
      have e : ((k : ℂ) * (k - 1) / 2) * L (n ^ 2 *ᵥ v) = L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v) := by
        rw [hk]; simp only [map_add, map_smul, smul_eq_mul]; ring
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have e' : ‖((k : ℂ) * (k - 1) / 2)‖ = (k : ℝ) * (k - 1) / 2 := by
        rw [show ((k : ℂ) * (k - 1) / 2) = (((k : ℝ) * (k - 1) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by have : (0 : ℝ) ≤ k - 1 := by linarith
                                  positivity)]
      have h2 := congrArg norm e
      rw [norm_mul, e'] at h2
      have h3 : ‖L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v)‖ ≤ ‖L ((1 + n) ^ k *ᵥ v)‖ + a + k * b := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        rw [norm_mul, Complex.norm_natCast]
      linarith
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 0)
      simpa using this
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (2 * C + a + b) / c + 1)
    have hq : 0 ≤ 2 * (2 * C + a + b) / c := by positivity
    have hk1 : (1 : ℝ) < k := by linarith
    have h4 := hle k (by exact_mod_cast hk1.le)
    have h5 : 2 * (2 * C + a + b) < (k - 1) * c := by
      rw [← div_lt_iff₀ hc]; linarith
    have h6 : (k : ℝ) * (2 * (2 * C + a + b)) < k * ((k - 1) * c) := mul_lt_mul_of_pos_left h5 (by linarith)
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hk1.le), mul_nonneg ha (sub_nonneg.2 hk1.le)]
  have step : ∀ j : ℕ, n ^ (j + 2) = 0 → n ^ 2 = 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      apply ih
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun u => ?_
      have := key (n ^ j *ᵥ u) (by rw [Matrix.mulVec_mulVec, ← pow_add, add_comm, show j + 3 = j + 1 + 2 by ring, hj]; simp)
      rw [Matrix.mulVec_mulVec, ← pow_add, add_comm] at this
      rw [Matrix.toLin'_apply, this, map_zero, LinearMap.zero_apply]
  obtain ⟨j, hj⟩ := hn
  exact step j (by rw [pow_add, hj, zero_mul])

theorem LinGrowth.pow {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth A) (m : ℕ) : LinGrowth (A ^ m) := by
  intro v w hw
  obtain ⟨L, hL, C, hC⟩ := h v w hw
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  refine ⟨L, hL, C * (1 + m), fun k => ?_⟩
  rw [← pow_mul]
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  push_cast
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {X : Data E N} {T : ℝ} {M : ℕ}
  {γ : GL (Fin N) E} {x : ℂ → Frame X.Ψ N}

theorem shift_pow (h : IsOrbit X T M γ x) (n : ℕ) (w : ℂ) (hw : T < w.im) :
    ∃ b ∈ Bor X.Ψ N, (∀ τ i, b τ i i = 1) ∧ x (w + (n * M : ℕ)) = rmul (lact (γ ^ n) (x w)) b := by
  induction n with
  | zero =>
    refine ⟨fun _ => (1 : Matrix (Fin N) (Fin N) ℂ), fun τ => ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩,
      fun _ i => Matrix.one_apply_eq i, ?_⟩
    · show (1 : Matrix (Fin N) (Fin N) ℂ).det ≠ 0
      simp
    · funext τ
      rw [zero_mul, Nat.cast_zero, add_zero]
      show mat (x w) τ = ((γ ^ 0 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * 1
      simp
  | succ n ih =>
    obtain ⟨b, hb, hb1, e⟩ := ih
    obtain ⟨b', hb', hb1', e'⟩ := h.2.2.2.2 (w + (n * M : ℕ)) (by simpa using hw)
    have tb : ∀ τ, (mat b τ).BlockTriangular id := fun τ a c hac => (hb τ).2 a c hac
    have tb' : ∀ τ, (mat b' τ).BlockTriangular id := fun τ a c hac => (hb' τ).2 a c hac
    refine ⟨rmul b b', fun τ => ⟨?_, fun a c hac => (tb τ).mul (tb' τ) hac⟩, fun τ i => ?_, ?_⟩
    · show (mat b τ * mat b' τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hb τ).1 (hb' τ).1
    · show (mat b τ * mat b' τ) i i = 1
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · show b τ i i * b' τ i i = 1
        rw [hb1, hb1', one_mul]
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [tb τ hj, zero_mul]
        · rw [tb' τ hj, mul_zero]
      · simp
    · rw [show w + (((n + 1) * M : ℕ) : ℂ) = w + (n * M : ℕ) + M by push_cast; ring, e', e]
      funext τ
      show (γ : Matrix (Fin N) (Fin N) E).map τ.1 *
          (((γ ^ n : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ) * mat b' τ =
        ((γ ^ (n + 1) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * (mat b τ * mat b' τ)
      rw [pow_succ', Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]

theorem isOrbit_pow (h : IsOrbit X T M γ x) {n : ℕ} (hn : 0 < n) : IsOrbit X T (n * M) (γ ^ n) x :=
  ⟨Nat.mul_pos hn h.1, pow_mem h.2.1 n, h.2.2.1, h.2.2.2.1, fun w hw => shift_pow h n w hw⟩

theorem linGrowth (h : IsOrbit X T M γ x) (τ : X.Ψ) : LinGrowth ((γ : Matrix (Fin N) (Fin N) E).map τ.1) := by
  intro v u hu
  set w : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hwdef
  have hwi : w.im = T + 1 := by simp [hwdef]
  have hw : T < w.im := by rw [hwi]; linarith
  have hx := h.2.2.2.1 w hw
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => X.Hf (x w) τ p u
      map_add' := fun p q => by
        have := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_left X (x w) τ (p + q) q u
        rw [add_sub_cancel_right] at this
        rw [this]; ring
      map_smul' := fun k p => ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_left X (x w) τ k p u }
  have hu0 := X.maj_pos hx τ hu
  have hv0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ v
  refine ⟨L, ?_, Real.sqrt ((2 + M ^ 2) * X.maj (x w) τ v * X.maj (x w) τ u), fun k => ?_⟩
  · show X.Hf (x w) τ u u ≠ 0
    rw [X.Hf_self hx τ u]
    exact_mod_cast hu0.ne'
  obtain ⟨b, hb, -, e⟩ := shift_pow h k w hw
  have hst := X.Γ_stab _ (pow_mem h.2.1 k)
  have hpow : ((γ ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 =
      ((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (τ.1.mapMatrix) _ k
  have h1 : X.maj (x (w + (k * M : ℕ))) τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) = X.maj (x w) τ v := by
    rw [e, MajInv.maj_rmul X (MajInv.lact_mem_dom X hst hx) hb, ← hpow]
    exact MajInv.maj_lact X hst _ τ v
  have h2 := GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x h.2.2.1 h.2.2.2.1 (w + (k * M : ℕ)) w (by simpa using hw) hw τ
    (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v)
  rw [h1, add_sub_cancel_left, Complex.norm_natCast, Complex.add_im, Complex.natCast_im, hwi] at h2
  have h3 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.cs X hx τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) u
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hM : (0 : ℝ) ≤ M := M.cast_nonneg
  have h4 : (2 + ((k * M : ℕ) : ℝ) ^ 2 / ((T + 1 + 0 - T) * (T + 1 - T))) ≤ (2 + M ^ 2) * (1 + k) ^ 2 := by
    rw [show (T + 1 + 0 - T) * (T + 1 - T) = 1 by ring]
    push_cast
    nlinarith [mul_nonneg hk (sq_nonneg (M : ℝ)), sq_nonneg (k : ℝ), sq_nonneg (M : ℝ)]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine h3.trans ?_
  calc _ ≤ (2 + M ^ 2) * (1 + k) ^ 2 * X.maj (x w) τ v * X.maj (x w) τ u :=
        mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_right h4 hv0)) hu0.le
    _ = _ := by ring

open Polynomial in

theorem exists_monic (Λ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin N → E)) = ⊤)
    (A : Matrix (Fin N) (Fin N) E) (hA : ∀ v ∈ Λ, A *ᵥ v ∈ Λ) : ∃ q : (𝓞 E)[X], q.Monic ∧ aeval A q = 0 := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  let f : Module.End (𝓞 E) Λ := ((Matrix.toLin' A).restrictScalars (𝓞 E)).restrict (fun v hv => hA v hv)
  obtain ⟨q, hq, hq0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have hpow : ∀ (n : ℕ) (v : Λ), (((f ^ n) v : Λ) : Fin N → E) = A ^ n *ᵥ (v : Fin N → E) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro v; rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]; rfl
  have hae : ∀ (p : (𝓞 E)[X]) (v : Λ), ((aeval f p v : Λ) : Fin N → E) = aeval A p *ᵥ (v : Fin N → E) := by
    intro p v
    rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow]
    exact (Matrix.smul_mulVec (algebraMap (𝓞 E) E (p.coeff i)) (A ^ i) v).symm
  refine ⟨q, hq, Matrix.toLin'.injective (LinearMap.ext_on hsp fun v hv => ?_)⟩
  have := hae q ⟨v, hv⟩
  rw [hq0] at this
  simpa using this.symm

open Polynomial in
theorem exists_pow_nilpotent (h : IsOrbit X T M γ x) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent ((γ : Matrix (Fin N) (Fin N) E) ^ m - 1) := by
  classical
  set A : Matrix (Fin N) (Fin N) E := γ.val with hA
  obtain ⟨q, hq, hq0⟩ := exists_monic X.Λ X.Λ_fg X.Λ_span A fun v hv => ((X.Γ_stab _ h.2.1).2 v).1 hv
  set p := minpoly E A with hp
  have hint : IsIntegral E A := Algebra.IsIntegral.isIntegral A
  have hpm : p.Monic := minpoly.monic hint
  have hpq : p ∣ q.map (algebraMap (𝓞 E) E) := minpoly.dvd E A (by rw [aeval_map_algebraMap, hq0])
  have hpc : p ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A
  let K := p.SplittingField
  have : NumberField K := NumberField.of_module_finite E K
  have hroot : ∀ a : K, aeval a p = 0 → ∃ n : ℕ, 0 < n ∧ a ^ n = 1 := by
    intro a ha
    have hc : aeval a A.charpoly = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hpc ha
    have hi : IsIntegral (𝓞 E) a := by
      refine ⟨q, hq, ?_⟩
      have := aeval_eq_zero_of_dvd_aeval_eq_zero hpq ha
      rwa [aeval_map_algebraMap] at this
    have hi' : IsIntegral ℤ a := isIntegral_trans a hi
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h0 : A.charpoly.coeff 0 = 0 := by
        rw [aeval_def, eval₂_at_zero] at hc
        exact (map_eq_zero _).1 hc
      have hd := Matrix.det_eq_sign_charpoly_coeff A
      rw [h0, mul_zero] at hd
      exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero hd
    have hgood : ∀ φ : K →+* ℂ, φ.comp (algebraMap E K) ∈ X.Ψ → ‖φ a‖ ≤ 1 := by
      intro φ hφ
      refine (linGrowth h ⟨_, hφ⟩).norm_le_one ?_
      rw [Matrix.charpoly_map, IsRoot, Polynomial.eval_map, ← hom_eval₂, ← aeval_def, hc, map_zero]
    obtain ⟨n, hn, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ ha0 hi' (fun φ => by
      by_cases hφ : φ.comp (algebraMap E K) ∈ X.Ψ
      · exact hgood φ hφ
      · have h2 : ComplexEmbedding.conjugate (φ.comp (algebraMap E K)) ∈ X.Ψ := by
          by_contra h3
          exact hφ ((X.cmType _).2 h3)
        have := hgood (ComplexEmbedding.conjugate φ) h2
        simpa using this)
    exact ⟨n, hn, hn1⟩
  choose! n hn hn1 using hroot
  set s := (p.map (algebraMap E K)).roots with hs
  have hmem : ∀ a ∈ s, aeval a p = 0 := fun a ha => by
    have := (mem_roots'.1 ha).2
    rwa [IsRoot, eval_map_algebraMap] at this
  refine ⟨∏ a ∈ s.toFinset, n a, Finset.prod_pos fun a ha => hn a (hmem a (Multiset.mem_toFinset.1 ha)), ?_⟩
  set m := ∏ a ∈ s.toFinset, n a
  have hm : ∀ a ∈ s, a ^ m = 1 := fun a ha => by
    obtain ⟨c, hc⟩ : n a ∣ m := Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.2 ha)
    rw [hc, pow_mul, hn1 a (hmem a ha), one_pow]
  have hsplit : p.map (algebraMap E K) = (s.map fun a => Polynomial.X - C a).prod :=
    (SplittingField.splits p).eq_prod_roots_of_monic (hpm.map _)
  have hdvd : ∀ t : Multiset K, (∀ a ∈ t, a ^ m = 1) →
      (t.map fun a => Polynomial.X - C a).prod ∣ (Polynomial.X ^ m - 1 : K[X]) ^ t.card := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro ht
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      refine mul_dvd_mul (dvd_iff_isRoot.2 ?_) (ih fun b hb => ht b (Multiset.mem_cons_of_mem hb))
      simp [ht a (Multiset.mem_cons_self a t)]
  have hd : p ∣ (Polynomial.X ^ m - 1 : E[X]) ^ s.card := by
    rw [← map_dvd_map' (algebraMap E K), hsplit]
    simpa using hdvd s hm
  refine ⟨s.card, ?_⟩
  have := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval E A)
  simpa using this

theorem exists_isOrbit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  intro E _ _ _ N X T M γ x h
  obtain ⟨m, hm, hnil⟩ := exists_pow_nilpotent h
  refine ⟨m * M, γ ^ m, isOrbit_pow h hm, ?_⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_contra hne
    push Not at hne
    exact hne φ ((X.cmType φ).2 (hne _))
  have hg := (linGrowth h ⟨τ, hτ⟩).pow m
  let F : Matrix (Fin N) (Fin N) E →+* Matrix (Fin N) (Fin N) ℂ := τ.mapMatrix
  have e : ((γ : Matrix (Fin N) (Fin N) E).map τ) ^ m = 1 + F ((γ : Matrix (Fin N) (Fin N) E) ^ m - 1) := by
    rw [map_sub, map_one, map_pow, add_sub_cancel]; rfl
  rw [e] at hg
  have h2 := hg.sq_eq_zero (hnil.map F)
  rw [← map_pow] at h2
  rw [Units.val_pow_eq_pow_val]
  ext i j
  exact (map_eq_zero τ).1 (congrFun (congrFun h2 i) j)

end GlobalTheory.ShFam.OrbitUnip
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  atlas_forward_decl GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent
end

section
section
open GlobalTheory.ShFam.BdArc Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ShFam.OrbitLimit

theorem eventually_imTop (T : ℝ) : ∀ᶠ w in imTop, T < w.im :=
  (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)

instance imTop_neBot : imTop.NeBot :=
  comap_neBot fun t ht => by
    obtain ⟨y, hy⟩ := Filter.nonempty_of_mem ht
    exact ⟨y * Complex.I, by simpa using hy⟩

theorem exists_tendsto_norm_lt {T h c : ℝ} (hh : 0 < h) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → f (w + h) = f w) (hb : ∀ w : ℂ, T < w.im → ‖f w‖ < c) :
    ∃ L, Tendsto f imTop (𝓝 L) ∧ ‖L‖ < c := by
  classical
  let g : ℂ → ℂ := fun w => if T < w.im then f w else 0
  have hg : ∀ w : ℂ, T < w.im → g w = f w := fun w hw => if_pos hw
  have hgp : Function.Periodic g h := fun w => by
    by_cases hw : T < w.im
    · rw [hg w hw, hg _ (by simpa using hw), hp w hw]
    · simp [g, hw]
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hgd : ∀ w : ℂ, T < w.im → DifferentiableAt ℂ g w := fun w hw =>
    (hd.congr fun z hz => hg z hz).differentiableAt (ho.mem_nhds hw)
  have hhol : ∀ᶠ w in imTop, DifferentiableAt ℂ g w := (eventually_imTop T).mono hgd
  have hbd : BoundedAtFilter imTop g := by
    refine Asymptotics.IsBigO.of_bound c ((eventually_imTop T).mono fun w hw => ?_)
    rw [hg w hw]
    simpa using (hb w hw).le
  set F := Function.Periodic.cuspFunction h g with hF
  set r : ℝ := Real.exp (-2 * Real.pi * (T + 1) / h) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have him : ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ r → T < (Function.Periodic.invQParam h q).im := fun q hq hqr => by
    rw [← Function.Periodic.norm_qParam_lt_iff hh, Function.Periodic.qParam_right_inv hh.ne' hq]
    refine hqr.trans_lt (Real.exp_lt_exp.2 ?_)
    rw [div_lt_div_iff_of_pos_right hh]
    nlinarith [Real.pi_pos]
  have hFd : DifferentiableOn ℂ F (closure (Metric.ball 0 r)) := fun q hq => by
    rw [closure_ball _ hr0.ne', mem_closedBall_zero_iff] at hq
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hq0 : q = 0
    · rw [hq0]
      exact Function.Periodic.differentiableAt_cuspFunction_zero hh hgp hhol hbd
    · rw [← Function.Periodic.qParam_right_inv hh.ne' hq0]
      exact Function.Periodic.differentiableAt_cuspFunction hh.ne' hgp (hgd _ (him q hq0 hq))
  refine ⟨F 0, (Function.Periodic.tendsto_at_I_inf hh hgp hhol hbd).congr' ((eventually_imTop T).mono hg), ?_⟩
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm (f := F) Metric.isBounded_ball
    (Metric.nonempty_ball.2 hr0) hFd.diffContOnCl
  rw [frontier_ball _ hr0.ne', mem_sphere_zero_iff_norm] at hz
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz; exact hr0.ne hz
  have h1 : ‖F 0‖ ≤ ‖F z‖ := hmax (subset_closure (Metric.mem_ball_self hr0))
  refine h1.trans_lt ?_
  rw [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hz0, hg _ (him z hz0 hz.le)]
  exact hb _ (him z hz0 hz.le)

def nsq {n : ℕ} (u : Fin n → ℂ) : ℝ := ∑ a, ‖u a‖ ^ 2

theorem nsq_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_lim_lt {n : ℕ} {T h c : ℝ} (hh : 0 < h) {u : ℂ → Fin n → ℂ}
    (hd : ∀ a, DifferentiableOn ℂ (fun w => u w a) {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → u (w + h) = u w) (hb : ∀ w : ℂ, T < w.im → nsq (u w) < c) {L : Fin n → ℂ}
    (hL : ∀ a, Tendsto (fun w => u w a) imTop (𝓝 (L a))) : nsq L < c := by
  obtain ⟨l, hl, hlt⟩ := exists_tendsto_norm_lt (c := (nsq L + c) / 2) hh
    (f := fun w => ∑ a, (starRingEnd ℂ) (L a) * u w a)
    (DifferentiableOn.fun_sum fun a _ => (hd a).const_mul _) (fun w hw => by simp only [hp w hw]) fun w hw => by
      refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (b := (nsq L + nsq (u w)) / 2) ?_ (by linarith [hb w hw]))
      rw [nsq, nsq, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖L a‖ - ‖u w a‖)]
  have h2 := tendsto_nhds_unique hl (tendsto_finsetSum _ fun a _ => (hL a).const_mul ((starRingEnd ℂ) (L a)))
  have h3 : l = (nsq L : ℝ) := by
    rw [h2, nsq]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Complex.conj_mul' _
  rw [h3, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg L)] at hlt
  linarith

def Jm (N p : ℕ) : Matrix (Fin N) (Fin N) ℂ := diagonal fun a : Fin N => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sum_castLE {N p : ℕ} (hp : p ≤ N) {R : Type} [AddCommMonoid R] (f : Fin N → R) :
    ∑ j, f (Fin.castLE hp j) = ∑ a : Fin N, if (a : ℕ) < p then f a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hp j) (fun j _ => by simp) (fun a _ b _ h => Fin.castLE_injective hp h)
    (fun a ha => ⟨⟨a, by simpa using ha⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl

theorem form_eq {N p : ℕ} (hp : p ≤ N) (u : Fin N → ℂ) :
    star u ⬝ᵥ Jm N p *ᵥ u = ((2 * nsq (fun j => u (Fin.castLE hp j)) - nsq u : ℝ) : ℂ) := by
  rw [nsq, nsq, sum_castLE hp (fun a => ‖u a‖ ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib, Complex.ofReal_sum,
    dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Jm, mulVec_diagonal, mul_left_comm, Pi.star_apply, Complex.star_def, Complex.conj_mul', sgn]
  split_ifs <;> push_cast <;> ring

theorem posDef_iff {N p : ℕ} (hp : p ≤ N) (U : Matrix (Fin N) (Fin p) ℂ) :
    (Uᴴ * Jm N p * U).PosDef ↔
      ∀ v, v ≠ 0 → nsq (U *ᵥ v) < 2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) := by
  have hH : (Uᴴ * Jm N p * U).IsHermitian := by
    refine isHermitian_conjTranspose_mul_mul _ ?_
    rw [Jm, IsHermitian, diagonal_conjTranspose]
    congr 1
    funext a
    simp
  have key : ∀ v, star v ⬝ᵥ (Uᴴ * Jm N p * U) *ᵥ v =
      ((2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) - nsq (U *ᵥ v) : ℝ) : ℂ) := fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, form_eq hp]
    rfl
  rw [posDef_iff_dotProduct_mulVec, and_iff_right hH]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [key, Complex.zero_lt_real, sub_pos]

theorem det_top_ne {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    (U.submatrix (Fin.castLE hp) id).det ≠ 0 := fun h0 => by
  obtain ⟨v, hv, h1⟩ := exists_mulVec_eq_zero_iff.2 h0
  have h2 := (posDef_iff hp U).1 hU v hv
  rw [h1] at h2
  have h3 := nsq_nonneg (U *ᵥ v)
  simp [nsq] at h2 h3
  linarith

def IsGraph {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) : Prop :=
  Y.submatrix (Fin.castLE hp) id = 1 ∧ (Yᴴ * Jm N p * Y).PosDef

theorem IsGraph.nsq_lt {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) {v : Fin p → ℂ}
    (hv : v ≠ 0) : nsq (Y *ᵥ v) < 2 * nsq v := by
  have := (posDef_iff hp Y).1 h.2 v hv
  rwa [h.1, one_mulVec] at this

theorem isGraph_mul_inv {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    IsGraph hp (U * (U.submatrix (Fin.castLE hp) id)⁻¹) := by
  have hd := (det_top_ne hp hU).isUnit
  refine ⟨?_, ?_⟩
  · rw [← mul_nonsing_inv _ hd]
    rfl
  · have := hU.conjTranspose_mul_mul_same (B := (U.submatrix (Fin.castLE hp) id)⁻¹)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hd)))
    simpa only [conjTranspose_mul, Matrix.mul_assoc] using this

theorem graph_limit {N p : ℕ} (hp : p ≤ N) {T h : ℝ} (hh : 0 < h) {Y : ℂ → Matrix (Fin N) (Fin p) ℂ}
    (hd : ∀ a j, DifferentiableOn ℂ (fun w => Y w a j) {w | T < w.im})
    (hper : ∀ w : ℂ, T < w.im → Y (w + h) = Y w) (hG : ∀ w : ℂ, T < w.im → IsGraph hp (Y w)) :
    ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y w a j) imTop (𝓝 (Y₀ a j)) := by
  have hex : ∀ a j, ∃ L, Tendsto (fun w => Y w a j) imTop (𝓝 L) := fun a j => by
    obtain ⟨L, hL, -⟩ := exists_tendsto_norm_lt (c := 2) hh (hd a j) (fun w hw => by simp only [hper w hw])
      fun w hw => by
        have h1 := (hG w hw).nsq_lt (v := Pi.single j 1) (by simp)
        have h2 : nsq (Pi.single j (1 : ℂ) : Fin p → ℂ) = 1 := by
          rw [nsq, Finset.sum_eq_single j] <;> simp +contextual
        have h3 : ‖Y w a j‖ ^ 2 ≤ nsq (Y w *ᵥ Pi.single j 1) := by
          have := Finset.single_le_sum (f := fun a => ‖(Y w *ᵥ Pi.single j 1) a‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
          simpa [nsq] using this
        nlinarith [norm_nonneg (Y w a j)]
    exact ⟨L, hL⟩
  choose Y₀ hY using hex
  have h1 : (Matrix.of Y₀).submatrix (Fin.castLE hp) id = 1 := by
    ext i j
    refine tendsto_nhds_unique (hY (Fin.castLE hp i) j) (tendsto_const_nhds.congr' ((eventually_imTop T).mono ?_))
    intro w hw
    exact (congrFun (congrFun (hG w hw).1 i) j).symm
  refine ⟨Matrix.of Y₀, ⟨h1, (posDef_iff hp _).2 fun v hv => ?_⟩, hY⟩
  rw [h1, one_mulVec]
  refine nsq_lim_lt (T := T) hh (u := fun w => Y w *ᵥ v) (fun a => ?_) (fun w hw => by simp only [hper w hw])
    (fun w hw => (hG w hw).nsq_lt hv) fun a => ?_
  · exact DifferentiableOn.fun_sum (u := Finset.univ) fun j _ => (hd a j).mul_const (v j)
  · exact tendsto_finsetSum Finset.univ fun j _ => (hY a j).mul_const (v j)

def extend {N p : ℕ} (Y : Matrix (Fin N) (Fin p) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : (b : ℕ) < p then Y a ⟨b, h⟩ else (1 : Matrix (Fin N) (Fin N) ℂ) a b

theorem extend_submatrix {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) :
    (extend Y).submatrix id (Fin.castLE hp) = Y := by
  ext a j
  simp [extend]

theorem det_extend {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) : (extend Y).det = 1 := by
  have key : ∀ a b : Fin N, a ≤ b → extend Y a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b := fun a b hab => by
    rw [extend, of_apply]
    split_ifs with hb
    · have ha : (a : ℕ) < p := lt_of_le_of_lt hab hb
      have := congrFun (congrFun h.1 ⟨a, ha⟩) ⟨b, hb⟩
      simpa [one_apply, Fin.ext_iff] using this
    · rfl
  rw [det_of_isLowerTriangular _ fun a b hab => by
    have hab' : a < b := hab
    rw [key a b hab'.le, one_apply_ne hab'.ne]]
  simp [key]

theorem span_col {N p : ℕ} (hp : p ≤ N) (m : Matrix (Fin N) (Fin N) ℂ) :
    Submodule.span ℂ (ReciprocityTheory.ChartRestriction.G.FD.col m '' {a | (a : ℕ) < p}) =
      LinearMap.range (m.submatrix id (Fin.castLE hp)).mulVecLin := by
  rw [range_mulVecLin]
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hp j, j.2, rfl⟩

theorem submatrix_mul_upper {N p : ℕ} (hp : p ≤ N) (y b : Matrix (Fin N) (Fin N) ℂ)
    (hb : ∀ a c, c < a → b a c = 0) :
    (y * b).submatrix id (Fin.castLE hp) =
      y.submatrix id (Fin.castLE hp) * b.submatrix (Fin.castLE hp) (Fin.castLE hp) := by
  ext a j
  simp only [submatrix_apply, mul_apply, id]
  rw [sum_castLE hp fun k => y a k * b k (Fin.castLE hp j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · rfl
  · rw [hb k _ (by have := j.2; simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]

theorem gramPos_iff {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {N : ℕ} (X : Data E N)
    {x : Frame X.Ψ N} {τ : X.Ψ} {P y : Matrix (Fin N) (Fin N) ℂ} (hP : gram τ.1 X.Gm P = Jm N X.p0)
    (hx : mat x τ = P * y) :
    (X.gramPos x τ).PosDef ↔ ((y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le)).PosDef := by
  have h1 : (X.gramPos x τ)ᵀ = (y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le) := by
    have h2 : (gram τ.1 X.Gm (mat x τ))ᵀ = yᴴ * Jm N X.p0 * y := by
      rw [hx, FrameDegreeData.gram_mul, hP, transpose_mul, transpose_mul, transpose_transpose, Jm, diagonal_transpose,
        Matrix.mul_assoc]
      rfl
    rw [Data.gramPos, transpose_submatrix, h2]
    rfl
  rw [← h1]
  exact ⟨fun h => h.transpose, fun h => by simpa using h.transpose⟩

theorem orbit_limit : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ)
    (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N,
      Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  intro E _ _ _ N X T M x ⟨hM, _, hd, hdom, hper⟩
  choose P hP0 hP using X.signature
  have hp := X.p0_le
  let U : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => ((P τ)⁻¹ * mat (x w) τ).submatrix id (Fin.castLE hp)
  let Y : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹
  have hx : ∀ τ w, mat (x w) τ = P τ * ((P τ)⁻¹ * mat (x w) τ) := fun τ w =>
    (mul_nonsing_inv_cancel_left _ _ (hP0 τ).isUnit).symm
  have hU : ∀ τ (w : ℂ), T < w.im → ((U τ w)ᴴ * Jm N X.p0 * U τ w).PosDef := fun τ w hw =>
    (gramPos_iff X (hP τ) (hx τ w)).1 (X.gramPos_posDef (hdom w hw) τ)
  have hUd : ∀ τ a j, DifferentiableOn ℂ (fun w => U τ w a j) {w | T < w.im} := fun τ a j =>
    DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
      (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hd τ) k) (Fin.castLE hp j)).const_mul
        ((P τ)⁻¹ a k)
  have hG : ∀ τ (w : ℂ), T < w.im → IsGraph hp (Y τ w) := fun τ w hw => isGraph_mul_inv hp (hU τ w hw)
  have hlim : ∀ τ, ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y τ w a j) imTop (𝓝 (Y₀ a j)) := fun τ => by
    refine graph_limit hp (T := T) (h := M) (by exact_mod_cast hM) (fun a j => ?_) (fun w hw => ?_) (hG τ)
    · exact DifferentiableOn.fun_sum (u := Finset.univ) fun k _ => (hUd τ a k).fun_mul
        (GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv (fun w => (U τ w).submatrix (Fin.castLE hp) id) _
          (fun i l => hUd τ _ l) (fun w hw => det_top_ne hp (hU τ w hw)) k j)
    · obtain ⟨b, hb, -, hxb⟩ := hper w hw
      have h1 : mat (x (w + M)) τ = mat (x w) τ * mat b τ := by
        rw [hxb]
        show ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ = _
        simp
      set c := (mat b τ).submatrix (Fin.castLE hp) (Fin.castLE hp) with hc
      have h2 : U τ (w + M) = U τ w * c := by
        simp only [U]
        rw [h1, ← Matrix.mul_assoc, submatrix_mul_upper hp _ (mat b τ) (hb τ).2]
      have h3 : (U τ w * c).submatrix (Fin.castLE hp) id = (U τ w).submatrix (Fin.castLE hp) id * c := rfl
      have h4 := det_top_ne hp (hU τ (w + M) (by simpa using hw))
      rw [h2, h3, det_mul] at h4
      simp only [Y, Complex.ofReal_natCast]
      rw [h2, h3, Matrix.mul_inv_rev, Matrix.mul_assoc,
        mul_nonsing_inv_cancel_left _ _ (right_ne_zero_of_mul h4).isUnit]
  choose Y₀ hY₀ hlim using hlim
  let fr : (X.Ψ → Matrix (Fin N) (Fin X.p0) ℂ) → Frame X.Ψ N := fun Z τ =>
    (P τ * extend (Z τ) : Matrix (Fin N) (Fin N) ℂ)
  have hfr : ∀ Z τ, mat (fr Z) τ = P τ * extend (Z τ) := fun _ _ => rfl
  have hmem : ∀ Z, (∀ τ, IsGraph hp (Z τ)) → fr Z ∈ X.dom := fun Z hZ =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨by
      rw [hfr, det_mul, det_extend (hZ τ), mul_one]
      exact hP0 τ, (gramPos_iff X (hP τ) (hfr Z τ)).2 (by rw [extend_submatrix]; exact (hZ τ).2)⟩
  refine ⟨fr Y₀, hmem _ hY₀, fun w => fr fun τ => Y τ w, ?_, (eventually_imTop T).mono fun w hw =>
    ⟨hmem _ fun τ => hG τ w hw, fun τ => ?_⟩⟩
  · refine tendsto_pi_nhds.2 fun τ => tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
    refine tendsto_finsetSum Finset.univ (f := fun k w => P τ a k * extend (Y τ w) k b)
      (a := fun k => P τ a k * extend (Y₀ τ) k b) fun k _ => Tendsto.const_mul _ ?_
    simp only [extend, of_apply]
    split_ifs with hb
    · exact hlim τ k _
    · exact tendsto_const_nhds
  · have h1 : (mat (x w) τ).submatrix id (Fin.castLE hp) = P τ * U τ w := by
      conv_lhs => rw [hx τ w]
      rfl
    have h2 : (P τ * extend (Y τ w)).submatrix id (Fin.castLE hp) =
        P τ * U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹ := by
      rw [Matrix.mul_assoc, ← extend_submatrix hp (U τ w * _)]
      rfl
    rw [span_col hp, span_col hp, hfr, h1, h2, mulVecLin_mul (P τ * U τ w), LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (det_top_ne hp (hU τ w hw)).isUnit)))

end GlobalTheory.ShFam.OrbitLimit
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N, Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  atlas_forward_decl GlobalTheory.ShFam.OrbitLimit.orbit_limit
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  first | exact @GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | exact GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | (intros; apply GlobalTheory.ShFam.BdArc.Leave.lift_not_converges <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.OrbitShort

theorem quad_bound {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℂ → V → ℝ) (T : ℝ) (M : ℕ) (hM : 0 < M) (b ξ : V)
    (h0 : ∀ w : ℂ, T < w.im → ∀ v, 0 ≤ m w v)
    (hsm : ∀ (w : ℂ) (k : ℕ) (v : V), m w ((k : ℂ) • v) = (k : ℝ) ^ 2 * m w v)
    (hpar : ∀ (w : ℂ) (u v : V), m w (u + v) + m w (u - v) = 2 * m w u + 2 * m w v)
    (hH : ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ v,
      m w' v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * m w v)
    (hξ : ∀ w : ℂ, T < w.im → m (w + M) ξ = m w ξ)
    (hb : ∀ w : ℂ, T < w.im → ∀ k : ℕ, m (w + M) (b + ((k + 1 : ℕ) : ℂ) • ξ) = m w (b + (k : ℂ) • ξ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im → m w ξ * (w.im - T) ≤ A := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hξk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) ξ = m w ξ := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hξ _ (by simpa using hw), ih]
  have hbk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) (b + (k : ℂ) • ξ) = m w b := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hb _ (by simpa using hw), ih]
  set w0 : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hw0
  have hw0im : w0.im = T + 1 := by simp [hw0]
  have hw0re : w0.re = 0 := by simp [hw0]
  have hm0 : 0 ≤ m w0 b := h0 _ (by rw [hw0im]; linarith) _
  refine ⟨(M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)), by positivity, ?_⟩
  have strip : ∀ w : ℂ, T + 1 < w.im → 0 ≤ w.re → w.re < M → m w ξ * (w.im - T) ≤
      (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)) := by
    intro w hw hr0 hr1
    have hw' : T < w.im := by linarith
    obtain ⟨y, hy⟩ : ∃ y, y = w.im - T := ⟨_, rfl⟩
    have hy1 : 1 < y := by linarith
    have hy0 : 0 < y := by linarith
    rw [← hy]

    have g1 : m w b ≤ (3 + (M : ℝ) ^ 2) * y * m w0 b := by
      refine (hH w0 w (by rw [hw0im]; linarith) hw' b).trans (mul_le_mul_of_nonneg_right ?_ hm0)
      have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (y - 1) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hw0im, hw0re, hy]; ring
      rw [e1, hw0im, ← hy, show (T + 1 - T) * y = y by ring]
      have : (w.re ^ 2 + (y - 1) ^ 2) / y ≤ (1 + (M : ℝ) ^ 2) * y := by
        rw [div_le_iff₀ hy0]
        have a1 : w.re ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
        have a2 : (M : ℝ) ^ 2 * 1 ≤ (M : ℝ) ^ 2 * (y * y) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith
      nlinarith
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, y ≤ k * M ∧ (k : ℝ) * M ≤ y + M := by
      refine ⟨⌈y / M⌉₊, ?_, ?_⟩
      · rw [← div_le_iff₀ hMr]; exact Nat.le_ceil _
      · have := (Nat.ceil_lt_add_one (a := y / M) (by positivity)).le
        have h2 := mul_le_mul_of_nonneg_right this hMr.le
        rwa [add_mul, div_mul_cancel₀ _ hMr.ne', one_mul] at h2
    have hwk : T < (w + k * M).im := by simpa using hw'
    have hmb : 0 ≤ m w b := h0 _ hw' _
    have g2 : m (w + k * M) b ≤ (2 + (1 + (M : ℝ)) ^ 2) * m w b := by
      refine (hH w (w + k * M) hw' hwk b).trans (mul_le_mul_of_nonneg_right ?_ hmb)
      have e1 : ‖w - (w + k * M)‖ ^ 2 = ((k : ℝ) * M) ^ 2 := by
        rw [show w - (w + k * M) = -(k * M) by ring, norm_neg, norm_mul]; simp
      have e2 : (w + k * M).im = w.im := by simp
      rw [e1, e2, ← hy]
      have : ((k : ℝ) * M) ^ 2 / (y * y) ≤ (1 + (M : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have a1 : (k : ℝ) * M ≤ (1 + M) * y := by nlinarith
        have a2 := pow_le_pow_left₀ (by positivity) a1 2
        nlinarith
      linarith
    have g3 : (k : ℝ) ^ 2 * m w ξ ≤ (6 + 2 * (1 + (M : ℝ)) ^ 2) * m w b := by
      have p := hpar (w + k * M) (b + (k : ℂ) • ξ) b
      rw [show b + (k : ℂ) • ξ - b = (k : ℂ) • ξ by abel, hsm, hξk k w hw', hbk k w hw'] at p
      have := h0 _ hwk (b + (k : ℂ) • ξ + b)
      linarith
    have hmξ : 0 ≤ m w ξ := h0 _ hw' _
    have g4 : y ^ 2 * m w ξ ≤ ((k : ℝ) * M) ^ 2 * m w ξ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0.le hk1 2) hmξ
    have g5 : (M : ℝ) ^ 2 * ((k : ℝ) ^ 2 * m w ξ) ≤
        (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * y * m w0 b)) :=
      mul_le_mul_of_nonneg_left (g3.trans (mul_le_mul_of_nonneg_left g1 (by positivity))) (by positivity)
    refine le_of_mul_le_mul_left ?_ hy0
    nlinarith
  intro w hw
  have hper : Function.Periodic (fun s : ℝ => m ((s : ℂ) + (w.im : ℂ) * Complex.I) ξ) (M : ℝ) := by
    intro s
    have e : ((s + (M : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = ((s : ℂ) + (w.im : ℂ) * Complex.I) + M := by
      push_cast; ring
    show m _ ξ = m _ ξ
    rw [e, hξ _ (by simp; linarith)]
  obtain ⟨s, hs, hse⟩ := hper.exists_mem_Ico₀ hMr w.re
  simp only [Complex.re_add_im] at hse
  have := strip ((s : ℂ) + (w.im : ℂ) * Complex.I) (by simpa using hw) (by simpa using hs.1) (by simpa using hs.2)
  rw [hse]
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_natCast_smul (x : Frame X.Ψ N) (τ : X.Ψ) (k : ℕ) (v : Fin N → ℂ) :
    X.maj x τ ((k : ℂ) • v) = (k : ℝ) ^ 2 * X.maj x τ v := by
  unfold Data.maj Data.posPart
  have e : ∀ a b c : ℂ, (k : ℂ) * a * b * ((k : ℂ) * c) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * (a * b * c) := by
    intro a b c; push_cast; ring
  have e' : ∀ a : ℂ, (k : ℂ) * ((k : ℂ) * a) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * a := by
    intro a; push_cast; ring
  simp only [hermC_smul_left, hermC_smul_right, map_mul, map_natCast, e, e', ← Finset.mul_sum,
    Complex.re_ofReal_mul]
  ring

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_parallelogram (x : Frame X.Ψ N) (τ : X.Ψ) (u v : Fin N → ℂ) :
    X.maj x τ (u + v) + X.maj x τ (u - v) = 2 * X.maj x τ u + 2 * X.maj x τ v := by
  have hs : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  have hp : X.posPart x τ (u + v) + X.posPart x τ (u - v) = 2 * X.posPart x τ u + 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [two_mul, two_mul]
    simp only [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hs, hermC_add_left, hermC_smul_left, map_add, map_mul, map_neg, map_one]
    ring
  have hh : hermC τ.1 X.Gm (u + v) (u + v) + hermC τ.1 X.Gm (u - v) (u - v) =
      hermC τ.1 X.Gm u u + hermC τ.1 X.Gm u u + (hermC τ.1 X.Gm v v + hermC τ.1 X.Gm v v) := by
    simp only [hs, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, map_neg, map_one]
    ring
  have hh' := congrArg Complex.re hh
  simp only [Complex.add_re] at hh'
  unfold Data.maj
  linarith

end GlobalTheory.OrbitShort

open GlobalTheory.OrbitShort in

theorem GlobalTheory.orbit_unipotent_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  intro E _ _ _ N X T M γ x ⟨hM, hγ, hd, hdom, hsh⟩ hsq hne
  have hst := X.Γ_stab γ hγ
  obtain ⟨b, hbΛ, hb⟩ : ∃ b ∈ X.Λ, Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hne
    have hz : Matrix.toLin' ((γ : Matrix (Fin N) (Fin N) E) - 1) = 0 := by
      refine LinearMap.ext_on X.Λ_span fun v hv => ?_
      rw [Matrix.toLin'_apply, hc v hv]; rfl
    have hz' : (γ : Matrix (Fin N) (Fin N) E) - 1 = 0 := Matrix.toLin'.map_eq_zero_iff.1 hz
    exact Units.ext (sub_eq_zero.1 hz')
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b := ⟨_, rfl⟩
  rw [← hξ] at hb
  have hγb : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) b = b + ξ := by
    rw [hξ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hγξ : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) ξ = ξ := by
    have : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) ξ = 0 := by
      rw [hξ, Matrix.mulVec_mulVec, ← sq, hsq, Matrix.zero_mulVec]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  have hξΛ : ξ ∈ X.Λ := by
    have h1 := (hst.2 b).1 hbΛ
    rw [hγb] at h1
    simpa using X.Λ.sub_mem h1 hbΛ
  have hiso : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0 := by
    have h1 := hst.1 ξ b
    rw [hγb, hγξ] at h1
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ (b + ξ) =
        ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ b + ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ := by
      simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, mul_add, Finset.sum_add_distrib]
    rw [h2] at h1
    simpa using h1
  have hemb : ∀ (τ : X.Ψ) (v : Fin N → E),
      Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 v) =
        Data.emb τ.1 (Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) v) := by
    intro τ v
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hshift : ∀ w : ℂ, T < w.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ),
      X.maj (x (w + M)) τ (Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) v) = X.maj (x w) τ v := by
    intro w hw τ v
    obtain ⟨β, hβ, -, he⟩ := hsh w hw
    rw [he, GlobalTheory.MajInv.maj_rmul X (GlobalTheory.MajInv.lact_mem_dom X hst (hdom w hw)) hβ, GlobalTheory.MajInv.maj_lact X hst]
  have hA : ∀ τ : X.Ψ, ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im →
      X.maj (x w) τ (Data.emb τ.1 ξ) * (w.im - T) ≤ A := by
    intro τ
    have eξ : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ := by
      rw [hemb, hγξ]
    have eb : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 b) =
        Data.emb τ.1 b + Data.emb τ.1 ξ := by
      rw [hemb, hγb]; funext i; simp [Data.emb]
    refine quad_bound (fun w v => X.maj (x w) τ v) T M hM (Data.emb τ.1 b) (Data.emb τ.1 ξ) ?_
      (fun w k v => maj_natCast_smul X _ τ k v) (fun w u v => maj_parallelogram X _ τ u v)
      (fun w w' hw hw' v => GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x hd hdom w w' hw hw' τ v) ?_ ?_
    · intro w hw v
      by_cases hv : v = 0
      · have := maj_natCast_smul X (x w) τ 0 v
        subst hv
        rw [smul_zero, Nat.cast_zero, sq, zero_mul, zero_mul] at this
        exact this.ge
      · exact (X.maj_pos (hdom w hw) τ hv).le
    · intro w hw
      have := hshift w hw τ (Data.emb τ.1 ξ)
      rwa [eξ] at this
    · intro w hw k
      have := hshift w hw τ (Data.emb τ.1 b + (k : ℂ) • Data.emb τ.1 ξ)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, eξ, eb] at this
      rw [← this]
      congr 1
      push_cast
      rw [add_smul, one_smul]; abel
  choose A hA0 hA using hA
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
    unfold Data.c
    positivity
  have hK0 : 0 ≤ ∑ τ, X.c τ * A τ := Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hA0 τ)
  refine ⟨ξ, 1 / (1 + ∑ τ, X.c τ * A τ), ⟨hξΛ, hiso, hb⟩, by positivity, fun w hw τ => ?_⟩
  have hv : Data.emb τ.1 ξ ≠ 0 := fun h => hb (funext fun a =>
    (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a))
  have hp := X.maj_pos (hdom w (by linarith)) τ hv
  have hle : X.c τ * A τ ≤ ∑ τ, X.c τ * A τ :=
    Finset.single_le_sum (f := fun τ => X.c τ * A τ) (fun τ _ => mul_nonneg (hc τ).le (hA0 τ)) (Finset.mem_univ τ)
  have h1 := mul_le_mul_of_nonneg_left (hA τ w hw) (hc τ).le
  unfold Data.tt
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (mul_pos (hc τ) hp)]
  nlinarith
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  atlas_forward_decl GlobalTheory.orbit_unipotent_short
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcLift_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  first | exact @GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | exact GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | (intros; apply GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_frame_limits_of_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → (∀ τ (j : Fin N), (X.p0 ≤ j → 0 ≤ la τ j) ∧ ((j : ℕ) < X.p0 → la τ j ≤ 0)) → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.nfac_inv_le_pow_of_isOrbit | exact GlobalTheory.nfac_inv_le_pow_of_isOrbit | (intros; apply GlobalTheory.nfac_inv_le_pow_of_isOrbit <;> assumption)
end

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree
open Formalism.L2.Pj hiding toC relab Unf IsUnf GoodEmb rdU laU perFr
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

section Key

open GlobalTheory.KeyFourth GlobalTheory.ShFam

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {r : ℕ} {M : ModelsOf F r} {k : Fin F.n}

instance isLocalRing_cAt : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)

end Key

end GlobalTheory.KeyHol
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus : ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  atlas_forward_decl GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_equation_holomorphic_limit : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : GlobalTheory.ProjVar.Var F) (Δ bd : Y.Dv) (g : Y.Fn), Y.Eff bd → (∀ y : Y.X, y ∉ Y.supp bd → Δ.RegularAt y g) → (∀ y ∈ Y.supp bd, ∀ V : Y.X.Opens, y ∈ V → ∃ (U : Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (t : Y.Fnˣ), U ≤ V ∧ (∀ y' ∈ U, Δ.IsEqn y' t) ∧ ∀ (a b : Γ(Y.X, U)) (ψ : ℂ → (Γ(Y.X, U) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec) ≫ Y.str = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∈ Y.supp bd) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ (show Sp Γ(Y.X, U) ⟶ Y.X from hU.fromSpec)) s ∉ Y.supp bd) → fnOf U (gen_mem hy) a = g * t * fnOf U (gen_mem hy) b → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u b ≠ 0) → Tendsto (fun u => ψ u a / ψ u b) (𝓝[≠] 0) (𝓝 0)) → g ∈ Y.H0 Δ ∧ Y.vanishOn Δ g (Y.supp bd) := by
  first | exact @GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto | exact GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto | (intros; apply GlobalTheory.ShFam.BdArc.mem_H0_and_vanishOn_of_tendsto <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_point_eigenframe : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_matches | exact GlobalTheory.ShFam.BdArc.exists_matches | (intros; apply GlobalTheory.ShFam.BdArc.exists_matches <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.ChartValue

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem exists_evR_eq_of_tri {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, ∀ (K : Type) [CommRing K] [IsLocalRing K] [Algebra c.F K] (ψ : R →ₐ[c.F] K)
      (v0 : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Z.t.G.left))
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (y0 : FrPt Xo c K),
      (∀ τ i, ∃ cf : Fin (Dw.mult τ) → K, cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t (spMap ψ.toRingHom ≫ x) (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) cf (v0 τ i)) →
      GlobalTheory.AllWt.ptF y0 = spMap ψ.toRingHom ≫ xF →
      (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
        w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
          w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = v0 τ i) →
      evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ψ a := by
  obtain ⟨y, w, hyx, hw⟩ := exists_frPt_of_eigFrame xF hs hx f
  refine ⟨evR Xo c g y, fun K _ _ _ ψ v0 t y0 hT hy hu => ?_⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap ψ y
  have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = y0.x := pullback.lift_fst _ _ _
  have h1 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = z.x := by rw [hz.1, hyx, hy, Category.assoc]
  have h2 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ ≫ pullback.fst _ _ = spMap ψ.toRingHom ≫ x := by rw [hy, ← hx, Category.assoc]
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c K z y0).1 (h0.symm.trans h1)
  choose cf hcf1 hcf2 hcf3 using hT
  have hcomb : ∀ τ i, IsCombAt z.x (z.u τ) (cf τ i) (y0.u τ i) := fun τ i => by
    obtain ⟨w0, a1, a2, a3⟩ := hu τ i
    have hv : ∀ k, (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.oF.t.G.hom =
        spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 := fun k => by
      rw [Category.assoc, (hw τ k).1, hy, ← Category.assoc, ← Category.assoc, OpenReg.spMap_comp, OpenReg.spMap_comp,
        GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]
    have e1 : z.u τ = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m0.toSABMap.φ := funext fun k => by
      rw [hz.2.1, Category.assoc, (hw τ k).2.1]
    have e2 : (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) =
        fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m.φ := funext fun k => by
      rw [Category.assoc, (hw τ k).2.2]
    have b := hcf3 τ i
    rw [e2, ← a3] at b
    rw [e1, ← a2]
    exact (comb_iff Z.m0.toSABMap h1 hv _ a1).2 ((comb_iff Z.m h2 hv _ a1).1 b)
  let T : Ix Dw → Kˣ := fun k => k.elim a fun k => t k.1 k.2
  have hb : FrBor T z y0 := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).2.2.2 T z y0).2
    ⟨fun τ => Matrix.of (cf τ), fun τ i => hcf1 τ i, fun τ i j hij => hcf2 τ i j hij, hc.1, hcomb, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, GlobalTheory.FlagTan.evR_frMap hg.1 hz, Fintype.prod_option, hex, zpow_zero,
    _root_.one_mul]
  rfl

theorem exists_value_local {A R K L : Type} [CommRing A] [CommRing R] [IsLocalRing R] [Field K] [CommRing L] [IsLocalRing L]
    [Algebra c.F K] [Algebra c.F L] (j : A →+* R) (ι : R →+* K) (hι : Function.Injective ι) (ψ : R →+* L) [IsLocalHom ψ]
    (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) {x' : Sp K ⟶ Z.X}
    (f0 : EigFrame Z (algebraMap c.F K) x') (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (hT : fr.Tri (ι.comp j) f0 t)
    (y0 : FrPt Xo c K) (hy0 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ = spMap (ι.comp j) ≫ x)
    (hu0 : ∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
        w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i)
    (hσ : (ψ.comp j).comp φ = algebraMap c.F L) (y : FrPt Xo c L)
    (hy : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (ψ.comp j) ≫ x)
    (hu : ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ GlobalTheory.AllWt.ptF y ∧
        w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (ψ.comp j)) ≫ fr.v τ i)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, evR Xo c g y0 = ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ι a ∧
      evR Xo c g y = ψ a := by
  letI : Algebra c.F R := (j.comp φ).toAlgebra
  haveI := Z.jQ_open
  obtain ⟨f, hf⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A R φ _ fr j
  let ι' : R →ₐ[c.F] K := { ι with commutes' := fun r => (RingHom.congr_fun hT.2.1 r).symm }
  let ψ' : R →ₐ[c.F] L := { ψ with commutes' := fun r => RingHom.congr_fun hσ r }
  have hr : Set.range (spMap j ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have h1 : p ⤳ spMap ψ (IsLocalRing.closedPoint L) := by
      have : spMap ψ (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint ψ
      rw [this]
      exact IsLocalRing.specializes_closedPoint p
    refine (h1.map (spMap j ≫ x).continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
      ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint L), ?_⟩
    have h2 : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap ψ ≫ spMap j ≫ x := by rw [hy, ← Category.assoc, OpenReg.spMap_comp]
    exact congrArg (fun m : Sp L ⟶ gen Z => m (IsLocalRing.closedPoint L)) h2
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap j ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF y0 = spMap ι ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy0]
  have hpt : GlobalTheory.AllWt.ptF y = spMap ψ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, OpenReg.spMap_comp, hy]
  have hs : xF ≫ pullback.snd _ _ = spMap (j.comp φ) := by
    obtain ⟨φ₁, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ι ≫ spMap φ₁.hom = spMap (algebraMap c.F K) := by
      have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [OpenReg.spMap_comp] at h1
    have h2 : ι.comp φ₁.hom = algebraMap c.F K := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₁.hom = j.comp φ := RingHom.ext fun r =>
      hι ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
    rw [← h, ← h3]
    rfl
  obtain ⟨a, ha⟩ := exists_evR_eq_of_tri xF hs (by rw [← Category.assoc, hxF, Category.assoc]) f hex hg
  have e0 : ∀ {M : Type} [CommRing M] (χ : R →+* M) (τ : E →+* ℂ),
      (fun k => spMap (dualMap χ) ≫ f.v τ k) = fun k => spMap (dualMap (χ.comp j)) ≫ fr.v τ k := fun χ τ =>
    funext fun k => by rw [hf, ← Category.assoc, OpenReg.spMap_comp, dualMap_comp']
  refine ⟨a, ha K ι' f0.v t y0 (fun τ i => ?_) hpt0 hu0, ?_⟩
  · obtain ⟨cf, h1, h2, h3⟩ := hT.2.2 τ i
    refine ⟨cf, h1, h2, ?_⟩
    have e1 : x' = spMap ι ≫ spMap j ≫ x ≫ genι Z := by rw [hT.1, ← Category.assoc (spMap ι), OpenReg.spMap_comp]
    subst e1
    rw [← e0 ι τ] at h3
    exact h3
  · have := ha L ψ' (fun τ i => spMap (dualMap (ψ.comp j)) ≫ fr.v τ i) 1 y (fun τ i => ?_) hpt hu
    · exact this.trans (by simp; rfl)
    · refine ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩
      obtain ⟨f', hf'⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R L _ _ f ψ
      have h := isCombAtG_single Z.t _ (fun k => hf' τ k ▸ f'.tan τ k) i
      rw [← congrFun (e0 ψ τ) i]
      exact h

theorem value_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (ex : Ix Dw → ℤ) (g : Rul Xo c) (σ : c.F →+* ℂ) (ψ : Γ(C.Y.X, U) →+* ℂ) (y : FrPt Xo c (CAt σ)) (a b : Γ(C.Y.X, U)), fr.Tri (fnOf U hg) C.f0 t → ex none = 0 → g ∈ GlobalTheory.AllWt.secZ Xo c ex → ψ.comp φ = σ → Matches fr ψ y → fnOf U hg a = C.val g * ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : C.Y.Fnˣ)⁻¹ : C.Y.Fnˣ) * fnOf U hg b → ψ a = toC (evR Xo c g y) * ψ b := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C U hU hg φ fr t ex g σ ψ y a b hT hex hsec hσ hM hab
  letI := (constF e C.Y).toAlgebra
  have hinj : Function.Injective (fnOf U hg) := fnOf_injective U hg
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime (RingHom.ker ψ)
  have u1 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (fnOf U hg s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [(injective_iff_map_eq_zero _).1 hinj _ h]; exact zero_mem _)
  let ψ₀ : Γ(C.Y.X, U) →+* CAt σ := ψ
  have u2 : ∀ s : (RingHom.ker ψ).primeCompl, IsUnit (ψ₀ s) := fun s => IsUnit.mk0 (G₀ := ℂ) _ s.2
  let ι : R →+* C.Y.Fn := IsLocalization.lift u1
  let χ : R →+* CAt σ := IsLocalization.lift u2
  have e1 : ι.comp (algebraMap _ R) = fnOf U hg := IsLocalization.lift_comp u1
  have e2 : χ.comp (algebraMap _ R) = ψ₀ := IsLocalization.lift_comp u2
  haveI : IsDomain Γ(C.Y.X, U) := hinj.isDomain _
  have hι : Function.Injective ι := (IsLocalization.lift_injective_iff u1).2 fun p q =>
    (IsLocalization.injective R (RingHom.ker ψ).primeCompl_le_nonZeroDivisors).eq_iff.trans hinj.eq_iff.symm
  haveI : IsLocalHom χ := ⟨fun r hr => by
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (RingHom.ker ψ).primeCompl r
    have h1 : χ r * ψ₀ s = ψ₀ p := by
      rw [← e2]; simpa using congrArg χ h
    have h2 : p ∈ (RingHom.ker ψ).primeCompl := IsUnit.ne_zero (M₀ := ℂ) (show IsUnit (ψ₀ p) from h1 ▸ hr.mul (u2 s))
    have h3 := IsLocalization.map_units R (⟨p, h2⟩ : (RingHom.ker ψ).primeCompl)
    exact isUnit_of_mul_isUnit_left (h ▸ h3)⟩
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hgen : genericPt C.Y = spMap (fnOf U hg) ≫ (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) :=
    (hU.fromSpecStalk_eq_fromSpecStalk hg).symm
  obtain ⟨a₀, h1, h2⟩ := exists_value_local (algebraMap _ R) ι hι χ φ _ fr C.f0 t (e1 ▸ hT) C.y0
    (by rw [e1, ← Category.assoc, ← hgen]; exact C.y0_x) C.flagComponentFramedPoint_frame (by rw [e2]; exact hσ) y
    (by rw [e2]; exact hM.1) (by rw [e2]; exact hM.2) hex hsec
  have h3 : algebraMap _ R a = a₀ * algebraMap _ R b := hι (by
    rw [map_mul]
    refine (RingHom.congr_fun e1 a).trans (hab.trans ?_)
    rw [show ι (algebraMap _ R b) = fnOf U hg b from RingHom.congr_fun e1 b, show C.val g = _ from h1,
      mul_right_comm _ (ι a₀), Units.mul_inv, _root_.one_mul])
  have h4 := congrArg χ h3
  rw [map_mul, ← h2] at h4
  exact (RingHom.congr_fun e2 a).symm.trans (h4.trans (congrArg (evR Xo c g y * ·) (RingHom.congr_fun e2 b)))

end GlobalTheory.ShFam.ChartValue
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_generic_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hg : genericPoint C.Y.X ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (ex : Ix Dw → ℤ) (g : Rul Xo c) (σ : c.F →+* ℂ) (ψ : Γ(C.Y.X, U) →+* ℂ) (y : FrPt Xo c (CAt σ)) (a b : Γ(C.Y.X, U)), fr.Tri (fnOf U hg) C.f0 t → ex none = 0 → g ∈ GlobalTheory.AllWt.secZ Xo c ex → ψ.comp φ = σ → Matches fr ψ y → fnOf U hg a = C.val g * ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : C.Y.Fnˣ)⁻¹ : C.Y.Fnˣ) * fnOf U hg b → ψ a = toC (evR Xo c g y) * ψ b := by
  first | exact @GlobalTheory.ShFam.ChartValue.value_at_point | exact GlobalTheory.ShFam.ChartValue.value_at_point | (intros; apply GlobalTheory.ShFam.ChartValue.value_at_point <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_mul_exp (C C' c c' T : ℝ) (B : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Tendsto (fun w : ℂ => C * Real.exp (-c * (c' * (w.im - T))) * (C' * w.im ^ B)) imTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ B * Real.exp (-(c * c') * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c * c') (mul_pos hc hc')
    simpa only [Real.rpow_natCast] using this
  have h2 := (h1.const_mul (C * C' * Real.exp (c * c' * T))).comp (tendsto_comap (f := Complex.im))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  have : Real.exp (-c * (c' * (w.im - T))) = Real.exp (c * c' * T) * Real.exp (-(c * c') * w.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Function.comp, this]
  ring

theorem tendsto_cusp {N : ℕ} {X : Data E N} {T : ℝ} {x : ℂ → Frame X.Ψ N} {la : Wt X.Ψ N} {P : Frame X.Ψ N → ℂ}
    (hP : P ∈ X.SS la) (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {ξ : Fin N → E} {c' : ℝ} (hξ : X.IsIso ξ) (hc' : 0 < c')
    (ht : ∀ w : ℂ, T + 1 < w.im → ∀ τ, c' * (w.im - T) ≤ X.tt ξ (x w) τ) {C' : ℝ} {B : ℕ}
    (hn : ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C' * w.im ^ B) :
    Tendsto (fun w => P (x w)) imTop (𝓝 0) := by
  obtain ⟨C, c, hc, hC⟩ := GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso E N X la P ξ hP hξ
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp C C' c c' T B hc hc')
  have he : ∀ᶠ w in imTop, T + 1 + 1 / c' < w.im :=
    (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  filter_upwards [hn, he] with w h1 h2
  have h0 : 0 < 1 / c' := by positivity
  have h3 : 1 ≤ c' * (w.im - T) := by
    have : 1 / c' ≤ w.im - T := by linarith
    rwa [div_le_iff₀' hc'] at this
  have h4 := hC (x w) (hd w (by linarith)) _ h3 (ht w (by linarith))
  have h5 : ‖P (x w)‖ = X.pnorm la P (x w) * (X.nfac la (x w))⁻¹ := by
    show _ = ‖P (x w)‖ * X.nfac la (x w) * _
    rw [mul_assoc, mul_inv_cancel₀ h1.1.ne', mul_one]
  have h6 : 0 ≤ X.pnorm la P (x w) := mul_nonneg (norm_nonneg _) h1.1.le
  rw [h5]
  exact mul_le_mul h4 h1.2 (inv_nonneg.2 h1.1.le) (h6.trans h4)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

theorem isEqn_LEx {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) (ex : Ix Dw → ℤ) {y : C.Y.X}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t τ i)) :
    (C.LEx ex).IsEqn y (∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k))⁻¹ := by
  have hE : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      (∑ k ∈ s, ex (some k) • C.gr k.1 k.2).IsEqn y (∏ k ∈ s, t k.1 k.2 ^ ex (some k)) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk]; exact ((ht _ _).zsmul _).add ih
  exact (hE Finset.univ).neg

end GlobalTheory.ShFam.BdArc
end
end
