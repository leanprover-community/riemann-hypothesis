import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShare

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

def shareExp (e : ℕ) : ℕ := (e + 15) / 16

def ShareBound.Statement : Prop :=
  ∀ (n : ℕ) (MS : Type) [TopologicalSpace MS] [T2Space MS] [SecondCountableTopology MS]
    [ConnectedSpace MS] (De : MvPolynomial (Fin n) ℂ) (z : MS → (Fin n → ℂ)) (δ : ℕ)
    (e : ℕ) (f τ w₀ : MS → ℂ) (s : Fin n → MS → ℂ) (hF hθ hτ hW wn rh : MS → ℝ)
    (κ Cf Cτ cw CompactFixesLatticeTheory K : ℝ),
    MvPolynomial.eval 0 De ≠ 0 →
    IsCoveringOfDegree z (complementOf De) δ →
    HolomorphicAlong z f → HolomorphicAlong z τ → HolomorphicAlong z w₀ →
    (∀ p, w₀ p ≠ 0) → (∀ p i, s i p = z p i * w₀ p) →
    (∀ p, 0 < hF p) → (∀ p, 0 < hθ p) → (∀ p, 0 < hτ p) → (∀ p, 0 < hW p) → 0 < κ →
    (∀ p, hF p * hθ p * hτ p ^ shareExp e = κ * hW p ^ e) →
    (∀ p, ‖f p‖ * hF p ≤ Cf) →
    (∃ (θ : MS → ℂ) (Cθ : ℝ), HolomorphicAlong z θ ∧ θ ≠ 0 ∧ ∀ p, ‖θ p‖ * hθ p ≤ Cθ) →
    τ ≠ 0 →
    (∀ p, ‖τ p‖ * hτ p ≤ Cτ * Real.exp (-(4 * rh p))) →
    0 < cw → (∀ p, 0 ≤ wn p) → (∀ p, cw * Real.exp (-(rh p / 2)) ≤ wn p ^ 2) →
    (∀ p, -K ≤ rh p) →
    (∀ p, wn p ≤ CompactFixesLatticeTheory * (hW p * Real.sqrt (‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2))) →
    f = 0 ∨ ∃ p, z p = 0 ∧ ¬ OrderGT z f p e

section Inhabitant

end Inhabitant

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

theorem HolomorphicAlong.analyticOnNhd {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (e : OpenPartialHomeomorph MS (Fin n → ℂ))
    (hz : ∀ q ∈ e.source, z q = e q) : AnalyticOnNhd ℂ (u ∘ e.symm) e.target := by
  intro x hx
  have hq : e.symm x ∈ e.source := e.map_target hx
  obtain ⟨e', hq', hz', han⟩ := hu (e.symm x)
  have hex : e' (e.symm x) = x := by rw [← hz' _ hq', hz _ hq, e.right_inv hx]
  have hx' : x ∈ e'.target := hex ▸ e'.map_source hq'
  refine (han x hx').congr ?_
  have h1 : ∀ᶠ x' in 𝓝 x, x' ∈ e.target := e.open_target.mem_nhds hx
  have h2 : ∀ᶠ x' in 𝓝 x, e.symm x' ∈ e'.source :=
    (e.continuousAt_symm hx).preimage_mem_nhds (e'.open_source.mem_nhds hq')
  filter_upwards [h1, h2] with x' h1 h2
  have h3 : e' (e.symm x') = x' := by rw [← hz' _ h2, hz _ (e.map_target h1), e.right_inv h1]
  have h4 : e'.symm x' = e.symm x' := by
    calc e'.symm x' = e'.symm (e' (e.symm x')) := by rw [h3]
      _ = e.symm x' := e'.left_inv h2
  simp only [Function.comp_apply, h4]

theorem HolomorphicAlong.continuous {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) : Continuous u := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨e, hp, -, han⟩ := hu p
  have hc : ContinuousAt ((u ∘ e.symm) ∘ e) p :=
    (han (e p) (e.map_source hp)).continuousAt.comp (e.continuousAt hp)
  refine hc.congr ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  simp [e.left_inv hq]

theorem HolomorphicAlong.mul {z : MS → (Fin n → ℂ)} {u v : MS → ℂ}
    (hu : HolomorphicAlong z u) (hv : HolomorphicAlong z v) :
    HolomorphicAlong z (fun p => u p * v p) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).mul (hv.analyticOnNhd e hz)⟩

theorem HolomorphicAlong.pow {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (k : ℕ) : HolomorphicAlong z (fun p => u p ^ k) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).pow k⟩

theorem HolomorphicAlong.eq_zero_of_eventually [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {u : MS → ℂ} (hu : HolomorphicAlong z u) {p₀ : MS} (h₀ : u =ᶠ[𝓝 p₀] 0) : u = 0 := by
  set A : Set MS := {p | u =ᶠ[𝓝 p] 0} with hA
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun p hp => ?_
    obtain ⟨e, hpe, hz, -⟩ := hu p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hpe)
    have hV : e.source ∩ e ⁻¹' Metric.ball (e p) ε ∈ 𝓝 p :=
      inter_mem (e.open_source.mem_nhds hpe)
        ((e.continuousAt hpe).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
    obtain ⟨q, ⟨hqs, hqb⟩, hqA⟩ := mem_closure_iff_nhds.1 hp _ hV
    have han : AnalyticOnNhd ℂ (u ∘ e.symm) (Metric.ball (e p) ε) :=
      (hu.analyticOnNhd e hz).mono hball
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (e q)] 0 := by
      have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
        have := (e.continuousAt_symm (e.map_source hqs)).tendsto
        rwa [e.left_inv hqs] at this
      exact ht.eventually hqA
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (e p) ε).isPreconnected hqb hev
    show u =ᶠ[𝓝 p] 0
    filter_upwards [hV] with q' ⟨hq's, hq'b⟩
    have := hzero hq'b
    simpa [e.left_inv hq's] using this
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨p₀, h₀⟩
  funext p
  have hp : p ∈ A := huniv ▸ Set.mem_univ p
  exact hp.self_of_nhds

theorem HolomorphicAlong.eq_zero_of_mul_eq_zero [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {g h : MS → ℂ} (hg : HolomorphicAlong z g) (hh : HolomorphicAlong z h)
    (hgh : ∀ p, g p * h p = 0) (hg0 : g ≠ 0) : h = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, g p ≠ 0 := by
    by_contra H
    exact hg0 (funext fun p => by_contra fun hp => H ⟨p, hp⟩)
  have hne : ∀ᶠ q in 𝓝 p, g q ≠ 0 := hg.continuous.continuousAt.eventually_ne hp
  refine hh.eq_zero_of_eventually (p₀ := p) ?_
  filter_upwards [hne] with q hq
  exact (mul_eq_zero.1 (hgh q)).resolve_left hq

theorem eventually_norm_le_of_continuous {u : MS → ℂ} (hu : Continuous u) (p : MS) :
    ∀ᶠ q in 𝓝 p, ‖u q‖ ≤ ‖u p‖ + 1 := by
  have : ∀ᶠ q in 𝓝 p, ‖u q‖ < ‖u p‖ + 1 :=
    hu.norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  filter_upwards [this] with q hq using hq.le

theorem ShareCore.proof (hNorm : NormLemma.Statement) : ShareCore.Statement := by
  intro n MS _ _ _ _ De z δ f θ τ C e a hDe hcov hf hθ hτ hθ0 hτ0 hbound hord
  have hτa : HolomorphicAlong z (fun p => τ p ^ a) := hτ.pow a
  have hg : HolomorphicAlong z (fun p => θ p * τ p ^ a) := hθ.mul hτa
  have hg0 : (fun p => θ p * τ p ^ a) ≠ 0 := by
    intro H
    have h0 : (fun p => τ p ^ a) = 0 :=
      hθ.eq_zero_of_mul_eq_zero hτa (fun p => congrFun H p) hθ0
    exact hτ0 (funext fun p => eq_zero_of_pow_eq_zero (congrFun h0 p))
  have hu : HolomorphicAlong z (fun p => f p * θ p * τ p ^ a) := (hf.mul hθ).mul hτa
  have horder : ∀ p, z p = 0 → OrderGT z (fun p => f p * θ p * τ p ^ a) p e := by
    intro p hp
    obtain ⟨Cf, hCf⟩ := hord p hp
    refine ⟨Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a), ?_⟩
    filter_upwards [hCf, eventually_norm_le_of_continuous hθ.continuous p,
      eventually_norm_le_of_continuous hτ.continuous p] with q hq1 hq2 hq3
    rw [norm_mul, norm_mul, norm_pow]
    have hr : 0 ≤ Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := (norm_nonneg _).trans hq1
    calc ‖f q‖ * ‖θ q‖ * ‖τ q‖ ^ a
        ≤ (Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1)) * (‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a := by
          gcongr
      _ = Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a) * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := by
          ring
  have hu0 := hNorm n MS De z δ _ C e hDe hcov hu hbound horder
  exact hg.eq_zero_of_mul_eq_zero hf (fun p => by
    have := congrFun hu0 p
    simp only [Pi.zero_apply] at this
    linear_combination this) hg0

theorem ShareNumbers.proof : ShareNumbers.Statement := by
  intro D N T hD hN hT
  have h11 : 11 * D ≤ T := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> omega

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

theorem HolomorphicAlong.inv {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (h0 : ∀ p, u p ≠ 0) : HolomorphicAlong z (fun p => (u p)⁻¹) := by
  intro p
  obtain ⟨e, hp, hz, han⟩ := hu p
  exact ⟨e, hp, hz, fun x hx => (han x hx).inv (h0 _)⟩

theorem le_sixteen_mul_shareExp (e : ℕ) : e ≤ 16 * shareExp e := by
  unfold shareExp; omega

theorem exp_quarter_le {rh wn cw : ℝ} (hcw : 0 < cw) (hwn : 0 ≤ wn)
    (h : cw * Real.exp (-(rh / 2)) ≤ wn ^ 2) : Real.exp (-(rh / 4)) ≤ wn / Real.sqrt cw := by
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.2 hcw
  rw [le_div_iff₀ hsc]
  have h1 : (Real.exp (-(rh / 4)) * Real.sqrt cw) ^ 2 = cw * Real.exp (-(rh / 2)) := by
    rw [mul_pow, Real.sq_sqrt hcw.le, ← Real.exp_nat_mul]
    push_cast; ring_nf
  have h2 : 0 ≤ Real.exp (-(rh / 4)) * Real.sqrt cw := by positivity
  nlinarith [h1, h, sq_nonneg (Real.exp (-(rh / 4)) * Real.sqrt cw - wn)]

theorem exp_four_mul_le {rh K : ℝ} {a e : ℕ} (hK : -K ≤ rh) (hae : e ≤ 16 * a) :
    Real.exp (-(4 * rh)) ^ a ≤ Real.exp (K * (4 * a - e / 4)) * Real.exp (-(rh / 4)) ^ e := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hae' : (e : ℝ) ≤ 16 * a := by exact_mod_cast hae
  nlinarith

theorem share_pointwise {x y t ω N hF hθ hτ hW wn rh κ Cf Cθ Cτ cw CompactFixesLatticeTheory K : ℝ} {a e : ℕ}
    (hae : e ≤ 16 * a) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) (hω : 0 < ω) (hN : 0 ≤ N)
    (hF0 : 0 < hF) (hθ0 : 0 < hθ) (hτ0 : 0 < hτ) (hW0 : 0 < hW) (hκ : 0 < κ)
    (hbk : hF * hθ * hτ ^ a = κ * hW ^ e)
    (hf : x * hF ≤ Cf) (hth : y * hθ ≤ Cθ) (htau : t * hτ ≤ Cτ * Real.exp (-(4 * rh)))
    (hcw : 0 < cw) (hwn : 0 ≤ wn) (hw : cw * Real.exp (-(rh / 2)) ≤ wn ^ 2) (hK : -K ≤ rh)
    (hfl : wn ≤ CompactFixesLatticeTheory * (hW * (ω * Real.sqrt (1 + N)))) :
    x * (y * (ω ^ e)⁻¹) * t ^ a ≤
      Cf * Cθ * Cτ ^ a * Real.exp (K * (4 * a - e / 4)) * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ *
        (1 + N) ^ ((e : ℝ) / 2) := by
  set E := Real.exp (K * (4 * a - e / 4))
  set S := Real.sqrt (1 + N)
  have hS : (1 + N) ^ ((e : ℝ) / 2) = S ^ e := by
    simp only [S]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  rw [hS]
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.2 hcw
  have hCf : 0 ≤ Cf := (by positivity : 0 ≤ x * hF).trans hf
  have hCθ : 0 ≤ Cθ := (by positivity : 0 ≤ y * hθ).trans hth
  have hCτ : 0 ≤ Cτ := by
    have : 0 ≤ Cτ * Real.exp (-(4 * rh)) := (by positivity : 0 ≤ t * hτ).trans htau
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)

  have hprod : (x * hF) * (y * hθ) * (t * hτ) ^ a ≤
      Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := by
    calc (x * hF) * (y * hθ) * (t * hτ) ^ a
        ≤ Cf * Cθ * (Cτ * Real.exp (-(4 * rh))) ^ a := by
          gcongr
      _ = Cf * Cθ * Cτ ^ a * Real.exp (-(4 * rh)) ^ a := by rw [mul_pow]; ring
      _ ≤ Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := by
          gcongr; exact exp_four_mul_le hK hae

  have hq : Real.exp (-(rh / 4)) ≤ CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S) := by
    calc Real.exp (-(rh / 4)) ≤ wn / Real.sqrt cw := exp_quarter_le hcw hwn hw
      _ ≤ CompactFixesLatticeTheory * (hW * (ω * S)) / Real.sqrt cw := by gcongr
      _ = CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S) := by ring
  have hqe : Real.exp (-(rh / 4)) ^ e ≤ (CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e) := by
    calc Real.exp (-(rh / 4)) ^ e ≤ (CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S)) ^ e := by
          gcongr
      _ = (CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e) := by ring
  have hden : 0 < κ * hW ^ e * ω ^ e := by positivity
  have hlhs : x * (y * (ω ^ e)⁻¹) * t ^ a =
      (x * hF) * (y * hθ) * (t * hτ) ^ a / (κ * hW ^ e * ω ^ e) := by
    rw [← hbk]; field_simp; ring
  rw [hlhs, div_le_iff₀ hden]
  calc (x * hF) * (y * hθ) * (t * hτ) ^ a
      ≤ Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := hprod
    _ ≤ Cf * Cθ * Cτ ^ a * (E * ((CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e))) := by
        gcongr
    _ = Cf * Cθ * Cτ ^ a * E * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ * S ^ e * (κ * hW ^ e * ω ^ e) := by
        field_simp

theorem ShareBound.proof (hNorm : NormLemma.Statement) : ShareBound.Statement := by
  intro n MS _ _ _ _ De z δ e f τ w₀ s hF hθ hτ hW wn rh κ Cf Cτ cw CompactFixesLatticeTheory K hDe hcov hf hτ hw₀
    hw₀0 hs hF0 hθ0 hτ0 hW0 hκ hbk hfb hex hτne htau hcw hwn hw hK hfl
  obtain ⟨θ, Cθ, hθ, hθne, hθb⟩ := hex
  set a := shareExp e

  set θ' : MS → ℂ := fun p => θ p * (w₀ p ^ e)⁻¹
  have hw₀e : HolomorphicAlong z (fun p => w₀ p ^ e) := hw₀.pow e
  have hθ' : HolomorphicAlong z θ' := hθ.mul (hw₀e.inv fun p => pow_ne_zero _ (hw₀0 p))
  have hθ'ne : θ' ≠ 0 := by
    intro H
    apply hθne
    funext p
    have := congrFun H p
    simp only [θ', Pi.zero_apply, mul_eq_zero, inv_eq_zero] at this
    exact this.resolve_right (pow_ne_zero _ (hw₀0 p))
  have hbound : ∀ p, ‖f p * θ' p * τ p ^ a‖ ≤
      Cf * Cθ * Cτ ^ a * Real.exp (K * (4 * a - e / 4)) * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ *
        (1 + normSq (z p)) ^ ((e : ℝ) / 2) := by
    intro p
    have hsum : ‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2 = ‖w₀ p‖ ^ 2 * (1 + normSq (z p)) := by
      simp only [hs p, norm_mul, mul_pow, normSq, ← Finset.sum_mul]
      ring
    have hfl' : wn p ≤ CompactFixesLatticeTheory * (hW p * (‖w₀ p‖ * Real.sqrt (1 + normSq (z p)))) := by
      have := hfl p
      rwa [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    have hN : 0 ≤ normSq (z p) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have := share_pointwise (le_sixteen_mul_shareExp e) (norm_nonneg (f p)) (norm_nonneg (θ p))
      (norm_nonneg (τ p)) (norm_pos_iff.2 (hw₀0 p)) hN (hF0 p) (hθ0 p) (hτ0 p) (hW0 p) hκ
      (hbk p) (hfb p) (hθb p) (htau p) hcw (hwn p) (hw p) (hK p) hfl'
    simpa only [θ', norm_mul, norm_inv, norm_pow] using this
  by_cases H : ∀ p, z p = 0 → OrderGT z f p e
  · left
    exact ShareCore.proof hNorm n MS De z δ f θ' τ _ e a hDe hcov hf hθ' hτ hθ'ne hτne hbound H
  · right
    push Not at H
    exact H

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end
