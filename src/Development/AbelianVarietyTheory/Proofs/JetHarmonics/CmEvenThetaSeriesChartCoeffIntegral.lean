import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  first | exact @GlobalTheory.MomOne.sup_norm_laws | exact GlobalTheory.MomOne.sup_norm_laws | (intros; apply GlobalTheory.MomOne.sup_norm_laws <;> assumption)
end

section
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThetaQuot

def fac (d : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ) +
    (-(Real.pi : ℂ) * h1 d z y - (Real.pi : ℂ) / 2 * h1 d y y))

lemma fac_ne (d : ℕ) (y z : ℂ) : fac d y z ≠ 0 := Complex.exp_ne_zero _

lemma nonzeroIndexPlaces_adelicDataResized_eq (d : ℕ) (y : ℂ) (F : ℂ → ℂ) (z : ℂ) : W1 d y F z = fac d y z * F (z + y) := by
  simp only [W1, U1, fac, Complex.exp_add]; ring

lemma fac_mul (d : ℕ) (α : ℂ) (m : ℕ) (hm : (m : ℂ) = α * conj α) (y z : ℂ) :
    fac d (α * y) (α * z) = fac d y z ^ m := by
  simp only [fac]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [hm, ← Complex.mul_conj, ← Complex.mul_conj]
  simp only [h1, map_mul]
  ring

lemma not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h2 : (-1 : ℂ) = 2 * u + v * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    simp only [wK] at h
    linear_combination 2 * h
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have : (-1 : ℤ) = 2 * u := by
    have : (-1 : ℝ) = 2 * u := by simpa using hre
    exact_mod_cast this
  omega

lemma inOK_mul (d : ℕ) (hd : d % 4 = 3) {α β : ℂ} (ha : InOK d α) (hb : InOK d β) : InOK d (α * β) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨u', v', rfl⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp
  have hk' : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  have hw : wK d ^ 2 = wK d - k := by
    simp only [wK]
    linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4) * hs - (1 / 4) * hk'
  refine ⟨u * u' - k * v * v', u * v' + v * u' + v * v', ?_⟩
  push_cast
  linear_combination (v * v' : ℂ) * hw

lemma zero_of_pole {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (p : ℂ)
    (h : meromorphicOrderAt (fun z => F z / G z) p < 0) : G p = 0 := by
  by_contra hp
  have ha : AnalyticAt ℂ (fun z => F z / G z) p := (hF.analyticAt p).div (hG.analyticAt p) hp
  exact absurd ha.meromorphicOrderAt_nonneg (not_le.mpr h)

theorem theta_quot : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  intro d q _ M ω θ hd hd16 hsp hL hch hθ α m hα hα0 hm
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  have hd4 : d % 4 = 3 := by omega
  have hA : Differentiable ℂ (fun z => θ (α * z)) := hdiff.comp (differentiable_id.const_mul α)
  have hB : Differentiable ℂ (fun z => θ z ^ m) := hdiff.pow m
  have hper : ∀ l ∈ M.L.lattice, ∀ z, θ (α * z) = fac d l z ^ m * θ (α * (z + l)) ∧
      θ z ^ m = fac d l z ^ m * θ (z + l) ^ m := by
    intro l hl z
    have hl' := (hL l).1 hl
    constructor
    · have := congrFun (hW _ (inOK_mul d hd4 hα hl')) (α * z)
      rw [nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm] at this
      rw [← this, mul_add]
    · have := congrFun (hW _ hl') z
      rw [nonzeroIndexPlaces_adelicDataResized_eq] at this
      rw [← mul_pow, this]
  have hEε : Ell M.L (fun z => θ (α * z) / θ z ^ m) := by
    refine ⟨fun p => (hA.analyticAt p).meromorphicAt.div (hB.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (α * (z + l)) / θ (z + l) ^ m = θ (α * z) / θ z ^ m
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hEη : Ell M.L (fun z => θ z ^ m / θ (α * z)) := by
    refine ⟨fun p => (hB.analyticAt p).meromorphicAt.div (hA.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (z + l) ^ m / θ (α * (z + l)) = θ z ^ m / θ (α * z)
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hA0 : θ (α * 0) ≠ 0 := by simp [h0]
  have hB0 : θ 0 ^ m ≠ 0 := by simp [h0]
  have haε : AnalyticAt ℂ (fun z => θ (α * z) / θ z ^ m) 0 :=
    (hA.analyticAt 0).div (hB.analyticAt 0) hB0
  have haη : AnalyticAt ℂ (fun z => θ z ^ m / θ (α * z)) 0 :=
    (hB.analyticAt 0).div (hA.analyticAt 0) hA0
  have hns : ∀ β p : ℂ, InOK d β → β ≠ 0 → θ (β * p) = 0 → ¬ M.Small p := by
    intro β p hβ hβ0 hp hs
    have hp0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
    have := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hch).2.2.2 p β 0 hβ hβ0 hp0
      (by simpa using hz _ hp) hs
    exact not_half d hd.pos this.2
  have hbε : Bdd (hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m)) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEε haε fun p hp => ?_
    have := zero_of_pole hA hB p hp
    exact hns 1 p ⟨1, 0, by simp⟩ one_ne_zero (by simpa using (pow_eq_zero_iff'.1 this).1)
  have hbη : Bdd (hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z))) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEη haη fun p hp => ?_
    exact hns α p hα hα0 (zero_of_pole hB hA p hp)
  obtain ⟨hh1, hh2, -, hh4, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q M.ι (C ω * logS) hch.2.1
  have hprod : hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m) *
      hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z)) = 1 := by
    rw [← (hh1 _ _ haε haη).2.1]
    have e1 : ∀ᶠ z in 𝓝 (0 : ℂ), θ (α * z) ≠ 0 := hA.continuous.continuousAt.eventually_ne hA0
    have e2 : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ^ m ≠ 0 := hB.continuous.continuousAt.eventually_ne hB0
    have := (hh1 _ (fun _ => (1 : ℂ)) (haε.mul haη) analyticAt_const).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with z h1' h2'
      show θ (α * z) / θ z ^ m * (θ z ^ m / θ (α * z)) = 1
      field_simp)
    refine Eq.trans this ?_
    rw [hh2]; simp
  have hε0 : θ (α * 0) / θ 0 ^ m = 1 := by simp [h0]
  have hmain : ∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * (θ (α * z) / θ z ^ m) := by
    intro z hz'
    field_simp
  refine ⟨fun z => θ (α * z) / θ z ^ m, hEε, haε, hε0, ?_, hmain, ?_⟩
  · refine ((GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws q).2.2.2.2.1 _ _ hbε hbη hprod ?_).1
    rw [hh4]; simp [h0]
  · intro y z hyz
    rw [nonzeroIndexPlaces_adelicDataResized_eq, nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm, ← mul_add, mul_pow, mul_assoc]
    exact congrArg _ (hmain _ hyz)

end GlobalTheory.MomOne.ThetaQuot
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  atlas_forward_decl GlobalTheory.MomOne.ThetaQuot.theta_quot
end

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem theta_series_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 →
    Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  intro d q hq M ω θ hd h16 hs hL hM hθ
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd h16 hs
  obtain ⟨α, hα, hα1, hα2⟩ := h4 1 1 (Nat.coprime_one_left q)
  obtain ⟨⟨a, ha⟩, ⟨m, hm⟩, -⟩ := h2 α hα
  have hq1 : (q : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    exact zpow_lt_one_of_neg₀ this (by norm_num)
  have hα1' : ‖M.ι α - 1‖ < 1 := by
    have := hα1.trans_lt hq1
    simpa using this
  have hn : ‖M.ι α‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := M.ι α - 1) (y := (1 : ℂ_[q]))
      (by rw [norm_one]; exact hα1'.ne)
    rw [sub_add_cancel, norm_one, max_eq_right hα1'.le] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hn
  have hmn : ‖(m : ℂ_[q])‖ < 1 := by
    have : (m : ℂ_[q]) = M.ι α * M.ι (conj α) := by
      rw [← map_mul, ← hm, map_natCast]
    rw [this, norm_mul, hn, one_mul]
    exact hα2.trans_lt hq1
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exfalso
      have : α * conj α = 0 := by rw [← hm]; simp
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    · simp at hmn
    · omega
  obtain ⟨ε, -, hεa, -, hεb, hfe, -⟩ := GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries d q M ω θ hd h16 hs hL hM hθ α m hα hα0 hm
  obtain ⟨hmul, -⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨hb, hc0, hc1, -⟩ := hmul a
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul]
    have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
    rw [this, mul_zero]
  obtain ⟨hring, hconst, -, hcc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  have hθa : ∀ z, AnalyticAt ℂ θ z := fun z => hθ.1.analyticAt z
  have hpow : ∀ k : ℕ, hat M.ι (C ω * logS) (fun z => θ z ^ k) = hat M.ι (C ω * logS) θ ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have := (hring (fun z => θ z ^ k) θ ((hθa 0).pow k) (hθa 0)).2.1
      simp only [pow_succ]
      rw [this, ih]
  have hsub := (GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω θ (hθa 0)).2.2.1 α a ha
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
    (hθa 0).continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
  have hαa : AnalyticAt ℂ (fun z => θ (α * z)) 0 :=
    (hθ.1.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => α * z))).analyticAt 0
  have heq := (hring (fun z => θ (α * z)) (fun z => θ z ^ m * ε z) hαa (((hθa 0).pow m).mul hεa)).2.2.1
    ((hne.mono fun z hz => hfe z hz).filter_mono nhdsWithin_le_nhds)
  rw [hsub, (hring (fun z => θ z ^ m) ε ((hθa 0).pow m) hεa).2.1, hpow] at heq
  refine (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m hc0 (by rw [hc1, ← ha, hn]) hmn hm2).2 _ _ hb hεb ?_ heq
  rw [hcc, hθ.2.1, map_one]

end GlobalTheory.MomOne
end
