import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add, map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FormalMul

section General
variable {K : Type*} [CommRing K]

theorem hs {f : K⟦X⟧} (hf : constantCoeff f = 0) : HasSubst f := HasSubst.of_constantCoeff_zero' hf

theorem cc_subst {f g : K⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    constantCoeff (f.subst g : K⟦X⟧) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (τ := Unit) hg f hf

theorem subst_C' (g : K⟦X⟧) (r : K) : ((C r : K⟦X⟧).subst g : K⟦X⟧) = C r := PowerSeries.subst_C r

theorem taylor_dvd (U f h : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 0) (hh0 : constantCoeff h = 0)
    (hh : X ^ N ∣ h) :
    (X : K⟦X⟧) ^ (2 * N) ∣ (U.subst (f + h) : K⟦X⟧) - U.subst f - (d⁄dX K U).subst f * h := by
  have hfh : constantCoeff (f + h) = 0 := by rw [map_add, hf, hh0, add_zero]
  set M := 2 * N with hM
  obtain ⟨V, P, hU⟩ : ∃ (V : K⟦X⟧) (P : Polynomial K), U = X ^ (M + 1) * V + (P : K⟦X⟧) :=
    ⟨_, _, eq_X_pow_mul_shift_add_trunc (M + 1) U⟩
  have hD : d⁄dX K U = X ^ M * (((M + 1 : ℕ) : K⟦X⟧) * V + X * d⁄dX K V) +
      ((Polynomial.derivative P : Polynomial K) : K⟦X⟧) := by
    rw [hU, map_add, derivative_coe, Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    ring
  obtain ⟨k, hk⟩ := (P.map (algebraMap K K⟦X⟧)).binomExpansion f h
  rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
    Polynomial.eval_map_algebraMap] at hk
  rw [hD]
  rw [hU, subst_add (hs hfh), subst_add (hs hf), subst_add (hs hf), subst_mul (hs hfh), subst_mul (hs hf),
    subst_mul (hs hf), subst_pow (hs hfh), subst_pow (hs hf), subst_pow (hs hf), subst_X (hs hfh), subst_X (hs hf),
    subst_coe (hs hfh), subst_coe (hs hf), subst_coe (hs hf)]
  have d1 : (X : K⟦X⟧) ^ M ∣ f ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hf) _
  have d2 : (X : K⟦X⟧) ^ M ∣ (f + h) ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hfh) _
  have d3 : (X : K⟦X⟧) ^ M ∣ h ^ 2 := by
    rw [hM, mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hh _
  have key : ∀ a b c p0 p1 p2 : K⟦X⟧, p0 = p1 + p2 * h + k * h ^ 2 →
      (X : K⟦X⟧) ^ M ∣ (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h := by
    intro a b c p0 p1 p2 e
    have : (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h
        = (f + h) ^ M * ((f + h) * a) - f ^ M * (f * b + c * h) + h ^ 2 * k := by
      rw [e]; ring
    rw [this]
    exact dvd_add (dvd_sub (d2.mul_right _) (d1.mul_right _)) (d3.mul_right _)
  exact key _ _ _ _ _ _ hk

theorem add_law (G : MvPowerSeries (Fin 2) K) (U : K⟦X⟧) (hU : constantCoeff U = 0)
    (hG : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) G
      = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    (f g : K⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![U.subst f, U.subst g] : Fin 2 → MvPowerSeries Unit K) G : K⟦X⟧) = U.subst (f + g) := by
  have hb := GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 := by simp
  have comp : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) (PowerSeries.subst a U)
        = PowerSeries.subst (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) a) U := by
    intro a ha
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero ha).const hb]
    rfl
  have ha : MvPowerSeries.HasSubst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 0) U hU
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 1) U hU
  have := congrArg (MvPowerSeries.subst (R := K) (![f, g] : Fin 2 → MvPowerSeries Unit K)) hG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb, comp _ (by simp), MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at this
  refine Eq.trans ?_ this
  congr! 2 with s
  fin_cases s
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [comp _ (hX 0), MvPowerSeries.subst_X hb]; rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [comp _ (hX 1), MvPowerSeries.subst_X hb]; rfl

theorem deriv_mul_eq_one {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ((d⁄dX K U).subst ℓ : K⟦X⟧) * d⁄dX K ℓ = 1 := by
  rw [← derivative_subst (hs hℓ), h, derivative_X]

theorem subst_inv {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ℓ.subst U = (X : K⟦X⟧) := by
  have h1 := congrArg constantCoeff (deriv_mul_eq_one hℓ h)
  rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX K ℓ), coeff_derivative] at h1
  simp only [zero_add, Nat.cast_zero, mul_one] at h1
  have : Invertible (coeff 1 ℓ) := ⟨_, h1, by rw [mul_comm]; exact h1⟩
  have h2 := subst_substInv_right ℓ hℓ
  have hV : HasSubst ℓ.substInv := hs (by simp)
  have : U = ℓ.substInv := by
    have := subst_comp_subst_apply (hs hℓ) hV U
    rw [h, h2, subst_X hV] at this
    rw [this, ← PowerSeries.map_algebraMap_eq_subst_X]; simp
  rw [this, h2]

theorem coeff_subst_C_mul (U ℓ : K⟦X⟧) (hℓ : constantCoeff ℓ = 0) (n : ℕ) (a : K) :
    coeff n (U.subst (C a * ℓ) : K⟦X⟧) = ∑ d ∈ Finset.range (n + 1), coeff d U * (a ^ d * coeff n (ℓ ^ d)) := by
  rw [coeff_subst' (hs (by simp [hℓ])), finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_pow, ← map_pow, coeff_C_mul, smul_eq_mul]
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    have : coeff n (ℓ ^ d) = 0 := X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hℓ) d) n (by omega)
    show _ • _ = _
    rw [mul_pow, ← map_pow, coeff_C_mul, this, mul_zero, smul_zero]

end General

section Padic
variable {q : ℕ} [Fact q.Prime]

theorem mem_int_iff (x : ℂ_[q]) : x ∈ 𝓞_ℂ_[q] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

theorem bd_map (f : 𝓞_ℂ_[q]⟦X⟧) : Bd 1 (PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f) := by
  intro n
  rw [coeff_map]
  exact (mem_int_iff _).1 (coeff n f).2

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  rw [zc, norm_algebraMap']; rfl

theorem zc_natCast (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by simp [zc]

theorem zc_mul (a b : ℤ_[q]) : zc (a * b) = zc a * zc b := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def Van (m : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n < m, ‖coeff n f‖ < 1

theorem norm_add_lt {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_mul_lt_left {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy

theorem van_mul {f g : ℂ_[q]⟦X⟧} {a b : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (ha : Van a f) (hb : Van b g) :
    Van (a + b) (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => ‖x‖ < 1) (fun _ _ => norm_add_lt) (by simp) ?_
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h : p.1 < a
  · exact norm_mul_lt_left (ha _ h) (hg _)
  · rw [mul_comm]
    exact norm_mul_lt_left (hb _ (by omega)) (hf _)

theorem bd_pow {g : ℂ_[q]⟦X⟧} (hg : Bd 1 g) (d : ℕ) : Bd 1 (g ^ d) := by
  induction d with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ d ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih hg).2
    rwa [one_mul, ← pow_succ] at this

theorem van_pow {g : ℂ_[q]⟦X⟧} {r : ℕ} (hg : Bd 1 g) (hr : Van r g) (d : ℕ) : Van (d * r) (g ^ d) := by
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    rw [add_mul, one_mul, pow_succ]
    exact van_mul (bd_pow hg d) hg ih hr

theorem van_subst {f g : ℂ_[q]⟦X⟧} {m r : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (h0 : constantCoeff g = 0)
    (hm : Van m f) (hr : Van r g) : Van (m * r) (f.subst g) := by
  intro n hn
  rw [coeff_subst' (hs h0)]
  refine finsum_induction (fun x => ‖x‖ < 1) (by simp) (fun _ _ => norm_add_lt) fun d => ?_
  rw [smul_eq_mul]
  by_cases h : d < m
  · exact norm_mul_lt_left (hm _ h) (bd_pow hg d n)
  · rw [mul_comm]
    exact norm_mul_lt_left (van_pow hg hr d n (hn.trans_le (Nat.mul_le_mul_right r (by omega)))) (hf d)

theorem map_law (F : FormalGroup 𝓞_ℂ_[q]) (f g : 𝓞_ℂ_[q]⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f, PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) g] :
      Fin 2 → MvPowerSeries Unit ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) : ℂ_[q]⟦X⟧)
    = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q])
      (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit 𝓞_ℂ_[q]) F.toPowerSeries) := by
  symm
  refine (MvPowerSeries.map_subst (GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg) _).trans ?_
  congr! 2 with s
  fin_cases s <;> rfl

end Padic

theorem padic_multiplications : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  intro q hq F U ℓ hU hℓ hUℓ hG
  have law := add_law _ U hU hG
  have hinv := subst_inv hℓ hUℓ
  have hc : ∀ a : ℂ_[q], constantCoeff (C a * ℓ) = 0 := fun a => by simp [hℓ]
  have hB0 : ∀ a : ℂ_[q], constantCoeff (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) = 0 := fun a => cc_subst hU (hc a)
  have hℓB : ∀ a : ℂ_[q], (ℓ.subst (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C a * ℓ := fun a => by
    rw [← subst_comp_subst_apply (hs hU) (hs (hc a)), hinv, subst_X (hs (hc a))]
  have hcomp : ∀ a b : ℂ_[q], (PowerSeries.subst (U.subst (C b * ℓ) : ℂ_[q]⟦X⟧) (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = U.subst (C (a * b) * ℓ) := fun a b => by
    rw [subst_comp_subst_apply (hs (hc a)) (hs (hB0 b)), subst_mul (hs (hB0 b)), subst_C', hℓB, map_mul, mul_assoc]

  have hnat : ∀ n : ℕ, (U.subst (C (n : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)
      = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) (GlobalTheory.ConvSer.nMul F n) := by
    intro n
    induction n with
    | zero =>
      ext m
      rw [coeff_subst_C_mul U ℓ hℓ, GlobalTheory.ConvSer.nMul_zero, map_zero, map_zero]
      refine Finset.sum_eq_zero fun d _ => ?_
      rcases d with _ | d
      · simp [hU]
      · simp
    | succ n ih =>
      rw [GlobalTheory.ConvSer.nMul_succ, ← map_law F _ _ (GlobalTheory.ConvSer.nMul_constantCoeff F n) constantCoeff_X, ← ih, map_X]
      have := law _ _ (hc n) hℓ
      rw [hUℓ] at this
      rw [this]
      congr 1
      push_cast
      rw [map_add, map_one]
      ring
  have hint : ∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ)) := by
    intro a m
    refine PadicInt.denseRange_natCast.induction_on (p := fun a => ‖coeff m (U.subst (C (zc a) * ℓ) : ℂ_[q]⟦X⟧)‖ ≤ 1)
      a ?_ fun n => ?_
    · simp only [coeff_subst_C_mul U ℓ hℓ]
      have := continuous_zc (q := q)
      exact isClosed_le (by fun_prop) continuous_const
    · rw [zc_natCast, hnat]
      exact bd_map _ m
  have hBq : Bd 1 (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    have := hint q
    rwa [zc_natCast] at this

  have hone := deriv_mul_eq_one hℓ hUℓ
  set W : ℂ_[q]⟦X⟧ := C (coeff 1 ℓ) * (d⁄dX ℂ_[q] U).subst ℓ with hW
  have hW0 : constantCoeff W = 1 := by
    have h1 := congrArg constantCoeff hone
    rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX _ ℓ), coeff_derivative] at h1
    simp only [zero_add, Nat.cast_zero, mul_one] at h1
    rw [hW, map_mul, constantCoeff_C, mul_comm, h1]
  have hWint : Bd 1 W := by
    intro m
    set N := m + 2 with hN
    have hXN : constantCoeff (X ^ N : ℂ_[q]⟦X⟧) = 0 := by simp [hN]
    set h : ℂ_[q]⟦X⟧ := ℓ.subst (X ^ N : ℂ_[q]⟦X⟧) with hh
    have hh0 : constantCoeff h = 0 := cc_subst hℓ hXN
    have hUh : (U.subst h : ℂ_[q]⟦X⟧) = X ^ N := by
      rw [hh, ← subst_comp_subst_apply (hs hℓ) (hs hXN), hUℓ, subst_X (hs hXN)]
    obtain ⟨V, hV⟩ : ∃ V : ℂ_[q]⟦X⟧, ℓ = C (coeff 1 ℓ) * X + X ^ 2 * V := by
      have : (X : ℂ_[q]⟦X⟧) ^ 2 ∣ ℓ - C (coeff 1 ℓ) * X := by
        rw [X_pow_dvd_iff]
        intro j hj
        interval_cases j
        · simp [hℓ]
        · simp
      obtain ⟨V, hV⟩ := this
      exact ⟨V, by rw [← hV]; ring⟩
    have hh' : h = C (coeff 1 ℓ) * X ^ N + X ^ (2 * N) * V.subst (X ^ N : ℂ_[q]⟦X⟧) := by
      rw [hh]
      conv_lhs => rw [hV]
      rw [subst_add (hs hXN), subst_mul (hs hXN), subst_mul (hs hXN), subst_pow (hs hXN), subst_C', subst_X (hs hXN),
        ← pow_mul, mul_comm N 2]
    have hd : (X : ℂ_[q]⟦X⟧) ^ N ∣ h := by
      rw [hh']
      exact dvd_add (dvd_mul_left _ _) ((pow_dvd_pow _ (by omega)).mul_right _)
    obtain ⟨T, hT⟩ := taylor_dvd U ℓ h N hℓ hh0 hd
    have hl := law _ _ hℓ hh0
    have hb := map_law F X (X ^ N) constantCoeff_X (by simp [hN])
    rw [map_pow, map_X] at hb
    rw [hUℓ, hUh, hb] at hl
    have hbd : Bd 1 (U.subst (ℓ + h)) := hl ▸ bd_map _
    have e : (U.subst (ℓ + h) : ℂ_[q]⟦X⟧) = X + X ^ N * W +
        X ^ (2 * N) * (T + (d⁄dX ℂ_[q] U).subst ℓ * V.subst (X ^ N : ℂ_[q]⟦X⟧)) := by
      rw [hUℓ] at hT
      rw [hW]
      linear_combination hT + ((d⁄dX ℂ_[q] U).subst ℓ : ℂ_[q]⟦X⟧) * hh'
    have := hbd (m + N)
    rw [e, map_add, map_add, coeff_X_pow_mul, coeff_X, if_neg (by omega), coeff_X_pow_mul', if_neg (by omega)] at this
    simpa using this
  have hq1 : ‖(q : ℂ_[q])‖ < 1 := by
    rw [← zc_natCast, norm_zc, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt)
  have hder : Bd ‖(q : ℂ_[q])‖ (d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ))) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ W 0 _ hWint (by rw [hW0, norm_one]) ?_
    have e : X ^ 0 * W * d⁄dX ℂ_[q] (U.subst (C (q : ℂ_[q]) * ℓ))
        = C (q : ℂ_[q]) * W.subst (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧) := by
      rw [derivative_subst (hs (hc q)), hW, subst_mul (hs (hB0 q)), subst_C',
        subst_comp_subst_apply (hs hℓ) (hs (hB0 q)), hℓB, Derivation.leibniz, derivative_C]
      simp only [smul_eq_mul]
      linear_combination (C (coeff 1 ℓ) * C (q : ℂ_[q]) *
        ((d⁄dX ℂ_[q] U).subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)) * hone
    rw [e]
    intro n
    rw [coeff_C_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((sup_norm_laws q).2.1 W _ 1 hWint hBq (hB0 q) n)
  have h2 : ∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)‖ < 1 := by
    intro k hk
    rcases k with _ | k
    · exact absurd (dvd_zero q) hk
    have := hder k
    rw [coeff_derivative, norm_mul] at this
    have hk1 : ‖((k : ℂ_[q]) + 1)‖ = 1 := by
      rw [← Nat.cast_succ, ← zc_natCast, norm_zc, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq.out).2 hk
    rw [hk1, mul_one] at this
    exact this.trans_lt hq1
  refine ⟨hint, h2, fun hqq k a ha => ?_⟩
  have hv : Van (2 * q) (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    intro n hn
    by_cases hd : q ∣ n
    · obtain ⟨c, rfl⟩ := hd
      have hc2 : c < 2 := by
        by_contra h
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q (by omega)
        omega
      interval_cases c
      · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hB0]; simp
      · rwa [mul_one]
    · exact h2 n hd
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow a k).1 ha)
  clear ha
  show Van _ _
  induction k with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by simpa using hn
    rw [coeff_zero_eq_constantCoeff_apply, hB0]; simp
  | succ k ih =>
    have := van_subst hBq (hint _) (hB0 _) hv ih
    rw [hcomp, ← zc_natCast, ← zc_mul, ← pow_succ'] at this
    convert this using 5
    ring

end GlobalTheory.MomOne.FormalMul
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  atlas_forward_decl GlobalTheory.MomOne.FormalMul.padic_multiplications
end

section
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulDegree

section Lattice
open Module

set_option backward.isDefEq.respectTransparency false in

theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ ℂ) {L₁ L₂ : AddSubgroup ℂ}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem relIndex_mul (L : PeriodPair) (β : ℂ) (N : ℕ) (hβ : β ≠ 0) (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice)
    (hN : (N : ℂ) = β * conj β) :
    (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft β)).relIndex L.lattice.toAddSubgroup = N := by
  let f : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective (Algebra.lmul ℝ ℂ β)
    ⟨fun x y h => mul_left_cancel₀ hβ h, fun y => ⟨β⁻¹ * y, by simp [hβ]⟩⟩
  have hf : ∀ x, f x = β * x := fun _ => rfl
  have h := relIndex_eq_abs_det (L.basis.map f) L.basis
    (L₁ := L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft β)) (L₂ := L.lattice.toAddSubgroup) ?_
    (by rw [L.lattice_eq_span_range_basis]) (by rintro _ ⟨l, hl, rfl⟩; exact hL l hl)
  · have h2 : L.basis.det (L.basis.map f) = Complex.normSq β := by
      have := L.basis.det_comp (Algebra.lmul ℝ ℂ β) L.basis
      rw [Basis.det_self, mul_one, ← Algebra.norm_apply, Algebra.norm_complex_apply] at this
      exact this
    rw [h2, abs_of_nonneg (Complex.normSq_nonneg β)] at h
    rw [Complex.mul_conj] at hN
    have h3 : (N : ℝ) = Complex.normSq β := by exact_mod_cast hN
    exact_mod_cast h.trans h3.symm
  · ext x
    have e : Set.range (L.basis.map f) = (LinearMap.mulLeft ℤ β) '' Set.range L.basis := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, ← L.lattice_eq_span_range_basis]
    simp

theorem dvd_of_mem (L : PeriodPair) (K : ℕ) (hK : 0 < K) (m a b : ℤ)
    (h : (m : ℂ) / K * (a * L.ω₁ + b * L.ω₂) ∈ L.lattice) : (K : ℤ) ∣ m * a ∧ (K : ℤ) ∣ m * b := by
  obtain ⟨s, t, e⟩ := PeriodPair.mem_lattice.mp h
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have e' : (K : ℂ) * (s * L.ω₁ + t * L.ω₂) = m * (a * L.ω₁ + b * L.ω₂) := by
    rw [e]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep ((m * a - K * s : ℤ) : ℝ) ((m * b - K * t : ℤ) : ℝ)
    (by simp; linear_combination -e')
  obtain ⟨h1, h2⟩ := this
  have h1' : m * a - K * s = 0 := by exact_mod_cast h1
  have h2' : m * b - K * t = 0 := by exact_mod_cast h2
  exact ⟨⟨s, by linarith⟩, ⟨t, by linarith⟩⟩

theorem exists_points (L : PeriodPair) (β : ℂ) (hβ : β ≠ 0) (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice)
    (q n : ℕ) (hq : q.Prime) : ∃ (K : ℕ) (P : ℕ → ℂ), Nat.Coprime K q ∧ (∀ i, (K : ℂ) * P i ∈ L.lattice) ∧
      (∀ i < n, β * P i ∉ L.lattice) ∧
      ∀ i < n, ∀ j < n, i ≠ j → P i + P j ∉ L.lattice ∧ P i - P j ∉ L.lattice := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hL _ L.ω₁_mem_lattice)
  obtain ⟨K, hK, hKp⟩ := Nat.exists_infinite_primes (q + 2 * n + 2 + a.natAbs + b.natAbs + 1)
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hKp.pos.ne'
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have small : ∀ m : ℤ, (K : ℤ) ∣ m → m.natAbs < K → m = 0 := fun m h1 h2 =>
    Int.eq_zero_of_abs_lt_dvd h1 (by rw [Int.abs_eq_natAbs]; exact_mod_cast h2)
  have hp : Prime (K : ℤ) := Nat.prime_iff_prime_int.mp hKp
  have one : ∀ m : ℤ, m ≠ 0 → m.natAbs < K → (m : ℂ) / K * L.ω₁ ∉ L.lattice := fun m h0 h1 h => by
    have := (dvd_of_mem L K hKp.pos m 1 0 (by simpa using h)).1
    exact h0 (small m (by simpa using this) h1)
  refine ⟨K, fun i => ((i + 1 : ℤ) : ℂ) / K * L.ω₁, (Nat.coprime_primes hKp hq).mpr (by omega), fun i => ?_,
    fun i hi h => ?_, fun i hi j hj hij => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact PeriodPair.mem_lattice.mpr ⟨i + 1, 0, by simp only; field_simp; simp⟩
  · have := dvd_of_mem L K hKp.pos (i + 1) a b (by rw [hab]; convert h using 1; ring)
    have h0 : ¬ (K : ℤ) ∣ (i + 1) := fun h => by have := small _ h (by omega); omega
    have ha := small a ((hp.dvd_or_dvd this.1).resolve_left h0) (by omega)
    have hb := small b ((hp.dvd_or_dvd this.2).resolve_left h0) (by omega)
    rw [ha, hb] at hab
    exact mul_ne_zero hβ hω (by simpa using hab.symm)
  · refine one (i + 1 + (j + 1)) (by omega) (by omega) ?_
    convert h using 1; push_cast; ring
  · refine one (i + 1 - (j + 1)) (by omega) (by omega) ?_
    convert h using 1; push_cast; ring

end Lattice

variable {q : ℕ} [Fact q.Prime]

theorem exists_rational (M : Mdl q) (hc : M.c ≠ 0) (β : ℂ) (N : ℕ) (hβ : β ≠ 0)
    (hL : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) (hN : (N : ℂ) = β * conj β) :
    ∃ A D : Polynomial ℂ, A.natDegree ≤ N ∧ D.natDegree ≤ N ∧ ∀ z, β * z ∉ M.L.lattice →
      D.eval (M.x z) ≠ 0 ∧ M.x (β * z) * D.eval (M.x z) = A.eval (M.x z) := by
  obtain ⟨A, D, -, -, -, -, -, hA, hD, h0, h⟩ := GlobalTheory.exists_weierstrassP_mul_eq_div hβ hL ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  rw [relIndex_mul M.L β N hβ hL hN] at hA
  set r := M.ι.symm (M.W.b₂ / 12) with hr
  let T : Polynomial ℂ := Polynomial.C (M.c ^ 2) * Polynomial.X + Polynomial.C (M.c ^ 2 * r)
  have hT : T.natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hTe : ∀ z, T.eval (M.x z) = M.L.weierstrassP z := fun z => by
    simp only [T, Mdl.x, ← hr, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    field_simp; ring
  have hdA : (A.comp T).natDegree ≤ N := Polynomial.natDegree_comp_le.trans (by nlinarith)
  have hdD : (D.comp T).natDegree ≤ N := Polynomial.natDegree_comp_le.trans (by nlinarith)
  refine ⟨Polynomial.C (M.c ^ 2)⁻¹ * A.comp T - Polynomial.C r * D.comp T, D.comp T, ?_, hdD, fun z hz => ?_⟩
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_C_mul_le _ _).trans hdA)
      ((Polynomial.natDegree_C_mul_le _ _).trans hdD))
  · have hz' : z ∉ M.L.lattice := fun h => hz (hL z h)
    have hD0 : D.eval (M.L.weierstrassP z) ≠ 0 := fun e => hz ((h0 z hz').mp e)
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hTe]
    refine ⟨hD0, ?_⟩
    rw [Mdl.x, ← hr, h z hz]
    field_simp

theorem norm_sub_le_of {x y : ℂ_[q]} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x - y‖ ≤ B := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg, ← sub_eq_add_neg] at this
  exact this.trans (max_le hx hy)

theorem norm_add_le_of {x y : ℂ_[q]} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem coeff_le_of_values (B : ℝ) (hB : 0 ≤ B) (p : ℕ → ℂ_[q]) : ∀ (n : ℕ) (A : Polynomial ℂ_[q]), A.degree < n →
    (∀ i < n, ‖p i‖ ≤ 1) → (∀ i < n, ∀ j < n, i ≠ j → ‖p i - p j‖ = 1) → (∀ i < n, ‖A.eval (p i)‖ ≤ B) →
    ∀ k, ‖A.coeff k‖ ≤ B := by
  intro n
  induction n with
  | zero =>
    intro A hA _ _ _ k
    have : A = 0 := by
      by_contra h
      rw [Polynomial.degree_eq_natDegree h] at hA
      simp at hA
    simpa [this] using hB
  | succ n ih =>
    intro A hA h1 h2 h3 k
    by_cases h0 : A = 0
    · simpa [h0] using hB
    set A₁ := A /ₘ (Polynomial.X - Polynomial.C (p n)) with hA₁
    have e : A = Polynomial.C (A.eval (p n)) + (Polynomial.X - Polynomial.C (p n)) * A₁ := by
      rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval, hA₁, Polynomial.modByMonic_add_div]
    have hd : A₁.degree < n := by
      have h4 := Polynomial.degree_divByMonic_lt A (Polynomial.X - Polynomial.C (p n)) h0 (by simp)
      rw [Polynomial.degree_eq_natDegree h0] at hA h4
      have h5 : A.natDegree < n + 1 := by exact_mod_cast hA
      exact h4.trans_le (by exact_mod_cast Nat.lt_succ_iff.mp h5)
    have hc := ih A₁ hd (fun i hi => h1 i (by omega)) (fun i hi j hj => h2 i (by omega) j (by omega)) (fun i hi => by
      have e2 : (p i - p n) * A₁.eval (p i) = A.eval (p i) - A.eval (p n) := by
        conv_rhs => enter [1]; rw [e]
        simp
      have := norm_sub_le_of (h3 i (by omega)) (h3 n (by omega))
      rwa [← e2, norm_mul, h2 i (by omega) n (by omega) (by omega), one_mul] at this)
    rw [e, Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    refine norm_add_le_of ?_ (norm_sub_le_of ?_ ?_)
    · rw [Polynomial.coeff_C]; split_ifs
      · exact h3 n (by omega)
      · simpa using hB
    · cases k with
      | zero => simpa using hB
      | succ k => rw [Polynomial.coeff_X_mul]; exact hc k
    · rw [norm_mul]
      calc _ ≤ 1 * B := mul_le_mul (h1 n (by omega)) (hc k) (norm_nonneg _) zero_le_one
        _ = B := one_mul B

def BdT (n : ℕ) (B : ℝ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ m < n, ‖coeff m f‖ ≤ B

theorem BdT.mul {n : ℕ} {A B : ℝ} {f g : ℂ_[q]⟦X⟧} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : BdT n A f) (hg : BdT n B g) :
    BdT n (A * B) (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  rw [norm_mul]
  exact mul_le_mul (hf _ (by omega)) (hg _ (by omega)) (norm_nonneg _) hA

theorem BdT.mul_one {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n 1 f) (hg : BdT n 1 g) : BdT n 1 (f * g) := by
  simpa using BdT.mul zero_le_one zero_le_one hf hg

theorem BdT.add {n : ℕ} {B : ℝ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n B f) (hg : BdT n B g) : BdT n B (f + g) :=
  fun m hm => by rw [map_add]; exact norm_add_le_of (hf m hm) (hg m hm)

theorem BdT.const {n : ℕ} {a : ℂ_[q]} (ha : ‖a‖ ≤ 1) : BdT n 1 (C a) := fun m _ => by
  rw [coeff_C]; split_ifs <;> simp [ha]

theorem BdT.of_bd {n : ℕ} {B : ℝ} {f : ℂ_[q]⟦X⟧} (hf : Bd B f) : BdT n B f := fun m _ => hf m

theorem BdT.sq {n : ℕ} {r : ℝ} {f : ℂ_[q]⟦X⟧} (hr : 0 ≤ r) (h1 : Bd 1 f) (hf : BdT n r f) :
    BdT (2 * n) r (f * f) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  rw [norm_mul]
  by_cases h : p.1 < n
  · simpa using mul_le_mul (hf _ h) (h1 p.2) (norm_nonneg _) hr
  · simpa using mul_le_mul (h1 p.1) (hf p.2 (by omega)) (norm_nonneg _) zero_le_one

theorem BdT.mul_succ {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n 1 f) (hg : BdT n 1 g) (hf0 : constantCoeff f = 0)
    (hg0 : constantCoeff g = 0) : BdT (n + 1) 1 (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  by_cases h1 : p.1 = 0
  · simp [h1, hf0]
  by_cases h2 : p.2 = 0
  · simp [h2, hg0]
  rw [norm_mul]
  exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))

theorem exists_cube (b w : ℂ_[q]⟦X⟧) (a₁ a₂ a₃ a₄ a₆ : ℂ_[q]) (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hb : Bd 1 b) (hb0 : constantCoeff b = 0) (hw0 : constantCoeff w = 0)
    (e : w = b * b * b + w * (C a₁ * b + C a₂ * (b * b) + C a₃ * w + C a₄ * (b * w) + C a₆ * (w * w))) :
    ∃ v, Bd 1 v ∧ w = b * b * b * v := by
  set Q := C a₁ * b + C a₂ * (b * b) + C a₃ * w + C a₄ * (b * w) + C a₆ * (w * w) with hQ
  have hQ0 : constantCoeff Q = 0 := by simp [hQ, hb0, hw0]
  have hQb : ∀ n, BdT n 1 w → BdT n 1 Q := fun n hw =>
    ((((((BdT.const h₁).mul_one (.of_bd hb)).add ((BdT.const h₂).mul_one ((BdT.of_bd hb).mul_one (.of_bd hb)))).add
      ((BdT.const h₃).mul_one hw)).add ((BdT.const h₄).mul_one ((BdT.of_bd hb).mul_one hw))).add
      ((BdT.const h₆).mul_one (hw.mul_one hw)))
  have hw : ∀ n, BdT n 1 w := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      rw [e]
      exact (((BdT.of_bd hb).mul_one (.of_bd hb)).mul_one (.of_bd hb)).add (ih.mul_succ (hQb n ih) hw0 hQ0)
  have h1 : Bd 1 (1 - Q) := fun m => by
    rw [map_sub]
    refine norm_sub_le_of ?_ (hQb (m + 1) (hw _) m (by omega))
    rw [coeff_one]; split_ifs <;> simp
  have h0 : constantCoeff (1 - Q) = 1 := by simp [hQ0]
  have hi : (1 - Q) * (1 - Q)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero)
  refine ⟨(1 - Q)⁻¹, (GlobalTheory.MomOne.sup_norm_laws q).2.2.1 _ _ h1 (by rw [h0]; simp) hi, ?_⟩
  linear_combination (1 - Q)⁻¹ * e - w * hi

theorem norm_le_of_bdT (xs : ℂ_[q]⟦X⟧) (k : ℕ) (c : ℕ → ℂ_[q]) (B : ℝ) (hx : Bd 1 xs) (h0 : ‖constantCoeff xs‖ = 1)
    (hB : BdT (2 * k + 1) B (∑ i ∈ Finset.range (k + 1), C (c i) * X ^ (2 * (k - i)) * xs ^ i)) :
    ∀ i ≤ k, ‖c i‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega))
  suffices h : ∀ n, ∀ j ≤ k, k - j = n → ‖c j‖ ≤ B from fun j hj => h _ j hj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj hn
    have h1 := hB (2 * n) (by omega)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)), map_add, map_sum, mul_assoc,
      coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), hn, Nat.sub_self, coeff_zero_eq_constantCoeff] at h1
    have h2 : ‖∑ l ∈ (Finset.range (k + 1)).erase j, coeff (2 * n) (C (c l) * X ^ (2 * (k - l)) * xs ^ l)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 ?_
      intro l hl
      obtain ⟨hlj, hls⟩ := Finset.mem_erase.mp hl
      have hls' := Finset.mem_range.mp hls
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      split_ifs with hle
      · rw [norm_mul]
        simpa using mul_le_mul (ih (k - l) (by omega) l (by omega) rfl) (Triang.bd_one_pow hx l _) (norm_nonneg _) hB0
      · simpa using hB0
    have h3 := norm_sub_le_of h1 h2
    rwa [add_sub_cancel_right, norm_mul, map_pow, norm_pow, h0, one_pow, mul_one] at h3

theorem bd_sum (xs : ℂ_[q]⟦X⟧) (k : ℕ) (c : ℕ → ℂ_[q]) (B : ℝ) (hB : 0 ≤ B) (hx : Bd 1 xs) (hc : ∀ i, ‖c i‖ ≤ B) :
    Bd B (∑ i ∈ Finset.range (k + 1), C (c i) * X ^ (2 * (k - i)) * xs ^ i) := by
  intro m
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB ?_
  intro l _
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hle
  · rw [norm_mul]
    simpa using mul_le_mul (hc l) (Triang.bd_one_pow hx l _) (norm_nonneg _) hB
  · simpa using hB

theorem hat_equation (M : Mdl q) (hM : M.Ok) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    let b := hat M.ι ℓ M.u
    let w := hat M.ι ℓ M.w
    w = b * b * b + w * (C M.W.a₁ * b + C M.W.a₂ * (b * b) + C M.W.a₃ * w + C M.W.a₄ * (b * w) +
      C M.W.a₆ * (w * w)) := by
  intro b w
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hM
  obtain ⟨hu, hw, -, -, -, he⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨H, hc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  have hadd := fun F G hF hG => (H F G hF hG).1
  have hmul := fun F G hF hG => (H F G hF hG).2.1
  have h1 := (H M.w (fun z => M.u z * M.u z * M.u z + M.w z * (M.ι.symm M.W.a₁ * M.u z +
    M.ι.symm M.W.a₂ * (M.u z * M.u z) + M.ι.symm M.W.a₃ * M.w z + M.ι.symm M.W.a₄ * (M.u z * M.w z) +
    M.ι.symm M.W.a₆ * (M.w z * M.w z))) hw (by fun_prop)).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds he] with z hz
      linear_combination hz.1)
  simp (disch := fun_prop) only [hadd, hmul, hc, RingEquiv.apply_symm_apply] at h1
  exact h1

theorem exists_unit_coeff : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (β : ℂ) (N : ℕ), M.Chart ℓ → β ≠ 0 → (∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) → (N : ℂ) = β * conj β → Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) → ∃ n ≤ N, ‖coeff n (hat M.ι ℓ (fun z => M.u (β * z)))‖ = 1 := by
  intro q hq M ℓ β N hch hβ hL hN hb
  by_contra hcon
  push Not at hcon
  have hM := hch.1
  have hℓ := hch.2.1
  obtain ⟨hc, h₁, h₂, h₃, h₄, h₆, -⟩ := id hM
  obtain ⟨A, D, hA, hD, hAD⟩ := exists_rational M hc β N hβ hL hN
  obtain ⟨hℓ1, v, xs, ys, -, hxs, -, -, hxs0, -, -, -, -, hxy⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hch
  obtain ⟨-, -, -, -, hu0, hw0, hu', -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hM
  obtain ⟨hu, hw, -, -, hev, -⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, -, -, hsc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  have hℓ' : constantCoeff (C (M.ι β) * ℓ) = 0 := by simp [hℓ]
  obtain ⟨H', hc', -, hcc', -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hℓ'

  have hub : AnalyticAt ℂ (fun z => M.u (β * z)) 0 :=
    AnalyticAt.comp (g := M.u) (f := fun z => β * z) (by simpa using hu) (by fun_prop)
  have hwb : AnalyticAt ℂ (fun z => M.w (β * z)) 0 :=
    AnalyticAt.comp (g := M.w) (f := fun z => β * z) (by simpa using hw) (by fun_prop)
  have ht : Filter.Tendsto (fun z : ℂ => β * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Filter.Tendsto (fun z : ℂ => β * z) (𝓝 0) (𝓝 (β * 0)) := (by fun_prop : Continuous _).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_ne_zero hβ hz
  have key := hxy _ A 0 N hub hA (by simp) _ hwb D N hD (by
    filter_upwards [ht.eventually hev] with z hz
    have := (hAD z hz.1).2
    simp only [Polynomial.eval_zero, zero_mul, add_zero]
    rw [← this, ← hz.2.2.1]; ring)
  rw [hsc _ β hu] at hb hcon key
  rw [hsc _ β hw] at key
  set b := hat M.ι (C (M.ι β) * ℓ) M.u with hbdef
  set w := hat M.ι (C (M.ι β) * ℓ) M.w with hwdef
  obtain ⟨e, he, hwe⟩ := exists_cube b w _ _ _ _ _ h₁ h₂ h₃ h₄ h₆ hb (by rw [hbdef, hcc', hu0, map_zero])
    (by rw [hwdef, hcc', hw0, map_zero]) (hat_equation M hM _ hℓ')
  have hb0 : b ≠ 0 := fun h0 => by
    have := (H' M.u (fun _ => 0) hu (by fun_prop)).2.2.2 (by simp [hβ, hℓ1]) (by rw [hc', ← hbdef, h0]; simp)
    have := this.deriv_eq
    rw [hu'] at this
    exact hc (by simpa using this)
  set Dh := ∑ i ∈ Finset.range (N + 1), C (M.ι (D.coeff i)) * X ^ (2 * (N - i)) * xs ^ i with hDh
  set Ah := ∑ i ∈ Finset.range (N + 1), C (M.ι (A.coeff i)) * X ^ (2 * (N - i)) * xs ^ i with hAh
  have hsum : ∑ i ∈ Finset.range (N + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (N - i) + 3) * xs ^ i +
      C (M.ι ((0 : Polynomial ℂ).coeff i)) * X ^ (2 * (N - i)) * xs ^ i * ys) = X ^ 3 * Ah := by
    rw [hAh, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.coeff_zero, map_zero, zero_mul, add_zero]
    ring
  rw [hsum, hwe] at key
  have key2 : Dh = b * b * (e * Ah) := by
    refine mul_left_cancel₀ (mul_ne_zero hb0 (pow_ne_zero (2 * N + 3) X_ne_zero)) ?_
    rw [key]; ring

  obtain ⟨n, hn, hnmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun n => ‖coeff n b‖) (by simp)
  have hr : ‖coeff n b‖ < 1 := lt_of_le_of_ne (hb n) (hcon n (by simpa [Nat.lt_succ_iff] using hn))
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun n => ‖M.ι (D.coeff n)‖) (by simp)
  have hDc : ∀ i, ‖M.ι (D.coeff i)‖ ≤ ‖M.ι (D.coeff m)‖ := fun i => by
    by_cases hi : i ≤ N
    · exact hmmax i (by simpa [Nat.lt_succ_iff] using hi)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

  obtain ⟨K, P, hK, hKP, hβP, hPP⟩ := exists_points M.L β hβ hL q (N + 1) hq.out
  obtain ⟨hint, hdist⟩ := GlobalTheory.MomOne.TorsionReduction.torsion_integral_and_distinct q M K hM hK
  have hP : ∀ i < N + 1, P i ∉ M.L.lattice := fun i hi h => hβP i hi (hL _ h)
  have hAc : ∀ i, ‖M.ι (A.coeff i)‖ ≤ ‖M.ι (D.coeff m)‖ := by
    have := coeff_le_of_values ‖M.ι (D.coeff m)‖ (norm_nonneg _) (fun i => M.ι (M.x (P i))) (N + 1)
      (A.map (M.ι : ℂ →+* ℂ_[q]))
      (Polynomial.degree_map_le.trans_lt (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast by omega)))
      (fun i hi => hint _ (hKP i) (hP i hi))
      (fun i hi j hj hij => hdist _ _ (hKP i) (hKP j) (hP i hi) (hP j hj) (hPP i hi j hj hij).1 (hPP i hi j hj hij).2)
      (fun i hi => ?_)
    · simpa using this
    · have e1 : (A.map (M.ι : ℂ →+* ℂ_[q])).eval (M.ι (M.x (P i))) = M.ι (A.eval (M.x (P i))) :=
        Polynomial.eval_map_apply (p := A) (M.ι : ℂ →+* ℂ_[q]) (M.x (P i))
      rw [e1, ← (hAD _ (hβP i hi)).2, map_mul, norm_mul]
      have e2 : ‖M.ι (M.x (β * P i))‖ ≤ 1 := hint _ (by rw [mul_left_comm]; exact hL _ (hKP i)) (hβP i hi)
      have e3 : ‖M.ι (D.eval (M.x (P i)))‖ ≤ ‖M.ι (D.coeff m)‖ := by
        rw [Polynomial.eval_eq_sum_range, map_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
        rw [map_mul, map_pow, norm_mul, norm_pow]
        simpa using mul_le_mul (hDc l) (pow_le_one₀ (norm_nonneg _) (hint _ (hKP i) (hP i hi)) (n := l))
          (by positivity) (norm_nonneg _)
      simpa using mul_le_mul e2 e3 (norm_nonneg _) zero_le_one
  have hAh' : Bd ‖M.ι (D.coeff m)‖ Ah := bd_sum xs N _ _ (norm_nonneg _) hxs hAc
  have hbb : BdT (2 * (N + 1)) ‖coeff n b‖ (b * b) :=
    BdT.sq (norm_nonneg _) hb fun i hi => hnmax i (by simpa using hi)
  have hfin := hbb.mul (norm_nonneg _) (by positivity)
    ((BdT.of_bd he).mul zero_le_one (norm_nonneg _) (BdT.of_bd hAh'))
  rw [← key2, one_mul] at hfin
  have h5 := norm_le_of_bdT xs N (fun i => M.ι (D.coeff i)) _ hxs hxs0 (fun i hi => hfin i (by omega)) m
    (by simpa [Nat.lt_succ_iff] using hm)
  have h6 : ‖M.ι (D.coeff m)‖ ≤ 0 := by nlinarith [norm_nonneg (M.ι (D.coeff m))]
  have hD0 : D = 0 := by
    ext i
    simpa using (hDc i).trans h6
  exact (hAD _ (hβP 0 (by omega))).1 (by simp [hD0])

end GlobalTheory.MomOne.MulDegree
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coeff_mul_series_le_norm : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (β : ℂ) (N : ℕ), M.Chart ℓ → β ≠ 0 → (∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) → (N : ℂ) = β * conj β → Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) → ∃ n ≤ N, ‖coeff n (hat M.ι ℓ (fun z => M.u (β * z)))‖ = 1 := by
  atlas_forward_decl GlobalTheory.MomOne.MulDegree.exists_unit_coeff
end

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end
