import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

private lemma u1_apply_eq_mul_u1_one (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω G z = G (z + ω) * U1 Λ ω (fun _ => (1 : ℂ)) z := by
  simp only [U1, one_mul]

private lemma u1_one_ne_zero (ω z : ℂ) : U1 Λ ω (fun _ => (1 : ℂ)) z ≠ 0 := by
  simp only [U1, one_mul]
  exact Complex.exp_ne_zero _

private lemma u1_one_add_mul_comm_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ a (fun _ => (1 : ℂ)) z * U1 Λ b (fun _ => (1 : ℂ)) (z + a) *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) := by
  simp only [U1, one_mul, ← Complex.exp_add]
  congr 1
  ring

private lemma u1_one_add_mul_eq_u1_one_add_mul_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ (a + b) (fun _ => (1 : ℂ)) z *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
  simp only [U1, one_mul, ← Complex.exp_add, map_add]
  congr 1
  ring

private lemma cexp_pi_mul_conj_sub_div_area_eq_one_of_mem (hΛ : IsLat Λ) {a b : ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) = 1 := by
  obtain ⟨z0, hz0⟩ := hΛ.dense_compl.nonempty
  have hs0 : sgStar Λ z0 ≠ 0 := fun h0 => hz0 ((hΛ.sg_eq_zero z0).1 h0)
  have hsq : ∀ c : ℂ, (if c / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro c
    split_ifs <;> norm_num
  have l1 := hΛ.sg_law (add_mem ha hb) z0
  have l2 := hΛ.sg_law ha (z0 + b)
  have l3 := hΛ.sg_law hb z0
  rw [u1_apply_eq_mul_u1_one] at l1 l2 l3
  have key : (if (a + b) / 2 ∈ Λ then (1 : ℂ) else -1) *
      Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) =
      (if a / 2 ∈ Λ then (1 : ℂ) else -1) * (if b / 2 ∈ Λ then (1 : ℂ) else -1) := by
    apply mul_right_cancel₀ hs0
    calc _ = sgStar Λ (z0 + (a + b)) * U1 Λ (a + b) (fun _ => (1 : ℂ)) z0 *
          Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
          rw [l1]; ring
      _ = sgStar Λ (z0 + b + a) * (U1 Λ a (fun _ => (1 : ℂ)) (z0 + b) * U1 Λ b (fun _ => (1 : ℂ)) z0) := by
          rw [u1_one_add_mul_eq_u1_one_add_mul_cexp, show z0 + b + a = z0 + (a + b) by ring]; ring
      _ = _ := by rw [← mul_assoc, l2, mul_assoc, l3]; ring
  have h2 : Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) /
      (2 * (area Λ : ℂ))) ^ 2 = 1 := by
    have := congrArg (· ^ 2) key
    simp only [mul_pow, hsq, one_mul] at this
    exact this
  rw [show (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ) =
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) +
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) by ring,
    Complex.exp_add, ← sq, h2]

theorem ratio_pow_add (hΛ : IsLat Λ) {t : ℂ} {N : ℕ} (hN : 0 < N) (ht : (N : ℂ) * t ∈ Λ)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    (U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l)) ^ N = (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
  by_cases hz : z ∈ Λ
  · have h1 : sgStar Λ z = 0 := (hΛ.sg_eq_zero z).2 hz
    have h2 : sgStar Λ (z + l) = 0 := (hΛ.sg_eq_zero _).2 (add_mem hz hl)
    rw [h1, h2, div_zero, div_zero]
  · have hs : sgStar Λ z ≠ 0 := fun h0 => hz ((hΛ.sg_eq_zero z).1 h0)
    have hzl : z + l ∉ Λ := fun h' => hz (by simpa using sub_mem h' hl)
    have hsl : sgStar Λ (z + l) ≠ 0 := fun h0 => hzl ((hΛ.sg_eq_zero _).1 h0)
    have hsn : (if l / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have la := hΛ.sg_law hl (z + t)
    have lb := hΛ.sg_law hl z
    rw [u1_apply_eq_mul_u1_one] at la lb
    have hK := u1_one_add_mul_comm_cexp (Λ := Λ) t l z
    have e3 := u1_one_ne_zero (Λ := Λ) l z
    have e4 := u1_one_ne_zero (Λ := Λ) l (z + t)
    have hA : sgStar Λ (z + l + t) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ (z + t) /
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) := by
      rw [eq_div_iff e4, show z + l + t = z + t + l by ring]
      exact la
    have hB : sgStar Λ (z + l) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ z /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact lb
    have hF : U1 Λ t (fun _ => (1 : ℂ)) (z + l) = U1 Λ t (fun _ => (1 : ℂ)) z *
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact hK
    have hbase : U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l) = U1 Λ t (sgStar Λ) z / sgStar Λ z *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) := by
      rw [u1_apply_eq_mul_u1_one, u1_apply_eq_mul_u1_one t (sgStar Λ) z, hA, hF, hB]
      field_simp
    rw [hbase, mul_pow, ← Complex.exp_nat_mul,
      show (N : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) =
        (Real.pi : ℂ) * ((N : ℂ) * t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) ((N : ℂ) * t)) / (area Λ : ℂ) by
        rw [map_mul, map_natCast]; ring,
      cexp_pi_mul_conj_sub_div_area_eq_one_of_mem hΛ ht hl, mul_one]

theorem sqThD_eq (hΛ : IsLat Λ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {v z : ℂ}
    (hv : v ∉ Λ) (hz : z ∉ Λ) : sqThD Λ v z = sgStar Λ z ^ 3 * L.derivWeierstrassP z := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hzL : z ∉ L.lattice := fun hz' => hz ((h z).2 hz')
  have hev : sqTh Λ v =ᶠ[𝓝 z] fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v) := by
    filter_upwards [hU.mem_nhds hzL] with w hw
    have hwΛ : w ∉ Λ := fun h' => hw ((h w).1 h')
    rw [hΛ.sqTh_eq hv hwΛ, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  have hsg : HasDerivAt (sgStar Λ) (deriv (sgStar Λ) z) z := (hΛ.differentiable z).hasDerivAt
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    have hd : DifferentiableAt ℂ L.weierstrassP z :=
      (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
    have := hd.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hD : HasDerivAt (fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)) _ z :=
    (hsg.pow 2).mul (hwp.sub_const (L.weierstrassP v))
  unfold sqThD
  rw [hev.deriv_eq, hD.deriv, hΛ.sqTh_eq hv hz,
    GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  norm_num
  ring

theorem exists_decomp : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ t N hN ht v hv
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hσ0 : ∀ w, sgStar Λ w = 0 ↔ w ∈ Λ := hΛ.sg_eq_zero
  have hU : Differentiable ℂ (U1 Λ t (sgStar Λ)) := by
    unfold U1
    fun_prop
  have hmer : Meromorphic (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) := fun x =>
    ((hU.analyticAt x).meromorphicAt.div (hσ.analyticAt x).meromorphicAt).pow N
  have hcont : ∀ a, a ∉ Λ → ContinuousAt (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) a :=
    fun a ha => ((hU a).continuousAt.div (hσ a).continuousAt (fun h0 => ha ((hσ0 a).1 h0))).pow N
  have hd : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (𝓝[≠] a) (𝓝 c) :=
    fun a ha => ⟨_, (hcont a (fun h' => ha ((hL a).1 h'))).tendsto.mono_left nhdsWithin_le_nhds⟩
  have hp : ∀ z, ∀ l ∈ L.lattice, (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (z + l) =
      (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) z :=
    fun z l hl => ratio_pow_add hΛ hN ht z ((hL l).2 hl)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L hmer hd hp
  have hpt : ∀ z, z ∉ Λ → (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hzΛ
    have hz : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have t1 := (hcont z hzΛ).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hc2 : ContinuousAt (fun w => A.eval (L.weierstrassP w) + B.eval (L.weierstrassP w) * L.derivWeierstrassP w) z :=
      (A.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).add
        ((B.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).mul
          (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt)
    exact tendsto_nhds_unique (t1.congr' (hAB z)) (hc2.tendsto.mono_left nhdsWithin_le_nhds)
  have hS : Differentiable ℂ (sqTh Λ v) := hΛ.differentiable_sqTh v
  have hdS : Continuous (deriv (sqTh Λ v)) := (hS.contDiff (n := 1)).continuous_deriv le_rfl
  have hdσ : Continuous (deriv (sgStar Λ)) := (hσ.contDiff (n := 1)).continuous_deriv le_rfl
  have hT : Continuous (sqThD Λ v) := by
    unfold sqThD
    exact (hσ.continuous.mul hdS).sub ((continuous_const.mul hdσ).mul hS.continuous)
  set P := A.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hP
  set Q := B.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hQ
  refine ⟨max (max P.natDegree Q.natDegree) N, fun i => P.coeff i, fun j => Q.coeff j, ?_, ?_⟩
  · have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  have hIP : P.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_left P.natDegree Q.natDegree
    omega
  have hIQ : Q.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_right P.natDegree Q.natDegree
    omega
  have hNI : N ≤ 2 * max (max P.natDegree Q.natDegree) N + 3 := by
    have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  generalize max (max P.natDegree Q.natDegree) N = I at hIP hIQ hNI ⊢
  have heq : (fun z => sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N) =
      fun z => ∑ i ∈ Finset.range (I + 1), P.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), Q.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
    refine Continuous.ext_on hΛ.dense_compl ((hσ.continuous.pow _).mul (hU.continuous.pow _))
      ((continuous_finsetSum _ fun i _ => continuous_const.mul ((hσ.continuous.pow _).mul (hS.continuous.pow _))).add
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (((hσ.continuous.pow _).mul (hS.continuous.pow _)).mul hT))) ?_
    intro z hz
    have hzΛ : z ∉ Λ := hz
    have hs : sgStar Λ z ≠ 0 := fun h0 => hzΛ ((hσ0 z).1 h0)
    have hz' : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have hq := hpt z hzΛ
    have hApt : A.eval (L.weierstrassP z) = P.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hP, Polynomial.eval_comp]; simp
    have hBpt : B.eval (L.weierstrassP z) = Q.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hQ, Polynomial.eval_comp]; simp
    rw [hApt, hBpt, Polynomial.eval_eq_sum_range' hIP, Polynomial.eval_eq_sum_range' hIQ] at hq
    have hUN : U1 Λ t (sgStar Λ) z ^ N = sgStar Λ z ^ N * (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
    simp only
    rw [hUN, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hNI, hq,
      sqThD_eq hΛ L hL hv hzΛ, hΛ.sqTh_eq hv hzΛ, GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL,
      mul_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = (2 * (I - i) + 3) + 2 * i by omega]
      ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = 2 * (I - j) + 2 * j + 3 by omega]
      ring
  intro z
  exact congrFun heq z

end GlobalTheory.ThetaTranslDecomp
end
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  first | exact @GlobalTheory.ThetaTranslDecomp.exists_decomp | exact GlobalTheory.ThetaTranslDecomp.exists_decomp | (intros; apply GlobalTheory.ThetaTranslDecomp.exists_decomp <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

noncomputable section

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) : coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · have h := (hF.1.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = derivative ℂ_[p] (GL3Theta.ser1 lam F) := by
  ext n
  rw [coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, taylorCoeffAtZero_deriv]
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  rw [ha]
  have e : ((n : ℂ) + 1) * (a (n + 1) : ℂ) = ((((n : Qbar) + 1) * a (n + 1) : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul, map_add, map_natCast, map_one,
    mul_comm]

theorem atU_deriv (g : GL3Theta.G1 p) {F : ℂ → ℂ} (hF : AlgEnt F) :
    derivative ℂ_[p] (g.atU F) =
      g.atU (deriv F) * (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * derivative ℂ_[p] g.l) := by
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, derivative_subst hs, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem bddSer_derivative {f : PowerSeries ℂ_[p]} (hf : BddSer f) : BddSer (derivative ℂ_[p] f) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  rw [coeff_derivative, norm_mul]
  have h1 : ‖((n : ℂ_[p]) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  calc _ ≤ B * 1 := mul_le_mul (hB _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = B := mul_one B

end GlobalTheory.ThetaTransl.CubeSer

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem sqThD_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  intro p _ g hOk hL h2 h3 hd hσ v hv hw
  obtain ⟨-, hwi, -, -, hA⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hOk hL h2 h3 hd
  have hq : IsWq g.W g.wq := hOk.2.1
  obtain ⟨hS, hB⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hmul, hconst, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨i1, i2, i3, i4, i6, -⟩ := hOk.1
  obtain ⟨vI, hvI, hvl⟩ := PI.JetsPhW.Inv.inverse_omega_holds p g.W g.wq i1 i2 i3 i4 i6 hq
  rw [PI.JetsPhW.Inv.dX_eq_derivative] at hvl
  change vI * derivative ℂ_[p] g.l = 1 at hvl
  have hσd := algEnt_deriv hσ
  have hSd := algEnt_deriv hS
  have hm2 : (((-2 : Qbar)) : ℂ) = -2 := by push_cast; rfl
  have hc := hconst (((-2 : Qbar)) : ℂ) (-2 : Qbar).2
  have hl2 : lamC g.lam (((-2 : Qbar)) : ℂ) = -2 := by
    rw [GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  have k1 := (hmul (sgStar g.abelian₂) (deriv (sqTh g.abelian₂ v)) hσ hSd).1
  have k2 := (hmul (deriv (sgStar g.abelian₂)) (sqTh g.abelian₂ v) hσd hS).1
  have k3 := (hmul (fun _ => (((-2 : Qbar)) : ℂ)) (fun z => deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)
    hc.1 k2.1).1
  have k4 := (hmul (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z)
    (fun z => (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) k1.1 k3.1).2
  have hT : sqThD g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z) := by
    funext z
    rw [hm2]
    simp only [sqThD]
    ring
  refine ⟨hT ▸ k4.1, ?_⟩
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  set L := lineSer g.wq⁻¹ (xAt g v) with hL'
  obtain ⟨-, hbdd, hCb, hX, -⟩ := SerRing.series_ring_laws p
  refine ⟨vI * (X * derivative ℂ_[p] L - 2 * L), ?_, ?_⟩
  · have hX2 : BddSer (X ^ 2 : PowerSeries ℂ_[p]) := by
      rw [pow_two]; exact (hbdd _ _ ⟨1, hX⟩ ⟨1, hX⟩).2.2
    have hLb : BddSer L := by
      rw [hL', lineSer]; exact (hbdd _ _ ⟨1, hwi⟩ (hbdd _ _ (hCb _).1 hX2).2.2).2.1
    have h2b : BddSer (2 : PowerSeries ℂ_[p]) := by
      rw [show (2 : PowerSeries ℂ_[p]) = C 2 from (map_ofNat C 2).symm]; exact (hCb 2).1
    refine (hbdd _ _ ⟨1, fun n => hvI n⟩ (hbdd _ _ ((hbdd _ _ ⟨1, hX⟩ (bddSer_derivative hLb)).2.2)
      ((hbdd _ _ h2b hLb).2.2)).2.1).2.2
  · have dA := atU_deriv g hσ
    have dB := atU_deriv g hS
    rw [hA] at dA
    rw [hB] at dB
    have hDA : derivative ℂ_[p] (C ε * X * e) = C ε * (e + X * derivative ℂ_[p] e) := by
      simp only [Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul]
      ring
    have hDB : derivative ℂ_[p] (e ^ 2 * L) =
        2 * e * derivative ℂ_[p] e * L + e ^ 2 * derivative ℂ_[p] L := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hDA] at dA
    rw [hDB] at dB
    have F4 : C ε * C ε⁻¹ = (1 : PowerSeries ℂ_[p]) := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero _), map_one]
    set a1 := g.atU (deriv (sgStar g.abelian₂))
    set b1 := g.atU (deriv (sqTh g.abelian₂ v))
    set x := C ε
    set y := C ε⁻¹
    set l' := derivative ℂ_[p] g.l
    set E' := derivative ℂ_[p] e
    set L'' := derivative ℂ_[p] L
    have ha1 : a1 = (e + X * E') * vI := by
      linear_combination (-a1) * F4 + (-a1 * x * y) * hvl + (-y * vI) * dA + ((e + X * E') * vI) * F4
    have hb1 : b1 = y * (2 * e * E' * L + e ^ 2 * L'') * vI := by
      linear_combination (-b1) * F4 + (-b1 * x * y) * hvl + (-y * vI) * dB
    have hT' : g.atU (sqThD g.abelian₂ v) = x * X * e * b1 + C (-2) * (a1 * (e ^ 2 * L)) := by
      rw [← hA, ← hB, ← hl2]
      calc g.atU (sqThD g.abelian₂ v) = g.atU (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
            (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) := by rw [← hT]
        _ = _ := by rw [k4.2, k1.2, k3.2, k2.2, hc.2]
    rw [hT', show (C (-2) : PowerSeries ℂ_[p]) = -2 by rw [map_neg, map_ofNat]]
    linear_combination (x * X * e) * hb1 - (2 * e ^ 2 * L) * ha1 +
      (X * e * (2 * e * E' * L + e ^ 2 * L'') * vI) * F4

end GlobalTheory.ThetaTransl.CubeSer
end
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  first | exact @GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | exact GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | (intros; apply GlobalTheory.ThetaTransl.CubeSer.sqThD_atU <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1
    rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n
    rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]
  simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  first | exact @GlobalTheory.TranslLin.transl_lin | exact GlobalTheory.TranslLin.transl_lin | (intros; apply GlobalTheory.TranslLin.transl_lin <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl
open GlobalTheory.EvenTheta

variable {p : ℕ} [Fact p.Prime]

def GoodAt (g : GL3Theta.G1 p) (k : ℕ) (F : ℂ → ℂ) : Prop :=
  AlgEnt F ∧ ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU F = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B

theorem bdd_mul {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f * h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2

theorem bdd_add {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f + h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1

theorem bdd_sub {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f - h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1

theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1

theorem bdd_X : BddSer (PowerSeries.X : PowerSeries ℂ_[p]) :=
  ⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩

theorem bdd_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ_[p]) (h : ∀ i ∈ s, BddSer (f i)) :
    BddSer (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  have h : (1 : ℂ) ∈ Qbar := one_mem _
  rw [lamC, dif_pos h]
  exact map_one lam

theorem good_mul {g : GL3Theta.G1 p} {k l : ℕ} {F G : ℂ → ℂ} (hF : GoodAt g k F) (hG : GoodAt g l G) :
    GoodAt g (k + l) (fun z => F z * G z) := by
  obtain ⟨hFa, B, hB, hFe⟩ := hF
  obtain ⟨hGa, B', hB', hGe⟩ := hG
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1
  refine ⟨ha, B * B', bdd_mul hB hB', ?_⟩
  rw [he, hFe, hGe, pow_add]
  ring

theorem good_one (g : GL3Theta.G1 p) : GoodAt g 0 (fun _ => (1 : ℂ)) := by
  obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
  refine ⟨ha, 1, ?_, ?_⟩
  · simpa using bdd_C (p := p) 1
  · rw [he, lamC_one, map_one, pow_zero, one_mul]

theorem good_pow {g : GL3Theta.G1 p} {k : ℕ} {F : ℂ → ℂ} (hF : GoodAt g k F) (n : ℕ) :
    GoodAt g (k * n) (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_one g
  | succ n ih =>
    have := good_mul ih hF
    simp only [← pow_succ] at this
    rwa [show k * n + k = k * (n + 1) by ring] at this

theorem good_congr {g : GL3Theta.G1 p} {k l : ℕ} {F : ℂ → ℂ} (h : GoodAt g k F) (e : k = l) : GoodAt g l F :=
  e ▸ h

theorem atU_mul_pow {g : GL3Theta.G1 p} {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) (m n : ℕ) :
    AlgEnt (fun z => F z ^ m * G z ^ n) ∧ g.atU (fun z => F z ^ m * G z ^ n) = g.atU F ^ m * g.atU G ^ n := by
  have hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧
      g.atU (fun z => H z ^ k) = g.atU H ^ k := by
    intro H hH k
    induction k with
    | zero =>
      obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
      simp only [pow_zero]
      exact ⟨ha, by rw [he, lamC_one, map_one]⟩
    | succ k ih =>
      obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1
      simp only [pow_succ]
      exact ⟨ha, by rw [he, ih.2]⟩
  obtain ⟨h1, e1⟩ := hpow hF m
  obtain ⟨h2, e2⟩ := hpow hG n
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1
  exact ⟨ha, by rw [he, e1, e2]⟩

set_option maxHeartbeats 800000 in

theorem tau_pow_bdd : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  intro D p _ cc δ g hg t ht N hN hNt
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by
    funext z; simp [U1]
  have hsg : AlgEnt (sgStar g.abelian₂) := hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩
  have htq : InRationalLattice g.abelian₂ t := ⟨N, hN, hNt⟩
  have hP := halg t htq
  have htn := ht.1
  have hwt : wpF g.abelian₂ t ∈ Qbar := (hwp t htq htn).1
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt
  have gS : GoodAt g 2 (sqTh g.abelian₂ t) := ⟨hSa, lineSer g.wq⁻¹ (xAt g t),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hsg t htn hwt
  have gT : GoodAt g 3 (sqThD g.abelian₂ t) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z := by
    intro z
    rw [hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic p g _ φ c _ hEa (fun k => (gφ k).1) hEq
  choose B hB hBe using fun k => (gφ k).2
  have hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k) :=
    bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)
  rw [hEe, hsgU] at hlin
  simp only [hBe] at hlin
  have hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t := by
    rw [tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]
  rw [hPe] at hlin
  set K := 2 * I + 3 - N with hKd
  have hK : K + N = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) =
      e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0, fun n => ?_⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaTransl
end
end
