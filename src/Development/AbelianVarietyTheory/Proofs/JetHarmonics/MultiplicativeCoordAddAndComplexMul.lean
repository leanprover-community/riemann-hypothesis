import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubstStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeriesStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXyStatement
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.hat_multiplicative_chart | exact GlobalTheory.MomOne.hat_multiplicative_chart | (intros; apply GlobalTheory.MomOne.hat_multiplicative_chart <;> assumption)
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.SmallPt
variable {q : ℕ} [Fact q.Prime]

lemma norm_pow_sub_pow {a b : ℂ_[q]} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ r ^ n * ‖a - b‖ := by
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    have key : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ r * (r ^ n * ‖a - b‖) :=
            mul_le_mul ha ih (norm_nonneg _) hr
        _ = r ^ (n + 1) * ‖a - b‖ := by ring
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ (n + 1) ≤ ‖a - b‖ * r ^ (n + 1) := by gcongr
        _ = r ^ (n + 1) * ‖a - b‖ := mul_comm _ _

lemma summable_ev {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) {a : ℂ_[q]} (ha : ‖a‖ < 1) :
    Summable fun n => coeff n f * a ^ n := by
  have hf' : ∀ n, ‖coeff n f‖ ≤ 1 := hf
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply squeeze_zero_norm (a := fun n => ‖a‖ ^ n)
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hf' n)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha

lemma ev_zero (f : ℂ_[q]⟦X⟧) : ev f 0 = constantCoeff f := by
  unfold ev
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

lemma norm_ev_sub {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) {a b : ℂ_[q]} {r : ℝ} (hr : r < 1) (ha : ‖a‖ ≤ r)
    (hb : ‖b‖ ≤ r) : ‖ev f a - ev f b - coeff 1 f * (a - b)‖ ≤ r * ‖a - b‖ := by
  have hf' : ∀ n, ‖coeff n f‖ ≤ 1 := hf
  have hr0 : 0 ≤ r := (norm_nonneg a).trans ha
  have hsa := summable_ev hf (ha.trans_lt hr)
  have hsb := summable_ev hf (hb.trans_lt hr)
  set s : ℕ → ℂ_[q] := fun n => coeff n f * a ^ n - coeff n f * b ^ n with hs_def
  have hs : Summable s := hsa.sub hsb
  have hdiff : ev f a - ev f b = ∑' n, s n := by
    unfold ev; exact (hsa.tsum_sub hsb).symm
  have e0 : s 0 = 0 := by simp [hs_def]
  have e1 : s 1 = coeff 1 f * (a - b) := by simp only [hs_def, pow_one]; ring
  have key : ev f a - ev f b - coeff 1 f * (a - b) = ∑' n, s (n + 2) := by
    rw [hdiff, ← hs.sum_add_tsum_nat_add 2, Finset.sum_range_succ, Finset.sum_range_one, e0, e1]
    ring
  rw [key]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hr0 (norm_nonneg _)) (fun n => ?_)
  simp only [hs_def]
  rw [← mul_sub, norm_mul]
  have h2 : ‖a ^ (n + 1 + 1) - b ^ (n + 1 + 1)‖ ≤ r ^ (n + 1) * ‖a - b‖ :=
    norm_pow_sub_pow ha hb (n + 1)
  have h3 : r ^ (n + 1) ≤ r := by
    simpa using pow_le_pow_of_le_one hr0 hr.le (Nat.le_add_left 1 n)
  calc ‖coeff (n + 2) f‖ * ‖a ^ (n + 2) - b ^ (n + 2)‖ ≤ 1 * (r ^ (n + 1) * ‖a - b‖) :=
        mul_le_mul (hf' _) h2 (norm_nonneg _) zero_le_one
    _ ≤ r * ‖a - b‖ := by rw [one_mul]; exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

lemma norm_ev_sub_eq {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (h1 : ‖coeff 1 f‖ = 1) {a b : ℂ_[q]} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) : ‖ev f a - ev f b‖ = ‖a - b‖ := by
  by_cases hab : a = b
  · subst hab; simp
  have hr1 : max ‖a‖ ‖b‖ < 1 := max_lt ha hb
  have hD := norm_ev_sub hf hr1 (le_max_left _ _) (le_max_right _ _)
  have hpos : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hlin : ‖coeff 1 f * (a - b)‖ = ‖a - b‖ := by rw [norm_mul, h1, one_mul]
  have hlt : ‖ev f a - ev f b - coeff 1 f * (a - b)‖ < ‖coeff 1 f * (a - b)‖ := by
    rw [hlin]
    calc _ ≤ max ‖a‖ ‖b‖ * ‖a - b‖ := hD
      _ < 1 * ‖a - b‖ := mul_lt_mul_of_pos_right hr1 hpos
      _ = ‖a - b‖ := one_mul _
  have hsplit : ev f a - ev f b =
      coeff 1 f * (a - b) + (ev f a - ev f b - coeff 1 f * (a - b)) := by ring
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hlin]

lemma exists_ev_eq {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (h0 : constantCoeff f = 0) (h1 : ‖coeff 1 f‖ = 1)
    {t : ℂ_[q]} (ht : ‖t‖ < 1) : ∃ a, ‖a‖ < 1 ∧ ev f a = t := by
  have hev0 : ev f 0 = 0 := by rw [ev_zero, h0]
  have hc : coeff 1 f ≠ 0 := by
    intro hc; rw [hc, norm_zero] at h1; exact zero_ne_one h1
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hz : ‖(0 : ℂ_[q])‖ ≤ ‖t‖ := by simp [ht0]
  have hmaps : ∀ x : ℂ_[q], ‖x‖ ≤ ‖t‖ → ‖x - (coeff 1 f)⁻¹ * (ev f x - t)‖ ≤ ‖t‖ := by
    intro x hx
    have hD := norm_ev_sub hf ht hx hz
    rw [hev0, sub_zero, sub_zero] at hD
    have e : x - (coeff 1 f)⁻¹ * (ev f x - t) =
        (coeff 1 f)⁻¹ * t + -((coeff 1 f)⁻¹ * (ev f x - coeff 1 f * x)) := by
      linear_combination (-x) * inv_mul_cancel₀ hc
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_inv, h1, inv_one, one_mul]
    · rw [norm_neg, norm_mul, norm_inv, h1, inv_one, one_mul]
      exact hD.trans (mul_le_of_le_one_right ht0 (hx.trans ht.le))
  let T : Metric.closedBall (0 : ℂ_[q]) ‖t‖ → Metric.closedBall (0 : ℂ_[q]) ‖t‖ :=
    fun x => ⟨x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t), by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hx := x.2
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hmaps x.1 hx⟩
  have hK : ContractingWith ‖t‖₊ T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]; exact ht
    · have hx := x.2
      have hy := y.2
      rw [Metric.mem_closedBall, dist_zero_right] at hx hy
      rw [coe_nnnorm, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      show ‖(x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t)) - (y.1 - (coeff 1 f)⁻¹ * (ev f y.1 - t))‖ ≤
        ‖t‖ * ‖x.1 - y.1‖
      have e2 : (x.1 - (coeff 1 f)⁻¹ * (ev f x.1 - t)) - (y.1 - (coeff 1 f)⁻¹ * (ev f y.1 - t)) =
          -((coeff 1 f)⁻¹ * (ev f x.1 - ev f y.1 - coeff 1 f * (x.1 - y.1))) := by
        linear_combination (-(x.1 - y.1)) * inv_mul_cancel₀ hc
      rw [e2, norm_neg, norm_mul, norm_inv, h1, inv_one, one_mul]
      exact norm_ev_sub hf ht hx hy
  have : CompleteSpace (Metric.closedBall (0 : ℂ_[q]) ‖t‖) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty (Metric.closedBall (0 : ℂ_[q]) ‖t‖) := ⟨⟨0, by simp [ht0]⟩⟩
  have hfix : T (ContractingWith.fixedPoint T hK) = ContractingWith.fixedPoint T hK :=
    ContractingWith.fixedPoint_isFixedPt hK
  obtain ⟨a, haB⟩ := ContractingWith.fixedPoint T hK
  have hval := congrArg Subtype.val hfix
  refine ⟨(ContractingWith.fixedPoint T hK).1, ?_, ?_⟩
  · have hm := (ContractingWith.fixedPoint T hK).2
    rw [Metric.mem_closedBall, dist_zero_right] at hm
    exact hm.trans_lt ht
  · have h2 : (coeff 1 f)⁻¹ * (ev f (ContractingWith.fixedPoint T hK).1 - t) = 0 := by
      have hv : (ContractingWith.fixedPoint T hK).1 - (coeff 1 f)⁻¹ *
          (ev f (ContractingWith.fixedPoint T hK).1 - t) = (ContractingWith.fixedPoint T hK).1 := hval
      linear_combination -hv
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (inv_ne_zero hc)
    · exact sub_eq_zero.1 h3

def cub (W : WeierstrassCurve ℂ_[q]) (u : ℂ_[q]) : ℂ_[q]⟦X⟧ :=
  PowerSeries.mk fun n => if n = 1 then 1 - (W.a₁ * u + W.a₂ * u ^ 2) else
    if n = 2 then -(W.a₃ + W.a₄ * u) else if n = 3 then -W.a₆ else 0

lemma ev_cub (W : WeierstrassCurve ℂ_[q]) (u w : ℂ_[q]) :
    ev (cub W u) w = w - (W.a₁ * u * w + W.a₂ * u ^ 2 * w + W.a₃ * w ^ 2 + W.a₄ * u * w ^ 2 +
      W.a₆ * w ^ 3) := by
  unfold ev cub
  rw [tsum_eq_sum (s := {1, 2, 3})]
  · simp [Finset.sum_insert, coeff_mk]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [coeff_mk, hn.1, hn.2.1, hn.2.2]

variable {M : Mdl q}

lemma norm_coeff_one_cub (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : ‖coeff 1 (cub M.W u)‖ = 1 := by
  unfold Mdl.Ok at h
  obtain ⟨-, h1, h2, -, -, -, -, -, -⟩ := h
  have hs : ‖M.W.a₁ * u + M.W.a₂ * u ^ 2‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans_lt hu
    · rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_left (by positivity) h2).trans_lt
        (pow_lt_one₀ (norm_nonneg _) hu two_ne_zero)
  rw [cub, coeff_mk, if_pos rfl]
  have hne : ‖(1 : ℂ_[q])‖ ≠ ‖-(M.W.a₁ * u + M.W.a₂ * u ^ 2)‖ := by
    rw [norm_one, norm_neg]; exact hs.ne'
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg,
    max_eq_left hs.le]

lemma bd_cub (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : Bd 1 (cub M.W u) := by
  have h1 := norm_coeff_one_cub h hu
  unfold Mdl.Ok at h
  obtain ⟨-, -, -, ha3, ha4, ha6, -, -, -⟩ := h
  unfold Bd
  intro n
  by_cases e1 : n = 1
  · subst e1; exact h1.le
  by_cases e2 : n = 2
  · subst e2
    rw [cub, coeff_mk, if_neg (by norm_num), if_pos rfl, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha3 ?_)
    rw [norm_mul]; exact mul_le_one₀ ha4 (norm_nonneg _) hu.le
  by_cases e3 : n = 3
  · subst e3
    rw [cub, coeff_mk, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, norm_neg]
    exact ha6
  · rw [cub, coeff_mk, if_neg e1, if_neg e2, if_neg e3, norm_zero]; exact zero_le_one

private lemma one_lt_norm_y_of_small_of_not_mem (h : M.Ok) {p : ℂ} (hp : M.Small p) (hL : p ∉ M.L.lattice) :
    1 < ‖M.ι (M.y p)‖ := by
  unfold Mdl.Small at hp
  have hx : 1 < ‖M.ι (M.x p)‖ := hp.resolve_left hL
  exact hx.trans (UW.norm_x_lt M h hL hx)

lemma ev_cub_small (h : M.Ok) {p : ℂ} (hp : M.Small p) :
    ev (cub M.W (M.ι (M.u p))) (M.ι (M.w p)) = M.ι (M.u p) ^ 3 := by
  rw [ev_cub]
  unfold Mdl.u Mdl.w
  by_cases hL : p ∈ M.L.lattice
  · simp [hL]
  · simp only [hL, if_false]
    have hY := one_lt_norm_y_of_small_of_not_mem h hp hL
    have hy' : M.ι (M.y p) ≠ 0 := fun e => by rw [e, norm_zero] at hY; linarith
    have E := congrArg M.ι (UW.equation M h hL)
    simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply] at E
    simp only [map_div₀, map_neg, map_one]
    field_simp
    linear_combination (-1 : ℂ_[q]) * E

private lemma norm_u_w_lt_one_and_w_eq_zero_iff_of_small (h : M.Ok) {p : ℂ} (hp : M.Small p) :
    ‖M.ι (M.u p)‖ < 1 ∧ ‖M.ι (M.w p)‖ < 1 ∧ (M.w p = 0 ↔ p ∈ M.L.lattice) := by
  by_cases hL : p ∈ M.L.lattice
  · have hu : M.u p = 0 := by unfold Mdl.u; simp [hL]
    have hw : M.w p = 0 := by unfold Mdl.w; simp [hL]
    simp [hu, hw, hL]
  · have hY := one_lt_norm_y_of_small_of_not_mem h hp hL
    have hp2 := hp
    unfold Mdl.Small at hp2
    have hx : 1 < ‖M.ι (M.x p)‖ := hp2.resolve_left hL
    have hxy := UW.norm_x_lt M h hL hx
    have hY0 : 0 < ‖M.ι (M.y p)‖ := zero_lt_one.trans hY
    have hu : M.u p = -M.x p / M.y p := by unfold Mdl.u; simp [hL]
    have hw : M.w p = -1 / M.y p := by unfold Mdl.w; simp [hL]
    have hy0 : M.y p ≠ 0 := fun e => by rw [e, map_zero, norm_zero] at hY; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hu, map_div₀, map_neg, norm_div, norm_neg, div_lt_one hY0]; exact hxy
    · rw [hw, map_div₀, map_neg, map_one, norm_div, norm_neg, norm_one, div_lt_one hY0]; exact hY
    · rw [hw]; simp [hy0, hL]

lemma sub_mem_of_u_eq (h : M.Ok) {p p' : ℂ} (hp : M.Small p) (hp' : M.Small p')
    (e : M.u p = M.u p') : p - p' ∈ M.L.lattice := by
  classical
  obtain ⟨-, hw1, hwL1⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp
  obtain ⟨hu2, hw2, hwL2⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp'
  have hU : M.ι (M.u p) = M.ι (M.u p') := by rw [e]
  have hev1 := ev_cub_small h hp
  have hev2 := ev_cub_small h hp'
  rw [hU] at hev1
  have hiso := norm_ev_sub_eq (bd_cub h hu2) (norm_coeff_one_cub h hu2) hw1 hw2
  rw [hev1, hev2, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hiso
  have hW : M.w p = M.w p' := M.ι.injective hiso
  by_cases hL : p ∈ M.L.lattice
  · have hL' : p' ∈ M.L.lattice := hwL2.1 (by rw [← hW]; exact hwL1.2 hL)
    exact sub_mem hL hL'
  · have hL' : p' ∉ M.L.lattice := fun h' => hL (hwL1.1 (hW.trans (hwL2.2 h')))
    have hy0 : M.y p' ≠ 0 := fun e0 => by
      have := one_lt_norm_y_of_small_of_not_mem h hp' hL'
      rw [e0, map_zero, norm_zero] at this; linarith
    have hy : M.y p = M.y p' := by
      have h0 := hW
      unfold Mdl.w at h0
      simp only [hL, hL', if_false] at h0
      rw [neg_div, neg_div, neg_inj, one_div, one_div, inv_inj] at h0
      exact h0
    have hx : M.x p = M.x p' := by
      have h0 := e
      unfold Mdl.u at h0
      simp only [hL, hL', if_false] at h0
      rw [hy, div_left_inj' hy0, neg_inj] at h0
      exact h0
    obtain ⟨φ, -, hker, hφ⟩ := Mdl.exists_pointHom q M h
    obtain ⟨h1, e1⟩ := hφ p hL
    obtain ⟨h2, e2⟩ := hφ p' hL'
    have hφ0 : φ (p - p') = 0 := by
      rw [map_sub, e1, e2, sub_eq_zero, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨by rw [hx], by rw [hy]⟩
    exact (hker _).1 hφ0

lemma exists_small (h : M.Ok) {u : ℂ_[q]} (hu : ‖u‖ < 1) : ∃ p, M.Small p ∧ u = M.ι (M.u p) := by
  classical
  have hf := bd_cub h hu
  have hc1 := norm_coeff_one_cub h hu
  have h0 : constantCoeff (cub M.W u) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, cub, coeff_mk]; simp
  have hu3 : ‖u ^ 3‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hu (by norm_num)
  obtain ⟨w, hw, hev⟩ := exists_ev_eq hf h0 hc1 hu3
  rw [ev_cub] at hev
  by_cases hw0 : w = 0
  · subst hw0
    have hu0 : u = 0 := by
      have h3 : u ^ 3 = 0 := by rw [← hev]; ring
      exact (pow_eq_zero_iff (by norm_num)).1 h3
    refine ⟨0, by unfold Mdl.Small; exact Or.inl (zero_mem _), ?_⟩
    unfold Mdl.u
    simp [hu0]
  · have hOk := h
    unfold Mdl.Ok at hOk
    obtain ⟨-, ha1, ha2, ha3, ha4, ha6, hΔ, -, -⟩ := hOk
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hrel : w = u ^ 3 + M.W.a₁ * u * w + M.W.a₂ * u ^ 2 * w + M.W.a₃ * w ^ 2 +
        M.W.a₄ * u * w ^ 2 + M.W.a₆ * w ^ 3 := by linear_combination hev
    have hwu : ‖w‖ < ‖u‖ := by
      by_contra hle
      push Not at hle
      have hw1 : ‖w‖ ≤ 1 := hw.le
      have hu1 : ‖u‖ ≤ 1 := hu.le
      have add_le : ∀ x y : ℂ_[q], ‖x‖ ≤ ‖w‖ ^ 2 → ‖y‖ ≤ ‖w‖ ^ 2 → ‖x + y‖ ≤ ‖w‖ ^ 2 :=
        fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
      have t1 : ‖u ^ 3‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_pow]
        calc ‖u‖ ^ 3 ≤ ‖w‖ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hle 3
          _ = ‖w‖ * ‖w‖ ^ 2 := by ring
          _ ≤ 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := one_mul _
      have t2 : ‖M.W.a₁ * u * w‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul]
        calc ‖M.W.a₁‖ * ‖u‖ * ‖w‖ ≤ 1 * ‖w‖ * ‖w‖ := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t3 : ‖M.W.a₂ * u ^ 2 * w‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        calc ‖M.W.a₂‖ * ‖u‖ ^ 2 * ‖w‖ ≤ 1 * ‖w‖ ^ 2 * 1 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t4 : ‖M.W.a₃ * w ^ 2‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        calc ‖M.W.a₃‖ * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := one_mul _
      have t5 : ‖M.W.a₄ * u * w ^ 2‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        calc ‖M.W.a₄‖ * ‖u‖ * ‖w‖ ^ 2 ≤ 1 * 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have t6 : ‖M.W.a₆ * w ^ 3‖ ≤ ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        calc ‖M.W.a₆‖ * ‖w‖ ^ 3 = ‖M.W.a₆‖ * ‖w‖ * ‖w‖ ^ 2 := by ring
          _ ≤ 1 * 1 * ‖w‖ ^ 2 := by gcongr
          _ = ‖w‖ ^ 2 := by ring
      have hb := add_le _ _ (add_le _ _ (add_le _ _ (add_le _ _ (add_le _ _ t1 t2) t3) t4) t5) t6
      rw [← hrel] at hb
      nlinarith
    have hΔ0 : M.W.Δ ≠ 0 := by
      intro e; rw [e, norm_zero] at hΔ; exact zero_ne_one hΔ
    have heq : M.W.toAffine.Equation (u / w) (-1 / w) := by
      rw [WeierstrassCurve.Affine.equation_iff]
      field_simp
      linear_combination hev
    have hns := (M.W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ0).1 heq
    obtain ⟨φ, hsurj, hker, hφ⟩ := Mdl.exists_pointHom q M h
    obtain ⟨z, hz⟩ := hsurj (WeierstrassCurve.Affine.Point.some (u / w) (-1 / w) hns)
    have hzL : z ∉ M.L.lattice := fun hz' => by
      rw [(hker z).2 hz'] at hz; cases hz
    obtain ⟨hz1, hz2⟩ := hφ z hzL
    rw [hz2, WeierstrassCurve.Affine.Point.some.injEq] at hz
    refine ⟨z, ?_, ?_⟩
    · unfold Mdl.Small
      right
      rw [hz.1, norm_div]
      exact (one_lt_div hwpos).2 hwu
    · unfold Mdl.u
      rw [if_neg hzL, map_div₀, map_neg, hz.1, hz.2]
      field_simp

lemma small_add {p l : ℂ} (hl : l ∈ M.L.lattice) (hp : M.Small p) : M.Small (p + l) := by
  unfold Mdl.Small at *
  by_cases hpL : p ∈ M.L.lattice
  · exact Or.inl (add_mem hpL hl)
  · right
    rw [UW.x_add M hl p]
    exact hp.resolve_left hpL

private lemma u_add_lattice {l : ℂ} (hl : l ∈ M.L.lattice) (p : ℂ) : M.u (p + l) = M.u p := by
  unfold Mdl.u
  by_cases hpL : p ∈ M.L.lattice
  · simp [hpL, add_mem hpL hl]
  · have hpl : p + l ∉ M.L.lattice := fun h' => hpL (by simpa using sub_mem h' hl)
    simp only [hpL, hpl, if_false, UW.x_add M hl p, UW.y_add M hl p]

theorem at_exists_unique : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ : ℂ_[q], ‖ζ - 1‖ < 1 → ∃ p, M.At ω ζ p) ∧ (∀ p, M.Small p → ∃ ζ, M.At ω ζ p) ∧ (∀ ζ ζ' p, M.At ω ζ p → M.At ω ζ' p → ζ = ζ') ∧ (∀ ζ p p', M.At ω ζ p → (M.At ω ζ p' ↔ p - p' ∈ M.L.lattice)) ∧ M.At ω 1 0 := by
  intro q _ M ω hω
  have hch := hω
  unfold Mdl.MChart Mdl.Chart at hch
  obtain ⟨h, hℓ0, hbd, hc1⟩ := hch
  have hu0 : M.u 0 = 0 := by unfold Mdl.u; simp [zero_mem]
  have hg0 : constantCoeff (hat M.ι (C ω * logS) M.u) = 0 := by
    rw [(TaylorRead.hat_laws q M.ι _ hℓ0).2.2.2.1 M.u, hu0, map_zero]
  have hev0 : ev (hat M.ι (C ω * logS) M.u) 0 = 0 := by rw [ev_zero, hg0]
  have hAt : ∀ ζ p, M.At ω ζ p ↔ M.Small p ∧ ‖ζ - 1‖ < 1 ∧
      ev (hat M.ι (C ω * logS) M.u) (ζ - 1) = M.ι (M.u p) := fun ζ p => Iff.rfl
  have hnorm : ∀ a : ℂ_[q], ‖a‖ < 1 → ‖ev (hat M.ι (C ω * logS) M.u) a‖ = ‖a‖ := fun a ha => by
    have := norm_ev_sub_eq hbd hc1 ha (by simp : ‖(0 : ℂ_[q])‖ < 1)
    rwa [hev0, sub_zero, sub_zero] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    have ht : ‖ev (hat M.ι (C ω * logS) M.u) (ζ - 1)‖ < 1 := by rw [hnorm _ hζ]; exact hζ
    obtain ⟨p, hp, hpu⟩ := exists_small h ht
    exact ⟨p, (hAt _ _).2 ⟨hp, hζ, hpu⟩⟩
  · intro p hp
    obtain ⟨hu1, -, -⟩ := norm_u_w_lt_one_and_w_eq_zero_iff_of_small h hp
    obtain ⟨a, ha, hea⟩ := exists_ev_eq hbd hg0 hc1 hu1
    refine ⟨a + 1, (hAt _ _).2 ⟨hp, by rw [add_sub_cancel_right]; exact ha, ?_⟩⟩
    rw [add_sub_cancel_right]; exact hea
  · intro ζ ζ' p h1 h2
    obtain ⟨-, hζ1, he1⟩ := (hAt _ _).1 h1
    obtain ⟨-, hζ2, he2⟩ := (hAt _ _).1 h2
    have := norm_ev_sub_eq hbd hc1 hζ1 hζ2
    rw [he1, he2, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero, sub_left_inj] at this
    exact this
  · intro ζ p p' h1
    obtain ⟨hp, hζ, he⟩ := (hAt _ _).1 h1
    constructor
    · intro h2
      obtain ⟨hp', -, he'⟩ := (hAt _ _).1 h2
      exact sub_mem_of_u_eq h hp hp' (M.ι.injective (he.symm.trans he'))
    · intro hd
      have hl : p' - p ∈ M.L.lattice := by simpa using neg_mem hd
      have hp' : M.Small p' := by simpa using small_add hl hp
      refine (hAt _ _).2 ⟨hp', hζ, ?_⟩
      rw [he, ← u_add_lattice hl p, add_sub_cancel]
  · refine (hAt _ _).2 ⟨by unfold Mdl.Small; exact Or.inl (zero_mem _), by simp, ?_⟩
    rw [sub_self, hev0, hu0, map_zero]

end GlobalTheory.MomOne.SmallPt
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ : ℂ_[q], ‖ζ - 1‖ < 1 → ∃ p, M.At ω ζ p) ∧ (∀ p, M.Small p → ∃ ζ, M.At ω ζ p) ∧ (∀ ζ ζ' p, M.At ω ζ p → M.At ω ζ' p → ζ = ζ') ∧ (∀ ζ p p', M.At ω ζ p → (M.At ω ζ p' ↔ p - p' ∈ M.L.lattice)) ∧ M.At ω 1 0 := by
  atlas_forward_decl GlobalTheory.MomOne.SmallPt.at_exists_unique
end

section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem dvd_aeval_sub_aeval_two {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a u w u' w' : A) (hu : a ∣ u - u') (hw : a ∣ w - w') (P : MvPolynomial (Fin 2) K) :
    a ∣ MvPolynomial.aeval ![u, w] P - MvPolynomial.aeval ![u', w'] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have := dvd_add hp hr
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have hi : a ∣ (![u, w] i) - (![u', w'] i) := by
      fin_cases i
      · simpa using hu
      · simpa using hw
    have := dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem X_pow_succ_dvd_of_DT {q : ℕ} [Fact q.Prime] (f : ℂ_[q]⟦X⟧) (n : ℕ)
    (h0 : constantCoeff f = 0) (hD : (X : ℂ_[q]⟦X⟧) ^ n ∣ DT f) :
    (X : ℂ_[q]⟦X⟧) ^ (n + 1) ∣ f := by
  have hu : IsUnit (1 + X : ℂ_[q]⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  unfold DT at hD
  rw [hu.dvd_mul_left, X_pow_dvd_iff] at hD
  rw [X_pow_dvd_iff]
  intro m hm
  cases m with
  | zero => simpa using h0
  | succ k =>
    have := hD k (by omega)
    rw [coeff_derivative] at this
    have hk : ((k : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hk

theorem ode_unique : ∀ (q : ℕ) [Fact q.Prime] (P₁ P₂ : MvPolynomial (Fin 2) ℂ_[q]) (u w u' w' : ℂ_[q]⟦X⟧), DT u = MvPolynomial.aeval ![u, w] P₁ → DT w = MvPolynomial.aeval ![u, w] P₂ → DT u' = MvPolynomial.aeval ![u', w'] P₁ → DT w' = MvPolynomial.aeval ![u', w'] P₂ → constantCoeff u = constantCoeff u' → constantCoeff w = constantCoeff w' → u = u' ∧ w = w' := by
  intro q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw
  have hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g := by
    intro f g
    unfold DT
    rw [map_sub, mul_sub]
  have key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hu, sub_self]
        · rw [hsub, h1, h3]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hw, sub_self]
        · rw [hsub, h2, h4]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
  constructor
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)

end GlobalTheory.MomOne
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.SmallTranslate
variable {q : ℕ} [Fact q.Prime]

lemma norm_coeff_mul_le (f g : ℂ_[q]⟦X⟧) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, i + j = n → ‖coeff i f * coeff j g‖ ≤ B) : ‖coeff n (f * g)‖ ≤ B := by
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro p hp
  exact h _ _ (by simpa using hp)

lemma bdd_C (c : ℂ_[q]) : Bdd (C c : ℂ_[q]⟦X⟧) := by
  refine ⟨‖c‖, fun n => ?_⟩
  rw [coeff_C]; split_ifs <;> simp

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A + B, fun n => ?_⟩
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨A * B, fun n => norm_coeff_mul_le f g n (mul_nonneg hA0 hB0) fun i j _ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hA i) (hB j) (norm_nonneg _) hA0

lemma shift_aeval {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {u w : ℂ_[q]⟦X⟧} (hu : Bdd u) (hw : Bdd w)
    (P : MvPolynomial (Fin 2) ℂ_[q]) :
    Bdd (MvPolynomial.aeval ![u, w] P) ∧
      shiftS ζ (MvPolynomial.aeval ![u, w] P) = MvPolynomial.aeval ![shiftS ζ u, shiftS ζ w] P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.aeval_C]
    exact ⟨bdd_C c, Shift.shiftS_C ζ c⟩
  | add p r hp hr =>
    simp only [map_add]
    exact ⟨bdd_add hp.1 hr.1, by rw [Shift.shiftS_add h hp.1 hr.1, hp.2, hr.2]⟩
  | mul_X p i hp =>
    have hi : Bdd (![u, w] i) := by
      fin_cases i
      · exact hu
      · exact hw
    have hi2 : shiftS ζ (![u, w] i) = ![shiftS ζ u, shiftS ζ w] i := by
      fin_cases i <;> rfl
    simp only [map_mul, MvPolynomial.aeval_X]
    exact ⟨bdd_mul hp.1 hi, by rw [Shift.shiftS_mul h hp.1 hi, hp.2, hi2]⟩

lemma hat_eval (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hℓ : constantCoeff ℓ = 0) {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (P : MvPolynomial (Fin 2) ℂ_[q]) :
    AnalyticAt ℂ (fun z => MvPolynomial.eval₂ (ι.symm : ℂ_[q] →+* ℂ) ![F z, G z] P) 0 ∧
      hat ι ℓ (fun z => MvPolynomial.eval₂ (ι.symm : ℂ_[q] →+* ℂ) ![F z, G z] P) =
        MvPolynomial.aeval ![hat ι ℓ F, hat ι ℓ G] P := by
  obtain ⟨h1, h2, -⟩ := TaylorRead.hat_laws q ι ℓ hℓ
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.eval₂_C]
    refine ⟨analyticAt_const, ?_⟩
    rw [h2]
    simp
  | add p r hp hr =>
    simp only [map_add, MvPolynomial.eval₂_add]
    exact ⟨hp.1.add hr.1, by rw [(h1 _ _ hp.1 hr.1).1, hp.2, hr.2]⟩
  | mul_X p i hp =>
    have hi : AnalyticAt ℂ (fun z => ![F z, G z] i) 0 := by
      fin_cases i
      · exact hF
      · exact hG
    have hi2 : hat ι ℓ (fun z => ![F z, G z] i) = ![hat ι ℓ F, hat ι ℓ G] i := by
      fin_cases i <;> rfl
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact ⟨hp.1.mul hi, by rw [(h1 _ _ hp.1 hi).2.1, hp.2, hi2]⟩

lemma one_add_X_mul_derivative_logS : (1 + X) * derivative ℂ_[q] (logS : ℂ_[q]⟦X⟧) = 1 := by
  have hc : ∀ n, coeff n (derivative ℂ_[q] (logS : ℂ_[q]⟦X⟧)) = (-1) ^ n := by
    intro n
    have hk : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [coeff_derivative, logS, coeff_mk, if_neg (Nat.succ_ne_zero n)]
    push_cast
    field_simp
    ring
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => rw [coeff_zero_X_mul, hc]; simp
  | succ n => rw [coeff_succ_X_mul, hc, hc, coeff_one, if_neg (Nat.succ_ne_zero n)]; ring

lemma constantCoeff_chart (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply logS, logS, coeff_mk]; simp

lemma DT_hat (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) :
    DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G) := by
  obtain ⟨-, -, -, -, h5, -⟩ := TaylorRead.hat_laws q ι _ (constantCoeff_chart ω)
  have hd : derivative ℂ_[q] (C ω * logS : ℂ_[q]⟦X⟧) = C ω * derivative ℂ_[q] logS := by
    rw [Derivation.leibniz]; simp
  rw [DT, h5 G hG, hd]
  linear_combination (C ω * hat ι (C ω * logS) (deriv G)) * one_add_X_mul_derivative_logS (q := q)

def Peq (W : WeierstrassCurve ℂ_[q]) : MvPolynomial (Fin 2) ℂ_[q] :=
  MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 + MvPolynomial.C W.a₃ * MvPolynomial.X 1 ^ 2 + MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 + MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3

def Pu (W : WeierstrassCurve ℂ_[q]) (c : ℂ_[q]) : MvPolynomial (Fin 2) ℂ_[q] :=
  MvPolynomial.C c * (1 - MvPolynomial.C W.a₁ * MvPolynomial.X 0 - MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 - 2 * MvPolynomial.C W.a₃ * MvPolynomial.X 1 - 2 * MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 1 - 3 * MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 2)

def Pw (W : WeierstrassCurve ℂ_[q]) (c : ℂ_[q]) : MvPolynomial (Fin 2) ℂ_[q] :=
  MvPolynomial.C c * (3 * MvPolynomial.X 0 ^ 2 + MvPolynomial.C W.a₁ * MvPolynomial.X 1 + 2 * MvPolynomial.C W.a₂ * MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.C W.a₄ * MvPolynomial.X 1 ^ 2)

lemma flow (M : Mdl q) (ω : ℂ_[q]) (p : ℂ) (hM : M.Ok) (hp : M.Small p) :
    hat M.ι (C ω * logS) (fun z => M.w (z + p)) =
      MvPolynomial.aeval ![hat M.ι (C ω * logS) (fun z => M.u (z + p)),
        hat M.ι (C ω * logS) (fun z => M.w (z + p))] (Peq M.W) ∧
    DT (hat M.ι (C ω * logS) (fun z => M.u (z + p))) =
      MvPolynomial.aeval ![hat M.ι (C ω * logS) (fun z => M.u (z + p)),
        hat M.ι (C ω * logS) (fun z => M.w (z + p))] (MvPolynomial.C ω * Pu M.W (M.ι M.c)) ∧
    DT (hat M.ι (C ω * logS) (fun z => M.w (z + p))) =
      MvPolynomial.aeval ![hat M.ι (C ω * logS) (fun z => M.u (z + p)),
        hat M.ι (C ω * logS) (fun z => M.w (z + p))] (MvPolynomial.C ω * Pw M.W (M.ι M.c)) := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := uw_elliptic_flow q M hM
  obtain ⟨hu, hw, -, -, -, hev⟩ := h p hp
  have ht : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 p) := by
    have : Continuous (fun z : ℂ => z + p) := by fun_prop
    simpa using this.tendsto 0
  have hev' := (ht.eventually hev).filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  have ha : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu' : AnalyticAt ℂ (fun z => M.u (z + p)) 0 := AnalyticAt.comp_of_eq hu ha (by simp)
  have hw' : AnalyticAt ℂ (fun z => M.w (z + p)) 0 := AnalyticAt.comp_of_eq hw ha (by simp)
  obtain ⟨h1, -⟩ := TaylorRead.hat_laws q M.ι _ (constantCoeff_chart ω)
  have e := hat_eval M.ι (constantCoeff_chart ω) hu' hw'
  have c2 : MvPolynomial.C (σ := Fin 2) (2 : ℂ_[q]) = 2 := rfl
  have c3 : MvPolynomial.C (σ := Fin 2) (3 : ℂ_[q]) = 3 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← (e _).2]
    refine (h1 _ _ hw' (e _).1).2.2.1 (hev'.mono fun z hz => ?_)
    have := hz.1
    simpa [Peq, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow] using this
  · rw [DT_hat _ _ hu', map_mul, MvPolynomial.aeval_C, ← (e _).2]
    congr 1
    refine (h1 _ _ hu'.deriv (e _).1).2.2.1 (hev'.mono fun z hz => ?_)
    have := hz.2.1
    rw [deriv_comp_add_const]
    simp only [Pu, ← c2, ← c3]
    simpa [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_sub, map_ofNat] using this
  · rw [DT_hat _ _ hw', map_mul, MvPolynomial.aeval_C, ← (e _).2]
    congr 1
    refine (h1 _ _ hw'.deriv (e _).1).2.2.1 (hev'.mono fun z hz => ?_)
    have := hz.2.2
    rw [deriv_comp_add_const]
    simp only [Pw, ← c2, ← c3]
    simpa [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_sub, map_ofNat] using this

def IntLt (n : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ m < n, ‖coeff m f‖ ≤ 1

lemma intLt_add {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f + g) := by
  intro m hm
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf m hm) (hg m hm))

lemma intLt_mul {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f * g) := by
  intro m hm
  refine norm_coeff_mul_le f g m zero_le_one fun i j hij => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma intLt_C {n : ℕ} {c : ℂ_[q]} (hc : ‖c‖ ≤ 1) : IntLt n (C c : ℂ_[q]⟦X⟧) := by
  intro m _
  rw [coeff_C]; split_ifs
  · exact hc
  · simp

lemma intLt_succ_mul {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g)
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0) : IntLt (n + 1) (f * g) := by
  intro m hm
  refine norm_coeff_mul_le f g m zero_le_one fun i j hij => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hf0]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hg0]
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma bd_of_equation (W : WeierstrassCurve ℂ_[q]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {u w : ℂ_[q]⟦X⟧} (hu : Bd 1 u)
    (hu0 : constantCoeff u = 0) (hw0 : constantCoeff w = 0)
    (h : w = MvPolynomial.aeval ![u, w] (Peq W)) : Bd 1 w := by
  have e : w = u * u * u + w * (C W.a₁ * u + C W.a₂ * (u * u) + C W.a₃ * w + C W.a₄ * (u * w)
      + C W.a₆ * (w * w)) := by
    refine h.trans ?_
    have hC : ∀ a : ℂ_[q], algebraMap ℂ_[q] ℂ_[q]⟦X⟧ a = C a := fun _ => rfl
    simp [Peq, hC]
    ring
  have hU : ∀ n, IntLt n u := fun n m _ => hu m
  have key : ∀ n, IntLt n w := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      rw [e]
      refine intLt_add (intLt_mul (intLt_mul (hU _) (hU _)) (hU _)) (intLt_succ_mul ih ?_ hw0 ?_)
      · exact intLt_add (intLt_add (intLt_add (intLt_add (intLt_mul (intLt_C h1) (hU _))
          (intLt_mul (intLt_C h2) (intLt_mul (hU _) (hU _)))) (intLt_mul (intLt_C h3) ih))
          (intLt_mul (intLt_C h4) (intLt_mul (hU _) ih))) (intLt_mul (intLt_C h6) (intLt_mul ih ih))
      · simp [hu0, hw0]
  exact fun n => key (n + 1) n (Nat.lt_succ_self n)

lemma norm_constantCoeff_shift_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f)
    (h0 : constantCoeff f = 0) : ‖constantCoeff (shiftS ζ f)‖ < 1 := by
  obtain ⟨g, rfl⟩ := X_dvd_iff.mpr h0
  have hg : Bd 1 g := fun n => by simpa [coeff_succ_X_mul] using hf (n + 1)
  have hX : Bdd (X : ℂ_[q]⟦X⟧) := ⟨1, fun n => by rw [coeff_X]; split_ifs <;> simp⟩
  have hs := Shift.bd_shiftS h hg 0
  rw [Shift.shiftS_mul h hX ⟨1, hg⟩, Shift.shiftS_X, map_mul, norm_mul]
  rw [coeff_zero_eq_constantCoeff_apply] at hs
  have : constantCoeff (C ζ * (1 + X) - 1 : ℂ_[q]⟦X⟧) = ζ - 1 := by simp
  rw [this]
  exact (mul_le_of_le_one_right (norm_nonneg _) hs).trans_lt h

lemma solution_unique {a₁ a₂ a₃ a₄ a₆ u w w' : ℂ_[q]} (h1 : ‖a₁‖ ≤ 1) (h2 : ‖a₂‖ ≤ 1)
    (h3 : ‖a₃‖ ≤ 1) (h4 : ‖a₄‖ ≤ 1) (h6 : ‖a₆‖ ≤ 1) (hu : ‖u‖ < 1) (hw : ‖w‖ < 1) (hw' : ‖w'‖ < 1)
    (e : w = u ^ 3 + a₁ * u * w + a₂ * u ^ 2 * w + a₃ * w ^ 2 + a₄ * u * w ^ 2 + a₆ * w ^ 3)
    (e' : w' = u ^ 3 + a₁ * u * w' + a₂ * u ^ 2 * w' + a₃ * w' ^ 2 + a₄ * u * w' ^ 2 + a₆ * w' ^ 3) :
    w = w' := by
  have ad : ∀ {x y : ℂ_[q]}, ‖x‖ < 1 → ‖y‖ < 1 → ‖x + y‖ < 1 := fun hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  have mu : ∀ {x y : ℂ_[q]}, ‖x‖ ≤ 1 → ‖y‖ < 1 → ‖x * y‖ < 1 := fun hx hy => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
  have hk : ‖a₁ * u + a₂ * (u * u) + a₃ * (w + w') + a₄ * (u * (w + w')) +
      a₆ * (w * w + w * w' + w' * w')‖ < 1 :=
    ad (ad (ad (ad (mu h1 hu) (mu h2 (mu hu.le hu))) (mu h3 (ad hw hw')))
      (mu h4 (mu hu.le (ad hw hw')))) (mu h6 (ad (ad (mu hw.le hw) (mu hw.le hw')) (mu hw'.le hw')))
  have hne : 1 - (a₁ * u + a₂ * (u * u) + a₃ * (w + w') + a₄ * (u * (w + w')) +
      a₆ * (w * w + w * w' + w' * w')) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hk
    simp at hk
  apply mul_left_cancel₀ hne
  linear_combination e - e'

lemma constantCoeff_equation (W : WeierstrassCurve ℂ_[q]) {U V : ℂ_[q]⟦X⟧}
    (h : V = MvPolynomial.aeval ![U, V] (Peq W)) :
    constantCoeff V = constantCoeff U ^ 3 + W.a₁ * constantCoeff U * constantCoeff V +
      W.a₂ * constantCoeff U ^ 2 * constantCoeff V + W.a₃ * constantCoeff V ^ 2 +
      W.a₄ * constantCoeff U * constantCoeff V ^ 2 + W.a₆ * constantCoeff V ^ 3 := by
  have hC : ∀ a : ℂ_[q], algebraMap ℂ_[q] ℂ_[q]⟦X⟧ a = C a := fun _ => rfl
  have := congrArg constantCoeff h
  simpa [Peq, hC] using this

theorem shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ), M.MChart ω → M.At ω ζ p → hat M.ι (C ω * logS) (fun z => M.u (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.u) ∧ hat M.ι (C ω * logS) (fun z => M.w (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.w) := by
  intro q _ M ω ζ p hM hA
  obtain ⟨hOk, hℓ, hu, -⟩ := hM
  obtain ⟨hp, hζ, hev⟩ := hA
  obtain ⟨f0, f1, f2⟩ := flow M ω p hOk hp
  obtain ⟨g0, g1, g2⟩ := flow M ω 0 hOk (Or.inl (zero_mem _))
  simp only [add_zero] at g0 g1 g2
  obtain ⟨-, -, -, -, u0, w0, -, -, hs⟩ := uw_elliptic_flow q M hOk
  obtain ⟨-, -, hup, hwp, -⟩ := hs p hp
  obtain ⟨-, -, -, hc, -⟩ := TaylorRead.hat_laws q M.ι _ hℓ
  obtain ⟨-, h1, h2, h3, h4, h6, -⟩ := hOk
  have cu : constantCoeff (hat M.ι (C ω * logS) M.u) = 0 := by rw [hc, u0, map_zero]
  have cw : constantCoeff (hat M.ι (C ω * logS) M.w) = 0 := by rw [hc, w0, map_zero]
  have hw : Bd 1 (hat M.ι (C ω * logS) M.w) := bd_of_equation M.W h1 h2 h3 h4 h6 hu cu cw g0
  have sh := shift_aeval hζ ⟨1, hu⟩ ⟨1, hw⟩
  have eu : constantCoeff (hat M.ι (C ω * logS) (fun z => M.u (z + p))) =
      constantCoeff (shiftS ζ (hat M.ι (C ω * logS) M.u)) := by
    rw [hc, Shift.constantCoeff_shiftS, hev, zero_add]
  refine ode_unique q _ _ _ _ _ _ f1 f2 ?_ ?_ eu ?_
  · rw [← (sh _).2, ← g1, Shift.DT_shiftS hζ ⟨1, hu⟩]
  · rw [← (sh _).2, ← g2, Shift.DT_shiftS hζ ⟨1, hw⟩]
  · have e1 := constantCoeff_equation M.W f0
    have e2 := constantCoeff_equation M.W
      (U := shiftS ζ (hat M.ι (C ω * logS) M.u)) (V := shiftS ζ (hat M.ι (C ω * logS) M.w))
      (by rw [← (sh _).2, ← g0])
    rw [← eu] at e2
    refine solution_unique h1 h2 h3 h4 h6 ?_ ?_ (norm_constantCoeff_shift_lt hζ hw cw) e1 e2
    · rw [hc, zero_add]; exact hup
    · rw [hc, zero_add]; exact hwp

end GlobalTheory.MomOne.SmallTranslate
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ), M.MChart ω → M.At ω ζ p → hat M.ι (C ω * logS) (fun z => M.u (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.u) ∧ hat M.ι (C ω * logS) (fun z => M.w (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.w) := by
  atlas_forward_decl GlobalTheory.MomOne.SmallTranslate.shift_eq_translate
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Transfer
variable {q : ℕ} [Fact q.Prime]

def Tr (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (p : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ (fun z => F (z + p)) 0 ∧ Bdd (hat ι ℓ F) ∧
    hat ι ℓ (fun z => F (z + p)) = shiftS ζ (hat ι ℓ F)

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).1⟩

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).2⟩

section
variable {ι : ℂ ≃+* ℂ_[q]} {ℓ : ℂ_[q]⟦X⟧} {ζ : ℂ_[q]} {p : ℂ}

lemma Tr.const (h0 : constantCoeff ℓ = 0) (c : ℂ) : Tr ι ℓ ζ p (fun _ => c) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).2.1 c
  refine ⟨analyticAt_const, analyticAt_const, ⟨‖ι c‖, fun n => ?_⟩, ?_⟩
  · rw [h, coeff_C]
    split_ifs <;> simp
  · rw [h, Shift.shiftS_C]

lemma Tr.add (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z + G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.add g1, f2.add g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).1]; exact bdd_add f3 g3
  · rw [(h _ _ f1 g1).1, (h _ _ f2 g2).1, f4, g4, Shift.shiftS_add hζ f3 g3]

lemma Tr.mul (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z * G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.mul g1, f2.mul g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).2.1]; exact bdd_mul f3 g3
  · rw [(h _ _ f1 g1).2.1, (h _ _ f2 g2).2.1, f4, g4, Shift.shiftS_mul hζ f3 g3]

lemma Tr.pow (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F : ℂ → ℂ} (hF : Tr ι ℓ ζ p F) (n : ℕ) :
    Tr ι ℓ ζ p (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 1
  | succ n ih => simpa only [pow_succ] using Tr.mul h0 hζ ih hF

lemma Tr.sum (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) (F : ℕ → ℂ → ℂ) (hF : ∀ i, Tr ι ℓ ζ p (F i))
    (n : ℕ) : Tr ι ℓ ζ p (fun z => ∑ i ∈ Finset.range n, F i z) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 0
  | succ n ih => simpa only [Finset.sum_range_succ] using Tr.add h0 hζ ih (hF n)

lemma exists_homog (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {u w : ℂ → ℂ} (hu : Tr ι ℓ ζ p u)
    (hw : Tr ι ℓ ζ p w) (A : Polynomial ℂ) :
    ∃ (k : ℕ) (F : ℂ → ℂ), Tr ι ℓ ζ p F ∧ ∀ z x : ℂ, x * w z = u z → F z = A.eval x * w z ^ k := by
  refine ⟨A.natDegree, fun z => ∑ i ∈ Finset.range (A.natDegree + 1),
    A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)), ?_, fun z x hx => ?_⟩
  · exact Tr.sum h0 hζ (fun i z => A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)))
      (fun i => Tr.mul h0 hζ (Tr.const h0 _) (Tr.mul h0 hζ (hu.pow h0 hζ i) (hw.pow h0 hζ _))) _
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi'
    rw [← hx, hj, Nat.add_sub_cancel_left]
    ring

lemma exists_quot (h0 : constantCoeff ℓ = 0) (h1 : coeff 1 ℓ ≠ 0) {f D N : ℂ → ℂ} (S : ℂ_[q]⟦X⟧)
    (hf : MeromorphicAt f 0) (hD : AnalyticAt ℂ D 0) (hN : AnalyticAt ℂ N 0)
    (hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0) (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z * D z = N z)
    (hS : S * hat ι ℓ D = hat ι ℓ N) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
  obtain ⟨h, hc, hid, hcc, -⟩ := TaylorRead.hat_laws q ι ℓ h0
  have hDne : hat ι ℓ D ≠ 0 := by
    intro hz
    have e : hat ι ℓ D = hat ι ℓ (fun _ => 0) := by rw [hz, hc]; simp
    have e2 := (h _ _ hD analyticAt_const).2.2.2 h1 e
    obtain ⟨z, hz1, hz2⟩ := (hD0.and (e2.filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  have hpow : ∀ n : ℕ, hat ι ℓ (fun z => z ^ n) = ℓ ^ n := by
    intro n
    induction n with
    | zero => simpa using hc 1
    | succ n ih =>
      simp only [pow_succ]
      rw [(h (fun z => z ^ n) (fun z => z) (by fun_prop) (by fun_prop)).2.1, ih, hid]
  have key : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      hat ι ℓ g = ℓ ^ n * S := by
    intro n g hg hge
    apply mul_right_cancel₀ hDne
    rw [mul_assoc, hS, ← hpow, ← (h _ _ hg hD).2.1, ← (h (fun z => z ^ n) N (by fun_prop) hN).2.1]
    refine (h _ _ (hg.mul hD) (AnalyticAt.mul (by fun_prop) hN)).2.2.1 ?_
    filter_upwards [hge, he] with z a b
    show g z * D z = z ^ n * N z
    rw [a, ← b, mul_assoc]
  have main : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
    intro n
    induction n with
    | zero =>
      intro g hg hge
      exact ⟨g, hg, by simpa using hge, by simpa using key 0 g hg hge⟩
    | succ n ih =>
      intro g hg hge
      have hg0 : g 0 = 0 := by
        have := congrArg constantCoeff (key _ g hg hge)
        rw [hcc] at this
        simpa [h0] using this
      obtain ⟨s, hs⟩ := hg
      refine ih (dslope g 0) ⟨_, hs.has_fpower_series_dslope_fslope⟩ ?_
      filter_upwards [hge, self_mem_nhdsWithin] with z a hz
      have hz' : z ≠ 0 := hz
      rw [dslope_of_ne _ hz', slope_def_field, hg0, a]
      field_simp
      ring
  obtain ⟨n, hn⟩ := hf
  exact main n _ hn (Filter.Eventually.of_forall fun z => by simp)
end

lemma x_ne (M : Mdl q) (hM : M.Ok) (c z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, M.x z - c ≠ 0 := by
  obtain ⟨-, -, hx, -, u0, w0, du, -, hs⟩ := uw_elliptic_flow q M hM
  have hm : Meromorphic (fun z => M.x z - c) := fun z => (hx.1 z).sub (MeromorphicAt.const c z)
  have h0 : meromorphicOrderAt (fun z => M.x z - c) 0 ≠ ⊤ := by
    intro ht
    rw [meromorphicOrderAt_eq_top_iff] at ht
    obtain ⟨au, aw, -, -, e1, e2⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
    have dw : deriv M.w 0 = 0 := by
      have := e2.self_of_nhds.2.2
      simpa [u0, w0] using this
    have e3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u z = c * M.w z := by
      filter_upwards [ht, e1] with z a b
      rw [← b.2.2.1, sub_eq_zero.mp a]
    have e4 : M.u =ᶠ[𝓝 0] fun z => c * M.w z := by
      rw [eventually_nhdsWithin_iff] at e3
      filter_upwards [e3] with z a
      by_cases hz : z = 0
      · simp [hz, u0, w0]
      · exact a hz
    have := e4.deriv_eq
    rw [du, deriv_const_mul _ aw.differentiableAt, dw, mul_zero] at this
    exact hM.1 this
  have h1 := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩ z₀
  rcases (hm z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h) h1
  · exact h

lemma tendsto_add_punct (p : ℂ) : Filter.Tendsto (fun z : ℂ => z + p) (𝓝[≠] 0) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 (0 + p)) :=
      (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem shift_eq_hat_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  intro q _ M ω ζ p φ hch hat' hφ hφ0 hφb
  have hM : M.Ok := hch.1
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hζ : ‖ζ - 1‖ < 1 := hat'.2.1
  obtain ⟨h1, v, xs, ys, -, -, bys, -, -, cys, -, hwy, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hch
  obtain ⟨tu, tw⟩ := GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hch hat'
  obtain ⟨m, P, A, B, -, hAB⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hM hφ
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := uw_elliptic_flow q M hM
  obtain ⟨au0, aw0, -, -, e0, -⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨aup, awp, -, -, ep, -⟩ := hs p hat'.1
  have htr : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu : Tr M.ι (C ω * logS) ζ p M.u :=
    ⟨au0, aup.comp_of_eq htr (zero_add p), ⟨1, hch.2.2.1⟩, tu⟩
  have hw : Tr M.ι (C ω * logS) ζ p M.w := by
    refine ⟨aw0, awp.comp_of_eq htr (zero_add p), ⟨1, ?_⟩, tw⟩
    refine (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 bys cys ?_
    rw [pow_zero, one_mul, mul_comm, hwy]
    intro n
    rw [map_neg, norm_neg, coeff_X_pow]
    split_ifs <;> simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hQ
  obtain ⟨a, FQ, tQ, eQ⟩ := exists_homog h0 hζ hu hw Q
  obtain ⟨b, FA, tA, eA⟩ := exists_homog h0 hζ hu hw A
  obtain ⟨c, FB, tB, eB⟩ := exists_homog h0 hζ hu hw B
  have tD : Tr M.ι (C ω * logS) ζ p (fun z => FQ z * M.w z ^ (b + c + 1)) :=
    tQ.mul h0 hζ (hw.pow h0 hζ _)
  have tN : Tr M.ι (C ω * logS) ζ p
      (fun z => M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b))) :=
    (hw.pow h0 hζ _).mul h0 hζ ((tA.mul h0 hζ (hw.pow h0 hζ _)).add h0 hζ
      ((Tr.const h0 (-1)).mul h0 hζ (tB.mul h0 hζ (hw.pow h0 hζ _))))
  have hid : ∀ z, (z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) →
      φ z * Q.eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z →
      φ z * (FQ z * M.w z ^ (b + c + 1)) =
        M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b)) := by
    intro z e1 e2
    rw [eQ z _ e1.2.2.1, eA z _ e1.2.2.1, eB z _ e1.2.2.1, ← e1.2.2.2]
    linear_combination M.w z ^ (a + b + c + 1) * e2
  have h := (TaylorRead.hat_laws q M.ι _ h0).1
  refine exists_quot h0 h1 _ ?_ tD.2.1 tN.2.1 ?_ ?_ ?_
  · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + p) (hφ.1 _) htr
  · have hQ0 : ∀ᶠ z in 𝓝[≠] p, ∀ i, M.x z - M.x (P i) ≠ 0 :=
      Filter.eventually_all.2 fun i => x_ne M hM _ p
    refine (tendsto_add_punct p).eventually (p := fun z => FQ z * M.w z ^ (b + c + 1) ≠ 0) ?_
    filter_upwards [hQ0, ep] with z a1 a2
    have hw0 : M.w z ≠ 0 := by
      intro hz
      have := a2.2.2.2
      rw [hz] at this
      simp at this
    rw [eQ z _ a2.2.2.1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hw0)) (pow_ne_zero _ hw0)
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using a1 i
  · exact (tendsto_add_punct p).eventually ((ep.and (hAB p)).mono fun z hz => hid z hz.1 hz.2)
  · rw [tD.2.2.2, tN.2.2.2, ← Shift.shiftS_mul hζ hφb tD.2.2.1, ← (h _ _ hφ0 tD.1).2.1]
    congr 1
    exact (h _ _ (hφ0.mul tD.1) tN.1).2.2.1 ((e0.and (hAB 0)).mono fun z hz => hid z hz.1 hz.2)

end GlobalTheory.MomOne.Transfer
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  atlas_forward_decl GlobalTheory.MomOne.Transfer.shift_eq_hat_translate
end

section
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.AtAdd

variable {q : ℕ} [Fact q.Prime]

open Classical in

theorem sub_mem_of_uw (M : Mdl q) (hM : M.Ok) (s t : ℂ) (ht : t ∉ M.L.lattice) (hy : M.y t ≠ 0)
    (hu : M.u s = M.u t) (hw : M.w s = M.w t) : s - t ∈ M.L.lattice := by
  have hwt : M.w t = -1 / M.y t := by simp [Mdl.w, ht]
  have hwt0 : M.w t ≠ 0 := by rw [hwt]; exact div_ne_zero (by norm_num) hy
  have hs : s ∉ M.L.lattice := by
    intro hs
    apply hwt0
    rw [← hw]; simp [Mdl.w, hs]
  have hws : M.w s = -1 / M.y s := by simp [Mdl.w, hs]
  have hys : M.y s ≠ 0 := by
    intro h
    apply hwt0
    rw [← hw, hws, h, div_zero]
  have hyy : M.y s = M.y t := by
    rw [hws, hwt, div_eq_div_iff hys hy] at hw
    linear_combination hw
  have hxx : M.x s = M.x t := by
    have h1 : M.u s = -M.x s / M.y s := by simp [Mdl.u, hs]
    have h2 : M.u t = -M.x t / M.y t := by simp [Mdl.u, ht]
    rw [h1, h2, hyy, div_left_inj' hy] at hu
    exact neg_injective hu
  obtain ⟨φ, -, hk, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨h1, e1⟩ := hφ s hs
  obtain ⟨h2, e2⟩ := hφ t ht
  rw [← hk, map_sub, e1, e2, sub_eq_zero]
  congr 1 <;> simp [hxx, hyy]

theorem sub_mem_of_germ (M : Mdl q) (hM : M.Ok) (α s t : ℂ) (hα : α ≠ 0) (ht : M.Small t)
    (hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u (α * z + s) = M.u (α * z + t))
    (hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.w (α * z + s) = M.w (α * z + t)) : s - t ∈ M.L.lattice := by
  have hg := ((uw_elliptic_flow q M hM).2.2.2.2.2.2.2.2 t ht).2.2.2.2.1
  have htend : Filter.Tendsto (fun z : ℂ => α * z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun z : ℂ => α * z + t) := by fun_prop
      simpa using hc.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hα] using hz
  obtain ⟨z, h1, h2, h3⟩ := ((htend.eventually hg).and (hu.and hw)).exists
  have := sub_mem_of_uw M hM _ _ h1.1 h1.2.1 h2 h3
  simpa using this

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  simp [logS, ← coeff_zero_eq_constantCoeff_apply]

theorem bd_w (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (h : M.Chart ℓ) : Bd 1 (hat M.ι ℓ M.w) := by
  obtain ⟨-, v, xs, ys, -, -, hys, -, -, hc, -, hw, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ h
  apply (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 hys hc
  rw [pow_zero, one_mul, mul_comm, hw]
  intro n
  rw [map_neg, norm_neg, coeff_X_pow]
  split_ifs <;> simp

theorem germ_add (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (ζ ζ' : ℂ_[q]) (p p' t : ℂ) (h : M.At ω ζ p) (h' : M.At ω ζ' p') (ht : M.At ω (ζ * ζ') t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (1 * z + (p + p')) = F (1 * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hEp : Ell M.L (fun z => F (z + p)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (x + p)).comp_analyticAt (f := F) (g := fun z => z + p) (by fun_prop)
    · show F (z + l + p) = F (z + p)
      rw [add_right_comm, hE.2 l hl]
  have hBp : Bdd (hat M.ι (C ω * logS) (fun z => F (z + p))) := by
    rw [hT ζ p h]
    exact ⟨1, (Shift.shift_laws q ζ h.2.1).1 _ _ hB⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ' p' _ hM h' hEp (han p h.1) hBp
  rw [hT ζ p h, (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).1 ζ' ζ _ h'.2.1 h.2.1 ⟨1, hB⟩, mul_comm ζ' ζ, ← hT _ t ht] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa (han t ht.1)).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [one_mul, ← e2, e1]
  congr 1; ring

theorem germ_mul (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p t : ℂ)
    (hL : ∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) (hα : M.ι α = zc a)
    (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hζ : ζ ^ (q ^ n) = 1)
    (h : M.At ω ζ p) (ht : M.At ω (ζ ^ k) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z + α * p) = F (α * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hF0 : AnalyticAt ℂ F 0 := hA 0 (Or.inl (zero_mem _))
  have hmul : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → AnalyticAt ℂ (fun z => G (α * z)) 0 := fun G hG =>
    AnalyticAt.comp_of_eq (g := G) (f := fun z => α * z) hG (by fun_prop) (by simp)
  have hEα : Ell M.L (fun z => F (α * z)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (α * x)).comp_analyticAt (f := F) (g := fun z => α * z) (by fun_prop)
    · show F (α * (z + l)) = F (α * z)
      rw [mul_add, hE.2 _ (hL l hl)]
  have hsub := (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω F hF0).2.2.1 α a hα
  have hm := (MulSeries.mulS_laws q).1 a
  have hBα : Bdd (hat M.ι (C ω * logS) (fun z => F (α * z))) := by
    rw [hsub]
    exact ⟨1, (sup_norm_laws q).2.1 _ _ _ hB hm.1 hm.2.1⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ p _ hM h hEα (hmul F hF0) hBα
  rw [hsub, ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n k a _ hζ hk ⟨1, hB⟩).2, ← hT _ t ht,
    ← (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω _ (han t ht.1)).2.2.1 α a hα] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa
    (hmul _ (han t ht.1))).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [← mul_add, ← e1, e2]

theorem norm_mul_sub_one_lt {ζ ξ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (h' : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = (ζ - 1) * (ξ - 1) + ((ζ - 1) + (ξ - 1)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h h'.le
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h')

theorem norm_pow_sub_one_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih h

theorem at_add_and_mul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  intro q _ M ω hM
  have hOk : M.Ok := hM.1
  obtain ⟨hex, -, -, hiff, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨hEu, hEw, -, -, -, -, -, -, hS⟩ := uw_elliptic_flow q M hOk
  have hBu : Bd 1 (hat M.ι (C ω * logS) M.u) := hM.2.2.1
  have hBw := bd_w M _ hM
  have hTu := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).1
  have hTw := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).2
  refine ⟨fun ζ ζ' p p' h h' => ?_, fun α a n k ζ p hL hα hk hζ h => ?_⟩
  · obtain ⟨t, ht⟩ := hex _ (norm_mul_sub_one_lt h.2.1 h'.2.1)
    have := sub_mem_of_germ M hOk 1 (p + p') t one_ne_zero ht.1
      (germ_add M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu ζ ζ' p p' t h h' ht)
      (germ_add M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw ζ ζ' p p' t h h' ht)
    refine (hiff _ t _ ht).2 ?_
    simpa using neg_mem this
  · by_cases h0 : α = 0
    · subst h0
      have ha : a = 0 := by
        have := (MulSeries.mulS_laws q).2.2.2.2.2 a
        rw [← hα, map_zero, norm_zero] at this
        exact norm_eq_zero.1 this.symm
      subst ha
      rw [zero_sub, norm_neg] at hk
      have hd : ((q : ℤ) ^ n) ∣ (k : ℤ) := by
        rw [← PadicInt.norm_int_le_pow_iff_dvd]
        simpa using hk
      have hd' : q ^ n ∣ k := by exact_mod_cast hd
      obtain ⟨m, rfl⟩ := hd'
      rw [pow_mul, hζ, one_pow, zero_mul]
      exact h10
    · obtain ⟨t, ht⟩ := hex _ (norm_pow_sub_one_lt h.2.1 k)
      have := sub_mem_of_germ M hOk α (α * p) t h0 ht.1
        (germ_mul M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu α a n k ζ p t hL hα hk hζ h ht)
        (germ_mul M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw α a n k ζ p t hL hα hk hζ h ht)
      refine (hiff _ t _ ht).2 ?_
      simpa using neg_mem this

end GlobalTheory.MomOne.AtAdd
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeCoord_add_and_complexMul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  atlas_forward_decl GlobalTheory.MomOne.AtAdd.at_add_and_mul
end
