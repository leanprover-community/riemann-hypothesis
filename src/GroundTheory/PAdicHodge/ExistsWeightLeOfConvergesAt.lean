import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMApprox
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def ConvAll (b : T.B) : Prop := ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB b) ρ

variable {T}

theorem ConvAll.add {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a + b) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_add h0 h1 (ha ρ h0 h1) (hb ρ h0 h1)).1

theorem ConvAll.neg {a : T.B} (ha : T.ConvAll a) : T.ConvAll (-a) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_neg h0 h1 (ha ρ h0 h1)).1

theorem ConvAll.sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem ConvAll.mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a * b) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_mul h0 h1 (ha ρ h0 h1) (hb ρ h0 h1)).1

theorem convAll_π_pow (c : ℕ) : T.ConvAll (algebraMap Γ T.B T.π ^ c) :=
  fun _ h0 _ => (gaussNorm_π_pow c h0).1

theorem convAll_zero : T.ConvAll (0 : T.B) := fun ρ _ _ => by
  rw [T.coeffB_zero_B]; exact convergesAt_zero

theorem convAll_sum {ι : Type*} (s : Finset ι) (f : ι → T.B) (h : ∀ i ∈ s, T.ConvAll (f i)) :
    T.ConvAll (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact convAll_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def ofAll (b : T.B) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt σ :=
  ((⟨b, hb σ σ.2.1 σ.2.2⟩ : T.Econ σ) : T.RobbaExt σ)

theorem ofAll_add {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a + b) (ha.add hb) σ = T.ofAll a ha σ + T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_add]; rfl

theorem ofAll_sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a - b) (ha.sub hb) σ = T.ofAll a ha σ - T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_sub]; rfl

theorem ofAll_mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a * b) (ha.mul hb) σ = T.ofAll a ha σ * T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_mul]; rfl

theorem ofAll_congr {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (h : a = b)
    (σ : Set.Ioo (0 : ℝ) 1) : T.ofAll a ha σ = T.ofAll b hb σ := by
  subst h; rfl

theorem extNorm_ofAll {b : T.B} (hb : T.ConvAll b) {σ : Set.Ioo (0 : ℝ) 1}
    (ρ : Set.Ioc (0 : ℝ) σ) : T.extNorm σ ρ (T.ofAll b hb σ) = gaussNorm (T.coeffB b) ρ :=
  T.extNorm_coe ρ _

theorem res_ofAll {b : T.B} (hb : T.ConvAll b) {σ σ' : Set.Ioo (0 : ℝ) 1} (h : (σ' : ℝ) ≤ σ) :
    T.res h (T.ofAll b hb σ) = T.ofAll b hb σ' := by
  rw [ofAll, res_coe]; rfl

theorem πExt_pow_eq_ofAll (c : ℕ) (σ : Set.Ioo (0 : ℝ) 1) :
    T.πExt σ ^ c = T.ofAll _ (convAll_π_pow c) σ := by
  induction c with
  | zero =>
    rw [pow_zero, ofAll, ← Completion.coe_one]
    congr 1
  | succ c ih =>
    rw [pow_succ, ih, πExt, ofAll, ofAll, ← Completion.coe_mul]
    congr 1

theorem TeichFrob.convAll_toB (F : T.TeichFrob) {b : T.B} (hb : T.ConvAll b) :
    T.ConvAll (F.toB b) := F.convergesAt_toB_of_forall hb

theorem TeichFrob.extFrob_ofAll (F : T.TeichFrob) {b : T.B} (hb : T.ConvAll b)
    (σ : Set.Ioo (0 : ℝ) 1) :
    F.extFrob σ (T.ofAll b hb σ) = T.ofAll (F.toB b) (F.convAll_toB hb) (F.powRadius σ) := by
  rw [ofAll, F.extFrob_coe]; rfl

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_weight_le_of_convergesAt {a : ℤ → L} {ρ : ℝ} (h : ConvergesAt a ρ) {ε : ℝ}
    (hε : 0 < ε) : ∃ K : ℤ, ∀ k, K ≤ k → ‖a k‖ * ρ ^ k ≤ ε := by
  obtain ⟨B, hB⟩ := (h.finite_le hε).bddAbove
  refine ⟨B + 1, fun k hk => ?_⟩
  by_contra hc
  have := hB (show k ∈ {n | ε ≤ ‖a n‖ * ρ ^ n} from (not_le.1 hc).le)
  omega

theorem exists_trunc {τ : ℝ} {b : T.B} (hb : ConvergesAt (T.coeffB b) τ) {ε : ℝ}
    (hε : 0 < ε) : ∃ d : T.B, T.ConvAll d ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ τ →
      ConvergesAt (T.coeffB (b - d)) ρ ∧ gaussNorm (T.coeffB (b - d)) ρ ≤ ε := by
  obtain ⟨K0, hK0⟩ := exists_weight_le_of_convergesAt hb hε
  obtain ⟨M, hMN, hMK⟩ : ∃ M : ℕ, T.den b ≤ M ∧ K0 ≤ (M : ℤ) - T.den b :=
    ⟨T.den b + K0.toNat, by omega, by omega⟩
  refine ⟨algebraMap Γ T.B (T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b, ?_, ?_⟩
  · intro ρ hρ0 hρ1
    refine convergesAt_of_eventually hρ0 (T.coeffB_neg_exists _) fun δ hδ => ⟨(M : ℤ) - T.den b, fun k hk => ?_⟩
    rw [T.coeffB_eq (T.mul_pow_eq_of_invSelf _)]
    simp only
    lift k + (T.den b : ℤ) to ℕ using (by omega) with j hj
    rw [zcoeff_natCast, partialSum, coeff_finSum, if_neg (by omega), norm_zero, zero_mul]
    exact hδ.le
  · have hbd : b - algebraMap Γ T.B (T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b =
        algebraMap Γ T.B (T.num b - T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b := by
      rw [map_sub, sub_mul, ← T.eq_num_mul b]
    have hcb : ∀ k, T.coeffB (b - algebraMap Γ T.B (T.partialSum (T.num b) M) *
        IsLocalization.Away.invSelf T.π ^ T.den b) k =
          if k + (T.den b : ℤ) < M then 0 else T.coeffB b k := by
      intro k
      rw [hbd, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
      simp only
      rcases lt_or_ge (k + (T.den b : ℤ)) 0 with h | h
      · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h, if_pos (by omega)]
      · lift k + (T.den b : ℤ) to ℕ using h with j hj
        rw [zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]
        by_cases hjM : j < M
        · rw [if_pos hjM, if_pos (by exact_mod_cast hjM)]
        · rw [if_neg hjM, if_neg (by exact_mod_cast hjM)]
    intro ρ hρ0 hρτ
    have hbρ : ConvergesAt (T.coeffB b) ρ := convergesAt_of_le (T.coeffB_neg_exists b) hb hρ0 hρτ
    have hle : ∀ k, ‖T.coeffB (b - algebraMap Γ T.B (T.partialSum (T.num b) M) *
        IsLocalization.Away.invSelf T.π ^ T.den b) k‖ ≤ ‖T.coeffB b k‖ := fun k => by
      rw [hcb]; split_ifs <;> simp
    refine ⟨(convergesAt_of_norm_le hρ0 hle hbρ).1, gaussNorm_le fun k => ?_⟩
    rw [hcb]
    split_ifs with hk
    · rw [norm_zero, zero_mul]; exact hε.le
    · have hk0 : 0 ≤ k := by omega
      refine le_trans ?_ (hK0 k (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      lift k to ℕ using hk0
      rw [zpow_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hρ0.le hρτ k

theorem gaussNorm_le_max_of_mem_Icc {b : T.B} {α β σ : ℝ} (hα : 0 < α) (hσ : σ ∈ Set.Icc α β)
    (hbα : ConvergesAt (T.coeffB b) α) (hbβ : ConvergesAt (T.coeffB b) β) :
    gaussNorm (T.coeffB b) σ ≤ max (gaussNorm (T.coeffB b) α) (gaussNorm (T.coeffB b) β) :=
  gaussNorm_le fun n => (weight_le_max_of_mem_Icc hα hσ n).trans
    (max_le_max (hbα.le_gaussNorm n) (hbβ.le_gaussNorm n))

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_approx_convAll {σ : Set.Ioo (0 : ℝ) 1} (z : T.RobbaExt σ) (r : Set.Ioc (0 : ℝ) σ)
    {ε : ℝ} (hε : 0 < ε) : ∃ d : T.B, ∃ hd : T.ConvAll d, ∀ ρ : Set.Ioc (0 : ℝ) σ,
      (r : ℝ) ≤ ρ → T.extNorm σ ρ (z - T.ofAll d hd σ) ≤ ε := by
  obtain ⟨b, hb⟩ := T.exists_approx z r (half_pos hε)
  obtain ⟨d, hd, hbd⟩ := exists_trunc (T := T) (τ := σ) b.2 (half_pos hε)
  refine ⟨d, hd, fun ρ hρ => ?_⟩
  have e : z - T.ofAll d hd σ = (z - b) + ((b : T.RobbaExt σ) - T.ofAll d hd σ) := by ring
  rw [e]
  refine (T.extNorm_add_le ρ _ _).trans (max_le ((hb ρ hρ).le.trans (by linarith)) ?_)
  rw [ofAll, ← Completion.coe_sub, extNorm_coe]
  exact ((hbd ρ ρ.2.1 ρ.2.2).2).trans (by linarith)

theorem exists_tendsto_of_gaussNorm {σ : Set.Ioo (0 : ℝ) 1} (s : ℕ → T.Econ σ)
    (h : ∀ ρ : Set.Ioc (0 : ℝ) σ, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      gaussNorm (T.coeffB ((s m : T.B) - s n)) ρ < ε) :
    ∃ l : T.RobbaExt σ, Tendsto (fun n => (s n : T.RobbaExt σ)) atTop (𝓝 l) := by
  have hs : CauchySeq s := by
    unfold CauchySeq
    change Cauchy (uniformSpace := ⨅ ρ, T.uniformAt σ ρ) _
    have : Nonempty (Set.Ioc (0 : ℝ) σ) := ⟨topRad σ⟩
    rw [cauchy_iInf_uniformSpace]
    intro ρ
    let psm : PseudoMetricSpace (T.Econ σ) := (T.gaussSeminorm σ ρ).toSeminormedRing.toPseudoMetricSpace
    have key : @CauchySeq _ _ psm.toUniformSpace _ s := by
      refine (@Metric.cauchySeq_iff _ _ psm _ _ s).2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := h ρ ε hε
      exact ⟨N, fun m hm n hn => by rw [T.dist_uniformAt']; exact hN m hm n hn⟩
    exact key
  exact cauchySeq_tendsto_of_complete ((Completion.uniformContinuous_coe _).comp_cauchySeq hs)

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_step [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {σ : Set.Ioo (0 : ℝ) 1}
    (z : T.RobbaExt σ) (r : Set.Ioc (0 : ℝ) σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t d R : T.B, T.ConvAll t ∧ T.ConvAll R ∧ ∃ hd : T.ConvAll d,
      F.toB t - algebraMap Γ T.B T.π ^ c * t = d - R ∧
      (∀ ρ : Set.Ioc (0 : ℝ) σ, (r : ℝ) ≤ ρ →
        T.extNorm σ ρ (z - T.ofAll d hd σ) ≤ ε ∧ gaussNorm (T.coeffB R) ρ ≤ ε) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → gaussNorm (T.coeffB t) ρ ≤
        max 2 (fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ))) * gaussNorm (T.coeffB d) ρ) := by
  have hq := F.two_le_q ha
  obtain ⟨d, hd, hzd⟩ := exists_approx_convAll z r hε
  have hr0 : (0 : ℝ) < r := r.2.1
  have hr1 : (r : ℝ) < 1 := rad_lt_one σ r
  set D := max (gaussNorm (T.coeffB d) r) (gaussNorm (T.coeffB d) σ)
  have hD : 0 ≤ D := le_max_of_le_left (gaussNorm_nonneg hr0)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (r : ℝ) ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) * D
      ≤ ε := by
    have := (tendsto_fwdConst_terms hq c hr0).mul_const D
    rw [zero_mul] at this
    exact (this.eventually (ge_mem_nhds hε)).exists
  obtain ⟨t, R, heq, ht, hR⟩ := F.exists_approx_sol ha c hd K
  refine ⟨t, d, R, fun ρ h0 h1 => (ht ρ h0 h1).1, fun ρ h0 h1 => (hR ρ h0 h1).1, hd, heq,
    fun ρ hρ => ⟨hzd ρ hρ, ?_⟩, fun ρ h0 h1 => (ht ρ h0 h1).2⟩
  have hρ0 : (0 : ℝ) < ρ := ρ.2.1
  have hρ1 : (ρ : ℝ) < 1 := rad_lt_one σ ρ
  refine (hR ρ hρ0 hρ1).2.trans (le_trans ?_ hK)
  have hdρ : gaussNorm (T.coeffB d) ρ ≤ D :=
    gaussNorm_le_max_of_mem_Icc hr0 ⟨hρ, ρ.2.2⟩ (hd r hr0 hr1) (hd σ σ.2.1 σ.2.2)
  have hz : (ρ : ℝ) ^ (-((c * K : ℕ) : ℤ)) ≤ (r : ℝ) ^ (-((c * K : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hρ _)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hdρ (gaussNorm_nonneg hρ0)
    (by positivity)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem continuous_extFrob (σ : Set.Ioo (0 : ℝ) 1) : Continuous (F.extFrob σ) :=
  Completion.continuous_map

theorem powRadius_le_self (σ : Set.Ioo (0 : ℝ) 1) : ((F.powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ σ :=
  pow_le_of_le_one σ.2.1.le σ.2.2.le F.q_pos.ne'

def halvedRad (τ : Set.Ioo (0 : ℝ) 1) (N : ℕ) : Set.Ioc (0 : ℝ) τ :=
  ⟨τ * (1 / 2) ^ N, mul_pos τ.2.1 (by positivity),
    mul_le_of_le_one_right τ.2.1.le (pow_le_one₀ (by norm_num) (by norm_num))⟩



end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}


namespace TeichFrob

variable (F : T.TeichFrob)


end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)


end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

variable (T) in

def πTilde : T.RobbaTilde := T.edagToTilde ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
  (T.algebraMap_π_mem_Econ _)⟩

theorem ofRad_πExt (ρ1 : Set.Ioo (0 : ℝ) 1) : T.ofRad ρ1 (T.πExt ρ1) = T.πTilde :=
  (T.edagToTilde_apply (T.algebraMap_π_mem_Econ ρ1)).symm

namespace TeichFrob

variable (F : T.TeichFrob)


end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
