import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMRankOne
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem linStep_mem {α γ y x : Γ} {n : ℕ}
    (hx : α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n}) {t : L}
    (ht : T.red α * T.red F.u ^ n * t ^ p ^ F.a - T.red γ * t +
      T.coeff (α * F.φ x - γ * x - y) n = 0) :
    α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y ∈
      Ideal.span {T.π ^ (n + 1)} := by
  obtain ⟨z, hz⟩ := T.mem_span_pow.1 hx
  have he : T.coeff (α * F.φ x - γ * x - y) n = T.red z := by
    rw [hz]; simpa using T.coeff_π_pow_mul_add n z 0
  have hred : T.red (z + α * (F.u ^ n * T.teich (t ^ p ^ F.a)) - γ * T.teich t) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, map_mul, map_pow, T.red_teich, T.red_teich, ← he]
    linear_combination ht
  obtain ⟨z', hz'⟩ := T.red_eq_zero_iff.1 hred
  have : α * F.φ (x + T.π ^ n * T.teich t) - γ * (x + T.π ^ n * T.teich t) - y =
      T.π ^ (n + 1) * z' := by
    rw [map_add, F.φ_π_pow_mul_teich, pow_succ, mul_assoc, ← hz']
    linear_combination hz
  rw [this]; exact T.π_pow_mul_mem le_rfl _

def linApprox (α γ y : Γ) (r : ℕ → L → L) : ℕ → Γ
  | 0 => 0
  | n + 1 => linApprox α γ y r n + T.π ^ n * T.teich (r n
      (T.coeff (α * F.φ (linApprox α γ y r n) - γ * linApprox α γ y r n - y) n))

def linCoeff (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) : L :=
  r n (T.coeff (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) n)

theorem linApprox_eq_finSum (α γ y : Γ) (r : ℕ → L → L) (n : ℕ) :
    F.linApprox α γ y r n = T.finSum (F.linCoeff α γ y r) n := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => rw [T.finSum_succ, ← ih]; rfl

variable {F}

theorem linApprox_mem {α γ y : Γ} {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0) (n : ℕ) :
    α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y ∈ Ideal.span {T.π ^ n} := by
  induction n with
  | zero => simp [linApprox]
  | succ n ih => exact F.linStep_mem ih (hr n _)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob}

theorem linCoeff_weight_le (ha : 0 < F.a) {α γ y : Γ} (hα : α ∈ T.int) {r : ℕ → L → L}
    (hr : ∀ n e, T.red α * T.red F.u ^ n * r n e ^ p ^ F.a - T.red γ * r n e + e = 0)
    (hα1 : ‖T.red α‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : ConvergesAt (T.zcoeff γ) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) {Y : ℝ} (hY : 0 ≤ Y)
    (hγY : gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1))
    (hyY : gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a) (n : ℕ) :
    ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  set q := p ^ F.a with hqdef
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨hs, hsY⟩ := T.finSum_gaussNorm_le hρ0 hρ1 (F.linCoeff α γ y r) hY n ih
  rw [← F.linApprox_eq_finSum] at hs hsY
  set s := F.linApprox α γ y r n
  set σ := ρ ^ q
  have hσ0 : 0 < σ := pow_pos hρ0 _
  have hσ1 : σ < 1 := pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hσρ : σ ≤ ρ := pow_le_of_le_one hρ0.le hρ1.le (by omega)
  obtain ⟨hφ, hφn⟩ := F.gaussNorm_zcoeff_map hρ0 hρ1 hs
  have hασ := T.convergesAt_of_mem_int hα hσ0 hσ1
  have hαφ := T.convergesAt_zcoeff_mul hσ0 hσ1 hασ hφ
  have hαφn : gaussNorm (T.zcoeff (α * F.φ s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (α * F.φ s)) σ
        ≤ gaussNorm (T.zcoeff α) σ * gaussNorm (T.zcoeff (F.φ s)) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hασ hφ
      _ ≤ 1 * Y ^ q := by
          refine mul_le_mul (T.gaussNorm_le_one_of_mem_int hα hσ0 hσ1.le) ?_
            (gaussNorm_nonneg hσ0) zero_le_one
          rw [hφn]; exact pow_le_pow_left₀ (gaussNorm_nonneg hρ0) hsY _
      _ = Y ^ q := one_mul _
  have hγσ : ConvergesAt (T.zcoeff γ) σ := convergesAt_of_le (T.zcoeff_neg_exists γ) hγ hσ0 hσρ
  have hsσ : ConvergesAt (T.zcoeff s) σ := convergesAt_of_le (T.zcoeff_neg_exists s) hs hσ0 hσρ
  have hyσ : ConvergesAt (T.zcoeff y) σ := convergesAt_of_le (T.zcoeff_neg_exists y) hy hσ0 hσρ
  have hγs := T.convergesAt_zcoeff_mul hσ0 hσ1 hγσ hsσ
  have hγsn : gaussNorm (T.zcoeff (γ * s)) σ ≤ Y ^ q := by
    calc gaussNorm (T.zcoeff (γ * s)) σ
        ≤ gaussNorm (T.zcoeff γ) σ * gaussNorm (T.zcoeff s) σ :=
          T.gaussNorm_zcoeff_mul_le hσ0 hσ1.le hγσ hsσ
      _ ≤ Y ^ (q - 1) * Y :=
          mul_le_mul ((T.gaussNorm_zcoeff_mono hσ0 hσρ hγ).trans hγY)
            ((T.gaussNorm_zcoeff_mono hσ0 hσρ hs).trans hsY) (gaussNorm_nonneg hσ0)
            (pow_nonneg hY _)
      _ = Y ^ q := by rw [← pow_succ]; congr 1; omega
  have hyn : gaussNorm (T.zcoeff y) σ ≤ Y ^ q := (T.gaussNorm_zcoeff_mono hσ0 hσρ hy).trans hyY
  have hn1 := T.convergesAt_zcoeff_neg hσ0 hσ1 hγs
  have hn2 := T.convergesAt_zcoeff_neg hσ0 hσ1 hyσ
  have hc1 := T.convergesAt_zcoeff_add hσ0 hσ1 hαφ hn1
  have hE : α * F.φ s - γ * s - y = (α * F.φ s + -(γ * s)) + -y := by ring
  have hG : gaussNorm (T.zcoeff (α * F.φ s - γ * s - y)) σ ≤ Y ^ q := by
    rw [hE]
    refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hc1 hn2).trans (max_le ?_ ?_)
    · refine (T.gaussNorm_zcoeff_add_le hσ0 hσ1.le hαφ hn1).trans (max_le hαφn ?_)
      exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hγs).trans hγsn
    · exact (T.gaussNorm_zcoeff_neg_le hσ0 hσ1.le hyσ).trans hyn
  have hconv : ConvergesAt (T.zcoeff (α * F.φ s - γ * s - y)) σ := by
    rw [hE]; exact T.convergesAt_zcoeff_add hσ0 hσ1 hc1 hn2
  set e := T.coeff (α * F.φ s - γ * s - y) n
  have hen : ‖e‖ * σ ^ n ≤ Y ^ q := by
    have := T.weight_natCast_le hconv n; rw [zpow_natCast] at this; exact this.trans hG
  have hρn0 : 0 < ρ ^ n := pow_pos hρ0 n
  have hρn1 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  set Y' := Y / ρ ^ n
  have hYY' : Y ≤ Y' := (le_div_iff₀ hρn0).2 (mul_le_of_le_one_right hY hρn1)
  have hY' : 0 ≤ Y' := hY.trans hYY'
  have he' : ‖e‖ ≤ Y' ^ q := by
    rw [div_pow, le_div_iff₀ (pow_pos hρn0 _), ← pow_mul, mul_comm n q, pow_mul]
    exact hen
  have hb : ‖T.red γ‖ ≤ Y' ^ (q - 1) := by
    have h0 := T.weight_natCast_le hγ 0
    simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
    exact h0.trans (hγY.trans (pow_le_pow_left₀ hY hYY' _))
  have hc : ‖T.red α * T.red F.u ^ n‖ = 1 := by rw [norm_mul, norm_pow, F.norm_red_u, one_pow, hα1, one_mul]
  have ht := norm_le_of_root hq hc (hr n e) hY' he' hb
  calc ‖F.linCoeff α γ y r n‖ * ρ ^ n ≤ Y' * ρ ^ n := mul_le_mul_of_nonneg_right ht hρn0.le
    _ = Y := div_mul_cancel₀ Y hρn0.ne'

variable (F)

theorem exists_linear_sol [IsAlgClosed L] (ha : 0 < F.a) {α : Γ} (hα : α ∈ T.int)
    (hα1 : ‖T.red α‖ = 1) (γ y : Γ) :
    ∃ x : Γ, α * F.φ x - γ * x = y ∧ ∀ ρ Y : ℝ, 0 < ρ → ρ < 1 →
      ConvergesAt (T.zcoeff γ) ρ → ConvergesAt (T.zcoeff y) ρ → 0 ≤ Y →
      gaussNorm (T.zcoeff γ) ρ ≤ Y ^ (p ^ F.a - 1) → gaussNorm (T.zcoeff y) ρ ≤ Y ^ p ^ F.a →
      ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y := by
  have hq := F.two_le_q ha
  have hc0 : ∀ n : ℕ, T.red α * T.red F.u ^ n ≠ 0 := fun n => by
    refine mul_ne_zero (norm_ne_zero_iff.1 (by rw [hα1]; exact one_ne_zero))
      (pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [F.norm_red_u]; exact one_ne_zero)))
  choose r hr _ using fun (n : ℕ) (e : L) => exists_root_of_isAlgClosed hq (hc0 n) (T.red γ) e
  refine ⟨T.ofCoeff (F.linCoeff α γ y r), ?_, fun ρ Y hρ0 hρ1 hγ hy hY hγY hyY n => ?_⟩
  · set x := T.ofCoeff (F.linCoeff α γ y r)
    have hall : ∀ n, α * F.φ x - γ * x - y ∈ Ideal.span {T.π ^ n} := fun n => by
      have h1 : x - F.linApprox α γ y r n ∈ Ideal.span {T.π ^ n} := by
        rw [F.linApprox_eq_finSum]; exact T.mk_sub_finSum_mem _ n
      have : α * F.φ x - γ * x - y = (α * F.φ (F.linApprox α γ y r n) - γ * F.linApprox α γ y r n - y) +
          (α * F.φ (x - F.linApprox α γ y r n) - γ * (x - F.linApprox α γ y r n)) := by
        rw [map_sub]; ring
      rw [this]
      exact add_mem (linApprox_mem hr n)
        (sub_mem (Ideal.mul_mem_left _ _ (F.φ_mem_span_pow h1)) (Ideal.mul_mem_left _ _ h1))
    have h0 : α * F.φ x - γ * x - y = 0 := T.eq_of_coeff_eq (funext fun n => by
      rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
    exact sub_eq_zero.1 h0
  · rw [T.coeff_ofCoeff]
    exact linCoeff_weight_le ha hα hr hα1 hρ0 hρ1 hγ hy hY hγY hyY n

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem ofCoeff_add_of_disjoint {f g : ℕ → L} (h : ∀ n, f n = 0 ∨ g n = 0) :
    T.ofCoeff f + T.ofCoeff g = T.ofCoeff (f + g) := by
  have hfin : ∀ n, T.finSum f n + T.finSum g n = T.finSum (f + g) n := fun n => by
    simp only [finSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h i with hi | hi <;> simp [hi]
  have hall : ∀ n, T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) ∈ Ideal.span {T.π ^ n} := by
    intro n
    have : T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) = (T.ofCoeff f - T.finSum f n) +
        (T.ofCoeff g - T.finSum g n) - (T.ofCoeff (f + g) - T.finSum (f + g) n) := by
      rw [← hfin n]; ring
    rw [this]
    exact sub_mem (add_mem (T.mk_sub_finSum_mem f n) (T.mk_sub_finSum_mem g n))
      (T.mk_sub_finSum_mem _ n)
  have h0 : T.ofCoeff f + T.ofCoeff g - T.ofCoeff (f + g) = 0 := T.eq_of_coeff_eq (funext fun n => by
    rw [T.coeff_zero_elem]; exact T.coeff_of_mem_span (hall (n + 1)) n le_rfl)
  exact sub_eq_zero.1 h0

def splitS (θ : ℝ) (x : Γ) : Γ :=
  T.ofCoeff fun n => if ‖T.coeff x n‖ < θ then T.coeff x n else 0

def splitB (θ : ℝ) (x : Γ) : Γ :=
  T.ofCoeff fun n => if ‖T.coeff x n‖ < θ then 0 else T.coeff x n

theorem coeff_splitS (θ : ℝ) (x : Γ) (n : ℕ) :
    T.coeff (T.splitS θ x) n = if ‖T.coeff x n‖ < θ then T.coeff x n else 0 := by
  simp [splitS]

theorem coeff_splitB (θ : ℝ) (x : Γ) (n : ℕ) :
    T.coeff (T.splitB θ x) n = if ‖T.coeff x n‖ < θ then 0 else T.coeff x n := by
  simp [splitB]

theorem splitS_add_splitB (θ : ℝ) (x : Γ) : T.splitS θ x + T.splitB θ x = x := by
  rw [splitS, splitB, T.ofCoeff_add_of_disjoint (fun n => by split_ifs <;> simp)]
  conv_rhs => rw [← T.ofCoeff_coeff x]
  congr 1; funext n; simp only [Pi.add_apply]; split_ifs <;> simp

def den (b : T.B) : ℕ := (IsLocalization.Away.surj T.π b).choose

def num (b : T.B) : Γ := (IsLocalization.Away.surj T.π b).choose_spec.choose

theorem num_spec (b : T.B) : b * algebraMap Γ T.B T.π ^ T.den b = algebraMap Γ T.B (T.num b) :=
  (IsLocalization.Away.surj T.π b).choose_spec.choose_spec

theorem invSelf_pow_mul_pow (N : ℕ) :
    IsLocalization.Away.invSelf T.π ^ N * algebraMap Γ T.B T.π ^ N = 1 := by
  rw [← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow]

theorem eq_num_mul (b : T.B) :
    b = algebraMap Γ T.B (T.num b) * IsLocalization.Away.invSelf T.π ^ T.den b := by
  rw [← T.num_spec, mul_assoc, mul_comm (_ ^ _), T.invSelf_pow_mul_pow, mul_one]

def smallPart (θ : ℝ) (b : T.B) : T.B :=
  algebraMap Γ T.B (T.splitS θ (T.num b)) * IsLocalization.Away.invSelf T.π ^ T.den b

def bigPart (θ : ℝ) (b : T.B) : T.B :=
  algebraMap Γ T.B (T.splitB θ (T.num b)) * IsLocalization.Away.invSelf T.π ^ T.den b

theorem smallPart_add_bigPart (θ : ℝ) (b : T.B) : T.smallPart θ b + T.bigPart θ b = b := by
  rw [smallPart, bigPart, ← add_mul, ← map_add, T.splitS_add_splitB, ← T.eq_num_mul]

theorem mul_pow_eq_of_invSelf {x : Γ} (N : ℕ) :
    (algebraMap Γ T.B x * IsLocalization.Away.invSelf T.π ^ N) * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B x := by
  rw [mul_assoc, T.invSelf_pow_mul_pow, mul_one]

theorem coeffB_smallPart (θ : ℝ) (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    T.coeffB (T.smallPart θ b) n = if ‖T.coeffB b n‖ < θ then T.coeffB b n else 0 := by
  rw [smallPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp [hθ]
  · lift n + T.den b to ℕ using h with k
    rw [zcoeff_natCast, zcoeff_natCast, coeff_splitS]

theorem coeffB_bigPart (θ : ℝ) (b : T.B) (n : ℤ) :
    T.coeffB (T.bigPart θ b) n = if ‖T.coeffB b n‖ < θ then 0 else T.coeffB b n := by
  rw [bigPart, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
  simp only
  rcases lt_or_ge (n + T.den b) 0 with h | h
  · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h]; simp
  · lift n + T.den b to ℕ using h with k
    rw [zcoeff_natCast, zcoeff_natCast, coeff_splitB]

end TeichLift

section Dominate

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem convergesAt_of_norm_le {a b : ℤ → K} {ρ : ℝ} (hρ : 0 < ρ) (h : ∀ n, ‖a n‖ ≤ ‖b n‖)
    (hb : ConvergesAt b ρ) : ConvergesAt a ρ ∧ gaussNorm a ρ ≤ gaussNorm b ρ := by
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hρ n).le)
    (fun n => mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le), ?_⟩
  exact gaussNorm_le fun n =>
    (mul_le_mul_of_nonneg_right (h n) (zpow_pos hρ n).le).trans (hb.le_gaussNorm n)

end Dominate

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem norm_coeffB_smallPart_le {θ : ℝ} (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.smallPart θ b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [T.coeffB_smallPart θ hθ]; split_ifs <;> simp

theorem norm_coeffB_bigPart_le (θ : ℝ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.bigPart θ b) n‖ ≤ ‖T.coeffB b n‖ := by
  rw [T.coeffB_bigPart]; split_ifs <;> simp

theorem norm_coeffB_smallPart_lt {θ : ℝ} (hθ : 0 < θ) (b : T.B) (n : ℤ) :
    ‖T.coeffB (T.smallPart θ b) n‖ < θ := by
  rw [T.coeffB_smallPart θ hθ]; split_ifs with h
  · exact h
  · simpa using hθ

theorem coeffB_bigPart_eq_zero_or (θ : ℝ) (b : T.B) (n : ℤ) :
    T.coeffB (T.bigPart θ b) n = 0 ∨ θ ≤ ‖T.coeffB (T.bigPart θ b) n‖ := by
  rw [T.coeffB_bigPart]; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr (not_lt.1 h)

theorem zcoeff_weight_le {x : Γ} {ρ Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ n : ℕ, ‖T.coeff x n‖ * ρ ^ n ≤ Y) (j : ℤ) : ‖T.zcoeff x j‖ * ρ ^ j ≤ Y := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [T.zcoeff_of_neg _ hj, norm_zero, zero_mul]; exact hY
  · lift j to ℕ using hj
    rw [zcoeff_natCast, zpow_natCast]; exact h j

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem toB_invSelf {v : Γ} (hv : F.u * v = 1) :
    F.toB (IsLocalization.Away.invSelf T.π) =
      IsLocalization.Away.invSelf T.π * algebraMap Γ T.B v := by
  have e1 : algebraMap Γ T.B T.π * algebraMap Γ T.B F.u * F.toB (IsLocalization.Away.invSelf T.π) = 1 := by
    rw [← map_mul, ← F.φ_π, ← F.toB_algebraMap, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have e2 : algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π = 1 :=
    IsLocalization.Away.mul_invSelf T.π
  have e3 : algebraMap Γ T.B F.u * algebraMap Γ T.B v = 1 := by rw [← map_mul, hv, map_one]
  linear_combination (IsLocalization.Away.invSelf T.π * algebraMap Γ T.B v) * e1 -
    (F.toB (IsLocalization.Away.invSelf T.π) * algebraMap Γ T.B F.u * algebraMap Γ T.B v) * e2 -
    F.toB (IsLocalization.Away.invSelf T.π) * e3

theorem exists_sol_big [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {b : T.B} (hbig : ∀ n, T.coeffB b n = 0 ∨ θ ≤ ‖T.coeffB b n‖) :
    ∃ z : T.B, F.toB z - algebraMap Γ T.B T.π ^ c * z = b ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ConvergesAt (T.coeffB b) ρ → ∀ n, ‖T.coeffB z n‖ * ρ ^ n ≤ θ⁻¹ * gaussNorm (T.coeffB b) ρ := by
  by_cases hb0 : b = 0
  · refine ⟨0, by simp [hb0], fun ρ hρ0 _ hb n => ?_⟩
    rw [← map_zero (algebraMap Γ T.B), T.coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
    simp only [Pi.zero_apply, norm_zero, zero_mul]
    exact mul_nonneg (inv_nonneg.2 hθ.le) (gaussNorm_nonneg hρ0)
  obtain ⟨v, hvint, huv, hv1⟩ := F.exists_inv_u
  set N := T.den b
  set x := T.num b
  have hx0 : x ≠ 0 := by
    intro h
    apply hb0
    rw [T.eq_num_mul b]
    change algebraMap Γ T.B x * _ = 0
    rw [h, map_zero, zero_mul]
  obtain ⟨m, x', hxx', hx'0, hz⟩ := T.exists_eq_π_pow_mul hx0
  set α := F.u ^ m * v ^ N
  have hα : α ∈ T.int := mul_mem (pow_mem F.u_mem_int m) (pow_mem hvint N)
  have hα1 : ‖T.red α‖ = 1 := by
    simp only [α, map_mul, map_pow, norm_mul, norm_pow, F.norm_red_u, hv1, one_pow, one_mul]
  obtain ⟨z', hz'eq, hz'b⟩ := F.exists_linear_sol ha hα hα1 (T.π ^ c) x'
  set P : T.B := algebraMap Γ T.B (T.π ^ m) * IsLocalization.Away.invSelf T.π ^ N
  have hP : F.toB P = P * algebraMap Γ T.B α := by
    simp only [P, α, map_mul, map_pow, F.toB_algebraMap, F.φ_π, F.toB_invSelf huv]
    ring
  refine ⟨algebraMap Γ T.B z' * P, ?_, fun ρ hρ0 hρ1 hb n => ?_⟩
  · rw [map_mul, hP, F.toB_algebraMap]
    have : algebraMap Γ T.B (F.φ z') * (P * algebraMap Γ T.B α) -
        algebraMap Γ T.B T.π ^ c * (algebraMap Γ T.B z' * P) =
        algebraMap Γ T.B (α * F.φ z' - T.π ^ c * z') * P := by
      simp only [map_sub, map_mul, map_pow]; ring
    rw [this, hz'eq, T.eq_num_mul b]
    change _ = algebraMap Γ T.B x * _
    simp only [P, hxx', map_mul]; ring
  ·
    have hbx : T.coeffB b = fun k => T.zcoeff x' (k + ((N : ℤ) - m)) := by
      rw [T.coeffB_eq (T.num_spec b)]
      funext k
      change T.zcoeff x (k + N) = _
      rw [hz]
      congr 1; ring
    have hx'c : ConvergesAt (T.zcoeff x') ρ := by
      rw [hbx, convergesAt_shift_iff hρ0] at hb; exact hb
    have hgb : gaussNorm (T.coeffB b) ρ = gaussNorm (T.zcoeff x') ρ * ρ ^ (-((N : ℤ) - m)) := by
      rw [hbx, gaussNorm_shift hρ0]
    set G := gaussNorm (T.zcoeff x') ρ
    have hG : θ ≤ G := by
      have h0 := T.weight_natCast_le hx'c 0
      simp only [Nat.cast_zero, zpow_zero, mul_one, coeff_zero] at h0
      refine le_trans ?_ h0
      have := hbig (((m : ℤ) - N))
      rw [hbx] at this
      simp only [show (m : ℤ) - N + (N - m) = 0 by ring] at this
      rcases this with h | h
      · exfalso; apply hx'0
        have e : T.zcoeff x' 0 = T.red x' := by simpa using T.zcoeff_natCast x' 0
        rw [← e]; exact h
      · have e : T.zcoeff x' 0 = T.red x' := by simpa using T.zcoeff_natCast x' 0
        rwa [e] at h
    set Y := max 1 G
    have hY1 : 1 ≤ Y := le_max_left _ _
    have hYq : 2 ≤ p ^ F.a := F.two_le_q ha
    have hγ : ConvergesAt (T.zcoeff (T.π ^ c)) ρ := by
      rw [zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
    have hγY : gaussNorm (T.zcoeff (T.π ^ c)) ρ ≤ Y ^ (p ^ F.a - 1) := by
      rw [zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_natCast]
      exact (pow_le_one₀ hρ0.le hρ1.le).trans (one_le_pow₀ hY1)
    have hyY : G ≤ Y ^ p ^ F.a := (le_max_right _ _).trans (le_self_pow₀ hY1 (by omega))
    have hw := hz'b ρ Y hρ0 hρ1 hγ hx'c (zero_le_one.trans hY1) hγY hyY
    have hYG : Y ≤ θ⁻¹ * G := by
      refine max_le ?_ ?_
      · rw [le_inv_mul_iff₀ hθ]; simpa using hG
      · exact le_mul_of_one_le_left (hθ.le.trans hG) (one_le_inv₀ hθ |>.2 hθ1)
    have hzc : T.coeffB (algebraMap Γ T.B z' * P) = fun k => T.zcoeff z' (k + ((N : ℤ) - m)) := by
      have : (algebraMap Γ T.B z' * P) * algebraMap Γ T.B T.π ^ N =
          algebraMap Γ T.B (T.π ^ m * z') := by
        simp only [P, map_mul, map_pow]
        rw [show ∀ a b c d : T.B, a * (b * c) * d = a * b * (c * d) by intros; ring,
          T.invSelf_pow_mul_pow, mul_one, mul_comm]
      rw [T.coeffB_eq this]
      funext k
      rw [show k + ((N : ℤ) - m) = k + N - m by ring]
      have := T.zcoeff_π_pow_mul m z' (k + N - m)
      rw [sub_add_cancel] at this
      exact this
    rw [hzc]
    simp only
    have hwz := T.zcoeff_weight_le (zero_le_one.trans hY1) hw (n + ((N : ℤ) - m))
    calc ‖T.zcoeff z' (n + ((N : ℤ) - m))‖ * ρ ^ n
        = (‖T.zcoeff z' (n + ((N : ℤ) - m))‖ * ρ ^ (n + ((N : ℤ) - m))) * ρ ^ (-((N : ℤ) - m)) := by
          rw [mul_assoc, ← zpow_add₀ hρ0.ne', add_neg_cancel_right]
      _ ≤ Y * ρ ^ (-((N : ℤ) - m)) := mul_le_mul_of_nonneg_right hwz (zpow_pos hρ0 _).le
      _ ≤ θ⁻¹ * G * ρ ^ (-((N : ℤ) - m)) := mul_le_mul_of_nonneg_right hYG (zpow_pos hρ0 _).le
      _ = θ⁻¹ * gaussNorm (T.coeffB b) ρ := by rw [hgb]; ring

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

theorem tendsto_mul_pow_pow_sub_one {A θ : ℝ} (hA : 0 ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {Q : ℕ}
    (hQ : 2 ≤ Q) : Tendsto (fun k : ℕ => A ^ k * θ ^ (Q ^ k - 1)) atTop (𝓝 0) := by
  have hQ1 : 1 < Q := by omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, A * θ ^ Q ^ j ≤ 1 / 2 := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul A
    rw [mul_zero] at h1
    obtain ⟨j, hj⟩ := (h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    refine ⟨j, le_trans ?_ hj⟩
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1.le
      (Nat.lt_pow_self hQ1).le) hA
  set B := A * θ ^ Q ^ j
  have hB0 : 0 ≤ B := by positivity
  have hlim : Tendsto (fun k : ℕ => A ^ j * (1 / 2 : ℝ) ^ (k - j)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k - j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat j)
    simpa using this.const_mul (A ^ j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun k => by positivity) ?_
  filter_upwards [eventually_ge_atTop j] with k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hexp : Q ^ j * d ≤ Q ^ (j + d) - 1 := by
    have h1 : d + 1 ≤ Q ^ d := Nat.lt_pow_self hQ1
    have h2 : 1 ≤ Q ^ j := Nat.one_le_pow _ _ (by omega)
    rw [pow_add]
    have : Q ^ j * (d + 1) ≤ Q ^ j * Q ^ d := Nat.mul_le_mul_left _ h1
    rw [mul_add, mul_one] at this
    omega
  calc A ^ (j + d) * θ ^ (Q ^ (j + d) - 1) ≤ A ^ (j + d) * θ ^ (Q ^ j * d) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1.le hexp) (by positivity)
    _ = A ^ j * B ^ d := by rw [pow_add, pow_mul, mul_pow]; ring
    _ ≤ A ^ j * (1 / 2) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hj d) (by positivity)
    _ = A ^ j * (1 / 2) ^ (j + d - j) := by rw [Nat.add_sub_cancel_left]

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem convergesAt_of_norm_coeffB_le {b : T.B} {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ n, ‖T.coeffB b n‖ ≤ θ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB b) ρ := by
  refine convergesAt_of_eventually hρ0 (T.coeffB_neg_exists b) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (θ + 1) by positivity) hρ1
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hn' : K ≤ n := by exact_mod_cast hn
  rw [zpow_natCast]
  calc ‖T.coeffB b n‖ * ρ ^ n ≤ (θ + 1) * ρ ^ K :=
        mul_le_mul (by linarith [h n]) (pow_le_pow_of_le_one hρ0.le hρ1.le hn') (by positivity)
          (by linarith)
    _ ≤ (θ + 1) * (ε / (θ + 1)) := mul_le_mul_of_nonneg_left hK.le (by linarith)
    _ = ε := by field_simp

theorem gaussNorm_pow_le {b : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : ∀ n, ‖T.coeffB b n‖ ≤ θ) {Q : ℕ} (hQ : 1 ≤ Q) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    gaussNorm (T.coeffB b) σ ^ Q ≤ θ ^ (Q - 1) * gaussNorm (T.coeffB b) (σ ^ Q) := by
  have hρ0 : 0 < σ ^ Q := pow_pos hσ0 Q
  have hρ1 : σ ^ Q < 1 := pow_lt_one₀ hσ0.le hσ1 (by omega)
  have hc := T.convergesAt_of_norm_coeffB_le hθ0 h hρ0 hρ1
  set X := θ ^ (Q - 1) * gaussNorm (T.coeffB b) (σ ^ Q)
  have hX : 0 ≤ X := mul_nonneg (pow_nonneg hθ0 _) (gaussNorm_nonneg hρ0)
  have hQ0 : Q ≠ 0 := by omega
  have hterm : ∀ n : ℤ, ‖T.coeffB b n‖ * σ ^ n ≤ X ^ ((Q : ℝ)⁻¹) := by
    intro n
    have ha : 0 ≤ ‖T.coeffB b n‖ * σ ^ n := mul_nonneg (norm_nonneg _) (zpow_pos hσ0 n).le
    have hpow : (‖T.coeffB b n‖ * σ ^ n) ^ Q ≤ X := by
      have e : (‖T.coeffB b n‖ * σ ^ n) ^ Q =
          ‖T.coeffB b n‖ ^ (Q - 1) * (‖T.coeffB b n‖ * (σ ^ Q) ^ n) := by
        rw [mul_pow, ← zpow_natCast (σ ^ n), ← zpow_mul, ← zpow_natCast σ Q, ← zpow_mul,
          mul_comm n]
        rw [show ‖T.coeffB b n‖ ^ Q = ‖T.coeffB b n‖ ^ (Q - 1) * ‖T.coeffB b n‖ by
          rw [← pow_succ]; congr 1; omega]
        ring
      rw [e]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h n) _) (hc.le_gaussNorm n)
        (mul_nonneg (norm_nonneg _) (zpow_pos hρ0 n).le) (pow_nonneg hθ0 _)
    calc ‖T.coeffB b n‖ * σ ^ n = ((‖T.coeffB b n‖ * σ ^ n) ^ Q) ^ ((Q : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast ha hQ0).symm
      _ ≤ X ^ ((Q : ℝ)⁻¹) := Real.rpow_le_rpow (pow_nonneg ha _) hpow (by positivity)
  calc gaussNorm (T.coeffB b) σ ^ Q ≤ (X ^ ((Q : ℝ)⁻¹)) ^ Q :=
        pow_le_pow_left₀ (gaussNorm_nonneg hσ0) (gaussNorm_le hterm) _
    _ = X := Real.rpow_inv_natCast_pow hX hQ0

theorem coeffB_invSelf_pow (c : ℕ) :
    T.coeffB (IsLocalization.Away.invSelf T.π ^ c) = fun k => T.zcoeff 1 (k + c) := by
  refine T.coeffB_eq ?_
  rw [T.invSelf_pow_mul_pow, map_one]

theorem gaussNorm_invSelf_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (IsLocalization.Away.invSelf T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (IsLocalization.Away.invSelf T.π ^ c)) ρ = ρ ^ (-(c : ℤ)) := by
  rw [T.coeffB_invSelf_pow, convergesAt_shift_iff hρ0, gaussNorm_shift hρ0, zcoeff_one,
    gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_pow_eq_radius {Q : ℕ} (hQ : 1 ≤ Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ σ ^ Q = ρ :=
  ⟨ρ ^ ((Q : ℝ)⁻¹), Real.rpow_pos_of_pos hρ0 _,
    Real.rpow_lt_one hρ0.le hρ1 (by positivity), Real.rpow_inv_natCast_pow hρ0.le (by omega)⟩

namespace TeichFrob

variable (F : T.TeichFrob)

theorem one_le_q : 1 ≤ p ^ F.a := F.q_pos

theorem convergesAt_toB_of_forall {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB (F.toB z)) ρ := by
  intro ρ hρ0 hρ1
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius F.one_le_q hρ0 hρ1
  exact (F.convergesAt_coeffB_toB_iff hσ0 hσ1 z).2 (hz σ hσ0 hσ1)

theorem convergesAt_toB_iterate_of_forall {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) (k : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB ((⇑F.toB)^[k] z)) ρ := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [Function.iterate_succ_apply']; exact F.convergesAt_toB_of_forall ih

theorem gaussNorm_toB_iterate {z : T.B} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hz : ConvergesAt (T.coeffB z) σ) (k : ℕ) :
    ConvergesAt (T.coeffB ((⇑F.toB)^[k] z)) (σ ^ (p ^ F.a) ^ k) ∧
      gaussNorm (T.coeffB ((⇑F.toB)^[k] z)) (σ ^ (p ^ F.a) ^ k) =
        gaussNorm (T.coeffB z) σ ^ (p ^ F.a) ^ k := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have hk0 : 0 < σ ^ (p ^ F.a) ^ k := pow_pos hσ0 _
    have hk1 : σ ^ (p ^ F.a) ^ k < 1 := pow_lt_one₀ hσ0.le hσ1 (pow_pos F.q_pos k).ne'
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    refine ⟨(F.convergesAt_coeffB_toB_iff hk0 hk1 _).2 ih.1, ?_⟩
    rw [F.gaussNorm_coeffB_toB hk0 hk1 ih.1, ih.2, ← pow_mul]

theorem gaussNorm_toB_iterate_le {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) (k : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB ((⇑F.toB)^[k] w)) ρ ∧
      gaussNorm (T.coeffB ((⇑F.toB)^[k] w)) ρ ≤
        θ ^ ((p ^ F.a) ^ k - 1) * gaussNorm (T.coeffB w) ρ := by
  have hQ : 1 ≤ (p ^ F.a) ^ k := Nat.one_le_pow _ _ F.q_pos
  obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius hQ hρ0 hρ1
  obtain ⟨h1, h2⟩ := F.gaussNorm_toB_iterate hσ0 hσ1
    (T.convergesAt_of_norm_coeffB_le hθ0 hw hσ0 hσ1) k
  exact ⟨h1, h2 ▸ T.gaussNorm_pow_le hθ0 hw hQ hσ0 hσ1⟩

def fwd (c : ℕ) (z : T.B) : T.B := IsLocalization.Away.invSelf T.π ^ c * F.toB z

theorem toB_eq_fwd (c : ℕ) (z : T.B) : F.toB z = algebraMap Γ T.B T.π ^ c * F.fwd c z := by
  rw [fwd, ← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]

theorem gaussNorm_fwd_iterate (c : ℕ) {z : T.B}
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB z) ρ) (k : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB ((F.fwd c)^[k] z)) ρ ∧
      gaussNorm (T.coeffB ((F.fwd c)^[k] z)) ρ =
        ρ ^ (-((c * k : ℕ) : ℤ)) * gaussNorm (T.coeffB ((⇑F.toB)^[k] z)) ρ := by
  induction k with
  | zero => intro ρ hρ0 hρ1; simpa using hz ρ hρ0 hρ1
  | succ k ih =>
    intro ρ hρ0 hρ1
    obtain ⟨σ, hσ0, hσ1, rfl⟩ := exists_pow_eq_radius F.one_le_q hρ0 hρ1
    obtain ⟨ih1, ih2⟩ := ih σ hσ0 hσ1
    have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
    have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
    have htw := (F.convergesAt_coeffB_toB_iff hσ0 hσ1 _).2 ih1
    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hq0
    obtain ⟨hm1, hm2⟩ := T.convergesAt_coeffB_mul hq0 hq1 hi1 htw
    have hzk := F.convergesAt_toB_iterate_of_forall hz k σ hσ0 hσ1
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨hm1, ?_⟩
    change gaussNorm (T.coeffB (IsLocalization.Away.invSelf T.π ^ c * F.toB _)) _ = _
    rw [hm2, hi2, F.gaussNorm_coeffB_toB hσ0 hσ1 ih1, ih2, mul_pow,
      ← F.gaussNorm_coeffB_toB hσ0 hσ1 hzk, ← mul_assoc]
    congr 1
    rw [← zpow_natCast σ (p ^ F.a), ← zpow_mul, ← zpow_natCast (σ ^ (-((c * k : ℕ) : ℤ))),
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hσ0.ne']
    congr 1
    push_cast; ring

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_zero_B : T.coeffB 0 = 0 := by
  rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]

theorem gaussNorm_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → T.B) {ρ M : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (h : ∀ i ∈ s, ConvergesAt (T.coeffB (f i)) ρ ∧ gaussNorm (T.coeffB (f i)) ρ ≤ M) :
    ConvergesAt (T.coeffB (∑ i ∈ s, f i)) ρ ∧ gaussNorm (T.coeffB (∑ i ∈ s, f i)) ρ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, T.coeffB_zero_B]
    exact ⟨convergesAt_zero, by simp [gaussNorm, hM]⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨h3, h4⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨h5, h6⟩ := T.convergesAt_coeffB_add hρ0 hρ1 h1 h3
    exact ⟨h5, h6.trans (max_le h2 h4)⟩

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem gaussNorm_fwd_iterate_le (c : ℕ) {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) (k : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.coeffB ((F.fwd c)^[k] w)) ρ ∧
      gaussNorm (T.coeffB ((F.fwd c)^[k] w)) ρ ≤
        ρ ^ (-((c * k : ℕ) : ℤ)) * θ ^ ((p ^ F.a) ^ k - 1) * gaussNorm (T.coeffB w) ρ := by
  obtain ⟨h1, h2⟩ := F.gaussNorm_fwd_iterate c
    (fun σ hσ0 hσ1 => T.convergesAt_of_norm_coeffB_le hθ0 hw hσ0 hσ1) k ρ hρ0 hρ1
  refine ⟨h1, ?_⟩
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (F.gaussNorm_toB_iterate_le hθ0 hw k hρ0 hρ1).2
    (zpow_pos hρ0 _).le

def fwdSum (c : ℕ) (w : T.B) (K : ℕ) : T.B := -∑ k ∈ Finset.range K, (F.fwd c)^[k] w

theorem toB_fwdSum_sub (c : ℕ) (w : T.B) (K : ℕ) :
    F.toB (F.fwdSum c w K) - algebraMap Γ T.B T.π ^ c * F.fwdSum c w K =
      algebraMap Γ T.B T.π ^ c * w - algebraMap Γ T.B T.π ^ c * (F.fwd c)^[K] w := by
  induction K with
  | zero => simp [fwdSum]
  | succ K ih =>
    have e : F.fwdSum c w (K + 1) = F.fwdSum c w K - (F.fwd c)^[K] w := by
      simp only [fwdSum, Finset.sum_range_succ]; ring
    rw [e, map_sub, F.toB_eq_fwd c ((F.fwd c)^[K] w), ← Function.iterate_succ_apply' (F.fwd c)]
    linear_combination ih

theorem gaussNorm_fwdSum_sub_le (c : ℕ) {w : T.B} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hw : ∀ n, ‖T.coeffB w n‖ ≤ θ) {K K' : ℕ} (hKK' : K ≤ K') {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k, K ≤ k → ρ ^ (-((c * k : ℕ) : ℤ)) * θ ^ ((p ^ F.a) ^ k - 1) *
      gaussNorm (T.coeffB w) ρ ≤ M) :
    ConvergesAt (T.coeffB (F.fwdSum c w K' - F.fwdSum c w K)) ρ ∧
      gaussNorm (T.coeffB (F.fwdSum c w K' - F.fwdSum c w K)) ρ ≤ M := by
  have e : F.fwdSum c w K' - F.fwdSum c w K = -∑ k ∈ Finset.Ico K K', (F.fwd c)^[k] w := by
    simp only [fwdSum, Finset.sum_Ico_eq_sub _ hKK']; ring
  rw [e]
  obtain ⟨h1, h2⟩ := T.gaussNorm_finsetSum_le (Finset.Ico K K') (fun k => (F.fwd c)^[k] w) hρ0 hρ1 hM
    fun k hk => by
      obtain ⟨h3, h4⟩ := F.gaussNorm_fwd_iterate_le c hθ0 hw k hρ0 hρ1
      exact ⟨h3, h4.trans (h k (Finset.mem_Ico.1 hk).1)⟩
  obtain ⟨h5, h6⟩ := T.convergesAt_coeffB_neg hρ0 hρ1 h1
  exact ⟨h5, h6 ▸ h2⟩

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

section Seq

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem convergesAt_of_weight_le {a : ℤ → K} {ρ σ Y : ℝ} (hσ0 : 0 < σ) (hσρ : σ < ρ)
    (hneg : ∃ N, ∀ n < N, a n = 0) (h : ∀ n, ‖a n‖ * ρ ^ n ≤ Y) : ConvergesAt a σ := by
  have hρ0 : 0 < ρ := hσ0.trans hσρ
  have hY : 0 ≤ Y := (mul_nonneg (norm_nonneg _) (zpow_pos hρ0 0).le).trans (h 0)
  have hsr0 : 0 ≤ σ / ρ := by positivity
  have hsr1 : σ / ρ < 1 := by rwa [div_lt_one hρ0]
  refine convergesAt_of_eventually hσ0 hneg fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (Y + 1) by positivity) hsr1
  refine ⟨M, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hn' : M ≤ n := by exact_mod_cast hn
  rw [zpow_natCast]
  calc ‖a n‖ * σ ^ n = (‖a n‖ * ρ ^ (n : ℤ)) * (σ / ρ) ^ n := by
        rw [div_pow, zpow_natCast]; field_simp
    _ ≤ Y * (σ / ρ) ^ M :=
        mul_le_mul (h n) (pow_le_pow_of_le_one hsr0 hsr1.le hn') (by positivity) hY
    _ ≤ (Y + 1) * (ε / (Y + 1)) := mul_le_mul (by linarith) hM.le (by positivity) (by linarith)
    _ = ε := by field_simp

end Seq

def fwdConst (q c : ℕ) (ρ : ℝ) : ℝ := ⨆ k : ℕ, ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)

theorem tendsto_fwdConst_terms {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    Tendsto (fun k : ℕ => ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1)) atTop (𝓝 0) := by
  have := tendsto_mul_pow_pow_sub_one (A := (ρ ^ c)⁻¹) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) hq
  refine this.congr fun k => ?_
  rw [inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]

theorem le_fwdConst {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℕ) :
    ρ ^ (-((c * k : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ k - 1) ≤ fwdConst q c ρ :=
  le_ciSup (tendsto_fwdConst_terms hq c hρ0).bddAbove_range k

theorem fwdConst_nonneg {q : ℕ} (hq : 2 ≤ q) (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    0 ≤ fwdConst q c ρ :=
  (by positivity : (0 : ℝ) ≤ ρ ^ (-((c * 0 : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ (q ^ 0 - 1)).trans
    (le_fwdConst hq c hρ0 0)

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem coeffB_invSelf_pow_mul (c : ℕ) (b : T.B) (n : ℤ) :
    T.coeffB (IsLocalization.Away.invSelf T.π ^ c * b) n = T.coeffB b (n + c) := by
  have h : (IsLocalization.Away.invSelf T.π ^ c * b) * algebraMap Γ T.B T.π ^ (T.den b + c) =
      algebraMap Γ T.B (T.num b) := by
    rw [pow_add, ← T.num_spec b]
    calc IsLocalization.Away.invSelf T.π ^ c * b *
          (algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B T.π ^ c)
        = b * algebraMap Γ T.B T.π ^ T.den b *
          (IsLocalization.Away.invSelf T.π ^ c * algebraMap Γ T.B T.π ^ c) := by ring
      _ = _ := by rw [T.invSelf_pow_mul_pow, mul_one]
  rw [T.coeffB_eq h, T.coeffB_eq (T.num_spec b)]
  simp only
  congr 1; push_cast; ring

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem gaussNorm_π_pow (c : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ConvergesAt (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ ∧
      gaussNorm (T.coeffB (algebraMap Γ T.B T.π ^ c)) ρ = ρ ^ c := by
  rw [← map_pow, T.coeffB_algebraMap, zcoeff_π_pow, gaussNorm_pi_single _ _ hρ0]
  exact ⟨convergesAt_pi_single _ _ _, by simp⟩

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_approx_sol [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {d : T.B}
    (hd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB d) ρ) (K : ℕ) :
    ∃ t R : T.B, F.toB t - algebraMap Γ T.B T.π ^ c * t = d - R ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB t) ρ ∧
        gaussNorm (T.coeffB t) ρ ≤
          max 2 (fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ))) * gaussNorm (T.coeffB d) ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB R) ρ ∧
        gaussNorm (T.coeffB R) ρ ≤
          ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) := by
  have hq := F.two_le_q ha
  have hθ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hsd : T.smallPart (1 / 2) d + T.bigPart (1 / 2) d = d := T.smallPart_add_bigPart _ d
  obtain ⟨w, hwdef⟩ : ∃ w, IsLocalization.Away.invSelf T.π ^ c * T.smallPart (1 / 2) d = w :=
    ⟨_, rfl⟩
  have hw : ∀ n, ‖T.coeffB w n‖ ≤ 1 / 2 := fun n => by
    rw [← hwdef, T.coeffB_invSelf_pow_mul]; exact (T.norm_coeffB_smallPart_lt hθ0 d _).le
  have hπw : algebraMap Γ T.B T.π ^ c * w = T.smallPart (1 / 2) d := by
    rw [← hwdef, ← mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  obtain ⟨z, hz, hzb⟩ := F.exists_sol_big ha c hθ0 (by norm_num)
    (T.coeffB_bigPart_eq_zero_or (1 / 2) d)
  refine ⟨z + F.fwdSum c w K, algebraMap Γ T.B T.π ^ c * (F.fwd c)^[K] w, ?_, ?_, ?_⟩
  · have h1 := F.toB_fwdSum_sub c w K
    rw [hπw] at h1
    rw [map_add, ← hsd]
    linear_combination hz + h1
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hbρ, hbρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_bigPart_le (1 / 2) d) hdρ
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ

    obtain ⟨ρ', hρ'0, hρ'1, hρρ'⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧ ρ < ρ' :=
      ⟨(ρ + 1) / 2, by positivity, by linarith, by linarith⟩
    obtain ⟨hbρ', -⟩ := convergesAt_of_norm_le hρ'0 (T.norm_coeffB_bigPart_le (1 / 2) d)
      (hd ρ' hρ'0 hρ'1)
    have hzc : ConvergesAt (T.coeffB z) ρ :=
      convergesAt_of_weight_le hρ0 hρρ' (T.coeffB_neg_exists z) (hzb ρ' hρ'0 hρ'1 hbρ')
    have hzn : gaussNorm (T.coeffB z) ρ ≤ 2 * gaussNorm (T.coeffB d) ρ := by
      refine gaussNorm_le fun n => (hzb ρ hρ0 hρ1 hbρ n).trans ?_
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left hbρn (by norm_num)

    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨hwc, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwc hwn
    have hwd : gaussNorm (T.coeffB w) ρ ≤ ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ := by
      rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
    have hM : 0 ≤ fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ :=
      mul_nonneg (mul_nonneg (fwdConst_nonneg hq c hρ0) (zpow_pos hρ0 _).le) (gaussNorm_nonneg hρ0)
    obtain ⟨hSc, hSn⟩ := F.gaussNorm_fwdSum_sub_le c hθ0.le hw (Nat.zero_le K) hρ0 hρ1 hM
      fun k _ => by
        rw [mul_assoc (fwdConst _ _ _)]
        exact mul_le_mul (le_fwdConst hq c hρ0 k) hwd (gaussNorm_nonneg hρ0)
          (fwdConst_nonneg hq c hρ0)
    have e0 : F.fwdSum c w 0 = 0 := by simp [fwdSum]
    rw [e0, sub_zero] at hSc hSn
    obtain ⟨htc, htn⟩ := T.convergesAt_coeffB_add hρ0 hρ1 hzc hSc
    refine ⟨htc, htn.trans ?_⟩
    rw [max_mul_of_nonneg _ _ (gaussNorm_nonneg hρ0)]
    exact max_le_max hzn (by rw [mul_assoc] at hSn ⊢; exact hSn)
  · intro ρ hρ0 hρ1
    have hdρ := hd ρ hρ0 hρ1
    obtain ⟨hsρ, hsρn⟩ := convergesAt_of_norm_le hρ0 (T.norm_coeffB_smallPart_le hθ0 d) hdρ
    obtain ⟨hi1, hi2⟩ := T.gaussNorm_invSelf_pow c hρ0
    obtain ⟨-, hwn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hi1 hsρ
    rw [hwdef] at hwn
    obtain ⟨hKc, hKn⟩ := F.gaussNorm_fwd_iterate_le c hθ0.le hw K hρ0 hρ1
    obtain ⟨hp1, hp2⟩ := gaussNorm_π_pow (T := T) c hρ0
    obtain ⟨hRc, hRn⟩ := T.convergesAt_coeffB_mul hρ0 hρ1 hp1 hKc
    refine ⟨hRc, ?_⟩
    rw [hRn, hp2]
    calc ρ ^ c * gaussNorm (T.coeffB ((F.fwd c)^[K] w)) ρ
        ≤ ρ ^ c * (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            (ρ ^ (-(c : ℤ)) * gaussNorm (T.coeffB d) ρ)) := by
          refine mul_le_mul_of_nonneg_left (hKn.trans ?_) (pow_pos hρ0 c).le
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hwn, hi2]; exact mul_le_mul_of_nonneg_left hsρn (zpow_pos hρ0 _).le
      _ = ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ := by
          rw [← zpow_natCast ρ c]
          have : ρ ^ (c : ℤ) * ρ ^ (-(c : ℤ)) = 1 := by
            rw [← zpow_add₀ hρ0.ne', add_neg_cancel, zpow_zero]
          linear_combination (ρ ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) *
            gaussNorm (T.coeffB d) ρ) * this

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
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
end
end
