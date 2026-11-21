import Mathlib
import Formalism.PeriodIntegrals.JetsPhW

section
noncomputable section

namespace PI.JetsPhW.Low

variable {K : Type*} [CommRing K]

theorem coeff_pow_eq_zero {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    ∀ (d : ℕ) (e : σ →₀ ℕ), Finsupp.degree e < d → MvPowerSeries.coeff e (A ^ d) = 0
  | 0, e, h => absurd h (Nat.not_lt_zero _)
  | d + 1, e, h => by
    classical
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hx1 : x.1 = 0
    · rw [hx1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    · have h1 : 1 ≤ Finsupp.degree x.1 := by
        rw [Nat.one_le_iff_ne_zero]
        intro h0
        exact hx1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have h2 : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree e := by
        rw [← map_add, hx]
      rw [coeff_pow_eq_zero hA d x.2 (by omega), mul_zero]

theorem const_subst {σ : Type*} {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst A f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [map_pow, hA, zero_pow hd, smul_zero]

theorem coeff_subst_low {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ} (he : e ≠ 0)
    (hd : Finsupp.degree e ≤ 2) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A +
        PowerSeries.coeff 2 f * MvPowerSeries.coeff e (A ^ 2) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_sum_of_support_subset _ (s := ({1, 2} : Finset ℕ)) ?_]
  · rw [Finset.sum_pair (by norm_num), pow_one, smul_eq_mul, smul_eq_mul]
  · intro d hd'
    rw [Function.mem_support] at hd'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hc
    push Not at hc
    apply hd'
    rcases Nat.lt_or_ge d 3 with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, MvPowerSeries.coeff_one, if_neg he, smul_zero]
    · rw [coeff_pow_eq_zero hA d e (by omega), smul_zero]

theorem coeff_subst_of_degree_eq_one {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A := by
  have he : e ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact absurd hd (by norm_num)
  rw [coeff_subst_low hA f he (by omega), coeff_pow_eq_zero hA 2 e (by omega), mul_zero, add_zero]

abbrev E0 : Fin 2 →₀ ℕ := Finsupp.single 0 1
abbrev E1 : Fin 2 →₀ ℕ := Finsupp.single 1 1
abbrev bivariateExponentMonomial : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem degree_expX : Finsupp.degree E0 = 1 := Finsupp.degree_single _ _
theorem degree_expY : Finsupp.degree E1 = 1 := Finsupp.degree_single _ _
theorem degree_expXY : Finsupp.degree bivariateExponentMonomial = 2 := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem expXY_ne_zero : bivariateExponentMonomial ≠ 0 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this

theorem expX_ne_expY : E0 ≠ E1 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this

theorem eq_of_add_eq_expXY {x y : Fin 2 →₀ ℕ} (hxy : x + y = bivariateExponentMonomial) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = E0 ∧ y = E1) ∨ (x = E1 ∧ y = E0) := by
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) hxy
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
  norm_num at h0 h1
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  have hy' : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  rcases Nat.eq_zero_or_pos (x 0) with a0 | a0
  · right
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega
  · left
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega

theorem coeff_expXY_mul {A B : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.coeff bivariateExponentMonomial (A * B) =
      MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B +
        MvPowerSeries.coeff E1 A * MvPowerSeries.coeff E0 B := by
  classical
  rw [MvPowerSeries.coeff_mul]
  have hsub : ({(E0, E1), (E1, E0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) ⊆
      Finset.HasAntidiagonal.antidiagonal bivariateExponentMonomial := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rcases hq with rfl | rfl
    · rfl
    · exact add_comm _ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_pair (fun h => expX_ne_expY (congrArg Prod.fst h))]
  · intro q hq hq'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    by_cases h1 : q.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    by_cases h2 : q.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]
    exfalso
    apply hq'
    rcases eq_of_add_eq_expXY hq h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
    · simp [Prod.ext_iff, a, b]
    · simp [Prod.ext_iff, a, b]

theorem coeff_expX_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E0 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E0 A :=
  coeff_subst_of_degree_eq_one hA f degree_expX

theorem coeff_expY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E1 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E1 A :=
  coeff_subst_of_degree_eq_one hA f degree_expY

theorem coeff_expXY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff bivariateExponentMonomial (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff bivariateExponentMonomial A +
        PowerSeries.coeff 2 f *
          (2 * (MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 A)) := by
  rw [coeff_subst_low hA f expXY_ne_zero (by rw [degree_expXY]), pow_two, coeff_expXY_mul hA hA]
  ring

theorem pcoeff1_subst {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 1 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 A :=
  coeff_subst_of_degree_eq_one (σ := Unit) hA f (Finsupp.degree_single _ _)

theorem pcoeff2_subst {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 2 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 2 A +
        PowerSeries.coeff 2 f * (PowerSeries.coeff 1 A) ^ 2 := by
  have h := coeff_subst_low (σ := Unit) hA f (e := Finsupp.single () 2)
    (by simp) (by rw [Finsupp.degree_single])
  have h2 : PowerSeries.coeff 2 (A ^ 2) = (PowerSeries.coeff 1 A) ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [hA]
    ring
  rw [← h2]
  exact h

end PI.JetsPhW.Low
end
end

section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
end
end

section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

theorem logOk_low {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (h : LogOk l ex) :
    PowerSeries.constantCoeff l = 0 ∧
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 ∧ ‖PowerSeries.coeff 1 ex‖ ≤ 1 := by
  obtain ⟨hex, hsub, v, hvint, hv⟩ := h
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hc := congrArg MvPowerSeries.constantCoeff hsub
    rw [const_subst hex] at hc
    rw [hc]
    exact PowerSeries.constantCoeff_X
  have hl1 : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hsub
    rw [pcoeff1_subst hex l, PowerSeries.coeff_one_X] at hc
    exact hc
  have hv0 : PowerSeries.coeff 0 v * PowerSeries.coeff 1 l = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hv
    simpa [PowerSeries.coeff_mul, dX] using hc
  have hev : PowerSeries.coeff 1 ex = PowerSeries.coeff 0 v := by
    linear_combination PowerSeries.coeff 0 v * hl1 - PowerSeries.coeff 1 ex * hv0
  refine ⟨hl0, hl1, ?_⟩
  rw [hev]
  exact hvint 0

theorem firstJetIntegralGeneral_holds : OneG := by
  intro p _ l ex ph h hp hs
  obtain ⟨_, _, h2⟩ := logOk_low h
  have h1 := (logOk_low h).2.1
  have h0 := (logOk_low h).1
  have hex := h.1
  have hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1 := by simp
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp [Xv]
  have hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X]
  have hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [const_subst hX0]
    exact h0
  have hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) =
      PowerSeries.coeff 1 l := by
    rw [coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]
  have hB0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hBe : MvPowerSeries.coeff (Finsupp.single () 1)
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l := by
    rw [MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]
  have hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [mulBy, const_subst hB0]
    exact hex
  have hAe : MvPowerSeries.coeff (Finsupp.single () 1)
      (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1 := by
    rw [mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]
    linear_combination (-1 : ℂ_[p]) * h1
  have hf : MvPowerSeries.coeff (Finsupp.single () 1)
      (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]
  have hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]
  have hint := hs.2 (Finsupp.single () 1)
  unfold IsIntP at hint
  rw [coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg] at hint
  have hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1 := by
    have h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph) := by
      ring
    rw [h2c, norm_neg, norm_mul, norm_two hp, one_mul] at hint
    exact hint
  show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1
  rw [pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) h2

end PI.JetsPhW.Low
end
end

section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

private lemma coeff_mulBy_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (hlog : LogOk l ex) (c : ℂ_[p])
    {A : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c A) = 0 ∧
      MvPowerSeries.coeff E0 (mulBy l ex c A) = c * MvPowerSeries.coeff E0 A ∧
      MvPowerSeries.coeff E1 (mulBy l ex c A) = c * MvPowerSeries.coeff E1 A := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hI : MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_mul, hAl, mul_zero]
  have e : mulBy l ex c A = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst A l) ex := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, const_subst hI]; exact hlog.1
  · rw [e, coeff_expX_subst hI, MvPowerSeries.coeff_C_mul, coeff_expX_subst hA]
    linear_combination (c * MvPowerSeries.coeff E0 A) * hle
  · rw [e, coeff_expY_subst hI, MvPowerSeries.coeff_C_mul, coeff_expY_subst hA]
    linear_combination (c * MvPowerSeries.coeff E1 A) * hle

private lemma coeff_be_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
    (hlog : LogOk l ex) {A B : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hA1 : MvPowerSeries.coeff E1 A = 0)
    (hB0 : MvPowerSeries.coeff E0 B = 0) :
    MvPowerSeries.coeff E0 (be l ex ph A B) = 0 ∧ MvPowerSeries.coeff E1 (be l ex ph A B) = 0 ∧
      MvPowerSeries.coeff bivariateExponentMonomial (be l ex ph A B) =
        2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B *
          (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex * PowerSeries.coeff 1 l ^ 2 +
            PowerSeries.coeff 2 ph) := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hBl : MvPowerSeries.constantCoeff (PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hB]; exact hl0
  have hS : MvPowerSeries.constantCoeff
      (PowerSeries.subst A l + PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add, hAl, hBl, add_zero]
  have ea : add l ex A B = PowerSeries.subst (PowerSeries.subst A l + PowerSeries.subst B l) ex := rfl
  have hadd : MvPowerSeries.constantCoeff (add l ex A B) = 0 := by
    rw [ea, const_subst hS]; exact hlog.1
  have eb : be l ex ph A B = PowerSeries.subst (add l ex A B) ph - PowerSeries.subst A ph -
      PowerSeries.subst B ph := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eb, map_sub, map_sub, coeff_expX_subst hadd, coeff_expX_subst hA, coeff_expX_subst hB, ea, coeff_expX_subst hS, map_add,
      coeff_expX_subst hA, coeff_expX_subst hB, hB0]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E0 A) * hle
  · rw [eb, map_sub, map_sub, coeff_expY_subst hadd, coeff_expY_subst hA, coeff_expY_subst hB, ea, coeff_expY_subst hS, map_add,
      coeff_expY_subst hA, coeff_expY_subst hB, hA1]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E1 B) * hle
  · rw [eb, map_sub, map_sub, coeff_expXY_subst hadd, coeff_expXY_subst hA, coeff_expXY_subst hB,
      ea, coeff_expXY_subst hS, coeff_expX_subst hS, coeff_expY_subst hS, map_add, map_add, map_add, coeff_expXY_subst hA, coeff_expXY_subst hB,
      coeff_expX_subst hA, coeff_expX_subst hB, coeff_expY_subst hA, coeff_expY_subst hB, hA1, hB0]
    linear_combination (PowerSeries.coeff 1 ph * (MvPowerSeries.coeff bivariateExponentMonomial A + MvPowerSeries.coeff bivariateExponentMonomial B) +
      2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B * PowerSeries.coeff 2 ph *
        (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

theorem secondJetIntegralGeneral_holds : TwoG := by
  intro p _ l ex ph a b hlog hsim
  obtain ⟨hl0, hle, he1⟩ := logOk_low hlog
  have hex0 : PowerSeries.constantCoeff ex = 0 := hlog.1
  have cX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by
    simp [Xv]
  have x00 : MvPowerSeries.coeff E0 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x01 : MvPowerSeries.coeff E1 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x10 : MvPowerSeries.coeff E0 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x11 : MvPowerSeries.coeff E1 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  obtain ⟨ma0, ma1, ma2⟩ := coeff_mulBy_low_degree hlog a (cX 0)
  obtain ⟨mb0, mb1, mb2⟩ := coeff_mulBy_low_degree hlog b (cX 1)
  obtain ⟨u0, u1, u2⟩ := coeff_be_low_degree ph hlog ma0 (cX 1) (by rw [ma2, x01, mul_zero]) x10
  obtain ⟨v0, v1, v2⟩ := coeff_be_low_degree ph hlog (cX 0) mb0 x01 (by rw [mb1, x10, mul_zero])
  set D := (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
    MvPowerSeries (Fin 2) ℂ_[p]) with hD
  have hD0 : MvPowerSeries.constantCoeff D = 0 := hsim.1
  have d0 : MvPowerSeries.coeff E0 D = 0 := by rw [hD, map_sub, u0, v0, sub_zero]
  have d1 : MvPowerSeries.coeff E1 D = 0 := by rw [hD, map_sub, u1, v1, sub_zero]

  have hs : (bivariateExponentMonomial.sum fun _ k => k) = 2 := degree_expXY
  have hexp : MvPowerSeries.coeff bivariateExponentMonomial (expMv D) = MvPowerSeries.coeff bivariateExponentMonomial D := by
    change (∑ n ∈ Finset.range ((bivariateExponentMonomial.sum fun _ k => k) + 1),
      MvPowerSeries.coeff bivariateExponentMonomial (D ^ n) / (n.factorial : ℂ_[p])) = _
    rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_two,
      coeff_expXY_mul hD0 hD0, d0, d1]
    simp [MvPowerSeries.coeff_one, expXY_ne_zero]
  have hint : ‖MvPowerSeries.coeff bivariateExponentMonomial D‖ ≤ 1 := by
    rw [← hexp]; exact hsim.2 bivariateExponentMonomial
  have hjet : jet ex ph 2 = 2 * (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex +
      PowerSeries.coeff 2 ph * PowerSeries.coeff 1 ex ^ 2) := by
    unfold jet
    rw [pcoeff2_subst hex0 ph]
    norm_num
  have hval : MvPowerSeries.coeff bivariateExponentMonomial D = (a - b) * jet ex ph 2 * PowerSeries.coeff 1 l ^ 2 := by
    rw [hD, map_sub, u2, v2, ma1, mb2, x00, x11, hjet]
    linear_combination (-2 * (a - b) * PowerSeries.coeff 2 ph *
      (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

  have hl1 : 1 ≤ ‖PowerSeries.coeff 1 l‖ := by
    have h := congrArg norm hle
    rw [norm_mul, norm_one] at h
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg (PowerSeries.coeff 1 ex), norm_nonneg (PowerSeries.coeff 1 l)]
  rw [hval, norm_mul, norm_pow] at hint
  unfold IsIntP
  have hxy := norm_nonneg ((a - b) * jet ex ph 2)
  have := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hl1) hxy
  linarith

end PI.JetsPhW.Low
end
end
