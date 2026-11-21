import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv C q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv C ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C}

def ix (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  Finsupp.single ((0 : Fin 3), i) L + γ.mapDomain (up 2)

theorem index_raise_first (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) :
    ix i L γ ((0 : Fin 3), j) = if j = i then L else 0 := by
  have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  simp only [ix, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, add_zero, Finsupp.single_apply,
    Prod.mk.injEq, true_and]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

def FrobX (V : VF C) (f : PS C 3 dd) : Prop :=
  ∀ p : Fin 3 × Fin dd →₀ ℕ, (∃ j, ¬ V.l ∣ p ((0 : Fin 3), j)) → V.MM (coeff p f)

def FrobD (V : VF C) (f : PS C 3 dd) : Prop := ∀ j : Fin dd, MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), j) f)

private theorem v_natCast_nonneg_of_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

private theorem v_intCast_nonneg' (V : VF C) (a : ℤ) : 0 ≤ V.v (a : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [Int.cast_natCast]
    exact v_natCast_nonneg_of_vf V m
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]
    exact v_natCast_nonneg_of_vf V m

private theorem v_natCast_nonpos_of_not_dvd (V : VF C) (n : ℕ) (hn : ¬ V.l ∣ n) : V.v (n : C) ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have hcop : Nat.Coprime n V.l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hn)
  have hb := Nat.gcd_eq_gcd_ab n V.l
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have h1 : (1 : C) = (n : C) * (Nat.gcdA n V.l : C) + (V.l : C) * (Nat.gcdB n V.l : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    exact_mod_cast this
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  have ha : 0 < V.v ((n : C) * (Nat.gcdA n V.l : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (v_intCast_nonneg' V _)
  have hb' : 0 < V.v ((V.l : C) * (Nat.gcdB n V.l : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact add_pos_of_pos_of_nonneg h01 (v_intCast_nonneg' V _)
  have := lt_of_lt_of_le (lt_min ha hb') (AddValuation.map_add _ _ _)
  rw [← h1, AddValuation.map_one] at this
  exact lt_irrefl _ this

theorem frobX_of {f : PS C 3 dd} (hi : IntS V f) (hd : FrobD V f) : FrobX V f := by
  unfold FrobD MaximalIdealCongruence.MMS at hd
  rintro p ⟨j, hj⟩
  have hp0 : p ((0 : Fin 3), j) ≠ 0 := by
    intro h
    rw [h] at hj
    exact hj (dvd_zero _)
  have h := hd j (p - Finsupp.single ((0 : Fin 3), j) 1)
  have hle : Finsupp.single ((0 : Fin 3), j) 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp0
  rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle] at h
  have hn : ((((p - Finsupp.single ((0 : Fin 3), j) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j)) : ℕ) : C) + 1 =
      (p ((0 : Fin 3), j) : C) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)
  rw [hn] at h
  unfold VF.MM at h ⊢
  rw [AddValuation.map_mul] at h
  by_contra hc
  push_neg at hc
  have := add_le_add hc (v_natCast_nonpos_of_not_dvd V _ hj)
  rw [add_zero] at this
  exact absurd h (not_lt.mpr this)

private theorem mm_add_of_mm_of_mm {V : VF C} {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_finset_sum_of_forall_mm {V : VF C} {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_mm_of_mm hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mms_mul_of_intS_of_mms {V : VF C} {σ : Type} {f h : MvPowerSeries σ C} (hf : IntS V f)
    (hh : MaximalIdealCongruence.MMS V h) : MaximalIdealCongruence.MMS V (f * h) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  apply mm_finset_sum_of_forall_mm
  intro x _
  have h1 := hf x.1
  have h2 := hh x.2
  unfold VF.Ge at h1
  unfold VF.MM at h2 ⊢
  rw [AddValuation.map_mul]
  have h1' : (0 : WithTop ℝ) ≤ V.v (coeff x.1 f) := by simpa using h1
  exact lt_of_lt_of_le h2 (le_add_of_nonneg_left h1')

theorem frobD_mul {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hf' : FrobD V f) (hg' : FrobD V g) :
    FrobD V (f * g) := by
  intro j
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  intro μ
  rw [map_add]
  apply mm_add_of_mm_of_mm
  · exact mms_mul_of_intS_of_mms hf (hg' j) μ
  · exact mms_mul_of_intS_of_mms hg (hf' j) μ

theorem eq_up_of {p : Fin 3 × Fin dd →₀ ℕ} (hp : ∀ j, p ((0 : Fin 3), j) = 0) :
    (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn)).mapDomain (up 2) = p := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    rw [Finsupp.mapDomain_notin_range, hp]
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapDomain_apply (up_inj 2), Finsupp.comapDomain_apply]

theorem coeff_free {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) {p : Fin 3 × Fin dd →₀ ℕ}
    (hp : ∀ j, p ((0 : Fin 3), j) = 0) : coeff p f = if p = 0 then 1 else 0 := by
  classical
  have hs : MvPowerSeries.HasSubst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) := by
    have hz : ∀ q : Fin 3 × Fin dd, constantCoeff (rz (C := C) (dd := dd) 2 q.1 q.2) = 0 := by
      rintro ⟨k, i⟩
      induction k using Fin.cases <;> simp [rz, pt]
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
  have hmon : ∀ d' : Fin 2 × Fin dd →₀ ℕ,
      (d'.prod fun s n => (X s : PS C 2 dd) ^ n) = MvPowerSeries.monomial d' (1 : C) := by
    intro d'
    induction d' using Finsupp.induction with
    | zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]
    | single_add a b g _ _ ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
        Finsupp.prod_single_index (h := fun x n => (X x : PS C 2 dd) ^ n) (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  have inj : Function.Injective (Finsupp.mapDomain (M := ℕ) (up (dd := dd) 2)) :=
    Finsupp.mapDomain_injective (up_inj 2)
  have hprod : ∀ (d : Fin 3 × Fin dd →₀ ℕ) (e : Fin 2 × Fin dd →₀ ℕ),
      coeff e (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) =
        if d = e.mapDomain (up 2) then 1 else 0 := by
    intro d e
    by_cases hx : ∀ j, d ((0 : Fin 3), j) = 0
    · have hd := (eq_up_of hx).symm
      rw [hd, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      show coeff e ((Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)).prod
        fun s n => (X s : PS C 2 dd) ^ n) = _
      rw [hmon, MvPowerSeries.coeff_monomial]
      by_cases he : e = Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)
      · rw [if_pos he, if_pos (by rw [he])]
      · rw [if_neg he, if_neg (fun h => he (inj h).symm)]
    · push_neg at hx
      obtain ⟨j, hj⟩ := hx
      have h0 : (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) = 0 := by
        apply Finset.prod_eq_zero (i := ((0 : Fin 3), j))
        · exact Finsupp.mem_support_iff.mpr hj
        · show (rz (C := C) (dd := dd) 2 0 j) ^ (d ((0 : Fin 3), j)) = 0
          rw [show rz (C := C) (dd := dd) 2 0 j = 0 from rfl, zero_pow hj]
      rw [h0, map_zero, if_neg]
      intro h
      apply hj
      rw [h, Finsupp.mapDomain_notin_range]
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
  have key : ∀ e : Fin 2 × Fin dd →₀ ℕ,
      coeff e (ev (rz (C := C) (dd := dd) 2) f) = coeff (e.mapDomain (up 2)) f := by
    intro e
    show coeff e (MvPowerSeries.subst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) f) = _
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (e.mapDomain (up 2))]
    · rw [hprod, if_pos rfl, smul_eq_mul, mul_one]
    · intro d hd
      rw [hprod, if_neg hd, smul_zero]
  have h2 := key (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn))
  rw [h1, eq_up_of hp, MvPowerSeries.coeff_one] at h2
  rw [← h2]
  by_cases hp0 : p = 0
  · subst hp0
    rw [if_pos rfl, if_pos]
    ext s
    rfl
  · rw [if_neg hp0, if_neg]
    intro h
    apply hp0
    rw [← eq_up_of hp, h, Finsupp.mapDomain_zero]

theorem x_le (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {p : Fin 3 × Fin dd →₀ ℕ} (hp : p ≤ ix i V.l γ)
    (j : Fin dd) (hj : j ≠ i) : p ((0 : Fin 3), j) = 0 := by
  have h := hp ((0 : Fin 3), j)
  rw [index_raise_first, if_neg hj] at h
  exact Nat.le_zero.mp h

private theorem mm_zero' : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_mul_of_mm_of_ge_zero {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem coeff_mul_cong {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hfF : FrobX V f) (hgF : FrobX V g)
    (hf1 : ev (rz 2) f = 1) (hg1 : ev (rz 2) g = 1) (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (coeff (ix i V.l γ) (f * g) - coeff (ix i V.l γ) f - coeff (ix i V.l γ) g) := by
  classical
  unfold FrobX at hfF hgF
  set N := ix i V.l γ with hN
  have hN0 : N ≠ 0 := by
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [hN, index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  have hf0 : coeff 0 f = 1 := by
    have := coeff_free hf1 (p := 0) (fun j => rfl)
    simpa using this
  have hg0 : coeff 0 g = 1 := by
    have := coeff_free hg1 (p := 0) (fun j => rfl)
    simpa using this
  rw [MvPowerSeries.coeff_mul]
  have h1 : ((0 : Fin 3 × Fin dd →₀ ℕ), N) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  have h2 : (N, (0 : Fin 3 × Fin dd →₀ ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal N).erase (0, N) := by
    rw [Finset.mem_erase]
    refine ⟨fun h => hN0 (congrArg Prod.fst h), ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2]
  dsimp only
  rw [hf0, hg0, one_mul, mul_one]
  have e : ∀ A B S : C, A + (B + S) - B - A = S := by
    intros
    ring
  rw [e]
  apply mm_finset_sum_of_forall_mm
  intro x hx
  obtain ⟨hne2, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hne1, hx''⟩ := Finset.mem_erase.mp hx'
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx''
  have ha : x.1 ≤ N := by
    rw [← hsum]
    exact le_self_add
  have hb : x.2 ≤ N := by
    rw [← hsum]
    exact le_add_self
  have ha0 : x.1 ≠ 0 := by
    intro h
    apply hne1
    refine Prod.ext h ?_
    show x.2 = N
    rw [← hsum, h, zero_add]
  have hb0 : x.2 ≠ 0 := by
    intro h
    apply hne2
    refine Prod.ext ?_ h
    show x.1 = N
    rw [← hsum, h, add_zero]
  have hxa : ∀ j, j ≠ i → x.1 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
  have hxb : ∀ j, j ≠ i → x.2 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ hb j hj
  have hti : x.1 ((0 : Fin 3), i) + x.2 ((0 : Fin 3), i) = V.l := by
    have h3 := congrArg (fun p => p ((0 : Fin 3), i)) hsum
    simp only [Finsupp.add_apply] at h3
    rw [h3, hN, index_raise_first, if_pos rfl]
  by_cases hd : V.l ∣ x.1 ((0 : Fin 3), i)
  · obtain ⟨q, hq⟩ := hd
    rcases q with _ | _ | q
    · have hfree : ∀ j, x.1 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simpa using hq
        · exact hxa j hj
      rw [coeff_free hf1 hfree, if_neg ha0, zero_mul]
      exact mm_zero'
    · have hfree : ∀ j, x.2 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simp at hq
          omega
        · exact hxb j hj
      rw [coeff_free hg1 hfree, if_neg hb0, mul_zero]
      exact mm_zero'
    · exfalso
      nlinarith [V.l_prime.pos]
  · exact mm_mul_of_mm_of_ge_zero (hfF x.1 ⟨i, hd⟩) (hg x.2)

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

abbrev p3 (k : Fin 3) : Pt C 3 dd := pt C (n := 3) dd k

theorem z0p3 (k : Fin 3) : ∀ j, constantCoeff ((p3 k : Pt C 3 dd) j) = 0 := by
  intro j
  simp [p3, pt]

theorem pderiv_eval_triple {n : ℕ} {a : Fin 3 → Pt C n dd} (ha : Z0 a) (f : PS C 3 dd) (q : Fin n × Fin dd) :
    pderiv C q (ev a f) = ∑ j, ev a (pderiv C ((0 : Fin 3), j) f) * pderiv C q (a 0 j) +
      ∑ j, ev a (pderiv C ((1 : Fin 3), j) f) * pderiv C q (a 1 j) +
      ∑ j, ev a (pderiv C ((2 : Fin 3), j) f) * pderiv C q (a 2 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 3 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_three]

theorem d_ev_keep {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv C ((0 : Fin 3), i) (B j) = 0) :
    pderiv C ((0 : Fin 3), i) (ev (n := 3) ![p3 0, B] f) = ev (n := 3) ![p3 0, B] (pderiv C ((0 : Fin 2), i) f) := by
  have hz : Z0 (![p3 0, B] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0p3 0 j
    · exact hB j
  rw [pderiv_eval_pair hz]
  refine (congrArg₂ (· + ·) ?_ (Finset.sum_eq_zero fun j _ => ?_)).trans (add_zero _)
  · rw [Finset.sum_eq_single i (fun j _ hj => by
        show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
        rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _
    rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  · show _ * pderiv C _ (B j) = 0
    rw [hd j, mul_zero]

theorem d_ev_keep_iter {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv C ((0 : Fin 3), i) (B j) = 0) (L : ℕ) :
    (pderiv C ((0 : Fin 3), i))^[L] (ev (n := 3) ![p3 0, B] f) =
      ev (n := 3) ![p3 0, B] ((pderiv C ((0 : Fin 2), i))^[L] f) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_ev_keep hB i hd]

def SS (G : FGLaw C dd) : Pt C 3 dd := addOf G.F (p3 1) (p3 2)

theorem triple_sum_constantCoeff (G : FGLaw C dd) (j : Fin dd) : constantCoeff (SS G j) = 0 :=
  const_ev (z0_pp 1 2) (G.const j)

theorem SS_int (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (j : Fin dd) : IntS V (SS G j) :=
  intS_ev (z0_pp 1 2) (fun k m => by fin_cases k <;> exact intS_X _) (hF j)

theorem SS_d (G : FGLaw C dd) (i j : Fin dd) : pderiv C ((0 : Fin 3), i) (SS G j) = 0 := by
  show pderiv C ((0 : Fin 3), i) (ev (n := 3) ![p3 1, p3 2] (G.F j)) = 0
  rw [pderiv_eval_pair (z0_pp 1 2)]
  refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ => ?_) (Finset.sum_eq_zero fun m _ => ?_)).trans
    (add_zero 0)
  · show _ * pderiv C _ (pt C (n := 3) dd 1 m) = 0
    rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  · show _ * pderiv C _ (pt C (n := 3) dd 2 m) = 0
    rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]

theorem triple_point_pderiv_first_zero (k : Fin 3) (hk : k ≠ 0) (i j : Fin dd) : pderiv C ((0 : Fin 3), i) ((p3 k : Pt C 3 dd) j) = 0 := by
  simp [p3, pt, MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff, Ne.symm hk]

def m3 (G : FGLaw C dd) (n : ℕ) : Pt C 3 dd := fun k => ev ![(p3 0 : Pt C 3 dd)] (mulL G.F n k)

theorem triple_multiplication_constantCoeff (G : FGLaw C dd) (n : ℕ) (k : Fin dd) : constantCoeff (m3 G n k) = 0 :=
  const_ev (z0_1 _ (z0p3 0)) (multiplication_constantCoeff_zero G n k)

theorem triple_multiplication_integral (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (n : ℕ) (k : Fin dd) : IntS V (m3 G n k) :=
  intS_ev (z0_1 _ (z0p3 0)) (fun k' m => by fin_cases k'; exact intS_X _) (mulL_int G hF n k)

def UU (Y : FBChart C V O dd) (w : Pt C 3 dd) : PS C 3 dd := ev (n := 3) ![p3 0, w] Y.u1

def QQ (Y : FBChart C V O dd) : PS C 3 dd := ev (n := 3) ![m3 Y.B.G V.l, p3 1, p3 2] Y.B.ph2

theorem ex_nsmul {σ : Type} (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) (n : ℕ) :
    ex (n • f) = ex f ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih =>
    rw [succ_nsmul, ex_add _ _ (by simp [hf]) hf, ih, pow_succ]

theorem height_at_zero_first (Y : FBChart C V O dd) {n : ℕ} (W : Pt C n dd) (hW : ∀ j, constantCoeff (W j) = 0) :
    ev (n := n) ![0, W] Y.h = 0 := by
  have h0 := Y.gauge.ax0
  have hz : Z0 (![(0 : Pt C 1 dd), pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := fun k j => by
    fin_cases k
    · exact map_zero _
    · exact z0_pt 0 j
  have h1 := congrArg (ev ![W]) h0
  rw [ev_ev hz (z0_1 W hW), ev_zero (z0_1 W hW)] at h1
  rw [← h1]
  congr 1
  funext k j
  fin_cases k
  · exact (ev_zero (z0_1 W hW)).symm
  · exact (ev_X (z0_1 W hW) 0 j).symm

theorem restrict_triple_multiplication (G : FGLaw C dd) (n : ℕ) (j : Fin dd) : ev (rz 2) (m3 G n j) = 0 := by
  unfold m3
  rw [ev_ev (z0_1 _ (z0p3 0)) (constant_zero_restrict_points 2)]
  have e : (fun k m => ev (rz (C := C) (dd := dd) 2) ((![(p3 0 : Pt C 3 dd)] : Fin 1 → Pt C 3 dd) k m)) =
      ![(0 : Pt C 2 dd)] := by
    funext k m
    fin_cases k
    exact ev_X (constant_zero_restrict_points 2) 0 m
  rw [e, ev_zero_pt, multiplication_constantCoeff_zero, map_zero]

theorem constant_zero_two_points {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : Z0 (![P, w] : Fin 2 → Pt C 3 dd) := by
  intro i j
  fin_cases i
  · exact hP j
  · exact hw j

theorem ev_smulC {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (c • f) = c • ev a f := by
  rw [ev_eq_alg ha, map_smul, ← ev_eq_alg ha]

theorem UU_eq (Y : FBChart C V O dd) (w : Pt C 3 dd) (hw : ∀ j, constantCoeff (w j) = 0) :
    UU Y w = ex (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw
  have hE0 : constantCoeff (gg Y V.l - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, h_const, mul_zero, sub_zero]
    exact height_multiple_constantCoeff Y V.l
  unfold UU
  rw [show Y.u1 = ex (gg Y V.l - (V.l : C) • Y.h) from rfl, ev_ex hz _ hE0, ev_sub hz, ev_smulC hz]
  congr 2
  unfold gg
  rw [ev_ev (constant_zero_double_multiplication_pair Y V.l) hz]
  congr 1
  funext k j
  fin_cases k
  · show ev ![p3 0, w] (ev ![pt C (n := 2) dd 0] (mulL Y.B.G.F V.l j)) = m3 Y.B.G V.l j
    rw [ev_ev (z0_1 _ (fun j => z0_pt 0 j)) hz]
    congr 1
    funext k' m
    fin_cases k'
    exact ev_X hz 0 m
  · exact ev_X hz 1 j

theorem hph2 (Y : FBChart C V O dd) : Y.B.ph2 = ex (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
    ev (n := 3) ![p3 0, SS Y.B.G] Y.h) := by
  have := Y.gauge.ph2
  rwa [toK_self, FK_self] at this

theorem eval_height_constantCoeff (Y : FBChart C V O dd) {P w : Pt C 3 dd} (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : constantCoeff (ev (n := 3) ![P, w] Y.h) = 0 :=
  const_ev (constant_zero_two_points P hP hw) (h_const Y)

theorem QQ_eq (Y : FBChart C V O dd) : QQ Y = ex (ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h +
    ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h - ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h) := by
  have ha : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact triple_multiplication_constantCoeff _ _ j
    · exact z0p3 1 j
    · exact z0p3 2 j
  have hE0 : constantCoeff (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
      ev (n := 3) ![p3 0, SS Y.B.G] Y.h) = 0 := by
    rw [map_sub, map_add, eval_height_constantCoeff Y (z0p3 0) (z0p3 1), eval_height_constantCoeff Y (z0p3 0) (z0p3 2), eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)]
    simp
  unfold QQ
  rw [hph2, ev_ex ha _ hE0, ev_sub ha, ev_add ha, ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 1)) ha,
    ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 2)) ha, ev_ev (constant_zero_two_points _ (z0p3 0) (triple_sum_constantCoeff _)) ha]
  have e1 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 1] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 1] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 1 j
  have e2 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 2] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 2] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 2 j
  have e3 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, SS Y.B.G] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, SS Y.B.G] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · show ev ![m3 Y.B.G V.l, p3 1, p3 2] (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = SS Y.B.G j
      rw [ev_ev (z0_pp 1 2) ha]
      congr 1
      funext k' m; fin_cases k'
      · exact ev_X ha 1 m
      · exact ev_X ha 2 m
  rw [e1, e2, e3]

theorem ident (Y : FBChart C V O dd) :
    UU Y (SS Y.B.G) * QQ Y = UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l := by
  have hm := triple_multiplication_constantCoeff Y.B.G V.l
  set a := ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h with ha
  set b1 := ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h with hb1
  set b2 := ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h with hb2
  set c0 := ev (n := 3) ![p3 0, SS Y.B.G] Y.h with hc0
  set c1 := ev (n := 3) ![p3 0, p3 1] Y.h with hc1
  set c2 := ev (n := 3) ![p3 0, p3 2] Y.h with hc2
  have za : constantCoeff a = 0 := eval_height_constantCoeff Y hm (triple_sum_constantCoeff _)
  have zb1 : constantCoeff b1 = 0 := eval_height_constantCoeff Y hm (z0p3 1)
  have zb2 : constantCoeff b2 = 0 := eval_height_constantCoeff Y hm (z0p3 2)
  have zc0 : constantCoeff c0 = 0 := eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)
  have zc1 : constantCoeff c1 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 1)
  have zc2 : constantCoeff c2 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 2)
  have zs : ∀ (c : C) (f : PS C 3 dd), constantCoeff f = 0 → constantCoeff (c • f) = 0 := fun c f hf => by
    rw [show c • f = MvPowerSeries.C c * f from (MvPowerSeries.smul_eq_C_mul f c), map_mul, hf, mul_zero]
  have zE : constantCoeff (c1 + c2 - c0) = 0 := by rw [map_sub, map_add, zc1, zc2, zc0]; simp
  rw [UU_eq _ _ (triple_sum_constantCoeff _), UU_eq _ _ (z0p3 1), UU_eq _ _ (z0p3 2), QQ_eq, hph2, ← hc0, ← hc1, ← hc2, ← ha,
    ← hb1, ← hb2, ← ex_nsmul _ zE V.l,
    ← ex_add _ _ (by rw [map_sub, za, zs _ _ zc0, sub_zero]) (by rw [map_sub, map_add, zb1, zb2, za]; simp),
    ← ex_add _ _ (by rw [map_sub, zb1, zs _ _ zc1, sub_zero]) (by rw [map_sub, zb2, zs _ _ zc2, sub_zero]),
    ← ex_add _ _ (by rw [map_add, map_sub, map_sub, zb1, zb2, zs _ _ zc1, zs _ _ zc2]; simp)
      (by rw [map_nsmul, zE, nsmul_zero])]
  congr 1
  rw [Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C]
  simp only [nsmul_sub, nsmul_add]
  abel

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem pderiv_first_unit_series_maximal (Y : FBChart C V O dd) (i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 2), i) Y.u1) := by
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv C ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint

theorem int_two {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, IntS V (P j)) (hw : ∀ j, IntS V (w j)) :
    ∀ k j, IntS V ((![P, w] : Fin 2 → Pt C 3 dd) k j) := fun k j => by
  fin_cases k
  · exact hP j
  · exact hw j

theorem triple_coordinate_integral (k : Fin 3) (j : Fin dd) : IntS V ((p3 k : Pt C 3 dd) j) := intS_X _

theorem UU_int (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) : IntS V (UU Y w) :=
  intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)

theorem UU_frob (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) (hd : ∀ i j, pderiv C ((0 : Fin 3), i) (w j) = 0) : FrobD V (UU Y w) := by
  intro i
  unfold UU
  rw [d_ev_keep hw0 i (hd i)]
  exact MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)

theorem UU_one (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0) :
    ev (rz 2) (UU Y w) = 1 := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw0
  have hw' : ∀ j, constantCoeff (ev (rz (C := C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)
  have hE0 : constantCoeff (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by
    rw [map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h =
      MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul,
      eval_height_constantCoeff Y (z0p3 0) hw0, mul_zero, sub_zero]
  rw [UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2),
    ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (constant_zero_restrict_points 2)]
  have e1 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · rfl
  have e2 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · rfl
  rw [e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]

theorem constant_zero_triple_multiplication (Y : FBChart C V O dd) : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact triple_multiplication_constantCoeff _ _ j
  · exact z0p3 1 j
  · exact z0p3 2 j

theorem QQ_int (Y : FBChart C V O dd) : IntS V (QQ Y) := by
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ j
  · exact intS_X _
  · exact intS_X _

theorem pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) :
    pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k) = ev ![(p3 0 : Pt C 3 dd)] (Jac (mulL Y.B.G.F V.l) k i) := by
  show pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _
  rw [pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _
  rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  rfl

theorem pderiv_triple_multiplication_maximal (Y : FBChart C V O dd) (k i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), i) (m3 Y.B.G V.l k)) := by
  rw [pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)),
    nsmul_eq_mul]
  refine MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)
  rw [Matrix.mul_apply]
  refine intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)
  refine intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
  fin_cases k'
  exact mulL_int Y.B.G Y.intF V.l j'

theorem QQ_frob (Y : FBChart C V O dd) : FrobD V (QQ Y) := by
  intro i
  unfold QQ
  rw [pderiv_eval_triple (constant_zero_triple_multiplication Y)]
  have h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((1 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  have h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv C ((2 : Fin 3), j) Y.B.ph2) *
      pderiv C ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]
  rw [h1, h2, add_zero, add_zero]
  refine MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ m
  · exact intS_X _
  · exact intS_X _

theorem rz_eq : (rz (C := C) (dd := dd) 2) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
  funext k j
  fin_cases k <;> rfl

theorem QQ_one (Y : FBChart C V O dd) : ev (rz 2) (QQ Y) = 1 := by
  unfold QQ
  rw [ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]
  have e : (fun k j => ev (rz (C := C) (dd := dd) 2)
      ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · exact ev_X (constant_zero_restrict_points 2) 1 j
    · exact ev_X (constant_zero_restrict_points 2) 2 j
  rw [e]
  exact Y.B.cocycleRight_zero_fst

theorem second_pairing_restrict_one (Y : FBChart C V O dd) : ev (rz 2) Y.B.ph2 = 1 := by
  rw [rz_eq]; exact Y.B.cocycleRight_zero_fst

theorem second_pairing_pow_restrict_one (Y : FBChart C V O dd) : ev (rz 2) (Y.B.ph2 ^ V.l) = 1 := by
  rw [ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]

theorem second_pairing_pow_frobenius (Y : FBChart C V O dd) : FrobD V (Y.B.ph2 ^ V.l) := by
  intro i
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  exact MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

def Phi (V : VF C) (u : Fin dd → C) (f : PS C 3 dd) (γ : Fin 2 × Fin dd →₀ ℕ) : C :=
  ∑ i, u i ^ V.l * coeff (ix i V.l γ) f

def Tk (f : PS C 3 dd) (k : Fin dd) : PS C 3 dd :=
  fun p => if (∀ j : Fin dd, j < k → p ((0 : Fin 3), j) = 0) then coeff (p + Finsupp.single ((0 : Fin 3), k) 1) f else 0

theorem Tk_int {f : PS C 3 dd} (hf : IntS V f) (k : Fin dd) : IntS V (Tk f k) := by
  intro μ
  show V.Ge 0 (if (∀ j : Fin dd, j < k → μ ((0 : Fin 3), j) = 0) then
    coeff (μ + Finsupp.single ((0 : Fin 3), k) 1) f else 0)
  split_ifs
  · exact hf _
  · unfold VF.Ge
    simp [AddValuation.map_zero]

theorem decomp {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) : f = 1 + ∑ k, X ((0 : Fin 3), k) * Tk f k := by
  classical
  ext p
  rw [map_add, MvPowerSeries.coeff_one, map_sum]
  have hX : ∀ k, coeff p (X ((0 : Fin 3), k) * Tk f k) =
      if Finsupp.single ((0 : Fin 3), k) 1 ≤ p then
        coeff (p - Finsupp.single ((0 : Fin 3), k) 1) (Tk f k) else 0 := by
    intro k
    rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
  simp only [hX]
  by_cases hfree : ∀ j, p ((0 : Fin 3), j) = 0
  · rw [coeff_free h1 hfree, Finset.sum_eq_zero, add_zero]
    intro k _
    rw [if_neg]
    rw [Finsupp.single_le_iff, hfree k]
    omega
  · push_neg at hfree
    set S := Finset.univ.filter (fun j : Fin dd => p ((0 : Fin 3), j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hfree
      exact ⟨j, by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj⟩
    set k0 := S.min' hS with hk0
    have hk0S : k0 ∈ S := S.min'_mem hS
    have hk0p : p ((0 : Fin 3), k0) ≠ 0 := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hk0S
      exact hk0S
    have hmin : ∀ j, j < k0 → p ((0 : Fin 3), j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne
      exact absurd hj (not_lt.mpr (S.min'_le j hjS))
    have hp0 : p ≠ 0 := by
      intro h
      apply hk0p
      rw [h]
      rfl
    have hle0 : Finsupp.single ((0 : Fin 3), k0) 1 ≤ p := by
      rw [Finsupp.single_le_iff]
      omega
    rw [if_neg hp0, zero_add, Finset.sum_eq_single k0]
    · rw [if_pos hle0]
      show coeff p f = (if (∀ j : Fin dd, j < k0 →
          (p - Finsupp.single ((0 : Fin 3), k0) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j) = 0) then
          coeff (p - Finsupp.single ((0 : Fin 3), k0) 1 + Finsupp.single ((0 : Fin 3), k0) 1) f else 0)
      rw [if_pos, tsub_add_cancel_of_le hle0]
      intro j hj
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg, hmin j hj]
      all_goals first
        | rfl
        | (intro h
           simp only [Prod.mk.injEq, true_and] at h
           subst h
           exact lt_irrefl _ hj)
    · intro k _ hk
      by_cases hle : Finsupp.single ((0 : Fin 3), k) 1 ≤ p
      · rw [if_pos hle]
        show (if (∀ j : Fin dd, j < k →
            (p - Finsupp.single ((0 : Fin 3), k) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j) = 0) then
            coeff (p - Finsupp.single ((0 : Fin 3), k) 1 + Finsupp.single ((0 : Fin 3), k) 1) f else 0) = 0
        rw [if_neg]
        intro hall
        have hkS : k ∈ S := by
          simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Finsupp.single_le_iff] at hle
          omega
        have hk0k : k0 < k := lt_of_le_of_ne (S.min'_le k hkS) (Ne.symm hk)
        have h2 := hall k0 hk0k
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg] at h2
        · exact hk0p (by omega)
        · intro h
          simp only [Prod.mk.injEq, true_and] at h
          exact hk h
      · rw [if_neg hle]
    · intro h
      exact absurd (Finset.mem_univ k0) h

theorem QQ_expand (Y : FBChart C V O dd) :
    QQ Y = 1 + ∑ k, m3 Y.B.G V.l k * ev ![m3 Y.B.G V.l, p3 1, p3 2] (Tk Y.B.ph2 k) := by
  have hz := constant_zero_triple_multiplication Y
  conv_lhs => rw [QQ, decomp (second_pairing_restrict_one Y)]
  rw [PartialDerivEval.ev_add hz, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_one, PartialDerivEval.ev_sum hz]
  simp only [PartialDerivEval.ev_mul hz, PartialDerivEval.ev_X hz]
  rfl

theorem triple_multiplication_pderiv_other (Y : FBChart C V O dd) (k : Fin dd) (s : Fin 3 × Fin dd) (hs : s.1 ≠ 0) :
    pderiv C s (m3 Y.B.G V.l k) = 0 := by
  simp only [m3]
  rw [pderiv_eval_single (fun j => by simp [p3, pt])]
  apply Finset.sum_eq_zero
  intro j _
  simp only [p3, pderiv_pt]
  rw [if_neg (fun h => hs (congrArg Prod.fst h).symm), mul_zero]

theorem triple_multiplication_first_only (Y : FBChart C V O dd) (k : Fin dd) (p : Fin 3 × Fin dd →₀ ℕ) (s : Fin 3 × Fin dd)
    (hs : s.1 ≠ 0) (hp : p s ≠ 0) : coeff p (m3 Y.B.G V.l k) = 0 := by
  have h := congrArg (coeff (p - Finsupp.single s 1)) (triple_multiplication_pderiv_other Y k s hs)
  rw [MvPowerSeries.coeff_pderiv, map_zero] at h
  have hle : Finsupp.single s 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp
  rw [tsub_add_cancel_of_le hle] at h
  exact (mul_eq_zero.mp h).resolve_right (Nat.cast_add_one_ne_zero _)

private theorem pderiv_ev_p3_zero_eq_ev_pderiv (i : Fin dd) (g : PS C 1 dd) :
    pderiv C ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] g) =
      ev ![(p3 0 : Pt C 3 dd)] (pderiv C ((0 : Fin 1), i) g) := by
  rw [pderiv_eval_single (fun j => by simp [p3, pt])]
  simp [p3, pderiv_pt, Finset.sum_ite_eq']

theorem iterate_pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) (L : ℕ) :
    (pderiv C ((0 : Fin 3), i))^[L] (m3 Y.B.G V.l k) =
      ev ![(p3 0 : Pt C 3 dd)] ((pderiv C ((0 : Fin 1), i))^[L] (mulL Y.B.G.F V.l k)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_ev_p3_zero_eq_ev_pderiv,
      ← Function.iterate_succ_apply' (pderiv C ((0 : Fin 1), i))]

private theorem coeff_iterate_pderiv_eq_coeff_add_single_mul_prod {σ : Type} (i : σ) (L : ℕ) : ∀ (f : MvPowerSeries σ C) (μ : σ →₀ ℕ),
    coeff μ ((pderiv C i)^[L] f) =
      coeff (μ + Finsupp.single i L) f * ∏ t ∈ Finset.range L, ((μ i : C) + t + 1) := by
  induction L with
  | zero =>
    intro f μ
    simp
  | succ L ih =>
    intro f μ
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv, Finset.prod_range_succ]
    have e : μ + Finsupp.single i L + Finsupp.single i 1 = μ + Finsupp.single i (L + 1) := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [e]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring

theorem coeff_triple_multiplication_single (Y : FBChart C V O dd) (k i : Fin dd) (L : ℕ) :
    coeff (Finsupp.single ((0 : Fin 3), i) L) (m3 Y.B.G V.l k) =
      coeff (Finsupp.single ((0 : Fin 1), i) L) (mulL Y.B.G.F V.l k) := by
  have hz : Z0 (![(p3 0 : Pt C 3 dd)] : Fin 1 → Pt C 3 dd) := by
    intro j i
    fin_cases j
    simp [p3, pt]
  have h1 := coeff_iterate_pderiv_eq_coeff_add_single_mul_prod ((0 : Fin 3), i) L (m3 Y.B.G V.l k) 0
  have h2 := coeff_iterate_pderiv_eq_coeff_add_single_mul_prod ((0 : Fin 1), i) L (mulL Y.B.G.F V.l k) 0
  rw [iterate_pderiv_triple_multiplication] at h1
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero] at h1 h2
  have hP : ∏ t ∈ Finset.range L, ((t : C) + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => Nat.cast_add_one_ne_zero t)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PartialDerivEval.constantCoeff_ev hz,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h2] at h1
  exact (mul_right_cancel₀ hP h1).symm

theorem triple_multiplication_frobenius (Y : FBChart C V O dd) (k : Fin dd) : FrobX V (m3 Y.B.G V.l k) := by
  exact frobX_of (triple_multiplication_integral Y.B.G Y.intF V.l k) (fun j => pderiv_triple_multiplication_maximal Y k j)

private theorem mm_zero_of_vf : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_add_character_germs {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_sum_character_germs {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) :=
  Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_character_germs hx hy) mm_zero_of_vf h

private theorem mm_mul_ge_zero_right {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem m3mul (Y : FBChart C V O dd) (k i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {G : PS C 3 dd} (hG : IntS V G) :
    V.MM (coeff (ix i V.l γ) (m3 Y.B.G V.l k * G) -
      coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * coeff (γ.mapDomain (up 2)) G) := by
  classical
  set N := ix i V.l γ with hN
  have hl0 : 0 < V.l := V.l_prime.pos
  have hNi : N ((0 : Fin 3), i) = V.l := by rw [hN, index_raise_first, if_pos rfl]
  have key : ∀ a : Fin 3 × Fin dd →₀ ℕ, a ≤ N → a ≠ Finsupp.single ((0 : Fin 3), i) V.l →
      V.MM (coeff a (m3 Y.B.G V.l k)) := by
    intro a ha hne
    by_cases hz : ∃ s : Fin 3 × Fin dd, s.1 ≠ 0 ∧ a s ≠ 0
    · obtain ⟨s, hs, has⟩ := hz
      rw [triple_multiplication_first_only Y k a s hs has]
      exact mm_zero_of_vf
    · push_neg at hz
      have hx : ∀ j, j ≠ i → a ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
      by_cases hd : V.l ∣ a ((0 : Fin 3), i)
      · have hle : a ((0 : Fin 3), i) ≤ V.l := by
          have := ha ((0 : Fin 3), i)
          rwa [hNi] at this
        have h01 : a ((0 : Fin 3), i) = 0 ∨ a ((0 : Fin 3), i) = V.l := by
          obtain ⟨q, hq⟩ := hd
          rcases q with _ | _ | q
          · left
            simpa using hq
          · right
            simpa using hq
          · exfalso
            have h3 := hq ▸ hle
            nlinarith
        have hext : ∀ c : ℕ, a ((0 : Fin 3), i) = c → a = Finsupp.single ((0 : Fin 3), i) c := by
          intro c hc
          ext ⟨kk, j⟩
          induction kk using Fin.cases with
          | zero =>
            rw [Finsupp.single_apply]
            by_cases hj : j = i
            · subst hj
              rw [if_pos rfl]
              exact hc
            · rw [if_neg (fun h => hj (congrArg Prod.snd h).symm), hx j hj]
          | succ kk' =>
            rw [Finsupp.single_apply, if_neg (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h).symm)]
            exact hz _ (Fin.succ_ne_zero _)
        rcases h01 with h0 | hL
        · rw [hext 0 h0, Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, triple_multiplication_constantCoeff]
          exact mm_zero_of_vf
        · exact absurd (hext V.l hL) hne
      · exact triple_multiplication_frobenius Y k a ⟨i, hd⟩
  rw [MvPowerSeries.coeff_mul]
  have hx0 : (Finsupp.single ((0 : Fin 3), i) V.l, γ.mapDomain (up 2)) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal, hN]
    rfl
  rw [← Finset.add_sum_erase _ _ hx0]
  dsimp only
  rw [coeff_triple_multiplication_single Y k i V.l, add_sub_cancel_left]
  apply mm_sum_character_germs
  intro x hx
  obtain ⟨hne, hxa⟩ := Finset.mem_erase.mp hx
  have hxa' := Finset.HasAntidiagonal.mem_antidiagonal.mp hxa
  have ha : x.1 ≤ N := by
    rw [← hxa']
    exact le_self_add
  have hne1 : x.1 ≠ Finsupp.single ((0 : Fin 3), i) V.l := by
    intro h1
    apply hne
    have h2 : x.2 = γ.mapDomain (up 2) := by
      have h3 := hxa'
      rw [h1, hN] at h3
      unfold ix at h3
      exact add_left_cancel h3
    exact Prod.ext h1 h2
  exact mm_mul_ge_zero_right (key x.1 ha hne1) (hG x.2)

private theorem intS_one' {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) := by
  intro μ
  unfold VF.Ge
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · simp [AddValuation.map_one]
  · simp [AddValuation.map_zero]

private theorem intS_mul_character_germs' {V : VF C} {σ : Type} {f g : MvPowerSeries σ C} (hf : IntS V f)
    (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  unfold VF.Ge
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  have h1 := hf x.1
  have h2 := hg x.2
  unfold VF.Ge at h1 h2
  simpa using add_le_add h1 h2

private theorem intS_pow' {V : VF C} {σ : Type} {f : MvPowerSeries σ C} (hf : IntS V f) (k : ℕ) :
    IntS V (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact intS_one'
  | succ k ih => rw [pow_succ]; exact intS_mul_character_germs' ih hf

private theorem intS_ev_of_z0_of_intS {V : VF C} {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a)
    (hi : ∀ k j, IntS V (a k j)) {f : PS C m dd} (hf : IntS V f) : IntS V (ev a f) := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  intro e
  show V.Ge 0 (coeff e (MvPowerSeries.subst (fun p : Fin m × Fin dd => a p.1 p.2) f))
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs f e)]
  unfold VF.Ge
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have hd : IntS V (d.prod fun s k => (fun p : Fin m × Fin dd => a p.1 p.2) s ^ k) := by
    unfold Finsupp.prod
    exact Finset.prod_induction _ (fun g => IntS V g) (fun x y hx hy => intS_mul_character_germs' hx hy) intS_one'
      (fun s _ => intS_pow' (hi s.1 s.2) _)
  have h1 := hf d
  have h2 := hd e
  unfold VF.Ge at h1 h2
  simpa using add_le_add h1 h2

private theorem mm_mul_of_ge_zero_of_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [AddValuation.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := by simpa using ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem phiQ (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (hV1 : Y.FirstVanishingAt u)
    (γ : Fin 2 × Fin dd →₀ ℕ) : V.MM (Phi V u (QQ Y) γ) := by
  have hzi : ∀ k i, IntS V ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k i) := by
    intro k i
    fin_cases k
    · exact triple_multiplication_integral Y.B.G Y.intF V.l i
    · exact triple_coordinate_integral 1 i
    · exact triple_coordinate_integral 2 i
  have hIT : ∀ k, IntS V (ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)) :=
    fun k => intS_ev_of_z0_of_intS (constant_zero_triple_multiplication Y) hzi (Tk_int Y.intPh2 k)
  have alg : ∀ (A : Fin dd → Fin dd → C) (B : Fin dd → Fin dd → C) (t : Fin dd → C) (w : Fin dd → C),
      ∑ i, w i * ∑ k, A i k = ∑ i, ∑ k, w i * (A i k - B k i * t k) + ∑ k, t k * ∑ i, B k i * w i := by
    intro A B t w
    have h1 : ∀ i, w i * ∑ k, A i k = ∑ k, w i * (A i k - B k i * t k) + ∑ k, w i * (B k i * t k) := by
      intro i
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
      Finset.sum_comm (f := fun i k => w i * (B k i * t k))]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hA : ∀ i, coeff (ix i V.l γ) (1 + ∑ k, m3 Y.B.G V.l k *
      ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)) =
      ∑ k, coeff (ix i V.l γ) (m3 Y.B.G V.l k * ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd)
        (Tk Y.B.ph2 k)) := by
    intro i
    rw [map_add, map_sum, MvPowerSeries.coeff_one, if_neg, zero_add]
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  unfold Phi
  rw [QQ_expand Y]
  simp only [hA]
  rw [alg _ (fun k i => coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k))
    (fun k => coeff (γ.mapDomain (up 2)) (ev (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) (Tk Y.B.ph2 k)))]
  apply mm_add_character_germs
  · apply mm_sum_character_germs
    intro i _
    apply mm_sum_character_germs
    intro k _
    have hul : V.Ge 0 (u i ^ V.l) := by
      unfold VF.Ge
      rw [AddValuation.map_pow]
      have h0 : (0 : WithTop ℝ) ≤ V.v (u i) := by simpa [VF.Ge] using hu i
      simpa using nsmul_nonneg h0 V.l
    exact mm_mul_of_ge_zero_of_mm hul (m3mul Y k i γ (hIT k))
  · apply mm_sum_character_germs
    intro k _
    exact mm_mul_of_ge_zero_of_mm (hIT k _) (hV1 k)

private theorem v_natCast_nonneg_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

private theorem mm_add_of_both {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  apply mm_add_character_germs (ha := ha) (hb := hb) <;> assumption

private theorem mm_finset_sum {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_both hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_add_pow_l_sub_pow_l_sub_pow_l {y z : C} (hy : V.Ge 0 y) (hz : V.Ge 0 z) :
    V.MM ((y + z) ^ V.l - y ^ V.l - z ^ V.l) := by
  obtain ⟨n, hn⟩ : ∃ n, V.l = n + 1 := ⟨V.l - 1, (Nat.succ_pred_eq_of_pos V.l_prime.pos).symm⟩
  have hpr : (n + 1).Prime := hn ▸ V.l_prime
  have hvl : V.v ((n + 1 : ℕ) : C) = 1 := by
    rw [← hn]
    exact V.v_l
  rw [hn, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero, mul_one, one_mul,
    Nat.cast_one]
  have e : ∀ A B D : C, A + B + D - D - B = A := by
    intros
    ring
  rw [e]
  apply mm_finset_sum
  intro m hm
  have hm' : m < n := Finset.mem_range.mp hm
  obtain ⟨q, hq⟩ := hpr.dvd_choose_self (Nat.succ_ne_zero m) (by omega)
  rw [hq, Nat.cast_mul]
  unfold VF.MM
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow,
    AddValuation.map_pow, hvl]
  have h1 : (0 : WithTop ℝ) ≤ (m + 1) • V.v y := nsmul_nonneg (by simpa [VF.Ge] using hy) _
  have h2 : (0 : WithTop ℝ) ≤ (n + 1 - (m + 1)) • V.v z := nsmul_nonneg (by simpa [VF.Ge] using hz) _
  have h3 := v_natCast_nonneg_vf V q
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  exact lt_of_lt_of_le (lt_of_lt_of_le h01 (le_add_of_nonneg_right h3)) (le_add_of_nonneg_left (add_nonneg h1 h2))

theorem mm_sum_pow {ι : Type} (s : Finset ι) (a : ι → C) (ha : ∀ i, V.Ge 0 (a i)) :
    V.MM ((∑ i ∈ s, a i) ^ V.l - ∑ i ∈ s, a i ^ V.l) := by
  classical
  refine Finset.induction_on s ?_ (fun x t hx ih => ?_)
  · simp only [Finset.sum_empty, sub_zero]
    rw [zero_pow V.l_prime.ne_zero]
    unfold VF.MM
    rw [AddValuation.map_zero, ← WithTop.coe_zero]
    exact WithTop.coe_lt_top _
  · rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hS : V.Ge 0 (∑ i ∈ t, a i) := by
      unfold VF.Ge
      apply AddValuation.map_le_sum
      intro i _
      exact ha i
    have e : (a x + ∑ i ∈ t, a i) ^ V.l - (a x ^ V.l + ∑ i ∈ t, a i ^ V.l) =
        ((a x + ∑ i ∈ t, a i) ^ V.l - a x ^ V.l - (∑ i ∈ t, a i) ^ V.l) +
          ((∑ i ∈ t, a i) ^ V.l - ∑ i ∈ t, a i ^ V.l) := by
      ring
    rw [e]
    exact mm_add_of_both (mm_add_pow_l_sub_pow_l_sub_pow_l (ha x) hS) ih

private theorem single_zero_apply_up_two_eq_zero (i : Fin dd) (L : ℕ) (t : Fin 2 × Fin dd) :
    (Finsupp.single ((0 : Fin 3), i) L : Fin 3 × Fin dd →₀ ℕ) (up 2 t) = 0 := by
  rw [Finsupp.single_apply, if_neg]
  intro h
  simp only [up, Prod.mk.injEq] at h
  exact Fin.succ_ne_zero _ h.1.symm

private theorem ix_apply_up_two (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (t : Fin 2 × Fin dd) :
    ix i L γ (up 2 t) = γ t := by
  rw [ix, Finsupp.add_apply, single_zero_apply_up_two_eq_zero, zero_add, Finsupp.mapDomain_apply (up_inj 2)]

theorem ix_div (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) (L : ℕ) (hL : 0 < L) :
    (ix i L γ).mapRange (fun n => n / L) (Nat.zero_div L) =
      (γ.mapRange (fun n => n / L) (Nat.zero_div L)).mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1 := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
    rw [Finsupp.mapRange_apply, index_raise_first, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, zero_add,
      Finsupp.single_apply]
    by_cases h : j = i
    · subst h
      simp [Nat.div_self hL]
    · simp [h, Ne.symm h]
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapRange_apply, ix_apply_up_two, Finsupp.add_apply, single_zero_apply_up_two_eq_zero, add_zero,
      Finsupp.mapDomain_apply (up_inj 2), Finsupp.mapRange_apply]

theorem ix_dvd (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    (∀ s, V.l ∣ ix i V.l γ s) ↔ ∀ t, V.l ∣ γ t := by
  constructor
  · intro h t
    have := h (up 2 t)
    rwa [ix_apply_up_two] at this
  · rintro h ⟨k, j⟩
    induction k using Fin.cases with
    | zero =>
      rw [index_raise_first]
      split_ifs <;> simp
    | succ k' =>
      have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
      rw [e, ix_apply_up_two]
      exact h _

theorem phiP (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (Y.B.ph2 ^ V.l) γ - coeff γ (frobTw V.l (Y.chartLinearTerm u))) := by
  have hl := V.l_prime
  have hP := MaximalIdealCongruence.mms_pow_frobTw (V := V) Y.intPh2
  have e1 : Phi V u (Y.B.ph2 ^ V.l) γ =
      ∑ i, u i ^ V.l * (coeff (ix i V.l γ) (Y.B.ph2 ^ V.l - frobTw V.l Y.B.ph2)) +
        ∑ i, u i ^ V.l * coeff (ix i V.l γ) (frobTw V.l Y.B.ph2) := by
    unfold Phi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub]; ring
  rw [e1, add_sub_assoc]
  refine GmExArith.mm_add (GmExArith.mm_sum fun i _ => GmExArith.mm_int_mul ((hu i).pow _) (hP _)) ?_
  rw [MaximalIdealCongruence.coeff_frobTw]
  by_cases hd : ∀ t, V.l ∣ γ t
  · rw [if_pos hd]
    have e2 : ∀ i, coeff (ix i V.l γ) (frobTw V.l Y.B.ph2) =
        (coeff ((γ.mapRange (fun n => n / V.l) (Nat.zero_div V.l)).mapDomain (up 2) +
          Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2) ^ V.l := by
      intro i
      rw [MaximalIdealCongruence.coeff_frobTw, if_pos ((ix_dvd i γ).2 hd), ix_div i γ V.l hl.pos]
    simp only [e2]
    set ν := γ.mapRange (fun n => n / V.l) (Nat.zero_div V.l) with hν
    have e3 : coeff ν (Y.chartLinearTerm u) = ∑ i, u i * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2 :=
      rfl
    rw [e3]
    have e4 : ∑ i, u i ^ V.l * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2 ^ V.l =
        ∑ i, (u i * coeff (ν.mapDomain (up 2) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2) ^ V.l :=
      Finset.sum_congr rfl fun i _ => (mul_pow _ _ _).symm
    rw [e4, ← neg_sub]
    exact GmExArith.mm_neg (mm_sum_pow _ _ fun i => (hu i).mul_int (Y.intPh2 _))
  · rw [if_neg hd, sub_zero]
    refine GmExArith.mm_sum fun i _ => ?_
    rw [MaximalIdealCongruence.coeff_frobTw, if_neg (fun h => hd ((ix_dvd i γ).1 h)), mul_zero]
    exact GmExArith.mm_zero

end Formalism.L2.FormalSeriesBounds.FunEq
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem aOf_eq (Y : FBChart C V O dd) (u : Fin dd → C) :
    Y.aOf u = ∑ i, MvPowerSeries.C (u i ^ V.l * ((V.l.factorial : C))⁻¹) *
      ev (rz 1) ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
  ext ν
  rw [map_sum]
  simp only [coeff_C_mul]
  show (∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
    ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1) = _
  have hup : (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2)) = up 1 := by
    funext q; obtain ⟨q1, q2⟩ := q; fin_cases q1; rfl
  rw [hup]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_rz_iter]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem link (Y : FBChart C V O dd) (u : Fin dd → C) (W : Pt C 2 dd) (hW : ∀ j, constantCoeff (W j) = 0)
    (Wup : Pt C 3 dd) (hW0 : ∀ j, constantCoeff (Wup j) = 0) (hd : ∀ i j, pderiv C ((0 : Fin 3), i) (Wup j) = 0)
    (hr : ∀ j, ev (rz 2) (Wup j) = W j) (γ : Fin 2 × Fin dd →₀ ℕ) :
    coeff γ (ev (n := 2) ![W] (Y.aOf u)) = Phi V u (UU Y Wup) γ := by
  have hz1 := z0_1 W hW
  have hz2 := constant_zero_two_points (p3 0) (z0p3 0) hW0
  rw [aOf_eq, ev_sum hz1]
  simp only [ev_mul hz1, ev_C, map_sum, coeff_C_mul]
  unfold Phi
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ev ![W] (ev (rz 1) ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1)) =
      ev (n := 2) ![0, W] ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
    rw [ev_ev (constant_zero_restrict_points 1) hz1]
    congr 1
    funext k j
    fin_cases k
    · exact ev_zero hz1
    · exact ev_X hz1 0 j
  have e2 : ev (rz 2) ((pderiv C ((0 : Fin 3), i))^[V.l] (UU Y Wup)) =
      ev (n := 2) ![0, W] ((pderiv C ((0 : Fin 2), i))^[V.l] Y.u1) := by
    unfold UU
    rw [d_ev_keep_iter hW0 i (hd i), ev_ev hz2 (constant_zero_restrict_points 2)]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · exact hr j
  have h3 := coeff_rz_iter 2 i V.l (UU Y Wup) γ
  rw [e2] at h3
  rw [e1, h3]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  rfl

theorem coeff_U_eq (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (UU Y (SS Y.B.G)) γ - Phi V u (UU Y (p3 1)) γ - Phi V u (UU Y (p3 2)) γ -
      Phi V u (Y.B.ph2 ^ V.l) γ + Phi V u (QQ Y) γ) := by
  have hU : ∀ {w : Pt C 3 dd}, (∀ j, constantCoeff (w j) = 0) → (∀ j, IntS V (w j)) →
      (∀ i j, pderiv C ((0 : Fin 3), i) (w j) = 0) → IntS V (UU Y w) ∧ FrobD V (UU Y w) ∧ ev (rz 2) (UU Y w) = 1 :=
    fun hw0 hw hd => ⟨UU_int Y hw0 hw, UU_frob Y hw0 hw hd, UU_one Y hw0⟩
  obtain ⟨iS, fS, oS⟩ := hU (triple_sum_constantCoeff Y.B.G) (SS_int Y.B.G Y.intF) (SS_d Y.B.G)
  obtain ⟨i1, f1, o1⟩ := hU (z0p3 1) (fun j => triple_coordinate_integral 1 j) (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j)
  obtain ⟨i2, f2, o2⟩ := hU (z0p3 2) (fun j => triple_coordinate_integral 2 j) (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j)
  have iQ := QQ_int Y
  have iP : IntS V (Y.B.ph2 ^ V.l) := intS_pow Y.intPh2 _
  have i12 : IntS V (UU Y (p3 1) * UU Y (p3 2)) := intS_mul i1 i2
  have f12 : FrobD V (UU Y (p3 1) * UU Y (p3 2)) := frobD_mul i1 i2 f1 f2
  have o12 : ev (rz 2) (UU Y (p3 1) * UU Y (p3 2)) = 1 := by rw [ev_mul (constant_zero_restrict_points 2), o1, o2, one_mul]
  unfold Phi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine GmExArith.mm_sum fun i _ => ?_
  have cS := coeff_mul_cong iS iQ (frobX_of iS fS) (frobX_of iQ (QQ_frob Y)) oS (QQ_one Y) i γ
  have cR1 := coeff_mul_cong i12 iP (frobX_of i12 f12) (frobX_of iP (second_pairing_pow_frobenius Y)) o12 (second_pairing_pow_restrict_one Y) i γ
  have cR2 := coeff_mul_cong i1 i2 (frobX_of i1 f1) (frobX_of i2 f2) o1 o2 i γ
  rw [ident] at cS
  have e : u i ^ V.l * coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 1)) -
      u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 2)) - u i ^ V.l * coeff (ix i V.l γ) (Y.B.ph2 ^ V.l) +
      u i ^ V.l * coeff (ix i V.l γ) (QQ Y) =
      u i ^ V.l * (-(coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
        coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - coeff (ix i V.l γ) (QQ Y)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
          coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (Y.B.ph2 ^ V.l)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (UU Y (p3 1)) -
          coeff (ix i V.l γ) (UU Y (p3 2)))) := by ring
  rw [e]
  exact GmExArith.mm_int_mul ((hu i).pow _) (GmExArith.mm_add (GmExArith.mm_add (GmExArith.mm_neg cS) cR1) cR2)

end Formalism.L2.FormalSeriesBounds.FunEq

namespace Formalism.L2.FormalSeriesBounds

open FunEq MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem funEqCore_holds : FunEqCoreSt := by
  intro C _ _ V O _ _ dd Y u hu hV1 μ
  have hS := link Y u (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1))
    (fun j => PartialDerivEval.const_ev (PartialDerivEval.z0_pp 0 1) (Y.B.G.const j)) (SS Y.B.G) (triple_sum_constantCoeff _) (SS_d _)
    (fun j => by
      show ev (rz 2) (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = _
      rw [PartialDerivEval.ev_ev (PartialDerivEval.z0_pp 1 2) (constant_zero_restrict_points 2)]
      congr 1
      funext k m
      fin_cases k
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 m
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 m) μ
  have h1 := link Y u (pt C (n := 2) dd 0) (fun j => PartialDerivEval.z0_pt 0 j) (p3 1) (z0p3 1)
    (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 j) μ
  have h2 := link Y u (pt C (n := 2) dd 1) (fun j => PartialDerivEval.z0_pt 1 j) (p3 2) (z0p3 2)
    (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 j) μ
  unfold cobd
  rw [map_sub, map_sub, map_sub, hS, h1, h2]
  have hA := coeff_U_eq Y u hu μ
  have hB := phiP Y u hu μ
  have hC := phiQ Y u hu hV1 μ
  have e : Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
      coeff μ (frobTw V.l (Y.chartLinearTerm u)) =
      (Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
        Phi V u (Y.B.ph2 ^ V.l) μ + Phi V u (QQ Y) μ) +
      (Phi V u (Y.B.ph2 ^ V.l) μ - coeff μ (frobTw V.l (Y.chartLinearTerm u))) - Phi V u (QQ Y) μ := by ring
  rw [e]
  exact GmExArith.mm_sub (GmExArith.mm_add hA hB) hC

end Formalism.L2.FormalSeriesBounds
end
end
