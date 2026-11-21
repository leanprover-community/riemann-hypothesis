import Formalism.PolynomialDimension.ChainOrderLetters
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.PartnerMeanProofs.TheoremMCKap7
import Formalism.ThetaLogCoordinates.PartnerMeanCoordinates.TheoremMXB

section
namespace Formalism.InvariantFactorPaths.MC

open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.InvariantFactorPaths.OddLevelGainBounds.TB

private lemma neg_logb_norm_natCast_eq_padicValNat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    -Real.logb p ‖(n : ℚ_[p])‖ = (padicValNat p n : ℝ) := by
  have h0 : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  have h1 : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
    rw [← h0, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
      padicValRat.of_nat]
    push_cast <;> simp [padicValRat.of_nat]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [h1, ← Real.rpow_intCast, Real.logb_rpow (by positivity) hp1.ne']
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg]

private lemma digits_sum_le_sub_one_mul_log_add_one (p : ℕ) [hp : Fact p.Prime] (n Xb : ℕ) (hn : n ≤ Xb) :
    ((p.digits n).sum : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by positivity)
  · have hlen := Nat.digits_len p n hp.out.one_lt hpos.ne'
    have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
      have := List.sum_le_card_nsmul (p.digits n) (p - 1)
        (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp.out.one_lt hx))
      simpa [smul_eq_mul] using this
    rw [hlen] at hsum
    have hlog : Nat.log p n ≤ Nat.log p Xb := Nat.log_mono_right hn
    have h2 : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr hsum
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.out.one_lt.le, Nat.cast_one] at h3
      exact h3
    have hl : (Nat.log p n : ℝ) ≤ Nat.log p Xb := by exact_mod_cast hlog
    nlinarith

lemma per_rowX (p : ℕ) [hp : Fact p.Prime] (Xb S o z e Mm : ℕ) (κ κ4 lgv : ℝ)
    (heo : e ≤ o) (ho : o ≤ Xb) (hS : S ≤ Xb) (hz : z + o ≤ Xb) (hL : (Nat.log p Xb : ℝ) + 1 ≤ lgv)
    (hκ0 : 0 ≤ κ) (hM : Mm = ⌈κ⌉₊) :
    -Real.logb p ‖betaT p Mm z o S e‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ4 ≤
      κ + 3 * lgv + κ4 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hq : 0 < (p : ℝ) - 1 := by linarith
  have hA : p ^ Mm * (e.factorial * (z + e).choose e) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne')
  have hB : o.factorial * S.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hβ : betaT p Mm z o S e = ((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p]) /
      ((o.factorial * S.factorial : ℕ) : ℚ_[p]) := by
    simp only [betaT]; push_cast; ring
  have hA' : ‖((p ^ Mm * (e.factorial * (z + e).choose e) : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hA)
  have hB' : ‖((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast hB)
  rw [hβ, norm_div, Real.logb_div hA' hB']
  have e1 := neg_logb_norm_natCast_eq_padicValNat p _ hA
  have e2 := neg_logb_norm_natCast_eq_padicValNat p _ hB
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero)
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'),
    padicValNat.prime_pow, padicValNat.mul (Nat.factorial_ne_zero _)
      (Nat.choose_pos (Nat.le_add_left e z)).ne'] at e1
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at e2
  simp only [Nat.cast_add] at e1 e2
  have hC : (padicValNat p ((z + e).choose e) : ℝ) ≤ Nat.log p Xb := by
    have h := @Nat.factorization_choose_le_log p (z + e) e
    rw [Nat.factorization_def _ hp.out] at h
    exact_mod_cast h.trans (Nat.log_mono_right (by omega))
  have L : ∀ n : ℕ, ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = n - ((p.digits n).sum : ℝ) := by
    intro n
    have h := sub_one_mul_padicValNat_factorial (p := p) n
    have h' : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_sub (Nat.digit_sum_le p n), Nat.cast_sub hp.out.one_lt.le] at h'
    simpa using h'
  have dso := digits_sum_le_sub_one_mul_log_add_one p o Xb ho
  have dsS := digits_sum_le_sub_one_mul_log_add_one p S Xb hS
  have dse : (0 : ℝ) ≤ ((p.digits e).sum : ℝ) := by positivity
  have Le := L e
  have Lo := L o
  have LS := L S
  have hsub : ((S + o - e : ℕ) : ℝ) = (S : ℝ) + o - e := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlv : ((p : ℝ) - 1) * ((Nat.log p Xb : ℝ) + 1) ≤ ((p : ℝ) - 1) * lgv :=
    mul_le_mul_of_nonneg_left hL hq.le
  have hdiv : ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) ≤
      2 * lgv - ((padicValNat p e.factorial : ℝ) - padicValNat p o.factorial - padicValNat p S.factorial) := by
    rw [div_le_iff₀ hq, hsub]
    nlinarith
  have hceil : (Mm : ℝ) < κ + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hκ0
  have hL' : (Nat.log p Xb : ℝ) ≤ lgv - 1 := by linarith
  linarith

theorem meanGamX_of (hDeg : GamDeg) (hLead : GamLead) (hC : GamIntC) (hW : Formalism.GM.WindowFullAP) :
    MeanGamX := by
  intro p hp K r hr LLw q J M ρ z w n₀ f ord s d Yw Xb E κ κ4 lgv U V dg hρ hr2 hv hli hspan hord hfil hE hYw hd
    hcop hSs h2S hzo hYX hrX hL hκ hL4 hsmith
  classical
  have hr1 : 1 ≤ r := by omega
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hPolZ : ∀ b, f b ∈ PolZ p r LLw := fun b =>
    Submodule.mem_inf.mpr ⟨hPol b, (Submodule.mem_inf.mp (hmem b)).2⟩
  have hCI := fun x y => hC p K r LLw ρ z (f x) (f y) hr1 hv (hPolZ x) (hPolZ y)
  choose cc hcc using hCI
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set cI := (K + 4) * (r * Nat.log p (S + o + r)) + 6 * Nat.log p (S + o + r) with hcIdef

  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlgv1 : 1 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ0 : 0 ≤ κ := by
    refine le_trans ?_ hκ
    positivity
  have hoS0 : o ≤ S := Finset.single_le_sum (f := LLw.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hS2a : S ≤ Xb := by omega
  have ho2a : o ≤ Xb := by omega
  have hcI : (cI : ℝ) ≤ κ := by
    have hX1 : Xb ≠ 0 := by omega
    have hl : Nat.log p (S + o + r) ≤ Nat.log p Xb + 1 := by
      rw [← Nat.log_mul_base hp.out.one_lt hX1]
      apply Nat.log_mono_right
      have : 2 ≤ p := hp.out.two_le
      nlinarith
    have hl' : (Nat.log p (S + o + r) : ℝ) ≤ lgv := by
      have : (Nat.log p (S + o + r) : ℝ) ≤ (Nat.log p Xb : ℝ) + 1 := by exact_mod_cast hl
      linarith
    have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 4) * (r : ℝ) + 6 := by positivity
    calc (cI : ℝ) = (((K : ℝ) + 4) * (r : ℝ) + 6) * (Nat.log p (S + o + r) : ℝ) := by
          rw [hcIdef]; push_cast; ring
      _ ≤ (((K : ℝ) + 4) * (r : ℝ) + 6) * lgv := mul_le_mul_of_nonneg_left hl' hK0
      _ ≤ κ := hκ
  have hcIc : cI ≤ ⌈κ⌉₊ := by
    have : (cI : ℝ) ≤ (⌈κ⌉₊ : ℝ) := hcI.trans (Nat.le_ceil κ)
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m + cI = ⌈κ⌉₊ := ⟨⌈κ⌉₊ - cI, Nat.sub_add_cancel hcIc⟩
  obtain ⟨hAeval, hnat, hlead, hord_le, hoS⟩ := lead_part hDeg hLead LLw J M ρ z w n₀ f ord κ4 m cI cc
    hr1 hv hli hspan hord hfil hL4 (fun x y n hn => hcc x y n hn)
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) m cc) with hAqdef
  have hLB := lead_bound p (fun b => ‖betaT p (m + cI) z o S (ord b)‖) (fun b => S + o - ord b) κ4
    (κ + 3 * lgv + κ4) ‖Aq.det.leadingCoeff‖ (fun b => norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) hlead
    (fun b => per_rowX p Xb S o z (ord b) (m + cI) κ κ4 lgv (hord_le b) ho2a hS2a hzo hL hκ0 hm)

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set c' : Fin n₀ → Fin n₀ → ℕ → PadicAlgCl p := fun i j k => alg (coefT p (S + o) m cc i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) (2 * S) c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg (2 * S) _
  have hDk : (binMatK (PadicAlgCl p) (2 * S) c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) (2 * S) c').det
  have hlc : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) (2 * S) c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hprod_pos : 0 < ∏ b, (‖betaT p (m + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ4)) := by
    apply Finset.prod_pos
    intro b _
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos (by linarith) _)
  have hleadne : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm]; exact lt_of_lt_of_le hprod_pos hlead
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) (2 * S) c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * (κ + 3 * lgv + κ4) := by
    rw [hlcnorm, hcard, hnd, hnat]; exact hLB
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap', coefT]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
        rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
      have h2 : ((p : ℝ)⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ m * ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp

  set h := Nat.log p Xb + 1 with hhdef
  have hph : Xb ≤ p ^ h := (Nat.lt_pow_succ_log_self hp.out.one_lt Xb).le
  have hhl : (h : ℝ) ≤ lgv := by rw [hhdef]; push_cast; exact hL
  have hYh : Yw ≤ p ^ h := by omega
  have hdelh : 2 * S ≤ p ^ h := by omega

  set idx : ℤ → ℕ := fun t => ((t - (s : ℤ)) / (d : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (s : ℤ) (d : ℤ) j) = j := by
    intro j
    simp only [hidxdef, progr, add_sub_cancel_left]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')]
    simp
  set U' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (U (idx t)).map alg with hU'
  set V' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (V (idx t)).map alg with hV'
  set dg' : ℤ → Fin n₀ → PadicAlgCl p := fun t b => alg (dg (idx t) b) with hdg'
  have hsm : ∀ j ∈ range Yw, (∀ x y, ‖U' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      ‖(U' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧ ‖(V' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) (2 * S) c').map (Polynomial.eval ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p)) =
        U' (progr (s : ℤ) (d : ℤ) j) * Matrix.diagonal (dg' (progr (s : ℤ) (d : ℤ) j)) *
          V' (progr (s : ℤ) (d : ℤ) j) := by
    intro j hj
    obtain ⟨hU1, hV1, hUd, hVd, hfac⟩ := hsmith j (Finset.mem_range.mp hj)
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hU1 x y
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hV1 x y
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hUd
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hVd
    · rw [hAK]
      ext x y
      have hpt : ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p) = ((s + d * j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      have hfe := congrFun (congrFun hfac x) y
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_diagonal] at hfe
      simp only [Matrix.map_apply, hpt, eval_natCast_map, Matrix.mul_apply, Matrix.mul_diagonal]
      rw [hAeval x y (s + d * j) (le_trans hSs (Nat.le_add_right _ _)), hm, hfe, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [Matrix.diagonal_apply, map_sum]
  have hcop' : IsCoprime (d : ℤ) (p : ℤ) := hcop
  have hE0 : (0 : ℝ) < E := by linarith
  have key := hW p (PadicAlgCl p) n₀ (2 * S) h E c' (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff
    (binMatK (PadicAlgCl p) (2 * S) c').det.roots (s : ℤ) (d : ℤ) Yw (κ + 3 * lgv + κ4) U' V' dg' hcop'
    (by omega) hYh hdelh hE0 hleadne hc'norm hsplit hsm hLB'

  have hcnt : ∀ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ) ≤
      ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) := by
    intro j _
    have hsub : univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E)) ⊆
        univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp only [hdg', hidx, halg, norm_algebraMap']
      exact hb.le
    exact_mod_cast Finset.card_le_card hsub
  have hYpos : (0 : ℝ) < Yw := by exact_mod_cast hYw
  calc (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw
      ≤ (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) /
          Yw := div_le_div_of_nonneg_right (Finset.sum_le_sum hcnt) hYpos.le
    _ ≤ (n₀ : ℝ) * (((2 * S : ℕ) : ℝ) / Yw + ((κ + 3 * lgv + κ4) + ((2 * S : ℕ) : ℝ) * h / Yw) / E) := key
    _ ≤ n₀ * (2 * (LLw.total : ℝ) / Yw + ((κ + 3 * lgv + κ4) + 2 * (LLw.total : ℝ) * lgv / Yw) / E) := by
      rw [← hSdef]
      push_cast
      have h1 : 2 * (S : ℝ) * h / Yw ≤ 2 * (S : ℝ) * lgv / Yw := by
        apply div_le_div_of_nonneg_right _ hYpos.le
        exact mul_le_mul_of_nonneg_left hhl (by positivity)
      have h2 : (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * h / Yw ≤ (κ + 3 * lgv + κ4) + 2 * (S : ℝ) * lgv / Yw := by
        linarith
      have h3 := div_le_div_of_nonneg_right h2 hE0.le
      have hn0 : (0 : ℝ) ≤ n₀ := by positivity
      nlinarith

end Formalism.InvariantFactorPaths.MC
end

section
namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

theorem gamma_zero_integral {p : ℕ} [Fact p.Prime] (K r : ℕ) (LLw : Letters (K + 1)) (ρ : Fin r) (n a : ℕ) (κ : ℝ)
    (hS : LLw.total ≤ n) (hn : n ≤ a) (h4 : (K + 2) * (r * Nat.log p a) ≤ ⌈κ⌉₊)
    (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hf : f ∈ PolZ p r LLw) (hf' : f' ∈ PolZ p r LLw) :
    ‖(p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p LLw ρ n f) (freeze p LLw ρ n f') /
      ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])))‖ ≤ 1 := by
  classical
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)
  obtain ⟨hfP, hfI⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hfP', hfI'⟩ := Submodule.mem_inf.mp hf'
  obtain ⟨hFP, -, hFI⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP
  obtain ⟨-, -, hFI'⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'
  set F := freeze p LLw ρ n f with hF
  set F' := freeze p LLw ρ n f' with hF'
  have hc := gammaIntegralityLemmas.intPol_coeff F (hFI hfI)
  have hc' := gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')
  set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')
  have hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p]) := by
    rw [hDen]; push_cast; ring
  rw [hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]
  refine gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_
  intro m hm
  have hmd : MultiDeg (LLw.snoc n) m := by
    rw [Pol, mem_restrictSupport_iff] at hFP
    exact hFP (Finset.mem_coe.mpr hm)
  set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum
  have hNum0 : Num ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hwf : gammaIntegralityLemmas.wf (p := p) m = (Num : ℚ_[p]) := by
    rw [hNum, gammaIntegralityLemmas.wf]; push_cast; rfl
  rw [hwf]
  have hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i := fun i => hmd i
  have hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ a := by
    intro i
    rw [hδ]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [FrozenVariableComponents.snoc_deg_last]; exact hn
    · rw [FrozenVariableComponents.snoc_deg_castSucc]
      exact (gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)
  have h1 := gammaIntegralityLemmas.vW_ge (p := p) m (T := a) (B := Nat.log p (a)) le_rfl hT
  rw [Fin.sum_univ_castSucc] at h1
  simp only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1
  have h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial +
      ∑ i, padicValNat p (LLw.deg i).factorial := by
    rw [hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne',
      gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤
      padicValNat p n.factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial hS
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne')
      (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']
    omega
  have h5 := gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m)
    Num Den hNum0 hDen0 1 norm_one (by
      have : (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ) := by
        have : padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊ := by
          rw [h2]
          have h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤
              padicValNat p Num + (K + 2) * (r * Nat.log p (a)) := h1
          omega
        exact_mod_cast this
      omega)
  rw [one_mul] at h5
  exact h5

theorem tieOpsX_main : TieOpsX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ _hp2 hr hρ hadm hE hSn hdeg hL hκ hHP hHW nb f U V dg fw hf hUV hfw i
  classical
  have hK : T.pos i + 1 + 1 ≤ N := hK_of_adm LL T hadm i
  have hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i := by
    rw [S_eq_total (LL.setTies T n) T i (by omega)]; exact hSn i
  have hni : n i ≤ Xb := by
    have := hdeg ⟨T.pos i + 1, by omega⟩
    rwa [setTies_deg_eta LL T hadm i n (by omega)] at this
  obtain ⟨coef, hcoef⟩ : ∃ coef : ℕ, coef =
      (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) + n i + r + T.z i - 1).choose
          (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i))) := ⟨_, rfl⟩
  obtain ⟨NN, hNN⟩ : ∃ NN : ℚ_[p], NN =
      ((((n i - ((LL.setTies T n).takeD (T.pos i + 1)).total).factorial *
            ((LL.setTies T n).takeD (T.pos i + 1)).total.factorial : ℕ) : ℚ_[p]) *
          ∏ x, ((((LL.setTies T n).takeD (T.pos i + 1)).deg x).factorial : ℚ_[p])) := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst : ℚ_[p], cst = (p : ℚ_[p]) ^ ⌈κ⌉₊ * (coef : ℚ_[p]) / NN := ⟨_, rfl⟩
  have hgam : ∀ g g', (p : ℚ_[p]) ^ ⌈κ⌉₊ * tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) g g' =
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    rw [gam_eq LL T hadm i ρ n g g', ← hcoef, ← hNN, hcst]
    ring
  let B : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]]
      MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    cst • ((fockB p (Fin N × Fin r)).compl₁₂ ((T.phi p (LL.setTies T n) i) ∘ₗ FfL p (LL.setTies T n) T i ρ (n i))
      (FfL p (LL.setTies T n) T i ρ (n i)))
  have hB : ∀ g g', B g g' = cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) g))
        (T.Ffull p (LL.setTies T n) i ρ (n i) g') := by
    intro g g'
    simp [B, fockB_apply, FfL_apply]
  have hsm : ∀ w, ∃ f' f'' : Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
      (∀ a, f' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      (∀ a, f'' a ∈ MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) ∧
      LinearIndependent ℚ_[p] f' ∧
      MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg i w a else 0 := by
    intro w
    obtain ⟨hU1, hV1, hU2, hV2, hfac⟩ := hUV i w
    refine smith_bases (nb i w) (f i w) _ (hf i w).1 (hf i w).2 B (U i w) (V i w) (dg i w) hU1 hV1 hU2 hV2 ?_
    rw [← hfac]
    ext x y
    simp only [Matrix.of_apply]
    rw [hB, hgam]
  choose f' f'' hf'1 hf''1 hf'li hf'sp hf'diag using hsm
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Finset (Fin r → ℤ), ∀ w, w ∈ Ω ↔
      MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ :=
    ⟨(mmw_finite (p := p) LL T i ρ n).toFinset, fun w => by simp⟩
  have hnb0 : ∀ w, w ∉ Ω → nb i w = 0 := by
    intro w hw
    by_contra h0
    have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w = ⊥ := by
      by_contra h; exact hw ((hΩ w).mpr h)
    have hmem : f i w ⟨0, Nat.pos_of_ne_zero h0⟩ ∈
        MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
      rw [← (hf i w).2]; exact Submodule.subset_span ⟨_, rfl⟩
    have h1 := mmwZ_mmw _ _ _ _ _ hmem
    rw [hbot, Submodule.mem_bot] at h1
    exact (hf i w).1.ne_zero _ h1
  have hκ' : (T.pos i + 2) * (r * Nat.log p Xb) ≤ ⌈κ⌉₊ := by
    have hl0 : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : ((T.pos i : ℝ) + 2) ≤ (N : ℝ) + 2 := by
      have : ((T.pos i + 1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
      push_cast at this; linarith
    have h2 : (r : ℝ) * (Nat.log p Xb : ℝ) ≤ (r : ℝ) ^ 2 * lgv :=
      mul_le_mul (by nlinarith) (by linarith) hl0 (by positivity)
    have h3 : (((T.pos i + 2) * (r * Nat.log p Xb) : ℕ) : ℝ) ≤ κ := by
      push_cast
      calc ((T.pos i : ℝ) + 2) * ((r : ℝ) * (Nat.log p Xb : ℝ)) ≤ ((N : ℝ) + 2) * ((r : ℝ) ^ 2 * lgv) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = ((N + 2) * r ^ 2 : ℝ) * lgv := by ring
        _ ≤ κ := hκ
    exact_mod_cast h3.trans (Nat.le_ceil κ)
  have hspZ : ∀ μ v, v ∈ TO.Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr →
      (GA p (LL.setTies T n) (T.pos i + 1 + 1)).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      v ∈ Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)) := by
    intro μ v hv hw hvi
    obtain ⟨g, hg, rfl⟩ := hw_is_Ffull LL T hadm i ρ hρ n hS μ v hv hw hvi
    by_cases hwΩ : (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ∈ Ω
    · have hg' := hf'sp _ hg
      refine Submodule.span_induction (p := fun g _ => T.Ffull p (LL.setTies T n) i ρ (n i) g ∈
        Submodule.span ℤ_[p] (Set.range fun x : (Σ w : Ω, Fin (nb i w.1)) =>
          T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))) ?_ ?_ ?_ ?_ hg'
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨⟨⟨_, hwΩ⟩, b⟩, rfl⟩
      · rw [← FfL_apply, map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [← FfL_apply, map_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [← FfL_apply, LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx
    · have hbot : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) = ⊥ := by
        by_contra h; exact hwΩ ((hΩ _).mpr h)
      have h1 := mmwZ_mmw _ _ _ _ _ hg
      rw [hbot, Submodule.mem_bot] at h1
      rw [h1, ← FfL_apply, map_zero]; exact Submodule.zero_mem _
  have hdiag : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      x.1.1 - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) = y.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1 →
      cst * fock p (T.phi p (LL.setTies T n) i (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2)))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f'' y.1.1 y.2)) = if x = y then dg i x.1.1 x.2 else 0 := by
    rintro ⟨⟨w, hw⟩, b⟩ ⟨⟨w', hw'⟩, b'⟩ hla
    have hww : w = w' := sub_left_injective hla
    subst hww
    have := hf'diag w b b'
    rw [hB] at this
    simp only
    rw [this]
    by_cases hbb : b = b'
    · subst hbb; simp
    · rw [if_neg hbb, if_neg]
      intro h
      apply hbb
      simpa using h
  have hG0 : ∀ x y : (Σ w : Ω, Fin (nb i w.1)),
      ‖cst * fock p (T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
        (T.Ffull p (LL.setTies T n) i ρ (n i) (f' y.1.1 y.2))‖ ≤ 1 := by
    intro x y
    rw [fock_Ffull LL T hadm i ρ n]
    have hg := gamma_zero_integral (p := p) (T.pos i) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) Xb κ hS hni hκ'
      (f' x.1.1 x.2) (f' y.1.1 y.2) (mmwZ_polZ _ _ _ _ _ (hf'1 x.1.1 x.2)) (mmwZ_polZ _ _ _ _ _ (hf'1 y.1.1 y.2))
    rw [← hNN] at hg
    have e : cst * fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) =
        (coef : ℚ_[p]) * ((p : ℚ_[p]) ^ ⌈κ⌉₊ *
          (fock p (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' x.1.1 x.2))
        (freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) (f' y.1.1 y.2)) / NN)) := by
      rw [hcst]; ring
    rw [e, norm_mul]
    exact mul_le_one₀ (gammaIntegralityLemmas.norm_natCast_le_one' coef) (norm_nonneg _) hg
  obtain ⟨Tm, πm, h1, h2, h3, h4, h5⟩ := tie_core (LL.setTies T n) T hadm i ρ e1 hK hHP hHW E (by linarith)
    (ι := Σ w : Ω, Fin (nb i w.1))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f' x.1.1 x.2))
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (f'' x.1.1 x.2))
    (fun x => x.1.1 - ((n i : ℕ) : ℤ) • Pi.single ρ 1)
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf'1 x.1.1 x.2)))
    (Ffull_indep LL T hadm i ρ n hS Ω (nb i) f' (fun w a => mmwZ_mmw _ _ _ _ _ (hf'1 w a)) hf'li)
    hspZ
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)) hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (mmwZ_mmw _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => Ffull_int LL T hadm i ρ n hS _ (mmwZ_polZ _ _ _ _ _ (hf''1 x.1.1 x.2)))
    (fun x => dg i x.1.1 x.2) cst hdiag hG0
    (fun x => T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))
    (fun x => Ffull_hw LL T hadm i ρ hρ n x.1.1 _ (hfw i x.1.1).1 hS)
    (fun x => Ffull_C LL T hadm i ρ n hS x.1.1 _ (hfw i x.1.1).1)
    (fun x => Ffull_ne LL T hadm i ρ n x.1.1 _ (hfw i x.1.1).1 ((hfw i x.1.1).2 ((hΩ _).mp x.1.2)) hS)
  refine ⟨Tm, πm, e1 * (T.pos i + 1 + 1) + 2 * e1,
    (by nlinarith [hK, Nat.zero_le e1]), h1, h2, h3, fun j hij u _ => h4 j hij u, ?_⟩
  have hsumN : ∑ x ∈ univ.filter (fun x : (Σ w : Ω, Fin (nb i w.1)) => ‖dg i x.1.1 x.2‖ < (p : ℝ) ^ (-E)),
      Module.finrank ℚ_[p] (TO.YYs (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
        (T.Ffull p (LL.setTies T n) i ρ (n i) (fw i x.1.1))) =
      ∑ w ∈ Ω, (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card *
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) := by
    rw [Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort Ω]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_filter, TO.YYsp_eq]
    exact Finset.sum_const_nat (fun _ _ => rfl)
  have hfs : ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) =
      ∑ w ∈ Ω, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    rw [Finset.mem_coe]
    by_contra hwΩ
    refine hw ?_
    have hle : (univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card ≤ nb i w :=
      (Finset.card_le_univ _).trans (by simp)
    have hle0 := Nat.le_zero.mp (hle.trans (hnb0 w hwΩ).le)
    simp only [hle0, Nat.cast_zero, zero_mul]
  rw [hfs]
  rw [hsumN] at h5
  exact_mod_cast h5

theorem partnerMX_of_parts (hT : TieOpsX) (hY : YPartnerC) : PartnerMX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ h2p hr hρ hadm hE hS hdeg hL hκ he1 hHP hHW nb f U V dg fw h1 h2 h3
  have hops := hT p N r LL T Xb E κ lgv e1 n ρ h2p hr hρ hadm hE hS hdeg hL hκ hHP hHW nb f U V dg fw h1 h2 h3
  choose Tm πm Kf hK hTY hTint hadj hcomm hrank using hops
  have hadm' : T.Admissible (LL.setTies T n) := hadm
  set LL' := LL.setTies T n with hLL'
  set Ysp : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Y p (r := r) LL' T.J T.thr with hYsp
  set W : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Ysp ⊓ (Finset.univ : Finset (Fin T.t)).inf (fun i => LinearMap.ker (πm i - LinearMap.id)) with hW
  have hYpol : Ysp ≤ Pol p r LL' := inf_le_left
  have hWY : W ≤ Ysp := inf_le_left
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hsat : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 →
      x ∈ YZ p (r := r) LL' T.J T.thr → c • x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' →
      x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' := by
    intro c x hc hx hcx
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hx).2⟩
    have hxY : x ∈ Ysp := (Submodule.mem_inf.mp hx).1
    have hcW : c • x ∈ W := (Submodule.mem_inf.mp hcx).1
    show x ∈ W
    refine Submodule.mem_inf.mpr ⟨hxY, ?_⟩
    rw [Submodule.mem_finsetInf]
    intro i _
    have hci := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp hcW).2) i (Finset.mem_univ i)
    rw [LinearMap.mem_ker] at hci ⊢
    rw [← algebraMap_smul ℚ_[p] c x, map_smul, smul_eq_zero] at hci
    rcases hci with h | h
    · exact absurd (PadicInt.ext (h.trans PadicInt.coe_zero.symm)) hc
    · exact h
  have hL1Y : W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' ≤ YZ p (r := r) LL' T.J T.thr :=
    inf_le_inf_right (PolZ p r LL') (show W.restrictScalars ℤ_[p] ≤ Ysp.restrictScalars ℤ_[p] from fun x hx => hWY hx)
  refine ⟨W.restrictScalars ℤ_[p] ⊓ PolZ p r LL', hL1Y, hsat, ?_, ?_⟩
  ·
    intro u hu hprim
    have huY : u ∈ YZ p (r := r) LL' T.J T.thr := hL1Y hu
    have hprimY : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL' T.J T.thr →
        u = c • x → IsUnit c := by
      intro c x hx hux
      by_cases hc : c = 0
      · exfalso
        have hu0 : u = 0 := by rw [hux, hc, zero_smul]
        have := hprim 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero])
        exact not_isUnit_zero this
      · exact hprim c x (hsat c x hc hx (hux ▸ hu)) hux
    obtain ⟨z'', hz'', hnorm⟩ := hY p N r LL' T.J T.thr ρ e1 hr hHP u huY hprimY
    obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = e1 * (N + 1) := ⟨_, rfl⟩
    rw [← hK₀] at hnorm
    set e := ⌊E⌋₊ with he
    let Ts : Fin T.t → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
      fun i => ((p : ℚ_[p]) ^ (Kf i)) • Tm i
    have hTsZ : ∀ i, ∀ y ∈ YZ p (r := r) LL' T.J T.thr, Ts i y ∈ YZ p (r := r) LL' T.J T.thr := by
      intro i y hy
      have hyY : y ∈ Ysp := (Submodule.mem_inf.mp hy).1
      have h1 : Ts i y ∈ Ysp := Ysp.smul_mem _ (hTY i y hyY)
      exact Submodule.mem_inf.mpr ⟨h1, Submodule.mem_inf.mpr ⟨hYpol h1, hTint i y hy⟩⟩
    have hTsY : ∀ i, ∀ y ∈ (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])), Ts i y ∈ Ysp :=
      fun i y hy => Ysp.smul_mem _ (hTY i y hy)
    set u' := lcomp Ts (List.finRange T.t) z'' with hu'
    have hu'Z : u' ∈ YZ p (r := r) LL' T.J T.thr :=
      lcomp_keep Ts (YZ p (r := r) LL' T.J T.thr : Set _) (List.finRange T.t) (fun j _ => hTsZ j) z'' hz''
    refine ⟨u', hu'Z, ?_⟩
    have hfix : ∀ i ∈ List.finRange T.t, πm i u = u := by
      intro i _
      have huW : u ∈ W := (Submodule.mem_inf.mp hu).1
      have := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp huW).2) i (Finset.mem_univ i)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    have hpeel := peel (fockN p LL') (T.phi p LL') Ts πm (fun i => (p : ℚ_[p]) ^ (Kf i + e))
      (fun i => (Y p (r := r) LL' T.J (T.thrUpTo i) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))
      (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (fun i => fun x hx => y_le_thrUpTo LL' T i hx) hTsY
      (fun i j hij => phi_keeps LL' T hadm' i j hij)
      (fun i j hij => hcomm i j hij)
      (fun i u hu u' hu' => by
        show fockN p LL' (T.phi p LL' i u) (((p : ℚ_[p]) ^ (Kf i)) • Tm i u') = _
        rw [fockN_smul_right', hadj i u hu u' hu', pow_add]; ring)
      (List.finRange T.t) (List.pairwise_lt_finRange T.t) u (hWY (Submodule.mem_inf.mp hu).1) hfix z''
      (Submodule.mem_inf.mp hz'').1
    have hphis : T.phis p (r := r) LL' = lcomp (T.phi p (r := r) LL') (List.finRange T.t) := rfl
    rw [hphis, hpeel]
    have hS' : (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ (T.t : ℝ) * (E + κ) := by
      have hb : ∀ i, ((Kf i + e : ℕ) : ℝ) ≤ E + κ := by
        intro i; push_cast
        have h1 : (Kf i : ℝ) ≤ ((e1 * (N + 2) : ℕ) : ℝ) := by exact_mod_cast hK i
        have h2 : (e : ℝ) ≤ E := Nat.floor_le (by linarith)
        linarith
      calc (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ ∑ _i : Fin T.t, (E + κ) := Finset.sum_le_sum fun i _ => hb i
        _ = (T.t : ℝ) * (E + κ) := by simp; ring
    have hK0' : (K₀ : ℝ) ≤ κ := by
      have h1 : (K₀ : ℝ) ≤ ((e1 * (N + 2) : ℕ) : ℝ) := by
        rw [hK₀]; exact_mod_cast Nat.mul_le_mul_left e1 (by omega)
      linarith
    have hD : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℤ) ≤ ⌊(T.t : ℝ) * (E + κ) + κ⌋ := by
      apply Int.le_floor.mpr
      have : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℝ) = (∑ i, ((Kf i + e : ℕ) : ℝ)) + K₀ := by push_cast; rfl
      rw [Int.cast_natCast, this]
      linarith
    have hprod : ((List.finRange T.t).map (fun i => (p : ℚ_[p]) ^ (Kf i + e))).prod =
        (p : ℚ_[p]) ^ (∑ i, (Kf i + e)) := by
      rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
    rw [hprod, norm_mul, norm_pow, Padic.norm_p]
    calc (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + κ) + κ⌋)
        ≤ (p : ℝ) ^ (-((((∑ i, (Kf i + e)) + K₀ : ℕ)) : ℤ)) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * (p : ℝ) ^ (-(K₀ : ℤ)) := by
        rw [Nat.cast_add, neg_add, zpow_add₀ (ne_of_gt hp0), zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * ‖fockN p LL' u z''‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
  ·
    haveI := pol_finiteDimensional (p := p) (r := r) LL'
    haveI : FiniteDimensional ℚ_[p] Ysp := Submodule.finiteDimensional_of_le hYpol
    have q1 : Module.finrank ℤ_[p] (YZ p (r := r) LL' T.J T.thr) = Module.finrank ℚ_[p] Ysp :=
      finrank_lattice LL' Ysp hYpol
    have q2 : Module.finrank ℤ_[p] (W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' : Submodule ℤ_[p] _) =
        Module.finrank ℚ_[p] W := finrank_lattice LL' W (hWY.trans hYpol)
    rw [q1, q2]
    have hc := codim_inf_le Ysp (fun i => LinearMap.ker (πm i - LinearMap.id)) univ
    refine (Nat.cast_le.mpr hc).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hrank i

theorem pointMX_of_partner (hBad : BadCrit) (hP : PartnerMX) : PointMX := by
  intro p _ N r _ _ LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  obtain ⟨L₁, hL₁, hsat, hprim, hrank⟩ :=
    hP p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hT hE hS hdeg hlg hκ hκ' hPP hW nb f U V dg fw hf hUV hfw
  have hfin : Module.Finite ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) := by
    haveI : IsNoetherian ℤ_[p] (PolZ p r (LL.setTies T n)) :=
      isNoetherian_of_fg_of_noetherian _ (polZ_fg (LL.setTies T n))
    haveI : IsNoetherian ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) :=
      isNoetherian_of_le (fun x hx => by unfold YZ at hx; exact hx.2)
    infer_instance
  have hb : bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ ≤
      Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ :=
    hBad p (MvPolynomial (Fin N × Fin r) ℚ_[p])
      (fockBil (LL.setTies T n) (T.phis p (LL.setTies T n))) (YZ p (r := r) (LL.setTies T n) T.J T.thr) L₁
      ⌊(T.t : ℝ) * (E + κ) + κ⌋ hfin hL₁ hsat hprim
  exact le_trans (Nat.cast_le.mpr hb) hrank

end Formalism.InvariantFactorPaths.MC
end

section
namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.TM Formalism.GM.M Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset

theorem theoremMXB_of_point (hMG : MeanGamX) (hMono : WeightSpaceDimMonotone) (hCount : MonoCount) (hSmith : SmithZp)
    (hAd : AdaptedBasisExists) (hPW : PointMX) : TheoremMXB := by
  intro p _ N r _ _ LL T Xb E κ κ4 lgv e1 Yl n₀ dd ρ hp2 hr hρ hadm hE hYd hS hdeg hsz hrX hL hκ32 he1 hκ4 hHyp
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgv := by
    have : (0 : ℝ) ≤ (Nat.log p Xb : ℝ) := Nat.cast_nonneg _
    linarith
  have hκ : ((N + 2) * r ^ 2 : ℝ) * lgv ≤ κ := by
    have : 0 ≤ ((N + 2) * r ^ 2 : ℝ) * lgv := by positivity
    linarith
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ

  choose nb fb ord hli hsp hord hfil using fun (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) =>
    hAd p (T.pos i) r L0 T.J (T.thrUpTo i) ρ w
  choose Uc Vc dgc hUc using fun (k : ℕ) (A : Matrix (Fin k) (Fin k) ℚ_[p]) => smith_qp hSmith A
  have hfwex : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ), ∃ g,
      g ∈ MMw p L0 T.J (T.thrUpTo i) ρ w ∧ (MMw p L0 T.J (T.thrUpTo i) ρ w ≠ ⊥ → g ≠ 0) := by
    intro i L0 w
    by_cases h : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
    · exact ⟨0, Submodule.zero_mem _, fun h' => absurd h h'⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨g, hg, fun _ => hg0⟩
  choose fw hfw using hfwex
  have hnb : ∀ i L0 w, nb i L0 w = Module.finrank ℚ_[p] (MMw p L0 T.J (T.thrUpTo i) ρ w) := fun i L0 w =>
    (finrank_of_lattice_basis _ (fb i L0 w) (hli i L0 w) (hsp i L0 w)).symm
  let MatF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ),
      Matrix (Fin (nb i L0 w)) (Fin (nb i L0 w)) ℚ_[p] := fun i L0 w y =>
    Matrix.of fun x x' => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p L0 ρ (T.z i) y (fb i L0 w x) (fb i L0 w x')
  let cntF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), ℕ := fun i L0 w y =>
    (univ.filter (fun b => ‖dgc _ (MatF i L0 w y) b‖ < (p : ℝ) ^ (-E))).card
  let Bx : ∀ i : Fin T.t, Letters (T.pos i + 1) → Finset (Fin r → ℤ) := fun i L0 =>
    Fintype.piFinset fun _ => Icc (-(L0.total : ℤ)) L0.total
  have hcntle : ∀ i L0 w y, cntF i L0 w y ≤ nb i L0 w := fun i L0 w y =>
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbot : ∀ i L0 w, w ∉ Bx i L0 → MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥ := fun i L0 w hw => by
    by_contra h; exact hw (mmw_ne_bot_box L0 T.J (T.thrUpTo i) ρ w h)
  have hnb0 : ∀ i L0 w, w ∉ Bx i L0 → nb i L0 w = 0 := fun i L0 w hw => by
    rw [hnb, hbot i L0 w hw, finrank_bot]
  have hcnt0 : ∀ i L0 w y, w ∉ Bx i L0 → cntF i L0 w y = 0 := fun i L0 w y hw =>
    Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (hnb0 i L0 w hw).le)
  let sI : Fin T.t → Finset ℕ := fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)
  let top : Fin T.t → ℕ := fun i => n₀ i + dd i * (Yl i - 1)
  have hsI : ∀ i y, y ∈ sI i → n₀ i ≤ y ∧ y ≤ top i := by
    intro i y hy
    simp only [sI, mem_image, mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩
  have hgrid : ∀ n ∈ Fintype.piFinset sI, ∀ i, n₀ i ≤ n i ∧ n i ≤ top i := fun n hn i =>
    hsI i (n i) (Fintype.mem_piFinset.mp hn i)
  have hinj : ∀ i, Set.InjOn (fun j => n₀ i + dd i * j) (range (Yl i) : Set ℕ) := by
    intro i x _ y _ hxy
    have := (hYd i).2.1
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left this (by omega)
  have hcard : ∀ i, (sI i).card = Yl i := fun i => by
    simp only [sI]; rw [Finset.card_image_of_injOn (hinj i), Finset.card_range]
  let BB : Fin T.t → (Fin T.t → ℕ) → ℝ := fun i n =>
    ∑ w ∈ Bx i ((LL.setTies T n).takeD (T.pos i + 1)),
      (cntF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)) : ℝ)
  refine grid_average sI (fun n => (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ)) BB
    (fun i n => (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ))
    (fun i => 2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
      (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E)
    (fun i => by rw [hcard]; exact (hYd i).1) ?_ ?_
  · intro n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    have hSn : ∀ i, T.S (LL.setTies T n) i ≤ n i := fun i =>
      (S_mono LL T n top hnt i).trans ((hS i).trans (hgrid n hn i).1)
    have hdegn : ∀ x, (LL.setTies T n).deg x ≤ Xb := fun x =>
      (setTies_deg_mono LL T n top hnt x).trans (hdeg x)
    obtain ⟨hP, hW, hL4⟩ := hHyp n hn
    have key := hPW p N r LL T Xb E κ lgv e1 n ρ hp2 hr hρ hadm hE hSn hdegn hL hκ he1 hP hW
      (fun i w => nb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => fb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => Uc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => Vc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => dgc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => ⟨hli _ _ _, hsp _ _ _⟩) (fun i w => hUc _ _) (fun i w => hfw _ _ _)
    refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    apply finsum_eq_sum_of_support_subset
    intro w hw
    by_contra hwn
    apply hw
    have h0 := hcnt0 i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) hwn
    simp only [cntF] at h0
    simp only [h0, Nat.cast_zero, zero_mul]
  · intro i n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    obtain ⟨hlt, hvW, _⟩ := hadm.2.1 i
    obtain ⟨_, _, hL4⟩ := hHyp n hn
    have hLW : ∀ y, (LL.setTies T (Function.update n i y)).takeD (T.pos i + 1) =
        (LL.setTies T n).takeD (T.pos i + 1) := fun y => takeD_setTies_update LL T n i y
    have hL0S : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T top) i := by
      rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n top hnt i
    have hL0tot : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n₀ i := hL0S.trans (hS i)
    have hvec : ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
      simp only [Letters.takeD, Fin.val_last]
      rw [dif_pos (by omega)]
      exact hvW
    have h2S : 2 * ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ Xb := by
      exact (Nat.mul_le_mul_left 2 hL0S).trans (hsz i).1
    have hzo : T.z i + ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) ≤ Xb := by
      have h1 := (hsz i).2.2 (by omega)
      have h2 : ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) =
          (LL.setTies T n).deg ⟨T.pos i, by omega⟩ := by
        simp only [Letters.takeD, Fin.val_last]
        rw [dif_pos (by omega)]
      have h3 := setTies_deg_mono LL T n top hnt ⟨T.pos i, by omega⟩
      rw [h2]
      exact (Nat.add_le_add_left h3 _).trans h1
    have hκi : ((((T.pos i : ℕ) : ℝ) + 4) * r + 6 : ℝ) * lgv ≤ κ := by
      refine le_trans ?_ hκ32
      have hP4 : ((T.pos i : ℕ) : ℝ) + 4 ≤ (N : ℝ) + 2 := by
        have : T.pos i + 4 ≤ N + 2 := by omega
        exact_mod_cast this
      have hP0 : (0 : ℝ) ≤ ((T.pos i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have hN4 : (4 : ℝ) ≤ (N : ℝ) + 2 := by linarith
      have g1 : 2 * (((N : ℝ) + 2) * r) ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := by
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) + 2) (by linarith : (0 : ℝ) ≤ (r : ℝ)))
          (sub_nonneg.mpr hr')
        nlinarith
      have g2 : (8 : ℝ) ≤ ((N : ℝ) + 2) * r := by
        have := mul_le_mul hN4 hr' (by norm_num) (by linarith)
        linarith
      have g3 : (((T.pos i : ℕ) : ℝ) + 4) * r ≤ ((N : ℝ) + 2) * r := mul_le_mul_of_nonneg_right hP4 (by linarith)
      have g4 : (((T.pos i : ℕ) : ℝ) + 4) * r + 6 ≤ 3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2) := by linarith
      calc ((((T.pos i : ℕ) : ℝ) + 4) * r + 6 : ℝ) * lgv
          ≤ (3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2)) * lgv := mul_le_mul_of_nonneg_right g4 hlg
        _ = 3 / 2 * (((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgv) := by ring
    set L0 := (LL.setTies T n).takeD (T.pos i + 1) with hL0
    have qe1 : ∀ y, BB i (Function.update n i y) = ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) := by
      intro y
      simp only [BB]
      rw [hLW y, Function.update_self]
    simp only [qe1]

    have hmono : ∀ y ∈ sI i, ∀ w, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) ≤
        (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
      intro y hy w
      by_cases hM : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
      · have : cntF i L0 w y = 0 := Nat.eq_zero_of_le_zero
          ((hcntle i L0 w y).trans (by rw [hnb, hM, finrank_bot]))
        simp [this]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hm := hMono p N r LL T hadm ρ hρ hr i (Function.update n i y) w (fw i L0 w)
          (by rw [hLW y]; exact (hfw i L0 w).1) ((hfw i L0 w).2 hM)
          (by rw [hLW y, Function.update_self]; exact hL0tot.trans (hsI i y hy).1) (top i)
          (by rw [Function.update_self]; exact (hsI i y hy).2)
        rw [Function.update_idem] at hm
        exact_mod_cast hm

    have hmean : ∀ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) ≤
        (Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E)) := by
      intro w _
      have hm := hMG p (T.pos i) r L0 T.J (T.thrUpTo i) ρ (T.z i) w (nb i L0 w) (fb i L0 w) (ord i L0 w)
        (n₀ i) (dd i) (Yl i) Xb E κ κ4 lgv (fun j => Uc _ (MatF i L0 w (n₀ i + dd i * j)))
        (fun j => Vc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => dgc _ (MatF i L0 w (n₀ i + dd i * j)))
        hρ hr hvec (hli _ _ _) (hsp _ _ _) (hord _ _ _) (hfil _ _ _) hE (hYd i).1 (hYd i).2.1 (hYd i).2.2
        hL0tot h2S hzo (hsz i).2.1 hrX hL hκi (hL4 i) (fun j _ => hUc _ _)
      have hY0 : (0 : ℝ) < Yl i := by exact_mod_cast (hYd i).1
      rw [div_le_iff₀ hY0] at hm
      have hsum : (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) =
          ∑ j ∈ range (Yl i), ((univ.filter (fun b =>
            ‖dgc _ (MatF i L0 w (n₀ i + dd i * j)) b‖ < (p : ℝ) ^ (-E))).card : ℝ) := by
        simp only [sI]
        rw [Finset.sum_image (hinj i)]
      rw [hsum]
      refine hm.trans ?_
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ hY0.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hE0 : (0 : ℝ) < E := by linarith
      have hL : ((L0.total : ℕ) : ℝ) ≤ (T.S (LL.setTies T top) i : ℝ) := by exact_mod_cast hL0S
      have hC : κ + 3 * lgv + κ4 ≤ 2 * κ := by linarith
      gcongr

    have hcount : (∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) =
        (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ) := by
      have hc := hCount p N r LL T hadm ρ hρ hr i (Function.update n i (top i))
        (by rw [hLW, Function.update_self]; exact hL0tot.trans (Nat.le_add_right _ _)) (fun w => fw i L0 w)
        (fun w => by rw [hLW]; exact hfw i L0 w)
      rw [hLW] at hc
      rw [finsum_eq_sum_of_support_subset _ (s := Bx i L0) (fun w hw => by
        by_contra hwn
        apply hw
        beta_reduce
        rw [← hnb, hnb0 i L0 w hwn, zero_mul])] at hc
      rw [← hc]
      push_cast
      apply Finset.sum_congr rfl
      intro w _
      rw [hnb]
    calc ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ)
        ≤ ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun w _ => hmono y hy w
      _ = ∑ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ ∑ w ∈ Bx i L0, ((Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E))) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hmean w hw) (Nat.cast_nonneg _)
      _ = (sI i).card * ((2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgv / Yl i) / E) *
            ∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
              (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) := by
          rw [hcard, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      _ = _ := by rw [hcount]

end Formalism.InvariantFactorPaths.MC
end

section
namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

theorem meanGamX : MeanGamX :=
  meanGamX_of (by first | exact Formalism.GM.gamma_degree_bound | exact Formalism.GM.Top.gamDeg)
    (by first | exact Formalism.GM.gamma_leading_term | exact Formalism.GM.Top.gamLead)
    (by first | exact Formalism.InvariantFactorPaths.MC.gamma_integral_holds | exact Formalism.InvariantFactorPaths.MC.Top.gamIntC)
    (by first | exact Formalism.GM.Top.windowFullAP | exact Top.windowFullAP)

theorem theoremMXB : TheoremMXB :=
  theoremMXB_of_point meanGamX
    (by first | exact DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.M.DimensionMonotonicity.highest_weight_dim_monotone | exact Formalism.GM.TM.DimensionMonotonicity.highest_weight_dim_monotone)
    (by first | exact monomial_count | exact Formalism.GM.monomial_count | exact Formalism.GM.M.monomial_count | exact Formalism.GM.TM.monomial_count)
    (by first | exact Formalism.GM.Top.smithZp | exact Formalism.GM.smith_form_p_adic_integers | exact Formalism.GM.TM.smith_form_p_adic_integers | exact Formalism.GM.M.smith_form_p_adic_integers)
    (by first | exact Formalism.GM.TM.existsAdaptedBasis | exact Formalism.GM.existsAdaptedBasis | exact Formalism.GM.Top.adaptedBasis)
    (pointMX_of_partner
      (by first | exact bad_criterion_holds | exact Formalism.InvariantFactorPaths.MC.bad_criterion_holds | exact Formalism.GM.bad_criterion_holds | exact Formalism.InvariantFactorPaths.MC.Top.badCrit | exact Formalism.GM.Top.badCrit)
      (partnerMX_of_parts tieOpsX_main (by first | exact partner_condition_holds | exact Formalism.InvariantFactorPaths.MC.Top.yPartnerC | exact Formalism.InvariantFactorPaths.MC.Top.yPartner)))

theorem natLog_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r x : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (hx : (x : ℝ) ≤ p * (8 * a + r)) : (Nat.log p x : ℝ) ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp hy
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  · have h1 : ((p ^ Nat.log p x : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hx0.ne'
    push_cast at h1
    have hpy : (0 : ℝ) < p * (8 * a + r) := mul_pos (by linarith) (by linarith)
    have h2 : (Nat.log p x : ℝ) ≤ Real.logb p (p * (8 * a + r)) := by
      rw [Real.le_logb_iff_rpow_le hp hpy, Real.rpow_natCast]
      linarith
    rw [Real.logb_mul (by positivity) (by linarith), Real.logb_self_eq_one hp] at h2
    linarith

theorem one_le_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) : 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp (by linarith)
  linarith

theorem natLog_floor_lgSeg (p : ℕ) [Fact p.Prime] (a : ℝ) (r : ℕ) (ha : 0 ≤ a) (hr : 1 ≤ r) :
    (Nat.log p ⌊8 * a + r⌋₊ : ℝ) + 1 ≤ lgSeg p a r := by
  unfold lgSeg
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ 8 * a + r := by linarith
  have hfl : 1 ≤ ⌊8 * a + (r : ℝ)⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hy)
  have h3 : ((p ^ Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ (⌊8 * a + (r : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p (by omega)
  have h4 := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * a + r)
  push_cast at h3
  have h2 : (Nat.log p ⌊8 * a + (r : ℝ)⌋₊ : ℝ) ≤ Real.logb p (8 * a + r) := by
    rw [Real.le_logb_iff_rpow_le hp (by linarith), Real.rpow_natCast]
    linarith
  linarith

theorem choose_two_le (r : ℕ) : ((r.choose 2 : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
  have h : 2 * r.choose 2 ≤ r ^ 2 := by
    rw [Nat.choose_two_right]
    have h1 := Nat.div_mul_le_self (r * (r - 1)) 2
    have h2 : r * (r - 1) ≤ r ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_left r (Nat.sub_le r 1)
    calc 2 * (r * (r - 1) / 2) = r * (r - 1) / 2 * 2 := mul_comm _ _
      _ ≤ r * (r - 1) := h1
      _ ≤ r ^ 2 := h2
  have h' : (2 : ℝ) * (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast h
  linarith

theorem gram_hypothesis_of_log_bound (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (lgv κ4 : ℝ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1)
    (hv : LLw.vec (Fin.last K) = true) (h1 : (Nat.log p (LLw.total + r - 1) : ℝ) ≤ lgv)
    (h2 : (Nat.log p (4 * LLw.total + r - 1) : ℝ) ≤ lgv)
    (hκ : ((K : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgv) ≤ κ4) : GramDeterminantGradedHypothesis p LLw J M ρ κ4 := by
  have hc := choose_two_le r
  have hl1 : (0 : ℝ) ≤ (Nat.log p (LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hl2 : (0 : ℝ) ≤ (Nat.log p (4 * LLw.total + r - 1) : ℝ) := Nat.cast_nonneg _
  have hlg : 0 ≤ lgv := hl1.trans h1
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgv := by positivity
  have g1 : ((kapC p r LLw.total : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    unfold kapC
    rw [Nat.cast_mul]
    exact mul_le_mul hc h1 hl1 (by positivity)
  have g2 : ((r.choose 2 * Nat.log p (4 * LLw.total + r - 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 / 2 * lgv := by
    rw [Nat.cast_mul]
    exact mul_le_mul hc h2 hl2 (by positivity)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ4 hr hρ hv (hypPE_setLast LLw ρ)
      (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_
    rw [Nat.mul_zero, Nat.add_zero, Nat.cast_mul]
    push_cast at hκ ⊢
    nlinarith
  · refine graded_bound_pos_of_proj highest_vector_projection_holds p K r LLw J M ρ (kapC p r LLw.total)
      (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ4 hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)
    · intro e _
      have ht' := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
      exact resSatL_mono _ J _ ρ
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))
        (restricted_saturation_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)
    · have h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgv) :=
        mul_le_mul_of_nonneg_left g1 (by positivity)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]
      push_cast at g2 h3 ⊢
      nlinarith

theorem deg_le_total' {N : ℕ} (LL : Letters N) (x : Fin N) : LL.deg x ≤ LL.total := by
  unfold Letters.total
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)

theorem theoremMV7Of : TheoremMV7Of := by
  unfold TheoremMV7Of
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp2 hr hρ hadm hch hcond ha hE hY hS hsize hH
  haveI : NeZero (2 * s + 1) := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlg1 : 1 ≤ lgSeg p a r := one_le_lgSeg p a r (by linarith) hr1
  have hfl := natLog_floor_lgSeg p a r (by linarith) hr1
  have hpos : 0 ≤ (r : ℝ) ^ 2 * lgSeg p a r := mul_nonneg (sq_nonneg _) (by linarith)
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hspos : 0 ≤ (s : ℝ) * ((r : ℝ) ^ 2 * lgSeg p a r) := mul_nonneg hsR hpos
  have hflo : ∀ m : ℕ, (m : ℝ) ≤ 8 * a + r → m ≤ ⌊8 * a + (r : ℝ)⌋₊ := fun m hm => Nat.le_floor hm
  obtain ⟨htot, hsz⟩ := hsize
  unfold epsSeg
  refine theoremMXB p (2 * s + 1) r LL T ⌊8 * a + (r : ℝ)⌋₊ E (kapSeg p a r s)
    (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r)) (lgSeg p a r) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊
    Yl n₀ dd ρ hp2 hr hρ hadm hE hY hS ?_ ?_ ?_ hfl ?_ ?_ ?_ hH
  · intro x
    apply hflo
    have h1 := deg_le_total' (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) x
    have h2 : ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg x : ℝ) ≤
        ((LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).total : ℝ) := by exact_mod_cast h1
    linarith
  · intro i
    obtain ⟨h1, h2, h3⟩ := hsz i
    refine ⟨?_, hflo _ h2, ?_⟩
    · apply hflo
      push_cast at h3 ⊢
      linarith
    · intro h
      apply hflo
      have hdA : degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i) =
          (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)).deg ⟨T.pos i, h⟩ := by
        unfold degreeAtPosition
        rw [dif_pos h]
      rw [hdA] at h1
      push_cast at h1 ⊢
      have h4 := (Nat.cast_nonneg (degreeAtPosition (LL.setTies T fun i => n₀ i + dd i * (Yl i - 1)) (T.pos i + 1)) : (0 : ℝ) ≤ _)
      linarith
  · exact hflo r (by linarith)
  · unfold kapSeg
    push_cast
    linarith
  · unfold kapSeg
    push_cast
    have h1 : ((⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 * lgSeg p a r := Nat.floor_le hpos
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * (s : ℝ) + 1 + 2)
    linarith
  · unfold kapSeg
    have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hr4 (by linarith : (0 : ℝ) ≤ lgSeg p a r)
    nlinarith

theorem setTies_total_le {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) :
    (LL.setTies T n).total ≤ (LL.setTies T n').total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  unfold Letters.setTies
  dsimp only
  split_ifs with hh
  · exact h _
  · exact le_rfl

theorem theoremMV7 : TheoremMV7 := by
  intro p _ s r _ LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz
  refine theoremMV7Of p s r LL T a E Yl n₀ dd ρ hp hr hρ hadm hch hco ha hE hY hS hsz ?_
  obtain ⟨htot, hsz⟩ := hsz
  have ha0 : 0 ≤ a := by linarith
  have hlg1 := one_le_lgSeg p a r ha0 (by omega)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hy : (0 : ℝ) ≤ 8 * a + r := by linarith
  have hQ : 0 ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := by positivity
  intro n hn
  have hle := grid_le T Yl n₀ dd n hn
  have hk : kapC p r (LL.setTies T n).total ≤ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ := by
    apply Nat.le_floor
    have ht : ((LL.setTies T n).total : ℝ) ≤ 8 * a + r :=
      le_trans (by exact_mod_cast setTies_total_le LL T n _ hle) htot
    have hx : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ p * (8 * a + r) := by
      have h1 : (((LL.setTies T n).total + r - 1 : ℕ) : ℝ) ≤ ((LL.setTies T n).total : ℝ) + r := by
        have : (LL.setTies T n).total + r - 1 ≤ (LL.setTies T n).total + r := Nat.sub_le _ _
        exact_mod_cast this
      nlinarith
    have hl := natLog_le_lgSeg p a r _ ha0 (by omega) hx
    unfold kapC
    rw [Nat.cast_mul]
    calc ((r.choose 2 : ℕ) : ℝ) * (Nat.log p ((LL.setTies T n).total + r - 1) : ℝ)
        ≤ (r : ℝ) ^ 2 / 2 * lgSeg p a r := mul_le_mul (choose_two_le r) hl (Nat.cast_nonneg _) (by positivity)
      _ ≤ (r : ℝ) ^ 2 * lgSeg p a r := by nlinarith
  refine ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p _ r _ ρ _ hk, Formalism.InvariantFactorPaths.PW.Top.dischargeW p _ r _ _ hk, fun i => ?_⟩
  obtain ⟨hlt, _, _⟩ := hadm.2.1 i
  obtain ⟨-, -, h2S⟩ := hsz i
  have hSle : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤
      T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i := by
    rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n _ hle i
  have hSr : 2 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + 1 ≤ 8 * a + r := by
    have : (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) ≤
        (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) := by exact_mod_cast hSle
    push_cast at h2S
    linarith
  have hS0 : (0 : ℝ) ≤ (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) := Nat.cast_nonneg _
  refine gram_hypothesis_of_log_bound p (T.pos i) r _ T.J (T.thrUpTo i) ρ (lgSeg p a r) _ hr hρ (takeD_vec_last LL T hadm n i) ?_ ?_ ?_
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤ ((LL.setTies T n).takeD (T.pos i + 1)).total + r :=
        Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · apply natLog_le_lgSeg p a r _ ha0 (by omega)
    have h1 : ((4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 : ℕ) : ℝ) ≤
        4 * (((LL.setTies T n).takeD (T.pos i + 1)).total : ℝ) + r := by
      have : 4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r - 1 ≤
          4 * ((LL.setTies T n).takeD (T.pos i + 1)).total + r := Nat.sub_le _ _
      exact_mod_cast this
    nlinarith
  · have hK : ((T.pos i : ℕ) : ℝ) + 7 ≤ 2 * ((s : ℝ) + 4) := by
      have : T.pos i + 7 ≤ 2 * (s + 4) := by omega
      exact_mod_cast this
    calc (((T.pos i : ℕ) : ℝ) + 7) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r)
        ≤ (2 * ((s : ℝ) + 4)) * ((r : ℝ) ^ 2 / 2 * lgSeg p a r) := mul_le_mul_of_nonneg_right hK hQ
      _ = ((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r) := by ring

end Formalism.InvariantFactorPaths.MC
end
