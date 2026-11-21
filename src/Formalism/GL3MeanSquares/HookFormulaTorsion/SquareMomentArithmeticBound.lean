import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem first_zeta_arithmetic_bound : ZetaValueArithmetic := by
  intro C₀ hC
  refine ⟨8 * C₀ + 11, ?_⟩
  intro ι _ N N' m n logHook logOm v L logT logg logK logh logh' lev logBlock logThn logS2 logTh
    hf hN hNN hm hv hL hT hg hlf hlN hlv hmax hK hh hh' hlev hBlock hThn hS2
  have hf1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hf
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNN' : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsum : ∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))
      ≤ (Fintype.card ι : ℝ) * ((N : ℝ) * N') * (2 + C₀ * L) := by
    calc _ ≤ ∑ _τ : ι, ((N : ℝ) * N') * (2 + C₀ * L) := by
          apply sum_le_sum
          intro τ _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmx : 0 < max 1 ((n τ : ℝ) / ((N : ℝ) * N')) := lt_of_lt_of_le one_pos (le_max_left _ _)
          rw [Real.log_mul (by positivity) hmx.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
            Real.log_exp]
          have := Real.log_two_lt_d9
          linarith [hmax τ]
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  generalize (∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))) = J
    at hsum hThn
  generalize (∑ τ, (logHook τ - n τ * logOm τ)) = Sg at hBlock ⊢
  generalize (Fintype.card ι : ℝ) = f at *
  generalize (N : ℝ) = Nr at *
  generalize (N' : ℝ) = Nr' at *
  generalize (m : ℝ) = mr at *
  have hN'1 : 1 ≤ Nr' := hN1.trans hNN'
  have hf0 : 0 < f := by linarith
  have hN0 : 0 < Nr := by linarith
  have hN'0 : 0 < Nr' := by linarith
  have hv0 : 0 < v := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlN0 : Real.log Nr ≤ L := (Real.log_le_log hN0 hNN').trans hlN
  have hl2 := Real.log_two_lt_d9
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl16 : Real.log 16 ≤ 3 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
  have hx1 : 1 ≤ f * Nr * Nr' * v := by
    have h1 : 1 ≤ f * Nr := one_le_mul_of_one_le_of_one_le hf1 hN1
    have h2 : 1 ≤ f * Nr * Nr' := one_le_mul_of_one_le_of_one_le h1 hN'1
    exact one_le_mul_of_one_le_of_one_le h2 hv
  have hbig : Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ 3 + 4 * L := by
    calc Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ Real.log (16 * (f * Nr * Nr' * v)) := by
          apply Real.log_le_log (by positivity); linarith
      _ = Real.log 16 + (Real.log f + Real.log Nr + Real.log Nr' + Real.log v) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hv0.ne',
            Real.log_mul (by positivity) hN'0.ne', Real.log_mul hf0.ne' hN0.ne']
      _ ≤ 3 + 4 * L := by linarith
  have hfN : Real.log (f * Nr') ≤ 2 * L := by
    rw [Real.log_mul hf0.ne' hN'0.ne']; linarith
  have hE0 : 0 ≤ L + logT + logg := by linarith
  have hm2 : 1 ≤ mr ^ 2 := one_le_pow₀ hm1
  have hP0 : 0 ≤ f * mr ^ 2 * Nr' ^ 2 := by positivity
  have a1 : f * Nr' ^ 2 ≤ f * mr ^ 2 * Nr' ^ 2 := by
    have : f * Nr' ^ 2 * 1 ≤ f * Nr' ^ 2 * mr ^ 2 := by gcongr
    linarith
  have a2 : f * Nr * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr * Nr' ≤ f * Nr' * Nr' := by gcongr
    linarith [this, sq Nr']
  have a3 : f * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr' * 1 ≤ f * Nr' * Nr' := by gcongr
    nlinarith [this]
  have a4 : f * (mr ^ 2 * Nr + Nr * Nr') ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) := by
    have h1 : f * (mr ^ 2 * Nr) ≤ f * (mr ^ 2 * Nr' ^ 2) := by
      have : Nr ≤ Nr' ^ 2 := by nlinarith
      gcongr
    have h2 : f * (Nr * Nr') ≤ f * mr ^ 2 * Nr' ^ 2 := by linarith
    linarith
  have t1 : f * Nr' ^ 2 * (L + logT + logg) ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul_of_nonneg_right a1 hE0
  have t2 : f * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hL0 hP0
  have t3 : f * Nr' * logT ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hT hP0
  have t4 : f * (mr ^ 2 * Nr + Nr * Nr') * logg
      ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) * (L + logT + logg) :=
    mul_le_mul a4 (by linarith) hg (by positivity)
  have t5 : f * Nr * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) hL0 hP0
  have t6 : f * Nr * Nr' * 1 ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) zero_le_one hP0
  have c1 := mul_le_mul_of_nonneg_left t1 hC
  have c2 := mul_le_mul_of_nonneg_left t2 hC
  have c3 := mul_le_mul_of_nonneg_left t3 hC
  have c4 := mul_le_mul_of_nonneg_left t4 hC
  have c5 := mul_le_mul_of_nonneg_left t5 hC
  have e1 : C₀ * f * Nr' * Real.log (f * Nr') ≤ C₀ * f * Nr' * (2 * L) := by gcongr
  have e2 : (f * Nr * Nr') * Real.log 4 ≤ (f * Nr * Nr') * 2 := by gcongr
  have e3 : (f * Nr * Nr') * Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ (f * Nr * Nr') * (3 + 4 * L) := by
    gcongr
  generalize Real.log (f * Nr') = z1 at *
  generalize Real.log 4 = z2 at *
  generalize Real.log (2 + 8 * (f * Nr * Nr') * v) = z3 at *
  linarith

private lemma log_weyl_dimension_bound (n : ℕ) (lam : Fin (n + 1) → ℤ) (h : Antitone lam) :
    Real.log (weylDim lam) ≤ ((n : ℝ) + 1) ^ 2 * Real.log (Wnum lam : ℝ) := by
  have hW1 : (1 : ℝ) ≤ (Wnum lam : ℝ) := by
    have h0 : lam (Fin.last n) ≤ lam 0 := h (Fin.zero_le _)
    have : (1 : ℤ) ≤ Wnum lam := by unfold Wnum; omega
    exact_mod_cast this
  have hfac : ∀ i j : Fin (n + 1), i < j →
      1 ≤ (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ∧
      (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ (Wnum lam : ℝ) := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hd : (1 : ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      linarith
    have h1 : lam j ≤ lam i := h hij.le
    have h2 : lam i ≤ lam 0 := h (Fin.zero_le _)
    have h3 : lam (Fin.last n) ≤ lam j := h (Fin.le_last _)
    have hj : (j : ℕ) ≤ n := j.is_le
    have hnum : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ))
        = ((lam i - lam j : ℤ) : ℝ) + (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by push_cast; ring
    have h1' : (0 : ℝ) ≤ ((lam i - lam j : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h1
    constructor
    · rw [le_div_iff₀ (by linarith), hnum]; linarith
    · rw [div_le_iff₀ (by linarith)]
      have h4 : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ)) ≤ (Wnum lam : ℝ) := by
        have : lam i - lam j + (j : ℤ) - (i : ℤ) ≤ Wnum lam := by unfold Wnum; omega
        exact_mod_cast this
      nlinarith
  have hpos : 0 < weylDim lam := by
    unfold weylDim
    apply prod_pos; intro i _; apply prod_pos; intro j hj
    have := (hfac i j (by simpa using hj)).1
    linarith
  have hle : weylDim lam ≤ (Wnum lam : ℝ) ^ ((n + 1) * (n + 1)) := by
    unfold weylDim
    calc _ ≤ ∏ _i : Fin (n + 1), (Wnum lam : ℝ) ^ (n + 1) := by
          apply prod_le_prod
          · intro i _; apply prod_nonneg; intro j hj
            have := (hfac i j (by simpa using hj)).1
            linarith
          · intro i _
            calc _ ≤ ∏ _j ∈ univ.filter (fun j : Fin (n + 1) => i < j), (Wnum lam : ℝ) := by
                  apply prod_le_prod
                  · intro j hj
                    have := (hfac i j (by simpa using hj)).1
                    linarith
                  · intro j hj
                    exact (hfac i j (by simpa using hj)).2
              _ = (Wnum lam : ℝ) ^ (univ.filter (fun j : Fin (n + 1) => i < j)).card := by
                  rw [prod_const]
              _ ≤ (Wnum lam : ℝ) ^ (n + 1) := by
                  apply pow_le_pow_right₀ hW1
                  calc _ ≤ (univ : Finset (Fin (n + 1))).card := card_filter_le _ _
                    _ = n + 1 := by simp
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  calc Real.log (weylDim lam) ≤ Real.log ((Wnum lam : ℝ) ^ ((n + 1) * (n + 1))) :=
        Real.log_le_log hpos hle
    _ = (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (Wnum lam : ℝ) := Real.log_pow _ _
    _ = _ := by push_cast; ring

private lemma arithmetic_bound_at_top {C₀ L logT b' eta S mt nn d M lw ld B bt A : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (hb : 0 ≤ b') (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hbt : bt ≤ 2 * b') (hB : B ≤ bt + eta + S) (hd : A - bt - C₀ * (S + eta + mt) ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ -A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (-A + 2 * b' + C₀ * (S + eta + mt)) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (-A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((-A + 2 * b' + C₀ * (S + eta + mt)) * logT
        + 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith

private lemma arithmetic_bound_off_top {C₀ L logT eta S mt nn d M lw ld B : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hB : B ≤ eta + S) (hd : -(S + eta) - C₀ * mt ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ 0
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (S + eta + C₀ * mt) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (0 + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((S + eta + C₀ * mt) * logT
        + 2 * nn * (C₀ * L) * (4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith

theorem third_zeta_application : ZetaBoundApplication := by
  intro C₀ hC
  refine ⟨12 * C₀ + 2, ?_⟩
  intro ι _ _ TT n lam sg A bt b' L logT eta S mt logP hL hT hb he hS hmt hI hW hbt hBt hBn hX
    hdt hdn hP
  have hL0 : 0 ≤ L := by linarith
  have hplace : ∀ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT ≤
      (if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨X, hXc, hXs⟩ := hX ρ
    have hB0 : 0 ≤ B0 (lam ρ) (sg ρ) := sum_nonneg (fun i _ => sub_nonneg.mpr ((hI ρ).2 i).1)
    have hlen : ∀ i, 0 ≤ len (lam ρ) i :=
      fun i => sub_nonneg.mpr (((hI ρ).2 i).1.trans ((hI ρ).2 i).2)
    have hM0 : 0 ≤ ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) :=
      sum_nonneg fun i _ => le_min (hlen i) hB0
    have hM : ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ))
        ≤ 3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i := by
      rw [← Finset.sum_add_sum_compl X]
      refine add_le_add ?_ (Finset.sum_le_sum fun i _ => min_le_left _ _)
      calc ∑ i ∈ X, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) ≤ ∑ _i ∈ X, B0 (lam ρ) (sg ρ) :=
            Finset.sum_le_sum fun i _ => min_le_right _ _
        _ = X.card * B0 (lam ρ) (sg ρ) := by simp
        _ ≤ 3 * B0 (lam ρ) (sg ρ) := by
            apply mul_le_mul_of_nonneg_right _ hB0
            exact_mod_cast hXc
    have hcast : (∑ i, ((min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ))
        = ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := (Int.cast_sum _ _).symm
    have hM0r : (0 : ℝ) ≤ ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := by
      exact_mod_cast hM0
    have hMr : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
        ≤ 3 * (B0 (lam ρ) (sg ρ) : ℝ) + (eta + S) := by
      have : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
          ≤ ((3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) := by exact_mod_cast hM
      rw [Int.cast_add, Int.cast_mul] at this
      have h3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
      rw [h3] at this
      linarith
    have hdim := log_weyl_dimension_bound n (lam ρ) (hI ρ).1
    unfold MeanSquareTwistBound
    rw [hcast]
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      exact arithmetic_bound_at_top hC hL0 hT hb he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim (hbt ρ hρ)
        (hBt ρ hρ) (hdt ρ hρ)
    · rw [if_neg hρ]
      exact arithmetic_bound_off_top hC hL0 hT he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim
        (hBn ρ hρ) (hdn ρ hρ)
  calc logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT := hP
    _ ≤ ∑ ρ, ((if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L)) := sum_le_sum fun ρ _ => hplace ρ
    _ = _ := by
      rw [sum_add_distrib, sum_const, sum_ite_mem, univ_inter, sum_add_distrib, sum_const,
        ← sum_mul, sum_neg_distrib, card_univ, nsmul_eq_mul, nsmul_eq_mul]
      ring

private lemma stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have h1 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

private lemma stirling_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have key : Real.log ((n : ℝ) / (n + 1)) ≤ (n : ℝ) / (n + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at key
    have e : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp; ring
    rw [e] at key
    have k2 : ((n : ℝ) + 1) * (Real.log n - Real.log ((n : ℝ) + 1)) ≤ -1 := by
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      have e2 : ((n : ℝ) + 1) * -(1 / ((n : ℝ) + 1)) = -1 := by field_simp
      linarith
    nlinarith

private lemma log_factorial_row_bound (n : ℕ) (x : ℝ) (hx : 1 ≤ x) (h : (n : ℝ) ≤ x) :
    Real.log (n.factorial : ℝ) ≤ x * Real.log x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using mul_nonneg (by linarith) (Real.log_nonneg hx)
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast hn) h
  have h3 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log (by positivity) h1
    _ = n * Real.log n := Real.log_pow _ _
    _ ≤ x * Real.log x := mul_le_mul h h2 h3 (by linarith)

private lemma sum_log_factorial_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (hx : 1 ≤ x) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, Real.log ((g i).factorial : ℝ) ∧
      ∑ i, Real.log ((g i).factorial : ℝ) ≤ k * (x * Real.log x) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast Nat.factorial_pos _)
  · calc ∑ i, Real.log ((g i).factorial : ℝ) ≤ ∑ _i : Fin k, x * Real.log x :=
          Finset.sum_le_sum fun i _ => log_factorial_row_bound _ _ hx (h i)
      _ = k * (x * Real.log x) := by simp

private lemma log_factorial_shift_bound (n k : ℕ) (x : ℝ) (h : ((n + k : ℕ) : ℝ) ≤ x) :
    Real.log ((n + k).factorial : ℝ) ≤ Real.log (n.factorial : ℝ) + k * Real.log x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h' : ((n + k : ℕ) : ℝ) ≤ x := by push_cast at h ⊢; linarith
    have h1 := ih h'
    rw [← add_assoc, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log ((n : ℝ) + k + 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by push_cast at h; linarith)
    nlinarith

private lemma log_hook_product_bounds (R : ℕ) (nu : Fin (R + 1) → ℕ) (h : Antitone nu) :
    Real.log (hookF nu) ≤ ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ) ∧
    ∑ i : Fin (R + 1), Real.log ((nu i + R - i : ℕ).factorial : ℝ)
        - ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log (hookF nu) := by
  obtain ⟨h1, h2, -⟩ := Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds R nu h
  refine ⟨?_, h2⟩
  have hpos : 0 < hookF nu := by
    unfold Formalism.LogVandermondeBounds.flipTwoThree.hookF
    apply div_pos (by positivity)
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    linarith [(Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds R nu h i j (mem_filter.mp hj).2).1]
  calc Real.log (hookF nu) ≤ Real.log (∏ i : Fin (R + 1), ((nu i + R - i : ℕ).factorial : ℝ)) :=
        Real.log_le_log hpos h1
    _ = _ := Real.log_prod (fun i _ => by positivity)

private lemma sum_rows_bounds (k : ℕ) (g : Fin k → ℕ) (x : ℝ) (h : ∀ i, (g i : ℝ) ≤ x) :
    0 ≤ ∑ i, (g i : ℝ) ∧ ∑ i, (g i : ℝ) ≤ k * x := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  · calc ∑ i, (g i : ℝ) ≤ ∑ _i : Fin k, x := Finset.sum_le_sum fun i _ => h i
      _ = k * x := by simp

set_option maxHeartbeats 800000 in
theorem second_zeta_top_bound : LargestPlaceHookBound := by
  intro C₀ hC
  refine ⟨21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu A w a b' L logOm hnu h0 hw hrow haA hA2 hb1 hba hL hla hRb hOm
  have ha1 : (1 : ℝ) ≤ a := hb1.trans hba
  have hA1r : (1 : ℝ) ≤ A := ha1.trans haA
  have hA1 : 1 ≤ A := by exact_mod_cast hA1r
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  set l5 := Real.log (5 * a) with hl5def
  have hl5 : l5 ≤ 5 * L := by
    rw [hl5def, Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 5 ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hl50 : 0 ≤ l5 := Real.log_nonneg (by linarith)
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : Real.log b' ≤ Real.log a := Real.log_le_log (by linarith) hba
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  rw [Fin.sum_univ_succ] at hup hlo
  have e0 : nu 0 + R - ((0 : Fin (R + 1)) : ℕ) = A + (w + R) := by
    have : ((0 : Fin (R + 1)) : ℕ) = 0 := rfl
    omega
  rw [e0] at hup hlo
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds R (fun i : Fin R => nu i.succ + R - (i.succ : Fin (R + 1))) X hX1 (by
    intro i
    have h1 : ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ) : ℝ) ≤ ((nu i.succ + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i.succ (Fin.succ_ne_zero i)
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin R, Real.log ((nu i.succ + R - (i.succ : Fin (R + 1)) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds R (fun i : Fin R => nu i.succ) ((2 + C₀) * b')
    (fun i => hrow i.succ (Fin.succ_ne_zero i))
  have hsum : ∑ i, (nu i : ℝ) = (A : ℝ) + w + ∑ i : Fin R, (nu i.succ : ℝ) := by
    rw [Fin.sum_univ_succ, h0]; push_cast; ring
  set S := ∑ i : Fin R, (nu i.succ : ℝ) with hS
  have hsh := log_factorial_shift_bound A (w + R) (5 * a) (by push_cast; linarith)
  have hmono : Real.log (A.factorial : ℝ) ≤ Real.log ((A + (w + R)).factorial : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_add_right _ _))
  have hlo' := stirling_lower_bound A hA1
  have hhi' := stirling_upper_bound A hA1
  have hlA : Real.log (A : ℝ) ≤ l5 := Real.log_le_log (by linarith) (by linarith)
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ l5 := by
    apply Real.log_le_log (by positivity)
    rw [h0]; push_cast; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hbL : b' * L ≤ Q := by
    have := mul_nonneg hR0 (mul_nonneg (by linarith : (0:ℝ) ≤ b') (by linarith : (0:ℝ) ≤ L))
    rw [hQ]; linarith
  have hLQ : L ≤ Q := (le_mul_of_one_le_left (by linarith) hb1).trans hbL
  have t1 : ((w + R : ℕ) : ℝ) * l5 ≤ 15 * Q := by
    have : ((w + R : ℕ) : ℝ) ≤ 3 * b' := by push_cast; linarith
    calc ((w + R : ℕ) : ℝ) * l5 ≤ (3 * b') * (5 * L) := mul_le_mul this hl5 hl50 (by linarith)
      _ = 15 * (b' * L) := by ring
      _ ≤ 15 * Q := by linarith
  have t2 : (R : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    have h2 : (R : ℝ) * (X * Real.log X) ≤ ((R : ℝ) + 1) * (X * ((3 + C₀) * L)) :=
      mul_le_mul (by linarith) h1 (mul_nonneg (by linarith) hlX0) (by linarith)
    calc _ ≤ _ := h2
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ 5 * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * l5 := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * (5 * L) := mul_le_mul h1 hl5 hl50 (mul_nonneg (by linarith) (by linarith))
      _ = 5 * Q := by rw [hQ]; ring
  have t4 : |((w : ℝ) + S) * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (w : ℝ) + S)]
    have h1 : (w : ℝ) + S ≤ ((R : ℝ) + 1) * ((2 + C₀) * b') := by
      have := mul_nonneg hC (by linarith : (0:ℝ) ≤ b')
      linarith
    calc ((w : ℝ) + S) * |logOm| ≤ (((R : ℝ) + 1) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul h1 hOm (abs_nonneg _)
            (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; ring
  have hgoal : placeTerm nu logOm - topTerm A logOm
      = (Real.log (hookF nu) - ((A : ℝ) * Real.log A - A)) - ((w : ℝ) + S) * logOm := by
    unfold placeTerm topTerm; rw [hsum]; ring
  have hfin : (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = (21 + (3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  rw [hgoal, hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have hQ0 : 0 ≤ Q := by linarith
  have hsq : 0 ≤ (3 + C₀) ^ 2 * Q := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem second_zeta_thin_bound : ThinPlaceHookBound := by
  intro C₀ hC
  refine ⟨(3 + C₀) ^ 2 + C₀ * (2 + C₀), ?_⟩
  intro R nu b' L logOm hnu hrow hb1 hL hlb hRb hOm
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set X := (3 + C₀) * b' with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hlX : Real.log X ≤ (3 + C₀) * L := by
    rw [hX, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log (3 + C₀) ≤ (3 + C₀) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  obtain ⟨hup, hlo⟩ := log_hook_product_bounds R nu hnu
  obtain ⟨hT0, hTU⟩ := sum_log_factorial_rows_bounds (R + 1) (fun i : Fin (R + 1) => nu i + R - (i : ℕ)) X hX1 (by
    intro i
    have h1 : ((nu i + R - (i : ℕ) : ℕ) : ℝ) ≤ ((nu i + R : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le _ _)
    have h2 := hrow i
    push_cast at h1
    rw [hX]
    linarith)
  set Tl := ∑ i : Fin (R + 1), Real.log ((nu i + R - (i : ℕ) : ℕ).factorial : ℝ) with hTl
  obtain ⟨hS0, hSU⟩ := sum_rows_bounds (R + 1) nu ((2 + C₀) * b') hrow
  set S := ∑ i, (nu i : ℝ) with hS
  have hl0 : Real.log ((nu 0 : ℝ) + R + 1) ≤ Real.log X := by
    apply Real.log_le_log (by positivity)
    have := hrow 0
    rw [hX]; linarith
  set Q := ((R : ℝ) + 1) * b' * L with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have t2 : ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ (3 + C₀) ^ 2 * Q := by
    have h1 : X * Real.log X ≤ X * ((3 + C₀) * L) := mul_le_mul_of_nonneg_left hlX (by linarith)
    calc ((R + 1 : ℕ) : ℝ) * (X * Real.log X) ≤ ((R + 1 : ℕ) : ℝ) * (X * ((3 + C₀) * L)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (3 + C₀) ^ 2 * Q := by rw [hX, hQ]; push_cast; ring
  have t3 : ((R : ℝ) + 1) ^ 2 * Real.log ((nu 0 : ℝ) + R + 1) ≤ (3 + C₀) * Q := by
    have h1 : ((R : ℝ) + 1) ^ 2 ≤ ((R : ℝ) + 1) * b' := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hRb (by linarith)
    calc _ ≤ ((R : ℝ) + 1) ^ 2 * Real.log X := mul_le_mul_of_nonneg_left hl0 (by positivity)
      _ ≤ (((R : ℝ) + 1) * b') * ((3 + C₀) * L) := mul_le_mul h1 hlX hlX0 (mul_nonneg (by linarith) (by linarith))
      _ = (3 + C₀) * Q := by rw [hQ]; ring
  have t4 : |S * logOm| ≤ C₀ * (2 + C₀) * Q := by
    rw [abs_mul, abs_of_nonneg hS0]
    calc S * |logOm| ≤ (((R + 1 : ℕ) : ℝ) * ((2 + C₀) * b')) * (C₀ * L) :=
          mul_le_mul hSU hOm (abs_nonneg _) (by positivity)
      _ = C₀ * (2 + C₀) * Q := by rw [hQ]; push_cast; ring
  have hfin : ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * ((R : ℝ) + 1) * b' * L
      = ((3 + C₀) ^ 2 + C₀ * (2 + C₀)) * Q := by rw [hQ]; ring
  unfold placeTerm
  rw [hfin]
  obtain ⟨t4a, t4b⟩ := abs_le.mp t4
  have h33 : (3 + C₀) * Q ≤ (3 + C₀) ^ 2 * Q := by
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 3 + C₀) (by linarith : (0:ℝ) ≤ 2 + C₀)) hQ0
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma mean_mono' {σ : Type} [Fintype σ] (F G : σ → ℝ) (h : ∀ s, F s ≤ G s) :
    mean F ≤ mean G := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => h s) (Nat.cast_nonneg _)

private lemma mean_add_eq {σ : Type} [Fintype σ] (F G : σ → ℝ) :
    mean (fun s => F s + G s) = mean F + mean G := by
  unfold mean; rw [Finset.sum_add_distrib, add_div]

private lemma mean_finset_sum_comm {σ J : Type} [Fintype σ] [Fintype J] (F : J → σ → ℝ) :
    mean (fun s => ∑ j, F j s) = ∑ j, mean (F j) := by
  unfold mean; rw [Finset.sum_comm, Finset.sum_div]

private lemma mean_const_eq {σ : Type} [Fintype σ] [Nonempty σ] (c : ℝ) :
    mean (fun _ : σ => c) = c := by
  unfold mean
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma mean_place_term_comm {σ : Type} [Fintype σ] [Nonempty σ] {N : ℕ} (nu : Fin N → ℕ)
    (x : σ → ℝ) : mean (fun s => placeTerm nu (x s)) = placeTerm nu (mean x) := by
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold placeTerm mean
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem second_zeta_mean_of_top_thin (ht : LargestPlaceHookBound) (hth : ThinPlaceHookBound) : MeanLogNormBound := by
  intro C₀ hC
  obtain ⟨Ct, hCt⟩ := ht C₀ hC
  obtain ⟨Cn, hCn⟩ := hth C₀ hC
  refine ⟨|Ct| + |Cn| + 2 * C₀, ?_⟩
  intro ι σ _ _ _ _ TT T2 R N m nu A w a b' L logT logg logOm logOms logTh logK hdis hRN hL hla hb1
    hba hNL hT0 hg0 hsqm hanti htop hthin hper hOm hTh hK
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg _
  have hRN' : (R:ℝ) + 1 ≤ N := by exact_mod_cast hRN
  have hRb : (R:ℝ) + 1 ≤ b' := by nlinarith
  have hlb : Real.log b' ≤ L := le_trans (Real.log_le_log (by linarith) hba) hla
  set f : ℝ := (Fintype.card ι : ℝ) with hf
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  set G : ℝ := (N:ℝ) * b' * L with hG
  have hG0 : 0 ≤ G := by positivity
  have hRG : ((R:ℝ) + 1) * b' * L ≤ G := by rw [hG]; gcongr
  have hRG0 : 0 ≤ ((R:ℝ) + 1) * b' * L := by positivity
  have hplace : ∀ τ, placeTerm (nu τ) logOm ≤ (if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G := by
    intro τ
    have hg1 : 0 ≤ |Ct| * G := by positivity
    have hg2 : 0 ≤ |Cn| * G := by positivity
    by_cases h1 : τ ∈ TT
    · have h2 : τ ∉ T2 := Finset.disjoint_left.1 hdis h1
      rw [if_pos h1, if_neg h2]
      obtain ⟨p1, p2, p3, p4, p5⟩ := htop τ h1
      have := hCt R (nu τ) (A τ) (w τ) a b' L logOm (hanti τ) p3 p4 p5 p1 p2 hb1 hba hL hla hRb hOm
      have h3 := (abs_le.1 this).2
      have h4 : Ct * ((R:ℝ) + 1) * b' * L ≤ |Ct| * G := by
        calc Ct * ((R:ℝ) + 1) * b' * L = Ct * (((R:ℝ) + 1) * b' * L) := by ring
          _ ≤ |Ct| * G := by gcongr; exact le_abs_self _
      linarith
    · by_cases h2 : τ ∈ T2
      · rw [if_neg h1, if_pos h2]; linarith
      · rw [if_neg h1, if_neg h2]
        have := hCn R (nu τ) b' L logOm (hanti τ) (hthin τ h1 h2) hb1 hL hlb hRb hOm
        have h3 := (abs_le.1 this).2
        have h4 : Cn * ((R:ℝ) + 1) * b' * L ≤ |Cn| * G := by
          calc Cn * ((R:ℝ) + 1) * b' * L = Cn * (((R:ℝ) + 1) * b' * L) := by ring
            _ ≤ |Cn| * G := by gcongr; exact le_abs_self _
        linarith
  have hsum : ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu τ) logOm + f * ((|Ct| + |Cn|) * G) := by
    calc ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ, ((if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G) :=
          Finset.sum_le_sum fun τ _ => hplace τ
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]
  have hmean : mean logK ≤ ∑ τ, placeTerm (nu τ) logOm + mean logTh
      + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) := by
    calc mean logK ≤ mean (fun s => (∑ τ, placeTerm (nu τ) (logOms τ s) + logTh s)
        + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := mean_mono' _ _ hK
      _ = _ := by
        rw [mean_add_eq, mean_add_eq, mean_finset_sum_comm, mean_const_eq]
        simp only [mean_place_term_comm, hper]
  have e1 : mean logTh ≤ C₀ * f * G := by
    refine le_trans hTh ?_
    have : (N:ℝ) ^ 2 * L ≤ G := by
      rw [hG]
      have h1 : (N:ℝ) ^ 2 * L ≤ N * b' := by nlinarith
      have h2 : (N:ℝ) * b' ≤ N * b' * L := by nlinarith [mul_nonneg hN0 hb0]
      linarith
    calc C₀ * f * (N:ℝ) ^ 2 * L = C₀ * f * ((N:ℝ) ^ 2 * L) := by ring
      _ ≤ _ := by gcongr
  have e2 : C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ C₀ * f * G := by
    calc C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)
        = C₀ * f * ((m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := by ring
      _ ≤ _ := by gcongr
  have hfin : (|Ct| + |Cn| + 2 * C₀) * f * N * b' * L
      = f * ((|Ct| + |Cn|) * G) + C₀ * f * G + C₀ * f * G := by rw [hG]; ring
  rw [hfin]
  linarith

theorem second_zeta_mean_bound : MeanLogNormBound := second_zeta_mean_of_top_thin second_zeta_top_bound second_zeta_thin_bound

end Formalism.HermitianLattices.TraceIntegrality
end

section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)









private lemma zii_plus_nonneg {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) (i : Fin (κ + 1)) :
    0 ≤ plus lam i := by
  simp only [plus]
  exact sub_nonneg.2 (h (Fin.le_last i))

private lemma zii_plus0_le {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    plus lam 0 ≤ wt (plus lam) := by
  unfold wt
  exact Finset.single_le_sum (f := plus lam) (fun i _ => zii_plus_nonneg lam h i) (Finset.mem_univ 0)

private lemma zii_log_le {a L v W : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hW0 : 0 < W) (hW : W ≤ 9 * a ^ 2) : Real.log W ≤ 10 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log W ≤ Real.log (9 * a ^ 2) := Real.log_le_log hW0 hW
  have h2 : Real.log (9 * a ^ 2) = Real.log 9 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 9)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith

theorem zeta_proposition_second : PropZ_ii := by
  intro C₀ hC
  refine ⟨11 + C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muM muV muDelta muNabla muMaxNabla
    hN hanti hTT hwt hwtp hwtp' hwt' hM hV hD hNab hMax
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hS0 := hN.S_nonneg
  have hκ0 : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  have hK1 : (1:ℝ) ≤ (κ:ℝ) + 1 := by linarith
  have hK0 : (0:ℝ) < (κ:ℝ) + 1 := by linarith
  have hKN : (κ:ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hNL : (N:ℝ) * L ≤ b' := by linarith [hN.lin]
  have hNNL : (N:ℝ) ≤ N * L := by nlinarith
  have hKb : (κ:ℝ) + 1 ≤ b' := by linarith
  have hKa : (κ:ℝ) + 1 ≤ a := le_trans hKb hba
  have hSb : S ≤ b' := by
    have := hN.small
    have := hN.eta_nonneg
    have : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith
  have ha1 : 1 ≤ a := le_trans hb1 hba
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlogK0 : 0 ≤ Real.log ((κ:ℝ) + 1) := Real.log_nonneg hK1
  have hKbS : 0 ≤ ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg hK0.le (by linarith)) hlogK0
  have hZ4 : ∀ ρ, MeanSquareWeightBound (lam ρ) ≤ (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
      + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    intro ρ
    have hp0 : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast zii_plus_nonneg (lam ρ) (hanti ρ) 0
    have hpW : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by
      exact_mod_cast zii_plus0_le (lam ρ) (hanti ρ)
    unfold MeanSquareWeightBound
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      obtain ⟨h1, h2, h3, h4⟩ := hTT ρ hρ
      have hw := hwtp ρ hρ
      have e1 : ((κ:ℝ) + 1) * (bt ρ + S) ≤ ((κ:ℝ) + 1) * (2 * (b' + S)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0.le
      have hWb : (wt (plus (lam ρ)) : ℝ) ≤ 2 * a + 2 * (((κ:ℝ) + 1) * (b' + S)) := by linarith
      have e2 : ((κ:ℝ) + 1) * (b' + S) ≤ a * (2 * a) :=
        mul_le_mul hKa (by linarith) (by linarith) (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right hWb hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
    · rw [if_neg hρ]
      have hw := hwtp' ρ hρ
      have e1 : ((κ:ℝ) + 1 + 3) * S ≤ 4 * (((κ:ℝ) + 1) * (b' + S)) := by nlinarith
      have e2 : ((κ:ℝ) + 1 + 3) * S ≤ (4 * a) * a := mul_le_mul (by linarith) (by linarith) hS0 (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right (hw.trans e1) hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
  have hsumZ4 : ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1))
      + (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
        + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
        = (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1)) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have e2 : ∑ _ρ : ι, (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)
        = (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
          + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ ∑ ρ, ((if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
          + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)) :=
          Finset.sum_le_sum fun ρ _ => hZ4 ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hwtbound : ∀ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT := by
    intro ρ
    have h3 : 0 ≤ C₀ * S * logT := mul_nonneg (mul_nonneg hC hS0) hT0
    have h4 : 0 ≤ S * logT := mul_nonneg hS0 hT0
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      have h := hwt ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ A ρ / ((κ:ℝ) + 1) + S := by
        rw [div_le_iff₀ hK0, add_mul, div_mul_cancel₀ _ hK0.ne']
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
    · rw [if_neg hρ]
      have h := hwt' ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ C₀ * S := by
        rw [div_le_iff₀ hK0]
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
  have hsumwt : ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT + (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0)
        = ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e2 : ∑ _ρ : ι, (1 + C₀) * S * logT = (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
        ≤ ∑ ρ, ((if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT) :=
          Finset.sum_le_sum fun ρ _ => hwtbound ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hmean : muM = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT) + ∑ ρ, muDelta ρ := by
    rw [hM]
    have hc : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    unfold mean
    simp only [hV]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hc.ne']
  have hDel : -(∑ ρ, MeanSquareWeightBound (lam ρ)) ≤ ∑ ρ, muDelta ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun ρ _ => by rw [hD ρ]; linarith [hNab ρ, hMax ρ]
  have hcard0 : (0:ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have n1 : 0 ≤ (TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hlogK0
  have m1 : 0 ≤ C₀ * ((TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1)) := mul_nonneg hC n1
  have n2 : 0 ≤ (Fintype.card ι : ℝ) * S * logT := mul_nonneg (mul_nonneg hcard0 hS0) hT0
  have n3 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)) :=
    mul_nonneg hcard0 hKbS
  have m3 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1))) :=
    mul_nonneg hC n3
  have n4 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L) :=
    mul_nonneg hcard0 (mul_nonneg (sq_nonneg _) (by linarith))
  have m4 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L)) := mul_nonneg hC n4
  linarith [hmean, hDel, hsumZ4, hsumwt, n1, m1, n2, n3, m3, n4, m4]

private lemma positive_part_head_le_weight {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    0 ≤ plus lam 0 ∧ plus lam 0 ≤ wt (plus lam) := ⟨zii_plus_nonneg lam h 0, zii_plus0_le lam h⟩

private lemma ziii_log {a L v x : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hx0 : 0 < x) (hx : x ≤ 7 * a ^ 2) : Real.log x ≤ 8 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log x ≤ Real.log (7 * a ^ 2) := Real.log_le_log hx0 hx
  have h2 : Real.log (7 * a ^ 2) = Real.log 7 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 7)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith

private lemma ziii_place {C₀ K b' S L lkv logT W lst lg U : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hlkv : 0 ≤ lkv) (hT : 0 ≤ logT)
    (hW : W ≤ U + 4 * K * (b' + S)) (hlg : lg ≤ 8 * L) (hlst : lst ≤ (2 + C₀) * (b' + S)) :
    W * (C₀ * lkv) + K ^ 2 * lg + lst * logT ≤
      U * (C₀ * lkv) + (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have h0 : 0 ≤ C₀ * lkv := mul_nonneg hC hlkv
  have h1 := mul_le_mul_of_nonneg_right hW h0
  have h2 := mul_le_mul_of_nonneg_left hlg (sq_nonneg K)
  have h3 := mul_le_mul_of_nonneg_right hlst hT
  linarith [h1, h2, h3]

private lemma ziii_top {C₀ K a b' S L v logT W p lst At bt : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hA2 : At ≤ 2 * a) (hbt2 : bt ≤ 2 * b') (hW : W ≤ At + K * (bt + S)) (hl : lst ≤ bt) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      2 * a * (C₀ * Real.log (K * v)) + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hbS : bt + S ≤ 3 * a := by linarith
  have hKbt : K * (bt + S) ≤ a * (3 * a) :=
    (mul_le_mul_of_nonneg_left hbS hK0).trans (mul_le_mul_of_nonneg_right hKa (by linarith))
  have hW' : W ≤ 2 * a + 4 * K * (b' + S) := by
    have : K * (bt + S) ≤ K * (4 * (b' + S)) := mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b' + S)]
  have := ziii_place (U := 2 * a) hC hK hlkv hT hW' hlg hlst
  linarith

private lemma ziii_other {C₀ K a b' S L v logT W p lst : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hW : W ≤ (K + 3) * S) (hl : lst ≤ C₀ * S) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      0 + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hW' : W ≤ 0 + 4 * K * (b' + S) := by
    have h1 : 1 * S ≤ K * S := mul_le_mul_of_nonneg_right hK hS
    have h2 : 0 ≤ K * b' := mul_nonneg hK0 (by linarith)
    nlinarith
  have hK3 : K + 3 ≤ 4 * a := by linarith
  have hSa : S ≤ a := by linarith
  have hKS : (K + 3) * S ≤ 4 * a * a := mul_le_mul hK3 hSa hS (by linarith)
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b')]
  have := ziii_place (U := 0) hC hK hlkv hT hW' hlg hlst
  linarith

private lemma final_part_arithmetic_bound {C₀ nT f a lkv K b' S logT L : ℝ} (hC : 0 ≤ C₀) (hnT : 0 ≤ nT) (hf : 0 ≤ f)
    (ha : 0 ≤ a) (hlkv : 0 ≤ lkv) (hK : 0 ≤ K) (hbS : 0 ≤ b' + S) (hT : 0 ≤ logT) (hL : 0 ≤ L) :
    nT * (2 * a * (C₀ * lkv)) + f * (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT
        + 8 * K ^ 2 * L) ≤
      (8 + 4 * C₀) * nT * a * lkv + (8 + 4 * C₀) * f * (b' + S) * (K * lkv + logT)
        + (8 + 4 * C₀) * f * K ^ 2 * L := by
  have p1 : 0 ≤ nT * a * lkv := mul_nonneg (mul_nonneg hnT ha) hlkv
  have q1 : 0 ≤ C₀ * (nT * a * lkv) := mul_nonneg hC p1
  have p2 : 0 ≤ f * (b' + S) * K * lkv := mul_nonneg (mul_nonneg (mul_nonneg hf hbS) hK) hlkv
  have p3 : 0 ≤ f * (b' + S) * logT := mul_nonneg (mul_nonneg hf hbS) hT
  have q3 : 0 ≤ C₀ * (f * (b' + S) * logT) := mul_nonneg hC p3
  have q4 : 0 ≤ C₀ * (f * K ^ 2 * L) := mul_nonneg hC (mul_nonneg (mul_nonneg hf (sq_nonneg K)) hL)
  linarith [p1, q1, p2, p3, q3, q4]

theorem zeta_proposition_third : PropZ_iii := by
  intro C₀ hC
  refine ⟨8 + 4 * C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muMaxM muMaxV hN hanti hTT hWT hlT
    hWo hlo hex hV
  obtain ⟨c, hc⟩ := hex
  have hL := hN.one_le_L
  have hv := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT := hN.logT_nonneg
  have hS := hN.S_nonneg
  have ha : 1 ≤ a := le_trans hb1 hba
  have hmt : (0:ℝ) ≤ (m : ℝ) * t := by positivity
  have hSb : S ≤ b' := by have := hN.small; have := hN.eta_nonneg; linarith
  have hKN : (κ : ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNb : (N : ℝ) ≤ b' := by
    have h1 := hN.lin
    have h2 : (N : ℝ) * 1 ≤ N * L := mul_le_mul_of_nonneg_left hL hN0
    linarith
  have hK1 : (1:ℝ) ≤ (κ : ℝ) + 1 := by
    have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
    linarith
  have hKa : (κ : ℝ) + 1 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (((κ : ℝ) + 1) * v) := Real.log_nonneg (by nlinarith)
  have key : ∀ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT) ≤
      (if ρ ∈ TT then 2 * a * (C₀ * Real.log (((κ : ℝ) + 1) * v)) else 0)
        + (4 * C₀ * ((κ : ℝ) + 1) * (b' + S) * Real.log (((κ : ℝ) + 1) * v)
          + (2 + C₀) * (b' + S) * logT + 8 * ((κ : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨hp0, hpW⟩ := positive_part_head_le_weight (lam ρ) (hanti ρ)
    have hp0' : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast hp0
    have hpW' : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by exact_mod_cast hpW
    rw [add_assoc ((plus (lam ρ) 0 : ℤ) : ℝ) (κ : ℝ) 1]
    by_cases hρ : ρ ∈ TT
    · obtain ⟨hA1, hA2, hbt1, hbt2⟩ := hTT ρ hρ
      rw [if_pos hρ]
      exact ziii_top hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' hA2 hbt2 (hWT ρ hρ)
        (hlT ρ hρ)
    · rw [if_neg hρ]
      exact ziii_other hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' (hWo ρ hρ) (hlo ρ hρ)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun ρ _ => key ρ)
  have hrhs : ∀ x y : ℝ, ∑ ρ : ι, ((if ρ ∈ TT then x else 0) + y)
      = (TT.card : ℝ) * x + (Fintype.card ι : ℝ) * y := by
    intro x y
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
  rw [hrhs] at hsum
  refine le_trans (le_trans hc (le_trans (hV c) hsum)) ?_
  exact final_part_arithmetic_bound hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hlkv (by linarith)
    (by linarith) hT (by linarith)

set_option maxHeartbeats 800000 in

theorem zeta_proposition_tail : Formalism.HermitianLattices.TraceIntegrality.PropZ_tail := by
  intro C₀ hC
  refine ⟨10 + 5 * C₀, ?_⟩
  intro f nT k m t N x b a b' L v logT logg eta S sA hN hb hax hnT1 hnTf hsA0 hsA
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hTle := hN.logT_le
  have hS0 := hN.S_nonneg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hN.one_le_k
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hN.one_le_m
  have hkN : (k:ℝ) ≤ N := by
    have : k ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1:ℝ) ≤ N := le_trans hk1 hkN
  have hNL : (N:ℝ) * L ≤ b' := by linarith only [hN.lin, hT0]
  have hNNL : (N:ℝ) ≤ N * L := le_mul_of_one_le_right hN0 hL1
  have hkb : (k:ℝ) ≤ b' := by linarith only [hkN, hNNL, hNL]
  have hka : (k:ℝ) ≤ a := le_trans hkb hba
  have hSb : S ≤ b' := by
    have h1 := hN.small
    have h2 := hN.eta_nonneg
    have h3 : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith only [h1, h2, h3]
  have hnT : (1:ℝ) ≤ nT := by exact_mod_cast hnT1
  have hnT0' : (0:ℝ) ≤ nT := by linarith only [hnT]
  have hm0' : (0:ℝ) ≤ m := by linarith only [hm1]
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hL0 : (0:ℝ) ≤ L := by linarith only [hL1]
  have hb0 : (0:ℝ) ≤ b' := by linarith only [hb1]
  have hk0 : (0:ℝ) ≤ k := by linarith only [hk1]
  have ha0 : (0:ℝ) ≤ a := by linarith only [hb1, hba]
  have hv0 : (0:ℝ) ≤ v := by linarith only [hv1]
  have hbS0 : (0:ℝ) ≤ b' + S := by linarith only [hb0, hS0]
  have hlogk : Real.log k ≤ L := by
    have : Real.log k ≤ Real.log (a * v) :=
      Real.log_le_log (by linarith only [hk1]) (hka.trans (le_mul_of_one_le_right ha0 hv1))
    linarith only [this, hN.log_av]
  have hlogkv0 : 0 ≤ Real.log (k * v) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hv1)
  have hlogkv : Real.log (k * v) ≤ L := by
    have : Real.log (k * v) ≤ Real.log (a * v) :=
      Real.log_le_log (mul_pos (by linarith only [hk1]) (by linarith only [hv1]))
        (mul_le_mul_of_nonneg_right hka hv0)
    linarith only [this, hN.log_av]
  have hG0 : 0 ≤ (f:ℝ) * N * b' * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hN0) hb0) hL0
  have hG : (f:ℝ) * N * b' * L ≤ f * m * N * b' * L := by
    have := mul_le_mul_of_nonneg_left hm1 hG0
    linarith only [this]
  have t1 : sA / k * logT ≤ 2 * C₀ * (a * nT * m * L / k) := by
    have s1 : sA / k ≤ 2 * a * nT / k := by gcongr
    have s0 : 0 ≤ 2 * a * nT / k :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hnT0') hk0
    calc sA / k * logT ≤ 2 * a * nT / k * logT := mul_le_mul_of_nonneg_right s1 hT0
      _ ≤ 2 * a * nT / k * (C₀ * m * L) := mul_le_mul_of_nonneg_left hTle s0
      _ = 2 * C₀ * (a * nT * m * L / k) := by ring
  have t2 : (nT:ℝ) * a * Real.log k ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogk (mul_nonneg hnT0' ha0)
  have t6 : (nT:ℝ) * a * Real.log (k * v) ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogkv (mul_nonneg hnT0' ha0)
  have t3 : (f:ℝ) * k * (b' + S) * Real.log k ≤ 2 * ((f:ℝ) * N * b' * L) := by
    have u1 : (k:ℝ) * (b' + S) ≤ N * (2 * b') :=
      mul_le_mul hkN (by linarith only [hSb]) hbS0 hN0
    have u2 : (f:ℝ) * k * (b' + S) * Real.log k ≤ f * k * (b' + S) * L :=
      mul_le_mul_of_nonneg_left hlogk (mul_nonneg (mul_nonneg hf0 hk0) hbS0)
    have u3 : (f:ℝ) * (k * (b' + S)) * L ≤ f * (N * (2 * b')) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2, u3]
  have t4 : (f:ℝ) * S * logT ≤ C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : S * logT ≤ b' * (C₀ * m * L) := mul_le_mul hSb hTle hT0 hb0
    have u2 : (f:ℝ) * (S * logT) ≤ f * (b' * (C₀ * m * L)) := mul_le_mul_of_nonneg_left u1 hf0
    have u3 : 0 ≤ (f:ℝ) * b' * C₀ * m * L :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 hb0) hC) hm0') hL0
    have u4 := mul_nonneg u3 (sub_nonneg.2 hN1)
    linarith only [u2, u4]
  have t5 : (f:ℝ) * (k:ℝ) ^ 2 * L ≤ (f:ℝ) * N * b' * L := by
    have u1 : (k:ℝ) * k ≤ N * b' := mul_le_mul hkN hkb hk0 hN0
    have u2 : (f:ℝ) * (k * k) * L ≤ f * (N * b') * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2]
  have t7 : (f:ℝ) * (b' + S) * (k * Real.log (k * v) + logT)
      ≤ 2 * ((f:ℝ) * N * b' * L) + 2 * C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : (k:ℝ) * Real.log (k * v) ≤ N * L :=
      (mul_le_mul_of_nonneg_left hlogkv hk0).trans (mul_le_mul_of_nonneg_right hkN hL0)
    have u2 : logT ≤ C₀ * m * N * L := by
      have h0 : 0 ≤ C₀ * m * L := mul_nonneg (mul_nonneg hC hm0') hL0
      calc logT ≤ C₀ * m * L := hTle
        _ = C₀ * m * L * 1 := by ring
        _ ≤ C₀ * m * L * N := mul_le_mul_of_nonneg_left hN1 h0
        _ = C₀ * m * N * L := by ring
    have u3 : 0 ≤ (k:ℝ) * Real.log (k * v) + logT := by
      have h0 := mul_nonneg hk0 hlogkv0
      linarith only [h0, hT0]
    have u4 : (b' + S) * ((k:ℝ) * Real.log (k * v) + logT) ≤ (2 * b') * (N * L + C₀ * m * N * L) :=
      mul_le_mul (by linarith only [hSb]) (by linarith only [u1, u2]) u3 (by linarith only [hb0])
    have u5 := mul_le_mul_of_nonneg_left u4 hf0
    linarith only [u5]
  have hD : (0:ℝ) < nT * m * b :=
    mul_pos (mul_pos (by linarith only [hnT]) (by linarith only [hm1])) hb
  rw [div_le_iff₀ hD]
  have hm0 : (m:ℝ) ≠ 0 := (by linarith only [hm1] : (0:ℝ) < m).ne'
  have hk0' : (k:ℝ) ≠ 0 := (by linarith only [hk1] : (0:ℝ) < k).ne'
  have hnT0 : (nT:ℝ) ≠ 0 := (by linarith only [hnT] : (0:ℝ) < nT).ne'
  have hb0' : b ≠ 0 := hb.ne'
  have hE : (10 + 5 * C₀) * (x * L / m + x * L / k + f * N * b' * L / (nT * b)) * (nT * m * b)
      = (10 + 5 * C₀) * (a * nT * L + a * nT * m * L / k + f * m * N * b' * L) := by
    rw [hax]
    field_simp
  rw [hE]
  have hQ1 : 0 ≤ a * nT * L := mul_nonneg (mul_nonneg ha0 hnT0') hL0
  have hQ2 : 0 ≤ a * nT * m * L / k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hnT0') hm0') hL0) hk0
  have hQ3 : 0 ≤ (f:ℝ) * m * N * b' * L := by linarith only [hG0, hG]
  have r1 := mul_nonneg hC hQ1
  have r2 := mul_nonneg hC hQ2
  have r3 := mul_nonneg hC hQ3
  linarith only [t1, t2, t3, t4, t5, t6, t7, hG, hQ1, hQ2, hQ3, r1, r2, r3]

end Formalism.HermitianLattices.TraceIntegrality
end
