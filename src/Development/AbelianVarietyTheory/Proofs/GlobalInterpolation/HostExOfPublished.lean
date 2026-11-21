import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExistenceOfChoicesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesDyadicLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeNormOneShortInterval
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePairBoxBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesAPIntervalOfTzRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiZeroConstOfIntegrableOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoprimeFourMulTwoPow
import Development.AutomorphicArithmetic.CharacterBoxes.ThinChoice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Development.AutomorphicArithmetic.ThickFrames.topsBase
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_of_pair {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

open Filter Topology GlobalTheory.Mem.An.ManyNormPrimes in

private theorem many_norm_primes_mod (hTZ : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) (eps : ℝ) (he : 0 < eps) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ M d : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 0 < M → d ∣ M → Real.log M ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 →
    ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y →
      Y ^ ((9 : ℝ) / 10) ≤ ((GlobalTheory.Mem.An.normPrimes d M Y (2 * Y)).card : ℝ) := by
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  have hT : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ C₀ ≤ t ∧ Cr * Real.exp (-cr * t) ≤ 1 / 200 ∧
      40 * Real.exp (-(1 / 20) * t) ≤ c := by
    filter_upwards [eventually_ge_atTop 10000, eventually_ge_atTop C₀,
      ev_exp Cr cr (1 / 200) hcr (by norm_num), ev_exp 40 (1 / 20) c (by norm_num) hc] with t a b c d
    exact ⟨a, b, c, d⟩
  have hsq : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ 1 / 2 * x ^ (eps / 5) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound (c := 1 / 2) (by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx h1
    have h0 : (0 : ℝ) ≤ x ^ (eps / 5) := Real.rpow_nonneg (by linarith) _
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h0] at hx
    exact hx
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((hT.eventually E).and (hsq.and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨x₀, fun x hx M d hd hd4 hd100 hM0 hdM hN Y hY hYx => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hl, hx0⟩ := hx₀ x hx
  have hxe : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  set t := x ^ (eps / 5) with ht
  have hMr : (d : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM0 hdM
  have hdr : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : (1 : ℝ) < 4 * (d : ℝ) * (M : ℝ) ^ 2 := by nlinarith
  have hBt : Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ 8 * t ^ 2 := by
    have b1 : 4 * (d : ℝ) * (M : ℝ) ^ 2 ≤ 4 * (M : ℝ) ^ 3 := by nlinarith [sq_nonneg (M : ℝ)]
    have b2 := Real.log_le_log (by linarith) b1
    have hNp : (0 : ℝ) < M := by linarith
    rw [Real.log_mul (x := 4) (y := (M : ℝ) ^ 3) (by norm_num) (by positivity), Real.log_pow] at b2
    push_cast at b2
    have b3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have b4 : t * Real.log x ^ 2 ≤ t * (1 / 2 * t) := mul_le_mul_of_nonneg_left hl (by linarith)
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := core C₀ Cr cr c t _ Y hC₀ hCr hcr hc t1 t2 t3 t4 hB1 hBt hY
    (by rw [← hxe]; exact hYx)
  have := H d M hd hd4 hd100 (by omega) Y 1 k1 le_rfl k2 k3
  rw [show Y * (1 + 1) = 2 * Y by ring] at this
  exact k4.trans this

open Filter Topology GlobalTheory.Mem.An.ShortWindow in

private theorem exists_prime_normOne_mod (hTZ : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) (eps : ℝ) (he : 0 < eps) (cs CY : ℝ) (hcs : 0 < cs)
    (hCY : 0 < CY) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ N d g₁ g₂ m : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N →
      Real.log N ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps →
      Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → ∀ W Ts : ℝ, 1 ≤ W → W ≤ x ^ (12 : ℝ) → 0 < Ts →
      cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / W) * Ts ∧ GlobalTheory.Mem.An.NormOne d (N * (g₁ * g₂) ^ 2) T := by
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  set CB : ℝ := 8 * CY + 12 with hCB
  have hCB0 : 0 < CB := by positivity
  have e1 := ev_log_le (a := 2 * eps / 5) (k := 1) (by positivity) one_pos 0 1 one_pos
  have e2 := ev_log_le (a := 1 / 3) (k := cs) (by positivity) hcs (C₀ * CB) 1 one_pos
  have e3 := ev_log_le (a := 1 / 3) (k := cr * cs / CB) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e4 := ev_log_le (a := 1 / 6) (k := cr * Real.sqrt cs) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e5 := ev_log_le (a := 1 / 3) (k := cs / 3) (by positivity) (by positivity) (7 * CB) 12 (by norm_num)
  have e6 := Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (eventually_ge_atTop (1 : ℝ))))))))
  refine ⟨x₀, fun x hx N d g₁ g₂ m hd hd4 hd100 hN0 hdN hN hg₁ hg₂ hl₁ hl₂ hm W Ts hW hWx hTs hT => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hW0 : 0 < W := by linarith
  set L : ℝ := x ^ eps with hL
  set u : ℝ := x ^ ((1 : ℝ) / 3) with hu
  have hL1 : 1 ≤ L := Real.one_le_rpow hx1 he.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hlx : 0 ≤ Real.log x := by linarith
  have hd1 : 1 ≤ d := hd.one_lt.le
  set M : ℕ := N * (g₁ * g₂) ^ 2 with hM
  have hM1 : 1 ≤ M := Nat.succ_le_of_lt (by positivity)
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hdNR : (d : ℝ) ≤ N := by exact_mod_cast Nat.le_of_dvd hN0 hdN
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hg₁R : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have hg₂R : (1 : ℝ) ≤ g₂ := by exact_mod_cast hg₂
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hB1 : 1 < B := by
    have : (1 : ℝ) ≤ (M : ℝ) ^ 2 := one_le_pow₀ hMR
    calc (1 : ℝ) < 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 := by gcongr
  have hB0 : 0 < B := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos hB1
  have hNL : Real.log N ≤ 3 * L := by
    have h1 : Real.log x ^ 2 ≤ (x ^ (2 * eps / 5)) ^ 2 := by
      gcongr; linarith
    have h2 : x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 = L := by
      rw [hL, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have h3 : 0 ≤ x ^ (eps / 5) := by positivity
    calc _ ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 := hN
      _ ≤ 3 * x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 := by gcongr
      _ = 3 * L := by rw [mul_assoc, h2]
  have hlB : Real.log B ≤ CB * L := by
    have h1 : B ≤ 4 * (N : ℝ) ^ 3 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4 := by
      calc B = (4 * d : ℝ) * ((N : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by
            rw [hB, hM]; push_cast; ring
        _ ≤ (4 * N : ℝ) * ((N : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by gcongr
        _ = _ := by ring
    have h2 := Real.log_le_log hB0 h1
    generalize Real.log B = lB at h2 ⊢
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    have b3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [hCB]; linarith
  have hT' : cs * u * L ≤ Real.log Ts := le_trans (by gcongr) hT
  have hT0 : 0 < Real.log Ts := lt_of_lt_of_le (by positivity) hT'
  have a1 : B ^ C₀ ≤ Ts := by
    rw [Real.rpow_def_of_pos hB0, ← Real.le_log_iff_exp_le hTs]
    calc Real.log B * C₀ ≤ CB * L * C₀ := by gcongr
      _ = (C₀ * CB) * L := by ring
      _ ≤ cs * u * L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ _ := hT'
  have a2 : 1 / W ≤ 1 := by rw [div_le_one hW0]; exact hW
  have a3 : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Ts ≤ 1 / W / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have b1 : Cr * Real.exp (-(cr * Real.log Ts / Real.log B)) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e3.trans ?_)
      rw [le_div_iff₀ hlB0]
      calc cr * cs / CB * u * Real.log B ≤ cr * cs / CB * u * (CB * L) := by gcongr
        _ = cr * (cs * u * L) := by field_simp
        _ ≤ _ := by gcongr
    have b2 : Cr * Real.exp (-(cr * Real.sqrt (Real.log Ts))) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e4.trans ?_)
      rw [mul_assoc]
      gcongr
      apply Real.le_sqrt_of_sq_le
      have : (x ^ ((1 : ℝ) / 6)) ^ 2 = u := by
        rw [hu, sq, ← Real.rpow_add hx0]; congr 1; norm_num
      rw [mul_pow, Real.sq_sqrt hcs.le, this]
      refine le_trans ?_ hT'
      exact le_mul_of_one_le_right (by positivity) hL1
    rw [neg_mul, neg_mul, neg_div]
    linarith
  have a4 : B ^ (7 : ℝ) ≤ 1 / W * Ts ^ ((1 : ℝ) / 3) := by
    have b1 : Real.log B * 7 + Real.log x * 12 ≤ Real.log Ts * (1 / 3) := by
      have c1 : Real.log x * 12 ≤ Real.log x * 12 * L := le_mul_of_one_le_right (by positivity) hL1
      have c2 : (7 * CB + 12 * Real.log x) * L ≤ cs / 3 * u * L := by gcongr
      linarith only [c1, c2, hlB, hT']
    have b2 := Real.exp_le_exp.2 b1
    rw [Real.exp_add, ← Real.rpow_def_of_pos hB0, ← Real.rpow_def_of_pos hx0, ← Real.rpow_def_of_pos hTs] at b2
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hW0]
    refine le_trans ?_ b2
    gcongr
  have key := H d M hd hd4 hd100 hM1 Ts (1 / W) a1 a2 a3 a4
  have hpos : (0 : ℝ) < ((GlobalTheory.Mem.An.normPrimes d M Ts (Ts * (1 + 1 / W))).card : ℝ) :=
    lt_of_lt_of_le (by positivity) key
  obtain ⟨T, hTm⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  unfold GlobalTheory.Mem.An.normPrimes at hTm
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hTm
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := hTm
  refine ⟨T, t3, Nat.lt_of_floor_lt t1, ?_, t4⟩
  rw [mul_comm]
  exact (Nat.le_floor_iff (by positivity)).1 t2

theorem normPrimes_of_TZQuad (hT : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := many_norm_primes_mod hT eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  obtain ⟨hd, hd4, hd100, hN0, hdN, hN⟩ := hq
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d hd hd4 hd100 hN0 hdN (hs ▸ hN) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_of_pair h4⟩

theorem levelPrime_of_quadratic (hT : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := exists_prime_normOne_mod hT eps he0 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hd, hd4, hd100, hN0, hdN, hN⟩ := hq
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m hd hd4 hd100 hN0 hdN (hs ▸ hN)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_of_pair hT4⟩

theorem normPrimes_and_levelPrime : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → NormPrimes ∧ LevelPrime :=
  fun hT => ⟨normPrimes_of_TZQuad hT, levelPrime_of_quadratic hT⟩

end GlobalTheory.EX
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primes_and_level_prime : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → NormPrimes ∧ LevelPrime := by
  first | exact @GlobalTheory.EX.normPrimes_and_levelPrime | exact GlobalTheory.EX.normPrimes_and_levelPrime | (intros; apply GlobalTheory.EX.normPrimes_and_levelPrime <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem qdChoice_of_explicitFormula : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → QDChoice := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 eps he he'
  obtain ⟨x0, C, hC, h⟩ := GlobalTheory.T.exists_prime_pair_box_bounds h1 h2 h3 h4 h5 h6 h7 h8 eps he he'
  refine ⟨C, x0, hC, fun x hx n hn hn' => ?_⟩
  obtain ⟨q, d, hb, hq, hr⟩ := h x hx
  exact ⟨q, d, hr n hn hn', hq, hb⟩

end GlobalTheory.EX
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem smallPrimeOne_of_tzRat : GlobalTheory.Mem.An.TZRat → SmallPrimeOne := by
  intro h
  obtain ⟨C₀, Cr, cr, c, h0, h1, h2, h3, H⟩ := GlobalTheory.Mem.An.primesAPInterval_of_tzRat h
  obtain ⟨s, hsC, hs21, hsr⟩ : ∃ s : ℝ, C₀ ≤ s ∧ 21 ≤ s ∧ 200 * Cr / cr ≤ s :=
    ⟨max C₀ (max 21 (200 * Cr / cr)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hss : s ≤ s ^ 2 := by nlinarith
  have hexp : Cr * Real.exp (-cr * s) ≤ 1 / 200 := by
    have e1 : 200 * Cr ≤ cr * s := by
      rw [div_le_iff₀ h2] at hsr; linarith
    have e2 := Real.add_one_le_exp (cr * s)
    have e3 : 0 < Real.exp (cr * s) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ e3 (by norm_num)]
    linarith
  refine ⟨3 * s ^ 2 + 1, by nlinarith, ?_⟩
  intro M hM
  rcases Nat.eq_or_lt_of_le hM with rfl | hM3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have e1 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (3 * s ^ 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ e1
    norm_num
  have hm3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hB0 : (0 : ℝ) < 4 * (M : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (M : ℝ) := by linarith
  have hlB : 1 ≤ Real.log (4 * (M : ℝ)) := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := (4 * (M : ℝ)) ^ (s ^ 2) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
  have hlY : Real.log Y = s ^ 2 * Real.log (4 * (M : ℝ)) := Real.log_rpow hB0 _
  have hlY2 : s ^ 2 ≤ Real.log Y := by rw [hlY]; nlinarith [sq_nonneg s]
  have hlY0 : 0 < Real.log Y := by linarith
  have hrho : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * M) Y ≤ 1 / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have a1 : Real.exp (-cr * Real.log Y / Real.log (4 * (M : ℝ))) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      rw [hlY, ← mul_assoc, mul_div_assoc, div_self (by linarith), mul_one]
      nlinarith
    have a2 : Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      have : s ≤ Real.sqrt (Real.log Y) := Real.le_sqrt_of_sq_le hlY2
      nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 h1.le
    have b2 := mul_le_mul_of_nonneg_left a2 h1.le
    linarith
  have h7 : (4 * (M : ℝ)) ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) := by
    rw [one_mul, hY, ← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hc := H M 1 hM3 (Nat.coprime_one_left M) Y 1
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) le_rfl hrho h7
  have hpos : 0 < c * 1 * (4 * (M : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y := by
    have := Real.rpow_pos_of_pos hB0 (-6 : ℝ)
    positivity
  have hcard := lt_of_lt_of_le hpos hc
  rw [Nat.cast_pos, Finset.card_pos] at hcard
  obtain ⟨p, hp⟩ := hcard
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨-, hp2⟩, hpp, hpm⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · have : p % M = 1 % M := hpm
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  · have e1 : (p : ℝ) ≤ Y * (1 + 1) :=
      le_trans (Nat.cast_le.2 hp2) (Nat.floor_le (by positivity))
    have hM0 : (0 : ℝ) < M := by linarith
    have e2 : Y ≤ (M : ℝ) ^ (3 * s ^ 2) := by
      rw [Real.rpow_mul hM0.le]
      apply Real.rpow_le_rpow hB0.le _ (by positivity)
      have : (M : ℝ) ^ (3 : ℝ) = (M : ℝ) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (M : ℝ) 3
      rw [this]
      have : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [Real.rpow_add hM0, Real.rpow_one]
    nlinarith

end GlobalTheory.EX
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem thinChoice_of_explicit : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount →
    Formalism.ZeroFreeDirichlet.ZFRDirichlet → ThinChoice :=
  fun _ _ _ _ _ => thinChoice_host

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thin_choice_of_zero_density : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ThinChoice := by
  atlas_forward_decl GlobalTheory.EX.thinChoice_of_explicit
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TopsOfHost

theorem topsChoice_of
    (hnum : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p) : TopsChoice := by
  intro eps Co he he'
  obtain ⟨Cb, x0, hCb, h⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.topsBase eps (max Co 2) he he' (le_trans one_le_two (le_max_right _ _))
  refine ⟨Cb, x0, hCb, fun s R H hs hx hR hJC ho hsb => ?_⟩
  subst hs
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hJ : 1 ≤ s.J := s.one_le_J
  have hCo : Co ≤ max Co 2 := le_max_left _ _
  have hpw : 0 < s.x ^ (2 + 8 * s.eps) := Real.rpow_pos_of_pos hx0 _
  have hn1 : s.x ^ (2 + 8 * s.eps) / 2 ≤ (R.n : ℝ) := by linarith [hR.n_lo]
  have hn2 : (R.n : ℝ) ≤ max Co 2 * s.x ^ (2 + 8 * s.eps) :=
    hR.n_up.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpw.le)
  have ho' : (R.toFrame.o : ℝ) ≤ max Co 2 := ho.trans hCo
  have hp : ∀ p : ℕ, p.Prime → H.cls p = PrimeClass.inertClass → s.x ^ (s.eps / (5 * max Co 2)) < p := by
    intro p hp hc
    obtain ⟨h2, -, -, h5, -⟩ := (primeClass_eq_inert_iff H.toHostRaw).1 hc
    have h2' : p ≠ 2 := by
      rintro rfl
      exact h2 H.two_mem_small
    have h6 : ⌊s.x ^ (s.ez / 5)⌋₊ < p := by
      by_contra hle
      exact h5 (H.split_small p hp h2' ((not_lt.mp hle).trans hsb))
    have h7 : s.x ^ (s.ez / 5) < p := (Nat.floor_lt (Real.rpow_nonneg hx0.le _)).1 h6
    refine lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le ?_) h7
    unfold Scale.ez
    rw [div_div]
    exact div_le_div_of_nonneg_left s.eps_pos.le (by linarith) (by linarith)
  obtain ⟨TT, t1, t2, t3, t4⟩ := h (baseOf s 0 0 H) (hPH H) rfl hx hn1 hn2 ho' hR.2.2.1.2 hp
  exact ⟨TT, t1, t2, t4, t3⟩

end GlobalTheory.EX.TopsOfHost

end
end

section
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.choice_of_tops : Formalism.G0.TileConditionFailureProbBound := by
  first | exact @GlobalTheory.RandomTops.prob_not_good_le | exact GlobalTheory.RandomTops.prob_not_good_le | (intros; apply GlobalTheory.RandomTops.prob_not_good_le <;> assumption)
end

section
section
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.OrbitTerms

theorem markedBound_bounds (δ : ℝ) (r : ℕ) (h0 : 0 < δ) (h1 : δ ≤ 1 / 100) :
    (1 / 10 : ℝ) ^ (6 * r + 1) ≤ Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ∧
      Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ≤ 1 := by
  unfold Formalism.G0.markedBound
  set u := Formalism.MainNotions.G.goodU δ with hu
  have hlo : 1 / δ ≤ (u : ℝ) := Nat.le_ceil _
  have hhi : (u : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlo' : 1 ≤ (u : ℝ) * δ := by rwa [div_le_iff₀ h0] at hlo
  have hhi' : (u : ℝ) * δ ≤ 1 + δ := by
    have := mul_le_mul_of_nonneg_right hhi.le h0.le
    rwa [add_mul, one_div, inv_mul_cancel₀ h0.ne', one_mul] at this
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h] at hlo'; norm_num at hlo'
    · exact h
  have hd0 : 0 ≤ 1 - δ := by linarith
  have hd1 : 1 - δ ≤ 1 := by linarith
  have hv1 : (2 * ((u / 2 : ℕ) : ℝ) ≤ u) := by
    have : 2 * (u / 2) ≤ u := by omega
    exact_mod_cast this
  have hv2 : ((u : ℝ) ≤ 2 * ((u / 2 : ℕ) : ℝ) + 1) := by
    have : u ≤ 2 * (u / 2) + 1 := by omega
    exact_mod_cast this
  set v : ℕ := u / 2 with hv
  have hB : (12 / 25 : ℝ) ≤ (1 - δ) ^ (v + 1) := by
    have := one_add_mul_le_pow (a := -δ) (by linarith) (v + 1)
    have e : (1 + -δ) = 1 - δ := by ring
    rw [e] at this
    push_cast at this
    nlinarith
  have hA : (1 / 5 : ℝ) ≤ (1 - δ) ^ u := by
    have h2 : (1 - δ) ^ ((v + 1) * 2) ≤ (1 - δ) ^ u :=
      pow_le_pow_of_le_one hd0 hd1 (by omega)
    rw [pow_mul] at h2
    nlinarith
  have hA1 : (1 - δ) ^ u ≤ 1 := pow_le_one₀ hd0 hd1
  have hC1 : (1 - δ) ^ (u - 1) ≤ 1 := pow_le_one₀ hd0 hd1
  have hC0 : 0 ≤ (1 - δ) ^ (u - 1) := pow_nonneg hd0 _
  have hCe : (1 - δ) * (1 - δ) ^ (u - 1) = (1 - δ) ^ u := by
    rw [← pow_succ']; congr 1; omega
  have hvd : (1 - δ) / 2 ≤ (v : ℝ) * δ := by nlinarith
  have hvd1 : (v : ℝ) * δ ≤ 1 := by nlinarith
  have hvd0 : 0 ≤ (v : ℝ) * δ := by positivity
  have hD : (1 / 10 : ℝ) ≤ (v : ℝ) * δ * (1 - δ) ^ (u - 1) := by
    have := mul_le_mul_of_nonneg_right hvd hC0
    nlinarith
  have hD1 : (v : ℝ) * δ * (1 - δ) ^ (u - 1) ≤ 1 := mul_le_one₀ hvd1 hC0 hC1
  constructor
  · have e : (1 / 10 : ℝ) ^ (6 * r + 1) = (1 / 10) ^ (3 * r + 1) * (1 / 10) ^ (3 * r) := by
      rw [← pow_add]; congr 1; ring
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith) _)
      (pow_le_pow_left₀ (by norm_num) hD _) (by positivity) (by positivity)
  · exact mul_le_one₀ (pow_le_one₀ (by positivity) hA1) (by positivity)
      (pow_le_one₀ (by positivity) hD1)

theorem binUpper_le (G N : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hN : 6 * Real.exp 1 * (G : ℝ) * δ ≤ N) :
    Formalism.G0.binUpper G δ N ≤ Real.exp (-(N : ℝ)) := by
  have hd0 : 0 ≤ 1 - δ := by linarith
  set t : ℝ := Real.exp 2 with ht
  have ht1 : 1 ≤ t := Real.one_le_exp (by norm_num)
  have hs : Formalism.G0.binUpper G δ N * t ^ N ≤ (t * δ + (1 - δ)) ^ G := by
    unfold Formalism.G0.binUpper
    rw [add_pow, Finset.sum_mul]
    calc ∑ j ∈ Finset.Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ N
        ≤ ∑ j ∈ Finset.Icc N G, (t * δ) ^ j * (1 - δ) ^ (G - j) * (G.choose j : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := (Finset.mem_Icc.1 hj).1
          have : t ^ N ≤ t ^ j := pow_le_pow_right₀ ht1 hj'
          calc (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ N
              ≤ (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ j :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by rw [mul_pow]; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => by positivity
          intro j hj
          have := (Finset.mem_Icc.1 hj).2
          exact Finset.mem_range.2 (by omega)
  have h2 : (t * δ + (1 - δ)) ^ G ≤ Real.exp (N : ℝ) := by
    have a1 : t * δ + (1 - δ) ≤ Real.exp (t * δ) := by
      have := Real.add_one_le_exp (t * δ)
      linarith
    calc (t * δ + (1 - δ)) ^ G ≤ Real.exp (t * δ) ^ G :=
          pow_le_pow_left₀ (by positivity) a1 _
      _ = Real.exp (G * (t * δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          refine Real.exp_le_exp.2 (le_trans ?_ hN)
          have e1 : t = Real.exp 1 * Real.exp 1 := by rw [ht, ← Real.exp_add]; norm_num
          have e2 : Real.exp 1 ≤ 6 := by have := Real.exp_one_lt_d9; linarith
          have e3 : t ≤ 6 * Real.exp 1 := by
            rw [e1]; exact mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
          have : (G : ℝ) * δ * t ≤ (G : ℝ) * δ * (6 * Real.exp 1) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
          linarith
  have h3 : t ^ N = Real.exp (2 * N) := by rw [ht, ← Real.exp_nat_mul]; congr 1; ring
  have h4 : Real.exp (-(N : ℝ)) * t ^ N = Real.exp (N : ℝ) := by
    rw [h3, ← Real.exp_add]; congr 1; ring
  have h5 : Formalism.G0.binUpper G δ N * t ^ N ≤ Real.exp (-(N : ℝ)) * t ^ N := by
    rw [h4]; exact hs.trans h2
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem exists_log_le_rpow (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → C * (Real.log x + 1) ≤ x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := 1 / (2 * C)) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)
  have h3 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hx x hxx
  rw [Real.norm_of_nonneg (Real.log_nonneg b3), Real.norm_of_nonneg (by positivity)] at b1
  have : C * Real.log x ≤ x ^ a / 2 := by
    calc C * Real.log x ≤ C * (1 / (2 * C) * x ^ a) := mul_le_mul_of_nonneg_left b1 hC.le
      _ = x ^ a / 2 := by field_simp
  linarith

theorem orbit_terms_le : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ n L₂ : ℕ, s.x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + 1) * ((6 * Formalism.MainNotions.G.rG s + 1) * Formalism.MainNotions.G.goodU s.delta1) ≤ n ∧ (n : ℝ) * (L₂.choose (Formalism.MainNotions.G.KG s) : ℝ) * s.delta1 ^ Formalism.MainNotions.G.KG s + n * (1 - Formalism.G0.markedBound s.delta1 (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + n * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) s.delta1 (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x - 1) ≤ Cb * s.x ^ (-2 : ℝ) := by
  intro eps he he'
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 2 + 8 * eps := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈8 * (h + 2) / eps⌉₊ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = K + 1 := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (h + 3) * 10 ^ (6 * r + 1) := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((6 * r + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨x₀, hx₀⟩ := exists_log_le_rpow ((P + 2) * c * 2 + 100) (eps / 8) (by positivity)
    (by positivity)
  refine ⟨2 * 2 ^ ⌈1242 / eps⌉₊ + 4, x₀, by positivity, fun s hs hx n L₂ hn1 hn2 hL => ?_⟩
  have ehG : Formalism.MainNotions.G.hG s = h := by rw [hh, ← hs]; rfl
  have eKG : Formalism.MainNotions.G.KG s = K := by rw [hK, ← ehG, ← hs]; rfl
  have erG : Formalism.MainNotions.G.rG s = r := by rw [hr, ← eKG]; rfl
  have eδ : s.delta1 = s.x ^ (-(eps / 8)) := by rw [← hs]; rfl
  rw [ehG] at hn2
  rw [ehG, eKG, erG]
  have hx1 := s.one_lt_alt
  have hbig := hx₀ _ hx
  generalize s.delta1 = δ at *
  generalize s.x = x at *
  have hxp : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x ^ (eps / 8) := ⟨_, rfl⟩
  rw [← hy] at hbig
  have hPc : 0 < (P + 2) * c * 2 := by positivity
  have hy100 : 100 ≤ y := by
    have := mul_nonneg hPc.le hlog
    linarith only [this, hbig, hlog, hPc]
  have hδy : δ = y⁻¹ := by rw [eδ, hy, Real.rpow_neg hxp.le]
  have hδ0 : 0 < δ := by rw [hδy]; positivity
  have hδ1 : δ ≤ 1 / 100 := by
    rw [hδy, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) hy100
  have hMe : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) = P * Real.log x := by
    rw [zpow_neg, zpow_natCast, hP, div_inv_eq_mul]; ring
  have hM1 : P * Real.log x ≤ (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) := by
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity; rw [hMe]; exact Nat.le_ceil _
  have hM2 : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) ≤ P * Real.log x + 1 := by
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity; rw [hMe]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hkey : ∀ T : ℝ, T ≤ Real.exp (-((h + 2) * Real.log x)) → (n : ℝ) * T ≤ 2 * x ^ (-2 : ℝ) := by
    intro T hT
    have e : Real.exp (-((h + 2) * Real.log x)) = x ^ (-(h + 2)) := by
      rw [Real.rpow_def_of_pos hxp]; congr 1; ring
    rw [e] at hT
    calc (n : ℝ) * T ≤ n * x ^ (-(h + 2)) := mul_le_mul_of_nonneg_left hT hn0
      _ ≤ 2 * x ^ h * x ^ (-(h + 2)) := mul_le_mul_of_nonneg_right hn2 (by positivity)
      _ = 2 * x ^ (-2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
  constructor
  · have hu : (Formalism.MainNotions.G.goodU δ : ℝ) ≤ 2 * y := by
      unfold Formalism.MainNotions.G.goodU
      have e : 1 / δ = y := by rw [hδy, one_div, inv_inv]
      rw [e]
      have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ y by linarith)).le
      linarith
    have hyy : y * y = x ^ (eps / 4) := by
      rw [hy, ← Real.rpow_add hxp]; congr 1; ring
    have hM3 : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1 ≤ (P + 2) * (Real.log x + 1) := by
      linarith only [hM2, hlog, hP0]
    have : ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * (c * (Formalism.MainNotions.G.goodU δ : ℝ)) ≤ n := by
      calc ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * (c * (Formalism.MainNotions.G.goodU δ : ℝ))
          ≤ ((P + 2) * (Real.log x + 1)) * (c * (2 * y)) :=
            mul_le_mul hM3 (mul_le_mul_of_nonneg_left hu hc0.le) (by positivity) (by positivity)
        _ = ((P + 2) * c * 2 * (Real.log x + 1)) * y := by ring
        _ ≤ y * y := mul_le_mul_of_nonneg_right (by linarith only [hbig, hlog]) (by linarith only [hy100])
        _ ≤ n := by rw [hyy]; exact hn1
    rw [hc] at this
    exact_mod_cast this
  · have t1 : (n : ℝ) * δ ^ K ≤ 2 * x ^ (-2 : ℝ) := by
      apply hkey
      have e : δ ^ K = Real.exp (-(eps / 8 * K * Real.log x)) := by
        rw [eδ, ← Real.rpow_mul_natCast hxp.le, Real.rpow_def_of_pos hxp]; congr 1; ring
      rw [e]
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ hlog))
      have : 8 * (h + 2) / eps ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
      rw [div_le_iff₀ he] at this
      linarith
    have c1 : (L₂.choose K : ℝ) ≤ 2 ^ ⌈1242 / eps⌉₊ := by
      have a1 : L₂ ≤ ⌈1242 / eps⌉₊ := by
        have := hL.trans (Nat.le_ceil _)
        exact_mod_cast this
      have a2 : L₂.choose K ≤ 2 ^ ⌈1242 / eps⌉₊ :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) a1)
      exact_mod_cast a2
    have t1' : (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K ≤ 2 ^ ⌈1242 / eps⌉₊ * (2 * x ^ (-2 : ℝ)) := by
      calc (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K = (L₂.choose K : ℝ) * (n * δ ^ K) := by ring
        _ ≤ _ := mul_le_mul c1 t1 (by positivity) (by positivity)
    have t2 : (n : ℝ) * (1 - Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤
        2 * x ^ (-2 : ℝ) := by
      apply hkey
      obtain ⟨m1, m2⟩ := markedBound_bounds δ r hδ0 hδ1
      obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 / 10 : ℝ) ^ (6 * r + 1) := ⟨_, rfl⟩
      rw [← hq] at m1
      have hq0 : 0 < q := by rw [hq]; positivity
      have hPq : P * q = h + 3 := by
        rw [hP, hq, mul_assoc, ← mul_pow]; norm_num
      have a1 : 1 - Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ≤ Real.exp (-q) := by
        have := Real.add_one_le_exp (-q)
        linarith
      calc _ ≤ Real.exp (-q) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x := pow_le_pow_left₀ (by linarith) a1 _
        _ = Real.exp ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) * -q) := by rw [Real.exp_nat_mul]
        _ ≤ _ := by
          refine Real.exp_le_exp.2 ?_
          have a2 := mul_le_mul_of_nonneg_right hM1 hq0.le
          have a3 : P * Real.log x * q = (h + 3) * Real.log x := by rw [← hPq]; ring
          linarith only [a2, a3, hlog]
    have t3 : (n : ℝ) * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ
        (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ 2 * x ^ (-2 : ℝ) := by
      apply hkey
      unfold Formalism.MainNotions.G.orbitWindowCount
      rw [Nat.add_sub_cancel]
      have b0 := Nat.le_ceil (max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ)
        ((h + 3) * Real.logb 2 x))
      refine (binUpper_le _ _ δ hδ0.le (by linarith) ((le_max_left _ _).trans b0)).trans ?_
      refine Real.exp_le_exp.2 (neg_le_neg (le_trans ?_ ((le_max_right _ _).trans b0)))
      have l2 : Real.log x ≤ Real.logb 2 x := by
        unfold Real.logb
        have p1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have p2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
        rw [le_div_iff₀ p1]
        exact mul_le_of_le_one_right hlog p2
      exact mul_le_mul (by linarith only) l2 hlog (by linarith only [hh0])
    linarith only [t1', t2, t3]

end GlobalTheory.OrbitTerms
end

open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_inequalities_good : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ n L₂ : ℕ, s.x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + 1) * ((6 * Formalism.MainNotions.G.rG s + 1) * Formalism.MainNotions.G.goodU s.delta1) ≤ n ∧ (n : ℝ) * (L₂.choose (Formalism.MainNotions.G.KG s) : ℝ) * s.delta1 ^ Formalism.MainNotions.G.KG s + n * (1 - Formalism.G0.markedBound s.delta1 (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + n * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) s.delta1 (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x - 1) ≤ Cb * s.x ^ (-2 : ℝ) := by
  atlas_forward_decl GlobalTheory.OrbitTerms.orbit_terms_le
end

section
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.TopsChoice

open Formalism.FrobeniusOrbits Finset

lemma bern_eq_prod {α : Type} [Fintype α] [DecidableEq α] (δ : ℝ) (T : Finset α) :
    bern δ T = (∏ _a ∈ T, δ) * ∏ _a ∈ univ \ T, (1 - δ) := by
  simp [bern, Finset.card_univ_diff]

lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then bern δ T else 0) = bern δ S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else δ with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - δ with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = bern δ S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [bern_eq_prod, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [bern_eq_prod]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (A : Finset β → Prop) [DecidablePred A] :
    ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0) =
      ∑ S : Finset β, if A S then bern δ S else 0 := by
  calc ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0)
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then (if A S then bern δ T else 0) else 0) := by
        refine sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ S : Finset β, if A S then bern δ S else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        by_cases hA : A S
        · simp only [if_pos hA]
          exact fibre_sum δ f hf S
        · simp [hA]

open Classical in
lemma fin_sum_eq (n : ℕ) (δ : ℝ) (i₀ : Fin n) (A : Finset ℕ → Prop) :
    (∑ S : Finset (Fin n), if i₀ ∈ S ∧ A (S.map Fin.valEmbedding) then bern δ S else 0) =
      Formalism.G0.condProbAt n δ i₀ A * δ := by
  unfold Formalism.G0.condProbAt
  rw [sum_mul]
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have hm : (i₀ : ℕ) ∈ S.map Fin.valEmbedding ↔ i₀ ∈ S :=
      Finset.mem_map' Fin.valEmbedding
    simp only [hm]
    split_ifs with h
    · have hc : 1 ≤ S.card := card_pos.mpr ⟨i₀, h.1⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc
      simp only [bern, card_map, Fintype.card_fin, hk, Nat.add_sub_cancel]
      ring
    · simp

open Classical in

lemma orbit_sum {α : Type} [Fintype α] [DecidableEq α] [AddCommGroup α] (δ : ℝ) (b h t : α)
    (ht : ∃ i : ℕ, b + i • h = t) (A : Finset ℕ → Prop) :
    ∃ i₀ < addOrderOf h,
      (∑ T : Finset α, if t ∈ T ∧ A ((univ.filter
          (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)
        then bern δ T else 0) = Formalism.G0.condProbAt (addOrderOf h) δ i₀ A * δ := by
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  refine ⟨i % addOrderOf h, hlt, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  rw [← fin_sum_eq (addOrderOf h) δ ⟨_, hlt⟩ A, ← marginal δ _ hinj
    (fun S => (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ S ∧ A (S.map Fin.valEmbedding))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T) := by
    simp [mod_addOrderOf_nsmul, hi]
  simp only [this]

end GlobalTheory.TopsChoice

namespace GlobalTheory

open GlobalTheory.TopsChoice

theorem topsChoice : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p := by
  classical
  intro eps he he'
  obtain ⟨Cb, x₀, hCb, hnum⟩ := GlobalTheory.T.parameter_inequalities_good eps he he'
  refine ⟨Cb, max x₀ 32, hCb, ?_⟩
  intro s hs hx e L₂ hlo hhi hL bs hbs _ PP hp ω hω hPP
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hx32 : 32 ≤ s.x := le_trans (le_max_right _ _) hx
  have hδ : 0 < s.delta1 := Real.rpow_pos_of_pos hx0 _
  have hδ1 : s.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by have := s.eps_pos; linarith)
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2 ^ e)) = 2 ^ e := ZMod.card _
  have h16 : 16 ≤ s.delta1 * (Fintype.card (ZMod (2 ^ e)) : ℝ) := by
    rw [hcard]
    have h1 : s.x ≤ s.delta1 * s.x ^ Formalism.MainNotions.G.hG s := by
      unfold Scale.delta1 Formalism.MainNotions.G.hG
      rw [← Real.rpow_add hx0]
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by have := s.eps_pos; linarith)
    have := mul_le_mul_of_nonneg_left hlo hδ.le
    linarith
  have hβ : 0 ≤ Cb * s.x ^ (-2 : ℝ) := by positivity
  obtain ⟨T, hT1, hT2, hT3⟩ := Formalism.FrobeniusOrbits.hostTops (ZMod (2 ^ e)) PP s.delta1 (Cb * s.x ^ (-2 : ℝ))
    (fun p => ω p)
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (Formalism.MainNotions.G.KG s)
      (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
    hδ hδ1 hβ (fun p => hω p) h16 (by
      intro p t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s := by
        refine le_trans ?_ hhi
        exact Nat.cast_le.mpr (addOrderOf_le_card_univ.trans hcard.le)
      obtain ⟨h1, h2⟩ := hnum s hs (le_trans (le_max_left _ _) hx) (addOrderOf (hp p)) L₂
        (hPP p p.2) hn hL
      obtain ⟨i₀, hi₀, hsum⟩ := orbit_sum s.delta1 (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ Formalism.G0.GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
          (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU s.delta1 := Nat.ceil_pos.mpr (by positivity)
      have h3 := GlobalTheory.T.choice_of_tops (addOrderOf (hp p)) s.delta1 L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
        (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) i₀ hδ.le hδ1
        (Nat.le_add_left 1 _) hu h1 hi₀
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (h3.trans h2) hδ.le)
      rw [← hsum]
      unfold Formalism.MainNotions.G.IsGoodOrbit
      convert rfl)
  rw [hcard] at hT1 hT2 hT3
  refine ⟨T, hT1, hT2, ?_⟩
  rw [← Finset.sum_coe_sort PP, ← Finset.sum_coe_sort PP ω]
  refine le_trans (le_of_eq ?_) hT3
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

end GlobalTheory
end

section
section
namespace GlobalTheory.EX

theorem exists_tops : TopsChoice := TopsOfHost.topsChoice_of GlobalTheory.topsChoice

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tops_choice : TopsChoice := by
  atlas_forward_decl GlobalTheory.EX.exists_tops
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostEx_of_zeroFreeRegion :
    GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → HostEx :=
  fun hZ hC hL hN hD hR hP hJ hQ =>
    GlobalTheory.T.host_existence_of_choices (GlobalTheory.EX.qdChoice_of_explicitFormula hZ hC hL hN hD hR hP hJ)
      (GlobalTheory.T.thin_choice_of_zero_density hZ hC hL hN hD) (GlobalTheory.T.norm_primes_and_level_prime hQ).1
      (GlobalTheory.EX.smallPrimeOne_of_tzRat hR) GlobalTheory.T.tops_choice

end GlobalTheory.EX
end
