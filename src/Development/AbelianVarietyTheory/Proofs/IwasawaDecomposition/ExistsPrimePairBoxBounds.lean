import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadCharsCountOfDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GChiApproximationSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPrimesResidueGeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfEqOnCoprime

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ChoiceOfModulus

theorem level_mem_bad {Q : ℝ} {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hN : (N : ℝ) ≤ Q) (hp : χ.IsPrimitive) (h2 : χ ^ 2 = 1) (hr : GlobalTheoryTheory.IsRealChar χ)
    (h1 : χ ≠ 1) (hb : ¬ GlobalTheoryTheory.GoodFor Q χ) :
    N ∈ (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  refine ⟨⟨n, χ⟩, ⟨hN, hp, h2, fun hg => hb ⟨hp, hr, hN, fun s hs ht h0 => ?_⟩⟩, rfl⟩
  exact hg s hs ht ⟨Or.inl h1, h0⟩

theorem card_le_of_levels {Q B : ℝ} (hB0 : 0 ≤ B)
    (hB : (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal B)
    (S : Finset ℕ) (g : ℕ → ℕ) (hg : Function.Injective g)
    (h : ∀ q ∈ S, g q ∈ (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q) : (S.card : ℝ) ≤ B := by
  have h1 : ((S.image g : Finset ℕ) : Set ℕ) ⊆
      (fun c : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) => c.1 + 1) ''
      Formalism.HermitianLattices.GL2PrimeSums.BadChars Q := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hn)
    exact h q hq
  have h2 := (Set.encard_le_encard h1).trans (Set.encard_image_le _ _)
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hg] at h2
  have h3 := (ENat.toENNReal_le.mpr h2).trans hB
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast] at h3
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp h3

theorem exists_avoid (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (A₁ A₂ : ℕ → Prop)
    [DecidablePred A₁] [DecidablePred A₂] {M t : ℝ} (hP : 0 < (P.card : ℝ)) (ht : 0 < t)
    (hM : (∑ q ∈ P, f q) / P.card ≤ M) (hMt : 4 * M ≤ t)
    (h₁ : 4 * ((P.filter A₁).card : ℝ) ≤ P.card) (h₂ : 4 * ((P.filter A₂).card : ℝ) ≤ P.card) :
    ∃ q ∈ P, f q ≤ t ∧ ¬ A₁ q ∧ ¬ A₂ q := by
  by_contra hc
  have hsub : P ⊆ (P.filter (fun q => t < f q) ∪ P.filter A₁) ∪ P.filter A₂ := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter]
    by_contra hn
    apply hc
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · by_contra h; exact hn (Or.inl (Or.inl ⟨hq, not_le.mp h⟩))
    · intro h; exact hn (Or.inl (Or.inr ⟨hq, h⟩))
    · intro h; exact hn (Or.inr ⟨hq, h⟩)
  have hc1 : P.card ≤ (P.filter (fun q => t < f q)).card + (P.filter A₁).card
      + (P.filter A₂).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc2 : (P.card : ℝ) ≤ (P.filter (fun q => t < f q)).card + (P.filter A₁).card
      + (P.filter A₂).card := by exact_mod_cast hc1
  have h3 : ((P.filter (fun q => t < f q)).card : ℝ) * t ≤ ∑ q ∈ P, f q := by
    calc ((P.filter (fun q => t < f q)).card : ℝ) * t
        = ∑ _q ∈ P.filter (fun q => t < f q), t := by simp
      _ ≤ ∑ q ∈ P.filter (fun q => t < f q), f q :=
          Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
      _ ≤ ∑ q ∈ P, f q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q _ _ => hf q
  rw [div_le_iff₀ hP] at hM
  have h4 : 4 * ((P.filter (fun q => t < f q)).card : ℝ) * t ≤ P.card * t := by nlinarith
  have h5 := le_of_mul_le_mul_right h4 ht
  linarith

theorem eventually_sizes {eps : ℝ} (he : 0 < eps) (C₁ C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 2 ≤ x ^ (eps / 5) ∧
      (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ x ^ (eps / 5) ∧
      Real.log 8 + x ^ (eps / 5) ≤ x ^ (eps / 4) ∧
      4 * (C₁ * (8 * Real.exp (x ^ (eps / 5))) ^ ((1 : ℝ) / 4)) ≤
        Real.exp (x ^ (eps / 5)) ^ ((9 : ℝ) / 10) ∧
      16 * C * Real.log x ≤ x ^ (2 * eps) := by
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have t5 : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have t20 : Tendsto (fun x : ℝ => x ^ (eps / 20)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have tE : Tendsto (fun x : ℝ => Real.exp (x ^ (eps / 5)) ^ ((13 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_exp_atTop.comp t5)
  have o1 := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound
    (c := 4 / Real.log 8) (by positivity)
  have o2 := (isLittleO_log_rpow_atTop (r := 2 * eps) (by positivity)).bound
    (c := 1 / (16 * |C| + 1)) (by positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), t5.eventually_ge_atTop 2,
    t5.eventually_ge_atTop (Real.log 8), t20.eventually_ge_atTop 2,
    tE.eventually_ge_atTop (4 * |C₁| * 8 ^ ((1 : ℝ) / 4)), o1, o2] with x h4 h2 h8 h20 hE b1 b2
  have hx : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  refine ⟨h4, h2, ?_, ?_, ?_, ?_⟩
  · rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      Real.rpow_two, div_mul_eq_mul_div, le_div_iff₀ hl8] at b1
    linarith
  · have : x ^ (eps / 4) = x ^ (eps / 5) * x ^ (eps / 20) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [this]; nlinarith
  · have hX : 0 < Real.exp (x ^ (eps / 5)) := Real.exp_pos _
    have : Real.exp (x ^ (eps / 5)) ^ ((9 : ℝ) / 10) =
        Real.exp (x ^ (eps / 5)) ^ ((13 : ℝ) / 20) * Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hX]; norm_num
    rw [this, Real.mul_rpow (by norm_num) hX.le]
    have h0 : 0 ≤ Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by positivity
    have h1 : 4 * C₁ * 8 ^ ((1 : ℝ) / 4) ≤ 4 * |C₁| * 8 ^ ((1 : ℝ) / 4) := by
      gcongr; exact le_abs_self _
    calc _ = (4 * C₁ * 8 ^ ((1 : ℝ) / 4)) * Real.exp (x ^ (eps / 5)) ^ ((1 : ℝ) / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans hE) h0
  · rw [Real.norm_of_nonneg hlx, Real.norm_of_nonneg (by positivity),
      div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at b2
    have := le_abs_self C
    nlinarith

theorem exists_prime_good_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d → GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) := by
  classical
  intro hEZ hEC hLD hZC hZF hTZ hPg hJu eps he he'
  obtain ⟨C₁, hC₁, hbad⟩ := GlobalTheory.FewBadChars.badChars_count_of_density hJu
  obtain ⟨x₁, C, hC, hG⟩ := GlobalTheory.T.g_chi_approximation_sum hEZ hEC hLD hZC hZF eps he he'
  obtain ⟨x₂, hcard⟩ := GlobalTheory.Mem.An.card_primes_residue_ge_rpow hTZ eps he he'
  obtain ⟨x₃, C₃, hmean⟩ := GlobalTheory.T.multiplicative_weight_prime_sum hTZ hPg hZF eps he he'
  obtain ⟨x₄, hsz⟩ := Filter.eventually_atTop.mp (eventually_sizes he C₁ C₃)
  refine ⟨max (max x₁ x₂) (max x₃ x₄), C, hC, fun x hx => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx₁, hx₂⟩, hx₃, hx₄⟩ := hx
  obtain ⟨h4, h2, hlog, hQ4, hBP, hCx⟩ := hsz x hx₄
  have hx0 : 0 < x := by linarith
  have hXdef : GlobalTheoryTheory.X1 x eps = Real.exp (x ^ (eps / 5)) := rfl
  rw [← hXdef] at hBP
  set X := GlobalTheoryTheory.X1 x eps with hX
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_exp (by linarith)
  have hX0 : 0 < X := by linarith
  have hlX : Real.log X = x ^ (eps / 5) := by rw [hXdef, Real.log_exp]
  have h65 : x ^ (eps / 6) ≤ x ^ (eps / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hH1 : (1 / 4) * Real.log x ^ 2 * Real.log ((8 : ℕ) : ℝ) ≤ Real.log X := by
    rw [hlX]; exact_mod_cast hlog
  have hH2 : x ^ (eps / 6) ≤ Real.log X := hlX ▸ h65
  have hPc := hcard x hx₂ 8 3 (by norm_num) (by norm_num) X hX0 hH1 hH2
  have hm := hmean x hx₃ 8 3 dvd_rfl (by norm_num) (by norm_num) (by norm_num)
    (fun p hp hd => Or.inl (by
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hd)
      have : (p : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd two_pos this
      linarith)) X hX0 hH1 hH2 (fun _ => 1) rfl (fun _ _ => (mul_one _).symm) (fun _ => by simp)
  set P := Formalism.HermitianLattices.GL2PrimeSums.PP 8 3 X with hP
  have hmem : ∀ q ∈ P, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt X < q ∧ (q : ℝ) ≤ X := by
    intro q hq
    simp only [hP, Formalism.HermitianLattices.GL2PrimeSums.PP, Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨ha, hb⟩, hp, hm⟩ := hq
    exact ⟨hp, hm, (Nat.floor_lt (Real.sqrt_nonneg _)).mp ha, (Nat.le_floor_iff hX0.le).mp hb⟩
  have hB := hbad (8 * X) (by linarith)
  have hB0 : 0 ≤ C₁ * (8 * X) ^ ((1 : ℝ) / 4) := by positivity

  have fam1 : ∀ q d : ℕ, q.Prime → q % 8 = 3 → d.Prime → d % 4 = 3 → q ≠ d →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        GlobalTheoryTheory.Induces χ (GlobalTheoryTheory.psDir q) (8 * q * d) → N = q ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
          GlobalTheoryTheory.IsRealChar χ ∧ ∀ a : ℕ, 0 < a → χ (a : ZMod N) = GlobalTheoryTheory.psDir q a := by
    intro q d hq hq8 hd hd4 hqd N _ χ hχ
    have := GlobalTheory.QuadPrim.main q d hq hd (by omega) hd4 hqd 1 0 0 (by simp) N χ (by simpa using hχ)
    simpa using this
  have fam2 : ∀ q d : ℕ, q.Prime → q % 8 = 3 → d.Prime → d % 4 = 3 → q ≠ d →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        GlobalTheoryTheory.Induces χ (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) →
          N = 8 * q ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧ GlobalTheoryTheory.IsRealChar χ := by
    intro q d hq hq8 hd hd4 hqd N _ χ hχ
    obtain ⟨a, b, c, e, -⟩ :=
      GlobalTheory.QuadPrim.main q d hq hd (by omega) hd4 hqd 1 0 1 (by simp) N χ (by simpa using hχ)
    exact ⟨by simpa using a, b, c, e⟩
  have hs0 : 0 < x ^ (1 / 2 + eps) := Real.rpow_pos_of_pos hx0 _
  obtain ⟨q, hqP, hqS, hq1, hq2⟩ := exists_avoid P
    (fun p => ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) p‖ ^ 2) (fun _ => by positivity)
    (fun q => ∃ d : ℕ, d.Prime ∧ d % 4 = 3 ∧ q ≠ d ∧
      ¬ GoodAllFor (8 * X) (GlobalTheoryTheory.psDir q) (8 * q * d))
    (fun q => ∃ d : ℕ, d.Prime ∧ d % 4 = 3 ∧ q ≠ d ∧
      ¬ GoodAllFor (8 * X) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d))
    (t := (x ^ (1 / 2 + eps) / 2) ^ 2)
    (lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hPc) (by positivity) hm
    (by
      have : (x ^ (1 / 2 + eps)) ^ 2 = x * x ^ (2 * eps) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_one_add' hx0.le (by positivity)]
        congr 1; push_cast; ring
      rw [div_pow, this]
      nlinarith)
    (by
      refine le_trans ?_ (hBP.trans hPc)
      refine mul_le_mul_of_nonneg_left (card_le_of_levels hB0 hB _ id Function.injective_id ?_)
        (by norm_num)
      intro q hq
      obtain ⟨hqP, d, hd, hd4, hqd, hn⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, h8, -, hle⟩ := hmem q hqP
      by_contra hc
      refine hn fun N _ χ hχ => ?_
      obtain ⟨a, b, c, e, -⟩ := fam1 q d hp h8 hd hd4 hqd N χ hχ
      by_contra hb
      subst a
      exact hc (level_mem_bad (N := N) χ (by linarith) hχ.1 b e c hb))
    (by
      refine le_trans ?_ (hBP.trans hPc)
      refine mul_le_mul_of_nonneg_left (card_le_of_levels hB0 hB _ (fun q => 8 * q)
        (mul_right_injective₀ (by norm_num)) ?_) (by norm_num)
      intro q hq
      obtain ⟨hqP, d, hd, hd4, hqd, hn⟩ := Finset.mem_filter.mp hq
      obtain ⟨hp, h8, -, hle⟩ := hmem q hqP
      by_contra hc
      refine hn fun N _ χ hχ => ?_
      obtain ⟨a, b, c, e⟩ := fam2 q d hp h8 hd hd4 hqd N χ hχ
      by_contra hb
      subst a
      exact hc (level_mem_bad χ (by push_cast; linarith) hχ.1 b e c hb))
  obtain ⟨hp, h8, hlo, hle⟩ := hmem q hqP
  refine ⟨q, hp, h8, hlo, hle, fun d hd hd4 hqd => ?_⟩
  have g1 : GoodAllFor (8 * X) (GlobalTheoryTheory.psDir q) (8 * q * d) := by
    by_contra h; exact hq1 ⟨d, hd, hd4, hqd, h⟩
  have g2 : GoodAllFor (8 * X) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
    by_contra h; exact hq2 ⟨d, hd, hd4, hqd, h⟩
  refine ⟨g1, g2, fun N _ χ hχ => ?_⟩
  obtain ⟨-, -, hne, -, hval⟩ := fam1 q d hp h8 hd hd4 hqd N χ hχ
  have hlQ : Real.log (8 * X) = Real.log 8 + x ^ (eps / 5) := by
    rw [Real.log_mul (by norm_num) hX0.ne', hlX]
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  obtain ⟨k1, k2⟩ := hG x hx₁ (8 * X) N χ (by positivity) (by rw [hlQ]; linarith)
    (by rw [hlQ]; exact hQ4) hne (g1 N χ hχ)
  refine ⟨?_, k2⟩
  have hS : ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N) =
      Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.sqSum
    refine Finset.sum_congr (by first | rfl | simp) fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [hval n hn0, GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q n (by omega) hn0, mul_one]
    rfl
  rw [hS] at k1
  have k3 : ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q‖ ≤ x ^ (1 / 2 + eps) / 2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hqS
  have k4 : x ^ eps ≤ x ^ (1 / 2 + eps) / 2 := by
    have : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
    have h0 : 0 < x ^ eps := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_add hx0]; nlinarith
  have k5 := norm_sub_le (GlobalTheoryTheory.gChi χ x + Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q)
    (Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun _ => 1) q)
  rw [add_sub_cancel_right] at k5
  linarith

end GlobalTheory.ChoiceOfModulus
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_three_mod_eight_good : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q : ℕ, q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < q ∧ (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d → GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir q) (8 * q * d) ∧ GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir q a) (8 * q * d) ∧ BoundsAtX x eps C (GlobalTheoryTheory.psDir q) (8 * q * d) := by
  atlas_forward_decl GlobalTheory.ChoiceOfModulus.exists_prime_good_bounds
end

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.SplitPrimeChoice

theorem exists_small_pair (P B : Finset ℕ) (f g : ℕ → ℝ) (A T : ℝ) (hT : 0 < T)
    (hB : 2 * (B.card : ℝ) < P.card)
    (hf : (∑ p ∈ P, f p ^ 2) / P.card ≤ A) (hg : (∑ p ∈ P, g p ^ 2) / P.card ≤ A)
    (hA : 4 * A ≤ T ^ 2) : ∃ d ∈ P, d ∉ B ∧ f d ≤ T ∧ g d ≤ T := by
  by_contra hcon
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hP : (0 : ℝ) < P.card := by linarith
  rw [div_le_iff₀ hP] at hf hg
  have h1 : ∀ d ∈ P \ B, T ^ 2 ≤ f d ^ 2 + g d ^ 2 := by
    intro d hd
    obtain ⟨hdP, hdB⟩ := mem_sdiff.1 hd
    by_cases h : f d ≤ T
    · have h' : T < g d := by
        by_contra h'
        exact hcon ⟨d, hdP, hdB, h, not_lt.1 h'⟩
      nlinarith [sq_nonneg (f d)]
    · have h' := not_le.1 h
      nlinarith [sq_nonneg (g d)]
  have h2 := sum_le_sum h1
  rw [sum_const, nsmul_eq_mul] at h2
  have h3 : ∑ d ∈ P \ B, (f d ^ 2 + g d ^ 2) ≤ ∑ d ∈ P, (f d ^ 2 + g d ^ 2) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun d _ _ => by positivity)
  rw [sum_add_distrib (s := P)] at h3
  have h4 : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast card_le_card_sdiff_add_card
  have h5 : (P.card : ℝ) < 2 * (P \ B).card := by linarith
  have h6 := mul_lt_mul_of_pos_right h5 (pow_pos hT 2)
  nlinarith

theorem exists_modulus (n q : ℕ) (hq : q.Prime) (hq2 : q % 2 = 1) :
    ∃ M : ℕ, M % 2 = 1 ∧ q ∣ M ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → p ≤ n ∨ p = q) ∧ M ≤ q * 4 ^ n := by
  set S := (range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hS
  refine ⟨q * ∏ p ∈ S, p, ?_, dvd_mul_right _ _, ?_, ?_, ?_⟩
  · rw [← Nat.odd_iff] at hq2 ⊢
    refine hq2.mul (Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_)
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hp
    exact h1.odd_of_ne_two h2
  · intro p hp h2 hn
    exact (dvd_prod_of_mem (fun p => p) (mem_filter.2 ⟨mem_range.2 (by omega), hp, h2⟩)).mul_left q
  · intro p hp hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
    · obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
      obtain ⟨h0, h1, -⟩ := mem_filter.1 hr
      have := (Nat.prime_dvd_prime_iff_eq hp h1).1 hpr
      have := mem_range.1 h0
      exact Or.inl (by omega)
  · refine Nat.mul_le_mul_left q (le_trans ?_ (primorial_le_four_pow n))
    refine Nat.le_of_dvd (primorial_pos n) (prod_dvd_prod_of_subset _ _ _ ?_)
    intro p hp
    obtain ⟨h0, h1, -⟩ := mem_filter.1 hp
    exact mem_filter.2 ⟨h0, h1⟩

theorem kronSym_eq_one_of_dvd (d p : ℕ) (hp : p % 2 = 1) (h : p ∣ d + 1) :
    GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1 := by
  unfold GlobalTheoryTheory.kronSym
  have h0 : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one]
  have h1 : (-(d : ℤ)) % p = 1 % p := by
    apply Int.modEq_iff_dvd.2
    have : (p : ℤ) ∣ ((d + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h
    have e : (1 : ℤ) - -(d : ℤ) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [e]
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]

theorem kronSym_two_eq_one (d : ℕ) (h : d % 8 = 7) : GlobalTheoryTheory.kronSym (-(d : ℤ)) 2 = 1 := by
  unfold GlobalTheoryTheory.kronSym GlobalTheoryTheory.kron2
  rw [Nat.prime_two.factorization_self]
  norm_num
  split_ifs <;> omega

theorem sizes (eps C C₁ : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 2 ≤ Real.log x ∧ 3 ≤ x ^ (eps / 5) ∧ 800 * Real.log x ≤ x ^ (eps / 5) ∧
      2 * Real.log x ^ 2 ≤ x ^ (eps / 20) ∧ 16 * C * Real.log x ≤ x ^ (2 * eps) ∧ 8 * C₁ ≤ x ^ (eps / 5) := by
  have key : ∀ (c r s : ℝ), 0 < s → ∀ᶠ x : ℝ in atTop, c * Real.log x ^ r ≤ x ^ s := by
    intro c r s hs
    have h := ((isLittleO_log_rpow_rpow_atTop r hs).const_mul_left c).bound one_pos
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 s)] at hx
    exact (le_abs_self _).trans hx
  have h5 : 0 < eps / 5 := by positivity
  filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 2,
    (tendsto_rpow_atTop h5).eventually_ge_atTop 3, key 800 1 _ h5,
    key 2 2 (eps / 20) (by positivity), key (16 * C) 1 (2 * eps) (by positivity),
    (tendsto_rpow_atTop h5).eventually_ge_atTop (8 * C₁)] with x h1 h2 h3 h4 h6 h7 h8
  rw [Real.rpow_one] at h4 h7
  rw [Real.rpow_two] at h6
  exact ⟨h1, h2, h3, h4, h6, h7, h8⟩

theorem exists_bad_set (Q K : ℝ) (hK : 0 ≤ K)
    (hQ : (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal K)
    (q : ℕ) (hq : q.Prime) (hq4 : q % 4 = 3) :
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ 4 * K ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d →
      8 * (q : ℝ) * d ≤ Q → d ∉ B → ∀ i k : Fin 2,
        GoodAllFor Q (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) := by
  classical
  have hfin : (Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).Finite := by
    rw [← Set.encard_ne_top_iff]
    intro h
    rw [h] at hQ
    simp at hQ
  have hcard : (hfin.toFinset.card : ℝ) ≤ K := by
    rw [hfin.encard_eq_coe_toFinset_card] at hQ
    have h : ENNReal.ofReal (hfin.toFinset.card : ℝ) ≤ ENNReal.ofReal K := by
      rw [ENNReal.ofReal_natCast]; exact_mod_cast hQ
    exact (ENNReal.ofReal_le_ofReal_iff hK).1 h
  refine ⟨(univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image
    (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1))), ?_, ?_⟩
  · have h : ((univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image
        (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1)))).card ≤ 4 * hfin.toFinset.card := by
      refine (card_biUnion_le_card_mul _ _ hfin.toFinset.card (fun _ _ => card_image_le)).trans ?_
      simp
    have h' := (Nat.cast_le (α := ℝ)).2 h
    rw [Nat.cast_mul, Nat.cast_ofNat] at h'
    linarith
  · intro d hd hd4 hqd hle hdB i k N _ χ hχ
    obtain ⟨hN, hsq, hne, hre, -⟩ := GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 k (by simp) N χ
      (by simpa using hχ)
    have hNQ : (N : ℝ) ≤ Q := by
      refine le_trans ?_ hle
      have h8 : 8 ^ k.1 ≤ 8 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hqq : q ^ i.1 ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos (by omega)
      have : N ≤ 8 * q * d := by
        rw [hN]
        calc _ ≤ 8 ^ 1 * d ^ (1 : Fin 2).1 * q ^ 1 := by gcongr
          _ = _ := by simp; ring
      exact_mod_cast this
    refine ⟨hχ.1, hre, hNQ, fun s hs hi hz => hdB ?_⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
    refine mem_biUnion.2 ⟨(i, k), mem_univ _, mem_image.2 ⟨⟨n, χ⟩, hfin.mem_toFinset.2
      ⟨hNQ, hχ.1, hsq, fun hg => hg s hs hi ?_⟩, ?_⟩⟩
    · exact ⟨Or.inl hne, hz⟩
    · apply Nat.div_eq_of_eq_mul_right (by have := hq.pos; positivity)
      have : n + 1 = _ := hN
      simp only [this]
      simp; ring

theorem boundsAtX_of_good (x eps C Q : ℝ) (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3)
    (hd4 : d % 4 = 3) (hqd : q ≠ d) (i : Fin 2) (f : ℕ → ℂ)
    (hf : ∀ a, f a = GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1)
    (hx : x ^ eps ≤ x ^ ((1 : ℝ) / 2 + eps) / 2)
    (hgood : GoodAllFor Q
      (fun a => GlobalTheoryTheory.chi8 a ^ (0 : Fin 2).1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d))
    (htail : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ →
      ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N)‖ ≤ x ^ eps ∧
        ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x)
    (hs : ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d‖ ≤
      x ^ ((1 : ℝ) / 2 + eps) / 2) :
    BoundsAtX x eps C f (8 * q * d) := by
  intro N _ χ hχ
  have hχ' : GlobalTheoryTheory.Induces χ
      (fun a => GlobalTheoryTheory.chi8 a ^ (0 : Fin 2).1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) :=
    ⟨hχ.1, fun a ha => by rw [hχ.2 a ha, hf]; simp⟩
  obtain ⟨-, -, hne, -, hval⟩ := GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 0 (by simp) N χ
    (by simpa using hχ')
  obtain ⟨h1, h2⟩ := htail N χ hne (hgood N χ hχ')
  refine ⟨?_, h2⟩
  have e : ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N) =
      Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := (mem_Icc.1 hn).1
    rw [hval n hn0 rfl, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, GlobalTheoryTheory.kron,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d n hd4 hn0,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q n hq4 hn0]
    have : GlobalTheoryTheory.cn x n = Formalism.HermitianLattices.GL2PrimeSums.cn x n := rfl
    rw [this]
    simp only [Fin.val_one, pow_one]
    ring
  rw [e] at h1
  have h3 := norm_sub_le (GlobalTheoryTheory.gChi χ x +
    Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d)
    (Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d)
  rw [add_sub_cancel_right] at h3
  linarith

set_option maxHeartbeats 1000000 in

theorem exists_prime_split_good_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q % 8 = 3 → Real.sqrt (GlobalTheoryTheory.X1 x eps) < q → (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps → ∃ d : ℕ, d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧ GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧ (∀ i k : Fin 2, GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧ BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨C₁, hC₁, Hbad⟩ := GlobalTheory.FewBadChars.badChars_count_of_density p8
  obtain ⟨x₁, C, hC, Htail⟩ := GlobalTheory.T.g_chi_approximation_sum p1 p2 p3 p4 p5 eps he he'
  obtain ⟨x₂, Hcard⟩ := GlobalTheory.Mem.An.card_primes_residue_ge_rpow p6 eps he he'
  obtain ⟨x₃, C₃, Hms⟩ := GlobalTheory.T.multiplicative_weight_prime_sum p6 p7 p5 eps he he'
  obtain ⟨x₀, H₀⟩ := eventually_atTop.1 ((sizes eps C₃ C₁ he).and ((eventually_ge_atTop x₁).and
    ((eventually_ge_atTop x₂).and (eventually_ge_atTop x₃))))
  refine ⟨x₀, C, hC, fun x hx q hq hq8 hq1 hq2 => ?_⟩
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, hx1, hx2, hx3⟩ := H₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hq4 : q % 4 = 3 := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h65 : x ^ (eps / 6) ≤ x ^ (eps / 5) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have h4 : x ^ (eps / 4) = x ^ (eps / 5) * x ^ (eps / 20) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  unfold GlobalTheoryTheory.X1 at hq1 hq2
  unfold GlobalTheoryTheory.X1 GlobalTheoryTheory.X2
  rw [← Real.exp_half] at hq1
  set y := x ^ (eps / 5) with hy
  set L := Real.log x with hL
  have hL2 : 4 ≤ L ^ 2 := by nlinarith
  have hyL : 4 * y ≤ y * L ^ 2 := by nlinarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

  obtain ⟨M, hM2, hMq, hMp, hMd, hMle⟩ := exists_modulus ⌊y⌋₊ q hq (by omega)
  have hM0 : 0 < M := by omega
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hcop : Nat.Coprime (8 * M - 1) (16 * M) := by
    have h1 : Nat.Coprime (8 * M - 1) (8 * M) := by
      have : 8 * M = (8 * M - 1) + 1 := by omega
      conv_rhs => rw [this]
      simp
    have h2 : Nat.Coprime (8 * M - 1) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
    have := Nat.Coprime.mul_right h2 h1
    rwa [← mul_assoc] at this
  have hqz : x ^ (400 : ℝ) < q := by
    refine lt_of_le_of_lt ?_ hq1
    rw [Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.2 (by linarith)
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ 16 * M → (p : ℝ) ≤ y ∨ x ^ (400 : ℝ) < p := by
    intro p hp hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · have h' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from h)
      have : (p : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd two_pos h'
      exact Or.inl (by linarith)
    · rcases hMd p hp h with h' | rfl
      · exact Or.inl ((Nat.le_floor_iff (by linarith)).1 h')
      · exact Or.inr hqz
  have hlogm : (1 / 4) * L ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (Real.exp (y * L ^ 2)) := by
    have h1 : (M : ℝ) ≤ q * 4 ^ ⌊y⌋₊ := by exact_mod_cast hMle
    have h2 := Real.log_le_log hM0' h1
    rw [Real.log_mul hq0.ne' (by positivity), Real.log_pow] at h2
    have h3 : Real.log q ≤ y := (Real.log_le_iff_le_exp hq0).2 hq2
    have h5 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have h6 : (⌊y⌋₊ : ℝ) * Real.log 4 ≤ y * 1.4 :=
      mul_le_mul h5 (by linarith) (by linarith) (by linarith)
    rw [Real.log_exp, Nat.cast_mul, Real.log_mul (by norm_num) hM0'.ne', Nat.cast_ofNat]
    have h7 : Real.log 16 + Real.log M ≤ 4 * y := by linarith
    have h8 := mul_le_mul_of_nonneg_left h7 (sq_nonneg L)
    linarith
  have hlogX : x ^ (eps / 6) ≤ Real.log (Real.exp (y * L ^ 2)) := by
    rw [Real.log_exp]; linarith
  have hP := Hcard x hx2 (16 * M) (8 * M - 1) (by omega) hcop _ (Real.exp_pos _) hlogm hlogX
  have hms := fun i : Fin 2 => Hms x hx3 (16 * M) (8 * M - 1) (Dvd.intro (2 * M) (by ring)) (by omega) hcop
    (by omega) hprimes _ (Real.exp_pos _) hlogm hlogX (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1)
    (by simp) (fun m n => by rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul, mul_pow])
    (fun n => by
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h])

  set Q := 8 * Real.exp y * Real.exp (y * L ^ 2) with hQ
  have hQ0 : 0 < Q := by positivity
  have hlogQ : Real.log Q = Real.log 8 + y + y * L ^ 2 := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp]
  have hQ3 : 3 ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ0
    linarith
  obtain ⟨B, hB, HB⟩ := exists_bad_set Q _ (by positivity) (Hbad Q hQ3) q hq hq4
  have hBP : 2 * (B.card : ℝ) < (Formalism.HermitianLattices.GL2PrimeSums.PP (16 * M) (8 * M - 1) (Real.exp (y * L ^ 2))).card := by
    refine lt_of_lt_of_le ?_ hP
    have h1 : 8 * C₁ < Real.exp y := by
      have := Real.add_one_le_exp y
      linarith
    have h2 : 0 < Q ^ ((1 : ℝ) / 4) := by positivity
    have h3 : Real.exp y * Q ^ ((1 : ℝ) / 4) ≤ Real.exp (y * L ^ 2) ^ ((9 : ℝ) / 10) := by
      rw [Real.rpow_def_of_pos hQ0, ← Real.exp_mul, ← Real.exp_add, hlogQ]
      exact Real.exp_le_exp.2 (by linarith)
    have h5 := mul_lt_mul_of_pos_right h1 h2
    linarith
  have hT : 4 * (C₃ * x * L) ≤ (x ^ ((1 : ℝ) / 2 + eps) / 2) ^ 2 := by
    have h1 : (x ^ ((1 : ℝ) / 2 + eps)) ^ 2 = x * x ^ (2 * eps) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm x, ← Real.rpow_add_one hx0.ne']
      congr 1; push_cast; ring
    have h2 := mul_le_mul_of_nonneg_left s6 hx0.le
    rw [div_pow, h1]
    linarith
  obtain ⟨d, hdP, hdB, hd0, hd1⟩ := exists_small_pair _ B _ _ _ _ (by positivity) hBP (hms 0) (hms 1) hT
  obtain ⟨hdI, hd, hdm⟩ := mem_filter.1 hdP
  obtain ⟨hdl, hdu⟩ := mem_Ioc.1 hdI
  have hdl' : Real.sqrt (Real.exp (y * L ^ 2)) < d := (Nat.floor_lt (Real.sqrt_nonneg _)).1 hdl
  have hdu' : (d : ℝ) ≤ Real.exp (y * L ^ 2) := (Nat.le_floor_iff (Real.exp_pos _).le).1 hdu
  have hd16 : d % 16 = 7 := by
    have : d % 16 = (8 * M - 1) % 16 := hdm.of_mul_right M
    omega
  have hMdvd : M ∣ d + 1 := by
    have h1 : d + 1 ≡ 8 * M - 1 + 1 [MOD M] := (hdm.of_mul_left 16).add_right 1
    rw [show 8 * M - 1 + 1 = 8 * M by omega] at h1
    exact (Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left M 8))))
  have hqd : q ≠ d := by
    rintro rfl
    rw [← Real.exp_half] at hdl'
    have := Real.exp_lt_exp.1 (hdl'.trans_le hq2)
    linarith
  have hgood := HB d hd (by omega) hqd (by rw [hQ]; gcongr) hdB
  have hxe : x ^ eps ≤ x ^ ((1 : ℝ) / 2 + eps) / 2 := by
    rw [Real.rpow_add hx0, ← Real.sqrt_eq_rpow]
    have h1 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have h2 : 0 < x ^ eps := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    linarith
  have htail := fun (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) =>
    Htail x hx1 Q N χ hQ0 (by linarith) (by
      have h1 := mul_le_mul_of_nonneg_left s5 (show 0 ≤ y by linarith)
      rw [h4, hlogQ]; linarith)
  refine ⟨d, hd, hd16, hdl', hdu', kronSym_eq_one_of_dvd d q (by omega) (hMq.trans hMdvd), ?_, hgood,
    boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 0 _ (by simp) hxe (hgood 0 0) htail hd0,
    boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 1 _ (by simp) hxe (hgood 1 0) htail hd1⟩
  intro p hp hpy
  by_cases h2 : p = 2
  · subst h2
    exact kronSym_two_eq_one d (by omega)
  · exact kronSym_eq_one_of_dvd d p (Nat.odd_iff.1 (hp.odd_of_ne_two h2))
      ((hMp p hp h2 (Nat.le_floor hpy)).trans hMdvd)

end GlobalTheory.SplitPrimeChoice
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_seven_mod_sixteen_good : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q % 8 = 3 → Real.sqrt (GlobalTheoryTheory.X1 x eps) < q → (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps → ∃ d : ℕ, d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧ GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧ (∀ i k : Fin 2, GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧ BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
  atlas_forward_decl GlobalTheory.SplitPrimeChoice.exists_prime_split_good_bounds
end

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem boundsAtX_mono_const {x eps C C' : ℝ} {f : ℕ → ℂ} {M : ℕ} (hx : 0 ≤ Real.log x) (hC : C ≤ C')
    (h : BoundsAtX x eps C f M) : BoundsAtX x eps C' f M := by
  intro N _ χ hχ
  obtain ⟨h1, h2⟩ := h N χ hχ
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hC hx)⟩

theorem log_four_mul_nqd_le {x eps : ℝ} {n q d : ℕ} (he : 0 < eps) (he' : eps < 1 / 52)
    (hx : Real.exp 5 ≤ x) (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (hd1 : 1 ≤ d)
    (hn : (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)) (hq : (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps) (hd : (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps) :
    Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  have hx0 : 0 < x := (Real.exp_pos 5).trans_le hx
  have hL : 5 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hy : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hx1 (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hlq : Real.log q ≤ x ^ (eps / 5) := (Real.log_le_iff_le_exp hq0).2 hq
  have hld : Real.log d ≤ x ^ (eps / 5) * Real.log x ^ 2 := (Real.log_le_iff_le_exp hd0).2 hd
  have hln : Real.log n ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have := Real.log_le_log hn0 hn
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at this
  have h4 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  have h3 : (2 + 8 * eps) * Real.log x ≤ 3 * Real.log x :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 5 * Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have h6 : Real.log x ^ 2 - 1 ≤ x ^ (eps / 5) * (Real.log x ^ 2 - 1) :=
    le_mul_of_one_le_left (by linarith) hy
  nlinarith

theorem exists_q_d_box_bounds_rows : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, Boxq x eps q d ∧ QDq x eps C q d ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) → Rowq x eps n q d := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x1, C1, hC1, H1⟩ := GlobalTheory.T.exists_prime_three_mod_eight_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x2, C2, hC2, H2⟩ := GlobalTheory.T.exists_prime_seven_mod_sixteen_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  refine ⟨max (max x1 x2) (Real.exp 5), max C1 C2, lt_max_of_lt_left hC1, fun x hx => ?_⟩
  have hx1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx5 : Real.exp 5 ≤ x := (le_max_right _ _).trans hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hx5)
  obtain ⟨q, hq, hq8, hql, hqu, Hq⟩ := H1 x hx1
  obtain ⟨d, hd, hd16, hdl, hdu, hk, hsp, hg, hb1, hb2⟩ := H2 x hx2 q hq hq8 hql hqu
  obtain ⟨g1, g2, b0⟩ := Hq d hd (by omega) (by rintro rfl; omega)
  refine ⟨q, d, ⟨g1, g2, ?_, ?_, ?_, ?_⟩,
    ⟨boundsAtX_mono_const hL (le_max_left _ _) b0, boundsAtX_mono_const hL (le_max_right _ _) hb1,
      boundsAtX_mono_const hL (le_max_right _ _) hb2⟩, fun n hn1 hn =>
    ⟨hq, hq8, hql, hqu, hd, hd16, hdl, hdu, hk, hsp,
      log_four_mul_nqd_le he he' hx5 hn1 hq.one_le hd.one_le hn hqu hdu⟩⟩
  · simpa using hg 0 0
  · simpa using hg 0 1
  · simpa using hg 1 0
  · simpa using hg 1 1

end GlobalTheory.Mem.An
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pair_box_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, Boxq x eps q d ∧ QDq x eps C q d ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) → Rowq x eps n q d := by
  atlas_forward_decl GlobalTheory.Mem.An.exists_q_d_box_bounds_rows
end
