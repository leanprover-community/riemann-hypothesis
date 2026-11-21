import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

section
open UpperHalfPlane CongruenceSubgroup UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def GoodWt (k : ℕ) : Prop :=
  ∃ f : ModularForm 𝒮ℒ (k : ℤ), coef f 0 = 1 ∧ ∀ n, ∃ c : ℤ, coef f n = c

private lemma bern4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

private lemma bern6 : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose, bernoulli'_four, bernoulli'_three, bernoulli'_two]

private lemma good0 : GoodWt 0 := by
  refine ⟨(1 : ModularForm 𝒮ℒ 0), ?_, fun n => ?_⟩
  · simp [coef, qExpansion_one]
  · refine ⟨if n = 0 then 1 else 0, ?_⟩
    simp [coef, qExpansion_one, PowerSeries.coeff_one]

private lemma good4 : GoodWt 4 := by
  refine ⟨ModularForm.E (k := 4) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern4]
    split_ifs
    · simp
    · push_cast; ring

private lemma good6 : GoodWt 6 := by
  refine ⟨ModularForm.E (k := 6) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern6]
    split_ifs
    · simp
    · push_cast; ring

private lemma good_add {a b : ℕ} (ha : GoodWt a) (hb : GoodWt b) : GoodWt (a + b) := by
  obtain ⟨f, hf0, hf⟩ := ha
  obtain ⟨g, hg0, hg⟩ := hb
  have h := ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g
  have key : ∀ n, coef (ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g)) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef f p.1 * coef g p.2 := by
    intro n
    unfold coef
    rw [ModularForm.coe_mcast, h, PowerSeries.coeff_mul]
  refine ⟨ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g), ?_, fun n => ?_⟩
  · rw [key]; simp [hf0, hg0]
  · choose c hc using hf
    choose d hd using hg
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2, ?_⟩
    rw [key]
    simp [hc, hd]

private lemma good_all (k : ℕ) (hk : Even k) (h2 : k ≠ 2) : GoodWt k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨m, hm⟩ := hk
    by_cases h0 : k = 0
    · subst h0; exact good0
    by_cases h6 : k = 6
    · subst h6; exact good6
    have : k = (k - 4) + 4 := by omega
    rw [this]
    exact good_add (ih _ (by omega) ⟨m - 2, by omega⟩ (by omega)) good4

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.levelOne :
    UpperTheory.V.Sd.LevelOne := by
  intro N k _ hk h2
  obtain ⟨f, hf0, hf⟩ := UpperTheory.V.Sd.good_all k hk h2
  have hle : (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  refine ⟨⟨⟨f, fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)⟩, ModularFormClass.holo f,
    fun hc => f.bdd_at_cusps' (hc.mono hle)⟩, fun γ => ?_, hf0, hf⟩
  exact SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
end

section
noncomputable section

open Formalism.ConjugateSelfDual Polynomial CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

section
variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N]

private structure Good (k : ℤ) (f : (ZMod N)ˣ → ℍ → ℂ) : Prop where
  mf : ∀ a, ∃ F : ModularForm (Gamma1 N) k, (F : ℍ → ℂ) = f a
  fam : ∀ (a b : (ZMod N)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → (b : ZMod N) = a * ((γ 1 1 : ℤ) : ZMod N) →
    f a ∣[k] γ = f b
  int : ∀ a, IntQ ι (f a)

omit [NeZero N] in
private lemma one_mem_per :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

variable {ι}

private lemma Good.q_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) (a) :
    qExpansion 1 (f a * g a) = qExpansion 1 (f a) * qExpansion 1 (g a) := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  rw [← hF, ← hG]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_per F G

private lemma Good.coef_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) (a) :
    coef (f a * g a) 0 = coef (f a) 0 * coef (g a) 0 := by
  unfold coef
  rw [hf.q_mul hg]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

private lemma Good.mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) :
    Good ι (k + k') (fun a => f a * g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F.mul G, by rw [ModularForm.coe_mul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [ModularForm.mul_slash_SL2, hf.fam a b γ hγ h, hg.fam a b γ hγ h]
  int a n := by
    unfold coef
    rw [hf.q_mul hg, PowerSeries.coeff_mul, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hf.int a p.1) (norm_nonneg _) (hg.int a p.2)

private lemma Good.coef_comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ) (a) (n : ℕ) :
    coef (f a + c • g a) n = coef (f a) n + c * coef (g a) n := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  unfold coef
  rw [← hF, ← hG]
  have h1 := ModularForm.qExpansion_add one_pos one_mem_per F (c • G)
  have h2 := ModularForm.qExpansion_smul one_pos one_mem_per c G
  rw [FunLike.coe_smul] at h1
  rw [h1, h2]
  simp

private lemma Good.comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ)
    (hc : ‖ι.symm c‖ ≤ 1) : Good ι k (fun a => f a + c • g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F + c • G, by rw [FunLike.coe_add, FunLike.coe_smul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [SlashAction.add_slash, ModularForm.SL_smul_slash, hf.fam a b γ hγ h, hg.fam a b γ hγ h]
  int a n := by
    rw [hf.coef_comb hg, map_add, map_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf.int a n) ?_)
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) (hg.int a n)

private lemma good_one (k : ℕ) (hk : Even k) (h2 : k ≠ 2) :
    ∃ E : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) E ∧ ∀ a, coef (E a) 0 = 1 := by
  obtain ⟨f, h1, h0, hi⟩ := levelOne N k hk h2
  refine ⟨fun _ => f, ⟨fun _ => ⟨f, rfl⟩, fun _ _ γ _ _ => h1 γ, fun _ n => ?_⟩, fun _ => h0⟩
  obtain ⟨c, hc⟩ := hi n
  rw [hc, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ c

omit [NeZero N] in
private lemma symm_Lk (k : ℕ) (x : ℂ) : ι.symm (Lk k x) = Lk k (ι.symm x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm

private def rt (ι : Qbar l ≃+* ℂ) (a : ZMod N) : Qbar l := ι.symm (ZMod.stdAddChar a : ℂ)

private lemma rt_pow (a : ZMod N) (n : ℕ) : rt ι a ^ n = rt ι (n • a) := by
  unfold rt
  rw [AddChar.map_nsmul_eq_pow, map_pow]

private lemma rt_zero : rt ι (0 : ZMod N) = 1 := by simp [rt]

private lemma rt_inj : Function.Injective (rt ι : ZMod N → Qbar l) :=
  ι.symm.injective.comp ZMod.injective_stdAddChar

private lemma rt_powN (a : ZMod N) : rt ι a ^ N = 1 := by
  rw [rt_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, rt_zero]

private lemma rt_norm (a : ZMod N) : ‖rt ι a‖ = 1 := by
  have h := congrArg norm (rt_powN (ι := ι) a)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).1 h

private lemma rt_neg (a : ZMod N) : rt ι (-a) = (rt ι a)⁻¹ := by
  unfold rt
  rw [AddChar.map_neg_eq_inv, map_inv₀]

private lemma rt_sq (hN : 3 ≤ N) (a : (ZMod N)ˣ) : rt ι (a : ZMod N) ^ 2 ≠ 1 := by
  intro h
  rw [rt_pow, ← rt_zero (ι := ι) (N := N)] at h
  have h1 := rt_inj h
  rw [nsmul_eq_mul, Units.mul_left_eq_zero, ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

private lemma unit_ne_zero (hN : 3 ≤ N) (a : (ZMod N)ˣ) : (a : ZMod N) ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact a.ne_zero

private lemma eis_coef0 (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : (ZMod N)ˣ) :
    ι.symm (coef (eisFun N k a) 0) = Lk k (rt ι (a : ZMod N)) := by
  rw [(eisCoef N k hk a (unit_ne_zero hN a)).1, symm_Lk]
  rfl

private lemma good_eis (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 3 ≤ k) :
    Good ι (k : ℤ) (fun a : (ZMod N)ˣ => eisFun N k a) where
  mf a := eisMF N k hk a
  fam a b γ hγ h := by
    rw [h]; exact eisSlash N k hk a γ hγ
  int a n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [eis_coef0 hN k hk]
      refine (lkSep l hl N (by omega) hlN).1 k _ (rt_powN _) fun h => rt_sq (ι := ι) hN a ?_
      rw [h, one_pow]
    · rw [(eisCoef N k hk a (unit_ne_zero hN a)).2 n hn, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
      have hr : ∀ b : ZMod N, ‖ι.symm (ZMod.stdAddChar b : ℂ)‖ = 1 := fun b => rt_norm (ι := ι) b
      rw [map_mul ι.symm, norm_mul, map_pow ι.symm, map_natCast ι.symm, norm_pow, map_add ι.symm, map_mul ι.symm]
      refine mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ e))
        (norm_nonneg _) ?_
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_mul, hr, hr, map_pow ι.symm, map_neg ι.symm, map_one ι.symm, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        max_self]

private lemma factor_of {m : ℕ} (hm : Even m) (h2 : m ≠ 2) {H : (ZMod N)ˣ → ℍ → ℂ} (hH : Good ι (m : ℤ) H)
    (d : (ZMod N)ˣ) (hd : ‖ι.symm (coef (H 1) 0) - ι.symm (coef (H d) 0)‖ = 1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) m hm h2
  refine ⟨m, _, hm, hH.comb hE (-coef (H d) 0) (by rw [map_neg, norm_neg]; exact hH.int d 0), ?_, ?_⟩
  · rw [hH.coef_comb hE, hE0]; ring
  · rw [hH.coef_comb hE, hE0, mul_one, ← sub_eq_add_neg, map_sub, hd]

private lemma factor (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (d : (ZMod N)ˣ) (h1 : d ≠ 1) (h2 : d ≠ -1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have g4 := good_eis (ι := ι) hl hN hlN 4 (by norm_num)
  have g5 := good_eis (ι := ι) hl hN hlN 5 (by norm_num)
  have hx : rt ι (d : ZMod N) ≠ rt ι ((1 : (ZMod N)ˣ) : ZMod N) := fun h => h1 (Units.ext (rt_inj h))
  have hy : rt ι (d : ZMod N) ≠ (rt ι ((1 : (ZMod N)ˣ) : ZMod N))⁻¹ := fun h => by
    rw [← rt_neg] at h
    exact h2 (Units.ext (rt_inj h))
  rcases (lkSep l hl N (by omega) hlN).2.2 _ _ (rt_powN _) (rt_powN _) (rt_sq hN 1) (rt_sq hN d) hx hy with h | h | h
  · refine factor_of (m := 4) (by decide) (by decide) g4 d ?_
    rw [eis_coef0 hN 4 (by norm_num), eis_coef0 hN 4 (by norm_num), h]
  · refine factor_of (m := 6) (by decide) (by decide) (g3.mul g3) d ?_
    rw [g3.coef_mul g3, g3.coef_mul g3, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl, ← sq, ← sq, h]
  · refine factor_of (m := 8) (by decide) (by decide) (g3.mul g5) d ?_
    rw [g3.coef_mul g5, g3.coef_mul g5, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl,
      eis_coef0 hN 5 (by norm_num), eis_coef0 hN 5 (by norm_num), h]

private lemma killer (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (S : Finset (ZMod N)ˣ) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ (∀ d ∈ S, d ≠ 1 → d ≠ -1 → coef (h d) 0 = 0) ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) 0 (by decide) (by decide)
    exact ⟨0, E, by decide, hE, by simp, by rw [hE0, map_one, norm_one]⟩
  | insert d S _ ih =>
    obtain ⟨m, h, hm, hg, h0, hu⟩ := ih
    by_cases hd : d ≠ 1 ∧ d ≠ -1
    · obtain ⟨m', h', hm', hg', h0', hu'⟩ := factor (ι := ι) hl hN hlN d hd.1 hd.2
      refine ⟨m + m', fun a => h a * h' a, hm.add hm', by exact_mod_cast hg.mul hg', fun e he e1 e2 => ?_, ?_⟩
      · rw [hg.coef_mul hg']
        rcases Finset.mem_insert.1 he with rfl | he
        · rw [h0', mul_zero]
        · rw [h0 e he e1 e2, zero_mul]
      · rw [hg.coef_mul hg', map_mul, norm_mul, hu, hu', mul_one]
    · refine ⟨m, h, hm, hg, fun e he e1 e2 => ?_, hu⟩
      rcases Finset.mem_insert.1 he with rfl | he
      · exact absurd ⟨e1, e2⟩ hd
      · exact h0 e he e1 e2

private lemma van_mul {k k' : ℕ} {f : ℍ → ℂ} (hf : VanOff N k f) {g : (ZMod N)ˣ → ℍ → ℂ} (hg : Good ι (k' : ℤ) g) (a) :
    VanOff N (k + k') (f * g a) := by
  intro γ hγ
  obtain ⟨G, hG⟩ := hg.mf a
  rw [Nat.cast_add, ModularForm.mul_slash_SL2, ← hG]
  exact Filter.ZeroAtFilter.mul_boundedAtFilter (hf γ hγ) (ModularFormClass.bdd_at_infty_slash G γ)

private lemma base (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 10 ≤ k) :
    ∃ f : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) f ∧ (∀ a, VanOff N k (f a)) ∧ ‖ι.symm (coef (f 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have v3 : ∀ a : (ZMod N)ˣ, VanOff N 3 (eisFun N 3 a) := fun a => eisVan N 3 le_rfl a a.isUnit (by omega)
  have u3 : ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N)) 0)‖ = 1 := by
    rw [eis_coef0 hN 3 le_rfl]
    exact (lkSep l hl N (by omega) hlN).2.1 _ (rt_powN _) (rt_sq hN 1)
  have step : ∀ (j : ℕ) (g : (ZMod N)ˣ → ℍ → ℂ), Good ι (j : ℤ) g → ‖ι.symm (coef (g 1) 0)‖ = 1 →
      Good ι ((3 + j : ℕ) : ℤ) (fun a : (ZMod N)ˣ => eisFun N 3 a * g a) ∧
      (∀ a : (ZMod N)ˣ, VanOff N (3 + j) (eisFun N 3 a * g a)) ∧
      ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N) * g 1) 0)‖ = 1 := fun j g hg hu =>
    ⟨by rw [Nat.cast_add]; exact g3.mul hg, fun a => van_mul (v3 a) hg a, by
      rw [g3.coef_mul hg, map_mul, norm_mul, u3, hu, mul_one]⟩
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 6) ⟨t - 3, by omega⟩ (by omega)
    obtain ⟨a1, -, a3⟩ := step _ E hE (by rw [hE0, map_one, norm_one])
    have := step _ _ a1 a3
    rw [show 3 + (3 + (2 * t - 6)) = 2 * t by omega] at this
    exact ⟨_, this⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 2) ⟨t - 1, by omega⟩ (by omega)
    have := step _ E hE (by rw [hE0, map_one, norm_one])
    rw [show 3 + (2 * t - 2) = 2 * t + 1 by omega] at this
    exact ⟨_, this⟩

end

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.unitFam :
    UpperTheory.V.Sd.UnitFam := by
  intro l _ hl ι N _ hN hlN
  obtain ⟨m, h, -, hg, h0, hu⟩ := killer (ι := ι) hl hN hlN Finset.univ
  refine ⟨10 + m, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + m := ⟨k - m, by omega⟩
  obtain ⟨f, hf, hv, hfu⟩ := base (ι := ι) hl hN hlN j (by omega)
  have hG : Good ι ((j + m : ℕ) : ℤ) (fun a => f a * h a) := by
    rw [Nat.cast_add]; exact hf.mul hg
  choose F hF using hG.mf
  refine ⟨F, fun a b γ hγ hab => ?_, fun a => ?_, fun a => ?_, ?_, fun a a1 a2 => ?_⟩
  · rw [hF, hF]; exact hG.fam a b γ hγ hab
  · rw [hF]; exact hG.int a
  · rw [hF]; exact van_mul (hv a) hg a
  · rw [hF, hf.coef_mul hg, map_mul, norm_mul, hfu, hu, mul_one]
  · rw [hF, hf.coef_mul hg, h0 a (Finset.mem_univ a) a1 a2, mul_zero]
end
end
